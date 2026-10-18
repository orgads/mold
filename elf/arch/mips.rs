//! MIPS is a RISC ISA developed in the '80s. It is no longer a popular
//! choice for new designs, but it is still widely used in network
//! appliances and routers. This file implements the two Linux ABIs that
//! matter in practice: the 32-bit O32 and N32 ABIs and the 64-bit N64 ABI,
//! in both byte orders. N32 is an ELF32 ABI for 64-bit CPUs and links like
//! O32 except that its object files use RELA.
//!
//! The MIPS psABIs diverge from the other psABIs in a few ways that make
//! them hard to support:
//!
//! 1. The ISA has no PC-relative addressing. A function materializes the
//!    address of its GOT plus 0x7ff0 in the GP register and reads GOT
//!    entries with a single load instruction with a signed 16-bit
//!    displacement, so only GP ± 32 KiB is addressable. A large program
//!    needs much more GOT than that, so the linker is expected to give
//!    each input file its own GOT ("multi-GOT"). A function computes its
//!    file's GP value from `_gp_disp`, `__gnu_local_gp` or
//!    `%neg(%gp_rel(func))`, all of which we resolve to the file's GOT.
//!
//!    We create one GOT per input file and merge consecutive ones as long
//!    as the result fits in 64 KiB. All GOTs are laid out back to back in
//!    a single `.got`.
//!
//! 2. The dynamic linker doesn't relocate GOT entries using ordinary
//!    dynamic relocations. Instead, the psABI requires `.dynsym` entries to
//!    be sorted so that the tail of `.dynsym` corresponds one-to-one to the
//!    tail of the "primary" GOT, which the loader fills with the symbols'
//!    addresses ("Quickstart"). There's no way to turn this off, so we
//!    reserve a placeholder region at the beginning of `.got` with one
//!    entry per dynamic symbol (DT_MIPS_GOTSYM is 0), let the loader fill
//!    it and otherwise ignore it. Our GOT entries are relocated with
//!    ordinary R_MIPS_REL32 dynamic relocations instead. As a side effect,
//!    `.dynsym` can be in any order.
//!
//! 3. A N64 relocation record has up to three relocation types that are
//!    applied in sequence. We represent them as a single 24-bit relocation
//!    type and support only the combinations that compilers emit. N32
//!    expresses the same combinations as consecutive records, which we
//!    merge into one when reading them.
//!
//! 4. Dynamic relocations are always of the REL type, even on N64 whose
//!    object files use RELA. O32 object files use REL, which we convert to
//!    RELA when reading them, because the addend of a HI16 relocation is
//!    split between the instruction it relocates and the instruction of
//!    the paired LO16 relocation.
//!
//! 5. `.eh_frame` contains absolute addresses even in position-independent
//!    code. We rewrite CIEs to make them PC-relative so that `.eh_frame`
//!    doesn't need dynamic relocations.
//!
//! 6. A position-independent function computes its GP value from its own
//!    address, which its caller must pass in t9. Non-PIC code calls
//!    functions with JAL, which doesn't set t9, so we redirect such calls
//!    to PIC functions to thunks that set t9 ("LA25 stubs").
//!
//! We don't create lazy-binding stubs. All imported symbols are resolved
//! on process startup.
//!
//! https://refspecs.linuxfoundation.org/elf/mipsabi.pdf
//! https://math-atlas.sourceforge.net/devel/assembly/mipsabi64.pdf

use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

use mold_common::{error, fatal, warn};

use crate::arch::{Class, ElfClass, Family, Target, ThunkLayout};
use crate::chunks::eh_frame;
use crate::context::Context;
use crate::elf::*;
use crate::input_files::{FileId, ObjectFile};
use crate::input_sections::{InputSection, NonAllocReloc, check_tlsle, scan_absrel, scan_pcrel};
use crate::symbol::{AddrFlags, NEEDS_PLT, Symbol, SymbolId};
use crate::thunks::Thunk;

#[derive(Clone, Copy, Debug, Default)]
pub struct MipsTarget<const LE: bool, const IS_64: bool>;

pub type Mips64Be = MipsTarget<false, true>;
pub type Mips64Le = MipsTarget<true, true>;
pub type Mips32Be = MipsTarget<false, false>;
pub type Mips32Le = MipsTarget<true, false>;

/// A N64 relocation record. r_info is split into a 32-bit symbol index, a
/// special symbol index and three relocation types, laid out in this order
/// regardless of the byte order.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct Mips64Rela<E: Target> {
    r_offset: U64<E>,
    r_sym: U32<E>,
    r_ssym: u8,
    r_type3: u8,
    r_type2: u8,
    r_type: u8,
    r_addend: I64<E>,
}

/// A N64 dynamic relocation record.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct Mips64Rel<E: Target> {
    r_offset: U64<E>,
    r_sym: U32<E>,
    r_ssym: u8,
    r_type3: u8,
    r_type2: u8,
    r_type: u8,
}

// SAFETY: all fields are byte-backed integers or bytes, and `repr(C)` does
// not insert padding between fields with alignment one.
unsafe impl<E: Target> FileRecord for Mips64Rela<E> {}
// SAFETY: see Mips64Rela.
unsafe impl<E: Target> FileRecord for Mips64Rel<E> {}

const _: () = assert!(size_of::<Mips64Rela<Mips64Be>>() == 24);
const _: () = assert!(size_of::<Mips64Rel<Mips64Be>>() == 16);

// The three relocation types are packed into one u32, the first type in
// the lowest byte.
macro_rules! impl_mips64_rel {
    ($record:ident, $is_rela:expr) => {
        impl<E: Target> $record<E> {
            fn get_type(&self) -> u32 {
                u32::from(self.r_type)
                    | u32::from(self.r_type2) << 8
                    | u32::from(self.r_type3) << 16
            }

            fn put_type(&mut self, value: u32) {
                self.r_type = value as u8;
                self.r_type2 = (value >> 8) as u8;
                self.r_type3 = (value >> 16) as u8;
            }
        }
    };
}

impl_mips64_rel!(Mips64Rela, true);
impl_mips64_rel!(Mips64Rel, false);

#[rustfmt::skip]
impl<E: Target> RelRecord for Mips64Rela<E> {
    const IS_RELA: bool = true;

    fn new(r_offset: u64, r_type: u32, r_sym: u32, r_addend: i64) -> Self {
        let mut rel = Self::default();
        rel.r_offset.set(r_offset);
        rel.put_type(r_type);
        rel.r_sym.set(r_sym);
        rel.r_addend.set(r_addend);
        rel
    }

    fn r_offset(&self) -> u64 { self.r_offset.get() }
    fn set_r_offset(&mut self, value: u64) { self.r_offset.set(value) }
    fn r_type(&self) -> u32 { self.get_type() }
    fn set_r_type(&mut self, value: u32) { self.put_type(value) }
    fn r_sym(&self) -> u32 { self.r_sym.get() }
    fn set_r_sym(&mut self, value: u32) { self.r_sym.set(value) }
    fn r_addend(&self) -> i64 { self.r_addend.get() }
    fn set_r_addend(&mut self, value: i64) { self.r_addend.set(value) }
}

#[rustfmt::skip]
impl<E: Target> RelRecord for Mips64Rel<E> {
    const IS_RELA: bool = false;

    fn new(r_offset: u64, r_type: u32, r_sym: u32, _r_addend: i64) -> Self {
        let mut rel = Self::default();
        rel.r_offset.set(r_offset);
        rel.put_type(r_type);
        rel.r_sym.set(r_sym);
        rel
    }

    fn r_offset(&self) -> u64 { self.r_offset.get() }
    fn set_r_offset(&mut self, value: u64) { self.r_offset.set(value) }
    fn r_type(&self) -> u32 { self.get_type() }
    fn set_r_type(&mut self, value: u32) { self.put_type(value) }
    fn r_sym(&self) -> u32 { self.r_sym.get() }
    fn set_r_sym(&mut self, value: u32) { self.r_sym.set(value) }
    fn r_addend(&self) -> i64 { 0 }
    fn set_r_addend(&mut self, _value: i64) {}
}

/// The relocation records of the 32-bit and 64-bit ABIs.
pub trait MipsClass {
    type Rel<E: Target>: RelRecord;
    type DynRel<E: Target>: RelRecord;
}

impl MipsClass for Class<false> {
    type Rel<E: Target> = ElfRela<E>;
    type DynRel<E: Target> = ElfRelNoAddend<E>;
}

impl MipsClass for Class<true> {
    type Rel<E: Target> = Mips64Rela<E>;
    type DynRel<E: Target> = Mips64Rel<E>;
}

// Relocation type combinations used by N64.
const R_GPREL16_SUB_HI16: u32 = R_MIPS_GPREL16 | R_MIPS_SUB << 8 | R_MIPS_HI16 << 16;
const R_GPREL16_SUB_LO16: u32 = R_MIPS_GPREL16 | R_MIPS_SUB << 8 | R_MIPS_LO16 << 16;
const R_GPREL32_64: u32 = R_MIPS_GPREL32 | R_MIPS_64 << 8;
const R_REL32_64: u32 = R_MIPS_REL32 | R_MIPS_64 << 8;

// ELF32 has only 8 bits for a relocation type, so merged N32 records use
// these otherwise unused types for the combinations.
const R_N32_GPREL16_SUB_HI16: u32 = 0xf0;
const R_N32_GPREL16_SUB_LO16: u32 = 0xf1;
const R_N32_GPREL32_64: u32 = 0xf2;

/// The type of a relocation, with N32 combinations in the N64 form.
fn rel_type<E: Target>(r_type: u32) -> u32 {
    match r_type {
        R_N32_GPREL16_SUB_HI16 if !E::IS_64 => R_GPREL16_SUB_HI16,
        R_N32_GPREL16_SUB_LO16 if !E::IS_64 => R_GPREL16_SUB_LO16,
        R_N32_GPREL32_64 if !E::IS_64 => R_GPREL32_64,
        _ => r_type,
    }
}

// %hi() and friends round to the nearest because the instruction that
// adds the low part sign-extends it.
fn hi16(v: u64) -> u64 {
    (v.wrapping_add(0x8000) >> 16) & 0xffff
}

fn higher(v: u64) -> u64 {
    (v.wrapping_add(0x8000_8000) >> 32) & 0xffff
}

fn highest(v: u64) -> u64 {
    (v.wrapping_add(0x8000_8000_8000) >> 48) & 0xffff
}

/// The address of the 64 KiB "page" that a GOT_PAGE entry holds. The
/// matching GOT_OFST, or LO16 for O32's GOT16, adds the rest.
fn page(v: u64) -> u64 {
    v.wrapping_add(0x8000) & !0xffff
}

impl<const LE: bool, const IS_64: bool> MipsTarget<LE, IS_64>
where
    Class<IS_64>: ElfClass + MipsClass,
{
    /// Replaces the 16-bit immediate field of the instruction at `loc`.
    fn write_imm16(loc: &mut [u8], val: u64) {
        let insn = Self::read_u32(loc);
        Self::write_u32(loc, (insn & 0xffff_0000) | (val as u32 & 0xffff));
    }
}

impl<const LE: bool, const IS_64: bool> Target for MipsTarget<LE, IS_64>
where
    Class<IS_64>: ElfClass + MipsClass,
{
    const IS_LITTLE: bool = LE;
    type Word = <Class<IS_64> as ElfClass>::Word<Self>;
    type Sym = <Class<IS_64> as ElfClass>::Sym<Self>;
    type Phdr = <Class<IS_64> as ElfClass>::Phdr<Self>;
    type Chdr = <Class<IS_64> as ElfClass>::Chdr<Self>;
    type Rel = <Class<IS_64> as MipsClass>::Rel<Self>;
    type DynRel = <Class<IS_64> as MipsClass>::DynRel<Self>;

    type InputSectionExtra = ();

    const NAME: &'static str = match (IS_64, LE) {
        (true, true) => "mips64le",
        (true, false) => "mips64be",
        (false, true) => "mips32le",
        (false, false) => "mips32be",
    };
    const FAMILY: Family = Family::Mips;
    const PAGE_SIZE: u64 = 65536;
    const E_MACHINE: u32 = EM_MIPS;
    const PLTGOT_SIZE: u64 = 0;
    const TRAP: &'static [u8] = if LE { &[0x0d, 0, 0, 0] } else { &[0, 0, 0, 0x0d] }; // break

    const R_COPY: u32 = R_MIPS_COPY;
    const R_GLOB_DAT: u32 = if IS_64 { R_REL32_64 } else { R_MIPS_REL32 };
    const R_JUMP_SLOT: u32 = R_MIPS_JUMP_SLOT;
    const R_ABS: u32 = if IS_64 { R_REL32_64 } else { R_MIPS_REL32 };
    const R_RELATIVE: u32 = if IS_64 { R_REL32_64 } else { R_MIPS_REL32 };
    const R_DTPOFF: u32 = if IS_64 { R_MIPS_TLS_DTPREL64 } else { R_MIPS_TLS_DTPREL32 };
    const R_TPOFF: u32 = if IS_64 { R_MIPS_TLS_TPREL64 } else { R_MIPS_TLS_TPREL32 };
    const R_DTPMOD: u32 = if IS_64 { R_MIPS_TLS_DTPMOD64 } else { R_MIPS_TLS_DTPMOD32 };
    const R_FUNCALL: &'static [u32] =
        &[R_MIPS_26, R_MIPS_CALL16, R_MIPS_CALL_HI16, R_MIPS_CALL_LO16, R_MIPS_JALR];
    const THUNK: Option<ThunkLayout> =
        Some(ThunkLayout { header_size: 0, max_entry_size: if IS_64 { 32 } else { 16 } });

    fn rel_to_string(r_type: u32) -> std::borrow::Cow<'static, str> {
        let r_type = rel_type::<Self>(r_type);
        if r_type <= 0xff {
            return mips_rel_to_string(r_type);
        }
        let mut names = vec![mips_rel_to_string(r_type & 0xff)];
        if (r_type >> 8) & 0xff != 0 || r_type >> 16 != 0 {
            names.push(mips_rel_to_string((r_type >> 8) & 0xff));
        }
        if r_type >> 16 != 0 {
            names.push(mips_rel_to_string(r_type >> 16));
        }
        names.join("/").into()
    }

    fn rewrite_input_sections(ctx: &mut Context<Self>) {
        // Output .MIPS.abiflags is a single record merged from the input
        // records, so we keep only the first input section. .reginfo and
        // .MIPS.options record the GP value of the input file, which is
        // meaningless in the output.
        let mut seen_abiflags = false;
        for file in &ctx.objs {
            for isec in file.input_sections() {
                if !isec.is_alive() {
                    continue;
                }
                match isec.sh_type(file) {
                    SHT_MIPS_ABIFLAGS if !seen_abiflags => seen_abiflags = true,
                    SHT_MIPS_ABIFLAGS | SHT_MIPS_REGINFO | SHT_MIPS_OPTIONS => {
                        isec.kill();
                    }
                    _ => {}
                }
            }
        }
    }

    fn scan_symbols(ctx: &mut Context<Self>) {
        let mut got = MipsGot::new(ctx.objs.pool_len());
        for file in &ctx.objs {
            got.gp0[file.id().index()] = read_gp0(file);
        }
        ctx.mips_got = Some(got);
    }

    fn after_scan_relocations(ctx: &mut Context<Self>) {
        finalize_got(ctx);
    }

    fn eflags(ctx: &Context<Self>) -> u32 {
        merge_eflags(ctx)
    }

    fn plt_entry_offset(_ctx: &Context<Self>, idx: u32) -> u64 {
        idx as u64 * PLT_ENTRY_SIZE
    }

    // PLT entries load a function address from .got.plt, which is
    // relocated with R_MIPS_JUMP_SLOT, and jump to it. Unlike the PLT of
    // GNU ld, ours has no header because it doesn't support lazy binding.
    fn write_plt_header(_ctx: &Context<Self>, _buf: &mut [u8]) {}

    fn write_plt_entry(ctx: &Context<Self>, buf: &mut [u8], sym: &Symbol) {
        let ent = sym.gotplt_addr(ctx);
        let load = if IS_64 { 0xdf39_0000 } else { 0x8f39_0000 }; // l[wd] t9, 0(t9)

        let insns: [u32; 8] = if ctx.args.pic {
            // A position-independent caller calls a function with its
            // address in t9, so we can compute addresses relative to it.
            let off = ent.wrapping_sub(sym.plt_addr(ctx));
            let addu = if IS_64 { 0x01f9_782d } else { 0x01f9_7821 }; // [d]addu t7, t7, t9
            [
                0x3c0f_0000 | hi16(off) as u32, // lui   t7, %hi(OFF)
                addu,
                (load & !0x03e0_0000) | 0x01e0_0000 | (off as u32 & 0xffff), // l[wd] t9, %lo(OFF)(t7)
                0x0320_0008,                                                 // jr    t9
                0,
                0,
                0,
                0,
            ]
        } else if IS_64 {
            [
                0x3c19_0000 | highest(ent) as u32, // lui    t9, %highest(ENT)
                0x6739_0000 | higher(ent) as u32,  // daddiu t9, t9, %higher(ENT)
                0x0019_cc38,                       // dsll   t9, t9, 16
                0x6739_0000 | hi16(ent) as u32,    // daddiu t9, t9, %hi(ENT)
                0x0019_cc38,                       // dsll   t9, t9, 16
                load | (ent as u32 & 0xffff),      // ld     t9, %lo(ENT)(t9)
                0x0320_0008,                       // jr     t9
                0,                                 // nop
            ]
        } else {
            [
                0x3c19_0000 | hi16(ent) as u32, // lui t9, %hi(ENT)
                load | (ent as u32 & 0xffff),   // lw  t9, %lo(ENT)(t9)
                0x0320_0008,                    // jr  t9
                0,
                0,
                0,
                0,
                0,
            ]
        };
        for (i, insn) in insns.into_iter().enumerate() {
            Self::write_u32(&mut buf[i * 4..], insn);
        }
    }

    fn write_pltgot_entry(_ctx: &Context<Self>, _buf: &mut [u8], _sym: &Symbol) {}

    fn always_needs_thunk(
        ctx: &Context<Self>,
        isec: &InputSection<Self>,
        sym: &Symbol,
        rel: &ElfRel<Self>,
    ) -> bool {
        // ponytail: a function is PIC if its file is; STO_MIPS_PIC, which
        // only MIPS16 and `ld -r` of mixed files set, is ignored.
        let is_pic = |e_flags: u32| e_flags & EF_MIPS_PIC != 0;
        rel.r_type() == R_MIPS_26
            && !is_pic(ctx.objs[isec.file.index()].base.e_flags)
            && sym.ty() == STT_FUNC
            && matches!(sym.file(), Some(FileId::Obj(id)) if is_pic(ctx.objs[id.index()].base.e_flags))
    }

    // A thunk entry puts the address of the destination in t9 and jumps
    // there.
    fn write_thunk(ctx: &Context<Self>, thunk: &Thunk, _addr: u64, buf: &mut [u8]) {
        for (i, &sym) in thunk.symbols.iter().enumerate() {
            let s = ctx.symbols[sym].addr(ctx);
            let insns: &[u32] = if IS_64 {
                &[
                    0x3c19_0000 | highest(s) as u32,   // lui    t9, %highest(S)
                    0x6739_0000 | higher(s) as u32,    // daddiu t9, t9, %higher(S)
                    0x0019_cc38,                       // dsll   t9, t9, 16
                    0x6739_0000 | hi16(s) as u32,      // daddiu t9, t9, %hi(S)
                    0x0019_cc38,                       // dsll   t9, t9, 16
                    0x6739_0000 | (s as u32 & 0xffff), // daddiu t9, t9, %lo(S)
                    0x0320_0008,                       // jr     t9
                    0,                                 // nop
                ]
            } else {
                &[
                    0x3c19_0000 | hi16(s) as u32,      // lui   t9, %hi(S)
                    0x2739_0000 | (s as u32 & 0xffff), // addiu t9, t9, %lo(S)
                    0x0320_0008,                       // jr    t9
                    0,                                 // nop
                ]
            };
            let off = thunk.offsets[i] as usize;
            for (j, &insn) in insns.iter().enumerate() {
                Self::write_u32(&mut buf[off + j * 4..], insn);
            }
        }
    }

    fn apply_eh_reloc(
        _ctx: &Context<Self>,
        _isec: &InputSection<Self>,
        rel: &ElfRel<Self>,
        loc: &mut [u8],
        p: u64,
        val: u64,
    ) {
        // Absolute pointers are converted to PC-relative ones; see
        // rewrite_cie() below.
        match rel.r_type() {
            R_NONE => {}
            R_MIPS_32 | R_MIPS_PC32 => Self::write_u32(loc, val.wrapping_sub(p) as u32),
            R_MIPS_64 => Self::write_u64(loc, val.wrapping_sub(p)),
            _ => eh_frame::unsupported::<Self>(rel),
        }
    }

    fn is_absrel(rel: &ElfRel<Self>) -> bool {
        rel.r_type() == if IS_64 { R_MIPS_64 } else { R_MIPS_32 }
    }

    fn scan_relocations(ctx: &Context<Self>, isec: &InputSection<Self>) {
        debug_assert!(isec.is_alloc());
        let file = &ctx.objs[isec.file.index()];
        let gp_syms = [ctx.syms.mips_gp_disp, ctx.syms.mips_gnu_local_gp];
        let mut keys = Vec::new();

        for rel in isec.rels(file) {
            if rel.r_type() == R_NONE || Self::is_absrel(rel) || isec.record_undef_error(ctx, rel) {
                continue;
            }
            let sym_id = file.base.symbols[rel.r_sym() as usize];
            let sym = &ctx.symbols[sym_id];
            let a = rel.r_addend();
            let mut add = |kind, sym: SymbolId, addend| keys.push(GotKey { kind, sym, addend });

            // ponytail: GCC for MIPS doesn't support IFUNC, so neither do we.
            if sym.is_ifunc() {
                error!("{}: IFUNC symbol `{}' is not supported on MIPS", isec.display(file), sym);
                continue;
            }

            match rel_type::<Self>(rel.r_type()) {
                R_MIPS_HI16 | R_MIPS_LO16 | R_MIPS_HIGHER | R_MIPS_HIGHEST
                    if gp_syms.contains(&Some(sym_id)) => {}
                // A LO16 completes a HI16 or a GOT16 (a GOT page address),
                // so the paired relocation is the one to check.
                R_MIPS_16 | R_MIPS_32 | R_MIPS_HI16 | R_MIPS_HIGHER | R_MIPS_HIGHEST => {
                    scan_absrel(ctx, isec, sym, rel)
                }
                R_MIPS_LO16 => {}
                R_MIPS_26 => {
                    // A PLT entry for a position-independent output expects
                    // its own address in t9, which J and JAL don't set.
                    if sym.is_imported() {
                        if ctx.args.pic {
                            error!(
                                "{}: {} relocation against imported symbol `{}' can not be used when making a position-independent output; recompile with -fPIC",
                                isec.display(file),
                                rel.type_name::<Self>(),
                                sym
                            );
                        }
                        sym.add_flags(NEEDS_PLT);
                    }
                }
                R_MIPS_PC16 | R_MIPS_PC32 => scan_pcrel(ctx, isec, sym, rel),
                R_MIPS_GOT_DISP | R_MIPS_CALL16 | R_MIPS_GOT_HI16 | R_MIPS_GOT_LO16
                | R_MIPS_CALL_HI16 | R_MIPS_CALL_LO16 => add(DISP, sym_id, a),
                R_MIPS_GOT16 => add(if is_local_ref(file, rel) { PAGE } else { DISP }, sym_id, a),
                R_MIPS_GOT_PAGE => add(PAGE, sym_id, a),
                R_MIPS_TLS_GD => add(TLSGD, sym_id, 0),
                R_MIPS_TLS_LDM => add(TLSLD, SymbolId(0), 0),
                R_MIPS_TLS_GOTTPREL => add(GOTTP, sym_id, 0),
                R_MIPS_TLS_TPREL_HI16
                | R_MIPS_TLS_TPREL_LO16
                | R_MIPS_TLS_TPREL32
                | R_MIPS_TLS_TPREL64 => check_tlsle(ctx, isec, sym, rel),
                R_MIPS_GOT_OFST
                | R_MIPS_GPREL16
                | R_MIPS_LITERAL
                | R_MIPS_GPREL32
                | R_GPREL16_SUB_HI16
                | R_GPREL16_SUB_LO16
                | R_GPREL32_64
                | R_MIPS_JALR
                | R_MIPS_TLS_DTPREL_HI16
                | R_MIPS_TLS_DTPREL_LO16
                | R_MIPS_TLS_DTPREL32
                | R_MIPS_TLS_DTPREL64 => {}
                _ => error!(
                    "{}: unknown relocation: {}",
                    isec.display(file),
                    rel.type_name::<Self>()
                ),
            }
        }

        if !keys.is_empty() {
            let got = ctx.mips_got.as_ref().unwrap();
            got.requests[isec.file.index()].lock().unwrap().extend(keys);
        }
    }

    fn apply_reloc_alloc(
        ctx: &Context<Self>,
        isec: &InputSection<Self>,
        rels: &mut [ElfRel<Self>],
        buf: &mut [u8],
    ) {
        let file = &ctx.objs[isec.file.index()];
        let isec_addr = isec.addr(ctx);
        let got = ctx.mips_got.as_ref().unwrap();
        let part = got.file_part[isec.file.index()] as usize;
        let gp = got.gp(ctx, part);
        let gp0 = got.gp0[isec.file.index()];

        for rel in rels.iter() {
            if rel.r_type() == R_NONE || Self::is_absrel(rel) {
                continue;
            }
            let sym_id = file.base.symbols[rel.r_sym() as usize];
            let sym = &ctx.symbols[sym_id];
            if sym.ty() == STT_TLS && sym.is_remaining_undef_weak() {
                continue;
            }

            let off = rel.r_offset() as usize;
            let loc = &mut buf[off..];
            let is_gp_disp = Some(sym_id) == ctx.syms.mips_gp_disp;
            let s = if Some(sym_id) == ctx.syms.mips_gnu_local_gp { gp } else { sym.addr(ctx) };
            let a = rel.r_addend() as u64;
            let p = isec_addr + rel.r_offset();
            let sa = s.wrapping_add(a);

            // A GP-relative value against a local symbol is relative to the
            // GP value the object file was created with, which is not zero
            // if it was created by `ld -r`.
            let gprel = || {
                let v = sa.wrapping_sub(gp);
                if is_local_ref(file, rel) { v.wrapping_add(gp0) } else { v }
            };

            let check = |val: u64, lo: i64, hi: i64| isec.check_range(ctx, rel, val as i64, lo, hi);

            // The GP-relative offset of a GOT entry. The load instruction
            // has a signed 16-bit displacement.
            let got_entry = |kind, sym: SymbolId, addend| {
                let v = got.entry_addr(ctx, part, GotKey { kind, sym, addend }).wrapping_sub(gp);
                check(v, -0x8000, 0x8000);
                v
            };

            match rel_type::<Self>(rel.r_type()) {
                R_MIPS_16 => {
                    check(sa, -0x8000, 0x10000);
                    Self::write_u16(loc, sa as u16);
                }
                R_MIPS_32 => Self::write_u32(loc, sa as u32),
                R_MIPS_26 => {
                    let dist = sa.wrapping_sub(p) as i64;
                    let sa = if Self::always_needs_thunk(ctx, isec, sym, rel)
                        || !(-Self::branch_distance()..Self::branch_distance()).contains(&dist)
                    {
                        sym.thunk_addr(ctx, p)
                    } else {
                        sa
                    };
                    // J and JAL replace the low 28 bits of the address of
                    // the delay slot instruction.
                    if (sa ^ p.wrapping_add(4)) & !0x0fff_ffff != 0 {
                        error!(
                            "{}: relocation {} against {} out of range: the destination is not in the same 256 MiB region",
                            isec.display(file),
                            rel.type_name::<Self>(),
                            sym
                        );
                    }
                    let insn = Self::read_u32(loc);
                    Self::write_u32(loc, (insn & 0xfc00_0000) | ((sa >> 2) as u32 & 0x03ff_ffff));
                }
                R_MIPS_HI16 if is_gp_disp => {
                    Self::write_imm16(loc, hi16(gp.wrapping_add(a).wrapping_sub(p)))
                }
                R_MIPS_LO16 if is_gp_disp => {
                    Self::write_imm16(loc, gp.wrapping_add(a).wrapping_sub(p).wrapping_add(4))
                }
                R_MIPS_HI16 => Self::write_imm16(loc, hi16(sa)),
                R_MIPS_LO16 => Self::write_imm16(loc, sa),
                R_MIPS_HIGHER => Self::write_imm16(loc, higher(sa)),
                R_MIPS_HIGHEST => Self::write_imm16(loc, highest(sa)),
                R_MIPS_GPREL16 | R_MIPS_LITERAL => {
                    let v = gprel();
                    check(v, -0x8000, 0x8000);
                    Self::write_imm16(loc, v);
                }
                R_MIPS_GPREL32 => Self::write_u32(loc, gprel() as u32),
                R_GPREL32_64 => Self::write_u64(loc, gprel()),
                R_GPREL16_SUB_HI16 => Self::write_imm16(loc, hi16(gprel().wrapping_neg())),
                R_GPREL16_SUB_LO16 => Self::write_imm16(loc, gprel().wrapping_neg()),
                R_MIPS_PC16 => {
                    let v = sa.wrapping_sub(p);
                    check(v, -(1 << 17), 1 << 17);
                    Self::write_imm16(loc, v >> 2);
                }
                R_MIPS_PC32 => Self::write_u32(loc, sa.wrapping_sub(p) as u32),
                R_MIPS_GOT_DISP | R_MIPS_CALL16 => {
                    Self::write_imm16(loc, got_entry(DISP, sym_id, a as i64))
                }
                R_MIPS_GOT16 => {
                    let kind = if is_local_ref(file, rel) { PAGE } else { DISP };
                    Self::write_imm16(loc, got_entry(kind, sym_id, a as i64));
                }
                R_MIPS_GOT_HI16 | R_MIPS_CALL_HI16 => {
                    let key = GotKey { kind: DISP, sym: sym_id, addend: a as i64 };
                    Self::write_imm16(loc, hi16(got.entry_addr(ctx, part, key).wrapping_sub(gp)));
                }
                R_MIPS_GOT_LO16 | R_MIPS_CALL_LO16 => {
                    let key = GotKey { kind: DISP, sym: sym_id, addend: a as i64 };
                    Self::write_imm16(loc, got.entry_addr(ctx, part, key).wrapping_sub(gp));
                }
                R_MIPS_GOT_PAGE => Self::write_imm16(loc, got_entry(PAGE, sym_id, a as i64)),
                R_MIPS_GOT_OFST => {
                    // An imported symbol's page entry holds its exact address.
                    let v = if sym.is_imported() { 0 } else { sa.wrapping_sub(page(sa)) };
                    Self::write_imm16(loc, v);
                }
                R_MIPS_JALR => {}
                R_MIPS_TLS_GD => Self::write_imm16(loc, got_entry(TLSGD, sym_id, 0)),
                R_MIPS_TLS_LDM => Self::write_imm16(loc, got_entry(TLSLD, SymbolId(0), 0)),
                R_MIPS_TLS_GOTTPREL => Self::write_imm16(loc, got_entry(GOTTP, sym_id, 0)),
                R_MIPS_TLS_DTPREL_HI16 => {
                    Self::write_imm16(loc, hi16(sa.wrapping_sub(ctx.dtp_addr)))
                }
                R_MIPS_TLS_DTPREL_LO16 => Self::write_imm16(loc, sa.wrapping_sub(ctx.dtp_addr)),
                R_MIPS_TLS_TPREL_HI16 => Self::write_imm16(loc, hi16(sa.wrapping_sub(ctx.tp_addr))),
                R_MIPS_TLS_TPREL_LO16 => Self::write_imm16(loc, sa.wrapping_sub(ctx.tp_addr)),
                R_MIPS_TLS_DTPREL32 => Self::write_u32(loc, sa.wrapping_sub(ctx.dtp_addr) as u32),
                R_MIPS_TLS_DTPREL64 => Self::write_u64(loc, sa.wrapping_sub(ctx.dtp_addr)),
                R_MIPS_TLS_TPREL32 => Self::write_u32(loc, sa.wrapping_sub(ctx.tp_addr) as u32),
                R_MIPS_TLS_TPREL64 => Self::write_u64(loc, sa.wrapping_sub(ctx.tp_addr)),
                _ => unreachable!("unexpected relocation {}", rel.type_name::<Self>()),
            }
        }
    }

    fn apply_reloc_nonalloc(ctx: &Context<Self>, isec: &InputSection<Self>, buf: &mut [u8]) {
        let mut fragment_cache = crate::input_sections::FragmentLookup::default();
        let file = &ctx.objs[isec.file.index()];
        for rel in isec.relocations(ctx) {
            let Some(NonAllocReloc { sym, s, a, frag }) =
                isec.resolve_nonalloc(ctx, file, &rel, &mut fragment_cache)
            else {
                continue;
            };
            let sa = s.wrapping_add(a);
            let loc = &mut buf[rel.r_offset() as usize..];

            match rel.r_type() {
                R_MIPS_32 => {
                    let v = isec.tombstone(ctx, sym, frag).unwrap_or(sa);
                    Self::write_u32(loc, v as u32);
                }
                R_MIPS_64 => Self::write_u64(loc, isec.tombstone(ctx, sym, frag).unwrap_or(sa)),
                R_MIPS_TLS_DTPREL32 => Self::write_u32(loc, sa.wrapping_sub(ctx.dtp_addr) as u32),
                R_MIPS_TLS_DTPREL64 => Self::write_u64(loc, sa.wrapping_sub(ctx.dtp_addr)),
                _ => fatal!(
                    "{}: invalid relocation for non-allocated sections: {}",
                    isec.display(file),
                    rel.type_name::<Self>()
                ),
            }
        }
    }

    fn finish_output(ctx: &Context<Self>, buf: &mut [u8]) {
        write_abiflags(ctx, buf);
    }
}

/// Reads the GP value an object file was created with from its
/// `.MIPS.options` (N64) or `.reginfo` (O32) section.
fn read_gp0<E: Target>(file: &ObjectFile<E>) -> u64 {
    for isec in file.input_sections() {
        let data = isec.contents();
        match isec.sh_type(file) {
            // Elf32_RegInfo: ri_gprmask, ri_cprmask[4], ri_gp_value
            SHT_MIPS_REGINFO if data.len() >= 24 => return E::read_i32(&data[20..]) as u64,
            // A list of Elf_Options records. ODK_REGINFO's Elf64_RegInfo is
            // ri_gprmask, ri_pad, ri_cprmask[4], ri_gp_value.
            SHT_MIPS_OPTIONS => {
                let mut rest = data;
                while rest.len() >= 8 && rest[1] != 0 {
                    let size = (rest[1] as usize).min(rest.len());
                    if rest[0] == ODK_REGINFO && size >= 40 {
                        return E::read_u64(&rest[32..]);
                    }
                    rest = &rest[size..];
                }
            }
            _ => {}
        }
    }
    0
}

const PLT_ENTRY_SIZE: u64 = 32;

/// Whether a relocation refers to a symbol local to its object file. A
/// symbol index past the file's symbol table refers to a section
/// fragment, which was a section symbol.
fn is_local_ref<E: Target>(file: &ObjectFile<E>, rel: &ElfRel<E>) -> bool {
    file.base.elf_syms.get(rel.r_sym() as usize).is_none_or(|esym| esym.st_bind() == STB_LOCAL)
}

//
// Conversion of O32 REL relocations to RELA
//

/// Computes the addends of O32 relocations, which live in the relocated
/// locations. The addend of a HI16-type relocation is split between its
/// own instruction and that of the next LO16-type relocation against the
/// same symbol (AHL in the psABI). Likewise, a LO16 relocation following
/// a HI16 one shares its high half.
pub fn decode_rel<E: Target>(
    rels: &[ElfRelNoAddend<E>],
    contents: &[u8],
    is_local: impl Fn(u32) -> bool,
) -> Box<[ElfRel<E>]> {
    // The type of the LO16-type relocation that completes a HI16-type one.
    let pair = |ty: u32| match ty {
        R_MIPS_HI16 | R_MIPS_GOT16 => Some(R_MIPS_LO16),
        R_MIPS_TLS_DTPREL_HI16 => Some(R_MIPS_TLS_DTPREL_LO16),
        R_MIPS_TLS_TPREL_HI16 => Some(R_MIPS_TLS_TPREL_LO16),
        _ => None,
    };
    let imm16 = |rel: &ElfRelNoAddend<E>| -> i64 {
        match contents.get(rel.r_offset() as usize..) {
            Some(loc) if loc.len() >= 4 => i64::from(E::read_u32(loc) as u16 as i16),
            _ => 0,
        }
    };

    // The high halves of the most recent HI16-type relocations, keyed
    // by symbol and LO16 type.
    let mut last_hi: Vec<(u32, u32, i64)> = Vec::new();

    let mut out = Vec::with_capacity(rels.len());
    for (i, rel) in rels.iter().enumerate() {
        let ty = rel.r_type();
        let loc = contents.get(rel.r_offset() as usize..).unwrap_or(&[]);
        let read32 = || if loc.len() >= 4 { i64::from(E::read_i32(loc)) } else { 0 };

        let addend = match ty {
            R_MIPS_32 | R_MIPS_REL32 | R_MIPS_GPREL32 | R_MIPS_PC32 | R_MIPS_TLS_DTPREL32
            | R_MIPS_TLS_TPREL32 => read32(),
            R_MIPS_16 => {
                if loc.len() >= 2 {
                    i64::from(E::read_u16(loc) as i16)
                } else {
                    0
                }
            }
            R_MIPS_26 => {
                // Sign-extend the 28-bit byte offset.
                let v = (read32() as u64 & 0x03ff_ffff) << 2;
                ((v << 36) as i64) >> 36
            }
            R_MIPS_PC16 => imm16(rel) << 2,
            // A GOT16 against a global symbol refers to a GOT entry of
            // its own and has no LO16 pair.
            R_MIPS_GOT16 if !is_local(rel.r_sym()) => imm16(rel),
            R_MIPS_HI16 | R_MIPS_GOT16 | R_MIPS_TLS_DTPREL_HI16 | R_MIPS_TLS_TPREL_HI16 => {
                let lo_ty = pair(ty).unwrap();
                let hi = imm16(rel) << 16;
                let lo = rels[i + 1..]
                    .iter()
                    .find(|r| r.r_type() == lo_ty && r.r_sym() == rel.r_sym())
                    .map_or(0, imm16);
                let ahl = (hi + lo) as i32 as i64;
                last_hi.retain(|&(sym, t, _)| (sym, t) != (rel.r_sym(), lo_ty));
                last_hi.push((rel.r_sym(), lo_ty, hi));
                ahl
            }
            R_MIPS_LO16 | R_MIPS_TLS_DTPREL_LO16 | R_MIPS_TLS_TPREL_LO16 => {
                let hi = last_hi
                    .iter()
                    .rev()
                    .find(|&&(sym, t, _)| sym == rel.r_sym() && t == ty)
                    .map_or(0, |&(_, _, hi)| hi);
                (hi + imm16(rel)) as i32 as i64
            }
            R_MIPS_GPREL16 | R_MIPS_LITERAL | R_MIPS_CALL16 | R_MIPS_GOT_DISP | R_MIPS_TLS_GD
            | R_MIPS_TLS_LDM | R_MIPS_TLS_GOTTPREL => imm16(rel),
            _ => 0,
        };
        out.push(ElfRel::<E>::new(rel.r_offset(), ty, rel.r_sym(), addend));
    }
    out.into_boxed_slice()
}

/// Merges the consecutive N32 relocation records that apply to the same
/// location into one. All but the first of them have no symbol. Returns
/// None if there is nothing to merge.
pub fn merge_n32_rels<E: Target>(
    file: &impl std::fmt::Display,
    rels: &[ElfRel<E>],
) -> Option<Box<[ElfRel<E>]>> {
    let follows = |a: &ElfRel<E>, b: &ElfRel<E>| b.r_offset() == a.r_offset() && b.r_sym() == 0;
    if !rels.windows(2).any(|w| follows(&w[0], &w[1])) {
        return None;
    }

    let mut out = Vec::with_capacity(rels.len());
    let mut i = 0;
    while i < rels.len() {
        let mut rel = rels[i];
        let mut ty = rel.r_type();
        i += 1;
        for shift in [8, 16] {
            if i < rels.len() && follows(&rel, &rels[i]) {
                ty |= rels[i].r_type() << shift;
                i += 1;
            }
        }
        rel.set_r_type(match ty {
            R_GPREL16_SUB_HI16 => R_N32_GPREL16_SUB_HI16,
            R_GPREL16_SUB_LO16 => R_N32_GPREL16_SUB_LO16,
            R_GPREL32_64 => R_N32_GPREL32_64,
            0..=0xff => ty,
            _ => fatal!(
                "{file}: unsupported relocation combination: {}",
                MipsTarget::<false, true>::rel_to_string(ty)
            ),
        });
        out.push(rel);
    }
    Some(out.into_boxed_slice())
}

//
// GOT
//

// Kinds of GOT entries, in the order they are laid out in a GOT. TLSGD and
// TLSLD entries take two words.
const DISP: u8 = 0; // The address of a symbol plus an addend
const PAGE: u8 = 1; // A 64 KiB-aligned page address for GOT_PAGE and O32's local GOT16
const GOTTP: u8 = 2; // The TP-relative offset of a TLS symbol
const TLSGD: u8 = 3; // The module ID and DTP-relative offset of a TLS symbol
const TLSLD: u8 = 4; // The module ID of this module

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct GotKey {
    kind: u8,
    sym: SymbolId,
    addend: i64,
}

impl GotKey {
    fn num_words(&self) -> u64 {
        if self.kind >= TLSGD { 2 } else { 1 }
    }
}

/// One GOT reachable from one GP value. Several input files may share one.
#[derive(Debug, Default)]
struct GotPart {
    /// Entries in the order they are laid out.
    keys: Vec<GotKey>,
    /// The word index of each entry relative to `offset`.
    index: HashMap<GotKey, u64>,
    /// Offset from the end of the GOT header, in words.
    offset: u64,
    num_words: u64,
}

impl GotPart {
    fn word_idx(&self, key: &GotKey) -> Option<u64> {
        Some(self.offset + self.index.get(key)?)
    }
}

/// The MIPS `.got`. It consists of the two words reserved for the dynamic
/// linker, a placeholder entry for each dynamic symbol (see the comment at
/// the top of this file), the GOTs of the input files and, for an
/// executable, a word in which the dynamic linker stores the address of
/// `r_debug` for debuggers (DT_MIPS_RLD_MAP_REL).
#[derive(Debug)]
pub struct MipsGot {
    /// GOT entries requested by each object file while relocations are
    /// scanned. Each file is scanned by one thread at a time.
    requests: Vec<Mutex<Vec<GotKey>>>,
    /// The index of the GOT of each object file.
    file_part: Vec<u32>,
    /// The GP value each object file was created with.
    gp0: Vec<u64>,
    parts: Vec<GotPart>,
    /// The number of words of all partitions.
    parts_words: u64,
    has_rld_map: bool,
}

/// The number of words reserved for the dynamic linker at the beginning of
/// `.got`. The dynamic linker writes the address of the lazy resolver to
/// the first one and the address of the link map to the second one.
pub const NUM_RESERVED: u64 = 2;

// A partition must fit in GP - 0x8000 to GP + 0x7fff.
const MAX_PART_SIZE: u64 = 0xfff0;

impl MipsGot {
    fn new(num_files: usize) -> Self {
        Self {
            requests: (0..num_files).map(|_| Mutex::new(Vec::new())).collect(),
            file_part: Vec::new(),
            gp0: vec![0; num_files],
            parts: Vec::new(),
            parts_words: 0,
            has_rld_map: false,
        }
    }

    /// The number of words before the first partition.
    fn header_words<E: Target>(ctx: &Context<E>) -> u64 {
        NUM_RESERVED + ctx.dynsym.symbols.len() as u64
    }

    fn part_addr<E: Target>(&self, ctx: &Context<E>, part: usize) -> u64 {
        let word = E::WORD_SIZE as u64;
        ctx.got.hdr.shdr.sh_addr.get() + (Self::header_words(ctx) + self.parts[part].offset) * word
    }

    /// The GP value of a partition. GP points 0x7ff0 bytes past the
    /// beginning of a GOT so that a signed 16-bit displacement can reach
    /// all of it.
    pub fn gp<E: Target>(&self, ctx: &Context<E>, part: usize) -> u64 {
        self.part_addr(ctx, part) + 0x7ff0
    }

    fn entry_addr<E: Target>(&self, ctx: &Context<E>, part: usize, key: GotKey) -> u64 {
        let word = E::WORD_SIZE as u64;
        // An entry is missing only for an undefined symbol, which has been
        // reported as an error.
        let Some(idx) = self.parts[part].word_idx(&key) else { return self.gp(ctx, part) };
        ctx.got.hdr.shdr.sh_addr.get() + (Self::header_words(ctx) + idx) * word
    }

    /// The address of the word for DT_MIPS_RLD_MAP_REL.
    pub fn rld_map_addr<E: Target>(&self, ctx: &Context<E>) -> Option<u64> {
        let word = E::WORD_SIZE as u64;
        self.has_rld_map.then(|| {
            ctx.got.hdr.shdr.sh_addr.get() + (Self::header_words(ctx) + self.parts_words) * word
        })
    }

    pub fn has_gottp(&self) -> bool {
        self.parts.iter().any(|p| p.keys.iter().any(|k| k.kind == GOTTP))
    }
}

/// Assigns GOTs to input files once their relocations are scanned.
/// Consecutive files share a GOT as long as it fits in 64 KiB.
pub fn finalize_got<E: Target>(ctx: &mut Context<E>) {
    let mut got = ctx.mips_got.take().unwrap();
    let word = E::WORD_SIZE as u64;
    let max_words = MAX_PART_SIZE / word;

    let mut file_part = vec![0; got.requests.len()];
    let mut parts: Vec<GotPart> = vec![GotPart::default()];
    let mut set: HashSet<GotKey> = HashSet::new();
    let mut words = 0;

    for file in &ctx.objs {
        let idx = file.id().index();
        let mut keys = std::mem::take(got.requests[idx].get_mut().unwrap());
        keys.sort_unstable();
        keys.dedup();

        // A file without GOT entries may use GP-relative small data, which
        // is relative to the primary GOT.
        if keys.is_empty() {
            continue;
        }
        let file_words: u64 = keys.iter().map(GotKey::num_words).sum();
        if file_words > max_words {
            error!("{file}: too many GOT entries; recompile with -mxgot");
        }
        let new_words: u64 = keys.iter().filter(|k| !set.contains(k)).map(GotKey::num_words).sum();
        if words + new_words > max_words {
            parts.last_mut().unwrap().keys = set.drain().collect();
            parts.push(GotPart::default());
            words = 0;
        }
        words += keys.iter().filter(|k| set.insert(**k)).map(GotKey::num_words).sum::<u64>();
        file_part[idx] = (parts.len() - 1) as u32;
    }
    parts.last_mut().unwrap().keys = set.drain().collect();

    let mut offset = 0;
    for part in &mut parts {
        // Symbol IDs depend on thread scheduling, so they don't give a
        // deterministic order.
        part.keys.sort_by_cached_key(|k| (k.kind, crate::thunks::sort_key(ctx, k.sym), k.addend));
        let mut words = 0;
        for key in &part.keys {
            part.index.insert(*key, words);
            words += key.num_words();
        }
        part.offset = offset;
        part.num_words = words;
        offset += words;
    }

    got.file_part = file_part;
    got.parts = parts;
    got.parts_words = offset;
    got.has_rld_map = ctx.dynamic.is_some() && !ctx.args.shared;
    ctx.mips_got = Some(got);
}

pub fn update_got_shdr<E: Target>(ctx: &mut Context<E>) {
    let Some(got) = &ctx.mips_got else { return };
    let words = MipsGot::header_words(ctx) + got.parts_words + u64::from(got.has_rld_map);
    ctx.got.hdr.shdr.sh_size.set(words * E::WORD_SIZE as u64);
}

/// Calls `emit` with the word index, value, dynamic relocation type and
/// dynamic symbol of each GOT entry of the input files' GOTs.
fn for_each_entry<E: Target>(
    ctx: &Context<E>,
    mut emit: impl FnMut(u64, u64, u32, Option<SymbolId>),
) {
    let got = ctx.mips_got.as_ref().unwrap();
    let header = MipsGot::header_words(ctx);

    for part in &got.parts {
        let mut idx = header + part.offset;
        for key in &part.keys {
            let sym = &ctx.symbols[key.sym];
            let a = key.addend as u64;
            let mut add = |val, r_type, sym| {
                emit(idx, val, r_type, sym);
                idx += 1;
            };

            match key.kind {
                DISP | PAGE => {
                    if sym.is_imported() {
                        add(a, E::R_GLOB_DAT, Some(key.sym));
                        continue;
                    }
                    let mut val = sym.addr_with(ctx, AddrFlags::NO_PLT).wrapping_add(a);
                    if key.kind == PAGE {
                        val = page(val);
                    }
                    if ctx.args.pic && sym.is_relative() {
                        add(val, E::R_RELATIVE, None);
                    } else {
                        add(val, R_NONE, None);
                    }
                }
                GOTTP => {
                    if sym.is_imported() {
                        add(0, E::R_TPOFF, Some(key.sym));
                    } else if ctx.args.shared {
                        add(sym.addr(ctx).wrapping_sub(ctx.tls_begin), E::R_TPOFF, None);
                    } else {
                        add(sym.addr(ctx).wrapping_sub(ctx.tp_addr), R_NONE, None);
                    }
                }
                TLSGD => {
                    if sym.is_imported() {
                        add(0, E::R_DTPMOD, Some(key.sym));
                        add(0, E::R_DTPOFF, Some(key.sym));
                    } else if ctx.args.shared {
                        add(0, E::R_DTPMOD, None);
                        add(sym.addr(ctx).wrapping_sub(ctx.dtp_addr), R_NONE, None);
                    } else {
                        add(1, R_NONE, None);
                        add(sym.addr(ctx).wrapping_sub(ctx.dtp_addr), R_NONE, None);
                    }
                }
                TLSLD => {
                    if ctx.args.shared {
                        add(0, E::R_DTPMOD, None);
                    } else {
                        add(1, R_NONE, None);
                    }
                    add(0, R_NONE, None);
                }
                _ => unreachable!(),
            }
        }
    }
}

// Counts the dynamic relocations for_each_entry emits without computing
// symbol addresses. The cases below must mirror for_each_entry.
pub fn num_dynrels<E: Target>(ctx: &Context<E>) -> u64 {
    let Some(got) = &ctx.mips_got else { return 0 };
    let mut n = 0;
    for part in &got.parts {
        for key in &part.keys {
            let sym = &ctx.symbols[key.sym];
            n += match key.kind {
                DISP | PAGE => (sym.is_imported() || (ctx.args.pic && sym.is_relative())) as u64,
                GOTTP => (sym.is_imported() || ctx.args.shared) as u64,
                TLSGD if sym.is_imported() => 2,
                TLSGD | TLSLD => ctx.args.shared as u64,
                _ => unreachable!(),
            };
        }
    }
    n
}

pub fn write_dynrels<E: Target>(ctx: &Context<E>, out: &mut [DynRel<E>]) {
    let addr = ctx.got.hdr.shdr.sh_addr.get();
    let word = E::WORD_SIZE as u64;
    let mut i = 0;
    for_each_entry(ctx, |idx, val, r_type, sym| {
        if r_type != R_NONE {
            let dynsym_idx = sym.and_then(|s| ctx.symbols[s].dynsym_idx(&ctx.symbols));
            out[i] =
                DynRel::<E>::new(addr + idx * word, r_type, dynsym_idx.unwrap_or(0), val as i64);
            i += 1;
        }
    });
    debug_assert_eq!(i, out.len());
}

pub fn copy_got<E: Target>(ctx: &Context<E>, buf: &mut [u8]) {
    buf.fill(0);
    let w = E::WORD_SIZE;
    let write = |buf: &mut [u8], idx: u64, val: u64| {
        Word::<E>::new(val).write(&mut buf[idx as usize * w..]);
    };

    // The most significant bit of GOT[1] tells the dynamic linker that
    // the second word is reserved too.
    write(buf, 1, 1 << (w * 8 - 1));

    // The dynamic linker computes the initial values of the placeholder
    // entries of functions under lazy binding by adding the load bias to
    // their link-time addresses.
    for (i, sym) in ctx.dynsym.symbols.iter().enumerate() {
        let Some(id) = *sym else { continue };
        let sym = &ctx.symbols[id];
        if matches!(sym.file(), Some(FileId::Obj(_))) && !sym.is_undef() {
            write(buf, NUM_RESERVED + i as u64, sym.addr_with(ctx, AddrFlags::NO_PLT));
        }
    }

    // Addends of REL-type dynamic relocations are in the relocated words.
    for_each_entry(ctx, |idx, val, _, _| write(buf, idx, val));
}

//
// .dynamic
//

/// Calls `define` with the MIPS-specific dynamic tags. `entry_addr` is the
/// address of the next .dynamic entry.
pub fn dynamic_tags<E: Target>(
    ctx: &Context<E>,
    entry_addr: u64,
    mut define: impl FnMut(u32, u64),
) {
    let ndynsym = ctx.dynsym.symbols.len() as u64;
    define(DT_MIPS_RLD_VERSION, 1);
    define(DT_MIPS_FLAGS, 0);
    define(DT_MIPS_BASE_ADDRESS, ctx.args.image_base);
    define(DT_MIPS_LOCAL_GOTNO, NUM_RESERVED);
    define(DT_MIPS_SYMTABNO, ndynsym);
    define(DT_MIPS_GOTSYM, 0);
    if !ctx.plt.symbols.is_empty() {
        define(DT_MIPS_PLTGOT, ctx.gotplt.shdr.sh_addr.get());
    }
    if let Some(addr) = ctx.mips_got.as_ref().and_then(|got| got.rld_map_addr(ctx)) {
        // The offset is relative to the .dynamic entry itself.
        let n = if ctx.plt.symbols.is_empty() { 6 } else { 7 };
        let entry_size = size_of::<ElfDyn<E>>() as u64;
        define(DT_MIPS_RLD_MAP_REL, addr.wrapping_sub(entry_addr + n * entry_size));
    }
}

//
// .eh_frame
//

/// Rewrites absolute pointer encodings in a CIE written to `buf` to
/// PC-relative ones. MIPS compilers use absolute pointers in `.eh_frame`
/// even for position-independent code, which would require dynamic
/// relocations in a read-only section. apply_eh_reloc() writes PC-relative
/// values accordingly.
pub fn rewrite_cie<E: Target>(buf: &mut [u8]) {
    // Skip Length, CIE ID and Version fields
    let version = buf[8];
    let mut p = 9;
    let aug_len = buf[p..].iter().position(|&b| b == 0).unwrap_or(0);
    let aug = buf[p..p + aug_len].to_vec();
    p += aug_len + 1;
    if aug.first() != Some(&b'z') {
        return;
    }

    let skip_leb = |p: &mut usize| {
        while buf[*p] & 0x80 != 0 {
            *p += 1;
        }
        *p += 1;
    };
    skip_leb(&mut p); // Code Alignment Factor
    skip_leb(&mut p); // Data Alignment Factor
    if version == 1 {
        p += 1; // Return Address Register
    } else {
        skip_leb(&mut p);
    }
    skip_leb(&mut p); // Augmentation Data Length

    // Returns the size of an encoded pointer, rewriting an absolute
    // encoding to a PC-relative one.
    let rewrite = |enc: &mut u8| -> usize {
        let format = *enc as u32 & 0xf;
        let size = if format == DW_EH_PE_absptr {
            E::WORD_SIZE
        } else if format == DW_EH_PE_udata4 || format == DW_EH_PE_sdata4 {
            4
        } else if format == DW_EH_PE_udata8 || format == DW_EH_PE_sdata8 {
            8
        } else {
            return 0;
        };
        if *enc as u32 & 0x70 == DW_EH_PE_absptr {
            let ty = if size == 4 { DW_EH_PE_sdata4 } else { DW_EH_PE_sdata8 };
            *enc = (*enc & 0x80) | (DW_EH_PE_pcrel | ty) as u8;
        }
        size
    };

    for &c in &aug[1..] {
        match c {
            b'L' | b'R' => {
                rewrite(&mut buf[p]);
                p += 1;
            }
            b'P' => {
                let size = rewrite(&mut buf[p]);
                p += size + 1;
            }
            _ => {}
        }
    }
}

//
// ELF header flags and .MIPS.abiflags
//

fn merge_eflags<E: Target>(ctx: &Context<E>) -> u32 {
    let internal = ctx.internal_obj;
    let mut objs = ctx.objs.iter().filter(|file| Some(file.id()) != internal);
    let Some(first) = objs.next() else { return 0 };
    let mut ret = first.base.e_flags;

    // ISA levels in increasing order, for the 32-bit and 64-bit variants.
    // The R6 architectures are not compatible with the older ones.
    let rank = |arch: u32| match arch >> 28 {
        0 => 0,      // MIPS I
        1 => 1,      // MIPS II
        2 => 2,      // MIPS III
        3 => 3,      // MIPS IV
        4 => 4,      // MIPS V
        5 => 3,      // MIPS32
        7 => 4,      // MIPS32R2
        6 => 5,      // MIPS64
        8 => 6,      // MIPS64R2
        9 | 10 => 7, // R6
        _ => 0,
    };

    for file in objs {
        let flags = file.base.e_flags;

        if flags & EF_MIPS_ABI != ret & EF_MIPS_ABI || flags & EF_MIPS_ABI2 != ret & EF_MIPS_ABI2 {
            error!("{file}: ABI is incompatible with {first}");
        }
        if flags & EF_MIPS_NAN2008 != ret & EF_MIPS_NAN2008 {
            error!("{file}: -mnan setting is incompatible with {first}");
        }

        // The output is PIC only if all inputs are.
        ret &= !(EF_MIPS_PIC | EF_MIPS_CPIC) | (flags & (EF_MIPS_PIC | EF_MIPS_CPIC));
        ret |= flags & (EF_MIPS_NOREORDER | EF_MIPS_FP64 | EF_MIPS_ARCH_ASE);

        let (arch, cur) = (flags & EF_MIPS_ARCH, ret & EF_MIPS_ARCH);
        if (arch >= EF_MIPS_ARCH_32R6) != (cur >= EF_MIPS_ARCH_32R6) && arch != cur {
            error!("{file}: ISA is incompatible with {first}");
        }
        if rank(arch) > rank(cur) || (rank(arch) == rank(cur) && arch > cur) {
            ret = (ret & !EF_MIPS_ARCH) | arch;
        }
        // Later Octeon models are supersets of earlier ones.
        let is_octeon = |mach: u32| matches!(mach, 0x008b_0000 | 0x008d_0000 | 0x008e_0000);
        let (mach, cur) = (flags & EF_MIPS_MACH, ret & EF_MIPS_MACH);
        if cur == 0 || (is_octeon(mach) && is_octeon(cur) && mach > cur) {
            ret = (ret & !EF_MIPS_MACH) | mach;
        }
    }
    ret
}

// .MIPS.abiflags record fields
const ABIFLAGS_SIZE: usize = 24;
const FP_ABI_ANY: u8 = 0;
const FP_ABI_DOUBLE: u8 = 1;
const FP_ABI_XX: u8 = 5;
const FP_ABI_64: u8 = 6;
const FP_ABI_64A: u8 = 7;

/// Merges the input `.MIPS.abiflags` records into the one that
/// rewrite_input_sections() kept.
fn write_abiflags<E: Target>(ctx: &Context<E>, buf: &mut [u8]) {
    let Some(id) = ctx.find_chunk_by_name(b".MIPS.abiflags") else { return };
    let shdr = &ctx.chunk_header(id).shdr;
    if shdr.sh_size.get() < ABIFLAGS_SIZE as u64 || shdr.sh_type.get() == SHT_NOBITS {
        return;
    }

    let mut out: Option<[u8; ABIFLAGS_SIZE]> = None;
    for file in &ctx.objs {
        for isec in file.input_sections() {
            if isec.sh_type(file) != SHT_MIPS_ABIFLAGS || isec.contents().len() < ABIFLAGS_SIZE {
                continue;
            }
            let rec = &isec.contents()[..ABIFLAGS_SIZE];
            let Some(out) = out.as_mut() else {
                out = Some(rec.try_into().unwrap());
                continue;
            };

            // ISA level and revision, register sizes
            if (rec[2], rec[3]) > (out[2], out[3]) {
                out[2] = rec[2];
                out[3] = rec[3];
            }
            for i in 4..7 {
                out[i] = out[i].max(rec[i]);
            }

            // Floating-point ABI. FPXX is compatible with DOUBLE, 64 and 64A.
            let (cur, fp) = (out[7], rec[7]);
            out[7] = match (cur, fp) {
                _ if cur == fp => cur,
                (FP_ABI_ANY, _) => fp,
                (_, FP_ABI_ANY) => cur,
                (FP_ABI_XX, FP_ABI_DOUBLE | FP_ABI_64 | FP_ABI_64A) => fp,
                (FP_ABI_DOUBLE | FP_ABI_64 | FP_ABI_64A, FP_ABI_XX) => cur,
                _ => {
                    warn!("{file}: floating-point ABI is incompatible with other input files");
                    cur
                }
            };

            // ISA extension, ASEs and flags1
            if E::read_u32(&out[8..]) == 0 {
                out[8..12].copy_from_slice(&rec[8..12]);
            }
            for i in [12, 16] {
                let v = E::read_u32(&out[i..]) | E::read_u32(&rec[i..]);
                E::write_u32(&mut out[i..], v);
            }
        }
    }

    if let Some(out) = out {
        let off = shdr.sh_offset.get() as usize;
        buf[off..off + ABIFLAGS_SIZE].copy_from_slice(&out);
    }
}
