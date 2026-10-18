#!/usr/bin/env bash
. $(dirname $0)/common.inc

[[ $MACHINE = mips || $MACHINE = mipsel ]] || skip
command -v perl > /dev/null || skip

# Old binutils exported the linker-defined _gp_disp from O32 DSOs as an
# SHN_ABS definition with version index 0 (libgcc_s.so.1 of gcc 4.8
# toolchains). Make such a DSO from an absolute symbol of the same length.
cat <<EOF | $CC -fPIC -c -o $t/a.o -xc -
int foo(void) { return 42; }
EOF

cat <<EOF | $CC -c -o $t/b.o -xassembler -
.globl _gp_dis0
_gp_dis0 = 0x1234
EOF

echo 'VER1 { global: *; };' > $t/a.ver
$CC -B. -shared -o $t/c.so $t/a.o $t/b.o -Wl,--version-script=$t/a.ver
perl -i -0777 -pe 's/_gp_dis0/_gp_disp/g' $t/c.so

idx=$(readelf -W --dyn-syms $t/c.so | awk '$8 ~ /^_gp_disp(@|$)/ { sub(":", "", $1); print $1 }')
off=$(readelf -WS $t/c.so | sed -n 's/.*\.gnu\.version  *VERSYM  *[0-9a-f]*  *\([0-9a-f]*\) .*/\1/p')
printf '\0\0' | dd of=$t/c.so bs=1 seek=$((0x$off + idx * 2)) conv=notrunc status=none
readelf -W --dyn-syms $t/c.so | grep -E 'ABS _gp_disp$'

cat <<EOF | $CC -fPIC -c -o $t/d.o -xc -
#include <stdio.h>
int foo(void);
int main() { printf("%d\n", foo()); }
EOF

# The patched DSO does not load (its _gp_disp is in the global GOT, now
# without a definition), so only the link is checked.
$CC -B. -o $t/exe $t/d.o $t/c.so
readelf -W --dyn-syms $t/exe | not grep -w _gp_disp
