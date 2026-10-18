#!/usr/bin/env bash
. $(dirname $0)/common.inc

# GCC for MIPS emits PIC code even with -fno-PIC.
[[ $MACHINE = mips* ]] && skip

[ $MACHINE = ppc64 ] && skip
[ $MACHINE = ppc64le ] && skip
[[ $MACHINE = loongarch* ]] && skip

cat <<EOF | $CC -o $t/a.o -c -xc -fno-PIE -
extern int foo;

int main() {
  return foo;
}
EOF

cat <<EOF | $CC -shared -o $t/b.so -xc -
__attribute__((visibility("protected"))) int foo;
EOF

not $CC -B. $t/a.o $t/b.so -o $t/exe -no-pie |&
  grep -F 'cannot create a copy relocation for protected symbol'
