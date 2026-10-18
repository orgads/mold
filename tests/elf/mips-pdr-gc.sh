#!/usr/bin/env bash
. $(dirname $0)/common.inc

[[ $MACHINE = mips* ]] || skip

# Nothing refers to .pdr, so --gc-sections removes it, as in GNU ld.
cat <<EOF | $CC -c -o $t/a.o -xc -
int main() { return 0; }
EOF

readelf -S $t/a.o | grep -F .pdr || skip

$CC -B. -o $t/exe1 $t/a.o
readelf -S $t/exe1 | grep -F .pdr

$CC -B. -o $t/exe2 $t/a.o -Wl,--gc-sections
readelf -S $t/exe2 | not grep -F .pdr
