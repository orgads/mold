#!/usr/bin/env bash
. $(dirname $0)/common.inc

[[ $MACHINE = mips* ]] || skip

# A PIC function computes its GP value from its own address in t9, which
# JAL from non-PIC code doesn't set, so such calls go through a thunk.
cat <<EOF | $CC -fPIC -c -o $t/a.o -xc -
int x = 42;
int get_x(void) { return x; }
EOF

# -G0 because GP doesn't point to our small data when libc calls main().
cat <<EOF | $CC -fno-pic -mno-abicalls -G0 -c -o $t/b.o -xc -
#include <stdio.h>
int get_x(void);
int main() { printf("%d\n", get_x()); }
EOF

readelf -h $t/b.o | grep Flags | not grep -w pic

$CC -B. -no-pie -o $t/exe1 $t/a.o $t/b.o
$QEMU $t/exe1 | grep '^42$'
$OBJDUMP -d $t/exe1 | grep -E 'jal.*<get_x\$thunk'

$CC -B. -static -o $t/exe2 $t/a.o $t/b.o
$QEMU $t/exe2 | grep '^42$'
