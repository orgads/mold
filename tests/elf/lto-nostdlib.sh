#!/usr/bin/env bash
. $(dirname $0)/common.inc

# The entry point of MIPS is __start.
[[ $MACHINE = mips* ]] && skip

test_cflags -flto || skip

cat <<EOF | $CC -flto -c -o $t/a.o -xc -
void _start() {}
EOF

$CC -B. -o $t/exe -flto $t/a.o -nostdlib
readelf -Ws $t/exe | grep -E ' _start'
