#!/usr/bin/env bash
. $(dirname $0)/common.inc

# Without a .plt, _PROCEDURE_LINKAGE_TABLE_ must not be left undefined.
cat <<EOF | $CC -c -o $t/a.o -xc -
void _start() {}
EOF

$CC -B. -nostdlib -static -o $t/exe $t/a.o
readelf -W --symbols $t/exe | not grep -E 'UND _PROCEDURE_LINKAGE_TABLE_'
