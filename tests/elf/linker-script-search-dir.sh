#!/usr/bin/env bash
. $(dirname $0)/common.inc

cat <<EOF | $CC -o $t/a.o -c -xc -
int foo() { return 3; }
EOF

mkdir -p $t/lib
rm -f $t/lib/libfoo.a
ar rcs $t/lib/libfoo.a $t/a.o

cat <<EOF | $CC -o $t/b.o -c -xc -
#include <stdio.h>
int foo();
int main() { printf("%d\n", foo()); }
EOF

cat <<EOF > $t/script
SEARCH_DIR("$t/lib")
EOF

$CC -B. -o $t/exe $t/b.o -lfoo -Wl,-T,$t/script
$QEMU $t/exe | grep -q '^3$'
