#!/usr/bin/env bash
. $(dirname $0)/common.inc

# The N32 tests use Clang under the name of GCC.
$GXX --version | grep -q clang && skip

# ppc64v1 reports a bad .opd relocation before reaching this error.
[ $MACHINE = ppc64 ] && skip
command -v $GXX >& /dev/null || skip

# GCC puts all destructor variants in one COMDAT group, unlike Clang.
cat <<'EOF' | $GXX -fPIC -c -o $t/a.o -xc++ -
struct Foo { ~Foo() {} };
Foo a;
EOF

cat <<'EOF' | $GXX -fPIC -c -o $t/b.o -xc++ -
struct Foo { virtual ~Foo() {} };
Foo b;
EOF

{ ./mold -shared -o $t/c.so $t/a.o $t/b.o 2>&1; [ $? = 1 ]; } |
  grep -F ">>> prevailing definition is in $t/a.o"
