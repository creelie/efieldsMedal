#!/usr/bin/env bash
# run_all.sh -- re-run every check of "Regular Morley tetrahedra from p-secting planes".
#
#   C       verification/c/morley.c               long double: Examples 1.5 and 1.6, Lemma 2.4 on
#                                                 random isosceles tetrahedra, Theorem 1.3(b) on random
#                                                 points of the four lines, Lemma 2.1
#   C++     verification/cpp/exact.cpp            exact arithmetic in Q and Q(sqrt 105): Section 3,
#                                                 Examples 1.5 and 1.6, the case analysis of Theorem 1.7
#                                                 for all integer shapes 1 <= alpha, beta, gamma <= 60
#   Shell   verification/shell/check_examples.sh  bc at 60 digits: the closed-form parameters of
#                                                 Examples 1.5 and 1.6
#   Python  verification/python/verify_morley.py  the construction straight from Definition 1.1:
#                                                 Lemmas 2.1, 2.2, 2.4, Proposition 2.3, Remark 2.5,
#                                                 Theorem 1.3, Corollary 1.4, Lemma 3.1, the examples
#   Julia   verification/julia/verify_morley.jl   256-bit BigFloat: the examples to 70 digits,
#                                                 Proposition 2.3, Theorem 1.3, Theorem 1.7 on a grid
#                                                 (if julia is on PATH or $JULIA is set)
#   Lean    verification/lean/                    Lean 4 + Mathlib v4.34.1: every statement of the
#                                                 paper, no sorry; Check.lean audits the axioms of all
#                                                 theorems (if lake is on PATH; LEAN=0 skips it)
#
# Exit status 0 means every check that ran passed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
V="$ROOT/verification"
BUILD="$ROOT/build"
mkdir -p "$BUILD"
FAILED=0
fail() { echo "FAIL: $*"; FAILED=1; }
ok() { echo "ok:   $*"; }
allok() { tail -n 1 "$1" | grep -q '^ALL OK$'; }

echo "== C and C++"
cc -O2 -Wall -o "$BUILD/morley" "$V/c/morley.c" -lm || fail "compile morley.c"
c++ -O2 -Wall -std=c++17 -o "$BUILD/exact" "$V/cpp/exact.cpp" || fail "compile exact.cpp"
"$BUILD/morley" > "$BUILD/c.txt" 2>&1 && allok "$BUILD/c.txt" && ok "morley.c" || fail "morley.c (see build/c.txt)"
"$BUILD/exact" > "$BUILD/cpp.txt" 2>&1 && allok "$BUILD/cpp.txt" && ok "exact.cpp" || fail "exact.cpp (see build/cpp.txt)"

echo "== Shell"
bash "$V/shell/check_examples.sh" > "$BUILD/sh.txt" 2>&1 && allok "$BUILD/sh.txt" \
  && ok "check_examples.sh" || fail "check_examples.sh (see build/sh.txt)"

echo "== Python"
python3 "$V/python/verify_morley.py" > "$BUILD/py.txt" 2>&1 && allok "$BUILD/py.txt" \
  && ok "verify_morley.py" || fail "verify_morley.py (see build/py.txt)"

echo "== Julia"
JULIA="${JULIA:-$(command -v julia || true)}"
if [ -z "$JULIA" ]; then echo "julia not found: skipping"; else
  "$JULIA" "$V/julia/verify_morley.jl" > "$BUILD/jl.txt" 2>&1 && allok "$BUILD/jl.txt" \
    && ok "verify_morley.jl" || fail "verify_morley.jl (see build/jl.txt)"
fi

echo "== Lean"
if [ "${LEAN:-1}" = 0 ] || ! command -v lake > /dev/null; then echo "lake not found or LEAN=0: skipping"; else
  out=$(cd "$V/lean" && lake build 2>&1 && lake env lean Check.lean 2>&1); st=$?
  echo "$out" > "$BUILD/lean.txt"
  if [ $st -eq 0 ] && ! grep -q "error\|declaration uses 'sorry'\|sorryAx" <<< "$out" \
       && grep -q "axiom audit: .* theorems, all within propext, Classical.choice, Quot.sound" <<< "$out" \
       && grep -q "'Morley.tran_false' depends on axioms: \[propext, Classical.choice, Quot.sound\]" <<< "$out"; then
    ok "Lean: $(grep -o 'axiom audit: [0-9]* theorems' <<< "$out"), tran_false kernel-checked"
  else fail "Lean (see build/lean.txt)"; fi
fi

if [ $FAILED -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "SOME CHECKS FAILED"; fi
exit $FAILED
