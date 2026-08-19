#!/usr/bin/env bash
# Trust conditions for this repository.  Fails closed.
set -uo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
rc=0
fail() { echo "AUDIT FAIL: $*"; rc=1; }

echo "== 1. build =="
lake build Challenge Solution Audit >/tmp/ddg-audit.log 2>&1 \
  || fail "lake build failed (see /tmp/ddg-audit.log)"
for m in Challenge Solution; do
  [ -f ".lake/build/lib/lean/$m.olean" ] || fail "$m.olean was not produced"
done

echo "== 2. permitted axioms only =="
if grep -q "depends on axioms" /tmp/ddg-audit.log; then
  if grep "depends on axioms" /tmp/ddg-audit.log \
     | grep -vE "\[propext, Classical\.choice, Quot\.sound\]"; then
    fail "a claimed theorem uses an axiom outside the permitted set"
  fi
else
  fail "no axiom report found; Audit.lean did not run"
fi

echo "== 3. no cheats =="
grep -nE "sorry|native_decide|unsafe |^axiom " Solution.lean && \
  fail "Solution.lean contains a cheat"
n=$(grep -c "^  sorry$" Challenge.lean)
[ "$n" = "4" ] || fail "Challenge.lean should hold exactly 4 deliberate sorry holes, found $n"

echo "== 4. claimed theorems agree between Challenge and Solution =="
for t in three_mul_card_faces sum_defect_eq_two_pi_mul_euler \
         card_edges_tetrahedron sum_defect_tetrahedron; do
  grep -q "theorem $t" Challenge.lean || fail "$t missing from Challenge.lean"
  grep -q "theorem $t" Solution.lean  || fail "$t missing from Solution.lean"
done

echo "== 5. mutation test =="
python3 scripts/mutation_test.py || fail "mutation test failed"

[ $rc = 0 ] && echo "AUDIT OK" || echo "AUDIT FAILED"
exit $rc
