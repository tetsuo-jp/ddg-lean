#!/usr/bin/env bash
# Trust conditions for this repository.  Fails closed.
set -uo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
AUDIT_LOG="${AUDIT_LOG:-/work/tmp/ddg-audit.log}"
mkdir -p "$(dirname "$AUDIT_LOG")"
rc=0
fail() { echo "AUDIT FAIL: $*"; rc=1; }

echo "== 1. build =="
lake build Challenge Solution Audit CotanChallenge CotanSolution CotanAudit \
  ForestChallenge ForestSolution ForestAudit \
  >"$AUDIT_LOG" 2>&1 \
  || fail "lake build failed (see $AUDIT_LOG)"
for m in Challenge Solution CotanChallenge CotanSolution ForestChallenge ForestSolution; do
  [ -f ".lake/build/lib/lean/$m.olean" ] || fail "$m.olean was not produced"
done

echo "== 2. permitted axioms only =="
if grep -q "depends on axioms" $AUDIT_LOG; then
  if grep "depends on axioms" "$AUDIT_LOG" \
     | grep -vE "\[propext, Classical\.choice, Quot\.sound\]"; then
    fail "a claimed theorem uses an axiom outside the permitted set"
  fi
else
  fail "no axiom report found; Audit.lean did not run"
fi

echo "== 3. no cheats =="
for m in Solution.lean CotanSolution.lean ForestSolution.lean; do
  grep -nE "sorry|native_decide|unsafe |^axiom " "$m" && fail "$m contains a cheat"
done
for pair in Challenge.lean:4 CotanChallenge.lean:7 ForestChallenge.lean:1; do
  f=${pair%%:*}; want=${pair##*:}; n=$(grep -c "^  sorry$" "$f")
  [ "$n" = "$want" ] || fail "$f should hold exactly $want deliberate sorry holes, found $n"
done

echo "== 4. claimed theorems agree between Challenge and Solution =="
for t in three_mul_card_faces sum_defect_eq_two_pi_mul_euler \
         card_edges_tetrahedron sum_defect_tetrahedron; do
  grep -q "theorem $t" Challenge.lean || fail "$t missing from Challenge.lean"
  grep -q "theorem $t" Solution.lean  || fail "$t missing from Solution.lean"
done
for t in gram_two inner_form cot_angle_mul_abs_cross cotan_form \
         corner_pair_inner corner_pair linear_precision; do
  grep -q "theorem $t" CotanChallenge.lean || fail "$t missing from CotanChallenge.lean"
  grep -q "theorem $t" CotanSolution.lean  || fail "$t missing from CotanSolution.lean"
done
grep -q "theorem exists_good_weights" ForestChallenge.lean || fail "exists_good_weights missing from ForestChallenge.lean"
grep -q "theorem exists_good_weights" ForestSolution.lean  || fail "exists_good_weights missing from ForestSolution.lean"

echo "== 5. mutation test =="
python3 scripts/mutation_test.py || fail "mutation test (Gauss-Bonnet) failed"
python3 scripts/mutation_test_cotan.py || fail "mutation test (cotangent) failed"
python3 scripts/mutation_test_forest.py || fail "mutation test (forest) failed"

[ $rc = 0 ] && echo "AUDIT OK" || echo "AUDIT FAILED"
exit $rc
