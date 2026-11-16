#!/usr/bin/env bash
# Checks the Lean files added with pandroots 0.13.0 and 0.14.0 and prints the axioms of their theorems.
# Run from the root of the repository, with the Mathlib cache of the repository in place:
#   bash paper/g8/validation/pandroots/verification/lean/check_0_14_0.sh
# These files are not part of `lake build`: each one is checked by itself with `lake env lean`.
set -uo pipefail
dir=paper/g8/validation/pandroots/verification/lean
status=0
check() {
  local file=$1 ns=$2; shift 2
  echo "== request: check $file (lake env lean)"
  if lake env lean "$dir/$file"; then echo "exit 0"; else echo "exit $?"; status=1; fi
  echo "== request: axioms of the theorems of $file"
  local tmp; tmp=$(mktemp --suffix=.lean)
  cat "$dir/$file" > "$tmp"
  for t in "$@"; do echo "#print axioms $ns.$t" >> "$tmp"; done
  local out; out=$(lake env lean "$tmp" 2>&1); local rc=$?
  echo "$out" | grep -E "depends on axioms|does not depend on any axioms|error" || true
  echo "exit $rc"
  if [ $rc -ne 0 ] || echo "$out" | grep -q "sorryAx"; then status=1; fi
  local n; n=$(echo "$out" | grep -cE "depends on axioms|does not depend on any axioms")
  if [ "$n" -ne "$#" ]; then echo "expected $# audited theorems, found $n"; status=1; fi
  if echo "$out" | grep "depends on axioms" | sed 's/.*\[//; s/\].*//' | tr ',' '\n' | sed 's/ //g' | grep -vE '^(propext|Classical\.choice|Quot\.sound|)$' | grep -q .; then echo "unexpected axiom"; status=1; fi
  rm -f "$tmp"
}
lean --version
check CertificateGap.lean LeanMath.Papers.CertificateGap div_le_div_gap sum_div_le sum_div_sq_le quick_test
check SparseHorner.lean LeanMath.Papers.SparseHorner zero_steps gap_step q1_succ two_q2 value_alone comp_bound
check TwoComplement.lean LeanMath.Papers.TwoComplement shift_floor scaled_shift step_value limb_of_shift limb_of_shift_pow
exit $status
