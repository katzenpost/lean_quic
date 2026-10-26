#!/usr/bin/env bash
# Print the axioms behind every theorem written in LeanQUIC and fail on anything beyond Lean's own
# (propext, Classical.choice, Quot.sound).
set -euo pipefail
cd "$(dirname "$0")/.."
tmp=$(mktemp -p "${TMPDIR:-.}" --suffix=.lean)
trap 'rm -f "$tmp"' EXIT
cat >"$tmp" <<'LEAN'
import LeanQUIC
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut names := #[]
  for (n, ci) in env.constants.toList do
    if let .thmInfo _ := ci then
      if let some m := env.getModuleIdxFor? n then
        if (env.header.moduleNames[m.toNat]!).getRoot == `LeanQUIC && !n.isInternal then
          -- Only theorems written in the source, not generated equations and injectivity lemmas.
          if (← findDeclarationRanges? n).isSome then
            names := names.push n
  for n in names.qsort (·.toString < ·.toString) do
    let axs ← collectAxioms n
    IO.println s!"{n}: {axs.qsort (·.toString < ·.toString) |>.toList}"
LEAN
out=$(lake env lean "$tmp" 2>&1)
echo "$out"
allowed='propext\|Classical.choice\|Quot.sound'
if grep -v ": \[\(\($allowed\)\(, \($allowed\)\)*\)\?\]$" <<<"$out" | grep -q .; then
  echo "FAIL: a theorem depends on an unexpected axiom" >&2
  exit 1
fi
echo "$(wc -l <<<"$out") theorems, no unexpected axioms"
