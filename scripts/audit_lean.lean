import XZMathieuSU2Counterexamples
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required := [``XZMathieuSU2Counterexamples.basic_xz,
    ``XZMathieuSU2Counterexamples.circuit_family,
    ``XZMathieuSU2Counterexamples.all_mixed_xz,
    ``XZMathieuSU2Counterexamples.integral_eq_interval_circle,
    ``XZMathieuSU2Counterexamples.multiIntegral_eq_product,
    ``XZMathieuSU2Counterexamples.Hopf.su2_integration_formula,
    ``XZMathieuSU2Counterexamples.Hopf.su2_counterexample,
    ``XZMathieuSU2Counterexamples.Hopf.SU2_not_mathieu,
    ``XZMathieuSU2Counterexamples.Hopf.small_pair]
  for name in required do
    unless (env.find? name).any (·.isTheorem) do
      throwError "Missing release theorem {name}"
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, ci) in env.constants.toList do
    if (`XZMathieuSU2Counterexamples).isPrefixOf name then
      declarations := declarations + 1
      if ci.isTheorem then theorems := theorems + 1
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Audited {declarations} project declarations ({theorems} theorems): only propext, Classical.choice, Quot.sound."
