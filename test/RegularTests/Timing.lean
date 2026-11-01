/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Eval

public section

open Lean Elab Command Meta

/-- `#linear p` decides `p n` for each `n` in `sizes`, by `decide +kernel` and by evaluating
`decide (p n)` in compiled code, and fails if either takes longer than `n / 100 + 2` units. A unit
is the time the kernel takes to reduce a fixed term, measured alongside, so that the budget holds
on a slower machine. -/
syntax (name := linear) "#linear " ident : command

meta def sizes : List Nat := [25, 50, 100, 200, 1000]

meta def timeNanos (k : CommandElabM Unit) : CommandElabM Nat := do
  let t₀ ← IO.monoNanosNow
  k
  return (← IO.monoNanosNow) - t₀

meta def unitNanos : CommandElabM Nat := do
  let once := timeNanos do
    elabCommand (← `(example : (List.replicate 1000 true).all id = true := by decide +kernel))
  return min (← once) (min (← once) (← once))

meta def evalDecide (p : Term) : CommandElabM Bool := liftTermElabM do
  let e ← Term.elabTermEnsuringType (← `(decide $p)) (mkConst ``Bool)
  Term.synthesizeSyntheticMVarsNoPostponing
  unsafe evalExpr Bool (mkConst ``Bool) (← instantiateMVars e)

@[command_elab linear]
meta def elabLinear : CommandElab
  | `(#linear $p:ident) =>
    withScope (fun s => { s with opts := Elab.async.set s.opts false }) do
      let unit ← unitNanos
      let mut report := m!"{p.getId}, unit {unit / 1000000} ms:"
      for n in sizes do
        let prop ← `($p $(Syntax.mkNumLit (toString n)))
        let kernel ← timeNanos (elabCommand (← `(example : $prop := by decide +kernel)))
        let t₀ ← IO.monoNanosNow
        unless ← evalDecide prop do throwError "{prop} evaluated to false"
        let compiled := (← IO.monoNanosNow) - t₀
        let budget := unit * (n / 100 + 2)
        report := report ++ m!" n = {n}: kernel {kernel / 1000000} ms, \
          compiled {compiled / 1000000} ms;"
        if kernel > budget || compiled > budget then
          throwError "{prop} took longer than its budget of {budget / 1000000} ms. {report}"
      logInfo report
  | _ => throwUnsupportedSyntax
