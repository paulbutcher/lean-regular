/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Command

public section

open Lean Elab Command

/-- `#bench "name" p` proves `p` by `decide` and again by `decide +kernel`, logging how long
each takes, kernel check included. -/
syntax (name := bench) "#bench " str ppSpace term : command

@[command_elab bench]
meta def elabBench : CommandElab
  | `(#bench $name:str $p:term) =>
    withScope (fun s => { s with opts := Elab.async.set s.opts false }) do
      let t₀ ← IO.monoNanosNow
      elabCommand (← `(example : $p := by decide))
      let t₁ ← IO.monoNanosNow
      elabCommand (← `(example : $p := by decide +kernel))
      let t₂ ← IO.monoNanosNow
      logInfo m!"{name.getString}: decide {(t₁ - t₀) / 1000000} ms, \
        decide +kernel {(t₂ - t₁) / 1000000} ms"
  | _ => throwUnsupportedSyntax
