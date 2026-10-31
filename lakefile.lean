/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lake
open Lake DSL

package regular where
  version := v!"0.1.0"
  leanOptions := #[⟨`warningAsError, true⟩]

@[default_target]
lean_lib Regular

/-- The `test` and `bench` subprojects are deliberately not dependencies of this package, so
that downstream consumers don't inherit their tooling. Running them as child processes keeps
`lake test` and `lake run bench` working from the repo root regardless. -/
@[test_driver]
script tests do
  let child ← IO.Process.spawn { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
  child.wait

script bench do
  let child ← IO.Process.spawn { cmd := "lake", args := #["build"], cwd := __dir__ / "bench" }
  child.wait
