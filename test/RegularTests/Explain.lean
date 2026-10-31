/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Regular
meta import Regular

namespace RegularTests.Explain

open Regular Regex Shape

inductive El | caption | thead | tr | script
  deriving DecidableEq

inductive Cat | caption | thead | tr | scriptSupporting
  deriving DecidableEq

def El.matches : El → Cat → Bool
  | .caption, .caption | .thead, .thead | .tr, .tr | .script, .scriptSupporting => true
  | _, _ => false

def table : Regex Cat := seq [Regex.opt (.sym .caption), Regex.opt (.sym .thead), plus (.sym .tr)]

def tagged (m : El → Cat → Bool) : Nat × El → Cat → Bool := fun p s => m p.2 s

-- Parts 0, 1 and 2 of the shape are `caption`, `tr*` and `thead`.
def shape : Regex El := seq [one .caption, many .tr, one .thead]

#guard counterexample (tagged El.matches) table (indexed shape) = some [(0, .caption), (2, .thead)]
#guard diagnose El.matches table [.caption, .thead] = .incomplete [.tr]
#guard diagnose El.matches table [.caption, .tr, .thead] = .unexpected 2 [.tr]
#guard diagnose El.matches table [.thead, .caption, .tr] = .unexpected 1 [.tr]
#guard diagnose El.matches table [.script] = .unexpected 0 [.caption, .thead, .tr]
#guard diagnose El.matches table [.caption, .tr] = .accepted

-- Indexing changes nothing but the letters, so acceptance can be decided either way.
example : Accepts (tagged El.matches) table (indexed (seq [one .thead, many1 .tr])) := by decide
example : Accepts El.matches table (seq [one .thead, many1 .tr]) :=
  accepts_indexed_iff.1 (by decide)

-- A state matching nothing is caught where it arises, and a symbol nothing can follow is not
-- expected.
#guard diagnose El.matches (seq [.sym .tr, .empty]) [.tr, .tr] = .unexpected 0 []
#guard diagnose El.matches (.alt (.sym .tr) (seq [.sym .tr, .sym .thead])) [.caption] =
  .unexpected 0 [.tr]

end RegularTests.Explain
