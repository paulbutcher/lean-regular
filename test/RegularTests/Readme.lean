/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Regular
meta import Regular

namespace RegularTests.Readme

open Regular Regex

inductive Kind | length | percentage | color
  deriving DecidableEq, Repr

inductive Ty | lengthPercentage | color
  deriving DecidableEq

def widens : Kind → Ty → Bool
  | .length, .lengthPercentage | .percentage, .lengthPercentage | .color, .color => true
  | _, _ => false

def grammar : Regex Ty := someOf [rep 1 2 (.sym .lengthPercentage), .sym .color]

example : Accepts widens grammar
    (seq [Shape.one .color, Shape.one .length, Shape.opt .percentage]) := by
  decide

example : ¬Accepts widens grammar (seq [Shape.one .length, Shape.many .color]) := by
  decide

#guard counterexample widens grammar (seq [Shape.one .length, Shape.many .color]) =
  some [.length, .color, .color]

end RegularTests.Readme
