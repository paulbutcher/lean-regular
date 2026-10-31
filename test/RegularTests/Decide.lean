/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Regular
meta import Regular

namespace RegularTests

open Regular Regex

inductive Kind | length | percentage | color | a | b | c
  deriving DecidableEq, Repr

inductive Ty | lengthPercentage | color | a | b | c
  deriving DecidableEq

/-- A length or a percentage is a `<length-percentage>`. -/
def widens : Kind → Ty → Bool
  | .length, .lengthPercentage | .percentage, .lengthPercentage | .color, .color
  | .a, .a | .b, .b | .c, .c => true
  | _, _ => false

open Kind in
def w (ks : List Kind) : Regex Kind := Shape.word ks

def lp : Regex Ty := .sym .lengthPercentage
def A : Regex Ty := .sym .a
def B : Regex Ty := .sym .b
def C : Regex Ty := .sym .c

-- Widening, and acceptance for every count.
example : Accepts widens (.star lp) (Shape.many .length) := by decide
example : Accepts widens (plus lp) (.cat (Shape.one .percentage) (Shape.many .length)) := by decide
example : ¬Accepts widens (plus lp) (Shape.many .length) := by decide
#guard counterexample widens (plus lp) (Shape.many .length) = some []
#guard counterexample widens (.star lp) (.cat (Shape.many .length) (Shape.one .color)) =
  some [.color]
#guard counterexample widens (.star lp) (Shape.many .length) = none

-- `allOf` keeps each member's block contiguous; `interleave` does not.
example : Accepts widens (.allOf [.cat A B, C]) (w [.c, .a, .b]) := by decide
example : ¬Accepts widens (.allOf [.cat A B, C]) (w [.a, .c, .b]) := by decide
example : Accepts widens (.interleave (.cat A B) C) (w [.a, .c, .b]) := by decide
#guard counterexample widens (.allOf [.cat A B, C]) (.alt (w [.a, .b, .c]) (w [.a, .c, .b])) =
  some [.a, .c, .b]

-- `someOf` takes each member at most once and at least one in all.
example : Accepts widens (someOf [A, B, C]) (.alt (w [.c, .a]) (w [.b])) := by decide
example : ¬Accepts widens (someOf [A, B, C]) (w [.a, .a]) := by decide
#guard counterexample widens (someOf [A, B, C]) (Shape.opt .a) = some []

-- Bounded repetition, against a shape whose count is unknown.
example : Accepts widens (rep 1 3 A) (.cat (Shape.one .a) (upTo 2 (.sym .a))) := by decide
#guard counterexample widens (rep 1 3 A) (Shape.many .a) = some []
#guard counterexample widens (rep 1 3 A) (Shape.many1 .a) = some [.a, .a, .a, .a]

-- Separated lists, and an unknown number of pairs.
example : Accepts widens (sepBy1 lp (.sym .color)) (Shape.groups1 [.length] .color) := by decide
example : ¬Accepts widens (sepBy1 lp (.sym .color)) (Shape.groups [.length] .color) := by decide
example : Accepts widens (.star (.cat A B)) (.star (w [.a, .b])) := by decide
#guard counterexample widens (.star (.cat A B)) (Shape.many .a) = some [.a]

-- `nonEmpty`, CSS's `!`, removes only the empty word.
example : Accepts widens (.nonEmpty (.star A)) (Shape.many1 .a) := by decide
#guard counterexample widens (.nonEmpty (.star A)) (Shape.many .a) = some []

/-- A counterexample really is one, so a consumer can report it as the offending input. -/
example : counterexample widens (.allOf [.cat A B, C]) (w [.a, .c, .b]) = some [.a, .c, .b] ∧
    ¬Matches widens (.allOf [.cat A B, C]) [.a, .c, .b] :=
  ⟨by decide, (counterexample_spec (by decide : counterexample widens _ (w [.a, .c, .b]) = _)).2⟩

end RegularTests
