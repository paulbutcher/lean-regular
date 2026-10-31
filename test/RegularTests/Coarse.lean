/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Regular
meta import Regular

namespace RegularTests.Coarse

open Regular Regex Shape

inductive Cat | text | phrasing | flow | caption | tr | tfoot
  deriving DecidableEq

def Cat.widens : Cat → Cat → Bool
  | .text, .phrasing | .text, .flow | .phrasing, .flow => true
  | a, b => a == b

def flowContent : Regex Cat := .star (.sym .flow)

def table : Regex Cat := seq [Regex.opt (.sym .caption), plus (.sym .tr), Regex.opt (.sym .tfoot)]

def children : List Cat := [.text, .phrasing, .text, .text, .phrasing, .text]

example : Accepts Cat.widens flowContent (word children) :=
  (accepts_kinds _).of_coarse (by decide)

example : Accepts Cat.widens table (word [.caption, .tr, .tr, .tr, .tfoot]) :=
  (accepts_collapse _).of_coarse (by decide)

-- `kinds` forgets order, so a grammar where order matters needs the fallback.
example : ¬Accepts Cat.widens table (kinds (word [.caption, .tr])) := by decide
example : Accepts Cat.widens table (word [.caption, .tr]) := by decide

-- Distinct child lists coarsen to the same shape, which is what a cache keys on.
#guard decide (kinds (word children) = kinds (word [.text, .phrasing]))
#guard decide (collapse ([.caption, .tr, .tr, .tfoot] : List Cat) = collapse [.caption, .tr, .tr, .tr, .tfoot])

end RegularTests.Coarse
