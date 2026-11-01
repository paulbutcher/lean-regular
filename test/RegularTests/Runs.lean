/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Regular
meta import Regular
meta import RegularTests.Timing

namespace RegularTests.Runs

open Regular Regex

inductive L | a | b
  deriving DecidableEq

def opts (n : Nat) : Regex L := seq (List.replicate n (Shape.opt .a))

def afterB (n : Nat) : Regex L := seq (Shape.one .b :: List.replicate n (Shape.opt .a))

def stars : Regex L := .star (.sym .a)

def bStars : Regex L := seq [.sym .b, .star (.sym .a)]

abbrev optsStars (n : Nat) : Prop := Accepts (· == ·) stars (opts n)
abbrev optsBStars (n : Nat) : Prop := ¬Accepts (· == ·) bStars (opts n)
abbrev afterBStars (n : Nat) : Prop := ¬Accepts (· == ·) stars (afterB n)
abbrev afterBBStars (n : Nat) : Prop := Accepts (· == ·) bStars (afterB n)

-- A run of optional letters decides in time linear in its length.
#linear optsStars
#linear optsBStars
#linear afterBStars
#linear afterBBStars

end RegularTests.Runs
