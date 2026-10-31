/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Regular.Combinators

@[expose] public section

/-!
A shape is what a consumer knows at compile time about its input: a `Regex` over the letters
themselves, whose language is taken with `(· == ·)` as the matching function.
-/

namespace Regular

universe v

namespace Shape

open Regex

variable {α : Type v}

def one (a : α) : Regex α := .sym a

def opt (a : α) : Regex α := Regex.opt (.sym a)

def many (a : α) : Regex α := .star (.sym a)

def many1 (a : α) : Regex α := plus (.sym a)

/-- The letters `as` in order. -/
def word (as : List α) : Regex α := seq (as.map .sym)

/-- Any number of copies of `word g`, with `sep` between each and the next. -/
def groups (g : List α) (sep : α) : Regex α := Regex.opt (sepBy1 (word g) (.sym sep))

/-- At least one copy of `word g`, with `sep` between each and the next. -/
def groups1 (g : List α) (sep : α) : Regex α := sepBy1 (word g) (.sym sep)

theorem matches_word [DecidableEq α] {as w : List α} :
    Matches (· == ·) (word as) w ↔ w = as := by
  induction as generalizing w with
  | nil => simp [word, seq, matches_eps_iff]
  | cons a as ih =>
    simp only [word, seq, List.map_cons, List.foldr_cons] at ih ⊢
    simp only [matches_cat_iff, matches_sym_iff, ih, beq_iff_eq]
    constructor
    · rintro ⟨_, _, rfl, ⟨_, rfl, rfl⟩, rfl⟩
      rfl
    · rintro rfl
      exact ⟨[a], as, rfl, ⟨a, rfl, rfl⟩, rfl⟩

end Shape

end Regular
