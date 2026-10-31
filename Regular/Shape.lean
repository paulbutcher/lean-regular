/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Regular.Combinators
public import Regular.Decide

@[expose] public section

/-!
A shape is what a consumer knows at compile time about its input: a `Regex` over the letters
themselves, whose language is taken with `(· == ·)` as the matching function.
-/

namespace Regular

universe u v

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

/-! Coarsening: a shape that contains `s` and is cheaper to check, so that checking it first and
falling back to `s` only when it fails gives the same answer at less cost, by `Accepts.of_coarse`.
Being smaller, coarse shapes also repeat more often, which makes caching results by shape pay. -/

/-- Any number of the letters of `s`, in any order, listed as they first appear in `s`. For a
grammar that is a `star` of alternatives, such as an HTML element taking any number of one
category, it gives the same answer as `s` whenever each letter of `s` occurs in some word. -/
def kinds [DecidableEq α] (s : Regex α) : Regex α := .star (oneOf (s.letters.eraseDups.map .sym))

/-- The letters `as` in order, with each run of two or more of a letter loosened to one or more,
so that child lists differing only in the lengths of their runs coarsen alike. -/
def collapse [DecidableEq α] : List α → Regex α
  | [] => .eps
  | a :: as => collapse.go a false as
where
  run (a : α) (repeated : Bool) : Regex α := if repeated then plus (.sym a) else .sym a
  go (a : α) (repeated : Bool) : List α → Regex α
    | [] => run a repeated
    | b :: bs => if b = a then go a true bs else .cat (run a repeated) (go b false bs)

variable [DecidableEq α]

theorem accepts_kinds (s : Regex α) : Accepts (· == ·) (kinds s) s := by
  intro w hw
  have hflat : ∀ w : List α, w = (w.map ([·])).flatten := by
    intro w
    induction w with
    | nil => rfl
    | cons a w ih => simp [← ih]
  refine matches_star_iff_flatten.2 ⟨w.map ([·]), ?_, hflat w⟩
  simp only [List.mem_map]
  rintro _ ⟨a, ha, rfl⟩
  refine matches_oneOf.2 ⟨.sym a, ?_, .sym (by simp)⟩
  simpa [List.mem_eraseDups] using mem_letters_of_matches hw a ha

private theorem matches_plus_replicate (a : α) {k : Nat} (hk : 0 < k) :
    Matches (· == ·) (plus (.sym a)) (List.replicate k a) := by
  refine matches_plus.2 ⟨List.replicate k [a], by simp; omega, ?_, ?_⟩
  · intro v hv
    rw [List.eq_of_mem_replicate hv]
    exact .sym (by simp)
  · clear hk
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ← ih]

private theorem matches_collapse_run (a : α) {repeated : Bool} {k : Nat} (hk : 0 < k)
    (h : repeated = false → k = 1) :
    Matches (· == ·) (collapse.run a repeated) (List.replicate k a) := by
  cases repeated
  · rw [h rfl]
    exact .sym (by simp)
  · exact matches_plus_replicate a hk

private theorem matches_collapse_go (a : α) (bs : List α) {repeated : Bool} {k : Nat}
    (hk : 0 < k) (h : repeated = false → k = 1) :
    Matches (· == ·) (collapse.go a repeated bs) (List.replicate k a ++ bs) := by
  induction bs generalizing a repeated k with
  | nil => simpa [collapse.go] using matches_collapse_run a hk h
  | cons b bs ih =>
    simp only [collapse.go]
    split
    · subst b
      have := ih a (repeated := true) (Nat.succ_pos k) nofun
      rwa [List.replicate_succ', List.append_assoc] at this
    · exact .cat (matches_collapse_run a hk h) (by simpa using ih b (Nat.succ_pos 0) fun _ => rfl)

theorem accepts_collapse (as : List α) : Accepts (· == ·) (collapse as) (word as) := by
  intro w hw
  rw [matches_word.1 hw]
  cases as with
  | nil => exact .eps
  | cons a as => simpa [collapse] using matches_collapse_go a as (Nat.succ_pos 0) fun _ => rfl

end Shape

/-- If the grammar accepts a coarser shape `s'`, it accepts `s`. -/
theorem Accepts.of_coarse {σ : Type u} {α : Type v} [DecidableEq α] {m : α → σ → Bool}
    {g : Regex σ} {s s' : Regex α} (hs : Accepts (· == ·) s' s) (h : Accepts m g s') :
    Accepts m g s :=
  fun w hw => h w (hs w hw)

end Regular
