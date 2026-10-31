/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

@[expose] public section

namespace Regular

universe u v

/-- A regular expression over symbols `σ`. -/
inductive Regex (σ : Type u) where
  | empty
  | eps
  | sym (s : σ)
  | cat (r s : Regex σ)
  | alt (r s : Regex σ)
  | star (r : Regex σ)
  /-- The shuffle of the two languages: their words' letters interleaved in any way. -/
  | interleave (r s : Regex σ)
  /-- The language of `r` without the empty word. -/
  | nonEmpty (r : Regex σ)
  /-- One word from each of `rs`, concatenated in any order, so each stays contiguous. -/
  | allOf (rs : List (Regex σ))
  deriving Inhabited

namespace Regex

variable {σ : Type u} {α : Type v}

/-- An induction principle that reaches the members of `allOf`, which `induction` cannot. -/
@[elab_as_elim]
theorem ind {motive : Regex σ → Prop} (empty : motive .empty) (eps : motive .eps)
    (sym : ∀ s, motive (.sym s))
    (cat : ∀ r s, motive r → motive s → motive (.cat r s))
    (alt : ∀ r s, motive r → motive s → motive (.alt r s))
    (star : ∀ r, motive r → motive (.star r))
    (interleave : ∀ r s, motive r → motive s → motive (.interleave r s))
    (nonEmpty : ∀ r, motive r → motive (.nonEmpty r))
    (allOf : ∀ rs, (∀ r ∈ rs, motive r) → motive (.allOf rs)) (r : Regex σ) : motive r :=
  Regex.rec (motive_1 := motive) (motive_2 := fun rs => ∀ r ∈ rs, motive r)
    empty eps sym cat alt star interleave nonEmpty allOf
    (fun _ h => nomatch h)
    (fun _ _ ih ihs _ h => by
      cases h with
      | head => exact ih
      | tail _ h => exact ihs _ h)
    r

section BEq

variable [DecidableEq σ]

mutual
def beq : Regex σ → Regex σ → Bool
  | .empty, .empty => true
  | .eps, .eps => true
  | .sym a, .sym b => decide (a = b)
  | .cat r s, .cat r' s' => beq r r' && beq s s'
  | .alt r s, .alt r' s' => beq r r' && beq s s'
  | .star r, .star r' => beq r r'
  | .interleave r s, .interleave r' s' => beq r r' && beq s s'
  | .nonEmpty r, .nonEmpty r' => beq r r'
  | .allOf rs, .allOf rs' => beqList rs rs'
  | _, _ => false

def beqList : List (Regex σ) → List (Regex σ) → Bool
  | [], [] => true
  | r :: rs, r' :: rs' => beq r r' && beqList rs rs'
  | _, _ => false
end

theorem beq_refl (r : Regex σ) : beq r r = true := by
  induction r using ind with
  | allOf rs ih =>
    simp only [beq]
    induction rs with
    | nil => rfl
    | cons r rs ihs =>
      simp only [beqList, ih r (by simp), ihs (fun x hx => ih x (by simp [hx])), Bool.and_self]
  | _ => simp_all [beq]

theorem eq_of_beq {r s : Regex σ} (h : beq r s = true) : r = s := by
  induction r using ind generalizing s with
  | allOf rs ih =>
    cases s <;> simp only [beq, reduceCtorEq] at h ⊢
    rename_i rs'
    induction rs generalizing rs' with
    | nil => cases rs' <;> simp_all [beqList]
    | cons r rs ihs =>
      cases rs' with
      | nil => simp [beqList] at h
      | cons r' rs' =>
        simp only [beqList, Bool.and_eq_true] at h
        have h₂ := ihs (fun x hx => ih x (by simp [hx])) _ h.2
        simp only [allOf.injEq] at h₂ ⊢
        rw [ih r (by simp) h.1, h₂]
  | cat _ _ ih₁ ih₂ | alt _ _ ih₁ ih₂ | interleave _ _ ih₁ ih₂ =>
    cases s <;> simp [beq] at h ⊢ <;> exact ⟨ih₁ h.1, ih₂ h.2⟩
  | star _ ih | nonEmpty _ ih => cases s <;> simp [beq] at h ⊢ <;> exact ih h
  | _ => cases s <;> simp_all [beq]

instance : DecidableEq (Regex σ) := fun r s =>
  decidable_of_iff (beq r s = true) ⟨eq_of_beq, fun h => h ▸ beq_refl r⟩

end BEq

end Regex

/-- `Shuffle u v w`: `w` interleaves the letters of `u` and `v`, keeping each one's order. -/
inductive Shuffle {α : Type v} : List α → List α → List α → Prop
  | nil : Shuffle [] [] []
  | left {a : α} {u v w : List α} : Shuffle u v w → Shuffle (a :: u) v (a :: w)
  | right {a : α} {u v w : List α} : Shuffle u v w → Shuffle u (a :: v) (a :: w)

/-- `Matches m r w`: the word `w` is in the language of `r`, where a letter is in the language
of a symbol when `m` says it matches. -/
inductive Matches {α : Type v} {σ : Type u} (m : α → σ → Bool) : Regex σ → List α → Prop
  | eps : Matches m .eps []
  | sym {a : α} {s : σ} : m a s = true → Matches m (.sym s) [a]
  | cat {r s : Regex σ} {u v : List α} : Matches m r u → Matches m s v →
      Matches m (.cat r s) (u ++ v)
  | altLeft {r s : Regex σ} {w : List α} : Matches m r w → Matches m (.alt r s) w
  | altRight {r s : Regex σ} {w : List α} : Matches m s w → Matches m (.alt r s) w
  | starNil {r : Regex σ} : Matches m (.star r) []
  | starCons {r : Regex σ} {u v : List α} : Matches m r u → Matches m (.star r) v →
      Matches m (.star r) (u ++ v)
  | interleave {r s : Regex σ} {u v w : List α} : Matches m r u → Matches m s v →
      Shuffle u v w → Matches m (.interleave r s) w
  | nonEmpty {r : Regex σ} {a : α} {w : List α} : Matches m r (a :: w) →
      Matches m (.nonEmpty r) (a :: w)
  | allOfNil : Matches m (.allOf []) []
  | allOfCons {r : Regex σ} {rs qs : List (Regex σ)} {u v : List α} : Matches m r u →
      Matches m (.allOf rs) v → (r :: rs).Perm qs → Matches m (.allOf qs) (u ++ v)

end Regular
