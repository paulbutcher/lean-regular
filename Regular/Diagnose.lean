/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Regular.Decide
public import Regular.Combinators

@[expose] public section

namespace Regular

universe u v

namespace Regex

variable {σ : Type u} {α : Type v} {m : α → σ → Bool}

mutual
/-- Whether `r` provably matches no word. It treats every symbol as matching some letter. -/
def isVoid : Regex σ → Bool
  | .empty => true
  | .eps | .sym _ | .star _ => false
  | .cat r s | .interleave r s => isVoid r || isVoid s
  | .alt r s => isVoid r && isVoid s
  | .nonEmpty r => atMostEps r
  | .allOf rs => anyVoid rs

/-- Whether `r` provably matches no word but the empty one. -/
def atMostEps : Regex σ → Bool
  | .empty | .eps => true
  | .sym _ => false
  | .cat r s | .interleave r s => isVoid r || isVoid s || (atMostEps r && atMostEps s)
  | .alt r s => atMostEps r && atMostEps s
  | .star r | .nonEmpty r => atMostEps r
  | .allOf rs => anyVoid rs || allAtMostEps rs

def anyVoid : List (Regex σ) → Bool
  | [] => false
  | r :: rs => isVoid r || anyVoid rs

def allAtMostEps : List (Regex σ) → Bool
  | [] => true
  | r :: rs => atMostEps r && allAtMostEps rs
end

theorem anyVoid_eq (rs : List (Regex σ)) : anyVoid rs = rs.any isVoid := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [anyVoid, ih]

theorem allAtMostEps_eq (rs : List (Regex σ)) : allAtMostEps rs = rs.all atMostEps := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [allAtMostEps, ih]

private theorem shuffle_append (u v : List α) : Shuffle u v (u ++ v) := by
  induction u with
  | nil => exact shuffle_nil_left_iff.2 rfl
  | cons a u ih => exact .left ih

theorem isVoid_sound (r : Regex σ) :
    (isVoid r = true → ∀ w, ¬Matches m r w) ∧
      (atMostEps r = true → ∀ w, Matches m r w → w = []) := by
  induction r using ind with
  | empty => exact ⟨fun _ _ h => not_matches_empty h, fun _ _ h => absurd h not_matches_empty⟩
  | eps => exact ⟨nofun, fun _ _ h => matches_eps_iff.1 h⟩
  | sym => exact ⟨nofun, nofun⟩
  | cat r s ihr ihs | interleave r s ihr ihs =>
    first
    | refine ⟨fun h w hw => ?_, fun h w hw => ?_⟩ <;>
        obtain ⟨u, v, rfl, hu, hv⟩ := matches_cat_iff.1 hw <;>
        simp only [isVoid, atMostEps, Bool.or_eq_true, Bool.and_eq_true] at h
      · rcases h with h | h
        · exact ihr.1 h u hu
        · exact ihs.1 h v hv
      · rcases h with (h | h) | ⟨h₁, h₂⟩
        · exact absurd hu (ihr.1 h u)
        · exact absurd hv (ihs.1 h v)
        · rw [ihr.2 h₁ u hu, ihs.2 h₂ v hv]; rfl
    | refine ⟨fun h w hw => ?_, fun h w hw => ?_⟩ <;>
        obtain ⟨u, v, hu, hv, hsh⟩ := matches_interleave_iff.1 hw <;>
        simp only [isVoid, atMostEps, Bool.or_eq_true, Bool.and_eq_true] at h
      · rcases h with h | h
        · exact ihr.1 h u hu
        · exact ihs.1 h v hv
      · rcases h with (h | h) | ⟨h₁, h₂⟩
        · exact absurd hu (ihr.1 h u)
        · exact absurd hv (ihs.1 h v)
        · rw [ihr.2 h₁ u hu, ihs.2 h₂ v hv] at hsh
          exact (shuffle_nil_left_iff.1 hsh).symm
  | alt r s ihr ihs =>
    refine ⟨fun h w hw => ?_, fun h w hw => ?_⟩ <;>
      simp only [isVoid, atMostEps, Bool.and_eq_true] at h <;>
      rcases matches_alt_iff.1 hw with hw | hw
    · exact ihr.1 h.1 w hw
    · exact ihs.1 h.2 w hw
    · exact ihr.2 h.1 w hw
    · exact ihs.2 h.2 w hw
  | star r ih =>
    refine ⟨nofun, fun h w hw => ?_⟩
    obtain ⟨ws, hws, rfl⟩ := matches_star_iff_flatten.1 hw
    exact List.flatten_eq_nil_iff.2 fun v hv => ih.2 h v (hws v hv)
  | nonEmpty r ih =>
    refine ⟨fun h w hw => ?_, fun h w hw => ?_⟩ <;>
      obtain ⟨hne, hw⟩ := matches_nonEmpty_iff.1 hw
    · exact hne (ih.2 h w hw)
    · exact absurd (ih.2 h w hw) hne
  | allOf rs ih =>
    have hvoid : anyVoid rs = true → ∀ w, ¬Matches m (.allOf rs) w := by
      intro h w hw
      obtain ⟨r, hr, hv⟩ := List.any_eq_true.1 (anyVoid_eq rs ▸ h)
      obtain ⟨ps, hps, hm, rfl⟩ := matches_allOf.1 hw
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hps.mem_iff.2 hr)
      exact (ih p.1 hr).1 hv p.2 (hm p hp)
    refine ⟨hvoid, fun h w hw => ?_⟩
    simp only [atMostEps, Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd hw (hvoid h w)
    · obtain ⟨ps, hps, hm, rfl⟩ := matches_allOf.1 hw
      refine List.flatten_eq_nil_iff.2 fun v hv => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
      have hr := hps.mem_iff.1 (List.mem_map_of_mem hp)
      exact (ih p.1 hr).2 (List.all_eq_true.1 (allAtMostEps_eq rs ▸ h) p.1 hr) p.2 (hm p hp)

private theorem matches_allOf_of_forall {rs : List (Regex σ)}
    (h : ∀ r ∈ rs, ∃ w, Matches m r w) : ∃ w, Matches m (.allOf rs) w := by
  induction rs with
  | nil => exact ⟨[], .allOfNil⟩
  | cons r rs ih =>
    obtain ⟨u, hu⟩ := h r (by simp)
    obtain ⟨v, hv⟩ := ih fun x hx => h x (by simp [hx])
    exact ⟨u ++ v, .allOfCons hu hv (List.Perm.refl _)⟩

/-- Given that every symbol matches some letter, `isVoid` and `atMostEps` are exact. -/
theorem isVoid_complete (hm : ∀ s, ∃ a, m a s = true) (r : Regex σ) :
    (isVoid r = false → ∃ w, Matches m r w) ∧
      (atMostEps r = false → ∃ w, w ≠ [] ∧ Matches m r w) := by
  induction r using ind with
  | empty => exact ⟨nofun, nofun⟩
  | eps => exact ⟨fun _ => ⟨[], .eps⟩, nofun⟩
  | sym s =>
    obtain ⟨a, ha⟩ := hm s
    exact ⟨fun _ => ⟨[a], .sym ha⟩, fun _ => ⟨[a], by simp, .sym ha⟩⟩
  | cat r s ihr ihs | interleave r s ihr ihs =>
    have build : ∀ u v, Matches m r u → Matches m s v →
        Matches m (.cat r s) (u ++ v) ∧ Matches m (.interleave r s) (u ++ v) :=
      fun u v hu hv => ⟨.cat hu hv, .interleave hu hv (shuffle_append u v)⟩
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      simp only [isVoid, atMostEps, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h
    all_goals first
      | obtain ⟨u, hu⟩ := ihr.1 h.1
        obtain ⟨v, hv⟩ := ihs.1 h.2
        first
        | exact ⟨u ++ v, (build u v hu hv).1⟩
        | exact ⟨u ++ v, (build u v hu hv).2⟩
      | obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
        obtain ⟨u, hu⟩ := ihr.1 h₁
        obtain ⟨v, hv⟩ := ihs.1 h₂
        rcases h₃ with h₃ | h₃
        · obtain ⟨u', hne, hu'⟩ := ihr.2 h₃
          first
          | exact ⟨u' ++ v, by simp [hne], (build u' v hu' hv).1⟩
          | exact ⟨u' ++ v, by simp [hne], (build u' v hu' hv).2⟩
        · obtain ⟨v', hne, hv'⟩ := ihs.2 h₃
          first
          | exact ⟨u ++ v', by simp [hne], (build u v' hu hv').1⟩
          | exact ⟨u ++ v', by simp [hne], (build u v' hu hv').2⟩
  | alt r s ihr ihs =>
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      simp only [isVoid, atMostEps, Bool.and_eq_false_iff] at h
    · rcases h with h | h
      · obtain ⟨w, hw⟩ := ihr.1 h; exact ⟨w, .altLeft hw⟩
      · obtain ⟨w, hw⟩ := ihs.1 h; exact ⟨w, .altRight hw⟩
    · rcases h with h | h
      · obtain ⟨w, hne, hw⟩ := ihr.2 h; exact ⟨w, hne, .altLeft hw⟩
      · obtain ⟨w, hne, hw⟩ := ihs.2 h; exact ⟨w, hne, .altRight hw⟩
  | star r ih =>
    refine ⟨fun _ => ⟨[], .starNil⟩, fun h => ?_⟩
    obtain ⟨w, hne, hw⟩ := ih.2 h
    exact ⟨w ++ [], by simpa using hne, .starCons hw .starNil⟩
  | nonEmpty r ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨w, hne, hw⟩ := ih.2 h
    · exact ⟨w, matches_nonEmpty_iff.2 ⟨hne, hw⟩⟩
    · exact ⟨w, hne, matches_nonEmpty_iff.2 ⟨hne, hw⟩⟩
  | allOf rs ih =>
    have hall : anyVoid rs = false → ∀ r ∈ rs, ∃ w, Matches m r w := fun h r hr =>
      (ih r hr).1 (by simpa using (List.any_eq_false.1 (anyVoid_eq rs ▸ h)) r hr)
    refine ⟨fun h => matches_allOf_of_forall (hall h), fun h => ?_⟩
    simp only [atMostEps, Bool.or_eq_false_iff] at h
    obtain ⟨r, hr, hne⟩ := by simpa using (allAtMostEps_eq rs ▸ h.2 : rs.all atMostEps = false)
    obtain ⟨u, hu, hmu⟩ := (ih r hr).2 (by simpa using hne)
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hr
    obtain ⟨v, hv⟩ := matches_allOf_of_forall (m := m) (rs := l₁ ++ l₂) fun x hx =>
      hall h.1 x (by rcases List.mem_append.1 hx with hx | hx <;> simp [hx])
    exact ⟨u ++ v, by simp [hu], .allOfCons hmu hv List.perm_middle.symm⟩

end Regex

open Regex Inclusion

/-- How a word falls short of a grammar. -/
inductive Diagnosis where
  | accepted
  /-- The letter at this position cannot follow the ones before it. -/
  | unexpected (i : Nat)
  /-- Every letter can follow the ones before it, but the word ends too soon. -/
  | incomplete
  deriving DecidableEq, Repr

variable {α : Type v} {σ : Type u} [DecidableEq σ]

/-- Locates where `w` goes wrong for `g`, typically a counterexample. -/
def diagnose (m : α → σ → Bool) (g : Regex σ) (w : List α) : Diagnosis := diagnose.go m 0 [g] w
where
  go (m : α → σ → Bool) (i : Nat) (ys : List (Regex σ)) : List α → Diagnosis
    | [] => if ys.any nullable then .accepted else .incomplete
    | a :: w =>
      let ys' := derivSet m a ys
      if ys'.all isVoid then .unexpected i else go m (i + 1) ys' w

/-- Some word of `g` starts with `u`. -/
def Viable (m : α → σ → Bool) (g : Regex σ) (u : List α) : Prop := ∃ v, Matches m g (u ++ v)

variable {m : α → σ → Bool} {g : Regex σ}

omit [DecidableEq σ] in
private theorem viable_of_rep {ys : List (Regex σ)} {p : List α}
    (hrep : ∀ v, (∃ y ∈ ys, Matches m y v) ↔ Matches m g (p ++ v))
    (hm : ∀ s, ∃ a, m a s = true) (h : ys.all isVoid = false) : Viable m g p := by
  obtain ⟨y, hy, hv⟩ := by simpa using h
  obtain ⟨v, hyv⟩ := (isVoid_complete hm y).1 (by simpa using hv)
  exact ⟨v, (hrep v).1 ⟨y, hy, hyv⟩⟩

private theorem go_spec {i : Nat} {ys : List (Regex σ)} {p w : List α}
    (hrep : ∀ v, (∃ y ∈ ys, Matches m y v) ↔ Matches m g (p ++ v)) :
    (diagnose.go m i ys w = .accepted ↔ Matches m g (p ++ w)) ∧
    (∀ j, diagnose.go m i ys w = .unexpected j → ∃ k, j = i + k ∧ k < w.length ∧
      ¬Viable m g (p ++ w.take (k + 1)) ∧
      ((∀ s, ∃ a, m a s = true) → ∀ k' < k, Viable m g (p ++ w.take (k' + 1)))) ∧
    (diagnose.go m i ys w = .incomplete → ¬Matches m g (p ++ w) ∧
      ((∀ s, ∃ a, m a s = true) → ∀ k < w.length, Viable m g (p ++ w.take (k + 1)))) := by
  induction w generalizing i ys p with
  | nil =>
    have hacc : (ys.any nullable = true) ↔ Matches m g (p ++ []) := by
      rw [← hrep []]
      simp only [List.any_eq_true]
      exact exists_congr fun y => and_congr_right fun _ => nullable_iff
    simp only [diagnose.go]
    split <;> rename_i h
    · exact ⟨by simpa using hacc.1 h, by simp, by simp⟩
    · exact ⟨by simpa using fun h' => h (hacc.2 h'), by simp,
        fun _ => ⟨fun h' => h (hacc.2 h'), by simp⟩⟩
  | cons a w ih =>
    have hrep' : ∀ v, (∃ y ∈ derivSet m a ys, Matches m y v) ↔ Matches m g ((p ++ [a]) ++ v) := by
      intro v
      simp only [mem_derivSet, List.append_assoc, List.singleton_append, ← hrep (a :: v)]
      constructor
      · rintro ⟨y, ⟨x, hx, hy⟩, hyv⟩
        exact ⟨x, hx, matches_cons_iff.2 ⟨y, hy, hyv⟩⟩
      · rintro ⟨x, hx, hxv⟩
        obtain ⟨y, hy, hyv⟩ := matches_cons_iff.1 hxv
        exact ⟨y, ⟨x, hx, hy⟩, hyv⟩
    have hdead : (derivSet m a ys).all isVoid = true → ¬Viable m g (p ++ [a]) := by
      rintro h ⟨v, hv⟩
      obtain ⟨y, hy, hyv⟩ := (hrep' v).2 hv
      exact (isVoid_sound y).1 (List.all_eq_true.1 h y hy) v hyv
    simp only [diagnose.go]
    split <;> rename_i h
    · refine ⟨⟨nofun, fun hw => absurd ⟨w, by simpa using hw⟩ (hdead h)⟩, ?_, nofun⟩
      intro j hj
      cases hj
      exact ⟨0, rfl, by simp, by simpa using hdead h, by simp⟩
    · obtain ⟨iha, ihu, ihi⟩ := ih (i := i + 1) hrep'
      have hlive := fun hm => viable_of_rep hrep' hm (by simpa using h)
      refine ⟨by simpa using iha, fun j hj => ?_, fun hj => ?_⟩
      · obtain ⟨k, rfl, hk, hnv, hv⟩ := ihu j hj
        refine ⟨k + 1, by omega, by simp; omega, by simpa using hnv, fun hm k' hk' => ?_⟩
        cases k' with
        | zero => simpa using hlive hm
        | succ k' => simpa using hv hm k' (by omega)
      · obtain ⟨hnm, hv⟩ := ihi hj
        refine ⟨by simpa using hnm, fun hm k hk => ?_⟩
        cases k with
        | zero => simpa using hlive hm
        | succ k => simpa using hv hm k (by simpa using hk)

theorem diagnose_accepted_iff {w : List α} : diagnose m g w = .accepted ↔ Matches m g w := by
  have := go_spec (m := m) (g := g) (i := 0) (ys := [g]) (p := []) (w := w) (by simp)
  simpa [diagnose] using this.1

/-- The prefix ending at position `i` is not the start of any word of `g`, and, given that every
symbol matches some letter, each shorter nonempty prefix is. -/
theorem diagnose_unexpected {w : List α} {i : Nat} (h : diagnose m g w = .unexpected i) :
    i < w.length ∧ ¬Viable m g (w.take (i + 1)) ∧
      ((∀ s, ∃ a, m a s = true) → ∀ k < i, Viable m g (w.take (k + 1))) := by
  have := go_spec (m := m) (g := g) (i := 0) (ys := [g]) (p := []) (w := w) (by simp)
  obtain ⟨k, rfl, hk, hnv, hv⟩ := this.2.1 i h
  exact ⟨by simpa using hk, by simpa using hnv, by simpa using hv⟩

/-- `w` is not a word of `g`, and, given that every symbol matches some letter, each of its
nonempty prefixes is the start of one. -/
theorem diagnose_incomplete {w : List α} (h : diagnose m g w = .incomplete) :
    ¬Matches m g w ∧
      ((∀ s, ∃ a, m a s = true) → ∀ k < w.length, Viable m g (w.take (k + 1))) := by
  have := go_spec (m := m) (g := g) (i := 0) (ys := [g]) (p := []) (w := w) (by simp)
  simpa using this.2.2 h

end Regular
