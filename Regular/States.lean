/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Regular.Deriv

@[expose] public section

namespace Regular

universe u v

def sublists {β : Type u} : List β → List (List β)
  | [] => [[]]
  | a :: l => sublists l ++ (sublists l).map (a :: ·)

theorem length_sublists {β : Type u} (l : List β) : (sublists l).length = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sublists, ih, Nat.pow_succ, Nat.mul_two]

theorem mem_sublists_of_sublist {β : Type u} {s l : List β} (h : s.Sublist l) :
    s ∈ sublists l := by
  induction h with
  | slnil => simp [sublists]
  | cons _ _ ih => simp [sublists, ih]
  | cons_cons _ _ ih => simp [sublists, ih]


theorem sublist_of_mem_sublists {β : Type u} {s l : List β} (h : s ∈ sublists l) :
    s.Sublist l := by
  induction l generalizing s with
  | nil => simp_all [sublists]
  | cons a l ih =>
    simp only [sublists, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨t, ht, rfl⟩
    · exact (ih h).cons a
    · exact (ih ht).cons_cons a
namespace Regex

variable {σ : Type u} {α : Type v} {m : α → σ → Bool}

mutual
/-- Every derivative of `r`, and every derivative of those, by any letters, is a member. -/
def states : Regex σ → List (Regex σ)
  | .empty | .eps => []
  | .sym _ => [.eps]
  | .cat r s => (states r).map (mkCat · s) ++ states s
  | .alt r s => states r ++ states s
  | .star r => (states r).map (mkCat · (.star r))
  | .interleave r s => (r :: states r).flatMap fun x => (s :: states s).map (mkInter x ·)
  | .nonEmpty r => states r
  | .allOf rs => (sublists rs).flatMap fun sub => (statesAll rs).map (mkCat · (.allOf sub))

def statesAll : List (Regex σ) → List (Regex σ)
  | [] => []
  | r :: rs => states r ++ statesAll rs
end

theorem mem_statesAll {rs : List (Regex σ)} {x : Regex σ} :
    x ∈ statesAll rs ↔ ∃ r ∈ rs, x ∈ states r := by
  induction rs with
  | nil => simp [statesAll]
  | cons r rs ih => simp [statesAll, ih]

mutual
/-- An upper bound on the length of `states`, computed without building it. -/
def bound : Regex σ → Nat
  | .empty | .eps => 0
  | .sym _ => 1
  | .cat r s | .alt r s => bound r + bound s
  | .star r | .nonEmpty r => bound r
  | .interleave r s => (bound r + 1) * (bound s + 1)
  | .allOf rs => boundAll rs <<< rs.length

def boundAll : List (Regex σ) → Nat
  | [] => 0
  | r :: rs => bound r + boundAll rs
end

theorem length_flatMap_map {β γ δ : Type _} (l : List β) (k : List γ) (f : β → γ → δ) :
    (l.flatMap fun x => k.map (f x)).length = l.length * k.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem length_states_le (r : Regex σ) : (states r).length ≤ bound r := by
  induction r using ind with
  | empty | eps | sym => simp [states, bound]
  | cat r s ihr ihs | alt r s ihr ihs => simp only [states, bound]; simp; omega
  | star r ih | nonEmpty r ih => simpa [states, bound] using ih
  | interleave r s ihr ihs =>
    simp only [states, bound, length_flatMap_map, List.length_cons]
    exact Nat.mul_le_mul (by omega) (by omega)
  | allOf rs ih =>
    have hall : (statesAll rs).length ≤ boundAll rs := by
      induction rs with
      | nil => simp [statesAll, boundAll]
      | cons r rs ihs =>
        simp only [statesAll, boundAll, List.length_append]
        have := ih r (by simp)
        have := ihs fun x hx => ih x (by simp [hx])
        omega
    simp only [states, bound, length_flatMap_map, length_sublists, Nat.shiftLeft_eq]
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ hall

theorem mem_deriv_mkCat {a : α} {x s d : Regex σ} (h : d ∈ deriv m a (mkCat x s)) :
    (∃ d' ∈ deriv m a x, d = mkCat d' s) ∨ (nullable x = true ∧ d ∈ deriv m a s) := by
  by_cases hx : x = .eps
  · subst hx
    exact .inr ⟨rfl, h⟩
  · have : mkCat x s = .cat x s := by cases x <;> simp_all [mkCat]
    rw [this] at h
    simp only [deriv, List.mem_append, List.mem_map, List.mem_ite_nil_right] at h
    rcases h with ⟨d', hd', rfl⟩ | h
    · exact .inl ⟨d', hd', rfl⟩
    · exact .inr h

theorem mem_deriv_mkInter {a : α} {x y d : Regex σ} (h : d ∈ deriv m a (mkInter x y)) :
    (∃ x' ∈ deriv m a x, d = mkInter x' y) ∨ (∃ y' ∈ deriv m a y, d = mkInter x y') := by
  unfold mkInter at h
  split at h
  · exact .inr ⟨d, h, rfl⟩
  · exact .inl ⟨d, h, (mkInter_eps_right d).symm⟩
  · simp only [deriv, List.mem_append, List.mem_map] at h
    rcases h with ⟨x', hx', rfl⟩ | ⟨y', hy', rfl⟩
    · exact .inl ⟨x', hx', rfl⟩
    · exact .inr ⟨y', hy', rfl⟩

/-- `states r` holds the derivatives of `r` and is closed under taking derivatives. -/
theorem deriv_mem_states (r : Regex σ) :
    (∀ a, ∀ d ∈ deriv m a r, d ∈ states r) ∧
      ∀ x ∈ states r, ∀ a, ∀ d ∈ deriv m a x, d ∈ states r := by
  induction r using ind with
  | empty => simp [deriv, states]
  | eps => simp [deriv, states]
  | sym s =>
    refine ⟨fun a d h => ?_, fun x hx a d h => ?_⟩
    · simp only [deriv] at h
      split at h <;> simp_all [states]
    · simp only [states, List.mem_singleton] at hx
      subst hx
      simp [deriv] at h
  | cat r s ihr ihs =>
    simp only [states, List.mem_append, List.mem_map]
    refine ⟨fun a d h => ?_, ?_⟩
    · simp only [deriv, List.mem_append, List.mem_map, List.mem_ite_nil_right] at h
      rcases h with ⟨d', hd', rfl⟩ | ⟨_, h⟩
      · exact .inl ⟨d', ihr.1 a d' hd', rfl⟩
      · exact .inr (ihs.1 a d h)
    · rintro x (⟨y, hy, rfl⟩ | hx) a d h
      · rcases mem_deriv_mkCat h with ⟨d', hd', rfl⟩ | ⟨_, h⟩
        · exact .inl ⟨d', ihr.2 y hy a d' hd', rfl⟩
        · exact .inr (ihs.1 a d h)
      · exact .inr (ihs.2 x hx a d h)
  | alt r s ihr ihs =>
    simp only [states, List.mem_append]
    refine ⟨fun a d h => ?_, ?_⟩
    · simp only [deriv, List.mem_append] at h
      exact h.imp (ihr.1 a d) (ihs.1 a d)
    · rintro x (hx | hx) a d h
      · exact .inl (ihr.2 x hx a d h)
      · exact .inr (ihs.2 x hx a d h)
  | star r ih =>
    have hstar : ∀ a, ∀ d ∈ deriv m a (.star r), d ∈ states (.star r) := by
      intro a d h
      simp only [deriv, List.mem_map] at h
      obtain ⟨d', hd', rfl⟩ := h
      simpa [states] using ⟨d', ih.1 a d' hd', rfl⟩
    refine ⟨hstar, ?_⟩
    simp only [states, List.mem_map]
    rintro _ ⟨y, hy, rfl⟩ a d h
    rcases mem_deriv_mkCat h with ⟨d', hd', rfl⟩ | ⟨_, h⟩
    · exact ⟨d', ih.2 y hy a d' hd', rfl⟩
    · simpa [states] using hstar a d h
  | interleave r s ihr ihs =>
    have hr : ∀ x ∈ r :: states r, ∀ a, ∀ d ∈ deriv m a x, d ∈ states r := by
      intro x hx a d h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ihr.1 a d h
      · exact ihr.2 x hx a d h
    have hs : ∀ y ∈ s :: states s, ∀ a, ∀ d ∈ deriv m a y, d ∈ states s := by
      intro y hy a d h
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ihs.1 a d h
      · exact ihs.2 y hy a d h
    simp only [states, List.mem_flatMap, List.mem_map]
    refine ⟨fun a d h => ?_, ?_⟩
    · simp only [deriv, List.mem_append, List.mem_map] at h
      rcases h with ⟨x', hx', rfl⟩ | ⟨y', hy', rfl⟩
      · exact ⟨x', by simp [ihr.1 a x' hx'], s, by simp, rfl⟩
      · exact ⟨r, by simp, y', by simp [ihs.1 a y' hy'], rfl⟩
    · rintro _ ⟨x, hx, y, hy, rfl⟩ a d h
      rcases mem_deriv_mkInter h with ⟨x', hx', rfl⟩ | ⟨y', hy', rfl⟩
      · exact ⟨x', by simp [hr x hx a x' hx'], y, hy, rfl⟩
      · exact ⟨x, hx, y', by simp [hs y hy a y' hy'], rfl⟩
  | nonEmpty r ih => simpa [deriv, states] using ih
  | allOf rs ih =>
    have hderiv : ∀ sub, sub.Sublist rs → ∀ a, ∀ d ∈ deriv m a (.allOf sub),
        d ∈ states (.allOf rs) := by
      intro sub hsub a d h
      obtain ⟨l₁, r, l₂, rfl, d', hd', rfl⟩ := mem_deriv_allOf.1 h
      have hr : r ∈ rs := hsub.mem (by simp)
      simp only [states, List.mem_flatMap, List.mem_map]
      exact ⟨l₁ ++ l₂, mem_sublists_of_sublist ((by simp : (l₁ ++ l₂).Sublist _).trans hsub),
        d', mem_statesAll.2 ⟨r, hr, (ih r hr).1 a d' hd'⟩, rfl⟩
    refine ⟨hderiv rs (List.Sublist.refl _), ?_⟩
    intro x hx a d h
    simp only [states, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨sub, hsub, y, hy, rfl⟩ := hx
    obtain ⟨r, hr, hy⟩ := mem_statesAll.1 hy
    rcases mem_deriv_mkCat h with ⟨d', hd', rfl⟩ | ⟨_, h⟩
    · simp only [states, List.mem_flatMap, List.mem_map]
      exact ⟨sub, hsub, d', mem_statesAll.2 ⟨r, hr, (ih r hr).2 y hy a d' hd'⟩, rfl⟩
    · exact hderiv sub (sublist_of_mem_sublists hsub) a d h

end Regex

end Regular
