/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Regular.Regex

@[expose] public section

namespace Regular

universe u v

section Shuffle

variable {α : Type v} {a : α} {u v w : List α}

theorem shuffle_nil_iff : Shuffle u v [] ↔ u = [] ∧ v = [] :=
  ⟨fun h => by cases h; exact ⟨rfl, rfl⟩, fun ⟨hu, hv⟩ => by subst hu hv; exact .nil⟩

theorem shuffle_nil_left_iff : Shuffle [] v w ↔ v = w := by
  constructor
  · intro h
    generalize hu : ([] : List α) = u at h
    induction h with
    | nil => rfl
    | left => cases hu
    | right _ ih => rw [ih hu]
  · rintro rfl
    induction v with
    | nil => exact .nil
    | cons _ _ ih => exact .right ih

theorem shuffle_nil_right_iff : Shuffle u [] w ↔ u = w := by
  constructor
  · intro h
    generalize hv : ([] : List α) = v at h
    induction h with
    | nil => rfl
    | left _ ih => rw [ih hv]
    | right => cases hv
  · rintro rfl
    induction u with
    | nil => exact .nil
    | cons _ _ ih => exact .left ih

theorem shuffle_cons_iff : Shuffle u v (a :: w) ↔
    (∃ u', u = a :: u' ∧ Shuffle u' v w) ∨ (∃ v', v = a :: v' ∧ Shuffle u v' w) := by
  constructor
  · intro h
    cases h with
    | left h => exact .inl ⟨_, rfl, h⟩
    | right h => exact .inr ⟨_, rfl, h⟩
  · rintro (⟨_, rfl, h⟩ | ⟨_, rfl, h⟩)
    · exact .left h
    · exact .right h

end Shuffle

namespace Regex

variable {σ : Type u} {α : Type v} {m : α → σ → Bool} {r s : Regex σ} {w : List α}

section Inversion

theorem matches_eps_iff : Matches m .eps w ↔ w = [] :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .eps⟩

theorem not_matches_empty : ¬ Matches m .empty w := fun h => by cases h

theorem matches_sym_iff {s : σ} : Matches m (.sym s) w ↔ ∃ a, w = [a] ∧ m a s = true :=
  ⟨fun h => by cases h with | sym h => exact ⟨_, rfl, h⟩, fun ⟨_, hw, h⟩ => hw ▸ .sym h⟩

theorem matches_cat_iff :
    Matches m (.cat r s) w ↔ ∃ u v, w = u ++ v ∧ Matches m r u ∧ Matches m s v :=
  ⟨fun h => by cases h with | cat hr hs => exact ⟨_, _, rfl, hr, hs⟩,
   fun ⟨_, _, hw, hr, hs⟩ => hw ▸ .cat hr hs⟩

theorem matches_alt_iff : Matches m (.alt r s) w ↔ Matches m r w ∨ Matches m s w :=
  ⟨fun h => by cases h with | altLeft h => exact .inl h | altRight h => exact .inr h,
   fun h => h.elim .altLeft .altRight⟩

theorem matches_star_iff : Matches m (.star r) w ↔
    w = [] ∨ ∃ u v, w = u ++ v ∧ Matches m r u ∧ Matches m (.star r) v :=
  ⟨fun h => by
    cases h with
    | starNil => exact .inl rfl
    | starCons hr hs => exact .inr ⟨_, _, rfl, hr, hs⟩,
   fun h => h.elim (fun hw => hw ▸ .starNil) fun ⟨_, _, hw, hr, hs⟩ => hw ▸ .starCons hr hs⟩

theorem matches_interleave_iff :
    Matches m (.interleave r s) w ↔ ∃ u v, Matches m r u ∧ Matches m s v ∧ Shuffle u v w :=
  ⟨fun h => by cases h with | interleave hr hs h => exact ⟨_, _, hr, hs, h⟩,
   fun ⟨_, _, hr, hs, h⟩ => .interleave hr hs h⟩

theorem matches_nonEmpty_iff : Matches m (.nonEmpty r) w ↔ w ≠ [] ∧ Matches m r w := by
  constructor
  · intro h
    cases h with | nonEmpty h => exact ⟨List.cons_ne_nil _ _, h⟩
  · rintro ⟨hw, h⟩
    obtain ⟨_, _, rfl⟩ := List.exists_cons_of_ne_nil hw
    exact .nonEmpty h

theorem matches_allOf_iff {qs : List (Regex σ)} : Matches m (.allOf qs) w ↔ (qs = [] ∧ w = []) ∨
    ∃ r rs u v, (r :: rs).Perm qs ∧ w = u ++ v ∧ Matches m r u ∧ Matches m (.allOf rs) v := by
  constructor
  · intro h
    cases h with
    | allOfNil => exact .inl ⟨rfl, rfl⟩
    | allOfCons hr hrs hp => exact .inr ⟨_, _, _, _, hp, rfl, hr, hrs⟩
  · rintro (⟨rfl, rfl⟩ | ⟨_, _, _, _, hp, rfl, hr, hrs⟩)
    · exact .allOfNil
    · exact .allOfCons hr hrs hp

theorem _root_.Regular.Matches.allOf_perm {rs qs : List (Regex σ)} (h : Matches m (.allOf rs) w)
    (hp : rs.Perm qs) : Matches m (.allOf qs) w := by
  rcases matches_allOf_iff.1 h with ⟨rfl, rfl⟩ | ⟨_, _, _, _, hp', rfl, hr, hrs⟩
  · rw [List.nil_perm.1 hp]
    exact .allOfNil
  · exact .allOfCons hr hrs (hp'.trans hp)

private theorem forall_of_matches_allOf_nil {x : Regex σ} (h : Matches m x w) :
    ∀ rs, x = .allOf rs → w = [] → ∀ r ∈ rs, Matches m r [] := by
  induction h with
  | allOfNil => intro _ h _ _ hr; cases h; cases hr
  | allOfCons hr _ hp _ ih =>
    intro _ hq hw _ hr'
    cases hq
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hw
    rcases List.mem_cons.1 (hp.mem_iff.2 hr') with rfl | h
    · exact hr
    · exact ih _ rfl rfl _ h
  | _ => intro _ h; cases h

theorem matches_allOf_nil_iff {rs : List (Regex σ)} :
    Matches m (.allOf rs) [] ↔ ∀ r ∈ rs, Matches m r [] := by
  refine ⟨fun h => forall_of_matches_allOf_nil h rs rfl rfl, fun h => ?_⟩
  induction rs with
  | nil => exact .allOfNil
  | cons r rs ih =>
    simpa using Matches.allOfCons (h r (by simp)) (ih fun x hx => h x (by simp [hx]))
      (List.Perm.refl _)

private theorem exists_of_matches_allOf_cons {x : Regex σ} {w' : List α} (h : Matches m x w') :
    ∀ qs a w, x = .allOf qs → w' = a :: w → ∃ r rs u v,
      (r :: rs).Perm qs ∧ w = u ++ v ∧ Matches m r (a :: u) ∧ Matches m (.allOf rs) v := by
  induction h with
  | @allOfCons r rs qs u v hr hrs hp _ ih =>
    intro _ a w hq hw
    cases hq
    cases u with
    | nil =>
      obtain ⟨r', rs', u', v', hp', rfl, hr', hrs'⟩ := ih rs a w rfl (by simpa using hw)
      refine ⟨r', r :: rs', u', v', ((List.Perm.swap r r' rs').trans (hp'.cons r)).trans hp,
        rfl, hr', ?_⟩
      simpa using Matches.allOfCons hr hrs' (List.Perm.refl _)
    | cons b u =>
      simp only [List.cons_append, List.cons.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨r, rs, u, v, hp, rfl, hr, hrs⟩
  | allOfNil => intro _ _ _ _ hw; cases hw
  | _ => intro _ _ _ hx; cases hx

/-- A nonempty word of `allOf qs` starts with a block of one member whose word is nonempty. -/
theorem matches_allOf_cons_iff {qs : List (Regex σ)} {a : α} :
    Matches m (.allOf qs) (a :: w) ↔ ∃ r rs u v,
      (r :: rs).Perm qs ∧ w = u ++ v ∧ Matches m r (a :: u) ∧ Matches m (.allOf rs) v := by
  refine ⟨fun h => exists_of_matches_allOf_cons h qs a w rfl rfl, ?_⟩
  rintro ⟨_, _, _, _, hp, rfl, hr, hrs⟩
  exact .allOfCons hr hrs hp

private theorem exists_of_matches_star_cons {x : Regex σ} {w' : List α} (h : Matches m x w') :
    ∀ r a w, x = .star r → w' = a :: w →
      ∃ u v, w = u ++ v ∧ Matches m r (a :: u) ∧ Matches m (.star r) v := by
  induction h with
  | @starCons r u v hr hs _ ih =>
    intro _ a w hx hw
    cases hx
    cases u with
    | nil => exact ih r a w rfl (by simpa using hw)
    | cons b u =>
      simp only [List.cons_append, List.cons.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨u, v, rfl, hr, hs⟩
  | starNil => intro _ _ _ _ hw; cases hw
  | _ => intro _ _ _ hx; cases hx

/-- A nonempty word of `star r` starts with a nonempty word of `r`. -/
theorem matches_star_cons_iff {a : α} : Matches m (.star r) (a :: w) ↔
    ∃ u v, w = u ++ v ∧ Matches m r (a :: u) ∧ Matches m (.star r) v := by
  refine ⟨fun h => exists_of_matches_star_cons h r a w rfl rfl, ?_⟩
  rintro ⟨_, _, rfl, hr, hs⟩
  exact .starCons hr hs

end Inversion

mutual
def nullable : Regex σ → Bool
  | .empty => false
  | .eps => true
  | .sym _ => false
  | .cat r s => nullable r && nullable s
  | .alt r s => nullable r || nullable s
  | .star _ => true
  | .interleave r s => nullable r && nullable s
  | .nonEmpty _ => false
  | .allOf rs => nullableAll rs

def nullableAll : List (Regex σ) → Bool
  | [] => true
  | r :: rs => nullable r && nullableAll rs
end

theorem nullableAll_eq (rs : List (Regex σ)) : nullableAll rs = rs.all nullable := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [nullableAll, ih]

theorem nullable_iff : nullable r = true ↔ Matches m r [] := by
  induction r using ind with
  | empty => simp [nullable, not_matches_empty]
  | eps => simp [nullable, Matches.eps]
  | sym => simp [nullable, matches_sym_iff]
  | cat r s ihr ihs =>
    simp only [nullable, Bool.and_eq_true, ihr, ihs, matches_cat_iff, List.nil_eq_append_iff]
    exact ⟨fun ⟨hr, hs⟩ => ⟨_, _, ⟨rfl, rfl⟩, hr, hs⟩,
      fun ⟨_, _, ⟨hu, hv⟩, hr, hs⟩ => by subst hu hv; exact ⟨hr, hs⟩⟩
  | alt r s ihr ihs => simp [nullable, matches_alt_iff, ihr, ihs]
  | star => simp [nullable, Matches.starNil]
  | interleave r s ihr ihs =>
    simp only [nullable, Bool.and_eq_true, ihr, ihs, matches_interleave_iff, shuffle_nil_iff]
    exact ⟨fun ⟨hr, hs⟩ => ⟨_, _, hr, hs, rfl, rfl⟩,
      fun ⟨_, _, hr, hs, hu, hv⟩ => by subst hu hv; exact ⟨hr, hs⟩⟩
  | nonEmpty => simp [nullable, matches_nonEmpty_iff]
  | allOf rs ih =>
    simp only [nullable, nullableAll_eq, List.all_eq_true, matches_allOf_nil_iff]
    exact forall₂_congr fun r hr => ih r hr

/-- `cat`, collapsing an `eps` left behind by a derivative so that equal states compare equal. -/
def mkCat : Regex σ → Regex σ → Regex σ
  | .eps, s => s
  | r, s => .cat r s

/-- `interleave`, collapsing an `eps` on either side. -/
def mkInter : Regex σ → Regex σ → Regex σ
  | .eps, s => s
  | r, .eps => r
  | r, s => .interleave r s

theorem mkInter_eps_right (r : Regex σ) : mkInter r .eps = r := by
  cases r <;> rfl

theorem matches_mkCat : Matches m (mkCat r s) w ↔ Matches m (.cat r s) w := by
  cases r <;> try rfl
  simp only [mkCat, matches_cat_iff]
  exact ⟨fun h => ⟨[], w, rfl, .eps, h⟩, fun ⟨_, _, hw, hu, hv⟩ => by
    rw [matches_eps_iff.1 hu] at hw; exact hw ▸ hv⟩

theorem matches_mkInter : Matches m (mkInter r s) w ↔ Matches m (.interleave r s) w := by
  unfold mkInter
  split
  · simp [matches_interleave_iff, matches_eps_iff, shuffle_nil_left_iff]
  · simp [matches_interleave_iff, matches_eps_iff, shuffle_nil_right_iff]
  · rfl

mutual
/-- Antimirov's partial derivatives of `r` by `a`, whose languages between them hold exactly the
`w` with `a :: w` in the language of `r`; `matches_cons_iff` proves it. -/
def deriv (m : α → σ → Bool) (a : α) : Regex σ → List (Regex σ)
  | .empty | .eps => []
  | .sym s => if m a s then [.eps] else []
  | .cat r s => (deriv m a r).map (mkCat · s) ++ if nullable r then deriv m a s else []
  | .alt r s => deriv m a r ++ deriv m a s
  | .star r => (deriv m a r).map (mkCat · (.star r))
  | .interleave r s => (deriv m a r).map (mkInter · s) ++ (deriv m a s).map (mkInter r ·)
  | .nonEmpty r => deriv m a r
  | .allOf rs => derivAll m a [] rs

/-- The derivatives of `allOf (pre ++ post)` whose first block is a member of `post`. -/
def derivAll (m : α → σ → Bool) (a : α) (pre : List (Regex σ)) :
    List (Regex σ) → List (Regex σ)
  | [] => []
  | r :: post =>
    (deriv m a r).map (mkCat · (.allOf (pre ++ post))) ++ derivAll m a (pre ++ [r]) post
end

theorem mem_derivAll {a : α} {pre post : List (Regex σ)} {d : Regex σ} :
    d ∈ derivAll m a pre post ↔ ∃ l₁ r l₂, post = l₁ ++ r :: l₂ ∧
      ∃ d' ∈ deriv m a r, d = mkCat d' (.allOf (pre ++ l₁ ++ l₂)) := by
  induction post generalizing pre with
  | nil => simp [derivAll]
  | cons r post ih =>
    simp only [derivAll, List.mem_append, List.mem_map, ih]
    constructor
    · rintro (⟨d', hd', rfl⟩ | ⟨l₁, r', l₂, rfl, d', hd', rfl⟩)
      · exact ⟨[], r, post, rfl, d', hd', by simp⟩
      · exact ⟨r :: l₁, r', l₂, rfl, d', hd', by simp⟩
    · rintro ⟨l₁, r', l₂, h, d', hd', rfl⟩
      cases l₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inl ⟨d', hd', by simp⟩
      | cons x l₁ =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr ⟨l₁, r', l₂, rfl, d', hd', by simp⟩

theorem mem_deriv_allOf {a : α} {qs : List (Regex σ)} {d : Regex σ} :
    d ∈ deriv m a (.allOf qs) ↔ ∃ l₁ r l₂, qs = l₁ ++ r :: l₂ ∧
      ∃ d' ∈ deriv m a r, d = mkCat d' (.allOf (l₁ ++ l₂)) := by
  simp [deriv, mem_derivAll]

theorem matches_cons_iff {a : α} : Matches m r (a :: w) ↔ ∃ d ∈ deriv m a r, Matches m d w := by
  induction r using ind generalizing w with
  | empty => simp [deriv, not_matches_empty]
  | eps => simp [deriv, matches_eps_iff]
  | sym s =>
    simp only [matches_sym_iff, deriv]
    constructor
    · rintro ⟨_, h, hs⟩
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.eps, by simp [hs], .eps⟩
    · rintro ⟨d, hd, hdw⟩
      split at hd
      · simp only [List.mem_singleton] at hd
        subst hd
        exact ⟨a, by rw [matches_eps_iff.1 hdw], ‹_›⟩
      · cases hd
  | cat r s ihr ihs =>
    simp only [matches_cat_iff, deriv, List.mem_append, List.mem_map, List.mem_ite_nil_right]
    constructor
    · rintro ⟨u, v, huv, hr, hs⟩
      cases u with
      | nil =>
        simp only [List.nil_append] at huv
        subst huv
        obtain ⟨d, hd, hdw⟩ := ihs.1 hs
        exact ⟨d, .inr ⟨nullable_iff.2 hr, hd⟩, hdw⟩
      | cons b u =>
        simp only [List.cons_append, List.cons.injEq] at huv
        obtain ⟨rfl, rfl⟩ := huv
        obtain ⟨d, hd, hdu⟩ := ihr.1 hr
        exact ⟨mkCat d s, .inl ⟨d, hd, rfl⟩, matches_mkCat.2 (.cat hdu hs)⟩
    · rintro ⟨d, ⟨d', hd', rfl⟩ | ⟨hn, hd⟩, hdw⟩
      · obtain ⟨u, v, rfl, hu, hv⟩ := matches_cat_iff.1 (matches_mkCat.1 hdw)
        exact ⟨a :: u, v, rfl, ihr.2 ⟨d', hd', hu⟩, hv⟩
      · exact ⟨[], a :: w, rfl, nullable_iff.1 hn, ihs.2 ⟨d, hd, hdw⟩⟩
  | alt r s ihr ihs =>
    simp only [matches_alt_iff, deriv, List.mem_append, ihr, ihs]
    constructor
    · rintro (⟨d, hd, h⟩ | ⟨d, hd, h⟩)
      · exact ⟨d, .inl hd, h⟩
      · exact ⟨d, .inr hd, h⟩
    · rintro ⟨d, hd | hd, h⟩
      · exact .inl ⟨d, hd, h⟩
      · exact .inr ⟨d, hd, h⟩
  | star r ihr =>
    simp only [matches_star_cons_iff, deriv, List.mem_map]
    constructor
    · rintro ⟨u, v, rfl, hr, hs⟩
      obtain ⟨d, hd, hdu⟩ := ihr.1 hr
      exact ⟨mkCat d (.star r), ⟨d, hd, rfl⟩, matches_mkCat.2 (.cat hdu hs)⟩
    · rintro ⟨_, ⟨d', hd', rfl⟩, hdw⟩
      obtain ⟨u, v, rfl, hu, hv⟩ := matches_cat_iff.1 (matches_mkCat.1 hdw)
      exact ⟨u, v, rfl, ihr.2 ⟨d', hd', hu⟩, hv⟩
  | interleave r s ihr ihs =>
    simp only [matches_interleave_iff, deriv, List.mem_append, List.mem_map]
    constructor
    · rintro ⟨u, v, hr, hs, hsh⟩
      rcases shuffle_cons_iff.1 hsh with ⟨u', rfl, hsh'⟩ | ⟨v', rfl, hsh'⟩
      · obtain ⟨d, hd, hdu⟩ := ihr.1 hr
        exact ⟨mkInter d s, .inl ⟨d, hd, rfl⟩, matches_mkInter.2 (.interleave hdu hs hsh')⟩
      · obtain ⟨d, hd, hdv⟩ := ihs.1 hs
        exact ⟨mkInter r d, .inr ⟨d, hd, rfl⟩, matches_mkInter.2 (.interleave hr hdv hsh')⟩
    · rintro ⟨_, ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩, hdw⟩
      · obtain ⟨u, v, hu, hv, hsh⟩ := matches_interleave_iff.1 (matches_mkInter.1 hdw)
        exact ⟨a :: u, v, ihr.2 ⟨d', hd', hu⟩, hv, .left hsh⟩
      · obtain ⟨u, v, hu, hv, hsh⟩ := matches_interleave_iff.1 (matches_mkInter.1 hdw)
        exact ⟨u, a :: v, hu, ihs.2 ⟨d', hd', hv⟩, .right hsh⟩
  | nonEmpty r ihr => simp [matches_nonEmpty_iff, deriv, ihr]
  | allOf qs ih =>
    simp only [matches_allOf_cons_iff, mem_deriv_allOf]
    constructor
    · rintro ⟨r, rs, u, v, hp, rfl, hr, hrs⟩
      have hmem : r ∈ qs := hp.mem_iff.1 (by simp)
      obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hmem
      obtain ⟨d', hd', hdu⟩ := (ih r hmem).1 hr
      refine ⟨_, ⟨l₁, r, l₂, rfl, d', hd', rfl⟩, matches_mkCat.2 (.cat hdu ?_)⟩
      exact hrs.allOf_perm (hp.trans List.perm_middle).cons_inv
    · rintro ⟨_, ⟨l₁, r, l₂, rfl, d', hd', rfl⟩, hdw⟩
      obtain ⟨u, v, rfl, hu, hv⟩ := matches_cat_iff.1 (matches_mkCat.1 hdw)
      exact ⟨r, l₁ ++ l₂, u, v, List.perm_middle.symm, rfl, (ih r (by simp)).2 ⟨d', hd', hu⟩, hv⟩

end Regex

end Regular
