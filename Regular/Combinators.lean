/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Regular.Deriv

@[expose] public section

namespace Regular

universe u v

namespace Regex

variable {σ : Type u} {α : Type v} {m : α → σ → Bool} {r sep : Regex σ} {w : List α}

def opt (r : Regex σ) : Regex σ := .alt .eps r

/-- One or more. -/
def plus (r : Regex σ) : Regex σ := .cat r (.star r)

/-- Exactly `n` in sequence. -/
def pow : Nat → Regex σ → Regex σ
  | 0, _ => .eps
  | n + 1, r => .cat r (pow n r)

/-- At most `n` in sequence, nested so that each optional copy follows the one before. -/
def upTo : Nat → Regex σ → Regex σ
  | 0, _ => .eps
  | n + 1, r => opt (.cat r (upTo n r))

/-- From `lo` to `hi` in sequence, CSS's `{lo,hi}`. -/
def rep (lo hi : Nat) (r : Regex σ) : Regex σ :=
  if lo ≤ hi then .cat (pow lo r) (upTo (hi - lo) r) else .empty

/-- At least `lo` in sequence, CSS's `{lo,}`. -/
def atLeast (lo : Nat) (r : Regex σ) : Regex σ := .cat (pow lo r) (.star r)

/-- One or more, with `sep` between each and the next, as CSS's `#` with `sep` a comma. -/
def sepBy1 (r sep : Regex σ) : Regex σ := .cat r (.star (.cat sep r))

def seq (rs : List (Regex σ)) : Regex σ := rs.foldr .cat .eps

def oneOf (rs : List (Regex σ)) : Regex σ := rs.foldr .alt .empty

/-- One or more of `rs` in any order, each at most once, as CSS's `||`. -/
def someOf (rs : List (Regex σ)) : Regex σ := .nonEmpty (.allOf (rs.map opt))

theorem matches_opt : Matches m (opt r) w ↔ w = [] ∨ Matches m r w := by
  simp [opt, matches_alt_iff, matches_eps_iff]

private theorem flatten_of_matches_star {x : Regex σ} (h : Matches m x w) :
    ∀ r, x = .star r → ∃ ws : List (List α), (∀ v ∈ ws, Matches m r v) ∧ w = ws.flatten := by
  induction h with
  | starNil => intro _ _; exact ⟨[], by simp, rfl⟩
  | @starCons r u v hr _ _ ih =>
    intro _ hx
    cases hx
    obtain ⟨ws, hws, rfl⟩ := ih r rfl
    exact ⟨u :: ws, List.forall_mem_cons.2 ⟨hr, hws⟩, by simp⟩
  | _ => intro _ hx; cases hx

theorem matches_star_iff_flatten :
    Matches m (.star r) w ↔ ∃ ws : List (List α), (∀ v ∈ ws, Matches m r v) ∧ w = ws.flatten := by
  refine ⟨fun h => flatten_of_matches_star h r rfl, ?_⟩
  rintro ⟨ws, hws, rfl⟩
  induction ws with
  | nil => exact .starNil
  | cons v ws ih =>
    obtain ⟨hv, hws⟩ := List.forall_mem_cons.1 hws
    exact .starCons hv (ih hws)

theorem matches_plus :
    Matches m (plus r) w ↔ ∃ ws : List (List α), ws ≠ [] ∧ (∀ v ∈ ws, Matches m r v) ∧ w = ws.flatten := by
  simp only [plus, matches_cat_iff, matches_star_iff_flatten]
  constructor
  · rintro ⟨u, _, rfl, hu, ws, hws, rfl⟩
    exact ⟨u :: ws, by simp, List.forall_mem_cons.2 ⟨hu, hws⟩, rfl⟩
  · rintro ⟨_ | ⟨u, ws⟩, hne, hws, rfl⟩
    · contradiction
    · obtain ⟨hu, hws⟩ := List.forall_mem_cons.1 hws
      exact ⟨u, ws.flatten, rfl, hu, ws, hws, rfl⟩

theorem matches_pow {n : Nat} : Matches m (pow n r) w ↔
    ∃ ws : List (List α), ws.length = n ∧ (∀ v ∈ ws, Matches m r v) ∧ w = ws.flatten := by
  induction n generalizing w with
  | zero =>
    simp only [pow, matches_eps_iff, List.length_eq_zero_iff]
    exact ⟨fun h => ⟨[], rfl, by simp, h⟩, fun ⟨_, h, _, hw⟩ => by simp [hw, h]⟩
  | succ n ih =>
    simp only [pow, matches_cat_iff, ih]
    constructor
    · rintro ⟨u, _, rfl, hu, ws, hlen, hws, rfl⟩
      exact ⟨u :: ws, by simp [hlen], List.forall_mem_cons.2 ⟨hu, hws⟩, rfl⟩
    · rintro ⟨_ | ⟨u, ws⟩, hlen, hws, rfl⟩
      · simp at hlen
      · obtain ⟨hu, hws⟩ := List.forall_mem_cons.1 hws
        exact ⟨u, ws.flatten, rfl, hu, ws, by simpa using hlen, hws, rfl⟩

theorem matches_upTo {n : Nat} : Matches m (upTo n r) w ↔
    ∃ ws : List (List α), ws.length ≤ n ∧ (∀ v ∈ ws, Matches m r v) ∧ w = ws.flatten := by
  induction n generalizing w with
  | zero =>
    simp only [upTo, matches_eps_iff, Nat.le_zero, List.length_eq_zero_iff]
    exact ⟨fun h => ⟨[], rfl, by simp, h⟩, fun ⟨_, h, _, hw⟩ => by simp [hw, h]⟩
  | succ n ih =>
    simp only [upTo, matches_opt, matches_cat_iff, ih]
    constructor
    · rintro (rfl | ⟨u, _, rfl, hu, ws, hlen, hws, rfl⟩)
      · exact ⟨[], by simp, by simp, rfl⟩
      · exact ⟨u :: ws, by simp [hlen], List.forall_mem_cons.2 ⟨hu, hws⟩, rfl⟩
    · rintro ⟨_ | ⟨u, ws⟩, hlen, hws, rfl⟩
      · exact .inl rfl
      · obtain ⟨hu, hws⟩ := List.forall_mem_cons.1 hws
        exact .inr ⟨u, ws.flatten, rfl, hu, ws, by simpa using hlen, hws, rfl⟩

private theorem exists_append_of_flatten {P : List α → Prop} {ws₁ ws₂ : List (List α)} :
    (∀ v ∈ ws₁ ++ ws₂, P v) ↔ (∀ v ∈ ws₁, P v) ∧ ∀ v ∈ ws₂, P v := by
  simp only [List.mem_append]
  exact ⟨fun h => ⟨fun v hv => h v (.inl hv), fun v hv => h v (.inr hv)⟩,
    fun ⟨h₁, h₂⟩ v hv => hv.elim (h₁ v) (h₂ v)⟩

theorem matches_rep {lo hi : Nat} : Matches m (rep lo hi r) w ↔
    ∃ ws : List (List α), lo ≤ ws.length ∧ ws.length ≤ hi ∧ (∀ v ∈ ws, Matches m r v) ∧
      w = ws.flatten := by
  unfold rep
  split
  · constructor
    · intro h
      obtain ⟨u, v, rfl, hu, hv⟩ := matches_cat_iff.1 h
      obtain ⟨ws₁, hlen₁, hws₁, rfl⟩ := matches_pow.1 hu
      obtain ⟨ws₂, hlen₂, hws₂, rfl⟩ := matches_upTo.1 hv
      exact ⟨ws₁ ++ ws₂, by simp; omega, by simp; omega,
        exists_append_of_flatten.2 ⟨hws₁, hws₂⟩, by simp⟩
    · rintro ⟨ws, hlo, hhi, hws, rfl⟩
      rw [← List.take_append_drop lo ws] at hws
      obtain ⟨hws₁, hws₂⟩ := exists_append_of_flatten.1 hws
      exact matches_cat_iff.2 ⟨_, _, by rw [← List.flatten_append, List.take_append_drop],
        matches_pow.2 ⟨ws.take lo, by simp; omega, hws₁, rfl⟩,
        matches_upTo.2 ⟨ws.drop lo, by simp; omega, hws₂, rfl⟩⟩
  · simp only [not_matches_empty, false_iff]
    rintro ⟨_, _, _, _, _⟩
    omega

theorem matches_atLeast {lo : Nat} : Matches m (atLeast lo r) w ↔
    ∃ ws : List (List α), lo ≤ ws.length ∧ (∀ v ∈ ws, Matches m r v) ∧ w = ws.flatten := by
  constructor
  · intro h
    obtain ⟨u, v, rfl, hu, hv⟩ := matches_cat_iff.1 h
    obtain ⟨ws₁, hlen₁, hws₁, rfl⟩ := matches_pow.1 hu
    obtain ⟨ws₂, hws₂, rfl⟩ := matches_star_iff_flatten.1 hv
    exact ⟨ws₁ ++ ws₂, by simp; omega, exists_append_of_flatten.2 ⟨hws₁, hws₂⟩, by simp⟩
  · rintro ⟨ws, hlo, hws, rfl⟩
    rw [← List.take_append_drop lo ws] at hws
    obtain ⟨hws₁, hws₂⟩ := exists_append_of_flatten.1 hws
    exact matches_cat_iff.2 ⟨_, _, by rw [← List.flatten_append, List.take_append_drop],
      matches_pow.2 ⟨ws.take lo, by simp; omega, hws₁, rfl⟩,
      matches_star_iff_flatten.2 ⟨ws.drop lo, hws₂, rfl⟩⟩

theorem matches_sepBy1 : Matches m (sepBy1 r sep) w ↔
    ∃ (v : List α) (ps : List (List α × List α)), Matches m r v ∧
      (∀ p ∈ ps, Matches m sep p.1 ∧ Matches m r p.2) ∧
      w = v ++ (ps.map fun p => p.1 ++ p.2).flatten := by
  constructor
  · intro h
    obtain ⟨v, _, rfl, hv, hs⟩ := matches_cat_iff.1 h
    obtain ⟨ws, hws, rfl⟩ := matches_star_iff_flatten.1 hs
    suffices ∃ ps : List (List α × List α), (∀ p ∈ ps, Matches m sep p.1 ∧ Matches m r p.2) ∧
        ws.flatten = (ps.map fun p => p.1 ++ p.2).flatten by
      obtain ⟨ps, hps, heq⟩ := this
      exact ⟨v, ps, hv, hps, by rw [heq]⟩
    clear h hv hs
    induction ws with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons x ws ih =>
      obtain ⟨hx, hws'⟩ := List.forall_mem_cons.1 hws
      obtain ⟨ps, hps, heq⟩ := ih hws'
      obtain ⟨s, t, rfl, hs, ht⟩ := matches_cat_iff.1 hx
      exact ⟨(s, t) :: ps, List.forall_mem_cons.2 ⟨⟨hs, ht⟩, hps⟩, by simp [heq]⟩
  · rintro ⟨v, ps, hv, hps, rfl⟩
    refine .cat hv (matches_star_iff_flatten.2 ⟨ps.map fun p => p.1 ++ p.2, ?_, rfl⟩)
    simp only [List.mem_map]
    rintro _ ⟨p, hp, rfl⟩
    exact .cat (hps p hp).1 (hps p hp).2

theorem matches_seq {rs : List (Regex σ)} : Matches m (seq rs) w ↔
    ∃ ps : List (Regex σ × List α), ps.map Prod.fst = rs ∧ (∀ p ∈ ps, Matches m p.1 p.2) ∧
      w = (ps.map Prod.snd).flatten := by
  induction rs generalizing w with
  | nil =>
    simp only [seq, List.foldr_nil, matches_eps_iff, List.map_eq_nil_iff]
    exact ⟨fun h => ⟨[], rfl, by simp, h⟩, fun ⟨_, h, _, hw⟩ => by simp [hw, h]⟩
  | cons r rs ih =>
    simp only [seq, List.foldr_cons] at ih ⊢
    simp only [matches_cat_iff, ih]
    constructor
    · rintro ⟨u, _, rfl, hu, ps, rfl, hps, rfl⟩
      exact ⟨(r, u) :: ps, rfl, List.forall_mem_cons.2 ⟨hu, hps⟩, rfl⟩
    · rintro ⟨_ | ⟨⟨r', u⟩, ps⟩, hrs, hps, rfl⟩
      · cases hrs
      · simp only [List.map_cons, List.cons.injEq] at hrs
        obtain ⟨rfl, rfl⟩ := hrs
        obtain ⟨hu, hps⟩ := List.forall_mem_cons.1 hps
        exact ⟨u, _, rfl, hu, ps, rfl, hps, rfl⟩

theorem matches_oneOf {rs : List (Regex σ)} : Matches m (oneOf rs) w ↔ ∃ r ∈ rs, Matches m r w := by
  induction rs with
  | nil => simp [oneOf, not_matches_empty]
  | cons r rs ih => simp only [oneOf, List.foldr_cons] at ih ⊢; simp [matches_alt_iff, ih]

private theorem pairs_of_matches_allOf {β : Type u} {f : β → Regex σ} {x : Regex σ}
    (h : Matches m x w) : ∀ qs rs, x = .allOf qs → qs.Perm (rs.map f) →
      ∃ ps : List (β × List α), (ps.map Prod.fst).Perm rs ∧
        (∀ p ∈ ps, Matches m (f p.1) p.2) ∧ w = (ps.map Prod.snd).flatten := by
  induction h with
  | allOfNil =>
    intro _ rs hx hp
    cases hx
    have : rs = [] := List.map_eq_nil_iff.1 (List.nil_perm.1 hp)
    exact ⟨[], by simp [this], by simp, rfl⟩
  | @allOfCons r rs₀ qs u v hr _ hp _ ih =>
    intro _ rs hx hq
    cases hx
    have hmem : r ∈ rs.map f := (hp.trans hq).mem_iff.1 (by simp)
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hmem
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hy
    have hrest : rs₀.Perm ((l₁ ++ l₂).map f) :=
      ((hp.trans hq).trans (by simp [List.perm_middle])).cons_inv
    obtain ⟨ps, hps, hm, rfl⟩ := ih _ (l₁ ++ l₂) rfl hrest
    exact ⟨(y, u) :: ps, (hps.cons y).trans List.perm_middle.symm,
      List.forall_mem_cons.2 ⟨hr, hm⟩, rfl⟩
  | _ => intro _ _ hx; cases hx

/-- `allOf` of a mapped list, which `someOf` needs; `matches_allOf` is the case `f = id`. -/
theorem matches_allOf_map {β : Type u} {f : β → Regex σ} {rs : List β} :
    Matches m (.allOf (rs.map f)) w ↔ ∃ ps : List (β × List α), (ps.map Prod.fst).Perm rs ∧
      (∀ p ∈ ps, Matches m (f p.1) p.2) ∧ w = (ps.map Prod.snd).flatten := by
  refine ⟨fun h => pairs_of_matches_allOf h _ rs rfl (List.Perm.refl _), ?_⟩
  rintro ⟨ps, hps, hm, rfl⟩
  have hp := hps.map f
  clear hps
  induction ps generalizing rs with
  | nil => exact Matches.allOfNil.allOf_perm (by simpa using hp)
  | cons p ps ih =>
    obtain ⟨hp₁, hm⟩ := List.forall_mem_cons.1 hm
    exact .allOfCons hp₁ (ih (rs := ps.map Prod.fst) hm (List.Perm.refl _)) (by simpa using hp)

theorem matches_allOf {rs : List (Regex σ)} : Matches m (.allOf rs) w ↔
    ∃ ps : List (Regex σ × List α), (ps.map Prod.fst).Perm rs ∧
      (∀ p ∈ ps, Matches m p.1 p.2) ∧ w = (ps.map Prod.snd).flatten := by
  simpa using matches_allOf_map (m := m) (f := id) (rs := rs) (w := w)

private theorem flatten_filter_nonEmpty (ps : List (Regex σ × List α)) :
    ((ps.filter fun p => !p.2.isEmpty).map Prod.snd).flatten = (ps.map Prod.snd).flatten := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨r, _ | ⟨a, u⟩⟩ <;> simp [ih]

/-- `someOf rs` matches exactly the nonempty concatenations of one word each of some of `rs`,
each used at most once, in any order. -/
theorem matches_someOf {rs : List (Regex σ)} : Matches m (someOf rs) w ↔ w ≠ [] ∧
    ∃ (ps : List (Regex σ × List α)) (rest : List (Regex σ)),
      (ps.map Prod.fst ++ rest).Perm rs ∧ (∀ p ∈ ps, Matches m p.1 p.2) ∧
      w = (ps.map Prod.snd).flatten := by
  simp only [someOf, matches_nonEmpty_iff, matches_allOf_map, matches_opt]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨ps, hps, hm, rfl⟩
    let keep (p : Regex σ × List α) : Bool := !p.2.isEmpty
    refine ⟨ps.filter keep, (ps.filter (!keep ·)).map Prod.fst, ?_, ?_, ?_⟩
    · rw [← List.map_append]
      exact ((List.filter_append_perm keep ps).map _).trans hps
    · intro p hp
      simp only [List.mem_filter, keep, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
      exact (hm p hp.1).resolve_left hp.2
    · exact (flatten_filter_nonEmpty ps).symm
  · rintro ⟨ps, rest, hps, hm, rfl⟩
    refine ⟨ps ++ rest.map (·, []), by simpa [Function.comp_def] using hps, fun p hp => ?_, by simp⟩
    rcases List.mem_append.1 hp with hp | hp
    · exact .inr (hm p hp)
    · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hp
      exact .inl rfl

end Regex

end Regular
