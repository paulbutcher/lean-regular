/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Regular.Shape

@[expose] public section

namespace Regular

universe u v w

namespace Regex

variable {σ : Type u} {τ : Type w} {α : Type v}

mutual
def map (g : σ → τ) : Regex σ → Regex τ
  | .empty => .empty
  | .eps => .eps
  | .sym s => .sym (g s)
  | .cat r s => .cat (map g r) (map g s)
  | .alt r s => .alt (map g r) (map g s)
  | .star r => .star (map g r)
  | .interleave r s => .interleave (map g r) (map g s)
  | .nonEmpty r => .nonEmpty (map g r)
  | .allOf rs => .allOf (mapAll g rs)

def mapAll (g : σ → τ) : List (Regex σ) → List (Regex τ)
  | [] => []
  | r :: rs => map g r :: mapAll g rs
end

theorem mapAll_eq (g : σ → τ) (rs : List (Regex σ)) : mapAll g rs = rs.map (map g) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [mapAll, ih]

theorem nullable_map (g : σ → τ) (r : Regex σ) : nullable (r.map g) = nullable r := by
  induction r using ind with
  | allOf rs ih =>
    simp only [map, nullable, nullableAll_eq, mapAll_eq, List.all_map]
    exact Bool.eq_iff_iff.2 (by
      simp only [List.all_eq_true, Function.comp_apply]
      exact forall₂_congr fun r hr => by rw [ih r hr])
  | _ => simp_all [map, nullable]

theorem map_mkCat (g : σ → τ) (r s : Regex σ) : (mkCat r s).map g = mkCat (r.map g) (s.map g) := by
  cases r <;> rfl

theorem map_mkInter (g : σ → τ) (r s : Regex σ) :
    (mkInter r s).map g = mkInter (r.map g) (s.map g) := by
  cases r <;> cases s <;> rfl

theorem deriv_map {m : α → τ → Bool} {a : α} (g : σ → τ) (r : Regex σ) :
    deriv m a (r.map g) = (deriv (fun a s => m a (g s)) a r).map (map g) := by
  induction r using ind with
  | sym s => simp only [map, deriv]; split <;> rfl
  | cat r s ihr ihs =>
    simp only [map, deriv, ihr, ihs, nullable_map, List.map_append, List.map_map]
    split <;> simp [Function.comp_def, map_mkCat]
  | alt r s ihr ihs => simp [map, deriv, ihr, ihs]
  | star r ih => simp [map, deriv, ih, Function.comp_def, map_mkCat]
  | interleave r s ihr ihs => simp [map, deriv, ihr, ihs, Function.comp_def, map_mkInter]
  | nonEmpty r ih => simp [map, deriv, ih]
  | allOf rs ih =>
    simp only [map, deriv, mapAll_eq]
    suffices ∀ pre, derivAll m a (pre.map (map g)) (rs.map (map g)) =
        (derivAll (fun a s => m a (g s)) a pre rs).map (map g) from this []
    intro pre
    induction rs generalizing pre with
    | nil => rfl
    | cons r rs ihs =>
      simp only [List.map_cons, derivAll, ih r (by simp), List.map_append, List.map_map]
      rw [show pre.map (map g) ++ [r.map g] = (pre ++ [r]).map (map g) by simp,
        ihs (fun x hx => ih x (by simp [hx]))]
      simp [Function.comp_def, map_mkCat, map, mapAll_eq]
  | _ => rfl

/-- Renaming symbols moves the renaming into the matching function. -/
theorem matches_map {m : α → τ → Bool} {g : σ → τ} {r : Regex σ} {w : List α} :
    Matches m (r.map g) w ↔ Matches (fun a s => m a (g s)) r w := by
  induction w generalizing r with
  | nil => rw [← nullable_iff, ← nullable_iff, nullable_map]
  | cons a w ih =>
    simp only [matches_cons_iff, deriv_map, List.mem_map]
    exact ⟨fun ⟨_, ⟨d, hd, rfl⟩, h⟩ => ⟨d, hd, ih.1 h⟩, fun ⟨d, hd, h⟩ => ⟨_, ⟨d, hd, rfl⟩, ih.2 h⟩⟩

theorem deriv_comap {β : Type w} {m : α → σ → Bool} (f : β → α) (b : β) (r : Regex σ) :
    deriv (fun b s => m (f b) s) b r = deriv m (f b) r := by
  induction r using ind with
  | allOf rs ih =>
    simp only [deriv]
    suffices ∀ pre, derivAll (fun b s => m (f b) s) b pre rs = derivAll m (f b) pre rs from this []
    intro pre
    induction rs generalizing pre with
    | nil => rfl
    | cons r rs ihs =>
      simp only [derivAll, ih r (by simp), ihs (fun x hx => ih x (by simp [hx]))]
  | _ => simp_all [deriv]

/-- Renaming letters moves the renaming into the matching function. -/
theorem matches_comap {β : Type w} {m : α → σ → Bool} {f : β → α} {r : Regex σ} {w : List β} :
    Matches (fun b s => m (f b) s) r w ↔ Matches m r (w.map f) := by
  induction w generalizing r with
  | nil => rw [List.map_nil, ← nullable_iff, ← nullable_iff]
  | cons b w ih => simp only [matches_cons_iff, deriv_comap, List.map_cons, ih]

theorem _root_.Regular.Matches.mono {m m' : α → σ → Bool} {r : Regex σ} {w : List α} (h : Matches m r w)
    (hm : ∀ a s, m a s = true → m' a s = true) : Matches m' r w := by
  induction h with
  | eps => exact .eps
  | sym h => exact .sym (hm _ _ h)
  | cat _ _ ih₁ ih₂ => exact .cat ih₁ ih₂
  | altLeft _ ih => exact .altLeft ih
  | altRight _ ih => exact .altRight ih
  | starNil => exact .starNil
  | starCons _ _ ih₁ ih₂ => exact .starCons ih₁ ih₂
  | interleave _ _ hsh ih₁ ih₂ => exact .interleave ih₁ ih₂ hsh
  | nonEmpty _ ih => exact .nonEmpty ih
  | allOfNil => exact .allOfNil
  | allOfCons _ _ hp ih₁ ih₂ => exact .allOfCons ih₁ ih₂ hp

end Regex

namespace Shape

open Regex

variable {α : Type v}

mutual
def indexFrom : Nat → Regex α → Regex (Nat × α) × Nat
  | n, .empty => (.empty, n)
  | n, .eps => (.eps, n)
  | n, .sym a => (.sym (n, a), n + 1)
  | n, .cat r s =>
    let p := indexFrom n r
    let q := indexFrom p.2 s
    (.cat p.1 q.1, q.2)
  | n, .alt r s =>
    let p := indexFrom n r
    let q := indexFrom p.2 s
    (.alt p.1 q.1, q.2)
  | n, .star r =>
    let p := indexFrom n r
    (.star p.1, p.2)
  | n, .interleave r s =>
    let p := indexFrom n r
    let q := indexFrom p.2 s
    (.interleave p.1 q.1, q.2)
  | n, .nonEmpty r =>
    let p := indexFrom n r
    (.nonEmpty p.1, p.2)
  | n, .allOf rs =>
    let p := indexFromAll n rs
    (.allOf p.1, p.2)

def indexFromAll : Nat → List (Regex α) → List (Regex (Nat × α)) × Nat
  | n, [] => ([], n)
  | n, r :: rs =>
    let p := indexFrom n r
    let q := indexFromAll p.2 rs
    (p.1 :: q.1, q.2)
end

/-- `s` with each letter tagged by the position of its `sym`, numbered from 0 left to right, so
that a counterexample to the indexed shape says which part of `s` produced each letter. -/
def indexed (s : Regex α) : Regex (Nat × α) := (indexFrom 0 s).1

theorem map_snd_indexFrom (n : Nat) (s : Regex α) : (indexFrom n s).1.map Prod.snd = s := by
  induction s using ind generalizing n with
  | allOf rs ih =>
    simp only [indexFrom, map, allOf.injEq, mapAll_eq]
    induction rs generalizing n with
    | nil => rfl
    | cons r rs ihs =>
      simp only [indexFromAll, List.map_cons, ih r (by simp),
        ihs (fun x hx => ih x (by simp [hx]))]
  | _ => simp_all [indexFrom, map]

variable [DecidableEq α]

private theorem exists_tag {a : α} {d : Regex (Nat × α)} {r : Regex (Nat × α)}
    (h : d ∈ deriv (fun a p => a == p.2) a r) : ∃ n, d ∈ deriv (· == ·) (n, a) r := by
  induction r using ind generalizing d with
  | empty | eps => simp [deriv] at h
  | sym p =>
    simp only [deriv] at h
    split at h
    · exact ⟨p.1, by simp_all [deriv]⟩
    · cases h
  | cat r s ihr ihs =>
    simp only [deriv, List.mem_append, List.mem_map, List.mem_ite_nil_right] at h
    rcases h with ⟨d', hd', rfl⟩ | ⟨hn, hd⟩
    · obtain ⟨n, hn⟩ := ihr hd'
      exact ⟨n, by simp only [deriv, List.mem_append, List.mem_map]; exact .inl ⟨d', hn, rfl⟩⟩
    · obtain ⟨n, hn'⟩ := ihs hd
      exact ⟨n, by simp [deriv, hn, hn']⟩
  | alt r s ihr ihs =>
    simp only [deriv, List.mem_append] at h
    rcases h with hd | hd
    · obtain ⟨n, hn⟩ := ihr hd; exact ⟨n, by simp [deriv, hn]⟩
    · obtain ⟨n, hn⟩ := ihs hd; exact ⟨n, by simp [deriv, hn]⟩
  | star r ih =>
    simp only [deriv, List.mem_map] at h
    obtain ⟨d', hd', rfl⟩ := h
    obtain ⟨n, hn⟩ := ih hd'
    exact ⟨n, by simp only [deriv, List.mem_map]; exact ⟨d', hn, rfl⟩⟩
  | interleave r s ihr ihs =>
    simp only [deriv, List.mem_append, List.mem_map] at h
    rcases h with ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩
    · obtain ⟨n, hn⟩ := ihr hd'
      exact ⟨n, by simp only [deriv, List.mem_append, List.mem_map]; exact .inl ⟨d', hn, rfl⟩⟩
    · obtain ⟨n, hn⟩ := ihs hd'
      exact ⟨n, by simp only [deriv, List.mem_append, List.mem_map]; exact .inr ⟨d', hn, rfl⟩⟩
  | nonEmpty r ih => simpa [deriv] using ih (by simpa [deriv] using h)
  | allOf rs ih =>
    obtain ⟨l₁, r, l₂, rfl, d', hd', rfl⟩ := mem_deriv_allOf.1 h
    obtain ⟨n, hn⟩ := ih r (by simp) hd'
    exact ⟨n, mem_deriv_allOf.2 ⟨l₁, r, l₂, rfl, d', hn, rfl⟩⟩

private theorem matches_untagged {r : Regex (Nat × α)} {v : List α} :
    Matches (fun a p => a == p.2) r v ↔ ∃ w, w.map Prod.snd = v ∧ Matches (· == ·) r w := by
  constructor
  · intro h
    induction v generalizing r with
    | nil => exact ⟨[], rfl, nullable_iff.1 (nullable_iff.2 h)⟩
    | cons a v ih =>
      obtain ⟨d, hd, hdv⟩ := matches_cons_iff.1 h
      obtain ⟨w, rfl, hw⟩ := ih hdv
      obtain ⟨n, hn⟩ := exists_tag hd
      exact ⟨(n, a) :: w, rfl, matches_cons_iff.2 ⟨d, hn, hw⟩⟩
  · rintro ⟨w, rfl, hw⟩
    refine matches_comap (m := fun a p => a == p.2) (f := Prod.snd) |>.1 (hw.mono ?_)
    intro p q h
    simp_all

/-- The words of `indexed s` are the words of `s`, each letter tagged. -/
theorem matches_indexed {s : Regex α} {v : List α} :
    Matches (· == ·) s v ↔ ∃ w, w.map Prod.snd = v ∧ Matches (· == ·) (indexed s) w := by
  conv => lhs; rw [← map_snd_indexFrom 0 s]
  rw [matches_map]
  exact matches_untagged

theorem accepts_indexed_iff {σ : Type u} {m : α → σ → Bool} {g : Regex σ} {s : Regex α} :
    Accepts (fun p s => m p.2 s) g (indexed s) ↔ Accepts m g s := by
  constructor
  · intro h v hv
    obtain ⟨w, rfl, hw⟩ := matches_indexed.1 hv
    exact matches_comap.1 (h w hw)
  · intro h w hw
    exact matches_comap.2 (h _ (matches_indexed.2 ⟨w, rfl, hw⟩))

/-- A counterexample to the indexed shape, its tags removed, is one to `s`. -/
theorem counterexample_indexed {σ : Type u} [DecidableEq σ] {m : α → σ → Bool} {g : Regex σ}
    {s : Regex α} {w : List (Nat × α)}
    (h : counterexample (fun p s => m p.2 s) g (indexed s) = some w) :
    Matches (· == ·) s (w.map Prod.snd) ∧ ¬Matches m g (w.map Prod.snd) := by
  obtain ⟨hs, hg⟩ := counterexample_spec h
  exact ⟨matches_indexed.2 ⟨w, rfl, hs⟩, fun h' => hg (matches_comap.2 h')⟩

end Shape

end Regular
