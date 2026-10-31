/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Regular.States

@[expose] public section

namespace Regular

universe u v

namespace Regex

variable {σ : Type u} {α : Type v} {m : α → σ → Bool}

mutual
def letters : Regex α → List α
  | .empty | .eps => []
  | .sym a => [a]
  | .cat r s | .alt r s | .interleave r s => letters r ++ letters s
  | .star r | .nonEmpty r => letters r
  | .allOf rs => lettersAll rs

def lettersAll : List (Regex α) → List α
  | [] => []
  | r :: rs => letters r ++ lettersAll rs
end

theorem mem_lettersAll {a : α} {rs : List (Regex α)} :
    a ∈ lettersAll rs ↔ ∃ r ∈ rs, a ∈ letters r := by
  induction rs with
  | nil => simp [lettersAll]
  | cons r rs ih => simp [lettersAll, ih]

theorem mem_letters_of_matches [DecidableEq α] {r : Regex α} {w : List α}
    (h : Matches (· == ·) r w) : ∀ a ∈ w, a ∈ letters r := by
  induction h with
  | eps => simp
  | sym h => simp_all [letters]
  | cat _ _ ih₁ ih₂ =>
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · simp [letters, ih₁ a ha]
    · simp [letters, ih₂ a ha]
  | altLeft _ ih => intro a ha; simp [letters, ih a ha]
  | altRight _ ih => intro a ha; simp [letters, ih a ha]
  | starNil => simp
  | starCons _ _ ih₁ ih₂ =>
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact ih₁ a ha
    · exact ih₂ a ha
  | interleave _ _ hsh ih₁ ih₂ =>
    intro a ha
    have : ∀ {u v w : List α}, Shuffle u v w → a ∈ w → a ∈ u ∨ a ∈ v := by
      intro u v w h
      induction h with
      | nil => simp
      | left _ ih =>
        intro h
        rcases List.mem_cons.1 h with rfl | h
        · simp
        · exact (ih h).imp (List.mem_cons_of_mem _) id
      | right _ ih =>
        intro h
        rcases List.mem_cons.1 h with rfl | h
        · simp
        · exact (ih h).imp id (List.mem_cons_of_mem _)
    rcases this hsh ha with ha | ha
    · simp [letters, ih₁ a ha]
    · simp [letters, ih₂ a ha]
  | nonEmpty _ ih => exact ih
  | allOfNil => simp
  | allOfCons _ _ hp ih₁ ih₂ =>
    intro a ha
    simp only [letters, mem_lettersAll] at ih₂ ⊢
    rcases List.mem_append.1 ha with ha | ha
    · exact ⟨_, hp.mem_iff.1 (by simp), ih₁ a ha⟩
    · obtain ⟨r, hr, ha⟩ := ih₂ a ha
      exact ⟨r, hp.mem_iff.1 (by simp [hr]), ha⟩

/-- `r` with every state reachable from it by derivatives. -/
def reach (r : Regex σ) : List (Regex σ) := r :: states r

theorem deriv_mem_reach {r x d : Regex σ} {a : α} (hx : x ∈ reach r)
    (hd : d ∈ deriv m a x) : d ∈ reach r := by
  rcases List.mem_cons.1 hx with rfl | hx
  · exact List.mem_cons_of_mem _ ((deriv_mem_states x).1 a d hd)
  · exact List.mem_cons_of_mem _ ((deriv_mem_states r).2 x hx a d hd)

theorem length_reach_le (r : Regex σ) : (reach r).length ≤ bound r + 1 := by
  simpa [reach] using length_states_le r

end Regex

open Regex

/-- Every word of the shape `s` is in the language of the grammar `g`. -/
def Accepts {α : Type v} {σ : Type u} [DecidableEq α] (m : α → σ → Bool) (g : Regex σ)
    (s : Regex α) : Prop :=
  ∀ w, Matches (· == ·) s w → Matches m g w

namespace Inclusion

/-- A state of the product of the shape's automaton with the determinized grammar's. -/
structure Node (α : Type v) (σ : Type u) where
  shape : Regex α
  grammar : List (Regex σ)
  /-- The word that led here, most recent letter first. -/
  trace : List α

inductive Outcome (α : Type v) where
  | accept
  | reject (w : List α)
  | outOfFuel

variable {α : Type v} {σ : Type u} [DecidableEq α] [DecidableEq σ]

def setEq {β : Type _} [BEq β] (a b : List β) : Bool := a.all b.contains && b.all a.contains

/-- The shape has a word ending here that the grammar does not. -/
def isBad (n : Node α σ) : Bool := n.shape.nullable && !n.grammar.any nullable

def seen (vs : List (Node α σ)) (c : Node α σ) : Bool :=
  vs.any fun v => v.shape == c.shape && setEq v.grammar c.grammar

def derivSet (m : α → σ → Bool) (a : α) (ys : List (Regex σ)) : List (Regex σ) :=
  (ys.flatMap (deriv m a)).eraseDups

def succs (m : α → σ → Bool) (letters : List α) (n : Node α σ) : List (Node α σ) :=
  letters.flatMap fun a =>
    (deriv (· == ·) a n.shape).eraseDups.map fun x => ⟨x, derivSet m a n.grammar, a :: n.trace⟩

/-- Adds to `new` each of `cs` not already among `new ++ vs`, stopping at the first bad one. -/
def insertAll (vs : List (Node α σ)) :
    List (Node α σ) → List (Node α σ) → Except (List α) (List (Node α σ))
  | new, [] => .ok new
  | new, c :: cs =>
    if isBad c then .error c.trace.reverse
    else if seen (new ++ vs) c then insertAll vs new cs
    else insertAll vs (c :: new) cs

/-- Breadth first search from the frontier `fr`, `old` holding the nodes already expanded. Each
round expands one level, so a word it rejects is a shortest one. -/
def explore (m : α → σ → Bool) (letters : List α) :
    Nat → List (Node α σ) → List (Node α σ) → Outcome α
  | 0, _, _ => .outOfFuel
  | _ + 1, _, [] => .accept
  | n + 1, old, fr@(_ :: _) =>
    match insertAll (fr ++ old) [] (fr.flatMap (succs m letters)) with
    | .error w => .reject w
    | .ok new => explore m letters n (fr ++ old) new

/-- Each round adds a node, and there are at most this many, by `length_le`. It is a shift rather
than a power because `decide` declines to evaluate a power with a large exponent. -/
def fuel (g : Regex σ) (s : Regex α) : Nat := (s.bound + 1) * (1 <<< (g.bound + 1)) + 1

def check (m : α → σ → Bool) (g : Regex σ) (s : Regex α) : Outcome α :=
  let start : Node α σ := ⟨s, [g], []⟩
  if isBad start then .reject [] else explore m s.letters.eraseDups (fuel g s) [] [start]

end Inclusion

open Inclusion

variable {α : Type v} {σ : Type u} [DecidableEq α] [DecidableEq σ]

/-- Whether every word of the shape `s` is in the language of the grammar `g`. -/
def accepts (m : α → σ → Bool) (g : Regex σ) (s : Regex α) : Bool :=
  match check m g s with
  | .accept => true
  | _ => false

/-- A shortest word of the shape `s` that is not in the language of the grammar `g`, if any. -/
def counterexample (m : α → σ → Bool) (g : Regex σ) (s : Regex α) : Option (List α) :=
  match check m g s with
  | .reject w => some w
  | _ => none

namespace Inclusion

variable {m : α → σ → Bool} {g : Regex σ} {s : Regex α}

theorem setEq_self (a : List σ) : setEq a a = true := by simp [setEq]

theorem setEq_comm (a b : List σ) : setEq a b = setEq b a := Bool.and_comm ..

theorem mem_of_setEq {a b : List σ} (h : setEq a b = true) {x : σ} : x ∈ a ↔ x ∈ b := by
  simp only [setEq, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1 x, h.2 x⟩

def Represented (c : Node α σ) (vs : List (Node α σ)) : Prop :=
  ∃ v ∈ vs, v.shape = c.shape ∧ setEq v.grammar c.grammar = true

omit [DecidableEq α] in
theorem Represented.mono {c : Node α σ} {vs vs' : List (Node α σ)} (h : Represented c vs)
    (hs : ∀ v ∈ vs, v ∈ vs') : Represented c vs' :=
  let ⟨v, hv, h⟩ := h
  ⟨v, hs v hv, h⟩

theorem seen_iff {vs : List (Node α σ)} {c : Node α σ} : seen vs c = true ↔ Represented c vs := by
  simp [seen, Represented]

def Distinct (a b : Node α σ) : Prop := ¬(a.shape = b.shape ∧ setEq a.grammar b.grammar = true)

/-- What a node means: it was reached by `trace`, its shape matches what may follow `trace` in
the shape `s`, and its grammar states between them match exactly what may follow it in `g`. -/
structure Valid (m : α → σ → Bool) (g : Regex σ) (s : Regex α) (n : Node α σ) : Prop where
  shape : ∀ v, Matches (· == ·) n.shape v → Matches (· == ·) s (n.trace.reverse ++ v)
  grammar : ∀ v, (∃ y ∈ n.grammar, Matches m y v) ↔ Matches m g (n.trace.reverse ++ v)
  shape_mem : n.shape ∈ reach s
  grammar_mem : ∀ y ∈ n.grammar, y ∈ reach g

omit [DecidableEq α] in
theorem mem_derivSet {a : α} {y : Regex σ} {ys : List (Regex σ)} :
    y ∈ derivSet m a ys ↔ ∃ x ∈ ys, y ∈ deriv m a x := by
  simp [derivSet, List.mem_eraseDups]

theorem mem_succs {ls : List α} {n c : Node α σ} :
    c ∈ succs m ls n ↔ ∃ a ∈ ls, ∃ x ∈ deriv (· == ·) a n.shape,
      c = ⟨x, derivSet m a n.grammar, a :: n.trace⟩ := by
  simp only [succs, List.mem_flatMap, List.mem_map, List.mem_eraseDups]
  exact exists_congr fun a => and_congr_right fun _ =>
    exists_congr fun x => and_congr_right fun _ => eq_comm

theorem Valid.succ {ls : List α} {n c : Node α σ} (hn : Valid m g s n)
    (hc : c ∈ succs m ls n) : Valid m g s c := by
  obtain ⟨a, _, x, hx, rfl⟩ := mem_succs.1 hc
  constructor
  · intro v hv
    simpa using hn.shape (a :: v) (matches_cons_iff.2 ⟨x, hx, hv⟩)
  · intro v
    simp only [mem_derivSet, List.reverse_cons, List.append_assoc, List.singleton_append,
      ← hn.grammar (a :: v)]
    constructor
    · rintro ⟨y, ⟨x, hx, hy⟩, hyv⟩
      exact ⟨x, hx, matches_cons_iff.2 ⟨y, hy, hyv⟩⟩
    · rintro ⟨x, hx, hxv⟩
      obtain ⟨y, hy, hyv⟩ := matches_cons_iff.1 hxv
      exact ⟨y, ⟨x, hx, hy⟩, hyv⟩
  · exact deriv_mem_reach hn.shape_mem hx
  · intro y hy
    obtain ⟨x, hx, hy⟩ := mem_derivSet.1 hy
    exact deriv_mem_reach (hn.grammar_mem x hx) hy

omit [DecidableEq σ] in
theorem Valid.reject {n : Node α σ} (hn : Valid m g s n) (hb : isBad n = true) :
    Matches (· == ·) s n.trace.reverse ∧ ¬Matches m g n.trace.reverse := by
  simp only [isBad, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hb
  refine ⟨by simpa using hn.shape [] (nullable_iff.1 hb.1), fun h => ?_⟩
  obtain ⟨y, hy, hyn⟩ := (hn.grammar []).2 (by simpa using h)
  exact absurd (nullable_iff.2 hyn) (by simpa using hb.2 y hy)

theorem insertAll_error {vs new cs : List (Node α σ)} {w : List α}
    (h : insertAll vs new cs = .error w) : ∃ c ∈ cs, isBad c = true ∧ w = c.trace.reverse := by
  induction cs generalizing new with
  | nil => simp [insertAll] at h
  | cons c cs ih =>
    simp only [insertAll] at h
    split at h
    · cases h
      exact ⟨c, by simp, by assumption, rfl⟩
    · split at h <;>
      · obtain ⟨c', hc', h⟩ := ih h
        exact ⟨c', by simp [hc'], h⟩

theorem insertAll_ok {vs new cs new' : List (Node α σ)} (h : insertAll vs new cs = .ok new') :
    ∃ added, new' = added ++ new ∧ (∀ x ∈ added, x ∈ cs) ∧
      (∀ c ∈ cs, isBad c = false ∧ Represented c (new' ++ vs)) ∧
      ((new ++ vs).Pairwise Distinct → (new' ++ vs).Pairwise Distinct) := by
  induction cs generalizing new with
  | nil =>
    simp only [insertAll, Except.ok.injEq] at h
    exact ⟨[], by simp [h], by simp, by simp, fun h' => h ▸ h'⟩
  | cons c cs ih =>
    simp only [insertAll] at h
    split at h
    · cases h
    rename_i hbad
    split at h
    · obtain ⟨added, rfl, hadded, hcs, hd⟩ := ih h
      refine ⟨added, rfl, fun x hx => by simp [hadded x hx], ?_, hd⟩
      intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact ⟨by simpa using hbad,
          (seen_iff.1 ‹_›).mono fun v hv => by simp_all⟩
      · exact hcs c' hc'
    · rename_i hseen
      obtain ⟨added, rfl, hadded, hcs, hd⟩ := ih h
      refine ⟨added ++ [c], by simp, fun x hx => ?_, ?_, fun h' => hd ?_⟩
      · rcases List.mem_append.1 hx with hx | hx
        · simp [hadded x hx]
        · simp_all
      · intro c' hc'
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact ⟨by simpa using hbad, ⟨c', by simp, rfl, setEq_self _⟩⟩
        · exact hcs c' hc'
      · refine List.pairwise_cons.2 ⟨fun v hv ⟨hs, hg⟩ => hseen ?_, h'⟩
        exact seen_iff.2 ⟨v, hv, hs.symm, by rw [setEq_comm]; exact hg⟩

/-- Every node so far is valid and none is bad; no two are the same state; every node already
expanded has each of its successors represented; and the search started from `s` and `g`. -/
structure Inv (m : α → σ → Bool) (g : Regex σ) (s : Regex α) (ls : List α)
    (old fr : List (Node α σ)) : Prop where
  valid : ∀ n ∈ fr ++ old, Valid m g s n ∧ isBad n = false
  distinct : (fr ++ old).Pairwise Distinct
  closed : ∀ n ∈ old, ∀ c ∈ succs m ls n, Represented c (fr ++ old)
  start : ⟨s, [g], []⟩ ∈ fr ++ old

theorem Inv.step {ls : List α} {old fr new : List (Node α σ)} (hI : Inv m g s ls old fr)
    (h : insertAll (fr ++ old) [] (fr.flatMap (succs m ls)) = .ok new) :
    Inv m g s ls (fr ++ old) new := by
  obtain ⟨added, rfl, hadded, hcs, hd⟩ := insertAll_ok h
  simp only [List.append_nil] at hcs hd ⊢
  refine ⟨fun n hn => ?_, hd hI.distinct, fun n hn c hc => ?_, by simp [hI.start]⟩
  · rcases List.mem_append.1 hn with hn | hn
    · have hc := hadded n hn
      obtain ⟨f, hf, hc'⟩ := List.mem_flatMap.1 hc
      exact ⟨(hI.valid f (by simp [hf])).1.succ hc', (hcs n hc).1⟩
    · exact hI.valid n hn
  · rcases List.mem_append.1 hn with hn | hn
    · exact (hcs c (List.mem_flatMap.2 ⟨n, hn, hc⟩)).2
    · exact (hI.closed n hn c hc).mono fun v hv => by simp_all

private def boolVecs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolVecs n).map (false :: ·) ++ (boolVecs n).map (true :: ·)

private theorem length_boolVecs (n : Nat) : (boolVecs n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [boolVecs, ih, Nat.pow_succ, Nat.mul_two]

private theorem mem_boolVecs {v : List Bool} : v ∈ boolVecs v.length := by
  induction v with
  | nil => simp [boolVecs]
  | cons b v ih => cases b <;> simp [boolVecs, ih]

private theorem length_le_of_nodup {β : Type _} [DecidableEq β] {l u : List β} (hl : l.Nodup)
    (hu : ∀ x ∈ l, x ∈ u) : l.length ≤ u.length := by
  induction l generalizing u with
  | nil => simp
  | cons a l ih =>
    have ha := hu a (by simp)
    have hl' := List.nodup_cons.1 hl
    have := ih hl'.2 fun x hx => (List.mem_erase_of_ne (fun h => by subst h; exact hl'.1 hx)).2
      (hu x (by simp [hx]))
    rw [List.length_erase_of_mem ha] at this
    have := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- The pigeonhole bound: distinct valid nodes are at most the shape states times the sets of
grammar states. -/
theorem length_le {vs : List (Node α σ)} (hv : ∀ n ∈ vs, Valid m g s n)
    (hd : vs.Pairwise Distinct) : vs.length ≤ (reach s).length * 2 ^ (reach g).length := by
  let key (n : Node α σ) : Regex α × List Bool := (n.shape, (reach g).map n.grammar.contains)
  have hnodup : (vs.map key).Nodup := by
    refine List.pairwise_map.2 (hd.imp_of_mem fun ha hb hab heq => hab ?_)
    simp only [key, Prod.mk.injEq, List.map_inj_left] at heq
    refine ⟨heq.1, ?_⟩
    simp only [setEq, Bool.and_eq_true, List.all_eq_true]
    exact ⟨fun y hy => by rw [← heq.2 y ((hv _ ha).grammar_mem y hy)]; simpa using hy,
      fun y hy => by rw [heq.2 y ((hv _ hb).grammar_mem y hy)]; simpa using hy⟩
  have := length_le_of_nodup hnodup (u := (reach s).flatMap fun x =>
    (boolVecs (reach g).length).map (x, ·)) (by
      simp only [List.mem_map, List.mem_flatMap]
      rintro _ ⟨n, hn, rfl⟩
      exact ⟨n.shape, (hv n hn).shape_mem, _,
        by simpa using mem_boolVecs (v := (reach g).map n.grammar.contains), rfl⟩)
  rwa [List.length_map, length_flatMap_map _ _ (fun x y => (x, y)), length_boolVecs] at this

theorem explore_reject {ls : List α} {fuel : Nat} {old fr : List (Node α σ)} {w : List α}
    (hI : Inv m g s ls old fr) (h : explore m ls fuel old fr = .reject w) :
    Matches (· == ·) s w ∧ ¬Matches m g w := by
  induction fuel generalizing old fr with
  | zero => simp [explore] at h
  | succ k ih =>
    cases fr with
    | nil => simp [explore] at h
    | cons f fs =>
      simp only [explore] at h
      split at h
      · rename_i w' hw
        cases h
        obtain ⟨c, hc, hb, rfl⟩ := insertAll_error hw
        obtain ⟨n, hn, hc⟩ := List.mem_flatMap.1 hc
        have hn' : n ∈ f :: fs ++ old := List.mem_append_left _ hn
        exact ((hI.valid n hn').1.succ hc).reject hb
      · exact ih (hI.step ‹_›) h

theorem accepts_of_closed {ls : List α} {vs : List (Node α σ)}
    (hls : ∀ a ∈ s.letters, a ∈ ls) (hv : ∀ n ∈ vs, Valid m g s n ∧ isBad n = false)
    (hc : ∀ n ∈ vs, ∀ c ∈ succs m ls n, Represented c vs) :
    ∀ w, ∀ n ∈ vs, Matches (· == ·) n.shape w → ∃ y ∈ n.grammar, Matches m y w := by
  intro w
  induction w with
  | nil =>
    intro n hn h
    have hb := (hv n hn).2
    simp only [isBad, nullable_iff.2 h, Bool.true_and, Bool.not_eq_false', List.any_eq_true] at hb
    obtain ⟨y, hy, hyn⟩ := hb
    exact ⟨y, hy, nullable_iff.1 hyn⟩
  | cons a w ih =>
    intro n hn h
    obtain ⟨x, hx, hxw⟩ := matches_cons_iff.1 h
    have ha : a ∈ ls := hls a <| mem_letters_of_matches ((hv n hn).1.shape (a :: w) h) a (by simp)
    obtain ⟨v, hv', hshape, hgrammar⟩ := hc n hn _ (mem_succs.2 ⟨a, ha, x, hx, rfl⟩)
    obtain ⟨y', hy', hy'w⟩ := ih v hv' (hshape ▸ hxw)
    obtain ⟨y, hy, hy'⟩ := mem_derivSet.1 ((mem_of_setEq hgrammar).1 hy')
    exact ⟨y, hy, matches_cons_iff.2 ⟨y', hy', hy'w⟩⟩

theorem explore_accept {fuel : Nat} {old fr : List (Node α σ)}
    (hI : Inv m g s s.letters.eraseDups old fr)
    (h : explore m s.letters.eraseDups fuel old fr = .accept) : Accepts m g s := by
  induction fuel generalizing old fr with
  | zero => simp [explore] at h
  | succ k ih =>
    cases fr with
    | nil =>
      intro w hw
      have := accepts_of_closed (fun a ha => List.mem_eraseDups.2 ha)
        (by simpa using hI.valid) (by simpa using hI.closed) w _ (by simpa using hI.start) hw
      simpa using this
    | cons f fs =>
      simp only [explore] at h
      split at h
      · cases h
      · exact ih (hI.step ‹_›) h

theorem explore_ne_outOfFuel {ls : List α} {fuel : Nat} {old fr : List (Node α σ)}
    (hI : Inv m g s ls old fr)
    (hf : (reach s).length * 2 ^ (reach g).length < fuel + old.length) :
    explore m ls fuel old fr ≠ .outOfFuel := by
  have hlen := length_le (fun n hn => (hI.valid n hn).1) hI.distinct
  induction fuel generalizing old fr with
  | zero => simp at hlen; omega
  | succ k ih =>
    cases fr with
    | nil => simp [explore]
    | cons f fs =>
      simp only [explore]
      split
      · simp
      · rename_i new hnew
        have hI' := hI.step hnew
        exact ih hI' (by simp at hlen ⊢; omega)
          (length_le (fun n hn => (hI'.valid n hn).1) hI'.distinct)

theorem start_inv (hb : isBad (⟨s, [g], []⟩ : Node α σ) = false) :
    Inv m g s s.letters.eraseDups [] [⟨s, [g], []⟩] where
  valid n hn := by
    simp only [List.append_nil, List.mem_singleton] at hn
    subst hn
    exact ⟨⟨fun _ h => h, by simp, List.mem_cons_self .., by simp [reach]⟩, hb⟩
  distinct := by simp
  closed := by simp
  start := by simp

theorem check_ne_outOfFuel : check m g s ≠ .outOfFuel := by
  unfold check
  dsimp only
  split
  · simp
  · refine explore_ne_outOfFuel (start_inv (by rename_i hb; simpa using hb)) ?_
    have hs := length_reach_le s
    have hg := Nat.pow_le_pow_right (by decide : 0 < 2) (length_reach_le g)
    simp only [fuel, Nat.one_shiftLeft, List.length_nil, Nat.add_zero]
    exact Nat.lt_succ_of_le (Nat.mul_le_mul hs hg)

theorem check_reject {w : List α} (h : check m g s = .reject w) :
    Matches (· == ·) s w ∧ ¬Matches m g w := by
  unfold check at h
  dsimp only at h
  split at h
  · cases h
    have := Valid.reject (m := m) (g := g) (s := s) (n := ⟨s, [g], []⟩)
      ⟨fun _ h => h, by simp, List.mem_cons_self .., by simp [reach]⟩ ‹_›
    simpa using this
  · exact explore_reject (start_inv (by rename_i hb; simpa using hb)) h

theorem check_accept (h : check m g s = .accept) : Accepts m g s := by
  unfold check at h
  dsimp only at h
  split at h
  · cases h
  · exact explore_accept (start_inv (by rename_i hb; simpa using hb)) h

end Inclusion

variable {m : α → σ → Bool} {g : Regex σ} {s : Regex α}

theorem accepts_iff : accepts m g s = true ↔ Accepts m g s := by
  unfold accepts
  split
  · exact ⟨fun _ => check_accept ‹_›, fun _ => rfl⟩
  · refine ⟨nofun, fun h => ?_⟩
    cases hc : check m g s with
    | accept => contradiction
    | reject w =>
      obtain ⟨hs, hg⟩ := check_reject hc
      exact absurd (h w hs) hg
    | outOfFuel => exact absurd hc check_ne_outOfFuel

theorem counterexample_eq_none_iff : counterexample m g s = none ↔ Accepts m g s := by
  rw [← accepts_iff]
  unfold counterexample accepts
  cases hc : check m g s with
  | accept => simp
  | reject => simp
  | outOfFuel => exact absurd hc check_ne_outOfFuel

theorem counterexample_spec {w : List α} (h : counterexample m g s = some w) :
    Matches (· == ·) s w ∧ ¬Matches m g w := by
  unfold counterexample at h
  split at h
  · cases h
    exact check_reject ‹_›
  · cases h

instance : Decidable (Accepts m g s) := decidable_of_iff _ accepts_iff

end Regular
