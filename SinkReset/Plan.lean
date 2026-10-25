/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import SinkReset.Basic

/-!
# Sharp reset thresholds for bounded-response synchronization games with a sink: the plan

The development declarations of the formalization plan (`docs/PROOF.md`), followed by the
statements of record restated under `_dev` names; `Solution.lean` bridges each statement of
record to its `_dev` copy.
-/

@[expose] public section

namespace SinkReset

namespace Plan

-- New definition bodies are holes; comments specify their required equations.
-- PROOF 54-75.
-- Equation: active S = S.erase 0.
def active {n : ℕ} [NeZero n] (S : Finset (Fin n)) : Finset (Fin n) := S.erase 0
-- Equation: ResetOn A S w = (A.IsWord w ∧ ∀ q ∈ S, act w q = 0).
def ResetOn {n : ℕ} [NeZero n] (A : Automaton n)
    (S : Finset (Fin n)) (w : List (Letter n)) : Prop :=
  A.IsWord w ∧ ∀ q ∈ S, act w q = 0
-- Equation: Within A S b = (∃ w, ResetOn A S w ∧ w.length ≤ b).
def Within {n : ℕ} [NeZero n] (A : Automaton n)
    (S : Finset (Fin n)) (b : ℕ) : Prop :=
  ∃ w, ResetOn A S w ∧ w.length ≤ b
-- Equation: SC A = (∀ p q, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q).
def SC {n : ℕ} [NeZero n] (A : Automaton n) : Prop :=
  ∀ p q : Fin n, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q
-- Equation: Z A = Finset.univ.filter (fun q => q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0).
noncomputable def Z {n : ℕ} [NeZero n] (A : Automaton n) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun q => q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0)
-- Equation: Y A = active Finset.univ \ Z A.
noncomputable def Y {n : ℕ} [NeZero n] (A : Automaton n) : Finset (Fin n) :=
  active Finset.univ \ Z A
-- Equation: Distances A d = ∀ q,
--   (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
--   ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length.
def Distances {n : ℕ} [NeZero n] (A : Automaton n) (d : Fin n → ℕ) : Prop :=
  ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
    ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length

section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)

-- PROOF 54-69.
theorem act_append (u v : List (Letter n)) (q : Fin n) :
    act (u ++ v) q = act v (act u q) := by
  simp [act, List.foldl_append]
theorem word_append (u v : List (Letter n)) :
    A.IsWord (u ++ v) ↔ A.IsWord u ∧ A.IsWord v := by
  simp only [Automaton.IsWord, List.mem_append, or_imp, forall_and]
theorem act_zero (w : List (Letter n)) (hw : A.IsWord w) :
    act w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha : a ∈ A.letters := hw a List.mem_cons_self
    have hw' : A.IsWord w := fun b hb => hw b (List.mem_cons_of_mem a hb)
    change act w (a 0) = 0
    rw [A.sink_fixed a ha]
    exact ih hw'
/-- `image_active_le` with `active` written out. -/
private theorem image_active_le' {n : ℕ} [NeZero n] (S : Finset (Fin n)) (g : Fin n → Fin n) (hg : g 0 = 0) :
    ((S.image g).erase 0).card ≤ (S.erase 0).card := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S.erase 0) (f := g))
  intro x hx
  obtain ⟨hx0, hx⟩ := Finset.mem_erase.1 hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
  refine Finset.mem_image.2 ⟨p, Finset.mem_erase.2 ⟨fun h => hx0 (h ▸ hg), hp⟩, rfl⟩

/-- `kill_decreases` with `active` written out. -/
private theorem kill_decreases' {n : ℕ} [NeZero n] (S : Finset (Fin n)) (q : Fin n) (hq : q ∈ S.erase 0)
    (g : Fin n → Fin n) (hg : g 0 = 0) (hkill : g q = 0) :
    ((S.image g).erase 0).card + 1 ≤ (S.erase 0).card := by
  classical
  have hsub : (S.image g).erase 0 ⊆ ((S.erase 0).erase q).image g := by
    intro x hx
    obtain ⟨hx0, hx⟩ := Finset.mem_erase.1 hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    refine Finset.mem_image.2 ⟨p, Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hp⟩⟩, rfl⟩
    · rintro rfl; exact hx0 hkill
    · rintro rfl; exact hx0 hg
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_erase_of_mem hq] at h1
  have h2 : 0 < (S.erase 0).card := Finset.card_pos.2 ⟨q, hq⟩
  omega

theorem image_active_le (S : Finset (Fin n)) (w : List (Letter n))
    (hw : A.IsWord w) :
    (active (S.image (act w))).card ≤ (active S).card :=
  image_active_le' S (act w) (act_zero A w hw)
theorem kill_decreases (S : Finset (Fin n)) (q : Fin n) (hq : q ∈ active S)
    (w : List (Letter n)) (hw : A.IsWord w) (hkill : act w q = 0) :
    (active (S.image (act w))).card + 1 ≤ (active S).card :=
  kill_decreases' S q hq (act w) (act_zero A w hw) hkill
theorem within_compose (S : Finset (Fin n)) (u : List (Letter n))
    (hu : A.IsWord u) (b : ℕ) (h : Within A (S.image (act u)) b) :
    Within A S (u.length + b) := by
  obtain ⟨v, ⟨hv, hv0⟩, hlen⟩ := h
  refine ⟨u ++ v, ⟨(word_append A u v).2 ⟨hu, hv⟩, fun q hq => ?_⟩, ?_⟩
  · rw [act_append]; exact hv0 _ (Finset.mem_image_of_mem _ hq)
  · rw [List.length_append]; omega
theorem within_univ (b : ℕ) :
    Within A Finset.univ b ↔ ∃ w, A.IsReset w ∧ w.length ≤ b := by
  constructor
  · rintro ⟨w, ⟨hw, hw0⟩, hlen⟩
    exact ⟨w, ⟨hw, fun q => hw0 q (Finset.mem_univ q)⟩, hlen⟩
  · rintro ⟨w, ⟨hw, hw0⟩, hlen⟩
    exact ⟨w, ⟨hw, fun q _ => hw0 q⟩, hlen⟩

-- PROOF 86-96; monotonicity also supplies the Bob-first equivalence.
theorem wins_mono {k : ℕ} {S T : Finset (Fin n)}
    (h : A.AliceWins k T) (hST : S ⊆ T) : A.AliceWins k S := by
  induction h generalizing S with
  | reset T hT => exact .reset S fun q hq => hT q (hST hq)
  | step T a ha _ ih =>
    exact .step S a ha fun u hu hlen => ih u hu hlen (Finset.image_subset_image hST)
theorem wins_word {k : ℕ} (hk : 1 ≤ k) {S : Finset (Fin n)}
    (h : A.AliceWins k S) : ∃ w, ResetOn A S w := by
  induction h with
  | reset S hS => exact ⟨[], fun a ha => by simp at ha, fun q hq => hS q hq⟩
  | step S a ha _ ih =>
    obtain ⟨w, hw, hw0⟩ := ih [] (fun b hb => by simp at hb) (by simp only [List.length_nil]; omega)
    refine ⟨a :: w, fun b hb => ?_, fun q hq => ?_⟩
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact hw b hb
    · exact hw0 _ (Finset.mem_image_of_mem _ hq)

private theorem act_cons (a : Letter n) (u : List (Letter n)) (q : Fin n) :
    act (a :: u) q = act u (a q) := rfl

private theorem act_nil (q : Fin n) : act ([] : List (Letter n)) q = q := rfl

private theorem word_cons {a : Letter n} {u : List (Letter n)} :
    A.IsWord (a :: u) ↔ a ∈ A.letters ∧ A.IsWord u := by
  simp [Automaton.IsWord]

private theorem word_nil : A.IsWord [] := by simp [Automaton.IsWord]

/-- `wins_word` with the plan definition `ResetOn` written out. -/
private theorem wins_word' {k : ℕ} (hk : 1 ≤ k) {S : Finset (Fin n)}
    (h : A.AliceWins k S) : ∃ w, A.IsWord w ∧ ∀ q ∈ S, act w q = 0 := by
  induction h with
  | reset S hS => exact ⟨[], word_nil A, fun q hq => hS q hq⟩
  | step S a ha _ ih =>
    obtain ⟨w, hw, hw0⟩ := ih [] (word_nil A) (by simp only [List.length_nil]; omega)
    refine ⟨a :: w, (word_cons A).2 ⟨ha, hw⟩, fun q hq => ?_⟩
    exact hw0 _ (Finset.mem_image_of_mem _ hq)

theorem one_game_iff : A.IsAk 1 ↔ ∃ w, A.IsReset w := by
  constructor
  · intro h
    obtain ⟨w, hw, hw0⟩ := wins_word' A le_rfl h
    exact ⟨w, hw, fun q => hw0 q (Finset.mem_univ q)⟩
  · rintro ⟨w, hw, hw0⟩
    suffices ∀ (w : List (Letter n)), A.IsWord w → ∀ S : Finset (Fin n),
        (∀ q ∈ S, act w q = 0) → A.AliceWins 1 S from this w hw _ fun q _ => hw0 q
    intro w
    induction w with
    | nil => intro _ S hS; exact .reset S hS
    | cons a w ih =>
      intro hw S hS
      rw [word_cons] at hw
      refine .step S a hw.1 fun u hu hlen => ?_
      have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hu0
      refine ih hw.2 _ fun q hq => ?_
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      exact hS p hp
theorem bob_first_iff {k : ℕ} (hk : 1 ≤ k) :
    A.IsAk k ↔ ∀ u, A.IsWord u → u.length < k →
      A.AliceWins k (Finset.univ.image (act u)) := by
  constructor
  · intro h u _ _
    exact wins_mono A h (Finset.subset_univ _)
  · intro h
    have := h [] (word_nil A) (by simp only [List.length_nil]; omega)
    have he : (Finset.univ.image (act ([] : List (Letter n)))) = Finset.univ := by
      ext q; simp [act_nil]
    rw [he] at this
    exact this

-- PROOF 154-159, 177-180, 319-324: induction on AliceWins.
/-- `trap`, for an arbitrary position meeting the trap. -/
private theorem trap_aux {k : ℕ} (T : Finset (Fin n)) (hzero : 0 ∉ T)
    (hreply : ∀ t ∈ T, ∀ a ∈ A.letters, ∃ u,
      A.IsWord u ∧ u.length < k ∧ act (a :: u) t ∈ T)
    {S : Finset (Fin n)} (h : A.AliceWins k S) : ∀ t ∈ S, t ∉ T := by
  induction h with
  | reset S hS =>
    intro t ht htT
    exact hzero (hS t ht ▸ htT)
  | step S a ha _ ih =>
    intro t ht htT
    obtain ⟨u, hu, hlen, hT⟩ := hreply t htT a ha
    exact ih u hu hlen _ (Finset.mem_image_of_mem _ ht) hT

theorem trap {k : ℕ} (T : Finset (Fin n)) (hne : T.Nonempty) (hzero : 0 ∉ T)
    (hreply : ∀ t ∈ T, ∀ a ∈ A.letters, ∃ u,
      A.IsWord u ∧ u.length < k ∧ act (a :: u) t ∈ T) :
    ¬ A.IsAk k := by
  intro h
  obtain ⟨t, ht⟩ := hne
  exact trap_aux A T hzero hreply h t (Finset.mem_univ t) ht

/-- `wins_of_rank`, with `active` written out. -/
private theorem wins_of_rank' {n : ℕ} [NeZero n] (A : Automaton n) {k : ℕ} (rank : Finset (Fin n) → ℕ)
    (hstep : ∀ S : Finset (Fin n), (S.erase 0).Nonempty → ∃ a ∈ A.letters,
      ∀ u, A.IsWord u → u.length < k → rank (S.image (act (a :: u))) < rank S) :
    ∀ S, A.AliceWins k S := by
  intro S
  induction hr : rank S using Nat.strong_induction_on generalizing S with
  | _ r ih =>
    rcases (S.erase 0).eq_empty_or_nonempty with h | h
    · refine .reset S fun q hq => ?_
      by_contra hq0
      have : q ∈ S.erase 0 := Finset.mem_erase.2 ⟨hq0, hq⟩
      rw [h] at this; simp at this
    · obtain ⟨a, ha, hlt⟩ := hstep S h
      exact .step S a ha fun u hu hlen => ih _ (hr ▸ hlt u hu hlen) _ rfl

-- PROOF 295-317: well-founded formulation of the finite progress argument.
theorem wins_of_rank {k : ℕ} (rank : Finset (Fin n) → ℕ)
    (hstep : ∀ S, (active S).Nonempty → ∃ a ∈ A.letters,
      ∀ u, A.IsWord u → u.length < k →
        rank (S.image (act (a :: u))) < rank S) :
    ∀ S, A.AliceWins k S :=
  wins_of_rank' A rank hstep

private theorem word_take {n : ℕ} [NeZero n] (A : Automaton n) {w : List (Letter n)} (hw : A.IsWord w) (i : ℕ) : A.IsWord (w.take i) :=
  fun a ha => hw a (List.mem_of_mem_take ha)

private theorem word_drop {n : ℕ} [NeZero n] (A : Automaton n) {w : List (Letter n)} (hw : A.IsWord w) (i : ℕ) : A.IsWord (w.drop i) :=
  fun a ha => hw a (List.mem_of_mem_drop ha)

private theorem word_single {n : ℕ} [NeZero n] (A : Automaton n) {a : Letter n} (ha : a ∈ A.letters) : A.IsWord [a] := by
  intro b hb
  simp only [List.mem_singleton] at hb
  exact hb ▸ ha

private theorem active_card_le {n : ℕ} [NeZero n] (S : Finset (Fin n)) : (S.erase 0).card ≤ n - 1 := by
  calc (S.erase 0).card ≤ (Finset.univ.erase (0 : Fin n)).card :=
        Finset.card_le_card (Finset.erase_subset_erase _ (Finset.subset_univ _))
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp

private theorem active_univ_card {n : ℕ} [NeZero n] : ((Finset.univ : Finset (Fin n)).erase 0).card = n - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp

/-- Distances (the plan's `Distances`, written out) exist when every state can be sent to `0`. -/
private theorem dist_exists {n : ℕ} [NeZero n] (A : Automaton n) (h : ∀ q, ∃ w, A.IsWord w ∧ act w q = 0) :
    ∃ d : Fin n → ℕ, ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length := by
  classical
  have hP : ∀ q, ∃ ℓ, ∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = ℓ := fun q => by
    obtain ⟨w, hw, hw0⟩ := h q
    exact ⟨_, w, hw, hw0, rfl⟩
  refine ⟨fun q => Nat.find (hP q), fun q => ⟨Nat.find_spec (hP q), fun w hw hw0 => ?_⟩⟩
  exact Nat.find_min' (hP q) ⟨w, hw, hw0, rfl⟩

private theorem dist_zero {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) : d 0 = 0 := by
  have := (hd 0).2 [] (word_nil A) rfl
  simpa using this

private theorem dist_eq_zero {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) {q : Fin n} (h : d q = 0) : q = 0 := by
  obtain ⟨w, _, hw0, hlen⟩ := (hd q).1
  rw [h] at hlen
  rw [List.eq_nil_of_length_eq_zero hlen] at hw0
  exact hw0

private theorem dist_le_succ {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) (q : Fin n) {a : Letter n} (ha : a ∈ A.letters) :
    d q ≤ d (a q) + 1 := by
  obtain ⟨w, hw, hw0, hlen⟩ := (hd (a q)).1
  have := (hd q).2 (a :: w) ((word_cons A).2 ⟨ha, hw⟩) hw0
  simpa [hlen] using this

private theorem dist_step {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) {q : Fin n} {j : ℕ} (h : d q = j + 1) :
    ∃ a ∈ A.letters, d (a q) = j := by
  obtain ⟨w, hw, hw0, hlen⟩ := (hd q).1
  cases w with
  | nil => simp at hlen; omega
  | cons a w =>
    rw [word_cons] at hw
    refine ⟨a, hw.1, ?_⟩
    have h1 := (hd (a q)).2 w hw.2 hw0
    have h2 := dist_le_succ hd q hw.1
    simp only [List.length_cons] at hlen
    omega

private theorem dist_chain {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) (j : ℕ) :
    ∀ t (q : Fin n), d q = j + t → ∃ p, d p = j := by
  intro t
  induction t with
  | zero => intro q hq; exact ⟨q, hq⟩
  | succ t ih =>
    intro q hq
    obtain ⟨a, _, ha⟩ := dist_step hd (j := j + t) (by rw [hq]; ring)
    exact ih _ ha

private theorem card_le_of_values {n : ℕ} [NeZero n] (d : Fin n → ℕ) (X : Finset (Fin n)) (lo hi : ℕ)
    (hex : ∀ j, lo ≤ j → j ≤ hi → ∃ p, d p = j)
    (hX : ∀ p, lo ≤ d p → d p ≤ hi → p ∈ X) : hi + 1 - lo ≤ X.card := by
  classical
  let c : ℕ → Fin n := fun j => if h : lo ≤ j ∧ j ≤ hi then Classical.choose (hex j h.1 h.2) else 0
  have hc : ∀ j ∈ Finset.Icc lo hi, d (c j) = j := by
    intro j hj
    have h := Finset.mem_Icc.1 hj
    simp only [c, dif_pos h]
    exact Classical.choose_spec (hex j h.1 h.2)
  rw [← Nat.card_Icc]
  refine Finset.card_le_card_of_injOn c ?_ ?_
  · intro j hj
    have h := Finset.mem_Icc.1 hj
    exact hX _ (by rw [hc j hj]; exact h.1) (by rw [hc j hj]; exact h.2)
  · intro i hi j hj hij
    have := congrArg d hij
    rwa [hc i hi, hc j hj] at this

/-- `short_kill`, from distances, with `active` written out. -/
private theorem short_kill' {n : ℕ} [NeZero n] (A : Automaton n) {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) (S : Finset (Fin n))
    (hne : (S.erase 0).Nonempty) :
    ∃ q ∈ S.erase 0, ∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length ≤ n - (S.erase 0).card := by
  classical
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image (S.erase 0) d hne
  obtain ⟨w, hw, hw0, hlen⟩ := (hd q).1
  refine ⟨q, hq, w, hw, hw0, ?_⟩
  have hq0 : d q ≠ 0 := fun h => (Finset.mem_erase.1 hq).1 (dist_eq_zero hd h)
  have hcount := card_le_of_values d (insert 0 (S.erase 0))ᶜ 1 (d q - 1)
    (fun j _ hj => dist_chain hd j (d q - j) q (by omega))
    (fun p h1 h2 => by
      rw [Finset.mem_compl, Finset.mem_insert, not_or]
      refine ⟨fun hp => ?_, fun hp => ?_⟩
      · rw [hp, dist_zero hd] at h1; omega
      · have := hmin p hp; omega)
  rw [Finset.card_compl, Finset.card_insert_of_notMem (by simp), Fintype.card_fin] at hcount
  have := active_card_le (n := n) S
  omega

/-- `classical_bound`, from distances, with `Within` and `active` written out. -/
private theorem classical_bound' {n : ℕ} [NeZero n] (A : Automaton n) {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) (S : Finset (Fin n)) :
    ∃ w, A.IsWord w ∧ (∀ q ∈ S, act w q = 0) ∧
      w.length ≤ ∑ j ∈ Finset.range (S.erase 0).card, (n - (j + 1)) := by
  classical
  induction hm : (S.erase 0).card using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    rcases (S.erase 0).eq_empty_or_nonempty with h | h
    · refine ⟨[], word_nil A, fun q hq => ?_, by simp⟩
      by_contra hq0
      have : q ∈ S.erase 0 := Finset.mem_erase.2 ⟨hq0, hq⟩
      rw [h] at this; simp at this
    · obtain ⟨q, hq, w, hw, hw0, hlen⟩ := short_kill' A hd S h
      have hdec := kill_decreases' S q hq (act w) (act_zero A w hw) hw0
      obtain ⟨w', hw', hw'0, hlen'⟩ := ih _ (by omega) (S.image (act w)) rfl
      refine ⟨w ++ w', (word_append A w w').2 ⟨hw, hw'⟩, fun p hp => ?_, ?_⟩
      · rw [act_append]; exact hw'0 _ (Finset.mem_image_of_mem _ hp)
      · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [List.length_append, hm', Finset.sum_range_succ]
        have : ∑ j ∈ Finset.range ((S.image (act w)).erase 0).card, (n - (j + 1)) ≤
            ∑ j ∈ Finset.range m', (n - (j + 1)) :=
          Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
        omega

private theorem mem_Y_of_dist {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length)
    (Y : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (p : Fin n) : p ∈ Y ↔ 2 ≤ d p := by
  rw [hY]
  constructor
  · rintro ⟨hp0, hpa⟩
    by_contra hlt
    rcases Nat.lt_succ_iff.1 (Nat.not_le.1 hlt) |>.lt_or_eq with h | h
    · exact hp0 (dist_eq_zero hd (by omega))
    · obtain ⟨a, ha, had⟩ := dist_step hd (j := 0) h
      exact hpa a ha (dist_eq_zero hd had)
  · intro h2
    refine ⟨fun hp0 => ?_, fun a ha hap => ?_⟩
    · rw [hp0, dist_zero hd] at h2; omega
    · have := (hd p).2 [a] (word_single A ha) hap
      simp at this; omega

private theorem dist_le_Y {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length)
    (Y : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (q : Fin n) : d q ≤ Y.card + 1 := by
  have := card_le_of_values d Y 2 (d q) (fun j _ hj => dist_chain hd j (d q - j) q (by omega))
    (fun p h1 _ => (mem_Y_of_dist hd Y hY p).2 h1)
  omega

private theorem dist_two_of_Y {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length)
    (Y : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (hne : Y.Nonempty) : ∃ y ∈ Y, d y = 2 := by
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image Y d hne
  have h2 := (mem_Y_of_dist hd Y hY y).1 hy
  refine ⟨y, hy, ?_⟩
  by_contra hne2
  obtain ⟨a, _, had⟩ := dist_step hd (q := y) (j := d y - 1) (by omega)
  have := hmin (a y) ((mem_Y_of_dist hd Y hY (a y)).2 (by omega))
  omega

private theorem mem_Z_iff {n : ℕ} [NeZero n] (A : Automaton n) (q : Fin n) :
    q ∈ Z A ↔ q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0 := by
  unfold Z
  simp

private theorem mem_Y_iff {n : ℕ} [NeZero n] (A : Automaton n) (q : Fin n) :
    q ∈ Y A ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0 := by
  show q ∈ (Finset.univ.erase 0) \ Z A ↔ _
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 h
    have h0 := (Finset.mem_erase.1 h1).1
    exact ⟨h0, fun a ha haq => h2 ((mem_Z_iff A q).2 ⟨h0, a, ha, haq⟩)⟩
  · rintro ⟨h0, h⟩
    refine Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨h0, Finset.mem_univ _⟩, fun hz => ?_⟩
    obtain ⟨_, a, ha, haq⟩ := (mem_Z_iff A q).1 hz
    exact h a ha haq

-- PROOF 88, 98-107, 161-169, 182-185.
theorem distances_exist (h : ∃ w, A.IsReset w) :
    ∃ d, Distances A d := by
  obtain ⟨w, hw, hw0⟩ := h
  exact dist_exists A fun q => ⟨w, hw, hw0 q⟩
theorem reachable_reset
    (h : ∀ q, ∃ w, A.IsWord w ∧ act w q = 0) (S : Finset (Fin n)) :
    ∃ w, ResetOn A S w := by
  obtain ⟨d, hd⟩ := dist_exists A h
  obtain ⟨w, hw, hw0, _⟩ := classical_bound' A hd S
  exact ⟨w, hw, hw0⟩
theorem distance_facts {d : Fin n → ℕ} (hd : Distances A d) :
    d 0 = 0 ∧
    (∀ q, (d q = 1 ↔ q ∈ Z A) ∧ (q ∈ Y A ↔ 2 ≤ d q)) ∧
    (∀ q a, a ∈ A.letters → d q ≤ d (a q) + 1) := by
  unfold Distances at hd
  refine ⟨dist_zero hd, fun q => ⟨?_, mem_Y_of_dist hd (Y A) (mem_Y_iff A) q⟩,
    fun q a ha => dist_le_succ hd q ha⟩
  rw [mem_Z_iff]
  constructor
  · intro h1
    obtain ⟨a, ha, had⟩ := dist_step hd (j := 0) h1
    exact ⟨fun h0 => by rw [h0, dist_zero hd] at h1; omega, a, ha, dist_eq_zero hd had⟩
  · rintro ⟨hq0, a, ha, haq⟩
    have h1 := (hd q).2 [a] (word_single A ha) haq
    have h2 : d q ≠ 0 := fun h => hq0 (dist_eq_zero hd h)
    simp at h1
    omega
theorem distance_Y {d : Fin n → ℕ} (hd : Distances A d) :
    (∀ q, d q ≤ (Y A).card + 1) ∧
    ((Y A).Nonempty → ∃ y ∈ Y A, d y = 2) := by
  unfold Distances at hd
  exact ⟨fun q => dist_le_Y hd (Y A) (mem_Y_iff A) q,
    fun hne => dist_two_of_Y hd (Y A) (mem_Y_iff A) hne⟩
theorem short_kill (h : ∃ w, A.IsReset w) (S : Finset (Fin n))
    (hne : (active S).Nonempty) :
    ∃ q ∈ active S, ∃ w, A.IsWord w ∧ act w q = 0 ∧
      w.length ≤ n - (active S).card := by
  obtain ⟨w₀, hw₀, hw₀0⟩ := h
  obtain ⟨d, hd⟩ := dist_exists A fun q => ⟨w₀, hw₀, hw₀0 q⟩
  exact short_kill' A hd S hne
theorem classical_bound (h : ∃ w, A.IsReset w) (S : Finset (Fin n)) :
    Within A S (∑ j ∈ Finset.range (active S).card, (n - (j + 1))) := by
  obtain ⟨w₀, hw₀, hw₀0⟩ := h
  obtain ⟨d, hd⟩ := dist_exists A fun q => ⟨w₀, hw₀, hw₀0 q⟩
  obtain ⟨w, hw, hw0, hlen⟩ := classical_bound' A hd S
  exact ⟨w, ⟨hw, hw0⟩, hlen⟩
end Basic

-- PROOF 119-131: lifting is needed because transformed alphabets can identify letters.
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
theorem lift_word
    (hletters : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τ a = b) (v : List (Letter m)) (hv : B.IsWord v) :
    ∃ u, A.IsWord u ∧ u.map τ = v ∧ u.length = v.length := by
  induction v with
  | nil => exact ⟨[], by simp [Automaton.IsWord], rfl, rfl⟩
  | cons b v ih =>
    have hb : b ∈ B.letters := hv b List.mem_cons_self
    obtain ⟨a, ha, rfl⟩ := (hletters b).1 hb
    obtain ⟨u, hu, hmap, hlen⟩ := ih fun c hc => hv c (List.mem_cons_of_mem _ hc)
    refine ⟨a :: u, ?_, by simp [hmap], by simp [hlen]⟩
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ha
    · exact hu c hc

private theorem push_act (φ : Fin n → Fin m)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (a q) = τ a (φ q))
    (u : List (Letter n)) (hu : A.IsWord u) (q : Fin n) :
    φ (act u q) = act (u.map τ) (φ q) := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    have ha : a ∈ A.letters := hu a List.mem_cons_self
    change φ (act u (a q)) = act (u.map τ) (τ a (φ q))
    rw [ih (fun c hc => hu c (List.mem_cons_of_mem _ hc)), hcomm a ha]

private theorem pull_act (φ : Fin m → Fin n)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (τ a q) = a (φ q))
    (u : List (Letter n)) (hu : A.IsWord u) (q : Fin m) :
    φ (act (u.map τ) q) = act u (φ q) := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    have ha : a ∈ A.letters := hu a List.mem_cons_self
    change φ (act (u.map τ) (τ a q)) = act u (a (φ q))
    rw [ih (fun c hc => hu c (List.mem_cons_of_mem _ hc)), hcomm a ha]

theorem wins_push
    (hletters : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τ a = b) (φ : Fin n → Fin m) (hzero : φ 0 = 0)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (a q) = τ a (φ q))
    {k : ℕ} {S : Finset (Fin n)} (h : A.AliceWins k S) :
    B.AliceWins k (S.image φ) := by
  induction h with
  | reset S hS =>
    refine .reset _ fun q hq => ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    rw [hS p hp, hzero]
  | step S a ha _ ih =>
    refine .step _ (τ a) ((hletters _).2 ⟨a, ha, rfl⟩) fun v hv hlen => ?_
    obtain ⟨u, hu, rfl, hlen'⟩ := lift_word A B τ hletters v hv
    have hu' : A.IsWord (a :: u) := fun c hc => by
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ha
      · exact hu c hc
    have key := ih u hu (hlen' ▸ hlen)
    rw [Finset.image_image] at key ⊢
    convert key using 2
    funext q
    simp only [Function.comp]
    rw [push_act A τ φ hcomm (a :: u) hu' q]
    rfl
theorem wins_pull
    (hletters : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τ a = b) (φ : Fin m → Fin n) (hzero : ∀ q, φ q = 0 ↔ q = 0)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (τ a q) = a (φ q))
    {k : ℕ} (S : Finset (Fin m)) (h : A.AliceWins k (S.image φ)) :
    B.AliceWins k S := by
  suffices H : ∀ X, A.AliceWins k X → ∀ S : Finset (Fin m), S.image φ ⊆ X → B.AliceWins k S from
    H _ h S subset_rfl
  intro X hX
  induction hX with
  | reset X hX =>
    intro S hS
    exact .reset S fun q hq => (hzero q).1 (hX _ (hS (Finset.mem_image_of_mem _ hq)))
  | step X a ha _ ih =>
    intro S hS
    refine .step _ (τ a) ((hletters _).2 ⟨a, ha, rfl⟩) fun v hv hlen => ?_
    obtain ⟨u, hu, rfl, hlen'⟩ := lift_word A B τ hletters v hv
    have hu' : A.IsWord (a :: u) := fun c hc => by
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ha
      · exact hu c hc
    refine ih u hu (hlen' ▸ hlen) _ ?_
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨q, ⟨p, hp, rfl⟩, rfl⟩ := hx
    have := pull_act A τ φ hcomm (a :: u) hu' p
    simp only [List.map_cons] at this
    rw [this]
    exact Finset.mem_image_of_mem _ (hS (Finset.mem_image_of_mem _ hp))
end Transport

/-- `closed_set_of_not_sc` with the plan definition `SC` written out. -/
private theorem closed_set_of_not_sc' {n : ℕ} [NeZero n] (A : Automaton n)
    (h : ¬ ∀ p q : Fin n, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q) :
    ∃ R : Finset (Fin n), 0 ∈ R ∧ 2 ≤ R.card ∧ R.card < n ∧
      ∀ a ∈ A.letters, ∀ q ∈ R, a q ∈ R := by
  classical
  simp only [not_forall] at h
  obtain ⟨p, q, hp, hq, hpq⟩ := h
  set R := Finset.univ.filter (fun x => x = 0 ∨ ∃ w, A.IsWord w ∧ act w p = x) with hR
  refine ⟨R, by simp [hR], ?_, ?_, ?_⟩
  · have hsub : ({0, p} : Finset (Fin n)) ⊆ R := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [hR]
      · simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨[], word_nil A, rfl⟩
    calc 2 = ({0, p} : Finset (Fin n)).card := (Finset.card_pair (Ne.symm hp)).symm
      _ ≤ R.card := Finset.card_le_card hsub
  · have hqR : q ∉ R := by
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
      exact ⟨hq, fun ⟨w, hw, hwq⟩ => hpq ⟨w, hw, hwq⟩⟩
    have : R ⊂ Finset.univ := Finset.ssubset_univ_iff.2 fun h => hqR (h ▸ Finset.mem_univ q)
    simpa using Finset.card_lt_card this
  · intro a ha x hx
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨w, hw, rfl⟩
    · exact Or.inl (A.sink_fixed a ha)
    · refine Or.inr ⟨w ++ [a], (word_append A w [a]).2 ⟨hw, ?_⟩, ?_⟩
      · intro b hb
        simp only [List.mem_singleton] at hb
        exact hb ▸ ha
      · rw [act_append]; rfl

-- PROOF 114-117: forward reachability replaces source SCC selection.
theorem closed_set_of_not_sc {n : ℕ} [NeZero n] (A : Automaton n) (h : ¬ SC A) :
    ∃ R : Finset (Fin n), 0 ∈ R ∧ 2 ≤ R.card ∧ R.card < n ∧
      ∀ a ∈ A.letters, ∀ q ∈ R, a q ∈ R :=
  closed_set_of_not_sc' A h

-- PROOF 109-135, strengthened to every proper closed R of size at least two.
private theorem emb_of_finset {n : ℕ} [NeZero n] (X : Finset (Fin n)) (h0 : (0 : Fin n) ∈ X)
    (p : ℕ) (hp : X.card = p + 1) :
    ∃ e : Fin (p + 1) → Fin n, Function.Injective e ∧ e 0 = 0 ∧ ∀ x, x ∈ X ↔ ∃ i, e i = x := by
  refine ⟨X.orderEmbOfFin hp, (X.orderEmbOfFin hp).injective, ?_, ?_⟩
  · have h1 := Finset.orderEmbOfFin_zero hp (Nat.succ_pos p)
    have h2 : X.min' (Finset.card_pos.mp (hp.symm ▸ Nat.succ_pos p)) ≤ 0 := Finset.min'_le X 0 h0
    have h3 : (X.min' (Finset.card_pos.mp (hp.symm ▸ Nat.succ_pos p))) = 0 :=
      le_antisymm h2 (Fin.zero_le _)
    rw [← h3, ← h1]
    rfl
  · intro x
    have := congrArg (x ∈ ·) (Finset.range_orderEmbOfFin X hp)
    simp only [Set.mem_range, Finset.mem_coe] at this
    exact Iff.of_eq this.symm

theorem closed_reduction {n k : ℕ} [NeZero n] (A : Automaton n) (hk : 1 ≤ k)
    (hA : A.IsAk k) (R : Finset (Fin n)) (hz : 0 ∈ R)
    (hcard : 2 ≤ R.card) (hproper : R.card < n)
    (hclosed : ∀ a ∈ A.letters, ∀ q ∈ R, a q ∈ R) :
    ∃ c d : ℕ, 1 ≤ c ∧ 1 ≤ d ∧ c + d + 1 = n ∧
      d + 1 = R.card ∧
      ∃ B : Automaton (c + 1), ∃ C : Automaton (d + 1),
        B.IsAk k ∧ C.IsAk k ∧
        ∀ u v, B.IsReset u → C.IsReset v →
          ∃ w, A.IsReset w ∧ w.length = u.length + v.length := by
  classical
  set c := n - R.card with hc
  set d := R.card - 1 with hd
  refine ⟨c, d, by omega, by omega, by omega, by omega, ?_⟩
  -- the subautomaton on `R`
  obtain ⟨eC, heCi, heC0, heCr⟩ := emb_of_finset R hz d (by omega)
  set iC := Function.invFun eC with hiC
  have hiCl : ∀ i, iC (eC i) = i := Function.leftInverse_invFun heCi
  have hiCr : ∀ x ∈ R, eC (iC x) = x := fun x hx => Function.invFun_eq ((heCr x).1 hx)
  have heCR : ∀ i, eC i ∈ R := fun i => (heCr _).2 ⟨i, rfl⟩
  let τC : Letter n → Letter (d + 1) := fun a i => iC (a (eC i))
  let C : Automaton (d + 1) :=
    { letters := τC '' A.letters
      sink_fixed := by
        rintro _ ⟨a, ha, rfl⟩
        change iC (a (eC 0)) = 0
        rw [heC0, A.sink_fixed a ha, ← heC0, hiCl] }
  have hCl : ∀ b, b ∈ C.letters ↔ ∃ a ∈ A.letters, τC a = b := fun b => Iff.rfl
  have hCc : ∀ a ∈ A.letters, ∀ q, eC (τC a q) = a (eC q) :=
    fun a ha q => hiCr _ (hclosed a ha _ (heCR q))
  -- the quotient on `Rᶜ ∪ {0}`
  have h0c : (0 : Fin n) ∈ insert 0 Rᶜ := Finset.mem_insert_self _ _
  have hXc : (insert 0 Rᶜ).card = c + 1 := by
    rw [Finset.card_insert_of_notMem (by simpa using hz), Finset.card_compl, Fintype.card_fin]
  obtain ⟨eB, heBi, heB0, heBr⟩ := emb_of_finset (insert 0 Rᶜ) h0c c hXc
  set iB := Function.invFun eB with hiB
  have hiBl : ∀ i, iB (eB i) = i := Function.leftInverse_invFun heBi
  have hiBr : ∀ x ∉ R, eB (iB x) = x := fun x hx =>
    Function.invFun_eq ((heBr x).1 (Finset.mem_insert_of_mem (Finset.mem_compl.2 hx)))
  let π : Fin n → Fin (c + 1) := fun q => if q ∈ R then 0 else iB q
  have hπ0 : π 0 = 0 := by simp [π, hz]
  have hπR : ∀ x, π x = 0 → x ∈ R := by
    intro x hx
    by_contra hxR
    simp only [π, if_neg hxR] at hx
    have := hiBr x hxR
    rw [hx, heB0] at this
    exact hxR (this ▸ hz)
  let τB : Letter n → Letter (c + 1) := fun a i => π (a (eB i))
  let B : Automaton (c + 1) :=
    { letters := τB '' A.letters
      sink_fixed := by
        rintro _ ⟨a, ha, rfl⟩
        change π (a (eB 0)) = 0
        rw [heB0, A.sink_fixed a ha, hπ0] }
  have hBl : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τB a = b := fun b => Iff.rfl
  have hBc : ∀ a ∈ A.letters, ∀ q, π (a q) = τB a (π q) := by
    intro a ha q
    change π (a q) = π (a (eB (π q)))
    by_cases hq : q ∈ R
    · have h1 : π q = 0 := by simp [π, hq]
      rw [h1, heB0, A.sink_fixed a ha, hπ0]
      simp [π, hclosed a ha q hq]
    · have h1 : π q = iB q := by simp [π, hq]
      rw [h1, hiBr q hq]
  refine ⟨B, C, ?_, ?_, ?_⟩
  · have := wins_push A B τB hBl π hπ0 hBc hA
    have hsurj : (Finset.univ : Finset (Fin n)).image π = Finset.univ := by
      refine Finset.eq_univ_of_forall fun i => Finset.mem_image.2 ⟨eB i, Finset.mem_univ _, ?_⟩
      by_cases hi : eB i ∈ R
      · have hmem := (heBr (eB i)).2 ⟨i, rfl⟩
        rcases Finset.mem_insert.1 hmem with h | h
        · have : i = 0 := heBi (h.trans heB0.symm)
          rw [this, heB0, hπ0]
        · exact absurd hi (Finset.mem_compl.1 h)
      · simp [π, hi, hiBl]
    rw [hsurj] at this
    exact this
  · refine wins_pull A C τC hCl eC ?_ hCc Finset.univ (wins_mono A hA (Finset.subset_univ _))
    intro q
    exact ⟨fun h => heCi (h.trans heC0.symm), fun h => h ▸ heC0⟩
  · rintro u v ⟨hu, hu0⟩ ⟨hv, hv0⟩
    obtain ⟨u', hu', rfl, hlu⟩ := lift_word A B τB hBl u hu
    obtain ⟨v', hv', rfl, hlv⟩ := lift_word A C τC hCl v hv
    refine ⟨u' ++ v', ⟨(word_append A u' v').2 ⟨hu', hv'⟩, fun q => ?_⟩, ?_⟩
    swap
    · rw [List.length_append, List.length_map, List.length_map]
    rw [act_append]
    have h1 : π (act u' q) = 0 := by rw [push_act A τB π hBc u' hu' q]; exact hu0 _
    obtain ⟨j, hj⟩ := (heCr _).1 (hπR _ h1)
    rw [← hj, ← pull_act A τC eC hCc v' hv' j, hv0, heC0]

-- PROOF 40, 137-140, 232-234, 326-328.
private theorem f_succ (k n : ℕ) : f k (n + 1) = f k n + (n + k - 1) / k := by
  unfold f
  exact Finset.sum_range_succ _ _

theorem f_one (n : ℕ) : f 1 n = n * (n - 1) / 2 := by
  rw [← Finset.sum_range_id]
  unfold f
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
theorem f_small {k n : ℕ} (hk : 1 ≤ k) (hn : n ≤ k + 1) :
    f k n = n - 1 := by
  induction n with
  | zero => simp [f]
  | succ n ih =>
    rw [f_succ, ih (by omega)]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp only [zero_add]
      rw [Nat.div_eq_of_lt (by omega)]
    · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
      omega

private theorem f_cycle' {k m : ℕ} (hk : 1 ≤ k) (hmk : m ≤ k) :
    f k (k + m + 1) = k + 2 * m := by
  induction m with
  | zero => rw [f_small hk (by omega)]; omega
  | succ m ih =>
    rw [show k + (m + 1) + 1 = (k + m + 1) + 1 by omega, f_succ, ih (by omega),
      Nat.div_eq_of_lt_le (k := 2) (by omega) (by omega)]
    omega

theorem f_cycle {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k) :
    f k (k + m + 1) = k + 2 * m := by
  exact f_cycle' hk hmk
theorem f_split {k c d : ℕ} (hk : 1 ≤ k) :
    f k (c + 1) + f k (d + 1) ≤ f k (c + d + 1) := by
  have h1 : f k (c + d + 1) = f k (d + 1) + ∑ x ∈ Finset.range c, (d + 1 + x + k - 1) / k := by
    rw [show c + d + 1 = (d + 1) + c by omega]
    unfold f
    exact Finset.sum_range_add _ _ _
  have h2 : f k (c + 1) = ∑ x ∈ Finset.range c, (x + 1 + k - 1) / k := by
    unfold f
    rw [Finset.sum_range_succ']
    simp only [zero_add, add_eq_left]
    exact Nat.div_eq_of_lt (by omega)
  rw [h1, h2, add_comm]
  refine Nat.add_le_add_left (Finset.sum_le_sum fun x _ => Nat.div_le_div_right (by omega)) _

/-- The greedy accounting of `greedy`, with `Y`, `Within` and `ResetOn` written out. -/
private theorem greedy' {n : ℕ} [NeZero n] (A : Automaton n) (Y : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (b : ℕ) (hb : n - 1 ≤ b)
    (hT : ∀ T : Finset (Fin n), T.Nonempty → T ⊆ Y →
      ∃ w, (A.IsWord w ∧ ∀ q ∈ T, act w q = 0) ∧ w.length + (n - 1 - T.card) ≤ b) :
    ∃ w, A.IsReset w ∧ w.length ≤ b := by
  classical
  suffices H : ∀ S : Finset (Fin n), ∃ w, A.IsWord w ∧ (∀ q ∈ S, act w q = 0) ∧
      w.length + (n - 1 - (S.erase 0).card) ≤ b by
    obtain ⟨w, hw, hw0, hlen⟩ := H Finset.univ
    rw [active_univ_card] at hlen
    exact ⟨w, ⟨hw, fun q => hw0 q (Finset.mem_univ q)⟩, by omega⟩
  intro S
  induction hm : (S.erase 0).card using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    by_cases hex : ∃ q ∈ S.erase 0, q ∉ Y
    · obtain ⟨q, hq, hqY⟩ := hex
      have hq0 := (Finset.mem_erase.1 hq).1
      have : ∃ a ∈ A.letters, a q = 0 := by
        by_contra hcon
        simp only [not_exists, not_and] at hcon
        exact hqY ((hY q).2 ⟨hq0, hcon⟩)
      obtain ⟨a, ha, haq⟩ := this
      have hdec := kill_decreases' S q hq a (A.sink_fixed a ha) haq
      obtain ⟨w', hw', hw'0, hlen'⟩ := ih _ (by omega) (S.image a) rfl
      have hle := active_card_le (n := n) S
      refine ⟨a :: w', (word_cons A).2 ⟨ha, hw'⟩, fun p hp => hw'0 _ (Finset.mem_image_of_mem _ hp), ?_⟩
      simp only [List.length_cons]
      omega
    · simp only [not_exists, not_and, not_not] at hex
      rcases (S.erase 0).eq_empty_or_nonempty with h | h
      · refine ⟨[], word_nil A, fun q hq => ?_, ?_⟩
        · by_contra hq0
          have : q ∈ S.erase 0 := Finset.mem_erase.2 ⟨hq0, hq⟩
          rw [h] at this; simp at this
        · rw [← hm, h]; simpa using hb
      · obtain ⟨w, ⟨hw, hw0⟩, hlen⟩ := hT (S.erase 0) h hex
        refine ⟨w, hw, fun q hq => ?_, by rw [← hm]; exact hlen⟩
        by_cases hq0 : q = 0
        · rw [hq0]; exact act_zero A w hw
        · exact hw0 q (Finset.mem_erase.2 ⟨hq0, hq⟩)

/-- `escape_to_Y`, with `Y` and `Z` written out: a shortest word into `Y` passes only through `Z`. -/
private theorem escape' {n : ℕ} [NeZero n] (A : Automaton n) (Y Z : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (hZ : ∀ q, q ∈ Z ↔ q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0)
    (x : Fin n) (hreach : ∃ w, A.IsWord w ∧ act w x ∈ Y) :
    ∃ w, A.IsWord w ∧ w.length ≤ Z.card ∧ act w x ∈ Y := by
  classical
  have hP : ∃ ℓ, ∃ w, A.IsWord w ∧ act w x ∈ Y ∧ w.length = ℓ := by
    obtain ⟨w, hw, hwY⟩ := hreach
    exact ⟨_, w, hw, hwY, rfl⟩
  obtain ⟨w, hw, hwY, hlen⟩ := Nat.find_spec hP
  set L := Nat.find hP with hL
  refine ⟨w, hw, ?_, hwY⟩
  have hY0 : ∀ y ∈ Y, y ≠ 0 := fun y hy => ((hY y).1 hy).1
  have hsplit : ∀ i, act w x = act (w.drop i) (act (w.take i) x) := by
    intro i
    rw [← act_append, List.take_append_drop]
  rw [← Finset.card_range w.length]
  refine Finset.card_le_card_of_injOn (fun i => act (w.take i) x) ?_ ?_
  · intro i hi
    have hi : i < w.length := Finset.mem_range.1 hi
    simp only [Finset.mem_coe]
    rw [hZ]
    have hne : act (w.take i) x ≠ 0 := by
      intro h0
      apply hY0 _ hwY
      rw [hsplit i, h0, act_zero A _ (word_drop A hw i)]
    refine ⟨hne, ?_⟩
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hmem : act (w.take i) x ∈ Y := (hY _).2 ⟨hne, hcon⟩
    have := Nat.find_min' hP ⟨w.take i, word_take A hw i, hmem, rfl⟩
    rw [List.length_take] at this
    omega
  · -- a repeated state would give a shortcut
    have key : ∀ i j, i < j → j < w.length → act (w.take i) x ≠ act (w.take j) x := by
      intro i j hlt hj hij
      have hword : A.IsWord (w.take i ++ w.drop j) :=
        (word_append A _ _).2 ⟨word_take A hw i, word_drop A hw j⟩
      have hact : act (w.take i ++ w.drop j) x ∈ Y := by
        rw [act_append, hij, ← hsplit j]; exact hwY
      have := Nat.find_min' hP ⟨_, hword, hact, rfl⟩
      rw [List.length_append, List.length_take, List.length_drop] at this
      omega
    intro i hi j hj hij
    simp only at hij
    have hi : i < w.length := Finset.mem_range.1 hi
    have hj : j < w.length := Finset.mem_range.1 hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key i j hlt hj hij
    · exact key j i hlt hi hij.symm

/-- `few_bad`, with `Y`, `Z` and `SC` written out. -/
private theorem few_bad' {n : ℕ} [NeZero n] (A : Automaton n) {k : ℕ} (hA : A.IsAk k)
    (hsc : ∀ p q : Fin n, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q)
    (Y Z : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (hZ : ∀ q, q ∈ Z ↔ q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0) :
    (Y.Nonempty → k ≤ Z.card) ∧ Y.card ≤ n - 1 - k := by
  have h1 : Y.Nonempty → k ≤ Z.card := by
    intro hne
    by_contra hlt
    apply trap A Y hne (fun h0 => ((hY 0).1 h0).1 rfl) _ hA
    intro t ht a ha
    have hat : a t ≠ 0 := ((hY t).1 ht).2 a ha
    by_cases hY' : a t ∈ Y
    · exact ⟨[], word_nil A, by simp only [List.length_nil]; omega, hY'⟩
    · obtain ⟨y, hy⟩ := hne
      have hreach : ∃ w, A.IsWord w ∧ act w (a t) ∈ Y := by
        obtain ⟨w, hw, hwy⟩ := hsc (a t) y hat ((hY y).1 hy).1
        exact ⟨w, hw, hwy ▸ hy⟩
      obtain ⟨u, hu, hlen, huY⟩ := escape' A Y Z hY hZ (a t) hreach
      exact ⟨u, hu, by omega, huY⟩
  refine ⟨h1, ?_⟩
  have hdisj : Disjoint Y Z := Finset.disjoint_left.2 fun q hqY hqZ => by
    obtain ⟨_, a, ha, h⟩ := (hZ q).1 hqZ
    exact ((hY q).1 hqY).2 a ha h
  have hsub : Y ∪ Z ⊆ Finset.univ.erase 0 := by
    intro q hq
    rcases Finset.mem_union.1 hq with h | h
    · exact Finset.mem_erase.2 ⟨((hY q).1 h).1, Finset.mem_univ _⟩
    · exact Finset.mem_erase.2 ⟨((hZ q).1 h).1, Finset.mem_univ _⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, active_univ_card] at hc
  rcases Y.eq_empty_or_nonempty with h | h
  · rw [h]; simp
  · have := h1 h; omega

/-- `two_bad` (with Lemma 7, `no_return`), with `Y`, `Z` and `Within` written out. -/
private theorem two_bad' {n : ℕ} [NeZero n] (A : Automaton n) {k : ℕ} (hk : 2 ≤ k) (hA : A.IsAk k)
    {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length)
    (Y : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (hcard : Y.card ≤ 2) (T : Finset (Fin n)) (hT : T ⊆ Y) (hsize : T.card = 2) :
    ∃ w, (A.IsWord w ∧ ∀ q ∈ T, act w q = 0) ∧ w.length ≤ 4 := by
  classical
  have hTY : T = Y := Finset.eq_of_subset_of_card_le hT (by omega)
  subst hTY
  obtain ⟨y₁, hy₁, hd₁⟩ := dist_two_of_Y hd T hY (Finset.card_pos.1 (by omega))
  have hpair : ∃ y₂, y₂ ≠ y₁ ∧ T = {y₁, y₂} := by
    obtain ⟨x, y, hxy, hT2⟩ := Finset.card_eq_two.1 hsize
    rw [hT2] at hy₁
    rcases Finset.mem_insert.1 hy₁ with rfl | h
    · exact ⟨y, Ne.symm hxy, hT2⟩
    · rw [Finset.mem_singleton] at h
      subst h
      exact ⟨x, hxy, by rw [hT2, Finset.pair_comm]⟩
  obtain ⟨y₂, hne, hT2⟩ := hpair
  have hmemT : ∀ q, q ∈ T ↔ q = y₁ ∨ q = y₂ := by
    intro q; rw [hT2]; simp
  have hy₂ : y₂ ∈ T := (hmemT y₂).2 (Or.inr rfl)
  -- states outside `T` are at distance at most one
  have hsmall : ∀ r, r ∉ T → d r ≤ 1 := fun r hr => by
    by_contra h
    exact hr ((mem_Y_of_dist hd T hY r).2 (by omega))
  have hd₂ : 2 ≤ d y₂ ∧ d y₂ ≤ 3 :=
    ⟨(mem_Y_of_dist hd T hY y₂).1 hy₂, by have := dist_le_Y hd T hY y₂; omega⟩
  have hdist_le : ∀ r, r ≠ y₂ → d r ≤ 2 := fun r hr => by
    by_cases hrT : r ∈ T
    · rcases (hmemT r).1 hrT with rfl | rfl
      · omega
      · exact absurd rfl hr
    · have := hsmall r hrT; omega
  obtain ⟨w₁, hw₁, hw₁0, hlw₁⟩ := (hd y₁).1
  rcases Nat.lt_or_ge (d y₂) 3 with h3 | h3
  · -- both states of `T` at distance two: every state is at distance at most two
    have hall : ∀ r, d r ≤ 2 := fun r => by
      by_cases hr : r = y₂
      · rw [hr]; omega
      · exact hdist_le r hr
    obtain ⟨w₂, hw₂, hw₂0, hlw₂⟩ := (hd (act w₁ y₂)).1
    refine ⟨w₁ ++ w₂, ⟨(word_append A _ _).2 ⟨hw₁, hw₂⟩, fun q hq => ?_⟩, ?_⟩
    · rw [act_append]
      rcases (hmemT q).1 hq with rfl | rfl
      · rw [hw₁0]; exact act_zero A w₂ hw₂
      · exact hw₂0
    · rw [List.length_append, hlw₁, hlw₂]
      have := hall (act w₁ y₂); omega
  · -- `d y₂ = 3`: Lemma 7
    have hd₂3 : d y₂ = 3 := by omega
    have hmap : ∀ a ∈ A.letters, a y₂ = y₁ ∨ a y₂ = y₂ := by
      intro a ha
      have := dist_le_succ hd y₂ ha
      exact (hmemT _).1 ((mem_Y_of_dist hd T hY _).2 (by omega))
    obtain ⟨c, hc, hcd⟩ := dist_step hd (q := y₂) (j := 2) hd₂3
    have hcy : c y₂ = y₁ := by
      rcases hmap c hc with h | h
      · exact h
      · rw [h] at hcd; omega
    have hno : ∀ a ∈ A.letters, a y₁ ≠ y₂ := by
      intro b hb hby
      refine trap A {y₂} (Finset.singleton_nonempty _) ?_ ?_ hA
      · rw [Finset.mem_singleton]
        exact fun h => ((hY y₂).1 hy₂).1 h.symm
      · intro t ht x hx
        rw [Finset.mem_singleton] at ht
        subst ht
        rcases hmap x hx with h | h
        · refine ⟨[b], word_single A hb, by simp only [List.length_singleton]; omega, ?_⟩
          change b (x t) ∈ _
          rw [h, hby]; exact Finset.mem_singleton_self _
        · refine ⟨[], word_nil A, by simp only [List.length_nil]; omega, ?_⟩
          change x t ∈ _
          rw [h]; exact Finset.mem_singleton_self _
    have hy₁Y := (hY y₁).1 hy₁
    have hz0 : c y₁ ≠ 0 := hy₁Y.2 c hc
    have hz2 : c y₁ ≠ y₂ := hno c hc
    by_cases hz1 : c y₁ = y₁
    · refine ⟨c :: w₁, ⟨(word_cons A).2 ⟨hc, hw₁⟩, fun q hq => ?_⟩, ?_⟩
      · rcases (hmemT q).1 hq with rfl | rfl
        · change act w₁ (c q) = 0; rw [hz1]; exact hw₁0
        · change act w₁ (c q) = 0; rw [hcy]; exact hw₁0
      · simp only [List.length_cons]; omega
    · have hzT : c y₁ ∉ T := fun h => by
        rcases (hmemT _).1 h with h | h
        · exact hz1 h
        · exact hz2 h
      have : ∃ β ∈ A.letters, β (c y₁) = 0 := by
        by_contra hcon
        simp only [not_exists, not_and] at hcon
        exact hzT ((hY _).2 ⟨hz0, hcon⟩)
      obtain ⟨β, hβ, hβz⟩ := this
      obtain ⟨w₂, hw₂, hw₂0, hlw₂⟩ := (hd (β y₁)).1
      refine ⟨c :: β :: w₂, ⟨(word_cons A).2 ⟨hc, (word_cons A).2 ⟨hβ, hw₂⟩⟩, fun q hq => ?_⟩, ?_⟩
      · rcases (hmemT q).1 hq with rfl | rfl
        · change act w₂ (β (c q)) = 0; rw [hβz]; exact act_zero A w₂ hw₂
        · change act w₂ (β (c q)) = 0; rw [hcy]; exact hw₂0
      · simp only [List.length_cons]
        have := hdist_le (β y₁) (hno β hβ)
        omega

private theorem f_lower_aux {k n : ℕ} (hk : 2 ≤ k) (hn : n ≤ k + 3) :
    n - 1 + (n - 1 - k) ≤ f k n := by
  rcases Nat.lt_or_ge n (k + 2) with h | h
  · rw [f_small (by omega) (by omega)]; omega
  · rcases Nat.lt_or_ge n (k + 3) with h' | h'
    · have : n = k + 1 + 1 := by omega
      subst this
      rw [f_cycle' (m := 1) (by omega) (by omega)]; omega
    · have : n = k + 2 + 1 := by omega
      subst this
      rw [f_cycle' (m := 2) (by omega) (by omega)]; omega

/-- `sc_upper`, with `SC` and `Within` written out. -/
private theorem sc_upper' {n : ℕ} [NeZero n] (A : Automaton n) {k : ℕ} (hk : 2 ≤ k) (hA : A.IsAk k)
    (hsc : ∀ p q : Fin n, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q)
    (hn : n ≤ k + 3) : ∃ w, A.IsReset w ∧ w.length ≤ f k n := by
  classical
  obtain ⟨w₀, hw₀, hw₀0⟩ := wins_word' A (by omega) hA
  obtain ⟨d, hd⟩ := dist_exists A fun q => ⟨w₀, hw₀, hw₀0 q (Finset.mem_univ q)⟩
  set Y := Finset.univ.filter (fun q : Fin n => q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0) with hYdef
  set Z := Finset.univ.filter (fun q : Fin n => q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0) with hZdef
  have hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0 := fun q => by simp [hYdef]
  have hZ : ∀ q, q ∈ Z ↔ q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0 := fun q => by simp [hZdef]
  have hfew := (few_bad' A hA hsc Y Z hY hZ).2
  have hf := f_lower_aux hk hn
  have hb : n - 1 ≤ f k n := by omega
  refine greedy' A Y hY (f k n) hb fun T hTne hTY => ?_
  have hTc : T.card ≤ n - 1 - k := (Finset.card_le_card hTY).trans hfew
  have hT1 : 1 ≤ T.card := Finset.card_pos.2 hTne
  rcases Nat.lt_or_ge T.card 2 with h | h
  · obtain ⟨y, rfl⟩ := Finset.card_eq_one.1 (show T.card = 1 by omega)
    obtain ⟨w, hw, hw0, hlw⟩ := (hd y).1
    refine ⟨w, ⟨hw, fun q hq => by rw [Finset.mem_singleton] at hq; rw [hq]; exact hw0⟩, ?_⟩
    have h1 := dist_le_Y hd Y hY y
    have h2 : Y.card ≤ n - 1 - k := hfew
    have h3 : y ≠ 0 := ((hY y).1 (hTY (Finset.mem_singleton_self y))).1
    have h4 : 2 ≤ n := by
      by_contra h5
      have : n = 1 := by have := NeZero.ne n; omega
      subst this
      exact h3 (Subsingleton.elim _ _)
    rw [Finset.card_singleton]
    omega
  · have hY2 : Y.card ≤ 2 := by omega
    have hT2 : T.card = 2 := by
      have := Finset.card_le_card hTY; omega
    obtain ⟨w, hw, hlw⟩ := two_bad' A hk hA hd Y hY hY2 T hTY hT2
    refine ⟨w, hw, ?_⟩
    rw [hT2]
    omega


/-- `upper` for `k ≥ 2`, by strong induction on the number of states (Proposition 10). -/
private theorem upper_ge_two {k : ℕ} (hk : 2 ≤ k) : ∀ N n, n ≤ N → ∀ [NeZero n] (A : Automaton n),
    A.IsAk k → n ≤ k + 3 → ∃ w, A.IsReset w ∧ w.length ≤ f k n := by
  intro N
  induction N with
  | zero =>
    intro n hn _ _
    exact absurd (Nat.le_zero.1 hn) (NeZero.ne n)
  | succ N ih =>
    intro n hn _ A hA hnk
    by_cases hsc : ∀ p q : Fin n, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q
    · exact sc_upper' A hk hA hsc hnk
    · obtain ⟨R, hz, hcard, hproper, hclosed⟩ := closed_set_of_not_sc' A hsc
      obtain ⟨c, d, hc, hd, hcdn, hdR, B, C, hB, hC, hcomb⟩ :=
        closed_reduction A (by omega) hA R hz hcard hproper hclosed
      obtain ⟨u, hu, hlu⟩ := ih (c + 1) (by omega) B hB (by omega)
      obtain ⟨v, hv, hlv⟩ := ih (d + 1) (by omega) C hC (by omega)
      obtain ⟨w, hw, hlw⟩ := hcomb u v hu hv
      refine ⟨w, hw, ?_⟩
      have := f_split (k := k) (c := c) (d := d) (by omega)
      rw [hcdn] at this
      omega

private theorem f_one_sum (n : ℕ) :
    ∑ j ∈ Finset.range (n - 1), (n - (j + 1)) = f 1 n := by
  have hf : f 1 n = ∑ i ∈ Finset.range n, i := by
    unfold f
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [hf]
  rcases n with _ | p
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ', add_zero]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    omega

/-- `upper`, with `Within` written out. -/
private theorem upper' {n k : ℕ} [NeZero n] (A : Automaton n) (hk : 1 ≤ k)
    (hnk : k = 1 ∨ n ≤ k + 3) (hA : A.IsAk k) :
    ∃ w, A.IsReset w ∧ w.length ≤ f k n := by
  rcases Nat.lt_or_ge k 2 with h | h
  · have hk1 : k = 1 := by omega
    subst hk1
    obtain ⟨w₀, hw₀, hw₀0⟩ := wins_word' A le_rfl hA
    obtain ⟨d, hd⟩ := dist_exists A fun q => ⟨w₀, hw₀, hw₀0 q (Finset.mem_univ q)⟩
    obtain ⟨w, hw, hw0, hlw⟩ := classical_bound' A hd Finset.univ
    refine ⟨w, ⟨hw, fun q => hw0 q (Finset.mem_univ q)⟩, ?_⟩
    rw [active_univ_card, f_one_sum] at hlw
    exact hlw
  · have hnk' : n ≤ k + 3 := by omega
    exact upper_ge_two h n n le_rfl A hA hnk'

section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)

-- PROOF 149-152.
theorem escape_to_Y (hsc : SC A) (hne : (Y A).Nonempty) (x : Fin n)
    (hx : x ∈ Z A) :
    ∃ w, A.IsWord w ∧ w.length ≤ (Z A).card ∧ act w x ∈ Y A := by
  have hx0 : x ≠ 0 := ((mem_Z_iff A x).1 hx).1
  obtain ⟨y, hy⟩ := hne
  obtain ⟨w, hw, hwy⟩ := hsc x y hx0 ((mem_Y_iff A y).1 hy).1
  exact escape' A (Y A) (Z A) (mem_Y_iff A) (mem_Z_iff A) x ⟨w, hw, hwy ▸ hy⟩
-- PROOF 146-159.
theorem few_bad (hk : 1 ≤ k) (hA : A.IsAk k) (hsc : SC A) :
    ((Y A).Nonempty → k ≤ (Z A).card) ∧ (Y A).card ≤ n - 1 - k :=
  few_bad' A hA hsc (Y A) (Z A) (mem_Y_iff A) (mem_Z_iff A)
-- PROOF 171-180.
theorem no_return (hk : 2 ≤ k) (hA : A.IsAk k) {d : Fin n → ℕ}
    (hd : Distances A d) (y₁ y₂ : Fin n) (hY : Y A = {y₁, y₂})
    (h₁ : d y₁ = 2) (h₂ : d y₂ = 3) :
    (∀ a ∈ A.letters, a y₂ = y₁ ∨ a y₂ = y₂) ∧
    (∃ c ∈ A.letters, c y₂ = y₁) ∧
    (∀ a ∈ A.letters, a y₁ ≠ y₂) := by
  unfold Distances at hd
  have hmemT : ∀ q, q ∈ Y A ↔ q = y₁ ∨ q = y₂ := by
    intro q; rw [hY]; simp
  have hy₂ : y₂ ∈ Y A := (hmemT y₂).2 (Or.inr rfl)
  have hmap : ∀ a ∈ A.letters, a y₂ = y₁ ∨ a y₂ = y₂ := by
    intro a ha
    have := dist_le_succ hd y₂ ha
    exact (hmemT _).1 ((mem_Y_of_dist hd (Y A) (mem_Y_iff A) _).2 (by omega))
  refine ⟨hmap, ?_, ?_⟩
  · obtain ⟨c, hc, hcd⟩ := dist_step hd (q := y₂) (j := 2) h₂
    refine ⟨c, hc, ?_⟩
    rcases hmap c hc with h | h
    · exact h
    · rw [h] at hcd; omega
  · intro b hb hby
    refine trap A {y₂} (Finset.singleton_nonempty _) ?_ ?_ hA
    · rw [Finset.mem_singleton]
      exact fun h => ((mem_Y_iff A y₂).1 hy₂).1 h.symm
    · intro t ht x hx
      rw [Finset.mem_singleton] at ht
      subst ht
      rcases hmap x hx with h | h
      · refine ⟨[b], word_single A hb, by simp only [List.length_singleton]; omega, ?_⟩
        change b (x t) ∈ _
        rw [h, hby]; exact Finset.mem_singleton_self _
      · refine ⟨[], word_nil A, by simp only [List.length_nil]; omega, ?_⟩
        change x t ∈ _
        rw [h]; exact Finset.mem_singleton_self _
-- PROOF 182-193; additive formulation avoids a reset-threshold maximum.
theorem greedy (b : ℕ) (hb : n - 1 ≤ b)
    (hY : ∀ T : Finset (Fin n), T.Nonempty → T ⊆ Y A →
      ∃ w, ResetOn A T w ∧ w.length + (n - 1 - T.card) ≤ b) :
    Within A Finset.univ b :=
  (within_univ A b).2 (greedy' A (Y A) (mem_Y_iff A) b hb hY)
-- PROOF 214-227.
theorem two_bad (hk : 2 ≤ k) (hA : A.IsAk k) (hcard : (Y A).card ≤ 2)
    (T : Finset (Fin n)) (hT : T ⊆ Y A) (hsize : T.card = 2) :
    Within A T 4 := by
  obtain ⟨w₀, hw₀, hw₀0⟩ := wins_word' A (by omega) hA
  obtain ⟨d, hd⟩ := dist_exists A fun q => ⟨w₀, hw₀, hw₀0 q (Finset.mem_univ q)⟩
  exact two_bad' A hk hA hd (Y A) (mem_Y_iff A) hcard T hT hsize
-- PROOF 199-227, with f evaluated by f_small and f_cycle.
theorem sc_upper (hk : 2 ≤ k) (hA : A.IsAk k) (hsc : SC A)
    (hn : n ≤ k + 3) : Within A Finset.univ (f k n) :=
  (within_univ A _).2 (sc_upper' A hk hA hsc hn)
-- PROOF 229-238, 351-353.
theorem upper (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) (hA : A.IsAk k) :
    Within A Finset.univ (f k n) :=
  (within_univ A _).2 (upper' A hk hnk hA)
end Upper

-- PROOF 250-255. The sink has weight zero; sums count distinct image states.
-- Equation: potential weight S = ∑ q ∈ S, weight q.
def potential {n : ℕ} (weight : Fin n → ℕ) (S : Finset (Fin n)) : ℕ :=
  ∑ q ∈ S, weight q

/-- `potential_bound`, with `potential` written out. -/
private theorem potential_bound' {n : ℕ} [NeZero n] (A : Automaton n) (weight : Fin n → ℕ) (hzero : weight 0 = 0)
    (hstep : ∀ a ∈ A.letters, ∀ S : Finset (Fin n),
      ∑ q ∈ S, weight q ≤ ∑ q ∈ S.image a, weight q + 1)
    (w : List (Letter n)) (hw : A.IsReset w) :
    ∑ q, weight q ≤ w.length := by
  classical
  have key : ∀ (w : List (Letter n)), A.IsWord w → ∀ S : Finset (Fin n),
      ∑ q ∈ S, weight q ≤ ∑ q ∈ S.image (act w), weight q + w.length := by
    intro w
    induction w with
    | nil =>
      intro _ S
      have : S.image (act ([] : List (Letter n))) = S := by ext; simp [act_nil]
      rw [this]; simp
    | cons a w ih =>
      intro hw S
      rw [word_cons] at hw
      have h1 := hstep a hw.1 S
      have h2 := ih hw.2 (S.image a)
      rw [Finset.image_image] at h2
      have : (act w ∘ a) = act (a :: w) := rfl
      rw [this] at h2
      simp only [List.length_cons]
      omega
  have := key w hw.1 Finset.univ
  have h0 : ∑ q ∈ Finset.univ.image (act w), weight q = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hx
    rw [hw.2 q, hzero]
  omega

/-- One step of a potential argument for an injective letter with a single unit deficit at `p`. -/
private theorem pot_perm {n : ℕ} (weight : Fin n → ℕ) (g : Fin n → Fin n) (hg : Function.Injective g)
    (p : Fin n) (hle : ∀ q, q ≠ p → weight q ≤ weight (g q)) (hp : weight p ≤ weight (g p) + 1)
    (S : Finset (Fin n)) :
    ∑ q ∈ S, weight q ≤ ∑ q ∈ S.image g, weight q + 1 := by
  classical
  rw [Finset.sum_image (fun x _ y _ h => hg h)]
  calc ∑ q ∈ S, weight q ≤ ∑ q ∈ S, (weight (g q) + if q = p then 1 else 0) :=
        Finset.sum_le_sum fun q _ => by
          by_cases h : q = p
          · subst h; simpa using hp
          · simpa [h] using hle q h
    _ = ∑ q ∈ S, weight (g q) + ∑ q ∈ S, (if q = p then 1 else 0) := Finset.sum_add_distrib
    _ ≤ ∑ q ∈ S, weight (g q) + 1 := by
        refine Nat.add_le_add_left ?_ _
        rw [Finset.sum_ite_eq']
        split_ifs <;> simp

/-- One step of a potential argument for a letter sending `p` to the sink and fixing the rest. -/
private theorem pot_kill {n : ℕ} (weight : Fin n → ℕ) (g : Fin n → Fin n) (p : Fin n)
    (hfix : ∀ q, q ≠ p → g q = q) (hp : weight p ≤ 1) (S : Finset (Fin n)) :
    ∑ q ∈ S, weight q ≤ ∑ q ∈ S.image g, weight q + 1 := by
  classical
  have hsub : S.erase p ⊆ S.image g := fun q hq => by
    obtain ⟨hqp, hq⟩ := Finset.mem_erase.1 hq
    exact Finset.mem_image.2 ⟨q, hq, hfix q hqp⟩
  have h1 := Finset.sum_le_sum_of_subset (f := weight) hsub
  by_cases hpS : p ∈ S
  · rw [← Finset.add_sum_erase S weight hpS]; omega
  · rw [Finset.erase_eq_of_notMem hpS] at h1; omega

theorem potential_bound {n : ℕ} [NeZero n] (A : Automaton n)
    (weight : Fin n → ℕ) (hzero : weight 0 = 0)
    (hstep : ∀ a ∈ A.letters, ∀ S : Finset (Fin n),
      potential weight S ≤ potential weight (S.image a) + 1)
    (w : List (Letter n)) (hw : A.IsReset w) :
    potential weight Finset.univ ≤ w.length :=
  potential_bound' A weight hzero hstep w hw

-- PROOF 257-267.
-- Equation: kill i q = if q = i then 0 else q.
def kill {n : ℕ} [NeZero n] (i : Fin n) : Letter n :=
  fun q => if q = i then 0 else q
-- Alphabet: {kill (1 : Fin n)} ∪ {a | ∃ i j : Fin n,
--   1 ≤ i.val ∧ j.val = i.val + 1 ∧ a = (Equiv.swap i j : Fin n → Fin n)}.
def transposition (n : ℕ) [NeZero n] : Automaton n :=
  { letters := {kill (1 : Fin n)} ∪ {a | ∃ i j : Fin n,
      1 ≤ i.val ∧ j.val = i.val + 1 ∧ a = (Equiv.swap i j : Fin n → Fin n)}
    sink_fixed := by
      rintro a (h | ⟨i, j, hi, hj, rfl⟩)
      · rw [Set.mem_singleton_iff] at h
        subst h
        simp [kill]
      · refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
        · intro h; rw [← h] at hi; simp at hi
        · intro h; rw [← h] at hj; simp at hj }
theorem transposition_step {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (a : Letter n) (ha : a ∈ (transposition n).letters) (S : Finset (Fin n)) :
    potential Fin.val S ≤ potential Fin.val (S.image a) + 1 := by
  have h1 : (1 : Fin n).val = 1 := by
    show 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  unfold potential
  rcases ha with h | ⟨i, j, hi, hj, rfl⟩
  · rw [Set.mem_singleton_iff] at h
    subst h
    refine pot_kill _ (kill 1) 1 (fun q hq => ?_) (by rw [h1]) S
    simp [kill, hq]
  · refine pot_perm _ _ (Equiv.injective _) j (fun q hq => ?_) ?_ S
    · by_cases hqi : q = i
      · subst hqi; simp [Equiv.swap_apply_left]; omega
      · simp [Equiv.swap_apply_of_ne_of_ne hqi hq]
    · simp [Equiv.swap_apply_right]; omega
theorem sum_values (n : ℕ) :
    potential Fin.val (Finset.univ : Finset (Fin n)) = n * (n - 1) / 2 := by
  unfold potential
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]
theorem transposition_reset {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ∃ w, (transposition n).IsReset w ∧ w.length = n * (n - 1) / 2 := by
  have h1 : (1 : Fin n).val = 1 := by
    show 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hkill1 : kill (1 : Fin n) ∈ (transposition n).letters := Or.inl rfl
  have hreach : ∀ v, ∀ q : Fin n, q.val = v → ∃ w, (transposition n).IsWord w ∧ act w q = 0 := by
    intro v
    induction v with
    | zero => intro q hq; exact ⟨[], word_nil _, by rw [act_nil]; exact Fin.ext (by simp [hq])⟩
    | succ v ih =>
      intro q hq
      rcases Nat.eq_zero_or_pos v with rfl | hv
      · refine ⟨[kill 1], word_single _ hkill1, ?_⟩
        change kill 1 q = 0
        have : q = 1 := Fin.ext (by rw [hq, h1])
        simp [kill, this]
      · let i : Fin n := ⟨v, by omega⟩
        have hsw : ⇑(Equiv.swap i q) ∈ (transposition n).letters := Or.inr ⟨i, q, hv, hq, rfl⟩
        obtain ⟨w, hw, hw0⟩ := ih i rfl
        refine ⟨⇑(Equiv.swap i q) :: w, (word_cons _).2 ⟨hsw, hw⟩, ?_⟩
        change act w (Equiv.swap i q q) = 0
        rw [Equiv.swap_apply_right]; exact hw0
  obtain ⟨d, hd⟩ := dist_exists _ fun q => hreach q.val q rfl
  obtain ⟨w, hw, hw0, hlen⟩ := classical_bound' _ hd Finset.univ
  have hres : (transposition n).IsReset w := ⟨hw, fun q => hw0 q (Finset.mem_univ q)⟩
  refine ⟨w, hres, le_antisymm ?_ ?_⟩
  · rw [active_univ_card, f_one_sum, f_one] at hlen; exact hlen
  · rw [← sum_values n]
    exact potential_bound _ Fin.val rfl (fun a ha S => transposition_step hn a ha S) w hres
theorem transposition_sharp {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (transposition n).IsAk 1 ∧
    ∀ w, (transposition n).IsReset w → f 1 n ≤ w.length := by
  obtain ⟨w, hw, _⟩ := transposition_reset hn
  refine ⟨(one_game_iff _).2 ⟨w, hw⟩, fun w hw => ?_⟩
  rw [f_one, ← sum_values n]
  exact potential_bound _ Fin.val rfl (fun a ha S => transposition_step hn a ha S) w hw

-- PROOF 269-273.
-- Value equation: (predecessor n q).val = q.val - 1.
def predecessor (n : ℕ) : Letter n :=
  fun q => ⟨q.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) q.isLt⟩
-- Alphabet: {predecessor n}.
def path (n : ℕ) [NeZero n] : Automaton n :=
  { letters := {predecessor n}
    sink_fixed := by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact Fin.ext (by simp [predecessor]) }
theorem path_action {n : ℕ} [NeZero n] (w : List (Letter n))
    (hw : (path n).IsWord w) (q : Fin n) :
    (act w q).val = q.val - w.length := by
  induction w generalizing q with
  | nil => simp [act_nil]
  | cons a w ih =>
    have ha : a = predecessor n := hw a List.mem_cons_self
    have hw' : (path n).IsWord w := fun b hb => hw b (List.mem_cons_of_mem a hb)
    change (act w (a q)).val = _
    rw [ih hw', ha, List.length_cons]
    show q.val - 1 - w.length = q.val - (w.length + 1)
    omega
theorem path_sharp {n k : ℕ} [NeZero n] (hk : 1 ≤ k) :
    (path n).IsAk k ∧
    (∃ w, (path n).IsReset w ∧ w.length = n - 1) ∧
    ∀ w, (path n).IsReset w → n - 1 ≤ w.length := by
  have hpred : predecessor n ∈ (path n).letters := rfl
  have hwr : (path n).IsWord (List.replicate (n - 1) (predecessor n)) := by
    intro a ha
    rw [List.mem_replicate] at ha
    rw [ha.2]; exact hpred
  refine ⟨?_, ⟨List.replicate (n - 1) (predecessor n), ⟨hwr, fun q => ?_⟩, by simp⟩, ?_⟩
  · refine wins_of_rank _ (fun S => ∑ q ∈ S, q.val) (fun S hS => ?_) Finset.univ
    refine ⟨predecessor n, hpred, fun u hu hlen => ?_⟩
    have hu' : (path n).IsWord (predecessor n :: u) := (word_cons _).2 ⟨hpred, hu⟩
    obtain ⟨q₀, hq₀⟩ := hS
    have hq₀' : q₀ ∈ S.erase 0 := hq₀
    calc ∑ x ∈ S.image (act (predecessor n :: u)), x.val ≤ ∑ q ∈ S, (act (predecessor n :: u) q).val :=
          Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
      _ < ∑ q ∈ S, q.val := by
          refine Finset.sum_lt_sum (fun q _ => by rw [path_action _ hu']; omega)
            ⟨q₀, (Finset.mem_erase.1 hq₀').2, ?_⟩
          rw [path_action _ hu']
          have : q₀.val ≠ 0 := fun h => (Finset.mem_erase.1 hq₀').1 (Fin.ext (by simpa using h))
          simp only [List.length_cons]
          omega
  · apply Fin.ext
    have := q.isLt
    rw [path_action _ hwr, List.length_replicate]
    simp only [Fin.val_zero]
    omega
  · rintro w ⟨hw, hw0⟩
    have := path_action w hw ⟨n - 1, by have := NeZero.ne n; omega⟩
    rw [hw0] at this
    simp at this
    omega

-- PROOF 275-278: positive state i+1 represents c_i.
-- Equation: shift k m q = if hq : q = 0 then 0 else
--   ⟨q.val % (k + m) + 1, proof using hq and q.isLt⟩.
def shift (k m : ℕ) : Letter (k + m + 1) :=
  fun q => if hq : q = 0 then 0 else
    ⟨q.val % (k + m) + 1, by
      have h1 : q.val ≠ 0 := fun h => hq (Fin.ext (by simp [h]))
      have h2 := q.isLt
      have h3 := Nat.mod_lt q.val (show 0 < k + m by omega)
      omega⟩
-- Alphabet: {shift k m} ∪ {a | ∃ i : Fin (k + m + 1),
--   2 ≤ i.val ∧ i.val ≤ k + 1 ∧ a = kill i}.
def cycle (k m : ℕ) : Automaton (k + m + 1) :=
  { letters := {shift k m} ∪ {a | ∃ i : Fin (k + m + 1),
      2 ≤ i.val ∧ i.val ≤ k + 1 ∧ a = kill i}
    sink_fixed := by
      rintro a (h | ⟨i, _, _, rfl⟩)
      · rw [Set.mem_singleton_iff] at h
        subst h
        simp [shift]
      · simp [kill] }
-- PROOF 283-286.
-- Equation: if q = 0 then 0 else if 2 ≤ q.val ∧ q.val ≤ k + 1 then 1 else 2.
def cycleWeight (k m : ℕ) (q : Fin (k + m + 1)) : ℕ :=
  if q = 0 then 0 else if 2 ≤ q.val ∧ q.val ≤ k + 1 then 1 else 2

private theorem shift_val {k m : ℕ} (q : Fin (k + m + 1)) :
    (shift k m q).val = if q.val = 0 then 0 else q.val % (k + m) + 1 := by
  by_cases h : q = 0
  · subst h; simp [shift]
  · have h' : q.val ≠ 0 := fun h'' => h (Fin.ext (by simp [h'']))
    simp [shift, h, h']

private theorem shift_val_pos {k m : ℕ} (q : Fin (k + m + 1)) (hq : q.val ≠ 0) :
    (shift k m q).val = if q.val < k + m then q.val + 1 else 1 := by
  have := q.isLt
  rw [shift_val, if_neg hq]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h]
  · rw [show q.val = k + m by omega, Nat.mod_self]

private theorem shift_injective {k m : ℕ} : Function.Injective (shift k m) := by
  intro x y hxy
  have h := congrArg Fin.val hxy
  apply Fin.ext
  have hx := x.isLt
  have hy := y.isLt
  by_cases hx0 : x.val = 0 <;> by_cases hy0 : y.val = 0
  · omega
  · rw [shift_val x, if_pos hx0, shift_val_pos y hy0] at h; split_ifs at h <;> omega
  · rw [shift_val y, if_pos hy0, shift_val_pos x hx0] at h; split_ifs at h <;> omega
  · rw [shift_val_pos x hx0, shift_val_pos y hy0] at h; split_ifs at h <;> omega

private theorem cycle_letter {k m : ℕ} (a : Letter (k + m + 1)) (ha : a ∈ (cycle k m).letters) :
    a = shift k m ∨ ∀ q, a q = q ∨ a q = 0 := by
  rcases ha with h | ⟨i, _, _, rfl⟩
  · exact Or.inl h
  · refine Or.inr fun q => ?_
    by_cases h : q = i <;> simp [kill, h]

private theorem cw_val {k m : ℕ} (q : Fin (k + m + 1)) :
    cycleWeight k m q = if q.val = 0 then 0 else if 2 ≤ q.val ∧ q.val ≤ k + 1 then 1 else 2 := by
  by_cases h : q = 0
  · subst h; simp [cycleWeight]
  · have h' : q.val ≠ 0 := fun h'' => h (Fin.ext (by simp [h'']))
    simp [cycleWeight, h, h']

theorem cycle_step {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (a : Letter (k + m + 1)) (ha : a ∈ (cycle k m).letters)
    (S : Finset (Fin (k + m + 1))) :
    potential (cycleWeight k m) S ≤ potential (cycleWeight k m) (S.image a) + 1 := by
  unfold potential
  rcases ha with h | ⟨i, hi2, hik, rfl⟩
  · rw [Set.mem_singleton_iff] at h
    subst h
    obtain ⟨one, hone⟩ : ∃ one : Fin (k + m + 1), one.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
    refine pot_perm _ (shift k m) shift_injective one (fun q hq => ?_) ?_ S
    · have hq1 : q.val ≠ 1 := fun h => hq (Fin.ext (h.trans hone.symm))
      have := q.isLt
      rw [cw_val, cw_val, shift_val]
      by_cases hq0 : q.val = 0
      · simp [hq0]
      · rw [if_neg hq0]
        rcases Nat.lt_or_ge q.val (k + m) with h | h
        · rw [Nat.mod_eq_of_lt h]; split_ifs <;> first | contradiction | omega
        · rw [show q.val = k + m by omega, Nat.mod_self]; split_ifs <;> first | contradiction | omega
    · rw [cw_val, cw_val, shift_val, hone, Nat.mod_eq_of_lt (by omega : 1 < k + m)]
      split_ifs <;> first | contradiction | omega
  · refine pot_kill _ (kill i) i (fun q hq => if_neg hq) ?_ S
    rw [cw_val]
    split_ifs <;> omega
theorem cycle_sum {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    potential (cycleWeight k m) Finset.univ = k + 2 * m := by
  obtain ⟨wt, hwt⟩ : ∃ wt : ℕ → ℕ, ∀ v, wt v = if v = 0 then 0 else if 2 ≤ v ∧ v ≤ k + 1 then 1 else 2 :=
    ⟨_, fun _ => rfl⟩
  have hcw : ∀ q, cycleWeight k m q = wt q.val := fun q => by rw [cw_val, hwt]
  have wt0 : wt 0 = 0 := by rw [hwt, if_pos rfl]
  have wt1 : wt 1 = 2 := by rw [hwt]; split_ifs <;> omega
  have wtK : ∀ v, 2 ≤ v → v ≤ k + 1 → wt v = 1 := fun v h1 h2 => by
    rw [hwt]; split_ifs <;> omega
  have wtO : ∀ v, k + 1 < v → wt v = 2 := fun v h1 => by
    rw [hwt]; split_ifs <;> omega
  unfold potential
  rw [Finset.sum_congr rfl fun q _ => hcw q, Fin.sum_univ_eq_sum_range wt (k + m + 1)]
  have h1 : ∀ s, s ≤ k → ∑ i ∈ Finset.range (s + 2), wt i = s + 2 := by
    intro s
    induction s with
    | zero =>
      intro _
      rw [Finset.sum_range_succ, Finset.sum_range_one, wt0, wt1]
    | succ s ih =>
      intro hs
      have e1 : ∑ i ∈ Finset.range (s + 1 + 2), wt i =
          ∑ i ∈ Finset.range (s + 2), wt i + wt (s + 2) := Finset.sum_range_succ wt (s + 2)
      rw [e1, ih (by omega), wtK (s + 2) (by omega) (by omega)]
  have h2 : ∀ t, t ≤ m - 1 → ∑ i ∈ Finset.range (k + 2 + t), wt i = k + 2 + 2 * t := by
    intro t
    induction t with
    | zero => intro _; exact h1 k le_rfl
    | succ t ih =>
      intro ht
      have e1 : ∑ i ∈ Finset.range (k + 2 + (t + 1)), wt i =
          ∑ i ∈ Finset.range (k + 2 + t), wt i + wt (k + 2 + t) :=
        Finset.sum_range_succ wt (k + 2 + t)
      rw [e1, ih (by omega), wtO _ (by omega)]
      ring
  rw [show k + m + 1 = k + 2 + (m - 1) by omega, h2 (m - 1) le_rfl]
  omega

private theorem act_map_kill {n : ℕ} [NeZero n] (L : List (Fin n)) (q : Fin n) :
    act (L.map kill) q = if q ∈ L then 0 else q := by
  induction L generalizing q with
  | nil => simp [act]
  | cons i L ih =>
    rw [List.map_cons]
    change act (L.map kill) (kill i q) = _
    by_cases hqi : q = i
    · rw [hqi, show kill i i = 0 from if_pos rfl, ih]
      simp
    · rw [show kill i q = q from if_neg hqi, ih]
      simp [hqi]

-- PROOF 288-293.
theorem cycle_reset {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∃ w, (cycle k m).IsReset w ∧ w.length = k + 2 * m := by
  obtain ⟨two, htwo⟩ : ∃ two : Fin (k + m + 1), two.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  have hkill2 : kill two ∈ (cycle k m).letters := Or.inr ⟨two, by omega, by omega, rfl⟩
  have hsh : shift k m ∈ (cycle k m).letters := Or.inl rfl
  obtain ⟨Ks, hKs⟩ : ∃ Ks : List (Fin (k + m + 1)),
      Ks = (List.finRange k).map (fun j => ⟨j.val + 2, by have := j.isLt; omega⟩) := ⟨_, rfl⟩
  have hmemK : ∀ q : Fin (k + m + 1), q ∈ Ks ↔ 2 ≤ q.val ∧ q.val ≤ k + 1 := by
    intro q
    rw [hKs, List.mem_map]
    constructor
    · rintro ⟨j, _, rfl⟩
      have := j.isLt
      show 2 ≤ j.val + 2 ∧ j.val + 2 ≤ k + 1
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨⟨q.val - 2, by omega⟩, List.mem_finRange _, Fin.ext ?_⟩
      show q.val - 2 + 2 = q.val
      omega
  obtain ⟨round, hround⟩ : ∃ r : List (Letter (k + m + 1)), r = [shift k m, kill two] := ⟨_, rfl⟩
  have hword_rep : ∀ r, (cycle k m).IsWord (List.replicate r round).flatten := by
    intro r a ha
    rw [List.mem_flatten] at ha
    obtain ⟨l, hl, hal⟩ := ha
    rw [List.mem_replicate] at hl
    rw [hl.2, hround] at hal
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hal
    rcases hal with rfl | rfl
    · exact hsh
    · exact hkill2
  have hlen_rep : ∀ r, ((List.replicate r round).flatten).length = 2 * r := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, hround]
      simp only [List.length_cons, List.length_nil]
      omega
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin (k + m + 1) → ℕ, ∀ q,
      δ q = if q.val = 1 then 1 else if k + 1 < q.val then k + m + 2 - q.val else 0 :=
    ⟨_, fun _ => rfl⟩
  have hrounds : ∀ r : ℕ, ∀ q : Fin (k + m + 1), (q.val = 1 ∨ (k + 2 ≤ q.val ∧ q.val ≤ k + m)) →
      δ q ≤ r → act (List.replicate r round).flatten q = 0 := by
    intro r
    induction r with
    | zero =>
      intro q hq hd
      exfalso
      rw [hδ] at hd
      split_ifs at hd <;> omega
    | succ r ih =>
      intro q hq hd
      have hr1 : act round q = kill two (shift k m q) := by rw [hround]; rfl
      rw [List.replicate_succ, List.flatten_cons, act_append, hr1]
      have hq0 : q.val ≠ 0 := by omega
      have hsv := shift_val_pos (k := k) (m := m) q hq0
      by_cases h1 : q.val = 1
      · have : shift k m q = two := Fin.ext (by rw [hsv, htwo]; split_ifs <;> omega)
        rw [this, show kill two two = 0 from if_pos rfl]
        exact act_zero _ _ (hword_rep r)
      · have hne : shift k m q ≠ two := fun h => by
          have := congrArg Fin.val h
          rw [hsv, htwo] at this
          split_ifs at this <;> omega
        rw [show kill two (shift k m q) = shift k m q from if_neg hne]
        have := q.isLt
        refine ih _ ?_ ?_
        · rw [hsv]; split_ifs <;> omega
        · rw [hδ] at hd ⊢
          rw [hsv]
          split_ifs at hd ⊢ <;> omega
  have hw1 : (cycle k m).IsWord (Ks.map kill) := by
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact Or.inr ⟨i, ((hmemK i).1 hi).1, ((hmemK i).1 hi).2, rfl⟩
  refine ⟨Ks.map kill ++ (List.replicate m round).flatten,
    ⟨(word_append _ _ _).2 ⟨hw1, hword_rep m⟩, fun q => ?_⟩, ?_⟩
  · rw [act_append, act_map_kill]
    split_ifs with hqK
    · exact act_zero _ _ (hword_rep m)
    · by_cases hq0 : q.val = 0
      · have : q = 0 := Fin.ext (by simp [hq0])
        rw [this]; exact act_zero _ _ (hword_rep m)
      · have := q.isLt
        have hnK := (hmemK q).not.1 hqK
        refine hrounds m q (by omega) ?_
        rw [hδ]
        split_ifs <;> omega
  · rw [List.length_append, List.length_map, hlen_rep, hKs, List.length_map, List.length_finRange]

-- PROOF 302-311: zero on K and sink; delta on O.
-- Equation: if q.val = 1 then 1 else if k + 1 < q.val then k + m + 2 - q.val else 0.
def cycleDelta (k m : ℕ) (q : Fin (k + m + 1)) : ℕ :=
  if q.val = 1 then 1 else if k + 1 < q.val then k + m + 2 - q.val else 0
-- Equation: delay k m S = sInf {r : ℕ | ∃ q ∈ active S, cycleDelta k m q = r}.
noncomputable def delay (k m : ℕ) (S : Finset (Fin (k + m + 1))) : ℕ :=
  sInf {r : ℕ | ∃ q ∈ active S, cycleDelta k m q = r}
-- Equation: cycleRank k m S = (m + 1) * (active S).card + delay k m S.
noncomputable def cycleRank (k m : ℕ) (S : Finset (Fin (k + m + 1))) : ℕ :=
  (m + 1) * (active S).card + delay k m S
theorem delay_spec {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (S : Finset (Fin (k + m + 1))) :
    delay k m S ≤ m ∧
    ((active S).Nonempty → ∃ q ∈ active S, cycleDelta k m q = delay k m S) ∧
    (∀ q ∈ active S, delay k m S ≤ cycleDelta k m q) := by
  have hδm : ∀ q, cycleDelta k m q ≤ m := fun q => by
    have := q.isLt
    unfold cycleDelta; split_ifs <;> omega
  unfold delay
  refine ⟨?_, ?_, ?_⟩
  · rcases (active S).eq_empty_or_nonempty with h | ⟨q, hq⟩
    · have : {r | ∃ q ∈ active S, cycleDelta k m q = r} = ∅ := by
        ext r; simp [h]
      rw [this, Nat.sInf_empty]; omega
    · exact (Nat.sInf_le (by rw [Set.mem_setOf_eq]; exact ⟨q, hq, rfl⟩)).trans (hδm _)
  · rintro ⟨q, hq⟩
    have := Nat.sInf_mem (s := {r | ∃ q ∈ active S, cycleDelta k m q = r}) ⟨_, q, hq, rfl⟩
    rw [Set.mem_setOf_eq] at this
    exact this
  · intro q hq
    exact Nat.sInf_le (by rw [Set.mem_setOf_eq]; exact ⟨q, hq, rfl⟩)

/-- Iterates of the cyclic letter of `C_{k,m}`, on values. -/
private theorem cyc_iter {k m : ℕ} (hkm : 0 < k + m) (e : Letter (k + m + 1))
    (he : ∀ q : Fin (k + m + 1), (e q).val = if q.val = 0 then 0 else q.val % (k + m) + 1)
    (q : Fin (k + m + 1)) (hq : q.val ≠ 0) :
    ∀ s, (e^[s] q).val = (q.val - 1 + s) % (k + m) + 1 := by
  intro s
  induction s with
  | zero =>
    have := q.isLt
    rw [Function.iterate_zero_apply, add_zero, Nat.mod_eq_of_lt (by omega)]
    omega
  | succ s ih =>
    rw [Function.iterate_succ_apply', he, ih, if_neg (Nat.succ_ne_zero _), Nat.mod_add_mod,
      show q.val - 1 + s + 1 = q.val - 1 + (s + 1) by omega]

/-- A single token under a word of `C_{k,m}`: it is killed or advanced by the letters `e` it meets. -/
private theorem cyc_token {N : ℕ} [NeZero N] (A : Automaton N) (e : Letter N)
    (hlet : ∀ a ∈ A.letters, a = e ∨ ∀ q, a q = q ∨ a q = 0) :
    ∀ u : List (Letter N), A.IsWord u → ∀ q, act u q ≠ 0 → ∃ r ≤ u.length, act u q = e^[r] q := by
  intro u
  induction u with
  | nil => intro _ q _; exact ⟨0, le_rfl, rfl⟩
  | cons a u ih =>
    intro hu q hne
    rw [word_cons] at hu
    change act u (a q) ≠ 0 at hne
    change ∃ r ≤ u.length + 1, act u (a q) = e^[r] q
    rcases hlet a hu.1 with rfl | h
    · obtain ⟨r, hr, hrq⟩ := ih hu.2 (a q) hne
      exact ⟨r + 1, by omega, by rw [hrq, Function.iterate_succ_apply]⟩
    · rcases h q with h | h
      · rw [h] at hne ⊢
        obtain ⟨r, hr, hrq⟩ := ih hu.2 q hne
        exact ⟨r, by omega, hrq⟩
      · rw [h, act_zero A u hu.2] at hne
        exact absurd rfl hne

/-- The delay of a token of `O` strictly drops in a round where Alice plays `e`. -/
private theorem cyc_delta_lt {k m v s : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (δ : ℕ → ℕ)
    (hδ : ∀ v, δ v = if v = 1 then 1 else if k + 1 < v then k + m + 2 - v else 0)
    (hv : v = 1 ∨ (k + 2 ≤ v ∧ v ≤ k + m)) (hs1 : 1 ≤ s) (hsk : s ≤ k) :
    δ ((v - 1 + s) % (k + m) + 1) < δ v := by
  rcases Nat.lt_or_ge (v - 1 + s) (k + m) with h | h
  · rw [Nat.mod_eq_of_lt h, hδ, hδ]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega), hδ, hδ]
    split_ifs <;> omega

-- PROOF 295-317: strict decrease compresses the bounded-round argument.
theorem cycle_rank_step {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (S : Finset (Fin (k + m + 1))) (hne : (active S).Nonempty) :
    ∃ a ∈ (cycle k m).letters, ∀ u, (cycle k m).IsWord u → u.length < k →
      cycleRank k m (S.image (act (a :: u))) < cycleRank k m S := by
  have hkm : 0 < k + m := by omega
  have hval0 : ∀ q : Fin (k + m + 1), q = 0 ↔ q.val = 0 := fun q => Fin.ext_iff
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℕ, ∀ v, δ v = if v = 1 then 1 else if k + 1 < v then k + m + 2 - v else 0 :=
    ⟨_, fun _ => rfl⟩
  have hδq : ∀ q, cycleDelta k m q = δ q.val := fun q => by rw [hδ]; rfl
  unfold cycleRank
  by_cases hK : ∃ i ∈ active S, 2 ≤ i.val ∧ i.val ≤ k + 1
  · obtain ⟨i, hi, hi2, hik⟩ := hK
    have hkli : kill i ∈ (cycle k m).letters := Or.inr ⟨i, hi2, hik, rfl⟩
    refine ⟨kill i, hkli, fun u hu _ => ?_⟩
    have hw : (cycle k m).IsWord (kill i :: u) := (word_cons _).2 ⟨hkli, hu⟩
    have hdec := kill_decreases _ S i hi (kill i :: u) hw (by
      change act u (kill i i) = 0
      rw [show kill i i = 0 from if_pos rfl]
      exact act_zero _ u hu)
    have h1 := (delay_spec hk hm (S.image (act (kill i :: u)))).1
    have h2 := Nat.mul_le_mul_left (m + 1) hdec
    rw [mul_add, mul_one] at h2
    omega
  · simp only [not_exists, not_and] at hK
    refine ⟨shift k m, Or.inl rfl, fun u hu hlen => ?_⟩
    have hw : (cycle k m).IsWord (shift k m :: u) := (word_cons _).2 ⟨Or.inl rfl, hu⟩
    have hle := image_active_le _ S (shift k m :: u) hw
    obtain ⟨q, hq, hqδ⟩ := (delay_spec hk hm S).2.1 hne
    have hq' : q ∈ S.erase 0 := hq
    have hq0 : q.val ≠ 0 := fun h => (Finset.mem_erase.1 hq').1 ((hval0 q).2 h)
    have hqO : q.val = 1 ∨ (k + 2 ≤ q.val ∧ q.val ≤ k + m) := by
      have := q.isLt
      have := hK q hq
      omega
    by_cases hp0 : act (shift k m :: u) q = 0
    · have hdec := kill_decreases _ S q hq (shift k m :: u) hw hp0
      have h1 := (delay_spec hk hm (S.image (act (shift k m :: u)))).1
      have h2 := Nat.mul_le_mul_left (m + 1) hdec
      rw [mul_add, mul_one] at h2
      omega
    · obtain ⟨r, hr, hpr⟩ := cyc_token (cycle k m) (shift k m) (fun a ha => cycle_letter a ha)
        u hu (shift k m q) hp0
      have hp : act (shift k m :: u) q = (shift k m)^[r + 1] q := by
        change act u (shift k m q) = _
        rw [hpr, Function.iterate_succ_apply]
      have hpval := cyc_iter hkm (shift k m) shift_val q hq0 (r + 1)
      have hlt := cyc_delta_lt hk hm δ hδ hqO (by omega : 1 ≤ r + 1) (by omega : r + 1 ≤ k)
      have hpmem : act (shift k m :: u) q ∈ active (S.image (act (shift k m :: u))) :=
        Finset.mem_erase.2 ⟨hp0, Finset.mem_image_of_mem _ (Finset.mem_erase.1 hq').2⟩
      have h1 := (delay_spec hk hm _).2.2 _ hpmem
      rw [hδq, hp, hpval] at h1
      rw [hδq] at hqδ
      have h2 := Nat.mul_le_mul_left (m + 1) hle
      omega
theorem cycle_wins {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (cycle k m).IsAk k :=
  wins_of_rank _ (cycleRank k m) (fun S hS => cycle_rank_step hk hm S hS) Finset.univ

private theorem act_replicate {n : ℕ} (e : Letter n) (r : ℕ) (q : Fin n) :
    act (List.replicate r e) q = e^[r] q := by
  induction r generalizing q with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ]
    change act (List.replicate r e) (e q) = _
    rw [ih, Function.iterate_succ_apply]

-- PROOF 319-324.
theorem cycle_loses {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ¬ (cycle k m).IsAk (k + 1) := by
  have hkm : 0 < k + m := by omega
  refine trap _ (Finset.univ.filter (fun q : Fin (k + m + 1) => q.val = 1 ∨ k + 1 < q.val))
    ⟨⟨1, by omega⟩, by simp⟩ (by simp) ?_
  intro t ht a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
  have ht0 : t.val ≠ 0 := by omega
  have := t.isLt
  rcases ha with h | ⟨i, hi2, hik, rfl⟩
  · rw [Set.mem_singleton_iff] at h
    subst h
    by_cases ht1 : t.val = 1
    · refine ⟨List.replicate k (shift k m), fun b hb => ?_, by simp, ?_⟩
      · rw [List.mem_replicate] at hb
        rw [hb.2]; exact Or.inl rfl
      · have hv : (act (shift k m :: List.replicate k (shift k m)) t).val = (k + 1) % (k + m) + 1 := by
          change (act (List.replicate k (shift k m)) (shift k m t)).val = _
          rw [act_replicate, show (shift k m)^[k] (shift k m t) = (shift k m)^[k + 1] t from
            (Function.iterate_succ_apply _ _ _).symm, cyc_iter hkm _ shift_val t ht0 (k + 1), ht1,
            Nat.sub_self, zero_add]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hv]
        rcases Nat.lt_or_ge (k + 1) (k + m) with h | h
        · right; rw [Nat.mod_eq_of_lt h]; omega
        · left; rw [show k + m = k + 1 by omega, Nat.mod_self]
    · refine ⟨[], word_nil _, by simp, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (shift k m t).val = 1 ∨ k + 1 < (shift k m t).val
      rw [shift_val_pos t ht0]
      split_ifs <;> omega
  · refine ⟨[], word_nil _, by simp, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hti : t ≠ i := fun h => by subst h; omega
    change (kill i t).val = 1 ∨ k + 1 < (kill i t).val
    rw [show kill i t = t from if_neg hti]
    exact ht
-- PROOF 275-328: full construction theorem, including m > k.
theorem cycle_sharp {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (cycle k m).IsAk k ∧
    (∃ w, (cycle k m).IsReset w ∧ w.length = k + 2 * m) ∧
    (∀ w, (cycle k m).IsReset w → k + 2 * m ≤ w.length) ∧
    ¬ (cycle k m).IsAk (k + 1) := by
  refine ⟨cycle_wins hk hm, cycle_reset hk hm, fun w hw => ?_, cycle_loses hk hm⟩
  rw [← cycle_sum hk hm]
  exact potential_bound _ _ (by simp [cycleWeight]) (fun a ha S => cycle_step hk hm a ha S) w hw

/-! The helpers below restate the plan's lemmas with the plan definitions (`active`, `ResetOn`,
`Within`, `SC`, `Z`, `Y`, `Distances`, `potential` and the example automata) written out, so that
`lower` and the statements of record are proved from `SinkReset.Basic` alone. -/

/-- The path automaton: one letter lowering every positive state by one. -/
private theorem path_exists {n : ℕ} [NeZero n] (k : ℕ) :
    ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → n - 1 ≤ w.length := by
  classical
  let pred : Letter n := fun q => ⟨q.val - 1, by omega⟩
  have hpred : ∀ q, (pred q).val = q.val - 1 := fun q => rfl
  let P : Automaton n :=
    { letters := {pred}
      sink_fixed := by
        rintro a rfl
        exact Fin.ext (by rw [hpred]; simp) }
  have hact : ∀ w, P.IsWord w → ∀ q : Fin n, (act w q).val = q.val - w.length := by
    intro w
    induction w with
    | nil => intro _ q; simp [act_nil]
    | cons a w ih =>
      intro hw q
      rw [word_cons] at hw
      have ha : a = pred := hw.1
      change (act w (a q)).val = _
      rw [ih hw.2, ha, hpred, List.length_cons]
      omega
  refine ⟨P, ?_, ?_⟩
  · refine wins_of_rank' P (fun S => ∑ q ∈ S, q.val) (fun S hS => ?_) Finset.univ
    refine ⟨pred, rfl, fun u hu hlen => ?_⟩
    have hu' : P.IsWord (pred :: u) := (word_cons P).2 ⟨rfl, hu⟩
    obtain ⟨q₀, hq₀⟩ := hS
    calc ∑ x ∈ S.image (act (pred :: u)), x.val ≤ ∑ q ∈ S, (act (pred :: u) q).val :=
          Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
      _ < ∑ q ∈ S, q.val := by
          refine Finset.sum_lt_sum (fun q _ => by rw [hact _ hu']; omega) ⟨q₀, (Finset.mem_erase.1 hq₀).2, ?_⟩
          rw [hact _ hu']
          have : q₀.val ≠ 0 := fun h => (Finset.mem_erase.1 hq₀).1 (Fin.ext (by simpa using h))
          simp only [List.length_cons]
          omega
  · rintro w ⟨hw, hw0⟩
    have := hact w hw ⟨n - 1, by have := NeZero.ne n; omega⟩
    rw [hw0] at this
    simp at this
    omega

/-- The transposition automaton (`k = 1`). -/
private theorem transposition_exists {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ∃ A : Automaton n, A.IsAk 1 ∧ ∀ w, A.IsReset w → f 1 n ≤ w.length := by
  classical
  let kill1 : Letter n := fun q => if q.val = 1 then 0 else q
  let T : Automaton n :=
    { letters := {a | a = kill1 ∨ ∃ i j : Fin n, 1 ≤ i.val ∧ j.val = i.val + 1 ∧
        a = ⇑(Equiv.swap i j)}
      sink_fixed := by
        rintro a (rfl | ⟨i, j, hi, hj, rfl⟩)
        · simp [kill1]
        · refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
          · intro h; rw [← h] at hi; simp at hi
          · intro h; rw [← h] at hj; simp at hj }
  have hkill1 : kill1 ∈ T.letters := Or.inl rfl
  refine ⟨T, ?_, ?_⟩
  · -- every state can be sent to the sink, hence `T` is synchronizing
    have hreach : ∀ v, ∀ q : Fin n, q.val = v → ∃ w, T.IsWord w ∧ act w q = 0 := by
      intro v
      induction v with
      | zero => intro q hq; exact ⟨[], word_nil T, by rw [act_nil]; exact Fin.ext (by simp [hq])⟩
      | succ v ih =>
        intro q hq
        rcases Nat.eq_zero_or_pos v with rfl | hv
        · exact ⟨[kill1], word_single T hkill1, by
            change kill1 q = 0; simp [kill1, hq]⟩
        · let i : Fin n := ⟨v, by omega⟩
          have hsw : ⇑(Equiv.swap i q) ∈ T.letters := Or.inr ⟨i, q, hv, hq, rfl⟩
          obtain ⟨w, hw, hw0⟩ := ih i rfl
          refine ⟨⇑(Equiv.swap i q) :: w, (word_cons T).2 ⟨hsw, hw⟩, ?_⟩
          change act w (Equiv.swap i q q) = 0
          rw [Equiv.swap_apply_right]; exact hw0
    obtain ⟨d, hd⟩ := dist_exists T fun q => hreach q.val q rfl
    obtain ⟨w, hw, hw0, _⟩ := classical_bound' T hd Finset.univ
    exact (one_game_iff T).2 ⟨w, hw, fun q => hw0 q (Finset.mem_univ q)⟩
  · intro w hw
    have hpot := potential_bound' T (fun q => q.val) rfl (fun a ha S => ?_) w hw
    · have hsum : ∑ q : Fin n, q.val = f 1 n := by
        rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
        unfold f
        refine Finset.sum_congr rfl fun i _ => ?_
        simp
      rw [hsum] at hpot
      exact hpot
    · rcases ha with rfl | ⟨i, j, hi, hj, rfl⟩
      · refine pot_kill _ kill1 ⟨1, by omega⟩ (fun q hq => ?_) le_rfl S
        have : q.val ≠ 1 := fun h => hq (Fin.ext h)
        simp [kill1, this]
      · refine pot_perm _ _ (Equiv.injective _) j (fun q hq => ?_) ?_ S
        · by_cases hqi : q = i
          · subst hqi; simp [Equiv.swap_apply_left]; omega
          · simp [Equiv.swap_apply_of_ne_of_ne hqi hq]
        · simp [Equiv.swap_apply_right]; omega

/-- The cycle automaton `C_{k,m}`: an `A_k` automaton with no reset word shorter than `k + 2m`. -/
private theorem cycle_exists {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∃ A : Automaton (k + m + 1), A.IsAk k ∧ ∀ w, A.IsReset w → k + 2 * m ≤ w.length := by
  classical
  have hkm : 0 < k + m := by omega
  let e : Letter (k + m + 1) := fun q =>
    if h : q.val = 0 then 0 else ⟨q.val % (k + m) + 1, by have := Nat.mod_lt q.val hkm; omega⟩
  have he : ∀ q : Fin (k + m + 1), (e q).val = if q.val = 0 then 0 else q.val % (k + m) + 1 := by
    intro q
    by_cases h : q.val = 0
    · rw [if_pos h]
      show (if h : q.val = 0 then (0 : Fin (k + m + 1)) else _).val = 0
      rw [dif_pos h]
      rfl
    · rw [if_neg h]
      show (if h : q.val = 0 then (0 : Fin (k + m + 1)) else _).val = _
      rw [dif_neg h]
  let kl : Fin (k + m + 1) → Letter (k + m + 1) := fun i q => if q = i then 0 else q
  let C : Automaton (k + m + 1) :=
    { letters := {a | a = e ∨ ∃ i : Fin (k + m + 1), 2 ≤ i.val ∧ i.val ≤ k + 1 ∧ a = kl i}
      sink_fixed := by
        rintro a (rfl | ⟨i, _, _, rfl⟩)
        · exact Fin.ext (by rw [he, if_pos (show ((0 : Fin (k + m + 1)) : ℕ) = 0 from rfl)]; rfl)
        · show (if (0 : Fin (k + m + 1)) = i then 0 else 0) = 0
          exact ite_self _ }
  have hval0 : ∀ q : Fin (k + m + 1), q = 0 ↔ q.val = 0 := fun q => Fin.ext_iff
  have hev : ∀ q : Fin (k + m + 1), q.val ≠ 0 →
      (e q).val = if q.val < k + m then q.val + 1 else 1 := by
    intro q hq
    have := q.isLt
    rw [he, if_neg hq]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · rw [show q.val = k + m by omega, Nat.mod_self]
  refine ⟨C, ?_, ?_⟩
  · -- `C` is `A_k`: Alice kills a token of `K` if there is one, and plays `e` otherwise
    obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℕ, ∀ v, δ v = if v = 1 then 1 else if k + 1 < v then k + m + 2 - v else 0 :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨delay, hdelay⟩ : ∃ delay : Finset (Fin (k + m + 1)) → ℕ,
        ∀ S, delay S = sInf {r | ∃ q ∈ S.erase 0, δ q.val = r} := ⟨_, fun _ => rfl⟩
    have hδm : ∀ v, δ v ≤ m := fun v => by rw [hδ]; split_ifs <;> omega
    have hdelay_le : ∀ S, delay S ≤ m := by
      intro S
      rw [hdelay]
      rcases (S.erase 0).eq_empty_or_nonempty with h | ⟨q, hq⟩
      · have : {r | ∃ q ∈ S.erase 0, δ q.val = r} = ∅ := by
          ext r; simp [h]
        rw [this, Nat.sInf_empty]; omega
      · exact (Nat.sInf_le (by rw [Set.mem_setOf_eq]; exact ⟨q, hq, rfl⟩)).trans (hδm _)
    have hdelay_min : ∀ S, ∀ q ∈ S.erase 0, delay S ≤ δ q.val := fun S q hq => by
      rw [hdelay]; exact Nat.sInf_le (by rw [Set.mem_setOf_eq]; exact ⟨q, hq, rfl⟩)
    have hdelay_mem : ∀ S : Finset (Fin (k + m + 1)), (S.erase 0).Nonempty →
        ∃ q ∈ S.erase 0, δ q.val = delay S := by
      rintro S ⟨q, hq⟩
      rw [hdelay]
      have := Nat.sInf_mem (s := {r | ∃ q ∈ S.erase 0, δ q.val = r}) ⟨_, q, hq, rfl⟩
      rw [Set.mem_setOf_eq] at this
      exact this
    have hlet' : ∀ a ∈ C.letters, a = e ∨ ∀ q, a q = q ∨ a q = 0 := by
      rintro a (rfl | ⟨i, _, _, rfl⟩)
      · exact Or.inl rfl
      · refine Or.inr fun q => ?_
        by_cases h : q = i <;> simp [kl, h]
    refine wins_of_rank' C (fun S => (m + 1) * (S.erase 0).card + delay S) (fun S hS => ?_)
      Finset.univ
    by_cases hK : ∃ i ∈ S.erase 0, 2 ≤ i.val ∧ i.val ≤ k + 1
    · obtain ⟨i, hi, hi2, hik⟩ := hK
      have hkli : kl i ∈ C.letters := Or.inr ⟨i, hi2, hik, rfl⟩
      refine ⟨kl i, hkli, fun u hu _ => ?_⟩
      have hw : C.IsWord (kl i :: u) := (word_cons C).2 ⟨hkli, hu⟩
      have hdec := kill_decreases' S i hi (act (kl i :: u)) (act_zero C _ hw) (by
        change act u (if i = i then 0 else i) = 0
        rw [if_pos rfl]
        exact act_zero C u hu)
      have h1 := hdelay_le (S.image (act (kl i :: u)))
      have h2 := Nat.mul_le_mul_left (m + 1) hdec
      rw [mul_add, mul_one] at h2
      omega
    · simp only [not_exists, not_and] at hK
      refine ⟨e, Or.inl rfl, fun u hu hlen => ?_⟩
      have hw : C.IsWord (e :: u) := (word_cons C).2 ⟨Or.inl rfl, hu⟩
      have hle := image_active_le' S (act (e :: u)) (act_zero C _ hw)
      obtain ⟨q, hq, hqδ⟩ := hdelay_mem S hS
      have hq0 : q.val ≠ 0 := fun h => (Finset.mem_erase.1 hq).1 ((hval0 q).2 h)
      have hqO : q.val = 1 ∨ (k + 2 ≤ q.val ∧ q.val ≤ k + m) := by
        have := q.isLt
        have := hK q hq
        omega
      by_cases hp0 : act (e :: u) q = 0
      · have hdec := kill_decreases' S q hq (act (e :: u)) (act_zero C _ hw) hp0
        have h1 := hdelay_le (S.image (act (e :: u)))
        have h2 := Nat.mul_le_mul_left (m + 1) hdec
        rw [mul_add, mul_one] at h2
        omega
      · obtain ⟨r, hr, hpr⟩ := cyc_token C e hlet' u hu (e q) hp0
        have hp : act (e :: u) q = e^[r + 1] q := by
          change act u (e q) = _
          rw [hpr, Function.iterate_succ_apply]
        have hpval := cyc_iter hkm e he q hq0 (r + 1)
        have hlt := cyc_delta_lt hk hm δ hδ hqO (by omega : 1 ≤ r + 1) (by omega : r + 1 ≤ k)
        have hpmem : act (e :: u) q ∈ (S.image (act (e :: u))).erase 0 :=
          Finset.mem_erase.2 ⟨hp0, Finset.mem_image_of_mem _ (Finset.mem_erase.1 hq).2⟩
        have h1 := hdelay_min _ _ hpmem
        rw [hp, hpval] at h1
        have h2 := Nat.mul_le_mul_left (m + 1) hle
        omega
  · -- lower bound by the potential with weight `1` on `K` and `2` on `O`
    intro w hw
    obtain ⟨wt, hwt⟩ : ∃ wt : ℕ → ℕ, ∀ v, wt v = if v = 0 then 0 else if 2 ≤ v ∧ v ≤ k + 1 then 1 else 2 :=
      ⟨_, fun _ => rfl⟩
    have wt0 : wt 0 = 0 := by rw [hwt, if_pos rfl]
    have wt1 : wt 1 = 2 := by rw [hwt]; split_ifs <;> omega
    have wtK : ∀ v, 2 ≤ v → v ≤ k + 1 → wt v = 1 := fun v h1 h2 => by
      rw [hwt]; split_ifs <;> omega
    have wtO : ∀ v, k + 1 < v → wt v = 2 := fun v h1 => by
      rw [hwt]; split_ifs <;> omega
    have wtpos : ∀ v, v ≠ 0 → 1 ≤ wt v := fun v h1 => by
      rw [hwt]; split_ifs <;> omega
    have hpot := potential_bound' C (fun q => wt q.val) wt0 (fun a ha S => ?_) w hw
    · have hsum : ∑ q : Fin (k + m + 1), wt q.val = k + 2 * m := by
        rw [Fin.sum_univ_eq_sum_range wt (k + m + 1)]
        have h1 : ∀ s, s ≤ k → ∑ i ∈ Finset.range (s + 2), wt i = s + 2 := by
          intro s
          induction s with
          | zero =>
            intro _
            rw [Finset.sum_range_succ, Finset.sum_range_one, wt0, wt1]
          | succ s ih =>
            intro hs
            have e1 : ∑ i ∈ Finset.range (s + 1 + 2), wt i =
                ∑ i ∈ Finset.range (s + 2), wt i + wt (s + 2) := Finset.sum_range_succ wt (s + 2)
            rw [e1, ih (by omega), wtK (s + 2) (by omega) (by omega)]
        have h2 : ∀ t, t ≤ m - 1 → ∑ i ∈ Finset.range (k + 2 + t), wt i = k + 2 + 2 * t := by
          intro t
          induction t with
          | zero => intro _; exact h1 k le_rfl
          | succ t ih =>
            intro ht
            have e1 : ∑ i ∈ Finset.range (k + 2 + (t + 1)), wt i =
                ∑ i ∈ Finset.range (k + 2 + t), wt i + wt (k + 2 + t) :=
              Finset.sum_range_succ wt (k + 2 + t)
            rw [e1, ih (by omega), wtO _ (by omega)]
            ring
        rw [show k + m + 1 = k + 2 + (m - 1) by omega, h2 (m - 1) le_rfl]
        omega
      rw [hsum] at hpot
      exact hpot
    · rcases ha with rfl | ⟨i, hi2, hik, rfl⟩
      · let one : Fin (k + m + 1) := ⟨1, by omega⟩
        have hone : one.val = 1 := rfl
        refine pot_perm _ e ?_ one (fun q hq => ?_) ?_ S
        · intro x y hxy
          have h := congrArg Fin.val hxy
          apply Fin.ext
          have hx := x.isLt
          have hy := y.isLt
          by_cases hx0 : x.val = 0 <;> by_cases hy0 : y.val = 0
          · omega
          · rw [he x, if_pos hx0, hev y hy0] at h; split_ifs at h <;> omega
          · rw [he y, if_pos hy0, hev x hx0] at h; split_ifs at h <;> omega
          · rw [hev x hx0, hev y hy0] at h; split_ifs at h <;> omega
        · have hq1 : q.val ≠ 1 := fun h => hq (Fin.ext h)
          have := q.isLt
          by_cases hq0 : q.val = 0
          · show wt q.val ≤ wt (e q).val
            rw [hq0, wt0]; exact Nat.zero_le _
          · show wt q.val ≤ wt (e q).val
            have hev' := hev q hq0
            rcases Nat.lt_or_ge (k + 1) q.val with hO | hK'
            · rw [wtO _ hO]
              split_ifs at hev' with hlt
              · rw [hev', wtO _ (by omega)]
              · rw [hev', wt1]
            · rw [wtK _ (by omega) hK']
              exact wtpos _ (by rw [hev']; split_ifs <;> omega)
        · show wt one.val ≤ wt (e one).val + 1
          have h1 := hev one (by rw [hone]; omega)
          rw [hone, if_pos (by omega)] at h1
          rw [h1, hone, wt1, wtK 2 le_rfl (by omega)]
      · refine pot_kill _ (kl i) i (fun q hq => if_neg hq) ?_ S
        show wt i.val ≤ 1
        rw [wtK _ hi2 hik]

-- PROOF 330-332, 355-363: stronger lower range than the record.
theorem lower {n k : ℕ} [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hnk : k = 1 ∨ n ≤ 2 * k + 1) :
    ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length := by
  rcases Nat.lt_or_ge (k + 1) n with h1 | h1
  · rcases hnk with rfl | hnk
    · exact transposition_exists hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = k + m + 1 := ⟨n - k - 1, by omega⟩
      obtain ⟨A, hA, hlow⟩ := cycle_exists hk (by omega : 1 ≤ m)
      refine ⟨A, hA, fun w hw => ?_⟩
      rw [f_cycle' hk (by omega)]
      exact hlow w hw
  · obtain ⟨A, hA, hlow⟩ := path_exists (n := n) k
    refine ⟨A, hA, fun w hw => ?_⟩
    rw [f_small hk h1]
    exact hlow w hw

end Plan

-- PROOF 229-238, 341-368. Exact statement signatures from Challenge.lean, under `_dev` names.
theorem reset_word_le_of_isAk_dev (n k : ℕ) [NeZero n] (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) (A : Automaton n) (hA : A.IsAk k) : ∃ w, A.IsReset w ∧ w.length ≤ f k n := by
  exact Plan.upper' A hk hnk hA

theorem exists_isAk_reset_ge_dev (n k : ℕ) [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) : ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length := by
  refine Plan.lower hn hk ?_
  omega

theorem five_two_reset_word_le_dev (A : Automaton 5) (hA : A.IsAk 2) : ∃ w, A.IsReset w ∧ w.length ≤ 6 := by
  have h : f 2 5 = 6 := by simp [f, Finset.sum_range_succ]
  rw [← h]
  exact reset_word_le_of_isAk_dev 5 2 (by norm_num) (by norm_num) A hA

theorem five_two_exists_isAk_reset_ge_dev : ∃ A : Automaton 5, A.IsAk 2 ∧ ∀ w, A.IsReset w → 6 ≤ w.length := by
  have h : f 2 5 = 6 := by simp [f, Finset.sum_range_succ]
  rw [← h]
  exact exists_isAk_reset_ge_dev 5 2 (by norm_num) (by norm_num) (by norm_num)

end SinkReset
