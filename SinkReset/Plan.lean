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
def active {n : ℕ} [NeZero n] (S : Finset (Fin n)) : Finset (Fin n) := by sorry
-- Equation: ResetOn A S w = (A.IsWord w ∧ ∀ q ∈ S, act w q = 0).
def ResetOn {n : ℕ} [NeZero n] (A : Automaton n)
    (S : Finset (Fin n)) (w : List (Letter n)) : Prop :=
  by sorry
-- Equation: Within A S b = (∃ w, ResetOn A S w ∧ w.length ≤ b).
def Within {n : ℕ} [NeZero n] (A : Automaton n)
    (S : Finset (Fin n)) (b : ℕ) : Prop :=
  by sorry
-- Equation: SC A = (∀ p q, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q).
def SC {n : ℕ} [NeZero n] (A : Automaton n) : Prop :=
  by sorry
-- Equation: Z A = Finset.univ.filter (fun q => q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0).
noncomputable def Z {n : ℕ} [NeZero n] (A : Automaton n) : Finset (Fin n) := by sorry
-- Equation: Y A = active Finset.univ \ Z A.
noncomputable def Y {n : ℕ} [NeZero n] (A : Automaton n) : Finset (Fin n) :=
  by sorry
-- Equation: Distances A d = ∀ q,
--   (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
--   ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length.
def Distances {n : ℕ} [NeZero n] (A : Automaton n) (d : Fin n → ℕ) : Prop :=
  by sorry

section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)

-- PROOF 54-69.
theorem act_append (u v : List (Letter n)) (q : Fin n) :
    act (u ++ v) q = act v (act u q) := by sorry
theorem word_append (u v : List (Letter n)) :
    A.IsWord (u ++ v) ↔ A.IsWord u ∧ A.IsWord v := by sorry
theorem act_zero (w : List (Letter n)) (hw : A.IsWord w) :
    act w 0 = 0 := by sorry
theorem image_active_le (S : Finset (Fin n)) (w : List (Letter n))
    (hw : A.IsWord w) :
    (active (S.image (act w))).card ≤ (active S).card := by sorry
theorem kill_decreases (S : Finset (Fin n)) (q : Fin n) (hq : q ∈ active S)
    (w : List (Letter n)) (hw : A.IsWord w) (hkill : act w q = 0) :
    (active (S.image (act w))).card + 1 ≤ (active S).card := by sorry
theorem within_compose (S : Finset (Fin n)) (u : List (Letter n))
    (hu : A.IsWord u) (b : ℕ) (h : Within A (S.image (act u)) b) :
    Within A S (u.length + b) := by sorry
theorem within_univ (b : ℕ) :
    Within A Finset.univ b ↔ ∃ w, A.IsReset w ∧ w.length ≤ b := by sorry

-- PROOF 86-96; monotonicity also supplies the Bob-first equivalence.
theorem wins_mono {k : ℕ} {S T : Finset (Fin n)}
    (h : A.AliceWins k T) (hST : S ⊆ T) : A.AliceWins k S := by sorry
theorem wins_word {k : ℕ} (hk : 1 ≤ k) {S : Finset (Fin n)}
    (h : A.AliceWins k S) : ∃ w, ResetOn A S w := by sorry
theorem one_game_iff : A.IsAk 1 ↔ ∃ w, A.IsReset w := by sorry
theorem bob_first_iff {k : ℕ} (hk : 1 ≤ k) :
    A.IsAk k ↔ ∀ u, A.IsWord u → u.length < k →
      A.AliceWins k (Finset.univ.image (act u)) := by sorry

-- PROOF 154-159, 177-180, 319-324: induction on AliceWins.
theorem trap {k : ℕ} (T : Finset (Fin n)) (hne : T.Nonempty) (hzero : 0 ∉ T)
    (hreply : ∀ t ∈ T, ∀ a ∈ A.letters, ∃ u,
      A.IsWord u ∧ u.length < k ∧ act (a :: u) t ∈ T) :
    ¬ A.IsAk k := by sorry

-- PROOF 295-317: well-founded formulation of the finite progress argument.
theorem wins_of_rank {k : ℕ} (rank : Finset (Fin n) → ℕ)
    (hstep : ∀ S, (active S).Nonempty → ∃ a ∈ A.letters,
      ∀ u, A.IsWord u → u.length < k →
        rank (S.image (act (a :: u))) < rank S) :
    ∀ S, A.AliceWins k S := by sorry

-- PROOF 88, 98-107, 161-169, 182-185.
theorem distances_exist (h : ∃ w, A.IsReset w) :
    ∃ d, Distances A d := by sorry
theorem reachable_reset
    (h : ∀ q, ∃ w, A.IsWord w ∧ act w q = 0) (S : Finset (Fin n)) :
    ∃ w, ResetOn A S w := by sorry
theorem distance_facts {d : Fin n → ℕ} (hd : Distances A d) :
    d 0 = 0 ∧
    (∀ q, (d q = 1 ↔ q ∈ Z A) ∧ (q ∈ Y A ↔ 2 ≤ d q)) ∧
    (∀ q a, a ∈ A.letters → d q ≤ d (a q) + 1) := by sorry
theorem distance_Y {d : Fin n → ℕ} (hd : Distances A d) :
    (∀ q, d q ≤ (Y A).card + 1) ∧
    ((Y A).Nonempty → ∃ y ∈ Y A, d y = 2) := by sorry
theorem short_kill (h : ∃ w, A.IsReset w) (S : Finset (Fin n))
    (hne : (active S).Nonempty) :
    ∃ q ∈ active S, ∃ w, A.IsWord w ∧ act w q = 0 ∧
      w.length ≤ n - (active S).card := by sorry
theorem classical_bound (h : ∃ w, A.IsReset w) (S : Finset (Fin n)) :
    Within A S (∑ j ∈ Finset.range (active S).card, (n - (j + 1))) := by sorry
end Basic

-- PROOF 119-131: lifting is needed because transformed alphabets can identify letters.
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
theorem lift_word
    (hletters : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τ a = b) (v : List (Letter m)) (hv : B.IsWord v) :
    ∃ u, A.IsWord u ∧ u.map τ = v ∧ u.length = v.length := by sorry
theorem wins_push
    (hletters : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τ a = b) (φ : Fin n → Fin m) (hzero : φ 0 = 0)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (a q) = τ a (φ q))
    {k : ℕ} {S : Finset (Fin n)} (h : A.AliceWins k S) :
    B.AliceWins k (S.image φ) := by sorry
theorem wins_pull
    (hletters : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τ a = b) (φ : Fin m → Fin n) (hzero : ∀ q, φ q = 0 ↔ q = 0)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (τ a q) = a (φ q))
    {k : ℕ} (S : Finset (Fin m)) (h : A.AliceWins k (S.image φ)) :
    B.AliceWins k S := by sorry
end Transport

-- PROOF 114-117: forward reachability replaces source SCC selection.
theorem closed_set_of_not_sc {n : ℕ} [NeZero n] (A : Automaton n) (h : ¬ SC A) :
    ∃ R : Finset (Fin n), 0 ∈ R ∧ 2 ≤ R.card ∧ R.card < n ∧
      ∀ a ∈ A.letters, ∀ q ∈ R, a q ∈ R := by sorry

-- PROOF 109-135, strengthened to every proper closed R of size at least two.
theorem closed_reduction {n k : ℕ} [NeZero n] (A : Automaton n) (hk : 1 ≤ k)
    (hA : A.IsAk k) (R : Finset (Fin n)) (hz : 0 ∈ R)
    (hcard : 2 ≤ R.card) (hproper : R.card < n)
    (hclosed : ∀ a ∈ A.letters, ∀ q ∈ R, a q ∈ R) :
    ∃ c d : ℕ, 1 ≤ c ∧ 1 ≤ d ∧ c + d + 1 = n ∧
      d + 1 = R.card ∧
      ∃ B : Automaton (c + 1), ∃ C : Automaton (d + 1),
        B.IsAk k ∧ C.IsAk k ∧
        ∀ u v, B.IsReset u → C.IsReset v →
          ∃ w, A.IsReset w ∧ w.length = u.length + v.length := by sorry

-- PROOF 40, 137-140, 232-234, 326-328.
theorem f_one (n : ℕ) : f 1 n = n * (n - 1) / 2 := by sorry
theorem f_small {k n : ℕ} (hk : 1 ≤ k) (hn : n ≤ k + 1) :
    f k n = n - 1 := by sorry
theorem f_cycle {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k) :
    f k (k + m + 1) = k + 2 * m := by sorry
theorem f_split {k c d : ℕ} (hk : 1 ≤ k) :
    f k (c + 1) + f k (d + 1) ≤ f k (c + d + 1) := by sorry

section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)

-- PROOF 149-152.
theorem escape_to_Y (hsc : SC A) (hne : (Y A).Nonempty) (x : Fin n)
    (hx : x ∈ Z A) :
    ∃ w, A.IsWord w ∧ w.length ≤ (Z A).card ∧ act w x ∈ Y A := by sorry
-- PROOF 146-159.
theorem few_bad (hk : 1 ≤ k) (hA : A.IsAk k) (hsc : SC A) :
    ((Y A).Nonempty → k ≤ (Z A).card) ∧ (Y A).card ≤ n - 1 - k := by sorry
-- PROOF 171-180.
theorem no_return (hk : 2 ≤ k) (hA : A.IsAk k) {d : Fin n → ℕ}
    (hd : Distances A d) (y₁ y₂ : Fin n) (hY : Y A = {y₁, y₂})
    (h₁ : d y₁ = 2) (h₂ : d y₂ = 3) :
    (∀ a ∈ A.letters, a y₂ = y₁ ∨ a y₂ = y₂) ∧
    (∃ c ∈ A.letters, c y₂ = y₁) ∧
    (∀ a ∈ A.letters, a y₁ ≠ y₂) := by sorry
-- PROOF 182-193; additive formulation avoids a reset-threshold maximum.
theorem greedy (b : ℕ) (hb : n - 1 ≤ b)
    (hY : ∀ T : Finset (Fin n), T.Nonempty → T ⊆ Y A →
      ∃ w, ResetOn A T w ∧ w.length + (n - 1 - T.card) ≤ b) :
    Within A Finset.univ b := by sorry
-- PROOF 214-227.
theorem two_bad (hk : 2 ≤ k) (hA : A.IsAk k) (hcard : (Y A).card ≤ 2)
    (T : Finset (Fin n)) (hT : T ⊆ Y A) (hsize : T.card = 2) :
    Within A T 4 := by sorry
-- PROOF 199-227, with f evaluated by f_small and f_cycle.
theorem sc_upper (hk : 2 ≤ k) (hA : A.IsAk k) (hsc : SC A)
    (hn : n ≤ k + 3) : Within A Finset.univ (f k n) := by sorry
-- PROOF 229-238, 351-353.
theorem upper (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) (hA : A.IsAk k) :
    Within A Finset.univ (f k n) := by sorry
end Upper

-- PROOF 250-255. The sink has weight zero; sums count distinct image states.
-- Equation: potential weight S = ∑ q ∈ S, weight q.
def potential {n : ℕ} (weight : Fin n → ℕ) (S : Finset (Fin n)) : ℕ :=
  by sorry
theorem potential_bound {n : ℕ} [NeZero n] (A : Automaton n)
    (weight : Fin n → ℕ) (hzero : weight 0 = 0)
    (hstep : ∀ a ∈ A.letters, ∀ S : Finset (Fin n),
      potential weight S ≤ potential weight (S.image a) + 1)
    (w : List (Letter n)) (hw : A.IsReset w) :
    potential weight Finset.univ ≤ w.length := by sorry

-- PROOF 257-267.
-- Equation: kill i q = if q = i then 0 else q.
def kill {n : ℕ} [NeZero n] (i : Fin n) : Letter n :=
  by sorry
-- Alphabet: {kill (1 : Fin n)} ∪ {a | ∃ i j : Fin n,
--   1 ≤ i.val ∧ j.val = i.val + 1 ∧ a = (Equiv.swap i j : Fin n → Fin n)}.
def transposition (n : ℕ) [NeZero n] : Automaton n := by sorry
theorem transposition_step {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (a : Letter n) (ha : a ∈ (transposition n).letters) (S : Finset (Fin n)) :
    potential Fin.val S ≤ potential Fin.val (S.image a) + 1 := by sorry
theorem sum_values (n : ℕ) :
    potential Fin.val (Finset.univ : Finset (Fin n)) = n * (n - 1) / 2 := by sorry
theorem transposition_reset {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ∃ w, (transposition n).IsReset w ∧ w.length = n * (n - 1) / 2 := by sorry
theorem transposition_sharp {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (transposition n).IsAk 1 ∧
    ∀ w, (transposition n).IsReset w → f 1 n ≤ w.length := by sorry

-- PROOF 269-273.
-- Value equation: (predecessor n q).val = q.val - 1.
def predecessor (n : ℕ) : Letter n :=
  by sorry
-- Alphabet: {predecessor n}.
def path (n : ℕ) [NeZero n] : Automaton n := by sorry
theorem path_action {n : ℕ} [NeZero n] (w : List (Letter n))
    (hw : (path n).IsWord w) (q : Fin n) :
    (act w q).val = q.val - w.length := by sorry
theorem path_sharp {n k : ℕ} [NeZero n] (hk : 1 ≤ k) :
    (path n).IsAk k ∧
    (∃ w, (path n).IsReset w ∧ w.length = n - 1) ∧
    ∀ w, (path n).IsReset w → n - 1 ≤ w.length := by sorry

-- PROOF 275-278: positive state i+1 represents c_i.
-- Equation: shift k m q = if hq : q = 0 then 0 else
--   ⟨q.val % (k + m) + 1, proof using hq and q.isLt⟩.
def shift (k m : ℕ) : Letter (k + m + 1) :=
  by sorry
-- Alphabet: {shift k m} ∪ {a | ∃ i : Fin (k + m + 1),
--   2 ≤ i.val ∧ i.val ≤ k + 1 ∧ a = kill i}.
def cycle (k m : ℕ) : Automaton (k + m + 1) := by sorry
-- PROOF 283-286.
-- Equation: if q = 0 then 0 else if 2 ≤ q.val ∧ q.val ≤ k + 1 then 1 else 2.
def cycleWeight (k m : ℕ) (q : Fin (k + m + 1)) : ℕ :=
  by sorry
theorem cycle_step {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (a : Letter (k + m + 1)) (ha : a ∈ (cycle k m).letters)
    (S : Finset (Fin (k + m + 1))) :
    potential (cycleWeight k m) S ≤ potential (cycleWeight k m) (S.image a) + 1 := by sorry
theorem cycle_sum {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    potential (cycleWeight k m) Finset.univ = k + 2 * m := by sorry
-- PROOF 288-293.
theorem cycle_reset {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∃ w, (cycle k m).IsReset w ∧ w.length = k + 2 * m := by sorry

-- PROOF 302-311: zero on K and sink; delta on O.
-- Equation: if q.val = 1 then 1 else if k + 1 < q.val then k + m + 2 - q.val else 0.
def cycleDelta (k m : ℕ) (q : Fin (k + m + 1)) : ℕ :=
  by sorry
-- Equation: delay k m S = sInf {r : ℕ | ∃ q ∈ active S, cycleDelta k m q = r}.
noncomputable def delay (k m : ℕ) (S : Finset (Fin (k + m + 1))) : ℕ :=
  by sorry
-- Equation: cycleRank k m S = (m + 1) * (active S).card + delay k m S.
noncomputable def cycleRank (k m : ℕ) (S : Finset (Fin (k + m + 1))) : ℕ :=
  by sorry
theorem delay_spec {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (S : Finset (Fin (k + m + 1))) :
    delay k m S ≤ m ∧
    ((active S).Nonempty → ∃ q ∈ active S, cycleDelta k m q = delay k m S) ∧
    (∀ q ∈ active S, delay k m S ≤ cycleDelta k m q) := by sorry
-- PROOF 295-317: strict decrease compresses the bounded-round argument.
theorem cycle_rank_step {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (S : Finset (Fin (k + m + 1))) (hne : (active S).Nonempty) :
    ∃ a ∈ (cycle k m).letters, ∀ u, (cycle k m).IsWord u → u.length < k →
      cycleRank k m (S.image (act (a :: u))) < cycleRank k m S := by sorry
theorem cycle_wins {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (cycle k m).IsAk k := by sorry
-- PROOF 319-324.
theorem cycle_loses {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ¬ (cycle k m).IsAk (k + 1) := by sorry
-- PROOF 275-328: full construction theorem, including m > k.
theorem cycle_sharp {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (cycle k m).IsAk k ∧
    (∃ w, (cycle k m).IsReset w ∧ w.length = k + 2 * m) ∧
    (∀ w, (cycle k m).IsReset w → k + 2 * m ≤ w.length) ∧
    ¬ (cycle k m).IsAk (k + 1) := by sorry

-- PROOF 330-332, 355-363: stronger lower range than the record.
theorem lower {n k : ℕ} [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hnk : k = 1 ∨ n ≤ 2 * k + 1) :
    ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length := by sorry

end Plan

-- PROOF 229-238, 341-368. Exact statement signatures from Challenge.lean, under `_dev` names.
theorem reset_word_le_of_isAk_dev (n k : ℕ) [NeZero n] (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) (A : Automaton n) (hA : A.IsAk k) : ∃ w, A.IsReset w ∧ w.length ≤ f k n := by
  sorry

theorem exists_isAk_reset_ge_dev (n k : ℕ) [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) : ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length := by
  sorry

theorem five_two_reset_word_le_dev (A : Automaton 5) (hA : A.IsAk 2) : ∃ w, A.IsReset w ∧ w.length ≤ 6 := by
  sorry

theorem five_two_exists_isAk_reset_ge_dev : ∃ A : Automaton 5, A.IsAk 2 ∧ ∀ w, A.IsReset w → 6 ≤ w.length := by
  sorry

end SinkReset
