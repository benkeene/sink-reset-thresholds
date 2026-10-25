/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import Mathlib
import SinkReset

/-!
# Sharp reset thresholds for bounded-response synchronization games with a sink: proofs of the statements of record

The definitions and statements of `Challenge.lean`, restated verbatim and proved. This module does not
import `Challenge`; the comparator checks that the statements and the definitions they use agree with
`Challenge.lean`. Restate the definitions of `Challenge.lean` above the theorems.
-/

@[expose] public section

namespace SinkReset

/-- `f k n = ∑_{i=1}^{n-1} ⌈i/k⌉`, the value the theorem gives for `M(n,k)`. For `k ≥ 1`,
`⌈i/k⌉ = (i + k - 1) / k` in natural-number division (Mathlib `Nat.ceilDiv_eq_add_pred_div`); the `i = 0`
term of `Finset.range n` is `0`, so the sum runs over `1 ≤ i ≤ n - 1`. -/
def f (k n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (i + k - 1) / k

/-- A letter is a transformation of the state set `Fin n`. -/
abbrev Letter (n : ℕ) := Fin n → Fin n

/-- The action of a word on a state: the letters of `w` act from left to right, `q · (a :: u) = (a q) · u`
(PROOF.md §0, right action, words act by composition). -/
def act {n : ℕ} (w : List (Letter n)) (q : Fin n) : Fin n := w.foldl (fun q a => a q) q

/-- An `n`-state automaton with sink `0`: an alphabet of letters, each fixing the sink (PROOF.md §0,
CLAIM.md "Definitions"). The alphabet is any set of transformations of `Fin n`; such a set is finite, so this
is an arbitrary finite alphabet. Letters are identified with the transformations they induce, which changes
neither the reset words nor the `k`-game. -/
structure Automaton (n : ℕ) [NeZero n] where
  /-- The alphabet. -/
  letters : Set (Letter n)
  /-- Every letter fixes the sink `0`. -/
  sink_fixed : ∀ a ∈ letters, a 0 = 0

/-- `w` is a word over the alphabet of `A`. -/
def Automaton.IsWord {n : ℕ} [NeZero n] (A : Automaton n) (w : List (Letter n)) : Prop :=
  ∀ a ∈ w, a ∈ A.letters

/-- `w` is a reset word of `A`: a word over its alphabet sending every state to the sink `0`. (With a sink,
`Q · w` is a singleton iff it is `{0}`, PROOF.md §0.) The reset threshold `rt` of the informal text is the least
length of a reset word; the statements of record speak of reset words and their lengths directly. -/
def Automaton.IsReset {n : ℕ} [NeZero n] (A : Automaton n) (w : List (Letter n)) : Prop :=
  A.IsWord w ∧ ∀ q, act w q = 0

/-- Alice wins the `k`-game of `A` from the position `S`, the set of states still in play (the image of the
state set under the history so far). Either `S` is already synchronized, `S ⊆ {0}`, or Alice has a letter `a`
of `A` such that for every reply `u` of Bob, a word over the alphabet of `A` of length `< k` (the empty word
included), she wins from `S · (a u)`. Alice moves first (PROOF.md Lemma 1(a): the order of the first move does
not matter). The positions are finitely many and Bob has finitely many replies, so this inductive predicate holds
at exactly the positions from which Alice has a strategy winning against every behaviour of Bob (the attractor
of a finite reachability game); a reset reached inside Bob's reply persists to its end because `0` is fixed.
See CORRESPONDENCE.md §3. -/
inductive Automaton.AliceWins {n : ℕ} [NeZero n] (A : Automaton n) (k : ℕ) : Finset (Fin n) → Prop
  | reset (S : Finset (Fin n)) (h : ∀ q ∈ S, q = 0) : A.AliceWins k S
  | step (S : Finset (Fin n)) (a : Letter n) (ha : a ∈ A.letters)
      (h : ∀ u : List (Letter n), A.IsWord u → u.length < k →
        A.AliceWins k (S.image (act (a :: u)))) : A.AliceWins k S

/-- `A` is an `A_k` automaton: Alice wins the `k`-game from the full state set (CLAIM.md "Definitions"). -/
def Automaton.IsAk {n : ℕ} [NeZero n] (A : Automaton n) (k : ℕ) : Prop :=
  A.AliceWins k Finset.univ

/-- Upper bound. Let k ≥ 1 and either k = 1 or n ≤ k + 3. Every n-state A_k automaton with sink 0 has a reset word of length at most f k n = ∑_{i=1}^{n-1} ⌈i/k⌉ (PROOF.md §5, Theorem, upper bound; Proposition 10). -/
theorem reset_word_le_of_isAk (n k : ℕ) [NeZero n] (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) (A : Automaton n) (hA : A.IsAk k) : ∃ w, A.IsReset w ∧ w.length ≤ f k n := by
  sorry

/-- Lower bound. Let n ≥ 2, k ≥ 1 and either k = 1 or n ≤ k + 3. Some n-state A_k automaton with sink 0 has no reset word shorter than f k n (PROOF.md §5, Theorem, lower bound; Lemmas 12, 13, 14). Together with the upper bound this says M(n,k) = f k n. -/
theorem exists_isAk_reset_ge (n k : ℕ) [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) : ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length := by
  sorry

/-- M(5,2) ≤ 6: every 5-state A_2 automaton with sink 0 has a reset word of length at most 6 (CLAIM.md headline; PROOF.md §5, the pair (5,2)). -/
theorem five_two_reset_word_le (A : Automaton 5) (hA : A.IsAk 2) : ∃ w, A.IsReset w ∧ w.length ≤ 6 := by
  sorry

/-- M(5,2) ≥ 6: some 5-state A_2 automaton with sink 0 has no reset word of length less than 6 (CLAIM.md headline; PROOF.md §4 Lemma 14, the automaton C_{2,2}). -/
theorem five_two_exists_isAk_reset_ge : ∃ A : Automaton 5, A.IsAk 2 ∧ ∀ w, A.IsReset w → 6 ≤ w.length := by
  sorry

end SinkReset
