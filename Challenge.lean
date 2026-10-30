/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene

Statements of record for the Palomar submission. Imports are Mathlib-only; every statement of record
ends in a deliberate `sorry` (the Comparator convention). Proofs are in `Solution.lean`, which does not
import this file.
-/
module

public import Mathlib

/-!
# Sharp reset thresholds for bounded-response synchronization games with a sink

Lipin and Volkov (Adversarial Synchronization, arXiv:2601.18362, §2.1) define the `k`-game on an automaton
with a sink: Alice plays a letter, Bob replies with any word of length `< k`, and Alice wins when the history is
a reset word. `A_k` automata are those Alice wins; `M(n,k)` is the largest reset threshold of an `n`-state `A_k`
automaton with sink over any finite alphabet. They prove `M(n,n-1) = n-1`, recall Rystsov's tight bound
`M(n,1) = n(n-1)/2`, exhibit automata `L^k_m` with reset threshold `f k n = ∑_{i=1}^{n-1} ⌈i/k⌉`, and
conjecture (§3.4) that `M(n,k) = (n-1+k)(n-1)/(2k)` whenever `k ∣ n-1`, where that expression equals `f k n`.
The ceiling-sum form `M(n,k) = f k n` for every `n, k` extends their conjecture to the non-divisible pairs; they
do not state it. Beyond the settled endpoints `k = 1` and `k = n-1`, the new content of `docs/PROOF.md` is
`M(k+2,k) = k+2` and `M(k+3,k) = k+4` for `k ≥ 2`, including the non-divisible pairs `(4,2)` and `(5,3)`;
`(5,2)` is the first pair with `k ∣ n-1` that is neither endpoint, so the first pair on which the
Lipin–Volkov conjecture itself was open; `(4,2)` is the first non-endpoint pair of all.

The statements of record render the theorem of `docs/PROOF.md` §5: `M(n,k) = f k n` whenever `k = 1` or
`n ≤ k + 3`, as a pair of bounds, plus the same pair for the headline case `M(5,2) = 6`:
* `SinkReset.reset_word_le_of_isAk`: every `n`-state `A_k` automaton with sink has a reset word of length
  `≤ f k n` (the upper bound, PROOF.md Proposition 10);
* `SinkReset.exists_isAk_reset_ge`: some `n`-state `A_k` automaton with sink has no reset word shorter than
  `f k n` (the lower bound, PROOF.md Lemmas 12–14);
* `SinkReset.five_two_reset_word_le`, `SinkReset.five_two_exists_isAk_reset_ge`: the two bounds for
  `n = 5`, `k = 2`, value `6`.

Conventions: states are `Fin n` with the sink `0` (so `[NeZero n]`); words act from the left letter
onwards; an automaton is any set of transformations fixing `0`; Alice's winning is the inductive predicate
`Automaton.AliceWins` (Alice moves first). Not formalized: `M(n,k)` itself as a supremum (the two bounds say
exactly that the supremum is attained and equals `f k n`), the Lipin–Volkov conjecture and its ceiling-sum
form beyond `k = 1` or `n ≤ k + 3`, and the computational record of PROOF.md Appendix A. CORRESPONDENCE.md
§3–§5 audit the definitions and the gaps.
The record section below is generated from `records.yaml` by `conductor package render`; its order is the
order of `comparator.json` and of `formalization.yaml` (`status.main_results`, `alignment.statements`).
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

-- conductor:records:begin (generated from records.yaml by `conductor package render`; edit records.yaml, not this region)

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

-- conductor:records:end

end SinkReset
