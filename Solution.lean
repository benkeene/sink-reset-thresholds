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
