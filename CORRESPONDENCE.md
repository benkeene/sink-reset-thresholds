# Correspondence: informal statements ↔ formal statements

Status (2026-10-29): the four statements of record are proved; the lab packet claim_0001 is FORMALLY_VERIFIED
(approved 2026-10-26 at commit 1eed040421fe after Ben Keene read this file, gate rule F10). Each is stated in `Challenge.lean` (record
bodies deliberately `sorry`, checked against `Solution.lean` by the comparator) and proved in `Solution.lean` by
one term naming its `_dev` copy in `SinkReset/Plan.lean`, whose development was written in the P-formalize run
`2026-10-25_formalize-sinkresetthresholds` (§7 says by whom, declaration by declaration). Every check that ran is
a row of §8, each naming the commit it ran at; the Lean sources, lakefile, toolchain, manifest, comparator,
`records.yaml` and `conductor.toml` have not changed since commit 1f2b0df9da90 except the module docstring of
`Challenge.lean` (commit d041020a04af; the §8 rows quoting `git diff --stat` show the empty diff up to 1eed040421fe
and the docstring-only diff after it), so a row at any later commit covers these sources. Nothing in this file
may describe a build, count or check except by quoting the command and its output.

## 1. Informal statements and status

Lab claim `claim_0001`, status at the start of run `2026-10-25_formalize-sinkresetthresholds`: VERIFIED.

- `SinkReset.reset_word_le_of_isAk` (record, PROOF.md §5 Theorem (upper bound), §3 Proposition 10): Upper bound. Let k ≥ 1 and either k = 1 or n ≤ k + 3. Every n-state A_k automaton with sink 0 has a reset word of length at most f k n = ∑_{i=1}^{n-1} ⌈i/k⌉ (PROOF.md §5, Theorem, upper bound; Proposition 10).
- `SinkReset.exists_isAk_reset_ge` (record, PROOF.md §5 Theorem (lower bound), §4 Lemmas 12-14): Lower bound. Let n ≥ 2, k ≥ 1 and either k = 1 or n ≤ k + 3. Some n-state A_k automaton with sink 0 has no reset word shorter than f k n (PROOF.md §5, Theorem, lower bound; Lemmas 12, 13, 14). Together with the upper bound this says M(n,k) = f k n.
- `SinkReset.five_two_reset_word_le` (record, PROOF.md §5 Theorem, the nine pairs, (5,2)): M(5,2) ≤ 6: every 5-state A_2 automaton with sink 0 has a reset word of length at most 6 (CLAIM.md headline; PROOF.md §5, the pair (5,2)).
- `SinkReset.five_two_exists_isAk_reset_ge` (record, PROOF.md §4 Lemma 14 (C_{2,2}), §5 Theorem): M(5,2) ≥ 6: some 5-state A_2 automaton with sink 0 has no reset word of length less than 6 (CLAIM.md headline; PROOF.md §4 Lemma 14, the automaton C_{2,2}).

## 2. Statements of record

The statements of record are listed, in order, in `records.yaml`; `Challenge.lean` (record section),
`comparator.json` and `formalization.yaml` are rendered from it by `conductor package render`, and
`conductor package check` fails on any drift among them.

### SinkReset.reset_word_le_of_isAk (record)

Informal (PROOF.md §5 Theorem (upper bound), §3 Proposition 10): Upper bound. Let k ≥ 1 and either k = 1 or n ≤ k + 3. Every n-state A_k automaton with sink 0 has a reset word of length at most f k n = ∑_{i=1}^{n-1} ⌈i/k⌉ (PROOF.md §5, Theorem, upper bound; Proposition 10).

Lean statement (Challenge.lean):

```lean
theorem reset_word_le_of_isAk (n k : ℕ) [NeZero n] (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) (A : Automaton n) (hA : A.IsAk k) : ∃ w, A.IsReset w ∧ w.length ≤ f k n
```

Proved in Solution.lean from: `SinkReset.reset_word_le_of_isAk_dev`

Informal ↔ formal argument: `[NeZero n]` is `n ≥ 1` and supplies the sink `0 : Fin n`; `hk : 1 ≤ k` and `hnk : k = 1 ∨ n ≤ k + 3` are the Theorem's hypotheses verbatim (PROOF.md §5: "k ≥ 1", "if k = 1, or n ≤ k + 3"); `A : Automaton n` with `hA : A.IsAk k` is "A is an n-state A_k automaton with sink" (§3); the conclusion `∃ w, A.IsReset w ∧ w.length ≤ f k n` is "rt(A) ≤ f_k(n)", a reset word of length at most f_k(n), with `f k n = ∑_{i=1}^{n-1} ⌈i/k⌉` by §3. The case `n = 1`, which PROOF.md does not state, is harmless: `f k 1 = 0` and the empty word is a reset word. Solution.lean proves it by the term `reset_word_le_of_isAk_dev n k hk hnk A hA`; that `_dev` theorem is `Plan.upper` (SinkReset/Plan.lean:1184, Proposition 10), which follows PROOF.md §3: the reduction to the strongly connected case (`Plan.closed_reduction`, Lemma 3), the strongly connected case itself (`Plan.sc_upper` with `Plan.two_bad`, Proposition 9, which uses Lemmas 5–8) and the classical bound for `k = 1` (`Plan.classical_bound`, Lemma 2). Its axioms are quoted in the §8 row "per-record axioms".

### SinkReset.exists_isAk_reset_ge (record)

Informal (PROOF.md §5 Theorem (lower bound), §4 Lemmas 12-14): Lower bound. Let n ≥ 2, k ≥ 1 and either k = 1 or n ≤ k + 3. Some n-state A_k automaton with sink 0 has no reset word shorter than f k n (PROOF.md §5, Theorem, lower bound; Lemmas 12, 13, 14). Together with the upper bound this says M(n,k) = f k n.

Lean statement (Challenge.lean):

```lean
theorem exists_isAk_reset_ge (n k : ℕ) [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) : ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length
```

Proved in Solution.lean from: `SinkReset.exists_isAk_reset_ge_dev`

Informal ↔ formal argument: `hn : 2 ≤ n` is the Theorem's `n ≥ 2`, `hk` and `hnk` as above; the conclusion `∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length` is "some n-state A_k automaton with sink has no reset word shorter than f_k(n)", i.e. rt(A) ≥ f_k(n). It is not vacuous: `Plan.wins_word` (Plan.lean:129, needs `1 ≤ k`) produces a reset word from `IsAk k`, and with the upper record the witness has rt(A) = f_k(n), so the supremum M(n,k) is attained. Solution.lean proves it by `exists_isAk_reset_ge_dev n k hn hk hnk`, which is `Plan.lower` (Plan.lean:2113) specialised (`omega` turns `k = 1 ∨ n ≤ k + 3` into its hypothesis `k = 1 ∨ n ≤ 2 * k + 1`, so the development proves the lower bound on a wider range than the record). The witnesses are PROOF.md §4's: the transposition automaton for `k = 1` (`Plan.transposition_sharp`, Lemma 12), the path automaton for `n ≤ k + 1` (`Plan.path_sharp`, Lemma 13) and the cycle automata C_{k,m} (`Plan.cycle_sharp`, Lemma 14, through the potential bound `Plan.potential_bound`, Lemma 11), with `f` evaluated by `Plan.f_cycle`, `Plan.f_split` (Lemma 4) and `Plan.f_one`.

### SinkReset.five_two_reset_word_le (record)

Informal (PROOF.md §5 Theorem, the nine pairs, (5,2)): M(5,2) ≤ 6: every 5-state A_2 automaton with sink 0 has a reset word of length at most 6 (CLAIM.md headline; PROOF.md §5, the pair (5,2)).

Lean statement (Challenge.lean):

```lean
theorem five_two_reset_word_le (A : Automaton 5) (hA : A.IsAk 2) : ∃ w, A.IsReset w ∧ w.length ≤ 6
```

Proved in Solution.lean from: `SinkReset.five_two_reset_word_le_dev`

Informal ↔ formal argument: the `(5,2)` instance of the upper record: `A : Automaton 5` with `hA : A.IsAk 2` is a 5-state A_2 automaton with sink, and a reset word of length `≤ 6` is rt(A) ≤ 6 = f_2(5) (CLAIM.md headline M(5,2) ≤ 6; PROOF.md §5, the pair (5,2)). Solution.lean proves it by `five_two_reset_word_le_dev A hA`, which applies `reset_word_le_of_isAk_dev 5 2` and rewrites `f 2 5 = 6` by `norm_num [f, Finset.sum_range_succ]`.

### SinkReset.five_two_exists_isAk_reset_ge (record)

Informal (PROOF.md §4 Lemma 14 (C_{2,2}), §5 Theorem): M(5,2) ≥ 6: some 5-state A_2 automaton with sink 0 has no reset word of length less than 6 (CLAIM.md headline; PROOF.md §4 Lemma 14, the automaton C_{2,2}).

Lean statement (Challenge.lean):

```lean
theorem five_two_exists_isAk_reset_ge : ∃ A : Automaton 5, A.IsAk 2 ∧ ∀ w, A.IsReset w → 6 ≤ w.length
```

Proved in Solution.lean from: `SinkReset.five_two_exists_isAk_reset_ge_dev`

Informal ↔ formal argument: the `(5,2)` instance of the lower record: a 5-state A_2 automaton with sink none of whose reset words is shorter than `6` (CLAIM.md headline M(5,2) ≥ 6; PROOF.md §4 Lemma 14 and §5, the cycle automaton C_{2,2}, which has `2 + 2 + 1 = 5` states). Solution.lean proves it by `five_two_exists_isAk_reset_ge_dev`, which applies `exists_isAk_reset_ge_dev 5 2` and rewrites `f 2 5 = 6` as above.

## 3. Definition audit

- `f k n = ∑ i ∈ Finset.range n, (i + k - 1) / k`. For `k ≥ 1`, `(i + k - 1) / k = ⌈i/k⌉` (Mathlib
  `Nat.ceilDiv_eq_add_pred_div`), and the `i = 0` term is `0`, so `f k n = ∑_{i=1}^{n-1} ⌈i/k⌉ = f_k(n)` of PROOF.md.
  Checked by `decide` for the nine pairs during packaging (`f 2 5 = 6`, `f 1 5 = 10`, `f 3 5 = 5`, `f 2 4 = 4`,
  `f 4 5 = 4`, `f 3 4 = 3`); for `k = 0` the value is meaningless and excluded by the hypothesis `1 ≤ k`.
- `Letter n := Fin n → Fin n`; `act w q` folds the letters of `w` over `q` from the left. PROOF.md §0 writes the right
  action `q · a` and `q · (uv) = (q · u) · v`; `act (u ++ v) q = act v (act u q)` by `List.foldl_append`.
- `Automaton n` (with `[NeZero n]` so that `0 : Fin n` exists): `letters : Set (Letter n)` and `sink_fixed`. PROOF.md
  §0 and CLAIM.md take "a finite alphabet of letters, each a transformation of Q fixing 0". Any set of
  transformations of `Fin n` is finite, so no finiteness hypothesis is lost; distinct letters with the same
  transformation are identified, which changes neither reset words (only the transformation acts) nor the game
  (Alice's and Bob's choices are the same transformations). The states are `Fin n`, the sink is `0`, as in §0.
- `IsWord`, `IsReset`: a reset word is a word over the alphabet with `act w q = 0` for every `q`. PROOF.md §0: `w` is a
  reset word iff `Q · w = {0}` iff `q · w = 0` for all `q` (since `0 · w = 0`). The reset threshold `rt(A)` is not
  defined as a number; "`rt(A) ≤ m`" is "there is a reset word of length `≤ m`" and "`rt(A) ≥ m`" is "every reset
  word has length `≥ m`", which is how the statements of record use it (so the value `∞` for non-synchronizing
  automata never arises).
- `AliceWins A k S` (inductive). Position `S` is the image of the state set under the history. Constructor `reset`:
  `S ⊆ {0}`, i.e. the history is a reset word (`0 ∈ Q · h` always, PROOF.md §0, so `Q · h = {0}` iff `Q · h ⊆ {0}`).
  Constructor `step`: Alice plays a letter `a` of the alphabet, and for every reply `u` of Bob, a word over the
  alphabet with `u.length < k` (the empty word included, as in CLAIM.md), Alice wins from `S.image (act (a :: u))`,
  the image of `S` under `a u`. Why this is "Alice has a winning strategy": the game has finitely many positions
  (subsets of `Fin n`) and finitely many moves at each (letters, replies of bounded length over a finite alphabet),
  and Alice's goal is to reach a position `⊆ {0}`. In such a reachability game the positions from which Alice has
  a strategy winning against every behaviour of Bob are exactly the least fixed point of "already at the goal, or
  some Alice move after which every Bob reply leads to a winning position", which is this inductive predicate
  (a winning strategy wins within a bounded number of rounds by König's lemma, and the attractor closes it). Two
  simplifications are faithful: Alice moves first (PROOF.md Lemma 1(a) proves the order of the first move is
  irrelevant); and only end-of-round positions are inspected, which is harmless because a reset word followed by
  any word is a reset word (`0` is fixed), so a reset inside Bob's reply is still a reset at its end.
- `IsAk A k := AliceWins A k Finset.univ`: Alice wins from the full state set, the start of the game.

Why `AliceWins` is "Alice has a winning strategy", in both directions (this argument is prose, not a Lean theorem;
§5 lists it as a gap). (⇒) A derivation of `AliceWins k S` is a strategy: at a `step` node Alice plays its letter
`a`; every reply `u` of Bob (any word over the alphabet with `u.length < k`, the empty word included) leads to the
position `S.image (act (a :: u))`, which the derivation covers. Derivations are well-founded, so every play reaches a
`reset` node, a position `⊆ {0}`, i.e. the history is a reset word. A reset reached inside Bob's reply persists to
its end, because `0` is fixed by every letter. (⇐) Suppose Alice has a history-dependent strategy that wins from `S`
but `¬ AliceWins k S`. Then `S ⊄ {0}`, and for the strategy's first letter `a` the negated `step` constructor gives a
legal reply `u` with `¬ AliceWins k (S.image (act (a :: u)))`; the residual strategy wins from that position, since
the rest of the play depends only on the current image. Iterating (dependent choice) builds an infinite play
consistent with the strategy that never reaches a position `⊆ {0}`, contradicting that the strategy wins. Alice
moving first is PROOF.md Lemma 1(a). Two boundary facts: `IsAk 0` holds for the automaton whose only letter is the
identity, although nothing resets it (with `k = 0` Bob has no reply and `AliceWins 0` is reached from any position
in one step), which is why every record assumes `1 ≤ k`; and from a position not containing `0` Alice can only win
by resetting, which never arises in the records since every position reached from `univ` contains `0`.

## 4. Hypotheses and conventions

- `[NeZero n]` on every statement (and on `Automaton n`): `n ≠ 0`, so the sink `0 : Fin n` exists. For `n = 1` the
  upper bound is trivial (the empty word is a reset word; `f k 1 = 0`) and the lower bound is stated only for
  `2 ≤ n`, as in the Theorem (`n ≥ 2`).
- `1 ≤ k`: PROOF.md assumes `k ≥ 1`. With `k = 0` Bob has no replies, `f 0 n = 0` (natural division by `0`) and
  `IsAk 0` holds for automata that nothing resets (§3), so the upper record would be false; `hk` is necessary as
  well as faithful.
- `k = 1 ∨ n ≤ k + 3`: the Theorem's hypothesis verbatim ("If `k = 1`, or `n ≤ k + 3`"); no relation between `n`
  and `k` is assumed otherwise (so `k ≥ n` is allowed, where `f k n = n - 1`).
- Natural subtraction appears once, in `i + k - 1`; with `k ≥ 1` it is exact. `Finset.range n = {0, …, n-1}` matches
  the sum `∑_{i=1}^{n-1}` because the `i = 0` term vanishes.
- States are indexed `0, …, n-1` as in PROOF.md §0, the sink being `0`. Words are `List (Letter n)`, lengths are
  `List.length`, and `act` applies the first letter first.
- Universes: everything is in `Type` (`Fin n`, functions, lists, finsets); no universe variables.
- The headline statements use the numerals `5`, `2`, `6` directly (`Automaton 5`, `IsAk 2`, length `6`), with
  `NeZero 5` found by instance search.
- `hn : 2 ≤ n` appears on the lower record only, as in the Theorem; the upper record also covers `n = 1` (§2).

## 5. Formalized scope and gaps

Formalized and proved (§8 rows): the Theorem of PROOF.md §5 in its full hypothesis `k = 1 ∨ n ≤ k + 3`, as an
upper and a lower bound, and its instance `(5,2)`. The development proves more than the records: `Plan.lower`
(Plan.lean:2113) gives the lower bound for `k = 1 ∨ n ≤ 2 * k + 1`, and `Plan.cycle_sharp` (Plan.lean:1821) holds
for every `k, m ≥ 1`; nothing extends the upper bound beyond `n ≤ k + 3` (PROOF.md Remark 2).

Informal only: `M(n,k)` as a supremum (the two records say the supremum is attained and equals `f k n`); the
equivalence of the Alice-first and Bob-first games (Lemma 1(a)), which the definition builds in; the argument that
the inductive `AliceWins` is "Alice has a winning strategy" (§3, prose in both directions, not a Lean theorem);
Remarks 1–3 of §5; the `n = k + 4` result of the independent prover's transcript, which is not part of the claim.

Excluded: PROOF.md Appendix A (the computational record; corroboration only, never a premise) and Appendix B
(packet errata, applied to `docs/CLAIM.md`, `docs/CONTEXT.md` and `docs/COMPUTATION.md` in this repository, the
packet files untouched); the Lipin–Volkov conjecture beyond the proved range.

Attribution. Lipin–Volkov (arXiv:2601.18362 §3.4) conjecture `M(n,k) = (n-1+k)(n-1)/(2k)` only when `k ∣ n-1`;
on that domain this equals `f k n`. The records settle the conjecture's cases with `k ∣ n-1` and (`k = 1` or
`n ≤ k + 3`), and the stronger ceiling-sum form `M(n,k) = f k n`, which Lipin–Volkov exhibit as a lower bound but do
not conjecture, for every `k = 1` or `n ≤ k + 3` (for instance `(4,2)`, where `2 ∤ 3`). The module docstring of
`Challenge.lean` stated the attribution without this restriction until commit d041020a04af, which corrects it and
names the new pairs (docstring only; §8 quotes the diff). Gate rule F4 pins the Challenge hash, so that commit needs
the follow-up formalize judgment that re-pins it. No statement of record, definition or proof is affected.

## 6. Toolchain

`lean-toolchain`: `leanprover/lean4:v4.35.0-rc3`; Mathlib `v4.35.0-rc3 (c55e6e786f49471c72fbddbec5415808896aec1e)`. Never commit `.lake`.

## 7. Provenance

Per declaration closed in run `2026-10-25_formalize-sinkresetthresholds`: the model that wrote its proof, the job id, the round and the
commit, from run.json (`conductor formalize correspondence`); edit the run, not this table.

<!-- conductor:provenance:begin -->
| declaration | model | job id | round | commit |
|---|---|---|---|---|
| `SinkReset.Plan.active` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.ResetOn` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.Within` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.SC` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.Z` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.Y` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.Distances` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.act_append` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.word_append` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.act_zero` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.image_active_le` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.kill_decreases` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.within_compose` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.within_univ` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.wins_mono` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.wins_word` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.one_game_iff` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.bob_first_iff` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.trap` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.wins_of_rank` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.distances_exist` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.reachable_reset` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.distance_facts` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.distance_Y` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.short_kill` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.classical_bound` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.lift_word` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.wins_push` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.wins_pull` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.closed_set_of_not_sc` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.closed_reduction` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.f_one` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.f_small` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.f_cycle` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.f_split` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.escape_to_Y` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.few_bad` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.no_return` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.greedy` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.two_bad` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.sc_upper` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.upper` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.potential` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.potential_bound` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.kill` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.transposition` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.transposition_step` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.sum_values` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.transposition_reset` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.transposition_sharp` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.predecessor` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.path` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.path_action` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.path_sharp` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.shift` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.cycle` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.cycleWeight` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.cycle_step` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.cycle_sum` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.cycle_reset` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.cycleDelta` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.delay` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.cycleRank` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.delay_spec` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.cycle_rank_step` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.cycle_wins` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.cycle_loses` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.cycle_sharp` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.lower` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.reset_word_le_of_isAk_dev` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.exists_isAk_reset_ge_dev` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.five_two_reset_word_le_dev` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.five_two_exists_isAk_reset_ge_dev` | operator (human session; no model; see the note below) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.reset_word_le_of_isAk` (statement of record; Solution.lean bridge) | plan materialization (see plan/plan_map.json) | sinkresetthresholds/20261025T083649_planner-planner-claim-0001, plan-materialize-1, plan-materialize-3, plan-materialize-4 | — | e623d0fcef39 |
| `SinkReset.exists_isAk_reset_ge` (statement of record; Solution.lean bridge) | plan materialization (see plan/plan_map.json) | sinkresetthresholds/20261025T083649_planner-planner-claim-0001, plan-materialize-1, plan-materialize-3, plan-materialize-4 | — | e623d0fcef39 |
| `SinkReset.five_two_reset_word_le` (statement of record; Solution.lean bridge) | plan materialization (see plan/plan_map.json) | sinkresetthresholds/20261025T083649_planner-planner-claim-0001, plan-materialize-1, plan-materialize-3, plan-materialize-4 | — | e623d0fcef39 |
| `SinkReset.five_two_exists_isAk_reset_ge` (statement of record; Solution.lean bridge) | plan materialization (see plan/plan_map.json) | sinkresetthresholds/20261025T083649_planner-planner-claim-0001, plan-materialize-1, plan-materialize-3, plan-materialize-4 | — | e623d0fcef39 |

Human sessions (commits made by hand on a stream worktree, judged like a session):
- `human-A-r1-h1` (3f354441fbad): opus-A-r1-s1's commit 0158e05, rejected only for its added section/variable/omit commands and a judge bug on sorry-bodied definitions; binders made explicit by hand, same proofs
<!-- conductor:provenance:end -->

## 8. Build and audit record

Every row is a quoted command output: the exact command, the commit it ran on, and its output (exit code and
the decisive lines) copied verbatim. A row that paraphrases an outcome is not allowed; a check that was not run
is a row with outcome `NOT RUN`.

| date | command | commit | quoted output |
|---|---|---|---|
| 2026-10-29 | `git diff --stat 1f2b0df9da90 d041020a04af -- '*.lean' lakefile.toml lean-toolchain lake-manifest.json comparator.json records.yaml conductor.toml` (Lean sources since 1f2b0df9da90: Challenge.lean module docstring only) | d041020a04af | ` Challenge.lean \| 20 +++++++++++++------- ⏎ 1 file changed, 13 insertions(+), 7 deletions(-)`; `git diff 1f2b0df9da90 d041020a04af -- Challenge.lean \| grep -E '^[-+][^-+]'`: 20 lines (7 removed, 13 added), all inside the `/-! ... -/` module docstring (file lines 18–27 and 37–39); no declaration, signature, docstring of a definition or record changed |
| 2026-10-29 | `lake build Challenge` (lake build) | d041020a04af | exit code 0: Build completed successfully (8960 jobs). (longLine linter warnings only) |
| 2026-10-26 | `lake build` (lake build; P-audit clone at this commit) | 1eed040421fe | rc=0 seconds=26.70 (audit quote `003-lake-build.txt`) |
| 2026-10-26 | `lake env lean --json <audit>/job/sweep-solution.lean` (AxiomAudit (axiom sweep); P-audit) | 1eed040421fe | exit code 0: SWEEP 178 constants checked, 0 flagged (audit quote `005-sweep-solution.txt`) |
| 2026-10-26 | `lake env lean --json <audit>/job/sweep-challenge.lean` (AxiomAudit (axiom sweep); P-audit) | 1eed040421fe | exit code 0: SWEEP 36 constants checked, 4 flagged (the four deliberate `sorry` record bodies of Challenge.lean; audit quote `006-sweep-challenge.txt`) |
| 2026-10-26 | `lake env leanchecker SinkReset.Basic`; `lake env leanchecker Challenge`; `lake env leanchecker Solution`; `lake env leanchecker SinkReset.Plan` (leanchecker, one call per module; P-audit) | 1eed040421fe | rc=0 seconds=18.25 ⏎ rc=0 seconds=18.25 ⏎ rc=0 seconds=18.25 ⏎ rc=0 seconds=19.45 (audit quotes `007`–`010`) |
| 2026-10-26 | `lake env lean --run <audit>/job/fidelity/Fidelity.lean <audit>/job/fidelity/fidelity-config.json` (statement fidelity (Challenge = Solution); P-audit) | 1eed040421fe | {"challenge_constants":3868,"detail":"","fidelity":"EQUAL","records":4,"solution_constants":8297,"stage":"done"} ⏎ rc=0 seconds=7.39 (audit quote `016-fidelity.txt`) |
| 2026-10-26 | `conductor audit <clone>` (lean-cheat-check ladder, mode full, allowlist propext, Classical.choice, Quot.sound) | 1eed040421fe | 1 static scan: 0 C / 0 H / 4 M (the four deliberate sorries) ⏎ 2 axiom sweep: 178 checked, 0 flagged ⏎ 3 kernel replay: rc 0 on 4/4 modules ⏎ 4 fidelity: type hashes equal 4/4; structural EQUAL; list-order ok ⏎ VERDICT: CLEAN (not checked: leanchecker --fresh, independent kernels, comparator CI; see the CI row) |
| 2026-10-26 | `./scripts/verify-comparator.sh` (CI job "Check statement against solution", GitHub Actions run 40323934155, https://github.com/benkeene/sink-reset-thresholds/actions/runs/40323934155) | 1eed040421fe | con-ron: accepted 7556 declarations (--verified) ⏎ con-ron kernel accepts the solution ⏎ nanoda kernel accepts the solution ⏎ Your solution is okay! ⏎ jobs: Check metadata and Apache licence: success; Check where the README sends a submitter: success; Build with Lean: success; Check statement against solution: success |
| 2026-10-25 | `lake build` (lake build) | 7980c16efbd4 | exit code 0: Build completed successfully (8966 jobs). (quote `003-lake-build.txt` sha256 0aaf9b27fb65) |
| 2026-10-25 | `lake build Challenge SinkReset SinkReset.Basic SinkReset.Plan Solution` (lake build) | 7980c16efbd4 | exit code 0: Build completed successfully (8966 jobs). (quote `004-lake-build-modules.txt` sha256 ebc4648c8127) |
| 2026-10-25 | `lake env lean --json /Users/ben/.cache/conductor/judge-out/2026-10-25_formalize-sinkresetthresholds/round-3/inv-1-20261025T134013/audit/job/sweep-solution.lean` (AxiomAudit (axiom sweep)) | 7980c16efbd4 | exit code 0: SWEEP 178 constants checked, 0 flagged (quote `005-sweep-solution.txt` sha256 7d9e04d75ca3) |
| 2026-10-25 | `lake env lean --json /Users/ben/.cache/conductor/judge-out/2026-10-25_formalize-sinkresetthresholds/round-3/inv-1-20261025T134013/audit/job/sweep-challenge.lean` (AxiomAudit (axiom sweep)) | 7980c16efbd4 | exit code 0: BAD_AXIOMS SinkReset.five_two_exists_isAk_reset_ge in Challenge : [sorryAx] ⏎ BAD_AXIOMS SinkReset.exists_isAk_reset_ge in Challenge : [sorryAx] ⏎ BAD_AXIOMS SinkReset.five_two_reset_word_le in Challenge : [sorryAx] ⏎ BAD_AXIOMS SinkReset.reset_word_le_of_isAk in Challenge : [sorryAx] ⏎ SWEEP 36 constants checked, 4 flagged (expected: the record bodies of Challenge.lean are deliberate `sorry`) (quote `006-sweep-challenge.txt` sha256 94c5cd82fa0a) |
| 2026-10-25 | `lake env leanchecker Challenge` (leanchecker) | 7980c16efbd4 | exit code 0: (no output) (quote `008-leanchecker-Challenge.txt` sha256 509df0d8badc) |
| 2026-10-25 | `lake env leanchecker Solution` (leanchecker) | 7980c16efbd4 | exit code 0: (no output) (quote `007-leanchecker-Solution.txt` sha256 ea82350cc8b5) |
| 2026-10-25 | `lake env leanchecker SinkReset.Basic` (leanchecker) | 7980c16efbd4 | exit code 0: (no output) (quote `009-leanchecker-SinkReset.Basic.txt` sha256 3513199e95f9) |
| 2026-10-25 | `lake env leanchecker SinkReset.Plan` (leanchecker) | 7980c16efbd4 | exit code 0: (no output) (quote `010-leanchecker-SinkReset.Plan.txt` sha256 539e5023262f) |
| 2026-10-25 | `lake build --no-build Challenge Solution` (statement fidelity (Challenge = Solution)) | 7980c16efbd4 | exit code 0: All targets up-to-date (8965 jobs). (quote `013-fidelity.txt` sha256 9063d7ab1e10) |
| 2026-10-25 | `lake env leanexport Challenge -- Quot Quot.mk Quot.lift Quot.ind SinkReset.reset_word_le_of_isAk SinkReset.exists_isAk_reset_ge SinkReset.five_two_reset_word_le SinkReset.five_two_exists_isAk_reset_ge propext Classical.c` (statement fidelity (Challenge = Solution)) | 7980c16efbd4 | exit code 0: [14753012 bytes, sha256 72a98b57f7c522b6b1a44e841f3682b8b9afbd86952262499082e5205d2ca770, kept at /Users/ben/.cache/conductor/judge-out/2026-10-25_formalize-sinkresetthresholds/round-3/inv-1-20261025T134013/audit/job/fidelity/challenge.ndjson] (quote `014-fidelity.txt` sha256 4a3842e7f4c6) |
| 2026-10-25 | `lake env leanexport Solution -- Quot Quot.mk Quot.lift Quot.ind SinkReset.reset_word_le_of_isAk SinkReset.exists_isAk_reset_ge SinkReset.five_two_reset_word_le SinkReset.five_two_exists_isAk_reset_ge propext Classical.ch` (statement fidelity (Challenge = Solution)) | 7980c16efbd4 | exit code 0: [37972178 bytes, sha256 ba97d8ff5a75e160fabc9aab526f8e80715fe6a8076a2330c58dcf884259cbd5, kept at /Users/ben/.cache/conductor/judge-out/2026-10-25_formalize-sinkresetthresholds/round-3/inv-1-20261025T134013/audit/job/fidelity/solution.ndjson] (quote `015-fidelity.txt` sha256 0eb4b431692f) |
| 2026-10-25 | `lake env lean --run /Users/ben/.cache/conductor/judge-out/2026-10-25_formalize-sinkresetthresholds/round-3/inv-1-20261025T134013/audit/job/fidelity/Fidelity.lean /Users/ben/.cache/conductor/judge-out/2026-10-25_formalize` (statement fidelity (Challenge = Solution)) | 7980c16efbd4 | exit code 0: {"challenge_constants":3868,"detail":"","fidelity":"EQUAL","records":4,"solution_constants":8297,"stage":"done"} (quote `016-fidelity.txt` sha256 40a9bc0dd8b3) |
| 2026-10-25 | `conductor judge --round` (round-3 verdict, per-record axioms) | 7980c16efbd4 | overall RECORDS_PROVED: SinkReset.reset_word_le_of_isAk: clean, axioms [propext, Classical.choice, Quot.sound] ⏎ SinkReset.exists_isAk_reset_ge: clean, axioms [propext, Classical.choice, Quot.sound] ⏎ SinkReset.five_two_reset_word_le: clean, axioms [propext, Classical.choice, Quot.sound] ⏎ SinkReset.five_two_exists_isAk_reset_ge: clean, axioms [propext, Classical.choice, Quot.sound] (verdict `round-3.verdict.json` sha256 8a431a2511ed) |
| 2026-10-25 | `git diff --stat 1f2b0df9da90 HEAD -- '*.lean' lakefile.toml lean-toolchain lake-manifest.json comparator.json records.yaml conductor.toml` (Lean sources unchanged since 1f2b0df9da90) | 7980c16efbd4 | rc=0 |
| 2026-10-25 | `lake build` (lake build) | b1ea5dd6aa1e | exit code 0: Build completed successfully (8966 jobs). (quote `003-lake-build.txt` sha256 fd163b699876) |
| 2026-10-25 | `lake build Challenge SinkReset SinkReset.Basic SinkReset.Plan Solution` (lake build) | b1ea5dd6aa1e | exit code 0: Build completed successfully (8966 jobs). (quote `004-lake-build-modules.txt` sha256 8dca7494b4c5) |
| 2026-10-25 | `lake env lean --json /Users/ben/.cache/conductor/judge-out/2026-10-25_formalize-sinkresetthresholds/round-2/inv-1-20261025T133626/audit/job/sweep-solution.lean` (AxiomAudit (axiom sweep)) | b1ea5dd6aa1e | exit code 0: {"caption":"","data":"TYPE SinkReset.five_two_reset_word_le : ∀\n  (A :\n    @SinkReset.Automaton (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))\n      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))\n  (hA :\n    @SinkReset.Automaton.IsAk (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))\n      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0}  (quote `005-sweep-solution.txt` sha256 5d908ac78e69) |
| 2026-10-25 | `lake env lean --json /Users/ben/.cache/conductor/judge-out/2026-10-25_formalize-sinkresetthresholds/round-2/inv-1-20261025T133626/audit/job/sweep-challenge.lean` (AxiomAudit (axiom sweep)) | b1ea5dd6aa1e | exit code 0: {"caption":"","data":"BAD_AXIOMS SinkReset.exists_isAk_reset_ge in Challenge : [sorryAx]","endPos":{"column":7,"line":31},"fileName":"/Users/ben/.cache/conductor/judge-out/2026-10-25_formalize-sinkresetthresholds/round-2/inv-1-20261025T133626/audit/job/sweep-challenge.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":31},"severity":"information"} ⏎ {"captio (quote `006-sweep-challenge.txt` sha256 71b11ea795c6) |
| 2026-10-25 | `lake env leanchecker SinkReset.Basic` (leanchecker) | b1ea5dd6aa1e | exit code 0: (no output) (quote `007-leanchecker-SinkReset.Basic.txt` sha256 690fb23f0177) |
| 2026-10-25 | `lake env leanchecker Solution` (leanchecker) | b1ea5dd6aa1e | exit code 0: (no output) (quote `008-leanchecker-Solution.txt` sha256 48b4d3675cc9) |
| 2026-10-25 | `lake env leanchecker Challenge` (leanchecker) | b1ea5dd6aa1e | exit code 0: (no output) (quote `009-leanchecker-Challenge.txt` sha256 6e33871bd44e) |
| 2026-10-25 | `lake env leanchecker SinkReset.Plan` (leanchecker) | b1ea5dd6aa1e | exit code 0: (no output) (quote `010-leanchecker-SinkReset.Plan.txt` sha256 b492633f8f40) |

## 9. Independent statement reconstruction

Two isolated GPT-6 Astra reconstructions of the statements of record from the informal text, in run
`2026-10-25_formalize-sinkresetthresholds` (`conductor formalize review`, then `review --recon-only`), each compared
with the records by a Claude Opus comparer. Isolation mode `instruction-only`, breach scan clean. The transcripts stay
in the lab and are identified here by sha256; the per-record comparison is the run's `review/recon.json` and
`review.json` (`recon_record.comparison`).

- `statement-recon-claim-0001` (job 20261025T140743, at commit 7980c16efbd4): transcript sha256 `70ddf53e23021b83`,
  status completed. Comparison `recon-compare-1`: AGREES on `exists_isAk_reset_ge`, `five_two_reset_word_le` and
  `five_two_exists_isAk_reset_ge`; DIFFERS on `reset_word_le_of_isAk`, because the comparer was shown the statement
  blocks only: the record carries `[NeZero n]` and the reconstruction's statement has no `n ≥ 1` hypothesis, although
  its own `Automaton` has a field `sink : Fin n`, which forces `n ≥ 1`. Superseded by the rerun below.
- `statement-recon-claim-0001-2` (job 20261026T081643, at commit 1eed040421fe; fresh key, the comparer now shown both
  sides' definitions): transcript sha256 `50d93c6f1cf850fa`, statement sha256 `a769cbdb403f8d3d`, isolation breach
  false. Comparison `recon-compare-2`:
  - `SinkReset.reset_word_le_of_isAk`: AGREES
  - `SinkReset.exists_isAk_reset_ge`: AGREES
  - `SinkReset.five_two_reset_word_le`: AGREES
  - `SinkReset.five_two_exists_isAk_reset_ge`: AGREES

The second reconstruction ran at commit 1eed040421fe; the §8 row quoting `git diff --stat` shows that the only later
change to a Lean source is the `Challenge.lean` module docstring, so its comparison covers the statements of record at
this commit.

Lean check of the reconstruction's equivalence with the statements of record: NOT RUN (not built in conductor v1; a
human compares the statements above with §2).

## 10. Source provenance

Generated from the conductor template; Palomar scripts in `scripts/` (see `scripts/README.md`).

