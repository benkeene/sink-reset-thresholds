# Correspondence: informal statements ↔ formal statements

Status (2026-10-25): the four statements of record are stated in `Challenge.lean` and restated in `Solution.lean`
with deliberate `sorry` bodies; nothing is proved and no check has run (§8 has no rows). Nothing in this file may
describe a build, count or check except by quoting the command and its output.

## 1. Informal statements and status

`docs/PROOF.md` §5 **Theorem**: for `k ≥ 1`, `n ≥ 2`, if `k = 1` or `n ≤ k + 3` then `M(n,k) = f_k(n) = ∑_{i=1}^{n-1} ⌈i/k⌉`;
in particular the nine values for `3 ≤ n ≤ 5`, among them `M(5,2) = 6`. Its upper bound is Proposition 10 (§3), its
lower bound Lemmas 12, 13, 14 (§4). Lab status: claim_0001 **VERIFIED** (prove run `2026-10-24_prove-claim-0001`;
Ben's approval 2026-10-25; `~/conductor-lab/agents/shared/claim_0001/STATUS.yaml`). Formalization: not started.
Not claimed by the packet and not a statement of record: the `n = k + 4` case in the independent prover's transcript
(joint report Problem 2), the general conjecture, and PROOF.md Appendix A (computation, corroboration only).

## 2. Statements of record

The statements of record are listed, in order, in `records.yaml`; `Challenge.lean` (record section),
`comparator.json` and `formalization.yaml` are rendered from it by `conductor package render`, and
`conductor package check` fails on any drift among them.

- `SinkReset.reset_word_le_of_isAk` (PROOF.md §5 Theorem, upper bound; §3 Proposition 10). For `n ≥ 1`, `k ≥ 1`
  with `k = 1 ∨ n ≤ k + 3`, every `Automaton n` satisfying `IsAk k` has a word `w` with `IsReset w` and
  `w.length ≤ f k n`. This is "`rt(A) ≤ f_k(n)` for every `n`-state `A_k` automaton with sink", hence
  `M(n,k) ≤ f_k(n)`. Development lemma: to be named by the formalize plan.
- `SinkReset.exists_isAk_reset_ge` (PROOF.md §5 Theorem, lower bound; §4 Lemmas 12–14). For `n ≥ 2`, `k ≥ 1` with
  `k = 1 ∨ n ≤ k + 3`, there is an `Automaton n` with `IsAk k` all of whose reset words have length `≥ f k n`. This is
  "some `n`-state `A_k` automaton with sink has `rt ≥ f_k(n)`" (the extremal automata `T_n`, `P_n`, `C_{k,1}`,
  `C_{k,2}`), hence `M(n,k) ≥ f_k(n)`. With the previous entry: `M(n,k) = f_k(n)`, and the supremum is attained.
  Development lemma: to be named by the formalize plan.
- `SinkReset.five_two_reset_word_le` (PROOF.md §5, the pair `(5,2)`): the first entry at `n = 5`, `k = 2`, with
  `f 2 5 = 6` evaluated: every 5-state `A_2` automaton with sink has a reset word of length `≤ 6`.
- `SinkReset.five_two_exists_isAk_reset_ge` (PROOF.md §4 Lemma 14, `C_{2,2}`; §5): the second entry at `n = 5`,
  `k = 2`: some 5-state `A_2` automaton with sink has no reset word of length `< 6`. The two together are the
  CLAIM.md headline `M(5,2) = 6`.

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

## 4. Hypotheses and conventions

- `[NeZero n]` on every statement (and on `Automaton n`): `n ≠ 0`, so the sink `0 : Fin n` exists. For `n = 1` the
  upper bound is trivial (the empty word is a reset word; `f k 1 = 0`) and the lower bound is stated only for
  `2 ≤ n`, as in the Theorem (`n ≥ 2`).
- `1 ≤ k`: PROOF.md assumes `k ≥ 1`. With `k = 0` Bob has no replies and `(i + 0 - 1) / 0 = 0`, so the statement
  would be false and meaningless; it is excluded, not formalized.
- `k = 1 ∨ n ≤ k + 3`: the Theorem's hypothesis verbatim ("If `k = 1`, or `n ≤ k + 3`"); no relation between `n`
  and `k` is assumed otherwise (so `k ≥ n` is allowed, where `f k n = n - 1`).
- Natural subtraction appears once, in `i + k - 1`; with `k ≥ 1` it is exact. `Finset.range n = {0, …, n-1}` matches
  the sum `∑_{i=1}^{n-1}` because the `i = 0` term vanishes.
- States are indexed `0, …, n-1` as in PROOF.md §0, the sink being `0`. Words are `List (Letter n)`, lengths are
  `List.length`, and `act` applies the first letter first.
- Universes: everything is in `Type` (`Fin n`, functions, lists, finsets); no universe variables.
- The headline statements use the numerals `5`, `2`, `6` directly (`Automaton 5`, `IsAk 2`, length `6`), with
  `NeZero 5` found by instance search.

## 5. Formalized scope and gaps

Formalized (as statements; proofs pending): the Theorem of PROOF.md §5 in its full hypothesis `k = 1 ∨ n ≤ k + 3`,
as upper and lower bound, and its instance `(5,2)`. Informal only: `M(n,k)` as a supremum (the bounds say the
supremum is attained and equals `f k n`); the equivalence of the Alice-first and Bob-first games (Lemma 1(a)), which
the definition builds in; Remarks 1–3 of §5; the `n = k + 4` result of the independent prover's transcript, not part
of the claim. Excluded: PROOF.md Appendix A (computational record; corroboration only, never a premise) and
Appendix B (packet errata; applied to `docs/CLAIM.md`, `docs/CONTEXT.md`, `docs/COMPUTATION.md` in this repository,
the packet files untouched); the general Lipin–Volkov conjecture (`n ≥ k + 4`, `k ≥ 2`).

## 6. Toolchain

`lean-toolchain`: `leanprover/lean4:v4.35.0-rc3`; Mathlib `v4.35.0-rc3`. Never commit `.lake`.

## 7. Provenance

Per declaration of record: the model that wrote its proof, the job id and the round. Filled by
`conductor package provenance . --from <run.json>`; edit the run, not this table.

<!-- conductor:provenance:begin -->
| declaration | model | job id | round |
|---|---|---|---|
<!-- conductor:provenance:end -->

## 8. Build and audit record

Every row is a quoted command output: the exact command, the commit it ran on, and its output (exit code and
the decisive lines) copied verbatim. A row that paraphrases an outcome is not allowed; a check that was not run
is a row with outcome `NOT RUN`.

| date | command | commit | quoted output |
|---|---|---|---|
| 2026-10-25 | `lake build` | 4854121 | `8 sorry warnings; last line: Build completed successfully (8965 jobs).; exit 0` |
| 2026-10-25 | `ruby scripts/validate-formalization.rb` | 4854121 | `formalization.yaml contains no TEMPLATE values; exit 0` |
| 2026-10-25 | `python3 -I scripts/check-lean-sources.py` | 4854121 | `Lean source requirements satisfied; exit 0` |
| 2026-10-25 | `uv run conductor package check ~/sink-reset-thresholds (from ~/conductor)` | 4854121 | `check: OK (0 drift findings); exit 0` |
| 2026-10-25 | `uv run conductor lean probe fidelity --tree ~/sink-reset-thresholds` (from ~/conductor) | 4854121 (identical tree, run before the commit) | `"fidelity":"MISMATCH"`, `"detail":"Illegal axiom detected: 'sorryAx'"` (job `~/.cache/conductor/sinkresetthresholds/fidelity/20261025T083324-303708`; the exit code was not captured, a pipe hid it). Expected: Solution.lean still proves every record by `sorry`; the row stays until a sorry-free Solution is probed |

## 9. Independent statement reconstruction

TODO: the reconstruction transcript, and the Lean check of its equivalence with the statements of record.

## 10. Source provenance

Generated from the conductor template; Palomar scripts in `scripts/` (see `scripts/README.md`).
