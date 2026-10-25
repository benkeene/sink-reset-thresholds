# Correspondence: informal statements ↔ formal statements

Status: TODO (author). One paragraph: what is proved, at which commit, which checks have run (each one is a
row of "Build and audit record" below). Nothing in this file may describe a build, count or check except by
quoting the command and its output.

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

Proved in Solution.lean from: (no named declaration)

Informal ↔ formal argument: TODO (documentation agent; quoted outputs only).

### SinkReset.exists_isAk_reset_ge (record)

Informal (PROOF.md §5 Theorem (lower bound), §4 Lemmas 12-14): Lower bound. Let n ≥ 2, k ≥ 1 and either k = 1 or n ≤ k + 3. Some n-state A_k automaton with sink 0 has no reset word shorter than f k n (PROOF.md §5, Theorem, lower bound; Lemmas 12, 13, 14). Together with the upper bound this says M(n,k) = f k n.

Lean statement (Challenge.lean):

```lean
theorem exists_isAk_reset_ge (n k : ℕ) [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) : ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length
```

Proved in Solution.lean from: (no named declaration)

Informal ↔ formal argument: TODO (documentation agent; quoted outputs only).

### SinkReset.five_two_reset_word_le (record)

Informal (PROOF.md §5 Theorem, the nine pairs, (5,2)): M(5,2) ≤ 6: every 5-state A_2 automaton with sink 0 has a reset word of length at most 6 (CLAIM.md headline; PROOF.md §5, the pair (5,2)).

Lean statement (Challenge.lean):

```lean
theorem five_two_reset_word_le (A : Automaton 5) (hA : A.IsAk 2) : ∃ w, A.IsReset w ∧ w.length ≤ 6
```

Proved in Solution.lean from: (no named declaration)

Informal ↔ formal argument: TODO (documentation agent; quoted outputs only).

### SinkReset.five_two_exists_isAk_reset_ge (record)

Informal (PROOF.md §4 Lemma 14 (C_{2,2}), §5 Theorem): M(5,2) ≥ 6: some 5-state A_2 automaton with sink 0 has no reset word of length less than 6 (CLAIM.md headline; PROOF.md §4 Lemma 14, the automaton C_{2,2}).

Lean statement (Challenge.lean):

```lean
theorem five_two_exists_isAk_reset_ge : ∃ A : Automaton 5, A.IsAk 2 ∧ ∀ w, A.IsReset w → 6 ≤ w.length
```

Proved in Solution.lean from: (no named declaration)

Informal ↔ formal argument: TODO (documentation agent; quoted outputs only).

## 3. Definition audit

TODO: each definition in `Challenge.lean`, what it means, and why it is the intended notion.

## 4. Hypotheses and conventions

TODO: natural subtraction, indexing, coercions, universes, and every hypothesis of each statement.

## 5. Formalized scope and gaps

TODO: what is formalized, what is informal only, and exclusions.

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
| `SinkReset.Plan.act_append` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.word_append` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.act_zero` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.image_active_le` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.kill_decreases` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.within_compose` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.within_univ` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.wins_mono` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.wins_word` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.one_game_iff` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.bob_first_iff` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.trap` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.wins_of_rank` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.distances_exist` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.reachable_reset` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.distance_facts` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.distance_Y` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.short_kill` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.classical_bound` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.lift_word` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.wins_push` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.wins_pull` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.closed_set_of_not_sc` | Claude Opus 5.5 (high) | opus-A-r1-s3 | 1 | 1f2b0df9da90 |
| `SinkReset.Plan.closed_reduction` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.f_one` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.f_small` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.f_cycle` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.Plan.f_split` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
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
| `SinkReset.Plan.lower` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.reset_word_le_of_isAk_dev` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.exists_isAk_reset_ge_dev` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.five_two_reset_word_le_dev` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.five_two_exists_isAk_reset_ge_dev` | conductor (human session; no model) | human-A-r1-h1 | 1 | 3f354441fbad |
| `SinkReset.reset_word_le_of_isAk` (statement of record; Solution.lean bridge) | plan materialization (see plan/plan_map.json) | sinkresetthresholds/20261025T083649_planner-planner-claim-0001, plan-materialize-1, plan-materialize-3, plan-materialize-4 | — | e623d0fcef39 |
| `SinkReset.exists_isAk_reset_ge` (statement of record; Solution.lean bridge) | plan materialization (see plan/plan_map.json) | sinkresetthresholds/20261025T083649_planner-planner-claim-0001, plan-materialize-1, plan-materialize-3, plan-materialize-4 | — | e623d0fcef39 |
| `SinkReset.five_two_reset_word_le` (statement of record; Solution.lean bridge) | plan materialization (see plan/plan_map.json) | sinkresetthresholds/20261025T083649_planner-planner-claim-0001, plan-materialize-1, plan-materialize-3, plan-materialize-4 | — | e623d0fcef39 |
| `SinkReset.five_two_exists_isAk_reset_ge` (statement of record; Solution.lean bridge) | plan materialization (see plan/plan_map.json) | sinkresetthresholds/20261025T083649_planner-planner-claim-0001, plan-materialize-1, plan-materialize-3, plan-materialize-4 | — | e623d0fcef39 |
<!-- conductor:provenance:end -->

## 8. Build and audit record

Every row is a quoted command output: the exact command, the commit it ran on, and its output (exit code and
the decisive lines) copied verbatim. A row that paraphrases an outcome is not allowed; a check that was not run
is a row with outcome `NOT RUN`.

| date | command | commit | quoted output |
|---|---|---|---|
| 2026-10-25 | `lake build` (lake build) | 1f2b0df9da90 | exit code 0: Build completed successfully (8966 jobs). (quote `003-lake-build.txt` sha256 653688f25e69) |
| 2026-10-25 | `lake build Challenge SinkReset SinkReset.Basic SinkReset.Plan Solution` (lake build) | 1f2b0df9da90 | exit code 0: Build completed successfully (8966 jobs). (quote `004-lake-build-modules.txt` sha256 fdf3bfaac3b9) |
| 2026-10-25 | `lake env lean --json /Users/ben/.cache/conductor/judge-out/2026-10-25_formalize-sinkresetthresholds/round-1/inv-1-20261025T133338/audit/job/sweep-solution.lean` (AxiomAudit (axiom sweep)) | 1f2b0df9da90 | exit code 0: {"caption":"","data":"TYPE SinkReset.five_two_reset_word_le : ∀\n  (A :\n    @SinkReset.Automaton (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))\n      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))\n  (hA :\n    @SinkReset.Automaton.IsAk (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))\n      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0}  (quote `005-sweep-solution.txt` sha256 57495a71567e) |
| 2026-10-25 | `lake env lean --json /Users/ben/.cache/conductor/judge-out/2026-10-25_formalize-sinkresetthresholds/round-1/inv-1-20261025T133338/audit/job/sweep-challenge.lean` (AxiomAudit (axiom sweep)) | 1f2b0df9da90 | exit code 0: {"caption":"","data":"BAD_AXIOMS SinkReset.exists_isAk_reset_ge in Challenge : [sorryAx]","endPos":{"column":7,"line":31},"fileName":"/Users/ben/.cache/conductor/judge-out/2026-10-25_formalize-sinkresetthresholds/round-1/inv-1-20261025T133338/audit/job/sweep-challenge.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":31},"severity":"information"} ⏎ {"captio (quote `006-sweep-challenge.txt` sha256 b8c2e057c724) |
| 2026-10-25 | `lake env leanchecker SinkReset.Basic` (leanchecker) | 1f2b0df9da90 | exit code 0: (no output) (quote `008-leanchecker-SinkReset.Basic.txt` sha256 0a6c4d300070) |
| 2026-10-25 | `lake env leanchecker Solution` (leanchecker) | 1f2b0df9da90 | exit code 0: (no output) (quote `007-leanchecker-Solution.txt` sha256 d4d2c05a57fc) |
| 2026-10-25 | `lake env leanchecker Challenge` (leanchecker) | 1f2b0df9da90 | exit code 0: (no output) (quote `009-leanchecker-Challenge.txt` sha256 090139637726) |
| 2026-10-25 | `lake env leanchecker SinkReset.Plan` (leanchecker) | 1f2b0df9da90 | exit code 0: (no output) (quote `010-leanchecker-SinkReset.Plan.txt` sha256 41368e23ae73) |

## 9. Independent statement reconstruction

- NOT RUN at this commit: the reconstruction runs after this file is committed (`conductor formalize review`). Its record is the run's `review/recon.json` (statements, hashes, breach scan, per-record AGREES/DIFFERS), and `conductor formalize gate` refuses to hand off unless it AGREES with every record.

Lean check of the reconstruction's equivalence with the statements of record: NOT RUN (not built in conductor v1; a human compares the statements above with §2).

## 10. Source provenance

Generated from the conductor template; Palomar scripts in `scripts/` (see `scripts/README.md`).
