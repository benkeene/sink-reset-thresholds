# sink-reset-thresholds

Sharp reset thresholds for bounded-response synchronization games with a sink — a Lean 4 / Mathlib formalization.

Lean statements of the theorem of `docs/PROOF.md` §5: for `k = 1` or `n ≤ k + 3`, every `n`-state `A_k`
automaton with a sink has a reset word of length at most `f k n = ∑_{i=1}^{n-1} ⌈i/k⌉`, and some such automaton has
none shorter; in particular `M(5,2) = 6`. The informal proof is the VERIFIED packet claim_0001 of the conductor lab
(cases of the Lipin–Volkov conjecture, arXiv:2601.18362, and of its ceiling-sum form). What is new: the endpoints
`k = 1` (Rystsov's bound) and `k = n - 1` were known; the theorem adds `M(k+2,k) = k+2` and `M(k+3,k) = k+4` for
`k ≥ 2`, including the non-divisible pairs `(4,2)` and `(5,3)`, which the Lipin–Volkov conjecture (stated for
`k ∣ n-1` only) does not cover. The four statements of record
are proved in `Solution.lean` from the development `SinkReset/Plan.lean`; every statement about a build or check
points at a quoted row of `CORRESPONDENCE.md` §8 ("Build and audit record").

## Layout

- `Challenge.lean` — statements of record (Mathlib-only imports, deliberate `sorry`s). The record section is
  rendered from `records.yaml`.
- `Solution.lean` — restates the definitions and proves each statement of record; does not import `Challenge`.
- `SinkReset/` — the development library.
- `records.yaml` — the ordered list of statements of record; `comparator.json` and `formalization.yaml`
  (`status.main_results`, `alignment.statements`) are rendered from it.
- `docs/PROOF.md` — the informal proof; `CORRESPONDENCE.md` — informal ↔ formal correspondence and the audit
  record.

## Building and checking

```
lake exe cache get
lake build
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh          # Linux with bubblewrap; runs in CI (job "Check statement against solution")
conductor package check .               # records.yaml ↔ Challenge.lean ↔ comparator.json ↔ formalization.yaml ↔ Solution.lean
```

Pinned toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib `v4.35.0-rc3`. Never commit `.lake`.

On a conductor host, skip `lake exe cache get`: there `.lake/packages` is a copy-on-write clone of the canonical
prebuilt `.lake` (`conductor lean lake-clone`), and `./scripts/verify-comparator.sh` is left to CI (see
`scripts/README.md`).

## Who wrote what

Ben Keene designed and ran the pipeline and reviewed CORRESPONDENCE.md. The proofs and records were written by
the agents named per declaration in `CORRESPONDENCE.md` §7 ("Provenance"); commits keep their `Co-Authored-By`
and `Astra-*` trailers. Agent agreement is never treated as evidence; the evidence is the Lean kernel and the
CI comparator. Decisions of scope, promotion and submission are Ben Keene's.

## Palomar entry and citation

Registered as [PALOMAR-2026-10-30-000003, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-30-000003&version=1)
on 2026-10-30 at commit `517b2cd82a8f3ee66476b90ee38a34d6cb9843f6`: Comparator checked the four statements of record
(`SinkReset.reset_word_le_of_isAk`, `SinkReset.exists_isAk_reset_ge`, `SinkReset.five_two_reset_word_le`,
`SinkReset.five_two_exists_isAk_reset_ge`), replayed through the nanoda and con-ron kernels, using only `propext`,
`Classical.choice` and `Quot.sound`; automated review: no blocking problems (not an endorsement), one non-blocking
comment. That comment is the erratum to version 1: its Challenge.lean docstring, formalization.yaml and docs/CLAIM.md
called `(5,2)` "the first pair that is neither endpoint"; `(4,2)` already is. `(5,2)` is the first non-endpoint pair with
`k ∣ n-1`, the first on which the Lipin–Volkov conjecture itself was open. Version 2, submitted from this commit,
carries the correction (docstring and prose only; no statement, definition or proof changed).

Cite as: Ben Keene, *Sharp reset thresholds for bounded-response synchronization games with a sink* (Lean 4 / Mathlib
formalization), Palomar Registry entry PALOMAR-2026-10-30-000003, 2026, https://github.com/benkeene/sink-reset-thresholds.

## Submission

Palomar submissions go through https://submit.palomar-registry.org/ with the full 40-character commit SHA.
Before submitting, run `conductor package checklist .` and tick every item with a quoted output (`docs/CHECKLIST.md`),
then run the Palomar mechanical preflight once on the commit to submit: the manual workflow
`.github/workflows/palomar-preflight.yml` calls Palomar's reusable submission workflow in full mode (the repository
must be public for it to run; the repository's own CI is not equivalent). Submit only on `status: pass`.

## License

Apache-2.0; see `LICENSE`.
