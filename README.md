# sink-reset-thresholds

Sharp reset thresholds for bounded-response synchronization games with a sink — a Lean 4 / Mathlib formalization.

TODO (author): two or three sentences on what is proved. Status statements must point at a quoted row of
`CORRESPONDENCE.md` §8 ("Build and audit record").

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

TODO: filled after registration (entry id, version, pinned commit, citation).

## Submission

Palomar submissions go through https://submit.palomar-registry.org/ with the full 40-character commit SHA.
Before submitting, run `conductor package checklist .` and tick every item with a quoted output.

## License

Apache-2.0; see `LICENSE`.
