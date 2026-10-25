# Correspondence: informal statements ↔ formal statements

Status: TODO (author). One paragraph: what is proved, at which commit, which checks have run (each one is a
row of "Build and audit record" below). Nothing in this file may describe a build, count or check except by
quoting the command and its output.

## 1. Informal statements and status

TODO: each informal statement (labelled as in `docs/PROOF.md`), with its lab status.

## 2. Statements of record

The statements of record are listed, in order, in `records.yaml`; `Challenge.lean` (record section),
`comparator.json` and `formalization.yaml` are rendered from it by `conductor package render`, and
`conductor package check` fails on any drift among them.

TODO: for each entry of `records.yaml`, in that order, the informal statement (its `informal_ref`), the Lean
statement in words, and the development lemma it is proved from. Do not restate the list itself here: name the
entries, and let `records.yaml` carry the order.

## 3. Definition audit

TODO: each definition in `Challenge.lean`, what it means, and why it is the intended notion.

## 4. Hypotheses and conventions

TODO: natural subtraction, indexing, coercions, universes, and every hypothesis of each statement.

## 5. Formalized scope and gaps

TODO: what is formalized, what is informal only, and exclusions.

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

## 9. Independent statement reconstruction

TODO: the reconstruction transcript, and the Lean check of its equivalence with the statements of record.

## 10. Source provenance

Generated from the conductor template; Palomar scripts in `scripts/` (see `scripts/README.md`).
