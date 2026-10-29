# Computation

<!-- Packet COMPUTATION.md was an empty template; this body is PROOF.md Appendix A, "Location" to "Status" inclusive (Appendix B item 4), applied at P-package 2026-10-25. -->

* **Verifier.** `verifier__verify.py`, SHA-256 `456ff3770a2f5256a23d8732f217fd87d40ad6eb21c14d43b202b42b53ff9c7f`.
* **Certificate.** `experiment__out__cert.json`, SHA-256
  `72af5a40653bb796a3132ede643129ef81ea718b33b71e18905dfdc0cf36ceb5`.
* **Stored verification record.** `verifier__results__20261024T083044703883.json` (lines 6–12 hold the two hashes
  above and the PASS outcome).
* **Reproduction.** Run from any directory:
  `python3 -I -B <dir>/verifier__verify.py <dir>/experiment__out__cert.json`, where `<dir>` is the directory holding the verifier and the certificate (the lab's research-run audit
  directory; it is not part of this repository).
  Expected exit status is 0, with the single output line
  `PASS M(n,k) = sum_i ceil(i/k) for all 9 cases 3<=n<=5, 1<=k<=n-1; 72 witnesses checked; every maximum recomputed exhaustively over all alphabets of <= n-1 letters (n<=4 by two engines; n=5 bit-parallel)`.
* **What it checks.** The verifier imports no searcher code. It recomputes every maximum exhaustively
  (`verifier__verify.py:340–352`) rather than trusting the certificate's `complete` flag. It also checks the 72
  witness automata.
* **Assumptions it relies on** (`verifier__README.md:47–69`). (i) The token game and the active-set game are equivalent.
  (ii) A positional winning strategy uses at most $n-1$ distinct letters, so alphabets of at most $n-1$ letters
  suffice. (iii) Padded alphabet multisets modulo relabelling of nonzero states cover all cases. Informational orbit
  counts are *not* independently certified (`README:26–28`, `verify.py:329–331`); the maxima do not depend on them.
* **Provenance of this record.** The hashes were matched against the stored record by the Astra adversary (job
  20261024T091633). The Astra reviewer (job 20261024T092424) independently reran the command above, with exit
  status 0, the output line above, and matching `shasum -a 256` hashes. This responder could not read that directory
  in the current round, so the entries above are transcribed from those two audit transcripts and were not
  re-executed here.
* **Status.** The Theorem is a handwritten proof (Sections 1–5). The computation is independent corroboration for
  $3\le n\le 5$; it is neither formal verification nor a premise.
