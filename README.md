# Comparing Speculative Semantics in Rocq

This repository contains the Rocq formalization accompanying Section 4 of [Jonathan Baumann's M2 internship report](https://jonathan.baumann.cv/stage-m2/report.pdf).

It contains three different speculative execution semantics for a simple toy language, with implication results between them:
- A forward-only, directive-based semantics similar to the one used for FSLH [[1]](#1)
- A directive-based semantics with rollbacks
- An always-mispredict semantics

We prove that observational equivalence in the directive-based semantics with and without rollbacks is equivalent (`Semantics.v`, Lemmas `fwd_same_leakage_implies_rb_same_leakage` and `rb_same_leakage_implies_fwd_same_leakage`), thus providing a mechanized proof of a prior result by Barthe et al. [[2]](#2) for our language.
We further prove that observational equivalence in the directive-based semantics with rollbacks implies observational equivalence in the always-mispredict semantics, under some restrictions (`Semantics.v`, Lemma `rb_same_leakage_implies_am_same_leakage`).

## Theorem numbers from report
Theorem 4.1.1 (Observational equivalence in semantics with rollbacks implies forward-only observational equivalence). File `Semantics.v`, Lemma `rb_same_leakage_implies_fwd_same_leakage`.

Lemma 4.1.2 (Removing rolled-back execution suffixes). File `Semantics.v`, Lemma `multi_rb_skip_rollback`.

Corollary 4.1.2.1 (Skipping all rolled-back executions). File `Semantics.v`, Lemma `rb_two_executions_skip_rolled_back_speculation`.

Theorem 4.1.3 ((Observational equivalence in forward-only semantics implies observational equivalence in semantics with rollbacks). File `Semantics.v`, Lemma `fwd_same_leakage_implies_rb_same_leakage`.

Theorem 4.2.2 (Observational equivalence in directive-based semantics implies observational equivalence in always-mispredict semantics). File `Semantics.v`, Lemma `rb_same_leakage_implies_am_same_leakage`.

## References
<a id="1">[1]</a>
[FSLH: Flexible Mechanized Speculative Load Hardening](https://arxiv.org/abs/2502.03203).
Jonathan Baumann, Roberto Blanco, Léon Ducruet, Sebastian Harwig, and Catalin Hritcu.
In 35th IEEE Computer Security Foundations Symposium (CSF). June 2025.
[Rocq Development](https://github.com/secure-compilation/fslh-rocq/)

<a id="2">[2]</a>
High-Assurance Cryptography in the Spectre Era.
G. Barthe et al.
In 42nd IEEE Symposium on Security and Privacy, SP, IEEE, 2021, pp. 1884–1901.
doi: 10.1109/SP40001.2021.00046.
