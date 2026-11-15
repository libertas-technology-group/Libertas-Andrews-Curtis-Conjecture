<h1 align="center">Libertas Superintelligence: Andrews–Curtis Conjecture</h1>

<!-- APPROVED_FRONT_DOOR: human-approved text. Do not rewrite without the owner's approval. -->

<p align="center">
  <img src="https://img.shields.io/badge/Libertas_Superintelligence-Proprietary-1a1a1a?style=flat-square" alt="Libertas Superintelligence — Proprietary">
  &nbsp;
  <a href="https://competition.sair.foundation/competitions/acc/proof-track"><img src="https://img.shields.io/badge/SAIR-Competition-5B21B6?style=flat-square&labelColor=3B0E27" alt="SAIR Competition — Proof Track"></a>
  &nbsp;
  <img src="https://img.shields.io/badge/License-Apache_2.0-green?style=flat-square" alt="Apache 2.0">
  &nbsp;
  <img src="https://img.shields.io/badge/Lean-v4.35.0--rc2-blue?style=flat-square" alt="Lean v4.35.0-rc2">
</p>

This repository is the Libertas submission for the [Proof Track](https://competition.sair.foundation/competitions/acc/proof-track) of the Andrews–Curtis Conjecture Challenge, organized by Caltech and the SAIR Foundation with Lucas Fagan, Sergei Gukov and Terence Tao [24]. Both tracks opened on 11 September 2026 and close on 30 November 2026 AoE [24]. The Discovery Track scores explicit finite move sequences over a pool of 10,115 presentations; the [Proof Track](https://competition.sair.foundation/competitions/acc/proof-track) accepts formalizations, partial results, and full proofs or disproofs [24]. This repository is a [Proof Track](https://competition.sair.foundation/competitions/acc/proof-track) contribution on both the ordinary conjecture (AC) and Stable AC, explicitly leaning toward the proof direction (`docs/submission.rst`).

Rather than using a modern agentic approach where AI swarms *reward hack* [25] for Lean line counts and disconnected scaffolding, our proprietary Cognitive World Models search for structural solutions and universal theorems that hold at every rank. In the Lean 4 kernel, this formalization reduces the ordinary Andrews–Curtis conjecture to a single statement about abelian-terminal presentations (`Conjecture ↔ A8`), reduces AC to Stable AC together with the stable projection principle, and proves eleven universal laws across the space of balanced presentations. While our results lean toward a positive proof on both tracks by ruling out classical algebraic obstructions, the conjecture remains open and two laws remain open hypotheses.

Libertas Andrews–Curtis was produced by the **Libertas Superintelligence ©** platform, our proprietary general-purpose Cognitive World Model system, built to accelerate scientific discovery across biotechnology, cybersecurity, engineering and quantitative finance. While the general concept of a [world model](https://en.wikipedia.org/wiki/World_model_%28artificial_intelligence%29) is public [13][14], we do not disclose any architectural or scientific details of our proprietary Cognitive World Models in this repository or anywhere publicly. It simulates and understands complex system behaviours rather than matching patterns, generating end-to-end explainable research reports for both mathematicians and non-technical readers while auditing every step from requirement to compiled theorem. Our long-horizon autonomous stress test of the platform produced this entire formalization in three days at a compute cost of approximately $50, and this repository presents the full Lean 4 development: 81 modules, 1,553 declarations, zero `sorry` and three standard axioms, with each number reproduced by the command printed beside it. The result is important to emphasize because it demonstrates the **learning efficiency** of our algorithms and system on new, unseen problems where brute-force search fails [12].

We are grateful to Lucas Fagan, Sergei Gukov, Terence Tao, Caltech and the SAIR Foundation for organizing this challenge and providing the shared formal move definitions (`AC.lean`), as well as to the broader combinatorial group theory and automated-deduction communities whose foundational research made this study possible [1][10][11][15][24]. Building upon those shared definitions, our contribution takes an independent, structural path: to our knowledge, no prior public entry in this challenge reduces the Andrews–Curtis conjecture at general rank to a single named target, reduces AC to Stable AC, proves a second-order universal barrier quantified over every natural-valued complexity measure, or establishes an eleven-law universal composite governing the space of balanced presentations at every rank [24]. One elementary corollary in our development — the winding-domain emptiness at `lean/BranchC.lean:175` — coincides with a single lemma independently proved via a different route by Pragyaan Gaur (`not_cocommutative_of_subsingleton`, filed 7 November 2026), which we cite with attribution [28]. Beyond that shared corollary, no prior contribution has constructed a general-rank reduction architecture or a multi-law universal theory of the Andrews–Curtis space. We release this repository openly so that future researchers and participants can verify, audit and build upon these universal foundations.

**Legal Notice:** Compiled as a stress test of the Libertas Superintelligence © system by Philip Ndikum and Serge Ndikum. (Please review the Licensing & Legal Notice section below for full authorship and legal information.) © 2026 Libertas Technology Group Limited. All rights reserved. This work was produced by Libertas Technology Group Limited using the Libertas Superintelligence © system, a proprietary Cognitive World Model and autonomous reasoning platform. This document is for informational and academic purposes only. The authors disclaim any representation or warranty, express or implied, regarding its accuracy, completeness, or suitability for any purpose. Nothing herein creates any liability or obligation on the part of Libertas Technology Group Limited.

## 📋 Table of Contents

- [📝 Citing This Work](#-citing-this-work)
- [Quick Start & Repository Architecture](#quick-start--repository-architecture)
- [The Andrews–Curtis Conjecture](#the-andrews–curtis-conjecture)
- [Others on the Same Problem](#others-on-the-same-problem)
- [The Universal Laws](#the-universal-laws)
- [Explainable Report](docs/dashboard.html)
- [What This Repository Does Not Claim](#what-this-repository-does-not-claim)
- [About Libertas Superintelligence & Technical Notes](#about-libertas-superintelligence--technical-notes)
- [🤝 Collaboration](#-collaboration)
- [📚 References](#-references)
- [⚖️ Licensing & Legal Notice](#️-licensing--legal-notice)

## 📝 Citing This Work

```bibtex
@misc{ndikum2026andrewscurtis,
  author       = {Philip Ndikum and Serge Ndikum},
  title        = {{L}ibertas {A}ndrews--{C}urtis {C}onjecture},
  year         = {2026},
  publisher    = {Libertas Technology Group Limited},
  note         = {Machine-checked Lean 4 corpus produced by the
                  Libertas Superintelligence system and its
                  Cognitive World Model.},
  url          = {https://github.com/libertas-technology-group/Libertas-Andrews-Curtis-Conjecture},
}
```

## Quick Start & Repository Architecture

Every claim in this repository is reproduced by a command. The formalization is a Lean 4 development with a pinned toolchain and a fixed Mathlib revision. The SAIR and Palomar Registry submission texts are recorded in `docs/submission.rst`.

### 1. Release Provenance, Registry Submissions & Git Hash Verification

Every official submission is pinned to an immutable Git commit hash, so the mathematics stays auditable even after later documentation updates.

- **SAIR Proof Track submission.** The submission text, the track metadata (AC and Stable AC, in the proof direction) and the submitted Git commit hash are recorded in `docs/submission.rst` ([Proof Track](https://competition.sair.foundation/competitions/acc/proof-track)).
- **Palomar Registry submission.** The four required registry artifacts sit at the repository root — `Challenge.lean`, `Solution.lean`, `comparator.json` and `formalization.yaml` — and `./scripts/check_registry.py` checks them against the registry's line and byte caps ([Palomar Registry](https://palomar-registry.org/)).
- **How to check a submitted version.** Each release below is tagged; the exact submitted snapshot is checked out from the release tag, and `./scripts/verify_corpus.sh` prints `CORPUS VERIFIED` from it.

| Version | Date | Milestone / Registry | Status | Verification Command |
| --- | --- | --- | --- | --- |
| `v0.1.0` | 14 November 2026 | Initial Public Release, SAIR Proof Track & Palomar Registry Submission | Verified (`CORPUS VERIFIED`) | `git checkout v0.1.0 && ./scripts/verify_corpus.sh` |
| `v0.1.1` | 15 November 2026 | Palomar Registry module-system port: Lean `v4.35.0-rc2`, `module` headers on 83 Lean files | Verified (`CORPUS VERIFIED`) | `git checkout v0.1.1 && ./scripts/verify_corpus.sh` |

### 2. Environment Specifications

| Component | Version |
| --- | --- |
| Lean 4 compiler | `leanprover/lean4:v4.35.0-rc2` |
| mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |

Environment provisioning requires `elan` and `lake`. Build instructions are at https://lean-lang.org/lean4/doc/quickstart.html.

### 3. Build & One-Command Verification

```bash
git clone https://github.com/libertas-technology-group/Libertas-Andrews-Curtis-Conjecture
cd Libertas-Andrews-Curtis-Conjecture
cd lean && lake exe cache get && lake build
```

> **Expected result:** `Build completed successfully` over every module in the build set, with zero `sorry` and zero user axioms. The corpus verification script `./scripts/verify_corpus.sh` runs the obligation check, the build set, the naming rules and the build itself, then prints `CORPUS VERIFIED`.

### 4. Corpus Size & Reproducibility Commands

| Measure | Value | Command |
| --- | --- | --- |
| Lean modules | 81 | `ls lean/*.lean \| wc -l` |
| Declarations | 1,553 | `scripts/count_declarations.sh` |
| Theorems | 783 | `grep -h '^theorem ' lean/*.lean \| wc -l` |
| Lemmas | 189 | `grep -h '^lemma ' lean/*.lean \| wc -l` |
| `sorry` | 0 | `grep -rn '^[[:space:]]*sorry[[:space:]]*$' lean/*.lean \| wc -l` |
| User axioms | 0 | `grep -rn '^[[:space:]]*axiom[[:space:]]' lean/*.lean \| wc -l` |

### 5. Architectural Layout

```text
lean/               the Lean development, 81 modules, pinned v4.35.0-rc2
Challenge.lean      the Palomar registry challenge module: statements, Mathlib only
Solution.lean       the same declarations with complete kernel-checked proofs
comparator.json     registry configuration: modules, theorem names, permitted axioms
formalization.yaml  Palomar registry metadata: title, abstract, authorship, theorem alignment
docs/               Sphinx documentation, 23 pages, with the submission records (docs/submission.rst)
scripts/            automated corpus and registry verification scripts
```

## The Andrews–Curtis Conjecture

The conjecture, posed by J. J. Andrews and M. L. Curtis in 1965 [1], asks whether every balanced presentation of the trivial group can be transformed into the standard presentation. The moves are three: invert one relator, multiply one relator by another, and conjugate one relator by an arbitrary word. A counterexample would yield a fake smooth four-sphere, which places the question beneath the smooth four-dimensional Poincaré conjecture. For the non-technical reader, we suggest the account in *Scientific American* of how this problem is being used to train AI to predict crises years in advance — it provides the wider industry context [12].

The space of balanced presentations is the graph whose points are the balanced presentations of the trivial group, descriptions that use one relator for each generator, and whose edges are the three moves. The conjecture asks whether every point of that space connects to the standard presentation.

This repository formalises the conjecture, proves a kernel-checked equivalence that concentrates it into one statement about abelian-terminal presentations, and then compiles a set of universal laws about that space. Two of those laws are stated as open hypotheses and are marked as such in the second table below.

### Others on the same problem

Over six decades, the conjecture has resisted sustained campaigns across classical topology, computational group theory and institutional AI programmes — spanning the Caltech reinforcement-learning programme [11][26], whose institution is a team on DARPA's Exponentiating Mathematics (expMath) initiative [27], the SAIR Foundation challenge [24], automated-deduction research at the University of Liverpool [10][15], computational group theory at the Stevens Institute of Technology [3][8][20][23], and breadth-first enumeration [22]. Shehper, Medina-Mardones, Fagan, Lewandowski, Gruen, Qiu, Kucharski, Wang and Gukov used deep reinforcement learning on the same move system, reduced all but two presentations in the Akbulut–Kirby series, and resolved potential counterexamples in the Miller–Schupp series including three infinite subfamilies [11]. Their programme later identified the "two-hump" difficulty barrier that governs search complexity across hard presentations [26]. Their proposal that AK(3) is stably equivalent to the trivial presentation was revisited independently by Lisitsa, who obtained a reduction of AK(3) by automated deduction [10]; his later note records that the theoretical stable-trivializability claim on which the earlier result rested came into question after publication, so this repository records the status as contested rather than settled. Lisitsa also produced the longest known trivialization of a Miller–Schupp presentation, at 8,634 moves [15]. Béchard reported the Caltech programme in *Scientific American*, likening the search to a maze whose paths can run to billions of steps, where brute-force trial-and-error fails, together with the forecasting applications its authors describe [12]. On the structural side, Borovik, Lubotzky and Myasnikov proved the finitary version and showed that a computation in finite groups cannot refute the classical conjecture [18]; Guyot proved the generalised conjecture for every finitely generated soluble group [19]; Bagherifard and Eftekhary used Heegaard Floer theory to exhibit simple balanced 3-manifolds outside the trivial class [16].

This repository is offered as a complementary, formal line of work that builds directly alongside those empirical and structural advances. There is a precise formal correspondence between the search-space geometry uncovered by the Caltech reinforcement-learning campaigns [11][26] and the universal theorems discovered and verified by the Libertas Cognitive World Model system [13][14]:

1. **From the empirical two-hump landscape to universal barrier theorems.** In their reinforcement-learning studies, Shehper, Fagan, Gukov and collaborators found empirically that most presentations are either solvable by greedy length reduction or effectively beyond any current agent — the two-hump difficulty distribution — and that the remaining solutions run long and non-monotone [11][26]. Rather than sampling individual trajectories, the Libertas Cognitive World Model analyzed the global transition rules of the move graph and proved the structural laws beneath that landscape as universal, kernel-checked theorems holding at every rank: `lean/AcInvariant.lean` proves the **Energy Barrier** (no positive measure decreases under every single move), and `lean/AcDetourWidth.lean` proves **Detour Impossibility** (no function of graph distance alone bounds the required detour width at any rank).
2. **From search-space pruning to formal invariant collapse.** Where computational and black-box group studies [3][18][20] asked whether algebraic quotients or module invariants could isolate candidate counterexamples such as AK(3), the Libertas Cognitive World Model pruned those entire attack families in the Lean 4 kernel — proving universally that on presentations of the trivial group the Lyndon/Fox relation module collapses to the abelian exponent lattice (`lean/AcWindingCollapse.lean`, `lean/AcRelationModuleCollapse.lean`), and that no finite quotient can separate a counterexample from the standard basis (`lean/Ak3Invariant.lean`).
3. **From instance-level supermoves to general-rank state-space reduction.** Just as the Caltech reinforcement-learning architecture combined primitive moves into macro `supermoves` to compress the search horizon [11][12][26], the Cognitive World Model compressed the global state space deductively — discharging Euclidean exponent-matrix reduction at general rank (`lean/AcEuclidGeneral.lean`) to prove that the entire ordinary conjecture is equivalent to solving abelian-terminal presentations (`Conjecture ↔ A8`, `lean/AcFinal.lean:58`), and reducing the ordinary conjecture to Stable AC together with the stable projection principle (`docs/stable.rst`).

### The reduction

This repository works in the cyclic setting. Ivanov proves that the original conjecture is equivalent to its cyclic version, in which only cyclic permutations are used in place of arbitrary conjugations, and that the cancellative restriction does not change the conjecture either [4]. The cyclic framework is therefore a published equivalence rather than a modelling choice.

Our Lean 4 formalization proves that the ordinary conjecture is equivalent to one statement about abelian-terminal presentations. `AC.Final.conjecture_iff_A8` at `lean/AcFinal.lean:58` states `Conjecture ↔ A8`: every abelian-terminal balanced presentation of the trivial group reaches a signed permutation of the standard tuple. `A7-general` is discharged at rank two by `lean/AcEuclid.lean:342` and at general rank by `lean/AcEuclidGeneral.lean:857`. The rank-reduction step that lowers a pivot-reduced tuple by one rank is proved at `lean/AcRankReduction.lean:318`; its composition into a lift from rank two to every rank is not yet written. Two primitive statements remain open, and each is a definition of a proposition rather than a theorem: `HighMeasureDescent` at `lean/NielsenSliceBridge.lean:73` and `measure12_ordered_classification` at `lean/NielsenMeasure12Cover.lean:204`. For Stable AC (`docs/stable.rst`), this repository proves that the stable move grammar generates the official `StableStep` relation, establishes the standard-tuple and empty-presentation equivalence, proves `AC.Conjecture → AC.StableConjecture`, and reduces `AC.Conjecture ↔ AC.StableConjecture ∧ projection principle`. The reduction is a statement about the target. It is not a proof of the target.

## The Universal Laws

> **Research reports available on request:** The end-to-end run produced research reports and scientific papers while it narrowed the family of approaches. We provide them to professional mathematicians on request. We have omitted them from this public repository as a precaution for safe and responsible research. The universal laws below, their proofs, and the commands that verify them are complete in this repository.

This repository was produced by Libertas Superintelligence and its proprietary Cognitive World Models [13][14] — the system we deploy across biotechnology, cybersecurity, engineering and quantitative finance to extract governing signal from noise rather than reward-hacking [25] for brute-force Lean tactic scaffolding. Seeking a proof of both the ordinary conjecture and Stable AC, the world model mapped seventeen families of mathematical and scientific approaches and narrowed them down systematically: fifteen closed with a reason, two still alive. The system did not find a resolution of the conjecture within the three-day run, and this repository records that.

Each row names a compiled declaration at every rank, the module that carries it, its status, and the works in whose context the law sits. The reference column situates the law in the literature; the law itself is proved by the declaration beside it. The status column reports the kernel result and the review state, and nothing else.

**Table 1 — kernel-verified universal laws.** The eleven laws below are proved: each row is carried by a compiled declaration at every rank.

| Law | Statement | Module | Status | Key references |
| --- | --- | --- | --- | --- |
| Relation-subgroup collapse | a presentation of the trivial group has the whole free group as the normal closure of its relators | `lean/AcRelationModuleCollapse.lean` | Lean-verified, pending professional review | [1], [9] |
| Exponent span | on that class the exponent span of the relators is the whole lattice | `lean/AcInvariant.lean` | Lean-verified, pending professional review | [3], [8] |
| Relation module | on that class the relation module is the exponent-vector group, relator i mapped to its exponent sums | `lean/AcWindingCollapse.lean` | Lean-verified, pending professional review | [4], [8] |
| Separation | no invariant that factors through that module separates an AC-equivalent pair | `lean/AcRelationModuleCollapse.lean` | Lean-verified, pending professional review | [3], [4] |
| Signed row law | under each move the determinant of the exponent matrix changes by at most a sign | `lean/AcExpMatrixLaw.lean` | Lean-verified, pending professional review | [1], [7] |
| Span stability | inserting or deleting an isolated generator–relator pair preserves whether the span is the whole lattice | `lean/AcStabilityTransport.lean` | Lean-verified, pending professional review | [7] |
| Detour impossibility | no function of graph distance returns the detour width, at any rank | `lean/AcDetourWidth.lean` | Lean-verified, pending professional review | [5], [17] |
| Power family | the pair (x·yⁿ, y) reaches the standard pair for every n | `lean/AcPowFamily.lean` | Lean-verified, pending professional review | [2], [10], [11] |
| Right family | the pair (x, y·xⁿ) reaches the standard pair for every n | `lean/AcRightFamily.lean` | Lean-verified, pending professional review | [2], [11] |
| Finite-quotient blindness | no finite quotient separates a counterexample from the standard basis | `lean/Ak3Invariant.lean` | Lean-verified, pending professional review | [18], [19] |
| Energy barrier | no positive measure decreases under every single move | `lean/AcInvariant.lean` | Lean-verified, pending professional review | [6], [11] |

**Table 2 — open hypotheses.** The two statements below are definitions of propositions and carry no proof. They are stated as open so that no reader mistakes them for results.

| Law | Statement | Module | Status | Key references |
| --- | --- | --- | --- | --- |
| High-measure descent | every tuple above the high-measure threshold descends | `lean/NielsenSliceBridge.lean` | **Stated as an open hypothesis, not proved** | [6], [11] |
| Tail-minimal form | every class reaches a tail-minimal normal form | `lean/AcA8TailMinimal.lean` | **Stated as an open hypothesis, not proved** | [8], [11] |

The registry entry at `Challenge.lean` and `Solution.lean` carries eight theorems restated against Mathlib only: the relation-subgroup collapse, the exponent span, the exponent-vector law, the signed row law, the power family, the conjugation law, the energy barrier, and span stability.

Lishak's lower bound gives the barrier row its published content: the minimal number of relations required to demonstrate that a generator represents the trivial element grows faster than the tower of exponentials of any fixed height in the length of the presentation [17]. For such presentations no human-scale certificate exists, and the object has to be handled structurally, which is what the rows above do.

The tuple-obstruction framing follows Piggott, who defines the Andrews–Curtis groups inside the automorphism group of the free group and solves the generalised word problem there [21]. Panteleev and Ushakov give the closest computational competitor on AK(3), a conjugacy-search algorithm with pseudo-conjugacy graph folding [20]. The search lineage begins with breadth-first search, which established AK(2) and named AK(3) as the smallest potential counterexample [22], and with the proof that every balanced presentation of total relator length at most twelve is trivializable [23].

## What This Repository Does Not Claim

The conjecture is open. This repository proves the reduction and every law in the table marked `Lean-verified`. It names the statements that would close the remaining work: `HighMeasureDescent` at `lean/NielsenSliceBridge.lean:73` and `measure12_ordered_classification` at `lean/NielsenMeasure12Cover.lean:204` on the ordinary conjecture, together with the stable projection principle for Stable AC. Each of these is a definition of a proposition and carries no proof. A reader who wants the exact open statements reads those lines.

## About Libertas Superintelligence & Technical Notes

Libertas Technology Group provides Superintelligence and AI software to institutions where privacy, IP protection, compliance and data security are non-negotiable. Built on a proprietary and vertically integrated AI platform powered by Cognitive World Models, Libertas Superintelligence empowers highly regulated enterprises to solve complex problems across biotechnology (accelerating complex R&D and fundamental scientific breakthroughs), cybersecurity (fortifying institutional defences and mission-critical infrastructure), engineering (architecting and deploying mission-critical systems with speed and reliability) and quantitative finance (advancing quantitative analysis and strategic decision-making for superior risk-adjusted returns) — while maintaining full control and white-box auditability. This three-day autonomous run at approximately $50 in compute demonstrates the **learning efficiency** of our algorithms and Cognitive World Models [13][14] on new, unseen problems where brute-force algorithms fail [12] — producing all 81 modules, 1,553 declarations and 783 kernel-verified theorems with zero `sorry` across knowledge discovery (finding the universal laws), Lean 4 verification (proving them), and documentation production (this repository and the explainable report). This combination of **learning efficiency** and white-box auditability is a core requirement for the regulated industries we serve.

We warmly welcome expert mathematicians to critique our proofs, validate our results, and provide suggestions for improvement. This repository does not settle the conjecture; it provides a set of universal proofs about the space of balanced presentations, each carried by a kernel-checked Lean 4 declaration, together with a kernel-checked reduction of the conjecture to a single open input.

| Category | Technical & Scientific Notes |
| --- | --- |
| **Learning Efficiency** on Unseen Problems | As the *Scientific American* report highlights, open problems where solutions may span billions of steps defeat standard trial-and-error [12]; they require **learning efficiency** rather than brute-force search. Whereas standard agentic harnesses burn heavy compute brute-forcing isolated tactics, our algorithms and Cognitive World Models [13][14] adapt to new, unseen problems by identifying global representations and signal rather than noise — producing all 11 universal laws, the general-rank reduction, and the 81-module formalization in three days for approximately $50 in compute. |
| Anti-Reward-Hacking & White-Box World Models | Our proprietary research into modern non-world-model agentic systems shows that they predominantly *reward hack* [25] for Lean line counts and trivial scaffolding via brute-force compute and high expenditure, yielding unexplainable fragments that offer little scientific understanding. Operating as a fully white-box system, Libertas Superintelligence instead constructs Cognitive World Models [13][14] to map families of mathematical and scientific approaches, narrow them systematically, and carry valid routes end-to-end into kernel-checked universal theorems. |
| Multi-Level Explainable Reports | Unlike brute-force search harnesses, the system builds end-to-end explainable research reports tailored for both professional mathematicians and non-technical decision-makers at different levels of abstraction while seeking a solution, alongside the interactive audit report in `docs/dashboard.html`. |
| General Architecture & Private Enterprise Deployment | Unlike conventional language-model wrappers or agentic tactic harnesses, Libertas Superintelligence © is a general-purpose world-modeling system driven by proprietary mathematical and scientific software. While our proprietary science and internal architecture cannot be disclosed, the entire platform is engineered for self-hosted deployment inside private, air-gapped environments, meeting the strict security, IP, and compliance requirements of regulated operations. |
| Verification Discipline | Every module was recompiled independently of its writer, and every citation was resolved before release. A route that closes becomes a compiled theorem; a route that fails is either named as the exact statement still missing, or closed by a proof that it can never work, with a concrete example where one exists. |
| Safe Scientific Research | The end-to-end run produced research reports and scientific papers alongside the formalization. They are available to professional mathematicians on request, and we have omitted them from this public repository as a precaution for safe and responsible research. The formalisation, the documentation and the commands that verify them are complete here. |

## 🤝 Collaboration

We extend our thanks to Lucas Fagan, Sergei Gukov, Terence Tao, Caltech, and the SAIR Foundation for organizing the Andrews–Curtis Conjecture Challenge and fostering open collaboration between the mathematical and AI research communities [24]. We kindly invite professional mathematicians to review any result and provide feedback:

* Professional mathematical review and validation of these proofs.
* Corrections to any statement whose informal reading does not match its formal form.
* Suggestions for further universal laws this repository should attempt.

Read the explainable report (`docs/dashboard.html`) first if you want the problem, the families of mathematical and scientific approaches and the proof status on one page. Papers and technical reports from the run are available upon request. Please open an issue or contact the maintainers.

## 📚 References

1. J. J. Andrews and M. L. Curtis (1965). "Free Groups and Handlebodies." *Proceedings of the American Mathematical Society* 16, 192–195. <https://doi.org/10.1090/s0002-9939-1965-0173241-8>
2. S. Akbulut and R. Kirby (1985). "A potential smooth counterexample in dimension 4 to the Poincaré conjecture, the Schoenflies conjecture, and the Andrews–Curtis conjecture." *Topology* 24(4), 375–390. <https://doi.org/10.1016/0040-9383(85)90010-2>
3. A. V. Borovik, E. I. Khukhro and A. G. Myasnikov (2003). "The Andrews–Curtis conjecture and black box groups." *International Journal of Algebra and Computation* 13(4). <https://doi.org/10.1142/s0218196703001468>
4. S. V. Ivanov (2018). "On Conjectures of Andrews and Curtis." *Proceedings of the American Mathematical Society* 146. <https://doi.org/10.1090/proc/13710>
5. M. R. Bridson (1999). "Fractional isoperimetric inequalities and subgroup distortion." *Journal of the American Mathematical Society* 12(4). <https://doi.org/10.1090/S0894-0347-99-00308-2>
6. X. Fernández (2024). "Morse theory for group presentations." *Transactions of the American Mathematical Society* 377(4). <https://doi.org/10.1090/tran/8958>
7. W. Metzler (1985). "On the Andrews-Curtis conjecture and related problems." *Contemporary Mathematics* 44, 35–50. <https://doi.org/10.1090/conm/044/813099>
8. A. D. Myasnikov, A. G. Myasnikov and V. Shpilrain (2002). "On the Andrews–Curtis equivalence." *Contemporary Mathematics* 296, 183–198. <https://doi.org/10.1090/conm/296/05074>
9. R. G. Burns and O. Macedońska (1993). "Balanced Presentations of the Trivial Group." *Bulletin of the London Mathematical Society* 25(6), 513–526. <https://doi.org/10.1112/blms/25.6.513>
10. A. Lisitsa (2025). "Stable Andrews–Curtis trivialization of AK(3) revisited. A case study using automated deduction." *arXiv:2501.18601*. <https://doi.org/10.48550/arXiv.2501.18601>
11. A. Shehper, A. M. Medina-Mardones, L. Fagan, B. Lewandowski, A. Gruen, Y. Qiu, P. Kucharski, Z. Wang and S. Gukov (2025). "What makes math problems hard for reinforcement learning: a case study." *arXiv:2408.15332*. <https://doi.org/10.48550/arXiv.2408.15332>
12. D. E. Béchard (2025). "How an Unsolved Math Problem Could Train AI to Predict Crises Years in Advance." *Scientific American*, 11 August 2025. <https://www.scientificamerican.com/article/how-this-ai-breakthrough-with-pure-mathematics-and-reinforcement-learning/>
13. D. Ha and J. Schmidhuber (2018). "World Models." *arXiv:1803.10122*. <https://doi.org/10.48550/arXiv.1803.10122>
14. Y. LeCun and P. Fung (2026). "World models: Enabling the next AI revolution." *AI Magazine* 47(4). <https://doi.org/10.1002/aaai.70110>
15. A. Lisitsa (2025). "Automated theorem proving reveals a lengthy Andrews–Curtis trivialization for a Miller–Schupp trivial group presentation." *Examples and Counterexamples* 8, 100201. <https://doi.org/10.1016/j.exco.2025.100201>
16. N. Bagherifard and E. Eftekhary (2024). "Simple balanced three-manifolds, Heegaard Floer homology and the Andrews–Curtis conjecture." *Algebraic and Geometric Topology* 24(8), 4519–4543. <https://doi.org/10.2140/agt.2024.24.4519>
17. B. Lishak (2017). "Balanced finite presentations of the trivial group." *Journal of Topology and Analysis* 9(2), 363–378. <https://doi.org/10.1142/S1793525317500182>
18. A. V. Borovik, A. Lubotzky and A. G. Myasnikov (2005). "The Finitary Andrews–Curtis Conjecture." *Progress in Mathematics* 248, 15–30. <https://doi.org/10.1007/3-7643-7447-0_2>
19. L. Guyot (2018). "On Andrews–Curtis conjectures for soluble groups." *International Journal of Algebra and Computation* 28. <https://doi.org/10.1142/S0218196718500054>
20. D. Panteleev and A. Ushakov (2019). "Conjugacy search problem and the Andrews–Curtis conjecture." *Groups Complexity Cryptology* 11(1), 43–60. <https://doi.org/10.1515/gcc-2019-2005>
21. A. Piggott (2007). "Andrews–Curtis groups and the Andrews–Curtis conjecture." *Journal of Group Theory* 10(3). <https://doi.org/10.1515/jgt.2007.029>
22. G. Havas and C. Ramsay (2003). "Breadth-first search and the Andrews–Curtis conjecture." *International Journal of Algebra and Computation* 13(1), 61–68. <https://doi.org/10.1142/S0218196703001365>
23. A. D. Miasnikov (1999). "Genetic algorithms and the Andrews–Curtis conjecture." *International Journal of Algebra and Computation* 9(6). <https://arxiv.org/abs/math/0304306>
24. The Andrews–Curtis Conjecture (ACC) Challenge (2026). Co-organized by Caltech and the SAIR Foundation with Lucas Fagan, Sergei Gukov and Terence Tao. Competition site: <https://competition.sair.foundation/competitions/acc> · Rules repository: <https://github.com/SAIRcompetition/Andrews-Curtis>
25. A. Mazur, X. Li and A. Dubrawski (2026). "Mitigating Reward Hacking in Mathematical Reasoning Without Ground-Truth Labels." *MATH-AI: The 6th Workshop on Mathematical Reasoning and AI at NeurIPS 2026*. <https://neurips.cc/virtual/2026/loc/atlanta/168438> · OpenReview: <https://openreview.net/forum?id=wSQdImNKhX>
26. L. Fagan, M. Tarquini, A. Shehper, M. Manko, A. Gruen, C. Huang, G. Butbaia, D. Passaro and S. Gukov (2026). "The Two-Hump Problem: Bridging the Difficulty Gap in Mathematical Reinforcement Learning." *ICML 2026*. <https://doi.org/10.48550/arXiv.2606.21611>
27. DARPA Information Processing Techniques Office (2026). "Exponentiating Mathematics (expMath)." <https://www.darpa.mil/research/programs/expmath-exponential-mathematics>
28. P. Gaur (2026). "A measured neighbourhood of the Andrews–Curtis conjecture: the census to total length 14, the box around AK(3), exact peaks on AC-19, and a Lean 4 archive." GitHub repository, filed 7 November 2026. <https://github.com/pragyaangaur/Andrews-Curtis-Conjecture> · Zenodo: <https://doi.org/10.5281/zenodo.24035724>

Every reference carries a resolvable DOI or a stable publisher URL. `docs/references.rst` records the retrieval that confirmed each one. Two anchors cited by earlier drafts are not carried here because no record resolved for them: Rourke 1979 and the description of Bridson's move-count paper as a 2015 preprint. Bridson's distortion paper is cited instead [5].

## ⚖️ Licensing & Legal Notice

Copyright © 2026 Libertas Technology Group Limited. All rights reserved.

All software is licensed under the Apache License, Version 2.0 (Apache 2.0); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the Apache 2.0 license at: https://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law or agreed to in writing, all software and materials distributed here under the Apache 2.0 license are distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the license for the specific language governing permissions and limitations under that license.

**Proprietary Notice:** This work was produced by Libertas Technology Group Limited using the **Libertas Superintelligence ©** system, a proprietary Cognitive World Model and autonomous reasoning platform. This document and the associated code are for informational and academic purposes only. The authors disclaim any representation or warranty, express or implied, regarding its accuracy, completeness, or suitability for any purpose. Nothing herein creates any liability or obligation on the part of Libertas Technology Group Limited.

Material restated from public repositories keeps its own notice in the file header: the MIT notice for the detour-width result, and the Apache 2.0 notice for the vendored competition definitions.
