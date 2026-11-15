.. raw:: html

   Libertas Andrews–Curtis — Documentation

The submission record
=====================

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

This page records the exact texts this repository submits under, so the public
record lives in the repository for provenance and for review. This repository submits
to the Proof Track of the Andrews–Curtis Conjecture Challenge on the ordinary
conjecture (AC), in the proof direction, with partial results on Stable AC. No
counterexample is claimed for either conjecture.

The SAIR Proof Track submission
------------------------------

The form fields, as this repository files them:

.. list-table::
   :header-rows: 1
   :widths: 30 70

   * - Field
     - Value
   * - Conjecture
     - AC (with partial results on Stable AC)
   * - Direction
     - proof
   * - Public GitHub repository
     - https://github.com/libertas-technology-group/Libertas-Andrews-Curtis-Conjecture
   * - Git commit hash
     - v0.1.0, 14 November 2026 (tagged release; resolve with git rev-parse v0.1.0)
   * - Sharing agreement
     - checked on the v0.1.0 submission; the submission is published in the SAIR Contributor Network
   * - Submission page
     - https://competition.sair.foundation/competitions/acc/proof-track

The description field, verbatim:

.. code-block:: text

   What this is. A Proof Track submission on the ordinary Andrews–Curtis conjecture (AC),
   in the proof direction, with partial results on Stable AC. This repository is a
   self-contained Lean 4 development over Mathlib (leanprover/lean4:v4.29.1): 81 modules,
   1,553 declarations, 783 theorems, zero sorry and zero user axioms across the build
   set, verified end-to-end by one deterministic command (./scripts/verify_corpus.sh
   prints CORPUS VERIFIED). Building on the competition's shared move definitions in
   AC.lean, this repository establishes, to our knowledge, the first publicly released
   general-rank reduction of the conjecture (Conjecture ↔ A8), the reduction of AC to
   Stable AC with the projection principle, a second-order universal barrier quantified
   over every natural-valued measure, and an eleven-law universal composite governing
   the Andrews–Curtis space at every rank. One elementary corollary — the winding-domain
   emptiness at lean/BranchC.lean:175 — coincides with a single lemma independently
   proved via a different route by Pragyaan Gaur (not_cocommutative_of_subsingleton,
   filed 7 November 2026, github.com/pragyaangaur/Andrews-Curtis-Conjecture), which we
   cite with attribution.

   What is established.
   (1) A kernel-checked general-rank reduction: the ordinary Andrews–Curtis conjecture
   is equivalent to a single statement about abelian-terminal presentations
   (Conjecture ↔ A8, lean/AcFinal.lean:58), with Euclidean matrix reduction discharged
   at rank two (lean/AcEuclid.lean:342) and general rank (lean/AcEuclidGeneral.lean:857),
   and pivot rank-reduction proved at lean/AcRankReduction.lean:318. The remaining
   non-abelian work is concentrated into two named open inputs at fixed file-and-line
   locations: HighMeasureDescent (lean/NielsenSliceBridge.lean:73) and
   measure12_ordered_classification (lean/NielsenMeasure12Cover.lean:204).
   (2) Eleven kernel-verified universal laws over the space of balanced presentations,
   each holding at every rank and for every tuple: relation-subgroup collapse
   (lean/AcRelationModuleCollapse.lean), exponent span (lean/AcInvariant.lean),
   relation-module winding collapse (lean/AcWindingCollapse.lean), module separation
   invariance (lean/AcRelationModuleCollapse.lean), the signed determinant row law
   (lean/AcExpMatrixLaw.lean), span stability under stabilization
   (lean/AcStabilityTransport.lean), detour-width impossibility (lean/AcDetourWidth.lean),
   infinite power-family closure (x·yⁿ, y) for all n (lean/AcPowFamily.lean), infinite
   right-family closure (x, y·xⁿ) for all n (lean/AcRightFamily.lean), finite-quotient
   blindness on AK(3) (lean/Ak3Invariant.lean), and the single-move energy barrier
   (lean/AcInvariant.lean).
   (3) Stable AC partial results (docs/stable.rst): across ten AcStable* modules, this
   repository proves that the stable move grammar generates the official StableStep
   relation, establishes rank accounting and the standard-tuple ↔ empty-presentation
   equivalence, proves stabilize invariance and the implication
   AC.Conjecture → AC.StableConjecture (lean/AC.lean:145), and establishes the
   reduction AC.Conjecture ↔ AC.StableConjecture ∧ projection principle
   (lean/BranchD.lean:286), isolating the stable projection principle as the named
   residual obligation.

   What remains open. The conjecture itself. The two primitive propositions named
   above (HighMeasureDescent and measure12_ordered_classification), the inductive
   composition lifting rank two to every rank, and the stable projection principle.
   No counterexample is claimed for either AC or Stable AC.

   Work by others that we use. We gratefully acknowledge the foundational work of the
   competition organizers and the broader combinatorial group theory community. The cyclic
   reformulation is licensed by S. V. Ivanov's published equivalence (Proceedings of the
   AMS 146, 2018, DOI 10.1090/proc/13710). The official move definitions follow the
   competition's shared formal statements in AC.lean (rules repository:
   https://github.com/SAIRcompetition/Andrews-Curtis, Apache 2.0). This formalization was
   directly inspired by the Caltech Math-AI reinforcement-learning programme of Shehper,
   Medina-Mardones, Fagan, Lewandowski, Gruen, Qiu, Kucharski, Wang and Gukov
   (arXiv:2408.15332, DOI 10.48550/arXiv.2408.15332) and the two-hump difficulty
   analysis of Fagan, Tarquini, Shehper, Manko, Gruen, Huang, Butbaia, Passaro and Gukov
   (ICML 2026, arXiv:2606.21611, DOI 10.48550/arXiv.2606.21611), alongside A. Lisitsa's
   automated-deduction studies on AK(3) and Miller–Schupp presentations
   (arXiv:2501.18601, DOI 10.48550/arXiv.2501.18601; DOI 10.1016/j.exco.2025.100201)
   and the classical barrier literature (Bridson 1999, Lishak 2017,
   Borovik–Lubotzky–Myasnikov 2005).

   Offered as a complementary formal contribution, our Libertas Cognitive World Model
   system establishes the universal, deductive counterpart to the empirical geometry
   uncovered by the Caltech reinforcement-learning programme (whose institution is a
   team on DARPA's Exponentiating Mathematics initiative):
   (i) Where the Caltech studies (arXiv:2408.15332; ICML 2026, arXiv:2606.21611) found
   empirically that most presentations are either solvable by greedy length reduction
   or effectively beyond reach — the two-hump difficulty distribution — our Cognitive
   World Model proved the governing structural laws at every rank in the Lean 4
   kernel: the single-move Energy Barrier (no positive measure decreases under every
   single move, lean/AcInvariant.lean) and Detour Impossibility (no function of graph
   distance bounds detour width, lean/AcDetourWidth.lean).
   (ii) Where algebraic and black-box group investigations (Borovik–Khukhro–Myasnikov
   2003; Borovik–Lubotzky–Myasnikov 2005) examined homological and finite-quotient
   obstructions, our system proved universally in Lean 4 that the Fox/Lyndon relation
   module collapses to the exponent lattice (lean/AcWindingCollapse.lean,
   lean/AcRelationModuleCollapse.lean) and that finite quotients cannot separate a
   counterexample from the standard basis (lean/Ak3Invariant.lean).
   (iii) Where reinforcement-learning agents rely on learned macro-actions
   ("supermoves") to navigate the presentation graph, our Cognitive World Model
   compressed the state space deductively across all ranks — discharging general-rank
   Euclidean reduction (lean/AcEuclidGeneral.lean) to concentrate the entire conjecture
   into abelian-terminal presentations (Conjecture ↔ A8, lean/AcFinal.lean:58) and
   reducing AC to Stable AC together with the stable projection principle
   (lean/BranchD.lean:286).

   Provenance. We thank Lucas Fagan, Sergei Gukov, Terence Tao, Caltech, and the SAIR
   Foundation for organizing this challenge and providing the shared formal definitions.
   This repository was produced as an internal stress test of Libertas Superintelligence ©
   and its proprietary Cognitive World Models — the general-purpose, white-box AI
   platform of Libertas Technology Group Limited (https://libertastechgroup.com) built
   for highly regulated enterprises in biotechnology, cybersecurity, engineering and
   quantitative finance. Within the SAIR Contributor Network, we cite Pragyaan Gaur's
   independent submission (github.com/pragyaangaur/Andrews-Curtis-Conjecture, filed 7
   November 2026, Zenodo DOI 10.5281/zenodo.24035724) for one shared corollary: the
   observation that a presentation of the trivial group at positive rank is not
   cocommutative. His route goes through unit exponent sums; ours goes through the
   exponent-span lattice laws (expSpan_eq_bot_of_cocommutative and
   expSpan_eq_top_of_presents) at lean/BranchC.lean:175. Beyond that shared corollary,
   to our knowledge no prior public entry states a second-order universal law over
   every measure, formalizes an eleven-law universal composite, or establishes the
   general-rank reduction of the conjecture in Lean 4.
   Demonstrating the learning efficiency of world-model-driven discovery, a single
   three-day autonomous run at approximately $50 in compute produced the complete
   81-module, 1,553-declaration, 783-theorem, zero-sorry Lean 4 formalization, which we
   share openly as a foundation for the community to build upon. Every claim above is
   reproduced by a deterministic command in the repository at
   https://github.com/libertas-technology-group/Libertas-Andrews-Curtis-Conjecture.

The Palomar registry entry
--------------------------

The Palomar registry of Lean verified mathematics (https://palomar-registry.org/)
registers a pinned commit of a GitHub repository with four artifacts, and this
repository ships all four. ``scripts/check_registry.py`` enforces the registry caps
on the challenge module at every verification run.

.. list-table::
   :header-rows: 1
   :widths: 40 60

   * - Registry artifact
     - This repository
   * - Challenge file, Mathlib-only imports, capped
     - ``Challenge.lean``, statements only, 167 lines
   * - Solution module proving the challenge claims
     - ``Solution.lean``, no sorry and no user axiom
   * - Registry configuration
     - ``comparator.json``
   * - Informal description and disclosures
     - ``formalization.yaml``

The v0.1.1 module-system port
-----------------------------

Release ``v0.1.1`` moves the development from Lean ``4.29.1`` to
``leanprover/lean4:v4.35.0-rc2`` and adds the module header to every submitted
Lean source file: the bare ``module`` keyword, ``public import`` for every
dependency, and ``@[expose] public section`` around each body. All 83 Lean files
carry the header, the eleven modules that the toolchain change broke were
repaired without a statement edit, and the theorem declarations are identical to
``v0.1.0``. The corpus verifies at 81 modules, 1,553 declarations, 783 theorems
and 189 lemmas with zero ``sorry`` and the three standard axioms. The filed SAIR
description above is the text submitted at ``v0.1.0`` and is preserved verbatim.

The registry reads the public title and abstract from the ``project`` block of
``formalization.yaml``. The current fields, verbatim:

.. code-block:: yaml

   project:
     name: 'Libertas — Andrews–Curtis Conjecture: universal laws and a kernel-checked reduction'
     description: 'A Lean 4 (Mathlib) corpus on the Andrews–Curtis conjecture: a kernel-checked
       reduction of the conjecture to abelian-terminal presentations, eleven universal laws
       over the space of balanced presentations, and infinite family closures. The registered
       statements are universal: the relation-subgroup collapse — a balanced presentation
       whose presented group is one-element has the whole free group as the normal closure
       of its relators — the exponent-span law, the signed determinant law under the three
       moves, the power family closure for every exponent, the absence of a strictly
       decreasing measure at every rank, and span stability under stable moves, with
       vocabulary lemmas recording that conjugation fixes the exponent data. Solution.lean
       carries no sorry and no user axiom; one command reproduces every count. Produced in a
       three-day autonomous stress test for approximately $50 in compute — demonstrating the
       learning efficiency of the Libertas Superintelligence platform and Cognitive World
       Models of Libertas Technology Group across biotechnology, cybersecurity, engineering
       and quantitative finance.'

The registry entry URL is recorded on this page when the snapshot is registered.

The direction
------------

This repository is a proof-direction contribution on both AC and Stable AC. On AC it
reduces the conjecture to abelian-terminal presentations and two named open
inputs. On Stable AC it proves the stable move grammar, the terminal-state
equivalence and the implication ``AC.Conjecture → AC.StableConjecture``, and
reduces the ordinary conjecture to ``AC.StableConjecture`` together with the
stable projection principle, which is the named residual obligation
(``docs/stable.rst``).
