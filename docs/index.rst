.. raw:: html

   Libertas Andrews–Curtis — Documentation

Libertas Andrews–Curtis Documentation
=====================================

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

.. rst-class:: home-tagline

*A machine-checked reduction of the Andrews–Curtis conjecture to named open inputs.*

Libertas Andrews–Curtis is the Lean 4 corpus for Libertas Superintelligence's attempt on the Andrews–Curtis conjecture. The conjecture asks whether every balanced presentation of the trivial group can be transformed into the standard presentation by invert, multiply and conjugate. It has stood open since 1965, and a counterexample would yield a fake smooth four-sphere, which places it beneath the smooth four-dimensional Poincaré conjecture and Zeeman's conjecture. It is prepared as the Libertas submission for the Proof Track of the Andrews–Curtis Conjecture Challenge, organized by Caltech and the SAIR Foundation with Lucas Fagan, Sergei Gukov and Terence Tao, closing on 30 November 2026 AoE.

The corpus formalises the conjecture and proves a kernel-checked equivalence that concentrates it into one statement about abelian-terminal presentations. It then proves the carrying chain at rank two down to two named propositions. Every step of the chain is recorded at a file and line, and one script reproduces the verdict, so a reviewer runs the check instead of trusting the author.

The corpus does not settle the question; it provides a kernel-checked reduction of the conjecture to two named propositions and a set of universal proofs about the space of balanced presentations. The chain proves the rank-two instance of A8; the lift from rank two to every rank is stated as an interface and is not composed. The measure-twelve slice is a definition with no proof in this tree, so the low half is conditional. The open inputs are named in the README and in :doc:`families/nielsen`, and each carries a file and line.

.. list-table::
   :widths: 25 25 25 25
   :align: center

   * - Kernel-checked reduction
     - Zero open obligations
     - One verification command
     - Named open inputs

The corpus is built for the people who review it:

1. **Every claim carries a location.** A theorem is cited by file and line, and the axiom record names the three standard axioms.
2. **The kernel decides.** No user axiom, no ``native_decide``, no ``sorry``, no ``admit`` in the build set.
3. **One command reproduces the verdict.** ``./scripts/verify_corpus.sh`` checks obligations, the build set, naming and documentation, then builds.
4. **The documentation states what is open.** Two definitions and one rank-lift interface carry the remaining work, and each is named.
5. **The families are readable.** Core reduction, stable, topology, homological, nielsen and assembly, each with an entry theorem and a page.
6. **The bibliography is primary.** Every entry carries a resolvable DOI or a stable publisher URL, grouped by the role it plays.

The research reports and scientific papers produced during the run are available to professional mathematicians on request; they are omitted from this public repository as a precaution for safe and responsible research.

The `explainable report <dashboard.html>`_ gives the problem, the families of mathematical and scientific approaches and the proof status on one page, in plain language and with the references at the foot.

.. toctree::
   :maxdepth: 2
   :caption: Statements

   statements

.. toctree::
   :maxdepth: 2
   :caption: Tracks

   proof_track
   submission
   results
   stable

.. toctree::
   :maxdepth: 2
   :caption: Method

   method
   build

.. toctree::
   :maxdepth: 2
   :caption: Standards and families

   standards
   naming
   families/index

.. toctree::
   :maxdepth: 2
   :caption: Results

   universals
   claims

.. toctree::
   :maxdepth: 2
   :caption: Reference

   collaboration
   citation
   licence
   references
