.. raw:: html

   Libertas Andrews–Curtis — Documentation

Nielsen
=======

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

The nielsen family carries the measure argument. It defines cyclic Nielsen length, states the uniform pivot statement, and proves the low half of it.

Entry theorem
-------------

``AC.Nielsen.cyclicNielsen_uniform_pivot_statement`` at ``lean/AcNielsen.lean:67``. The statement says that every abelian-terminal presentation of the trivial group whose two relators are cyclically reduced, are not a signed permutation, and have length at least five admits one step to a smaller abelian-terminal presentation.

Files
-----

``AcNielsenDefs.lean`` and ``AcNielsen.lean`` hold the definitions and the statement. ``AcNielsenCounterexample.lean`` holds the counterexample interface. ``NielsenRotationNormalForm.lean`` and ``NielsenCycLenConj.lean`` hold the normal form and the conjugation lemmas. ``NielsenMeasure12.lean`` and ``NielsenMeasure12Cover.lean`` hold the measure-twelve slice. ``NielsenSevenStage.lean`` holds the seven-stage witness descent. ``NielsenOddness.lean`` and ``NielsenOddnessBridge.lean`` hold the parity results. ``NielsenMeasure10Certificates.lean`` and ``NielsenMeasure10Consumer.lean`` hold the eight measure-ten descent theorems. ``NielsenLowMeasureFinal.lean`` is the capstone. ``NielsenSliceBridge.lean`` splits the target into the low and high cases at ``lean/NielsenSliceBridge.lean:104``. ``NielsenPivotP1.lean`` carries the pivot to the classical candidate in sixty-seven kernel steps. ``NielsenWitnessTrivial.lean`` holds the witness triviality results.

What the family establishes
---------------------------

The low half is conditional on the measure-twelve base. ``low_measure_descent_of_slice`` at ``lean/NielsenLowMeasureFinal.lean:47`` proves ``LowMeasureDescent`` from ``bothLong_measure12_uniform``, whose own closure consumes ``measure12_covers_witness``, which in turn rests on ``measure12_ordered_classification`` at ``lean/NielsenMeasure12Cover.lean:200``. The high half, ``HighMeasureDescent`` at ``lean/NielsenSliceBridge.lean:69``, quantifies over every abelian-terminal presentation above twelve and is open.

Edge to the next family
-----------------------

The assembly family takes the high-half hypothesis and composes it with the proved low half, then walks the result up the chain to the conjecture.
