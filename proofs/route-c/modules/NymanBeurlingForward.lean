import RiemannHypothesis.Criteria.NymanBeurling.BaezDuarte

/-!
# Nyman--Beurling forward bridge

This file splits the existing RH-level Nyman--Beurling equivalence into the two
logical directions needed by the project.  It is deliberately additive:
`BaezDuarte.lean` still contains the historical equivalence axiom, while this
file provides named forward/converse targets and wiring lemmas so future work can
replace only the forward direction.
-/

namespace RH.Criteria.NymanBeurling.NymanBeurlingForward

open RH.Criteria.NymanBeurling.BaezDuarte

/-- The forward Nyman--Beurling implication needed for the RH pipeline. -/
def NBForward : Prop :=
  NymanBeurlingCriterion → RH.Basic.RiemannHypothesis

/-- The converse Nyman--Beurling implication, kept separate and deferred. -/
def NBConverse : Prop :=
  RH.Basic.RiemannHypothesis → NymanBeurlingCriterion

/--
Named container for the split Nyman--Beurling/RH bridge.  Future work can
provide only `forward` while leaving `converse` absent.
-/
structure NymanBeurlingSplitBridge where
  forward : NBForward
  converse : NBConverse

/-- Reassemble the full equivalence from the two split directions. -/
theorem iff_of_forward_and_converse (hF : NBForward) (hC : NBConverse) :
    NymanBeurlingCriterion ↔ RH.Basic.RiemannHypothesis :=
  ⟨hF, hC⟩

/-- The existing equivalence axiom supplies the forward direction. -/
theorem NBForward_of_nyman_beurling_criterion_iff_RH : NBForward :=
  nyman_beurling_criterion_iff_RH.mp

/-- The existing equivalence axiom supplies the converse direction. -/
theorem NBConverse_of_nyman_beurling_criterion_iff_RH : NBConverse :=
  nyman_beurling_criterion_iff_RH.mpr

/-- The existing equivalence axiom packages into the split bridge structure. -/
def splitBridge_of_nyman_beurling_criterion_iff_RH :
    NymanBeurlingSplitBridge where
  forward := NBForward_of_nyman_beurling_criterion_iff_RH
  converse := NBConverse_of_nyman_beurling_criterion_iff_RH

/-- Báez--Duarte criterion implies the Nyman--Beurling criterion by the proved finite bridge. -/
theorem nymanBeurlingCriterion_of_baezDuarteCriterion
    (h : BaezDuarteCriterion) : NymanBeurlingCriterion :=
  nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr h

/--
Forward-only replacement for `baez_duarte_criterion_implies_RH`: the old theorem
uses the full iff axiom, while this theorem needs only `NBForward`.
-/
theorem RH_of_baezDuarteCriterion_of_NBForward
    (hF : NBForward) (h : BaezDuarteCriterion) :
    RH.Basic.RiemannHypothesis :=
  hF (nymanBeurlingCriterion_of_baezDuarteCriterion h)

/-- The split bridge supplies the forward-only Báez--Duarte-to-RH theorem. -/
theorem RH_of_baezDuarteCriterion_of_splitBridge
    (H : NymanBeurlingSplitBridge) (h : BaezDuarteCriterion) :
    RH.Basic.RiemannHypothesis :=
  RH_of_baezDuarteCriterion_of_NBForward H.forward h

/--
The old Báez--Duarte-to-RH theorem factors through the new forward-only wrapper.
This theorem is intentionally axiom-dependent only because its input
`NBForward_of_nyman_beurling_criterion_iff_RH` comes from the pre-existing iff
axiom.
-/
theorem baez_duarte_criterion_implies_RH_via_NBForward :
    BaezDuarteCriterion → RH.Basic.RiemannHypothesis :=
  RH_of_baezDuarteCriterion_of_NBForward
    NBForward_of_nyman_beurling_criterion_iff_RH

-- ---------------------------------------------------------------------------
-- NB1 stop-gate: Mellin--Plancherel on the critical line
-- ---------------------------------------------------------------------------

/-- The point `1/2 + it` on the critical line. -/
noncomputable def criticalLinePoint (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)

/-- The ordinary L² norm-square over the positive half-line. -/
noncomputable def positiveHalfLineL2NormSq (f : ℝ → ℂ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), ‖f x‖ ^ 2

/-- The critical-line Mellin norm-square. -/
noncomputable def mellinCriticalLineL2NormSq (f : ℝ → ℂ) : ℝ :=
  ∫ t : ℝ, ‖mellin f (criticalLinePoint t)‖ ^ 2

/--
Named stop-gate for NB1(b): the Mellin transform should be unitary from
`L²(0,∞)` to the critical line, up to the classical `1 / (2π)` normalization.

Mathlib already has the ingredients (`mellin_eq_fourier` and Fourier
Plancherel on `L²`), but not this project-facing positive-half-line wrapper.
This structure states the exact wrapper needed by the Nyman--Beurling forward
argument without adding an axiom or a `sorry`.
-/
structure MellinPlancherelUnitary where
  plancherel :
    ∀ f : ℝ → ℂ,
      MeasureTheory.MemLp f 2
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) →
      positiveHalfLineL2NormSq f =
        (1 / (2 * Real.pi)) * mellinCriticalLineL2NormSq f

end RH.Criteria.NymanBeurling.NymanBeurlingForward
