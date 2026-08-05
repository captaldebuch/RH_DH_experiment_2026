/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15AristotleRouteAudit
import NBMellinTools.NB15CoupledBoundaryDecay

/-!
# NB15: exact resonant/nonresonant split of the finite middle window

The certified post-functional-equation phase is `e_q(± r u)`.  On every
reduced H15 row it is identically one when `q ∣ r`.  This module splits the
literal finite integrated middle window along that exact criterion.

The split is performed before taking norms and retains the whole signed H15
summand.  The elementary endpoint ledger and the endpoint-to-linear defect
remain in the correction-coupled low sector.  Thus no correction is assigned
termwise to a resonant or nonresonant row.

No estimate is asserted.  The resulting decomposition is the correct input
for a Kuzmin--Landau/geometric estimate on the nonresonant sector and a
separate signed quotient-fiber analysis of the resonant sector.
-/

open scoped BigOperators Topology LSeries.notation
open Complex Filter

namespace NBMellinTools.NB12

/-! ## Exact frequency resonance on a genuine row -/

/-- A row--frequency pair is resonant when its primitive modulus divides the
Estermann frequency. -/
def h15DirectAdditiveFrequencyResonant {N : ℕ}
    (ir : H15LaurentRowIndex N × ℕ) : Prop :=
  h15BettinChandeeModulusVariable ir.1 ∣ ir.2

noncomputable instance h15DirectAdditiveFrequencyResonant_decidable
    {N : ℕ} (ir : H15LaurentRowIndex N × ℕ) :
    Decidable (h15DirectAdditiveFrequencyResonant ir) :=
  Classical.dec _

/-- On a valid resonant row, the reduced direct phase is one in either
orientation. -/
theorem h15DirectAdditiveReducedUnitPhase_eq_one_of_resonant
    {N : ℕ} (sign : BettinChandeeUnitSign)
    (ir : H15LaurentRowIndex N × ℕ)
    (hvalid : h15LaurentRowValid ir.1)
    (hres : h15DirectAdditiveFrequencyResonant ir) :
    h15DirectAdditiveReducedUnitPhase sign ir.2
      (h15BettinChandeeInverseVariable ir.1)
      (h15BettinChandeeModulusVariable ir.1) = 1 := by
  have hcop := h15BettinChandeeInverse_coprime_modulus ir.1 hvalid
  rw [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ hcop]
  exact h15DirectAdditiveUnitPhase_eq_one_of_modulus_dvd_frequency
    sign ir.2 (h15BettinChandeeInverseVariable ir.1)
      (h15BettinChandeeModulusVariable ir.1)
      (Nat.ne_of_gt (h15BettinChandeeModulusVariable_pos ir.1))
      hcop hres

/-! ## Finite middle-window supports -/

noncomputable def h15BettinChandeeResonantMiddleSupport
    (n K J : ℕ) :
    Finset (H15LaurentRowIndex (NB8.logTaperLength n) × ℕ) :=
  (h15BettinChandeeFiniteBox (NB8.logTaperLength n) K J).filter
    h15DirectAdditiveFrequencyResonant

noncomputable def h15BettinChandeeNonresonantMiddleSupport
    (n K J : ℕ) :
    Finset (H15LaurentRowIndex (NB8.logTaperLength n) × ℕ) :=
  (h15BettinChandeeFiniteBox (NB8.logTaperLength n) K J).filter
    (fun ir => ¬ h15DirectAdditiveFrequencyResonant ir)

noncomputable def h15BettinChandeeResonantMiddleFrequencyIntegral
    (n K J : ℕ) (T : ℝ) : ℂ :=
  ∑ ir ∈ h15BettinChandeeResonantMiddleSupport n K J,
    h15BettinChandeeIntegratedSummand n T ir

noncomputable def h15BettinChandeeNonresonantMiddleFrequencyIntegral
    (n K J : ℕ) (T : ℝ) : ℂ :=
  ∑ ir ∈ h15BettinChandeeNonresonantMiddleSupport n K J,
    h15BettinChandeeIntegratedSummand n T ir

/-- Exact signed partition of the literal finite middle window. -/
theorem h15BettinChandeeMiddleFrequencyIntegral_eq_resonant_add_nonresonant
    (n K J : ℕ) (T : ℝ) :
    h15BettinChandeeMiddleFrequencyIntegral n K J T =
      h15BettinChandeeResonantMiddleFrequencyIntegral n K J T +
        h15BettinChandeeNonresonantMiddleFrequencyIntegral n K J T := by
  classical
  unfold h15BettinChandeeMiddleFrequencyIntegral
    h15BettinChandeeFiniteIntegratedHigh
    h15BettinChandeeResonantMiddleFrequencyIntegral
    h15BettinChandeeNonresonantMiddleFrequencyIntegral
    h15BettinChandeeResonantMiddleSupport
    h15BettinChandeeNonresonantMiddleSupport
  exact (Finset.sum_filter_add_sum_filter_not
    (h15BettinChandeeFiniteBox (NB8.logTaperLength n) K J)
    h15DirectAdditiveFrequencyResonant
    (h15BettinChandeeIntegratedSummand n T)).symm

/-! ## Right-edge and certified-energy splits -/

noncomputable def h15BettinChandeeResonantMiddleFrequencyRightEdge
    (n K J : ℕ) (T : ℝ) : ℂ :=
  I * h15BettinChandeeResonantMiddleFrequencyIntegral n K J T

noncomputable def h15BettinChandeeNonresonantMiddleFrequencyRightEdge
    (n K J : ℕ) (T : ℝ) : ℂ :=
  I * h15BettinChandeeNonresonantMiddleFrequencyIntegral n K J T

theorem h15BettinChandeeMiddleFrequencyRightEdge_eq_resonant_add_nonresonant
    (n K J : ℕ) (T : ℝ) :
    h15BettinChandeeMiddleFrequencyRightEdge n K J T =
      h15BettinChandeeResonantMiddleFrequencyRightEdge n K J T +
        h15BettinChandeeNonresonantMiddleFrequencyRightEdge n K J T := by
  unfold h15BettinChandeeMiddleFrequencyRightEdge
    h15BettinChandeeResonantMiddleFrequencyRightEdge
    h15BettinChandeeNonresonantMiddleFrequencyRightEdge
  rw [h15BettinChandeeMiddleFrequencyIntegral_eq_resonant_add_nonresonant]
  ring

end NBMellinTools.NB12

namespace NBMellinTools.NB15

open NBMellinTools.NB12

/-- The certified energy with the complete correction retained in the low
sector and the finite middle window split at its exact direct-phase
resonances. -/
theorem h15CertifiedCoupledBoundaryEnergy_eq_lowEndpoint_add_resonant_add_nonresonant_add_high
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    h15CertifiedCoupledBoundaryEnergy n =
      h15CertifiedCorrectionCoupledLowEndpointSector n T +
        (h15BettinChandeeResonantMiddleFrequencyRightEdge n
          (h15CanonicalMiddleLowerCutoff n)
          (h15CanonicalMiddleWindowLength n) T).im +
        (h15BettinChandeeNonresonantMiddleFrequencyRightEdge n
          (h15CanonicalMiddleLowerCutoff n)
          (h15CanonicalMiddleWindowLength n) T).im +
        (h15HighFrequencyRightEdgeRemainder n
          (h15CanonicalMiddleUpperCutoff n) T).im := by
  rw [h15CertifiedCoupledBoundaryEnergy_eq_lowEndpoint_add_middle_add_high
    n T hT]
  rw [h15BettinChandeeMiddleFrequencyRightEdge_eq_resonant_add_nonresonant]
  simp only [Complex.add_im]
  ring

end NBMellinTools.NB15
