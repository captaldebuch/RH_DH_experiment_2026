import RiemannHypothesis.Criteria.NymanBeurling.H15CenteredAggregateEstimate
import RiemannHypothesis.Criteria.NymanBeurling.AsymptoticEnergy

/-!
# H15 integrated-cancellation interface

This module records the minimal *null-decay* form of the existing centered H15
residual.  It does not claim a new estimate, a residue-free contour identity,
or a proof of RH.

The previous H15 interface asks for the stronger rate `O(1 / log^2 N)`.  A
vanishing bound is enough only after an explicit, weight-matched transfer from
the H15 residual to the finite Báez--Duarte approximation energy has been
proved.  The transfer and the forward Nyman--Beurling implication therefore
remain separate obligations; this module stops at the Báez--Duarte criterion.

The residual here is deliberately the existing `h15CenteredResidual`, with
the project's triangular cutoff.  It is *not* identified with the BCF
logarithmic-taper approximant without a separate exact Gram identity.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open Filter Topology
open RH.Criteria.NymanBeurling.BaezDuarte

/-- A null majorant for the exact centered H15 residual.  This is the weak
analytic endpoint sought by the integrated-cancellation programme; no rate is
built into the statement. -/
structure H15CenteredResidualDecay where
  eta : ℕ → ℝ
  eta_nonneg : ∀ N, 0 ≤ eta N
  eta_tendsto_zero : Tendsto eta atTop (𝓝 0)
  residual_bound : ∀ N, h15CenteredResidual N ≤ eta N

/-- The centered residual is nonnegative by construction. -/
theorem h15CenteredResidual_nonneg (N : ℕ) : 0 ≤ h15CenteredResidual N := by
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

/-- The abstract majorant immediately gives convergence of the exact centered
H15 residual. -/
theorem h15CenteredResidual_tendsto_zero
    (H : H15CenteredResidualDecay) :
    Tendsto h15CenteredResidual atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    H.eta_tendsto_zero h15CenteredResidual_nonneg H.residual_bound

/-- The established logarithmic-square H15 interface is stronger than the
null-decay interface.  The `log 2` factor handles the finitely small cutoffs
where `log (N + 2) < 1`. -/
noncomputable def h15CenteredResidualDecay_of_logSqBound
    (H : H15CenteredResidualBound) : H15CenteredResidualDecay := by
  let logTwo : ℝ := Real.log 2
  refine
    { eta := fun N => (H.C_residual / logTwo) / Real.log (N + 2 : ℝ)
      eta_nonneg := ?_
      eta_tendsto_zero := ?_
      residual_bound := ?_ }
  · intro N
    exact div_nonneg (div_nonneg H.C_residual_nonneg
      (Real.log_pos (by norm_num)).le)
      (Real.log_pos (by norm_cast; omega)).le
  · simpa [AsymptoticEnergy.logEnergyBound, logTwo] using
      (AsymptoticEnergy.logEnergyBound_tendsto_zero
        (C := H.C_residual / logTwo))
  · intro N
    have hlogTwo : 0 < logTwo := Real.log_pos (by norm_num)
    have hlogN : 0 < Real.log (N + 2 : ℝ) :=
      Real.log_pos (by norm_cast; omega)
    have hmono : logTwo ≤ Real.log (N + 2 : ℝ) := by
      dsimp [logTwo]
      exact Real.log_le_log (by norm_num) (by norm_cast; omega)
    have hratio :
        H.C_residual / Real.log (N + 2 : ℝ) ≤ H.C_residual / logTwo :=
      div_le_div_of_nonneg_left H.C_residual_nonneg hlogTwo hmono
    calc
      h15CenteredResidual N ≤
          H.C_residual / Real.log (N + 2 : ℝ) ^ 2 := H.residual_bound N
      _ = (H.C_residual / Real.log (N + 2 : ℝ)) /
          Real.log (N + 2 : ℝ) := by ring
      _ ≤ (H.C_residual / logTwo) / Real.log (N + 2 : ℝ) :=
        div_le_div_of_nonneg_right hratio hlogN.le

/-- The missing deterministic bridge for the integrated-cancellation route.

`linear_error` must contain every term not already represented by
`h15CenteredResidual`, and `distance_bound` must be proved for the *same*
coefficient family and cutoff weight.  In particular, this structure is not
an assertion that the current triangular-cutoff H15 residual equals the BCF
logarithmic-taper error. -/
structure H15ResidualToBaezDuarteEnergyTransfer where
  linear_error : ℕ → ℝ
  linear_error_tendsto_zero : Tendsto linear_error atTop (𝓝 0)
  distance_bound : ∀ N,
    BaezDuarteDistance N ≤ h15CenteredResidual N + linear_error N

/-- A residual null bound together with a proved transfer yields the
Báez--Duarte approximation criterion.  This statement has no hidden rate or
zero-simplicity hypothesis. -/
theorem baezDuarteCriterion_of_h15CenteredResidualDecay
    (H : H15CenteredResidualDecay)
    (T : H15ResidualToBaezDuarteEnergyTransfer) :
    BaezDuarteCriterion := by
  apply baezDuarteCriterion_of_certified_energy_sequence
    (fun N => h15CenteredResidual N + T.linear_error N)
  · exact T.distance_bound
  · simpa using
      (h15CenteredResidual_tendsto_zero H).add T.linear_error_tendsto_zero

end RH.Criteria.NymanBeurling.QuadraticInteraction
