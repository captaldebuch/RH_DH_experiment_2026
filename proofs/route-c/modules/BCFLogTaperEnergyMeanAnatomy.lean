import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperCancellationAnatomy
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCompleteRowAbelDecay

/-!
# Exact anatomy of the remaining dyadic energy mean

The complete signed row-Abel route is already equivalent to a null dyadic
mean of the exact BCF log-taper energies.  This module removes the auxiliary
majorant from that statement and expands the resulting normalized mean into
its diagonal and signed compensating parts.

The diagonal mean is uniformly larger than one.  Consequently the remaining
analytic assertion is not decay of the off-diagonal, linear, or correction
terms separately: their complete signed dyadic mean must approach the
negative diagonal mean.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEnergyMeanAnatomy

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperCancellationAnatomy
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCompleteRowAbelDecay
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeTruncatedFormula
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- The inclusive dyadic block `[X, 2X]` contains exactly `X + 1` cutoffs. -/
theorem card_ehmDyadicNBlock (X : ℕ) :
    (ehmDyadicNBlock X).card = X + 1 := by
  simp only [ehmDyadicNBlock, Nat.card_Icc]
  omega

/-- The uniquely normalized dyadic mean of the exact BCF energies. -/
noncomputable def ehmDyadicExactEnergyMean (X : ℕ) : ℝ :=
  (∑ N ∈ ehmDyadicNBlock X, energy N) /
    ((ehmDyadicNBlock X).card : ℝ)

/-- The normalized positive diagonal contribution. -/
noncomputable def ehmDyadicDiagonalMean (X : ℕ) : ℝ :=
  (∑ N ∈ ehmDyadicNBlock X, gramDiagonal N) /
    ((ehmDyadicNBlock X).card : ℝ)

/-- The normalized, fully signed off-diagonal-plus-linear compensator. -/
noncomputable def ehmDyadicCompensatingMean (X : ℕ) : ℝ :=
  (∑ N ∈ ehmDyadicNBlock X, compensatingCorrelation N) /
    ((ehmDyadicNBlock X).card : ℝ)

theorem ehmDyadicNBlock_card_cast_pos (X : ℕ) :
    (0 : ℝ) < ((ehmDyadicNBlock X).card : ℝ) := by
  exact_mod_cast (ehmDyadicNBlock_nonempty X).card_pos

/-- The exact energy mean is nonnegative. -/
theorem ehmDyadicExactEnergyMean_nonneg (X : ℕ) :
    0 ≤ ehmDyadicExactEnergyMean X := by
  unfold ehmDyadicExactEnergyMean
  exact div_nonneg
    (Finset.sum_nonneg fun N _ ↦ energy_nonneg N)
    (ehmDyadicNBlock_card_cast_pos X).le

/-- The project-wide arithmetic mean and the Ehm block normalization are
literally the same function. -/
theorem ehmDyadicExactEnergyMean_eq_dyadicBlockEnergyMean (X : ℕ) :
    ehmDyadicExactEnergyMean X =
      RH.Criteria.NymanBeurling.BCFLogTaperCofinalEnergy.dyadicBlockEnergyMean
        energy X := by
  unfold ehmDyadicExactEnergyMean
  unfold RH.Criteria.NymanBeurling.BCFLogTaperCofinalEnergy.dyadicBlockEnergyMean
  rw [card_ehmDyadicNBlock]
  simp only [ehmDyadicNBlock, Nat.cast_add, Nat.cast_one]

/-- Exact normalized diagonal/compensator splitting.  Every correction is
retained inside the second summand. -/
theorem ehmDyadicExactEnergyMean_eq_diagonal_add_compensating (X : ℕ) :
    ehmDyadicExactEnergyMean X =
      ehmDyadicDiagonalMean X + ehmDyadicCompensatingMean X := by
  unfold ehmDyadicExactEnergyMean ehmDyadicDiagonalMean
    ehmDyadicCompensatingMean
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N _
  rw [RH.Criteria.NymanBeurling.BCFLogTaperGcd.energy_eq_gramQuadraticForm_add_linearCorrection,
    gramQuadraticForm_eq_diagonal_add_offDiagonal]
  unfold compensatingCorrelation
  ring

/-- The exact majorant-package target is equivalent to convergence of the
single normalized energy mean. -/
theorem nonempty_dyadicLogTaperEnergyMeanVanishing_iff_tendsto :
    Nonempty DyadicLogTaperEnergyMeanVanishing ↔
      Tendsto ehmDyadicExactEnergyMean atTop (nhds 0) := by
  constructor
  · rintro ⟨H⟩
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds H.eta_tendsto_zero
    · exact Eventually.of_forall ehmDyadicExactEnergyMean_nonneg
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
      have hcard := ehmDyadicNBlock_card_cast_pos X
      unfold ehmDyadicExactEnergyMean
      exact (div_le_iff₀ hcard).2 (by
        simpa [mul_comm] using H.sum_bound X hX)
  · intro hmean
    refine ⟨{
      eta := ehmDyadicExactEnergyMean
      eta_nonneg := ehmDyadicExactEnergyMean_nonneg
      eta_tendsto_zero := hmean
      sum_bound := ?_ }⟩
    intro X _
    have hcard_ne : ((ehmDyadicNBlock X).card : ℝ) ≠ 0 :=
      ne_of_gt (ehmDyadicNBlock_card_cast_pos X)
    unfold ehmDyadicExactEnergyMean
    rw [mul_comm, div_mul_cancel₀ _ hcard_ne]

/-- Complete signed row-Abel decay is therefore exactly a statement about
the normalized exact energy mean, with no auxiliary cutoff left. -/
theorem nonempty_completeRowAbelSignedDecay_iff_tendsto_energyMean
    (D : EhmPrimeDiscrepancyTruncatedModeData)
    (V : VaalerSawtoothPackage)
    (HS : EhmAutocorrelationR1RationalSeriesBridge) :
    Nonempty (EhmPrimeCompleteRowAbelSignedDecay D V) ↔
      Tendsto ehmDyadicExactEnergyMean atTop (nhds 0) := by
  rw [nonempty_ehmPrimeCompleteRowAbelSignedDecay_iff_energyMean D V HS]
  exact nonempty_dyadicLogTaperEnergyMeanVanishing_iff_tendsto

/-- The diagonal mean is uniformly larger than one on every nontrivial
dyadic block. -/
theorem one_lt_ehmDyadicDiagonalMean {X : ℕ} (hX : 2 ≤ X) :
    1 < ehmDyadicDiagonalMean X := by
  have hsum :
      (∑ _N ∈ ehmDyadicNBlock X, (1 : ℝ)) <
        ∑ N ∈ ehmDyadicNBlock X, gramDiagonal N := by
    exact Finset.sum_lt_sum_of_nonempty (ehmDyadicNBlock_nonempty X)
      (fun N hN ↦ one_lt_gramDiagonal
        (hX.trans (Finset.mem_Icc.mp hN).1))
  have hcard := ehmDyadicNBlock_card_cast_pos X
  unfold ehmDyadicDiagonalMean
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  exact (lt_div_iff₀ hcard).2 (by simpa [mul_comm] using hsum)

/-- The final mean-decay statement is exactly the signed compensation of
the nonvanishing diagonal mean. -/
theorem tendsto_energyMean_zero_iff_signed_diagonal_compensation :
    Tendsto ehmDyadicExactEnergyMean atTop (nhds 0) ↔
      Tendsto
        (fun X ↦ ehmDyadicDiagonalMean X + ehmDyadicCompensatingMean X)
        atTop (nhds 0) := by
  apply tendsto_congr'
  exact Eventually.of_forall fun X ↦
    ehmDyadicExactEnergyMean_eq_diagonal_add_compensating X

/-- In difference form, the signed compensator must asymptotically equal
the negative diagonal mean. -/
theorem tendsto_energyMean_zero_iff_compensator_matches_negative_diagonal :
    Tendsto ehmDyadicExactEnergyMean atTop (nhds 0) ↔
      Tendsto
        (fun X ↦ ehmDyadicCompensatingMean X -
          (-ehmDyadicDiagonalMean X)) atTop (nhds 0) := by
  simpa [sub_eq_add_neg, add_comm] using
    tendsto_energyMean_zero_iff_signed_diagonal_compensation

end RH.Criteria.NymanBeurling.BCFLogTaperEnergyMeanAnatomy
