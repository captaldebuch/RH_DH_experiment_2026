import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPeriodicL2
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Coefficient-space convergence for Ehm's finite periodic sums

The `K`-th centered-sawtooth sum has, at a nonzero frequency `m`, one
contribution for every positive divisor of `|m|` which is at most `K`.
This module proves that the resulting truncated coefficient vectors converge
in `ℓ²(ℤ)` to Ehm's full divisor-coefficient vector, and hence that their
Fourier syntheses converge in circle `L²`.

Identifying these synthesized partial vectors with the concrete functions
`ehmPhi1Partial K` is deliberately left to the finite dilation theorem.  No
analytic tail estimate remains in that identification step.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmCoefficientConvergence

open Filter MeasureTheory Real AddCircle
open scoped BigOperators ENNReal Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPeriodicL2

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Number of positive divisors of `n` retained by the row cutoff `K`. -/
def ehmTruncatedDivisorCount (K n : ℕ) : ℕ :=
  (n.divisors.filter fun d => d ≤ K).card

/-- Positive-frequency amplitude produced by the rows `1 ≤ k ≤ K`. -/
noncomputable def ehmPartialPositiveComplexAmplitude (K n : ℕ) : ℝ :=
  (ehmTruncatedDivisorCount K (n + 1) : ℝ) /
    (2 * Real.pi * (n + 1 : ℝ))

/-- The exact truncated two-sided coefficient vector. -/
noncomputable def ehmPhi1PartialComplexFourierCoefficient (K : ℕ) : ℤ → ℂ
  | .ofNat 0 => 0
  | .ofNat (n + 1) => Complex.I * ehmPartialPositiveComplexAmplitude K n
  | .negSucc n => -Complex.I * ehmPartialPositiveComplexAmplitude K n

private theorem truncatedDivisorCount_le (K n : ℕ) :
    ehmTruncatedDivisorCount K n ≤ n.divisors.card := by
  exact Finset.card_filter_le _ _

private theorem truncatedDivisorCount_eq_card_of_le
    {K n : ℕ} (hn : 0 < n) (hnK : n ≤ K) :
    ehmTruncatedDivisorCount K n = n.divisors.card := by
  unfold ehmTruncatedDivisorCount
  congr 1
  ext d
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro hd
    refine ⟨hd, (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)).trans hnK⟩

private theorem partialAmplitude_nonneg (K n : ℕ) :
    0 ≤ ehmPartialPositiveComplexAmplitude K n := by
  unfold ehmPartialPositiveComplexAmplitude
  positivity

private theorem partialAmplitude_le (K n : ℕ) :
    ehmPartialPositiveComplexAmplitude K n ≤ ehmPositiveComplexAmplitude n := by
  unfold ehmPartialPositiveComplexAmplitude ehmPositiveComplexAmplitude
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast truncatedDivisorCount_le K (n + 1)) (by positivity)

private theorem partialAmplitude_eventually_eq (n : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      ehmPartialPositiveComplexAmplitude K n = ehmPositiveComplexAmplitude n := by
  filter_upwards [eventually_ge_atTop (n + 1)] with K hK
  unfold ehmPartialPositiveComplexAmplitude ehmPositiveComplexAmplitude
  rw [truncatedDivisorCount_eq_card_of_le (by omega) hK]

private theorem norm_partialCoefficient_le_full (K : ℕ) (m : ℤ) :
    ‖ehmPhi1PartialComplexFourierCoefficient K m‖ ≤
      ‖ehmPhi1ComplexFourierCoefficient m‖ := by
  cases m with
  | ofNat n => cases n with
    | zero => simp [ehmPhi1PartialComplexFourierCoefficient,
        ehmPhi1ComplexFourierCoefficient]
    | succ n =>
        simp only [ehmPhi1PartialComplexFourierCoefficient,
          ehmPhi1ComplexFourierCoefficient, norm_mul, Complex.norm_I,
          one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (partialAmplitude_nonneg K n)]
        rw [abs_of_nonneg (by
          unfold ehmPositiveComplexAmplitude
          positivity)]
        exact partialAmplitude_le K n
  | negSucc n =>
      simp only [ehmPhi1PartialComplexFourierCoefficient,
        ehmPhi1ComplexFourierCoefficient, norm_mul, norm_neg,
        Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (partialAmplitude_nonneg K n)]
      rw [abs_of_nonneg (by
        unfold ehmPositiveComplexAmplitude
        positivity)]
      exact partialAmplitude_le K n

theorem summable_norm_sq_ehmPhi1PartialComplexFourierCoefficient (K : ℕ) :
    Summable (fun m : ℤ =>
      ‖ehmPhi1PartialComplexFourierCoefficient K m‖ ^ 2) := by
  apply summable_norm_sq_ehmPhi1ComplexFourierCoefficient.of_nonneg_of_le
  · intro m
    positivity
  · intro m
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_partialCoefficient_le_full K m) 2

theorem ehmPhi1PartialComplexFourierCoefficient_memLp_two (K : ℕ) :
    Memℓp (ehmPhi1PartialComplexFourierCoefficient K) 2 := by
  apply memℓp_gen
  simpa using summable_norm_sq_ehmPhi1PartialComplexFourierCoefficient K

/-- Fourier synthesis of the exact divisor-truncated coefficient vector. -/
noncomputable def ehmPhi1CoefficientPartialL2 (K : ℕ) :
    Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance) :=
  (@fourierBasis 1 inferInstance).repr.symm
    (⟨ehmPhi1PartialComplexFourierCoefficient K,
      ehmPhi1PartialComplexFourierCoefficient_memLp_two K⟩ :
      lp (fun _ : ℤ => ℂ) 2)

theorem ehmPhi1CoefficientPartialL2_fourierCoefficient (K : ℕ) (m : ℤ) :
    fourierCoeff (ehmPhi1CoefficientPartialL2 K) m =
      ehmPhi1PartialComplexFourierCoefficient K m := by
  rw [← fourierBasis_repr]
  simp [ehmPhi1CoefficientPartialL2]

private theorem partialCoefficient_eventually_eq (m : ℤ) :
    ∀ᶠ K : ℕ in atTop,
      ehmPhi1PartialComplexFourierCoefficient K m =
        ehmPhi1ComplexFourierCoefficient m := by
  cases m with
  | ofNat n => cases n with
    | zero => simp [ehmPhi1PartialComplexFourierCoefficient,
        ehmPhi1ComplexFourierCoefficient]
    | succ n =>
        filter_upwards [partialAmplitude_eventually_eq n] with K hK
        simp [ehmPhi1PartialComplexFourierCoefficient,
          ehmPhi1ComplexFourierCoefficient, hK]
  | negSucc n =>
      filter_upwards [partialAmplitude_eventually_eq n] with K hK
      simp [ehmPhi1PartialComplexFourierCoefficient,
        ehmPhi1ComplexFourierCoefficient, hK]

private theorem norm_sub_partialCoefficient_le_full (K : ℕ) (m : ℤ) :
    ‖ehmPhi1PartialComplexFourierCoefficient K m -
        ehmPhi1ComplexFourierCoefficient m‖ ≤
      ‖ehmPhi1ComplexFourierCoefficient m‖ := by
  cases m with
  | ofNat n => cases n with
    | zero => simp [ehmPhi1PartialComplexFourierCoefficient,
        ehmPhi1ComplexFourierCoefficient]
    | succ n =>
        change ‖Complex.I * (ehmPartialPositiveComplexAmplitude K n : ℂ) -
            Complex.I * (ehmPositiveComplexAmplitude n : ℂ)‖ ≤
          ‖Complex.I * (ehmPositiveComplexAmplitude n : ℂ)‖
        rw [← mul_sub, norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul,
          ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
        rw [abs_of_nonpos (sub_nonpos.mpr (partialAmplitude_le K n))]
        rw [abs_of_nonneg (by unfold ehmPositiveComplexAmplitude; positivity)]
        linarith [partialAmplitude_nonneg K n]
  | negSucc n =>
      change ‖-Complex.I * (ehmPartialPositiveComplexAmplitude K n : ℂ) -
          -Complex.I * (ehmPositiveComplexAmplitude n : ℂ)‖ ≤
        ‖-Complex.I * (ehmPositiveComplexAmplitude n : ℂ)‖
      rw [← mul_sub, norm_mul, norm_mul, norm_neg, Complex.norm_I,
        one_mul, one_mul, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonpos (sub_nonpos.mpr (partialAmplitude_le K n))]
      rw [abs_of_nonneg (by unfold ehmPositiveComplexAmplitude; positivity)]
      linarith [partialAmplitude_nonneg K n]

private theorem tendsto_tsum_sq_coefficient_error_zero :
    Tendsto (fun K : ℕ => ∑' m : ℤ,
      ‖ehmPhi1PartialComplexFourierCoefficient K m -
        ehmPhi1ComplexFourierCoefficient m‖ ^ 2)
      atTop (nhds 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (𝓕 := atTop)
    summable_norm_sq_ehmPhi1ComplexFourierCoefficient
    (g := fun _ : ℤ => (0 : ℝ))
    (fun m => by
      apply tendsto_const_nhds.congr'
      filter_upwards [partialCoefficient_eventually_eq m] with K hK
      show (0 : ℝ) =
        ‖ehmPhi1PartialComplexFourierCoefficient K m -
          ehmPhi1ComplexFourierCoefficient m‖ ^ 2
      rw [hK, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
    (Eventually.of_forall fun K m =>
      (by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg
          ‖ehmPhi1PartialComplexFourierCoefficient K m -
            ehmPhi1ComplexFourierCoefficient m‖)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (norm_sub_partialCoefficient_le_full K m) 2))
  simpa using h

private theorem norm_sq_coefficientPartial_sub_periodic (K : ℕ) :
    ‖ehmPhi1CoefficientPartialL2 K - periodicEhmKernelL2‖ ^ 2 =
      ∑' m : ℤ,
        ‖ehmPhi1PartialComplexFourierCoefficient K m -
          ehmPhi1ComplexFourierCoefficient m‖ ^ 2 := by
  rw [← (@fourierBasis 1 inferInstance).repr.norm_map]
  rw [map_sub]
  have hpartial :
      (@fourierBasis 1 inferInstance).repr (ehmPhi1CoefficientPartialL2 K) =
        (⟨ehmPhi1PartialComplexFourierCoefficient K,
          ehmPhi1PartialComplexFourierCoefficient_memLp_two K⟩ :
          lp (fun _ : ℤ => ℂ) 2) := by
    simp [ehmPhi1CoefficientPartialL2]
  have hfull :
      (@fourierBasis 1 inferInstance).repr periodicEhmKernelL2 =
        (⟨ehmPhi1ComplexFourierCoefficient,
          ehmPhi1ComplexFourierCoefficient_memLp_two⟩ :
          lp (fun _ : ℤ => ℂ) 2) := by
    simp [periodicEhmKernelL2]
  rw [hpartial, hfull]
  have h := lp.norm_rpow_eq_tsum
    (p := (2 : ℝ≥0∞)) (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    ((⟨ehmPhi1PartialComplexFourierCoefficient K,
        ehmPhi1PartialComplexFourierCoefficient_memLp_two K⟩ :
        lp (fun _ : ℤ => ℂ) 2) -
      (⟨ehmPhi1ComplexFourierCoefficient,
        ehmPhi1ComplexFourierCoefficient_memLp_two⟩ :
        lp (fun _ : ℤ => ℂ) 2))
  norm_num at h
  simpa only [PiLp.sub_apply] using h

/-- The exact divisor-truncated Fourier syntheses converge in circle `L²`.
This discharges all square-summability and tail analysis required for Ehm's
finite functions; only their finite dilation/coefficient identity remains. -/
theorem ehmPhi1CoefficientPartialL2_tendsto :
    Tendsto ehmPhi1CoefficientPartialL2 atTop (nhds periodicEhmKernelL2) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsq := tendsto_tsum_sq_coefficient_error_zero
  rw [Metric.tendsto_nhds] at hsq
  filter_upwards [hsq (ε ^ 2) (sq_pos_of_pos hε)] with K hK
  rw [dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _ ) hε.le]
  rw [norm_sq_coefficientPartial_sub_periodic]
  have hnonneg : 0 ≤ ∑' m : ℤ,
      ‖ehmPhi1PartialComplexFourierCoefficient K m -
        ehmPhi1ComplexFourierCoefficient m‖ ^ 2 :=
    tsum_nonneg fun _ => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hK
  exact hK

end RH.Criteria.NymanBeurling.BCFLogTaperEhmCoefficientConvergence
