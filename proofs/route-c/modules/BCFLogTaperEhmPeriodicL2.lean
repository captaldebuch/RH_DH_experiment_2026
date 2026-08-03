import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDivisorSquare
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The periodic `L²` object determined by Ehm's coefficients

Ehm's Proposition 5.1 gives the sine series

`φ₁(x) = - ∑_{m ≥ 1} d(m) / (π m) * sin (2 π m x)`.

For Mathlib's complex Fourier convention, the corresponding coefficient is
`I * d(m) / (2 π m)` at positive frequency `m` and its conjugate at negative
frequency.  In particular, the Parseval energy has a factor `1 / 2` relative
to the square of the displayed sine coefficient.

This module constructs the unique element of `L²(AddCircle 1)` with those
coefficients and proves its exact Parseval identity.  Identification of that
abstract `L²` element with the pointwise centered-fractional-part series is a
separate theorem; keeping the two claims separate prevents Fourier synthesis
from silently being used as pointwise convergence.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPeriodicL2

open MeasureTheory Real AddCircle
open scoped BigOperators ENNReal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDivisorSquare

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Half of the magnitude of the `m = n+1` sine coefficient. -/
noncomputable def ehmPositiveComplexAmplitude (n : ℕ) : ℝ :=
  ((n + 1).divisors.card : ℝ) / (2 * Real.pi * (n + 1 : ℝ))

/-- The correctly normalized, two-sided complex Fourier coefficients for
Ehm's formal sine series. -/
noncomputable def ehmPhi1ComplexFourierCoefficient : ℤ → ℂ
  | .ofNat 0 => 0
  | .ofNat (n + 1) => Complex.I * ehmPositiveComplexAmplitude n
  | .negSucc n => -Complex.I * ehmPositiveComplexAmplitude n

theorem summable_ehmPositiveComplexAmplitude_sq :
    Summable (fun n : ℕ => ehmPositiveComplexAmplitude n ^ 2) := by
  have h := divisorFunctionSquareSummable
  have hc := h.mul_left ((1 : ℝ) / (4 * Real.pi ^ 2))
  apply hc.congr
  intro n
  unfold ehmPositiveComplexAmplitude
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  push_cast
  ring

theorem norm_sq_ehmPhi1ComplexFourierCoefficient_ofNat_succ (n : ℕ) :
    ‖ehmPhi1ComplexFourierCoefficient (Int.ofNat (n + 1))‖ ^ 2 =
      ehmPositiveComplexAmplitude n ^ 2 := by
  change ‖Complex.I * (ehmPositiveComplexAmplitude n : ℂ)‖ ^ 2 =
    ehmPositiveComplexAmplitude n ^ 2
  have ha : 0 ≤ ehmPositiveComplexAmplitude n := by
    unfold ehmPositiveComplexAmplitude
    positivity
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ha]

theorem norm_sq_ehmPhi1ComplexFourierCoefficient_negSucc (n : ℕ) :
    ‖ehmPhi1ComplexFourierCoefficient (Int.negSucc n)‖ ^ 2 =
      ehmPositiveComplexAmplitude n ^ 2 := by
  change ‖-Complex.I * (ehmPositiveComplexAmplitude n : ℂ)‖ ^ 2 =
    ehmPositiveComplexAmplitude n ^ 2
  have ha : 0 ≤ ehmPositiveComplexAmplitude n := by
    unfold ehmPositiveComplexAmplitude
    positivity
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ha]

theorem summable_norm_sq_ehmPhi1ComplexFourierCoefficient :
    Summable (fun k : ℤ => ‖ehmPhi1ComplexFourierCoefficient k‖ ^ 2) := by
  apply Summable.of_add_one_of_neg_add_one
  · apply summable_ehmPositiveComplexAmplitude_sq.congr
    intro n
    exact (norm_sq_ehmPhi1ComplexFourierCoefficient_ofNat_succ n).symm
  · apply summable_ehmPositiveComplexAmplitude_sq.congr
    intro n
    exact (norm_sq_ehmPhi1ComplexFourierCoefficient_negSucc n).symm

theorem ehmPhi1ComplexFourierCoefficient_memLp_two :
    Memℓp ehmPhi1ComplexFourierCoefficient 2 := by
  apply memℓp_gen
  simpa using summable_norm_sq_ehmPhi1ComplexFourierCoefficient

/-- The canonical unit-periodic `L²` function synthesized from Ehm's formal
Fourier coefficients. -/
noncomputable def periodicEhmKernelL2 :
    Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance) :=
  (@fourierBasis 1 inferInstance).repr.symm
    (⟨ehmPhi1ComplexFourierCoefficient,
      ehmPhi1ComplexFourierCoefficient_memLp_two⟩ : lp (fun _ : ℤ => ℂ) 2)

/-- Fourier synthesis recovers every prescribed Ehm coefficient. -/
theorem periodicEhmKernelL2_fourierCoefficient (k : ℤ) :
    fourierCoeff periodicEhmKernelL2 k = ehmPhi1ComplexFourierCoefficient k := by
  rw [← fourierBasis_repr]
  simp [periodicEhmKernelL2]

theorem periodicEhmKernelL2_parseval :
    ∫ t : AddCircle 1, ‖periodicEhmKernelL2 t‖ ^ 2 ∂haarAddCircle =
      ∑' k : ℤ, ‖ehmPhi1ComplexFourierCoefficient k‖ ^ 2 := by
  rw [← tsum_sq_fourierCoeff periodicEhmKernelL2]
  congr 1
  funext k
  rw [periodicEhmKernelL2_fourierCoefficient]

private theorem coefficient_norm_sq_even :
    Function.Even (fun k : ℤ => ‖ehmPhi1ComplexFourierCoefficient k‖ ^ 2) := by
  intro k
  cases k with
  | ofNat n => cases n with
    | zero => simp [ehmPhi1ComplexFourierCoefficient]
    | succ n =>
        change ‖ehmPhi1ComplexFourierCoefficient (Int.negSucc n)‖ ^ 2 =
          ‖ehmPhi1ComplexFourierCoefficient (Int.ofNat (n + 1))‖ ^ 2
        rw [norm_sq_ehmPhi1ComplexFourierCoefficient_negSucc,
          norm_sq_ehmPhi1ComplexFourierCoefficient_ofNat_succ]
  | negSucc n =>
      change ‖ehmPhi1ComplexFourierCoefficient (Int.ofNat (n + 1))‖ ^ 2 =
        ‖ehmPhi1ComplexFourierCoefficient (Int.negSucc n)‖ ^ 2
      rw [norm_sq_ehmPhi1ComplexFourierCoefficient_ofNat_succ,
        norm_sq_ehmPhi1ComplexFourierCoefficient_negSucc]

theorem tsum_norm_sq_ehmPhi1ComplexFourierCoefficient :
    ∑' k : ℤ, ‖ehmPhi1ComplexFourierCoefficient k‖ ^ 2 =
      2 * ∑' n : ℕ+, ehmPositiveComplexAmplitude n.natPred ^ 2 := by
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat coefficient_norm_sq_even
    summable_norm_sq_ehmPhi1ComplexFourierCoefficient]
  simp only [ehmPhi1ComplexFourierCoefficient, norm_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, nsmul_eq_mul]
  congr 1
  apply tsum_congr
  intro n
  change ‖ehmPhi1ComplexFourierCoefficient (Int.ofNat n.val)‖ ^ 2 =
    ehmPositiveComplexAmplitude n.natPred ^ 2
  rw [← PNat.natPred_add_one n]
  exact norm_sq_ehmPhi1ComplexFourierCoefficient_ofNat_succ n.natPred

private theorem ehmPositiveComplexAmplitude_sq_eq (n : ℕ+) :
    ehmPositiveComplexAmplitude n.natPred ^ 2 =
      (1 / (4 * Real.pi ^ 2)) *
        ((n.val.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
  unfold ehmPositiveComplexAmplitude
  rw [PNat.natPred_add_one]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hn : (n : ℝ) = (n.natPred : ℝ) + 1 := by
    exact_mod_cast (PNat.natPred_add_one n).symm
  field_simp
  nlinarith

/-- Corrected Parseval normalization.  Because Ehm's displayed coefficient
is a sine coefficient, the complex Fourier energy is half the sum of its
squares. -/
theorem periodicEhmKernelL2_energy_divisorSeries :
    ∫ t : AddCircle 1, ‖periodicEhmKernelL2 t‖ ^ 2 ∂haarAddCircle =
      (1 / (2 * Real.pi ^ 2)) *
        ∑' n : ℕ+, ((n.val.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
  rw [periodicEhmKernelL2_parseval,
    tsum_norm_sq_ehmPhi1ComplexFourierCoefficient]
  rw [tsum_congr ehmPositiveComplexAmplitude_sq_eq, tsum_mul_left]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPeriodicL2
