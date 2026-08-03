import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmReciprocalTaylor

/-!
# MSTT reduction for the low-product Ehm rows

This module applies the polynomial-phase interface column by column to the
exact low-product truncation of the paired Ehm row.  For each fixed Vaaler
frequency `h` and product coordinate `n`, the outer Möbius variable is the
MSTT variable.  The reciprocal phase `e(h*n/m)` is replaced by its Taylor
polynomial on `(X,X+H]`, and the paired main-plus-near coefficient remains
one complex weight.

The resulting estimate has two explicit losses:

* the discrete variation of the complete paired weight in `m`;
* the accumulated reciprocal Taylor phase error.

Bounding those losses uniformly, and summing them over the retained
frequencies and product coordinates together with the correction terms,
remains an analytic obligation.  No MSTT instance or H15 closure is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation
open RH.Criteria.NymanBeurling.BCFLogTaperMSTTPolynomialPhase
open RH.Criteria.NymanBeurling.BCFLogTaperEhmReciprocalTaylor

/-! ## Fixed product-coordinate columns -/

/-- The complete paired main-plus-near amplitude at fixed product
coordinate `n`, without the outer Möbius factor or reciprocal phase. -/
noncomputable def ehmMSTTLowProductWeight
    (N D n m : ℕ) : ℂ :=
  ((ehmDyadicVaalerPairedProductCoefficient N D m n /
    (n : ℝ) : ℝ) : ℂ)

/-- One exact reciprocal-phase column on the outer block `(X,X+H]`. -/
noncomputable def ehmMSTTLowProductColumn
    (h : ℤ) (N D n X H : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc X (X + H),
    (((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmVaalerRationalPhase h n 1 m) *
        ehmMSTTLowProductWeight N D n m)

/-- The polynomialized version of one reciprocal column. -/
noncomputable def ehmMSTTLowProductPolynomialColumn
    (h : ℤ) (N D n X H K : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc X (X + H),
    (((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      msttPolynomialPhase
        (reciprocalTaylorPolynomial
          ((h : ℝ) * (n : ℝ)) (X : ℝ) K) m) *
        ehmMSTTLowProductWeight N D n m)

/-- The exact columnwise Taylor error, retaining the paired weight before
taking any norm. -/
noncomputable def ehmMSTTLowProductTaylorErrorColumn
    (h : ℤ) (N D n X H K : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc X (X + H),
    (((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmMSTTLowProductWeight N D n m) *
        (ehmVaalerRationalPhase h n 1 m -
          msttPolynomialPhase
            (reciprocalTaylorPolynomial
              ((h : ℝ) * (n : ℝ)) (X : ℝ) K) m))

/-- Exact reciprocal column equals its polynomialized column plus the
explicit Taylor-error column. -/
theorem ehmMSTTLowProductColumn_eq_polynomial_add_error
    (h : ℤ) (N D n X H K : ℕ) :
    ehmMSTTLowProductColumn h N D n X H =
      ehmMSTTLowProductPolynomialColumn h N D n X H K +
        ehmMSTTLowProductTaylorErrorColumn h N D n X H K := by
  classical
  unfold ehmMSTTLowProductColumn ehmMSTTLowProductPolynomialColumn
    ehmMSTTLowProductTaylorErrorColumn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-! ## Polynomial and Taylor-error estimates -/

/-- Direct MSTT bound for the polynomialized fixed-`n` column.  The full
paired coefficient appears only through its exact discrete variation. -/
theorem norm_ehmMSTTLowProductPolynomialColumn_le
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (h : ℤ) (N D n : ℕ)
    (logSaving K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X H : ℕ)
    (hthreshold : HM.threshold K logSaving epsilon ≤ X)
    (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hHlower :
      Real.rpow (X : ℝ) ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ))
    (hHupper :
      (H : ℝ) ≤ Real.rpow (X : ℝ) (1 - epsilon)) :
    ‖ehmMSTTLowProductPolynomialColumn h N D n X H K‖ ≤
      (HM.constant K logSaving epsilon * (H : ℝ) /
          (Real.log (X : ℝ)) ^ logSaving) *
        complexWeightVariation
          (ehmMSTTLowProductWeight N D n) (X + 1) (X + H) := by
  unfold ehmMSTTLowProductPolynomialColumn
  exact norm_weighted_msttMobiusPolynomialBlock_le HM K logSaving
    epsilon hepsilon X H hthreshold hX hH hHlower hHupper
    (reciprocalTaylorPolynomial
      ((h : ℝ) * (n : ℝ)) (X : ℝ) K)
    (reciprocalTaylorPolynomial_natDegree_le _ _ _) _

/-- Explicit unsigned Taylor-error mass for one fixed product column. -/
noncomputable def ehmMSTTLowProductTaylorErrorMajorant
    (h : ℤ) (N D n X H K : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc X (X + H),
    ‖(((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmMSTTLowProductWeight N D n m))‖ *
        (2 * Real.pi *
          |reciprocalTaylorRemainder
            ((h : ℝ) * (n : ℝ)) (X : ℝ) K
              ((m : ℝ) - (X : ℝ))|)

theorem norm_ehmMSTTLowProductTaylorErrorColumn_le
    (h : ℤ) (N D n X H K : ℕ) (hX : 1 ≤ X) :
    ‖ehmMSTTLowProductTaylorErrorColumn h N D n X H K‖ ≤
      ehmMSTTLowProductTaylorErrorMajorant h N D n X H K := by
  classical
  unfold ehmMSTTLowProductTaylorErrorColumn
    ehmMSTTLowProductTaylorErrorMajorant
  calc
    ‖∑ m ∈ Finset.Ioc X (X + H),
        (((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          ehmMSTTLowProductWeight N D n m) *
            (ehmVaalerRationalPhase h n 1 m -
              msttPolynomialPhase
                (reciprocalTaylorPolynomial
                  ((h : ℝ) * (n : ℝ)) (X : ℝ) K) m))‖ ≤
      ∑ m ∈ Finset.Ioc X (X + H),
        ‖(((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          ehmMSTTLowProductWeight N D n m) *
            (ehmVaalerRationalPhase h n 1 m -
              msttPolynomialPhase
                (reciprocalTaylorPolynomial
                  ((h : ℝ) * (n : ℝ)) (X : ℝ) K) m))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Ioc X (X + H),
        ‖(((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          ehmMSTTLowProductWeight N D n m))‖ *
            (2 * Real.pi *
              |reciprocalTaylorRemainder
                ((h : ℝ) * (n : ℝ)) (X : ℝ) K
                  ((m : ℝ) - (X : ℝ))|) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hmpos : 0 < m := by
        have hXm := (Finset.mem_Ioc.mp hm).1
        omega
      exact norm_ehmVaalerRationalPhase_sub_reciprocalTaylor_le
        h n m K (X : ℝ) (by exact_mod_cast (show X ≠ 0 by omega)) hmpos.ne'

/-- Combined fixed-column estimate after polynomialization. -/
theorem norm_ehmMSTTLowProductColumn_le
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (h : ℤ) (N D n : ℕ)
    (logSaving K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X H : ℕ)
    (hthreshold : HM.threshold K logSaving epsilon ≤ X)
    (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hHlower :
      Real.rpow (X : ℝ) ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ))
    (hHupper :
      (H : ℝ) ≤ Real.rpow (X : ℝ) (1 - epsilon)) :
    ‖ehmMSTTLowProductColumn h N D n X H‖ ≤
      (HM.constant K logSaving epsilon * (H : ℝ) /
          (Real.log (X : ℝ)) ^ logSaving) *
        complexWeightVariation
          (ehmMSTTLowProductWeight N D n) (X + 1) (X + H) +
      ehmMSTTLowProductTaylorErrorMajorant h N D n X H K := by
  rw [ehmMSTTLowProductColumn_eq_polynomial_add_error]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_ehmMSTTLowProductPolynomialColumn_le HM h N D n
      logSaving K epsilon hepsilon X H hthreshold hX hH hHlower hHupper)
    (norm_ehmMSTTLowProductTaylorErrorColumn_le h N D n X H K
      (by omega)))

/-! ## Reconstruction of the complete low-product block -/

/-- The low-product paired rows restricted to the outer block `(X,X+H]`. -/
noncomputable def ehmMSTTLowProductRowsBlock
    (h : ℤ) (N D J Y X H : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc X (X + H),
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmDyadicVaalerPairedLowProductRow h N D J Y m)

/-- Exact exchange of the finite outer block and low-product coordinate
sums. -/
theorem ehmMSTTLowProductRowsBlock_eq_sum_columns
    (h : ℤ) (N D J Y X H : ℕ) :
    ehmMSTTLowProductRowsBlock h N D J Y X H =
      ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
        ehmMSTTLowProductColumn h N D n X H := by
  classical
  unfold ehmMSTTLowProductRowsBlock ehmMSTTLowProductColumn
    ehmDyadicVaalerPairedLowProductRow
    ehmDyadicVaalerPairedProductSummand ehmMSTTLowProductWeight
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- MSTT-plus-Taylor bound for the full retained low-product row on one
outer block.  The right side displays exactly the variation and Taylor
error masses still to be estimated. -/
theorem norm_ehmMSTTLowProductRowsBlock_le
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (h : ℤ) (N D J Y : ℕ)
    (logSaving K : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X H : ℕ)
    (hthreshold : HM.threshold K logSaving epsilon ≤ X)
    (hX : 3 ≤ X) (hH : 1 ≤ H)
    (hHlower :
      Real.rpow (X : ℝ) ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ))
    (hHupper :
      (H : ℝ) ≤ Real.rpow (X : ℝ) (1 - epsilon)) :
    ‖ehmMSTTLowProductRowsBlock h N D J Y X H‖ ≤
      ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
        ((HM.constant K logSaving epsilon * (H : ℝ) /
            (Real.log (X : ℝ)) ^ logSaving) *
          complexWeightVariation
            (ehmMSTTLowProductWeight N D n) (X + 1) (X + H) +
          ehmMSTTLowProductTaylorErrorMajorant h N D n X H K) := by
  rw [ehmMSTTLowProductRowsBlock_eq_sum_columns]
  calc
    ‖∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
        ehmMSTTLowProductColumn h N D n X H‖ ≤
      ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
        ‖ehmMSTTLowProductColumn h N D n X H‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n _
      exact norm_ehmMSTTLowProductColumn_le HM h N D n
        logSaving K epsilon hepsilon X H hthreshold hX hH hHlower hHupper

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows
