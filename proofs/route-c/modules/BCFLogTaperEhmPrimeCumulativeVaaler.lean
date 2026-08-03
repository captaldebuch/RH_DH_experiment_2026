import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeTaper
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift

/-!
# Vaaler lift of the cumulative prime transform

This module lifts the exact smooth--Bernoulli--endpoint decomposition of
Ehm's `R₁` kernel through the cumulative outer taper.  Only the Bernoulli
piece is Fourier expanded.  The smooth and integer-endpoint pieces remain
explicit, so the retained correction is not discarded by a termwise bound.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeVaaler

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimePrefixCollapse
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeRemainderKernel
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- The arithmetic coefficient in the cumulative prime transform. -/
noncomputable def ehmPrimeCumulativeMobiusCoeff
    (X k m : ℕ) : ℂ :=
  ((((ArithmeticFunction.moebius m : ℤ) : ℝ) / (m : ℝ) : ℝ) : ℂ) *
    (ehmPrimeCumulativeOuterTaper X k m : ℂ)

/-- A generic kernel transformed by the cumulative logarithmic taper. -/
noncomputable def ehmPrimeCumulativeKernelTransform
    (R : ℝ → ℝ) (X k : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (2 * X),
    ehmPrimeCumulativeMobiusCoeff X k m *
      (R (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ)

/-- The filtered `R₁` kernel is the generic cumulative transform. -/
theorem ehmPrimeFilteredR1Kernel_eq_kernelTransform (X k : ℕ) :
    ehmPrimeFilteredR1Kernel X k =
      ehmPrimeCumulativeKernelTransform ehmR1 X k := by
  rw [ehmPrimeFilteredR1Kernel_eq_cumulativeMobius]
  rfl

/-- The cumulative transform is additive in its kernel. -/
theorem ehmPrimeCumulativeKernelTransform_add
    (R S : ℝ → ℝ) (X k : ℕ) :
    ehmPrimeCumulativeKernelTransform (R + S) X k =
      ehmPrimeCumulativeKernelTransform R X k +
        ehmPrimeCumulativeKernelTransform S X k := by
  classical
  unfold ehmPrimeCumulativeKernelTransform
  simp_rw [Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]

/-- The cumulative transform commutes with negation. -/
theorem ehmPrimeCumulativeKernelTransform_neg
    (R : ℝ → ℝ) (X k : ℕ) :
    ehmPrimeCumulativeKernelTransform (-R) X k =
      -ehmPrimeCumulativeKernelTransform R X k := by
  classical
  unfold ehmPrimeCumulativeKernelTransform
  simp_rw [Pi.neg_apply, Complex.ofReal_neg, mul_neg, Finset.sum_neg_distrib]

/-- Exact reconstruction of the cumulative `R₁` transform. -/
theorem ehmPrimeCumulativeKernelTransform_R1_eq_threePieces
    (X k : ℕ) :
    ehmPrimeCumulativeKernelTransform ehmR1 X k =
      ehmPrimeCumulativeKernelTransform ehmR1SmoothPart X k -
        ehmPrimeCumulativeKernelTransform ehmR1BernoulliSawtoothPart X k +
          ehmPrimeCumulativeKernelTransform ehmR1IntegerEndpointPart X k := by
  have hfun : ehmR1 =
      ehmR1SmoothPart + (-ehmR1BernoulliSawtoothPart) +
        ehmR1IntegerEndpointPart := by
    funext x
    simpa [Pi.neg_apply] using ehmR1_eq_smooth_sub_bernoulli_add_endpoint x
  rw [hfun, ehmPrimeCumulativeKernelTransform_add,
    ehmPrimeCumulativeKernelTransform_add,
    ehmPrimeCumulativeKernelTransform_neg]
  ring

/-- The Vaaler approximant in the cumulative-taper coordinates. -/
noncomputable def ehmPrimeCumulativeVaalerApprox
    (V : VaalerSawtoothPackage) (H X k : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (2 * X),
    ehmPrimeCumulativeMobiusCoeff X k m *
      ehmVaalerBernoulliPointApprox V H (k + 1) m

/-- The accumulated pointwise Vaaler error with the same signed coefficient. -/
noncomputable def ehmPrimeCumulativeVaalerError
    (V : VaalerSawtoothPackage) (H X k : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (2 * X),
    ehmPrimeCumulativeMobiusCoeff X k m *
      ehmVaalerBernoulliPointError V H (k + 1) m

/-- Exact Vaaler lift of the Bernoulli piece through the cumulative taper. -/
theorem ehmPrimeCumulativeBernoulli_eq_vaaler
    (V : VaalerSawtoothPackage) (H X k : ℕ) :
    ehmPrimeCumulativeKernelTransform ehmR1BernoulliSawtoothPart X k =
      ehmPrimeCumulativeVaalerApprox V H X k +
        ehmPrimeCumulativeVaalerError V H X k := by
  classical
  unfold ehmPrimeCumulativeKernelTransform
    ehmPrimeCumulativeVaalerApprox ehmPrimeCumulativeVaalerError
  calc
    (∑ m ∈ Finset.Icc 1 (2 * X),
        ehmPrimeCumulativeMobiusCoeff X k m *
          (ehmR1BernoulliSawtoothPart
            (((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℂ)) =
      ∑ m ∈ Finset.Icc 1 (2 * X),
        ehmPrimeCumulativeMobiusCoeff X k m *
          (ehmVaalerBernoulliPointApprox V H (k + 1) m +
            ehmVaalerBernoulliPointError V H (k + 1) m) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [ehmR1BernoulliSawtoothPart_natRatio_eq_vaaler]
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib]

/-- One reciprocal character of the cumulative prime transform. -/
noncomputable def ehmPrimeCumulativePhaseForm
    (h : ℤ) (X k : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (2 * X),
    ehmPrimeCumulativeMobiusCoeff X k m *
      ehmVaalerRationalPhase h (k + 1) 1 m /
        (((((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℝ) : ℂ)

/-- Frequency-first form of the cumulative Vaaler polynomial. -/
theorem ehmPrimeCumulativeVaalerApprox_eq_frequencySum
    (V : VaalerSawtoothPackage) (H X k : ℕ) :
    ehmPrimeCumulativeVaalerApprox V H X k =
      ∑ h ∈ V.frequencies H,
        V.coefficient H h * ehmPrimeCumulativePhaseForm h X k := by
  classical
  unfold ehmPrimeCumulativeVaalerApprox
    ehmVaalerBernoulliPointApprox ehmPrimeCumulativePhaseForm
  calc
    (∑ m ∈ Finset.Icc 1 (2 * X),
        ehmPrimeCumulativeMobiusCoeff X k m *
          ∑ h ∈ V.frequencies H,
            V.coefficient H h *
              ehmVaalerRationalPhase h (k + 1) 1 m /
                (((((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℝ) : ℂ)) =
      ∑ m ∈ Finset.Icc 1 (2 * X),
        ∑ h ∈ V.frequencies H,
          ehmPrimeCumulativeMobiusCoeff X k m *
            (V.coefficient H h *
              ehmVaalerRationalPhase h (k + 1) 1 m /
                (((((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℝ) : ℂ)) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ h ∈ V.frequencies H,
        ∑ m ∈ Finset.Icc 1 (2 * X),
          ehmPrimeCumulativeMobiusCoeff X k m *
            (V.coefficient H h *
              ehmVaalerRationalPhase h (k + 1) 1 m /
                (((((k + 1 : ℕ) : ℝ) / (m : ℝ)) : ℝ) : ℂ)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring

/-- The interior prime prefix with all correction-bearing pieces retained.
The only Fourier-expanded term is the Bernoulli sawtooth contribution. -/
theorem ehmPrimeDyadicAbelKernelPrefix_eq_cumulativeVaaler
    (V : VaalerSawtoothPackage) (H X J k : ℕ)
    (hJ : 2 * X ≤ J) (hkX : X ≤ k) (hkJ : k < J) :
    ehmPrimeDyadicAbelKernelPrefix X J k =
      -ehmPrimeCumulativeKernelTransform ehmR1SmoothPart X k +
        ehmPrimeCumulativeVaalerApprox V H X k +
          ehmPrimeCumulativeVaalerError V H X k -
            ehmPrimeCumulativeKernelTransform ehmR1IntegerEndpointPart X k := by
  rw [ehmPrimeDyadicAbelKernelPrefix_eq_cumulativeMobius X J k hJ hkX hkJ]
  change -ehmPrimeCumulativeKernelTransform ehmR1 X k = _
  rw [ehmPrimeCumulativeKernelTransform_R1_eq_threePieces]
  rw [ehmPrimeCumulativeBernoulli_eq_vaaler]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeVaaler
