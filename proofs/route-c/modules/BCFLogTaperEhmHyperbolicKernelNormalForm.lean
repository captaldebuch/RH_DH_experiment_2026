import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit

/-!
# Hyperbolic kernel normal form for the Ehm Type-I/II split

The near Möbius bilinear form is initially indexed by triples `(m,d,q)` with
the hyperbolic condition `d*q ≤ J`.  This file collapses the inner row to the
exact reciprocal kernel

```text
K(R₁; J,m,d) = ∑_{1 ≤ q ≤ J/d} R₁(q*d/m).
```

The resulting two-variable Type-I/II identity is finite and exact.  It uses
no estimate and, in particular, does not solve the remaining signed
cancellation problem.  The explicit polynomial conductor `D(X)=(X+1)^8`
from the far-tail module can now be substituted directly into this normal
form.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbolicKernelNormalForm

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCommonSplit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicFarTail
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit

/-! ## The collapsed reciprocal row -/

/-- The exact finite reciprocal `q`-kernel attached to one pair `(m,d)`. -/
noncomputable def ehmDyadicReciprocalQKernel
    (R1 : ℝ → ℝ) (J m d : ℕ) : ℝ :=
  ehmR1PartialSeries R1 (J / d) ((d : ℝ) / (m : ℝ))

/-- Collapsing `d*q ≤ J` is exactly the replacement `q ≤ J/d`. -/
theorem ehmDyadicHyperbolicRow_eq_reciprocalQKernel
    (R1 : ℝ → ℝ) (c : ℝ) (J m d : ℕ) (hd : 0 < d) :
    (∑ q ∈ Finset.Icc 1 J,
      if d * q ≤ J then
        c * R1 (((d * q : ℕ) : ℝ) / (m : ℝ))
      else 0) =
      c * ehmDyadicReciprocalQKernel R1 J m d := by
  have h := ehmFiniteHyperbolicRow_eq_partialSeries
    R1 c (1 / (m : ℝ)) d J hd
  simpa only [ehmDyadicReciprocalQKernel, div_eq_mul_inv,
    Nat.cast_mul, one_mul, mul_assoc] using h

/-! ## Two-variable Möbius normal form -/

/-- The near Möbius bilinear form after the exact `q`-row collapse. -/
noncomputable def ehmDyadicNearMobiusKernelMRange
    (R1 : ℝ → ℝ) (X D J mLo mHi : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)) / (m : ℝ)) *
      ehmDyadicNearPairAmplitude X m d *
        ehmDyadicReciprocalQKernel R1 J m d

/-- The triple hyperbolic sum and the two-variable kernel sum are exactly
equal on every `m` interval. -/
theorem ehmDyadicNearMobiusBilinearMRange_eq_kernelMRange
    (R1 : ℝ → ℝ) (X D J mLo mHi : ℕ) :
    ehmDyadicNearMobiusBilinearMRange R1 X D J mLo mHi =
      ehmDyadicNearMobiusKernelMRange R1 X D J mLo mHi := by
  classical
  unfold ehmDyadicNearMobiusBilinearMRange
    ehmDyadicNearMobiusKernelMRange
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro d hdmem
  have hd : 0 < d := by
    have hdlo := (Finset.mem_Icc.mp hdmem).1
    omega
  exact ehmDyadicHyperbolicRow_eq_reciprocalQKernel
    R1
      (((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) / (m : ℝ)) *
        ehmDyadicNearPairAmplitude X m d)
      J m d hd

/-- Type-I part in the collapsed kernel coordinates. -/
noncomputable def ehmDyadicNearKernelTypeI
    (R1 : ℝ → ℝ) (X D J U : ℕ) : ℝ :=
  ehmDyadicNearMobiusKernelMRange R1 X D J 1 U

/-- Type-II part in the collapsed kernel coordinates. -/
noncomputable def ehmDyadicNearKernelTypeII
    (R1 : ℝ → ℝ) (X D J U : ℕ) : ℝ :=
  ehmDyadicNearMobiusKernelMRange R1 X D J (U + 1) (2 * X)

/-- Exact identification of the original Type-I range with its kernel form. -/
theorem ehmDyadicNearTypeI_eq_kernelTypeI
    (R1 : ℝ → ℝ) (X D J U : ℕ) :
    ehmDyadicNearTypeI R1 X D J U =
      ehmDyadicNearKernelTypeI R1 X D J U := by
  exact ehmDyadicNearMobiusBilinearMRange_eq_kernelMRange
    R1 X D J 1 U

/-- Exact identification of the original Type-II range with its kernel form. -/
theorem ehmDyadicNearTypeII_eq_kernelTypeII
    (R1 : ℝ → ℝ) (X D J U : ℕ) :
    ehmDyadicNearTypeII R1 X D J U =
      ehmDyadicNearKernelTypeII R1 X D J U := by
  exact ehmDyadicNearMobiusBilinearMRange_eq_kernelMRange
    R1 X D J (U + 1) (2 * X)

/-- The indivisible coupled near core in the exact two-variable kernel
coordinates. -/
theorem ehmDyadicExplicitCoupledNearCore_eq_kernelTypeI_typeII
    (R1 : ℝ → ℝ) (X D J U : ℕ) (hU : U ≤ 2 * X) :
    ehmDyadicExplicitCoupledNearCore R1 X D J =
      ehmDyadicFullMainJointSum R1 X J +
        ehmDyadicNearKernelTypeI R1 X D J U +
        ehmDyadicNearKernelTypeII R1 X D J U +
        ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N := by
  rw [ehmDyadicExplicitCoupledNearCore_eq_typeI_typeII R1 X D J U hU,
    ehmDyadicNearTypeI_eq_kernelTypeI,
    ehmDyadicNearTypeII_eq_kernelTypeII]

/-! ## Explicit polynomial-conductor specialization -/

/-- The coupled near core at the proved polynomial far cutoff.  This is the
finite normal form to which a future signed Type-I/II estimate should apply. -/
theorem ehmDyadicExplicitCutoffCoupledNearCore_eq_kernelTypeI_typeII
    (R1 : ℝ → ℝ) (X J U : ℕ) (hU : U ≤ 2 * X) :
    ehmDyadicExplicitCoupledNearCore R1 X (ehmExplicitFarCutoff X) J =
      ehmDyadicFullMainJointSum R1 X J +
        ehmDyadicNearKernelTypeI R1 X (ehmExplicitFarCutoff X) J U +
        ehmDyadicNearKernelTypeII R1 X (ehmExplicitFarCutoff X) J U +
        ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N := by
  exact ehmDyadicExplicitCoupledNearCore_eq_kernelTypeI_typeII
    R1 X (ehmExplicitFarCutoff X) J U hU

/-! ## The fixed-conductor analytic gate -/

/-- The remaining signed estimate, now stated at the explicit conductor
`D(X)=(X+1)^8` and in the collapsed reciprocal-kernel coordinates.

All four coupled terms remain under one signed upper bound.  This structure
is intentionally not constructed in this file: its `cofinal_bound` field is
the genuine H15-strength arithmetic problem. -/
structure EhmDyadicExplicitKernelCoupledAnalyticGate where
  U : ℕ → ℕ
  U_le : ∀ X, U X ≤ 2 * X
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      (ehmDyadicFullMainJointSum ehmR1 X J +
          ehmDyadicNearKernelTypeI ehmR1 X
            (ehmExplicitFarCutoff X) J (U X) +
          ehmDyadicNearKernelTypeII ehmR1 X
            (ehmExplicitFarCutoff X) J (U X) +
          ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N) ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- The explicit kernel gate combines with the proved polynomial far-tail
bound to supply the established common-split closure interface. -/
noncomputable def EhmDyadicExplicitKernelCoupledAnalyticGate.toCommonSplit
    (H : EhmDyadicExplicitKernelCoupledAnalyticGate) :
    EhmDyadicCommonSplitSignedAverageVanishing where
  D := ehmExplicitFarCutoff
  D_ge := two_mul_le_ehmExplicitFarCutoff
  etaNear := H.eta
  etaNear_nonneg := H.eta_nonneg
  etaNear_tendsto_zero := H.eta_tendsto_zero
  etaFar := ehmExplicitFarEta
  etaFar_nonneg := ehmExplicitFarEta_nonneg
  etaFar_tendsto_zero := ehmExplicitFarEta_tendsto_zero
  near_cofinal_bound X hX :=
    (H.cofinal_bound X hX).mono fun J hJ ↦ by
      rw [ehmDyadicCommonNearCoreSum_eq_coupled,
        ehmDyadicExplicitCutoffCoupledNearCore_eq_kernelTypeI_typeII
          ehmR1 X J (H.U X) (H.U_le X)]
      exact hJ
  far_uniform_bound := fun X hX J hJ ↦
    ehmDyadicCommonDivisorTailMass_explicit_bound X J hX hJ

/-- Conditional closure from the precisely isolated fixed-conductor signed
kernel estimate.  No additional analytic assumption is introduced here. -/
theorem baezDuarteCriterion_of_ehmDyadicExplicitKernelCoupledAnalyticGate
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicExplicitKernelCoupledAnalyticGate) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicCommonSplitSignedAverage HS
    H.toCommonSplit

end RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbolicKernelNormalForm
