import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTSectorCoupling

/-!
# Common coordinates for the centered low MSTT sector

This file puts the low retained correction and the main-only low Vaaler
modes in the same `(m,n)` summand.  It is the finite-algebra completion of
the first follow-up priority for the sector-coupled strategy.

The resulting point kernel is

`(n/m) * (smooth(n/m) + endpoint(n/m)) - P_Q(n/m)`,

where `P_Q` is the nonzero Vaaler polynomial.  The full low residual is the
signed Möbius--von-Mangoldt sum of this kernel plus the linear coupled
remainder.  No analytic estimate for that sum is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowCommonCoordinates

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTCenteredGate
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTSectorCoupling
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTVariation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerAnalyticGate
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- The nonzero Vaaler polynomial evaluated at the rational point `n/m`. -/
noncomputable def ehmMSTTNonzeroVaalerPolynomial
    (V : VaalerSawtoothPackage) (Q n m : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h * ehmVaalerRationalPhase h n 1 m

/-- The common signed arithmetic coefficient of the low correction and the
normalized low Fourier modes. -/
noncomputable def ehmMSTTLowArithmeticWeight
    (X m n : ℕ) : ℂ :=
  (((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
    ehmDyadicLogTaperAverage X m *
    ArithmeticFunction.vonMangoldt n / (n : ℝ)) : ℝ) : ℂ)

/-- The exact point kernel left after the low smooth and endpoint correction
is centered against the nonzero Vaaler polynomial. -/
noncomputable def ehmMSTTLowCenteredPointKernel
    (V : VaalerSawtoothPackage) (Q n m : ℕ) : ℂ :=
  ((((n : ℝ) / (m : ℝ)) : ℝ) : ℂ) *
      ((ehmR1SmoothPart ((n : ℝ) / (m : ℝ)) +
        ehmR1IntegerEndpointPart ((n : ℝ) / (m : ℝ)) : ℝ) : ℂ) -
    ehmMSTTNonzeroVaalerPolynomial V Q n m

/-- For a zero-mean Vaaler package, the explicitly nonzero polynomial is
the package approximant at `n/m`. -/
theorem ehmMSTTNonzeroVaalerPolynomial_eq_approx
    (V : VaalerSawtoothPackage)
    (hV : VaalerSawtoothHasZeroCoefficient V)
    (Q n m : ℕ) :
    ehmMSTTNonzeroVaalerPolynomial V Q n m =
      vaalerSawtoothApprox V Q ((n : ℝ) / (m : ℝ)) := by
  classical
  unfold ehmMSTTNonzeroVaalerPolynomial vaalerSawtoothApprox
  rw [V.finite_fourier]
  have hphase : ∀ h : ℤ,
      ehmVaalerRationalPhase h n 1 m =
        vaalerFourierPhase h ((n : ℝ) / (m : ℝ)) := by
    intro h
    simp [ehmVaalerRationalPhase, div_eq_mul_inv]
  simp_rw [hphase]
  exact Finset.sum_erase (V.frequencies Q) (by simp [hV Q])

/-- The centered point kernel is exactly the original Ehm kernel, multiplied
by its argument, plus the Vaaler error.  This identity shows that centering
has not created a new independent small function: the remaining cancellation
is the original signed Ehm cancellation in explicit coordinates. -/
theorem ehmMSTTLowCenteredPointKernel_eq_r1_add_vaalerError
    (V : VaalerSawtoothPackage)
    (hV : VaalerSawtoothHasZeroCoefficient V)
    (Q n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ehmMSTTLowCenteredPointKernel V Q n m =
      ((((n : ℝ) / (m : ℝ)) : ℝ) : ℂ) *
      (ehmR1 ((n : ℝ) / (m : ℝ)) : ℂ) +
      vaalerSawtoothError V Q ((n : ℝ) / (m : ℝ)) := by
  unfold ehmMSTTLowCenteredPointKernel
  rw [ehmMSTTNonzeroVaalerPolynomial_eq_approx V hV]
  rw [ehmR1_eq_smooth_sub_bernoulli_add_endpoint]
  unfold ehmR1BernoulliSawtoothPart
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  rw [vaalerSawtooth_decomposition]
  field_simp [hnC, hmC]
  ring

/-- The complete low-sector residual in common `(m,n)` coordinates. -/
noncomputable def ehmMSTTLowCommonCoordinateResidual
    (V : VaalerSawtoothPackage) (Q X J Y : ℕ) : ℂ :=
  (∑ m ∈ Finset.Icc 1 (2 * X),
    ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
      ehmMSTTLowArithmeticWeight X m n *
        ehmMSTTLowCenteredPointKernel V Q n m) +
    ((∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N : ℝ) : ℂ)

/-- The original Ehm-kernel part exposed by the pointwise simplification. -/
noncomputable def ehmMSTTLowR1CoordinateSum
    (X J Y : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (2 * X),
    ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
      ehmMSTTLowArithmeticWeight X m n *
        (((((n : ℝ) / (m : ℝ)) : ℝ) : ℂ) *
          (ehmR1 ((n : ℝ) / (m : ℝ)) : ℂ))

/-- The pointwise Vaaler error left beside the original Ehm kernel. -/
noncomputable def ehmMSTTLowPointwiseVaalerErrorSum
    (V : VaalerSawtoothPackage) (Q X J Y : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (2 * X),
    ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
      ehmMSTTLowArithmeticWeight X m n *
        vaalerSawtoothError V Q ((n : ℝ) / (m : ℝ))

/-- The common-coordinate residual is exactly the original low Ehm kernel,
the pointwise Vaaler error, and the coupled linear remainder.  Thus the
centering route has exposed, rather than bypassed, the original signed
arithmetic cancellation. -/
theorem ehmMSTTLowCommonCoordinateResidual_eq_r1_add_error_add_remainder
    (V : VaalerSawtoothPackage)
    (hV : VaalerSawtoothHasZeroCoefficient V)
    (Q X J Y : ℕ) :
    ehmMSTTLowCommonCoordinateResidual V Q X J Y =
      ehmMSTTLowR1CoordinateSum X J Y +
        ehmMSTTLowPointwiseVaalerErrorSum V Q X J Y +
        ((∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N : ℝ) : ℂ) := by
  classical
  unfold ehmMSTTLowCommonCoordinateResidual
    ehmMSTTLowR1CoordinateSum
    ehmMSTTLowPointwiseVaalerErrorSum
  rw [← Finset.sum_add_distrib]
  apply congrArg₂ (· + ·) ?_ rfl
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := by
    have := (mem_ehmDyadicVaalerLowProductRange_iff J Y n).1 hn |>.1
    omega
  rw [ehmMSTTLowCenteredPointKernel_eq_r1_add_vaalerError
    V hV Q n m hnpos hmpos]
  ring

/-! ## Reindex the main-only modes -/

/-- The main-only low modes are exactly the common arithmetic weight times
the nonzero Vaaler polynomial. -/
theorem ehmMSTTMainLowProductModes_eq_commonCoordinates
    (V : VaalerSawtoothPackage) (Q X J Y : ℕ) :
    ehmMSTTMainLowProductModes V Q X J Y =
      ∑ m ∈ Finset.Icc 1 (2 * X),
        ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
          ehmMSTTLowArithmeticWeight X m n *
            ehmMSTTNonzeroVaalerPolynomial V Q n m := by
  classical
  unfold ehmMSTTMainLowProductModes
    ehmMSTTMainLowProductRowsMRange
    ehmMSTTMainLowProductRow
    ehmMSTTNonzeroVaalerPolynomial
    ehmMSTTLowArithmeticWeight
    ehmMSTTMainProductWeight
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro h _
  push_cast
  ring

/-! ## Reindex the retained low correction -/

/-- The low smooth and endpoint main correction has the same arithmetic
weight, multiplied by `(n/m)` to undo its normalized `1/n` form. -/
theorem ehmMSTTLowSectorRetainedCorrection_eq_commonCoordinates
    (X J Y : ℕ) :
    (ehmMSTTLowSectorRetainedCorrection X J Y : ℂ) =
      (∑ m ∈ Finset.Icc 1 (2 * X),
        ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
          ehmMSTTLowArithmeticWeight X m n *
            (((((n : ℝ) / (m : ℝ)) : ℝ) : ℂ) *
              ((ehmR1SmoothPart ((n : ℝ) / (m : ℝ)) +
                ehmR1IntegerEndpointPart
                  ((n : ℝ) / (m : ℝ)) : ℝ) : ℂ))) +
        ((∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N : ℝ) : ℂ) := by
  classical
  unfold ehmMSTTLowSectorRetainedCorrection
    ehmMSTTFullMainLowProductJointSum
  push_cast
  rw [← Finset.sum_add_distrib]
  apply congrArg₂ (· + ·) ?_ rfl
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := by
    have := (mem_ehmDyadicVaalerLowProductRange_iff J Y n).1 hn |>.1
    omega
  rw [ehmDyadicMobiusCutoffCoeff_eq_moebius_mul_average]
  unfold ehmMSTTLowArithmeticWeight
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  push_cast
  field_simp [hmC, hnC]

/-! ## The exact centered low target -/

/-- For the structural cutoff `Y <= X`, the low sector is exactly the common
coordinate residual.  This is the object whose centered block variation and
Taylor error must be estimated. -/
theorem ehmMSTTLowSectorCoupledResidual_eq_commonCoordinates
    (V : VaalerSawtoothPackage) (Q X J Y : ℕ) (hY : Y ≤ X) :
    ehmMSTTLowSectorCoupledResidual V Q X J Y =
      ehmMSTTLowCommonCoordinateResidual V Q X J Y := by
  rw [ehmMSTTLowSectorCoupledResidual_eq_main_of_cutoff_le
    V Q X J Y hY,
    ehmMSTTLowSectorRetainedCorrection_eq_commonCoordinates,
    ehmMSTTMainLowProductModes_eq_commonCoordinates]
  unfold ehmMSTTLowCommonCoordinateResidual
    ehmMSTTLowCenteredPointKernel
  push_cast
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

/-! ## Final common-coordinate interface -/

/-- The strongest current statement of the remaining analytic work.  Its
low bound refers directly to the explicit common-coordinate sum, while the
high sector and Vaaler error remain correction-coupled and common-cofinal. -/
structure EhmMSTTCommonCoordinateAnalyticGate where
  V : VaalerSawtoothPackage
  V_zero : VaalerSawtoothHasZeroCoefficient V
  degree : ℕ → ℕ → ℕ
  U : ℕ → ℕ
  U_le : ∀ X, U X ≤ 2 * X
  productCutoff : ℕ → ℕ → ℕ
  productCutoff_le : ∀ X J, productCutoff X J ≤ X
  etaLow : ℕ → ℝ
  etaLow_nonneg : ∀ X, 0 ≤ etaLow X
  etaLow_tendsto_zero : Tendsto etaLow atTop (nhds 0)
  etaHigh : ℕ → ℝ
  etaHigh_nonneg : ∀ X, 0 ≤ etaHigh X
  etaHigh_tendsto_zero : Tendsto etaHigh atTop (nhds 0)
  etaError : ℕ → ℝ
  etaError_nonneg : ∀ X, 0 ≤ etaError X
  etaError_tendsto_zero : Tendsto etaError atTop (nhds 0)
  cofinal_bounds : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |(ehmMSTTLowCommonCoordinateResidual V
        (degree X J) X J (productCutoff X J)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaLow X ∧
      |(ehmMSTTHighSectorCoupledResidual V
        (degree X J) X J (U X) (productCutoff X J)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaHigh X ∧
      |(ehmDyadicVaalerKernelNormalError V (degree X J) X
        (ehmExplicitFarCutoff X) J (U X)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaError X

/-- The explicit common-coordinate gate implies the sector-coupled gate. -/
noncomputable def EhmMSTTCommonCoordinateAnalyticGate.toSectorCoupled
    (H : EhmMSTTCommonCoordinateAnalyticGate) :
    EhmMSTTSectorCoupledAnalyticGate where
  V := H.V
  V_zero := H.V_zero
  degree := H.degree
  U := H.U
  U_le := H.U_le
  productCutoff := H.productCutoff
  productCutoff_le := H.productCutoff_le
  etaLow := H.etaLow
  etaLow_nonneg := H.etaLow_nonneg
  etaLow_tendsto_zero := H.etaLow_tendsto_zero
  etaHigh := H.etaHigh
  etaHigh_nonneg := H.etaHigh_nonneg
  etaHigh_tendsto_zero := H.etaHigh_tendsto_zero
  etaError := H.etaError
  etaError_nonneg := H.etaError_nonneg
  etaError_tendsto_zero := H.etaError_tendsto_zero
  cofinal_bounds X hX := by
    refine (H.cofinal_bounds X hX).mono ?_
    intro J hbounds
    refine ⟨hbounds.1, ?_, hbounds.2.2.1, hbounds.2.2.2⟩
    rw [ehmMSTTLowSectorCoupledResidual_eq_commonCoordinates
      H.V (H.degree X J) X J (H.productCutoff X J)
      (H.productCutoff_le X J)]
    exact hbounds.2.1

/-- Conditional Báez--Duarte closure from the explicit common-coordinate
low target, coupled high target, and Vaaler error. -/
theorem baezDuarteCriterion_of_ehmMSTTCommonCoordinateAnalyticGate
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmMSTTCommonCoordinateAnalyticGate) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmMSTTSectorCoupledAnalyticGate
    HS H.toSectorCoupled

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowCommonCoordinates
