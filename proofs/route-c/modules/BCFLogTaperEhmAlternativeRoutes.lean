import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
import RiemannHypothesis.Criteria.NymanBeurling.H15SawtoothAnalyticInterfaces

/-!
# Reciprocal-phase and cotangent compatibility for the coupled Ehm target

Ehm's elementary kernel uses the raw centered fractional part
`fract x - 1/2`.  The existing Vaaler package uses the endpoint-corrected
Bernoulli function `bernoulliB1`, which is zero at integers.  Their difference
is an exact integer-supported correction.  This file records that correction
inside the complete coupled near-core expression.

Consequently, a reciprocal-phase proof must control all three coupled terms:

* the smooth log--harmonic part together with the linear remainder;
* the endpoint-corrected Bernoulli/Vaaler part; and
* the divisibility-supported integer endpoint correction.

The file also records that the existing Vasyunin cotangent expression already
keeps its elementary bilinear pieces, cotangent bilinear, linear correction,
and constant coupled, and therefore gives a valid stronger closure route.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes

open scoped BigOperators
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicNearCoreReindex
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## Exact normalization of Ehm's sawtooth -/

/-- The smooth log--harmonic constituent of Ehm's elementary kernel. -/
noncomputable def ehmR1SmoothPart (x : ℝ) : ℝ :=
  Real.log x + Real.eulerMascheroniConstant - ehmHarmonic x

/-- The raw centered sawtooth quotient appearing literally in `ehmR1`. -/
noncomputable def ehmR1RawSawtoothPart (x : ℝ) : ℝ :=
  (Int.fract x - 1 / 2) / x

/-- The endpoint-corrected Bernoulli quotient compatible with the existing
Vaaler package. -/
noncomputable def ehmR1BernoulliSawtoothPart (x : ℝ) : ℝ :=
  bernoulliB1 x / x

/-- The exact correction at integer arguments, where `bernoulliB1` is zero
but the raw centered fractional part is `-1/2`. -/
noncomputable def ehmR1IntegerEndpointPart (x : ℝ) : ℝ :=
  (if Int.fract x = 0 then (1 : ℝ) / 2 else 0) / x

theorem ehmR1RawSawtoothPart_eq_bernoulli_sub_endpoint (x : ℝ) :
    ehmR1RawSawtoothPart x =
      ehmR1BernoulliSawtoothPart x - ehmR1IntegerEndpointPart x := by
  unfold ehmR1RawSawtoothPart ehmR1BernoulliSawtoothPart
    ehmR1IntegerEndpointPart
  rw [bernoulliB1_eq_fract_sub_half_add_indicator]
  ring

/-- Exact pointwise decomposition with the endpoint correction restored. -/
theorem ehmR1_eq_smooth_sub_bernoulli_add_endpoint (x : ℝ) :
    ehmR1 x =
      ehmR1SmoothPart x - ehmR1BernoulliSawtoothPart x +
        ehmR1IntegerEndpointPart x := by
  calc
    ehmR1 x = ehmR1SmoothPart x - ehmR1RawSawtoothPart x := by
      unfold ehmR1 ehmR1SmoothPart ehmR1RawSawtoothPart
      ring
    _ = _ := by
      rw [ehmR1RawSawtoothPart_eq_bernoulli_sub_endpoint]
      ring

/-! ## Linearity of the finite coupled kernel part -/

/-- The `R1`-dependent portion of the coupled near core.  The linear
remainder is deliberately excluded so it is inserted exactly once after a
kernel decomposition. -/
noncomputable def ehmDyadicCoupledKernelPart
    (R1 : ℝ → ℝ) (X D J : ℕ) : ℝ :=
  ehmDyadicFullMainJointSum R1 X J -
    ehmDyadicNearComplementaryJointSum R1 X D J

theorem ehmDyadicFullMainJointSum_add
    (R S : ℝ → ℝ) (X J : ℕ) :
    ehmDyadicFullMainJointSum (R + S) X J =
      ehmDyadicFullMainJointSum R X J +
        ehmDyadicFullMainJointSum S X J := by
  classical
  unfold ehmDyadicFullMainJointSum
  simp_rw [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ehmDyadicNearComplementaryJointSum_add
    (R S : ℝ → ℝ) (X D J : ℕ) :
    ehmDyadicNearComplementaryJointSum (R + S) X D J =
      ehmDyadicNearComplementaryJointSum R X D J +
        ehmDyadicNearComplementaryJointSum S X D J := by
  classical
  unfold ehmDyadicNearComplementaryJointSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hdq : d * q ≤ J
  · simp [hdq, Pi.add_apply]
    ring
  · simp [hdq]

theorem ehmDyadicCoupledKernelPart_add
    (R S : ℝ → ℝ) (X D J : ℕ) :
    ehmDyadicCoupledKernelPart (R + S) X D J =
      ehmDyadicCoupledKernelPart R X D J +
        ehmDyadicCoupledKernelPart S X D J := by
  unfold ehmDyadicCoupledKernelPart
  rw [ehmDyadicFullMainJointSum_add,
    ehmDyadicNearComplementaryJointSum_add]
  ring

theorem ehmDyadicCoupledKernelPart_neg
    (R : ℝ → ℝ) (X D J : ℕ) :
    ehmDyadicCoupledKernelPart (-R) X D J =
      -ehmDyadicCoupledKernelPart R X D J := by
  have hfull : ehmDyadicFullMainJointSum (-R) X J =
      -ehmDyadicFullMainJointSum R X J := by
    classical
    unfold ehmDyadicFullMainJointSum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp [Pi.neg_apply]
  have hnear : ehmDyadicNearComplementaryJointSum (-R) X D J =
      -ehmDyadicNearComplementaryJointSum R X D J := by
    classical
    unfold ehmDyadicNearComplementaryJointSum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hdq : d * q ≤ J
    · simp [hdq, Pi.neg_apply]
    · simp [hdq]
  unfold ehmDyadicCoupledKernelPart
  rw [hfull, hnear]
  ring

theorem ehmDyadicExplicitCoupledNearCore_eq_kernelPart_add_remainder
    (R1 : ℝ → ℝ) (X D J : ℕ) :
    ehmDyadicExplicitCoupledNearCore R1 X D J =
      ehmDyadicCoupledKernelPart R1 X D J +
        ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N := by
  rfl

/-- The exact reciprocal-phase-compatible decomposition of the indivisible
coupled target.  The endpoint term and the smooth-plus-linear term are both
mandatory. -/
theorem ehmDyadicExplicitCoupledNearCore_eq_reciprocalRoutePieces
    (X D J : ℕ) :
    ehmDyadicExplicitCoupledNearCore ehmR1 X D J =
      (ehmDyadicCoupledKernelPart ehmR1SmoothPart X D J +
        ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N) -
      ehmDyadicCoupledKernelPart ehmR1BernoulliSawtoothPart X D J +
      ehmDyadicCoupledKernelPart ehmR1IntegerEndpointPart X D J := by
  have hfun : ehmR1 =
      ehmR1SmoothPart + (-ehmR1BernoulliSawtoothPart) +
        ehmR1IntegerEndpointPart := by
    funext x
    simpa [Pi.neg_apply] using ehmR1_eq_smooth_sub_bernoulli_add_endpoint x
  rw [ehmDyadicExplicitCoupledNearCore_eq_kernelPart_add_remainder, hfun]
  rw [ehmDyadicCoupledKernelPart_add,
    ehmDyadicCoupledKernelPart_add,
    ehmDyadicCoupledKernelPart_neg]
  ring

/-! ## Route audit interfaces -/

/-- A reciprocal/Vaaler proof is compatible with the Ehm target only if its
reconstruction bounds the complete three-piece expression above.  This
interface deliberately does not accept a bound for the Bernoulli term alone. -/
structure EhmCoupledReciprocalRouteEstimate where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Filter.Tendsto eta Filter.atTop (nhds 0)
  cofinal_reconstructed_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in Filter.atTop,
      BCFLogTaperEhmDyadicFarTail.ehmDyadicUniformFarTailVanishing.D X ≤ J ∧
      ((ehmDyadicCoupledKernelPart ehmR1SmoothPart X
            (BCFLogTaperEhmDyadicFarTail.ehmDyadicUniformFarTailVanishing.D X) J +
          ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N) -
        ehmDyadicCoupledKernelPart ehmR1BernoulliSawtoothPart X
          (BCFLogTaperEhmDyadicFarTail.ehmDyadicUniformFarTailVanishing.D X) J +
        ehmDyadicCoupledKernelPart ehmR1IntegerEndpointPart X
          (BCFLogTaperEhmDyadicFarTail.ehmDyadicUniformFarTailVanishing.D X) J) ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- Exact reconstruction turns a valid reciprocal-route estimate into the
indivisible coupled target. -/
noncomputable def EhmCoupledReciprocalRouteEstimate.toCoupledNearCore
    (H : EhmCoupledReciprocalRouteEstimate) :
    BCFLogTaperEhmCoupledNearCoreTarget.EhmDyadicCoupledNearCoreSignedAverageVanishing where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  cofinal_bound X hX :=
    (H.cofinal_reconstructed_bound X hX).mono fun J hJ ↦ by
      rw [ehmDyadicExplicitCoupledNearCore_eq_reciprocalRoutePieces]
      exact hJ

/-- A reciprocal-phase proof which reconstructs all mandatory pieces closes
the verified dyadic Ehm route. -/
theorem baezDuarteCriterion_of_ehmCoupledReciprocalRoute
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmCoupledReciprocalRouteEstimate) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicCoupledNearCoreSignedAverage HS
    H.toCoupledNearCore

/-- The existing Vasyunin package already controls the complete pointwise
coupled expression, so it closes the criterion without discarding any
boundary or linear term. -/
theorem baezDuarteCriterion_of_vasyuninCoupledCancellation
    (H : VasyuninCoupledCancellationEstimate) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_spectralVanishing
    (spectralVanishingEstimate_of_coupledLogTaperCancellation
      H.toCoupledLogTaperProved)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
