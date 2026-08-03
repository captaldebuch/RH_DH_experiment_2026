import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperCofinalEnergy
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDispersionBlocks

/-!
# Double-cofinal closure of the finite Ehm boundary

The all-`N` power-law boundary estimate is stronger than the
Báez--Duarte criterion requires.  This module isolates the genuinely weaker
two-level target:

* for every positive accuracy and every lower cutoff `N₀`, choose one
  `N >= N₀`;
* at that fixed `N`, the fully coupled finite Ehm boundary is small at
  arbitrarily late hyperbolic cutoffs `J`.

Fixed-`N` convergence in `J` transfers the cofinal finite bound to the exact
Ehm expression.  The exact Ehm identity then makes the log-taper energy
small at arbitrarily large `N`, which is precisely the cofinal-energy
criterion.  No rate in `N` and no estimate at every `N` are introduced.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperCofinalEnergy
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmComplementarySector
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDispersionBlocks
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral

/-- The minimal two-level cofinal finite-boundary target.  The existential
choice of `N` may depend on both `ε` and `N₀`; the good hyperbolic cutoffs
need only be cofinal for that chosen `N`. -/
structure EhmDoubleCofinalBoundaryVanishing (R1 : ℝ → ℝ) where
  cofinally_small : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
    ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
      ∃ᶠ J : ℕ in atTop,
        |ehmFiniteCoupledBoundaryExpression R1 N J| < ε

/-- The double-cofinal finite condition passes through the fixed-`N`
rational Ehm series limit.  This conclusion is still merely cofinal in
`N`; it does not assert convergence of the exact expression at every
cutoff. -/
theorem ehmCoupledExpression_cofinally_small_of_doubleCofinal
    (H : EhmKernelPackage)
    (HS : EhmR1RationalSeriesBridge H.S1 H.R1)
    (HB : EhmDoubleCofinalBoundaryVanishing H.R1) :
    ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
      ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
        |ehmInversionError H.S1 H.R1 N + ehmCoupledRemainder N| < ε := by
  intro ε hε N₀
  rcases HB.cofinally_small (ε / 2) (half_pos hε) N₀ with
    ⟨N, hN₀, hN, hfreq⟩
  refine ⟨N, hN₀, hN, ?_⟩
  have hle :
      |ehmInversionError H.S1 H.R1 N + ehmCoupledRemainder N| ≤ ε / 2 := by
    apply abs_limit_le_of_tendsto_of_frequently_abs_le
      (ehmFiniteCoupledBoundaryExpression_tendsto_of_rational HS N hN)
    exact hfreq.mono fun J hJ ↦ hJ.le
  exact hle.trans_lt (half_lt_self hε)

/-- Consequently the exact coupled GCD-ratio expression is arbitrarily
small at arbitrarily large outer cutoffs. -/
theorem coupledGcdRatioExpression_cofinally_small_of_doubleCofinal
    (H : EhmKernelPackage)
    (HS : EhmR1RationalSeriesBridge H.S1 H.R1)
    (HB : EhmDoubleCofinalBoundaryVanishing H.R1) :
    ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
      ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
        |coupledGcdRatioExpression N| < ε := by
  intro ε hε N₀
  rcases ehmCoupledExpression_cofinally_small_of_doubleCofinal
    H HS HB ε hε N₀ with ⟨N, hN₀, hN, hsmall⟩
  refine ⟨N, hN₀, hN, ?_⟩
  rw [coupledGcdRatioExpression_eq_ehmInversionError_add_remainder H N hN]
  exact hsmall

/-- For the concrete autocorrelation kernel, double-cofinal finite Ehm
control supplies exactly the cofinal log-taper energy certificate. -/
noncomputable def cofinalLogTaperEnergyVanishing_of_ehmDoubleCofinal
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HB : EhmDoubleCofinalBoundaryVanishing ehmR1) :
    CofinalLogTaperEnergyVanishing where
  cofinally_small ε hε N₀ := by
    let H : EhmKernelPackage :=
      ehmS1PointwiseKernelPackageProved.toEhmKernelPackage
    rcases coupledGcdRatioExpression_cofinally_small_of_doubleCofinal
      H HS HB ε hε N₀ with ⟨N, hN₀, _hN, hsmall⟩
    refine ⟨N, hN₀, ?_⟩
    have heq : coupledGcdRatioExpression N = energy N := by
      simpa only [coupledGcdRatioExpression] using
        (energy_eq_gcdRatioFormula N).symm
    rw [← heq]
    exact (le_abs_self (coupledGcdRatioExpression N)).trans_lt hsmall

/-- The weakest Ehm closure presently exposed: rational-scale series
identification and double-cofinal finite cancellation imply the
Báez--Duarte criterion. -/
theorem baezDuarteCriterion_of_ehmDoubleCofinal
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HB : EhmDoubleCofinalBoundaryVanishing ehmR1) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_cofinalLogTaperEnergy
    (cofinalLogTaperEnergyVanishing_of_ehmDoubleCofinal HS HB)

/-- The same finite expression in the natural low-convolution/high-
dispersion coordinates, with the far complementary sector still coupled
under its original minus sign. -/
noncomputable def ehmFiniteNearFarDispersionExpression
    (R1 : ℝ → ℝ) (N D J M : ℕ) : ℝ :=
  ehmFiniteLogTaperConvolutionBlock R1 N J 1 M 2 D +
    ehmFiniteNearDispersionBlock R1 N D J 1 M (D + 1) J +
    ehmFiniteLogTaperConvolutionBlock R1 N J (M + 1) N 2 D +
    ehmFiniteNearDispersionBlock R1 N D J (M + 1) N (D + 1) J +
    ehmCoupledRemainder N -
    ehmFiniteComplementaryDivisorFarOuter R1 N D J

/-- Exact identification of the near/far rectangular expression with the
original finite coupled boundary. -/
theorem ehmFiniteCoupledBoundaryExpression_eq_nearFarDispersion
    (R1 : ℝ → ℝ) (N D J M : ℕ)
    (hN : 2 ≤ N) (hND : N ≤ D) (hM : M ≤ N) (hDJ : D ≤ J) :
    ehmFiniteCoupledBoundaryExpression R1 N J =
      ehmFiniteNearFarDispersionExpression R1 N D J M := by
  rw [ehmFiniteCoupledBoundaryExpression_eq_nearCore_sub_far
    R1 N D J hN hND hDJ,
    ehmFiniteComplementaryDivisorNearCore_eq_lowConvolution_highDispersion
      R1 N D J M hN hM (by omega) hDJ]
  rfl

/-- Equivalent research interface phrased directly in near/far dispersion
blocks.  All four signed blocks, the moment remainder, and the far-sector
subtraction remain inside one absolute value. -/
structure EhmDoubleCofinalNearFarDispersionVanishing (R1 : ℝ → ℝ) where
  cofinally_small : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
    ∃ N D M : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧ N ≤ D ∧ M ≤ N ∧
      ∃ᶠ J : ℕ in atTop,
        D ≤ J ∧ |ehmFiniteNearFarDispersionExpression R1 N D J M| < ε

/-- The near/far block formulation gives the minimal finite-boundary
formulation by the exact rectangular identity. -/
def EhmDoubleCofinalNearFarDispersionVanishing.toBoundary
    {R1 : ℝ → ℝ} (H : EhmDoubleCofinalNearFarDispersionVanishing R1) :
    EhmDoubleCofinalBoundaryVanishing R1 where
  cofinally_small ε hε N₀ := by
    rcases H.cofinally_small ε hε N₀ with
      ⟨N, D, M, hN₀, hN, hND, hM, hfreq⟩
    refine ⟨N, hN₀, hN, ?_⟩
    exact hfreq.mono fun J hJ ↦ by
      rw [ehmFiniteCoupledBoundaryExpression_eq_nearFarDispersion
        R1 N D J M hN hND hM hJ.1]
      exact hJ.2

/-- Conversely, the minimal finite-boundary formulation is already a
near/far block formulation: choose the degenerate but exact divisor split
`D=N` and outer split `M=N`, then intersect the cofinal set with `J>=N`.
Thus the block interface does not silently strengthen the analytic target. -/
def EhmDoubleCofinalBoundaryVanishing.toNearFar
    {R1 : ℝ → ℝ} (H : EhmDoubleCofinalBoundaryVanishing R1) :
    EhmDoubleCofinalNearFarDispersionVanishing R1 where
  cofinally_small ε hε N₀ := by
    rcases H.cofinally_small ε hε N₀ with ⟨N, hN₀, hN, hfreq⟩
    refine ⟨N, N, N, hN₀, hN, le_rfl, le_rfl, ?_⟩
    have hevent : ∀ᶠ J : ℕ in atTop, N ≤ J := eventually_ge_atTop N
    exact (hfreq.and_eventually hevent).mono fun J hJ ↦ by
      refine ⟨hJ.2, ?_⟩
      rw [← ehmFiniteCoupledBoundaryExpression_eq_nearFarDispersion
        R1 N N J N hN le_rfl le_rfl hJ.2]
      exact hJ.1

/-- Near/far dispersion-block cancellation at the double-cofinal strength
therefore also proves the Báez--Duarte criterion. -/
theorem baezDuarteCriterion_of_ehmDoubleCofinalNearFar
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HB : EhmDoubleCofinalNearFarDispersionVanishing ehmR1) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDoubleCofinal HS HB.toBoundary

end RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
