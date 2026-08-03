import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion

/-!
# Signed dyadic averaging for the finite Ehm boundary

The second-moment dispersion criterion is convenient but stronger than the
double-cofinal conclusion requires.  This module keeps the average over the
outer cutoff `N` signed.

At a fixed dyadic block, the finite Ehm boundary sum converges as the
hyperbolic cutoff tends to infinity to a sum of exact BCF energies.  Those
limiting energies are nonnegative.  Consequently, a one-sided cofinal upper
bound for the signed finite sum forces the exact energy average to be small,
even though the finite Ehm summands may cancel across `N`.

Thus absolute values and squares are unnecessary at the outer averaging
stage.  All internal Möbius, near/far, and linear-term cancellation is
preserved.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperCofinalEnergy
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary

/-! ## Exact fixed-block signed limit -/

/-- A finite signed sum of Ehm boundaries converges to the corresponding
sum of exact certified energies. -/
theorem ehmDyadicBoundarySum_tendsto_energySum
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (X : ℕ) (hX : 2 ≤ X) :
    Tendsto
      (fun J : ℕ => ∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression BCFLogTaperEhm.ehmR1 N J)
      atTop
      (nhds (∑ N ∈ ehmDyadicNBlock X, energy N)) := by
  apply tendsto_finsetSum
  intro N hNmem
  exact ehmFiniteCoupledBoundaryExpression_tendsto_energy HS N
    (hX.trans (Finset.mem_Icc.mp hNmem).1)

/-! ## Signed finite-boundary and exact-energy packages -/

/-- A one-sided signed dyadic mean estimate for the complete finite Ehm
boundary.  No absolute value is taken around individual outer-cutoff terms. -/
structure EhmDyadicSignedBoundaryAverageVanishing where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_sum_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteCoupledBoundaryExpression
          BCFLogTaperEhm.ehmR1 N J) ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- A null upper majorant for dyadic sums of the nonnegative exact BCF
energies. -/
structure DyadicLogTaperEnergyMeanVanishing where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  sum_bound : ∀ X : ℕ, 2 ≤ X →
    (∑ N ∈ ehmDyadicNBlock X, energy N) ≤
      ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- The fixed-block signed limit transports a cofinal one-sided Ehm bound
to an exact nonnegative energy-mean bound. -/
noncomputable def EhmDyadicSignedBoundaryAverageVanishing.toEnergyMean
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicSignedBoundaryAverageVanishing) :
    DyadicLogTaperEnergyMeanVanishing where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  sum_bound X hX :=
    le_of_tendsto_of_frequently
      (ehmDyadicBoundarySum_tendsto_energySum HS X hX)
      (H.cofinal_sum_bound X hX)

/-- A vanishing dyadic mean of exact nonnegative energies selects
arbitrarily large cutoffs with small certified energy. -/
noncomputable def DyadicLogTaperEnergyMeanVanishing.toCofinalEnergy
    (H : DyadicLogTaperEnergyMeanVanishing) :
    CofinalLogTaperEnergyVanishing where
  cofinally_small ε hε N₀ := by
    have heta_event : ∀ᶠ X : ℕ in atTop, H.eta X < ε :=
      H.eta_tendsto_zero.eventually (Iio_mem_nhds hε)
    have hX_event : ∀ᶠ X : ℕ in atTop, max N₀ 2 ≤ X :=
      eventually_ge_atTop (max N₀ 2)
    rcases (heta_event.and hX_event).exists with ⟨X, heta, hX⟩
    have hX2 : 2 ≤ X := (le_max_right N₀ 2).trans hX
    rcases exists_mem_le_of_sum_le_card_mul
      (ehmDyadicNBlock X) (ehmDyadicNBlock_nonempty X)
      energy (H.eta X) (H.sum_bound X hX2) with ⟨N, hNmem, hNeta⟩
    have hXN : X ≤ N := (Finset.mem_Icc.mp hNmem).1
    exact ⟨N, (le_max_left N₀ 2).trans (hX.trans hXN),
      hNeta.trans_lt heta⟩

/-- Signed dyadic Ehm averaging is sufficient for the Báez--Duarte
criterion. -/
theorem baezDuarteCriterion_of_ehmDyadicSignedBoundaryAverage
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicSignedBoundaryAverageVanishing) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_cofinalLogTaperEnergy
    (H.toEnergyMean HS).toCofinalEnergy

/-- The signed average route also recovers the double-cofinal finite-boundary
statement itself.  After selecting a small exact energy, fixed-`N`
convergence makes the corresponding finite boundary eventually small in
`J` (and hence cofinally small). -/
noncomputable def EhmDyadicSignedBoundaryAverageVanishing.toDoubleCofinal
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicSignedBoundaryAverageVanishing) :
    EhmDoubleCofinalBoundaryVanishing BCFLogTaperEhm.ehmR1 where
  cofinally_small ε hε N₀ := by
    have hhalf : 0 < ε / 2 := half_pos hε
    let HE : CofinalLogTaperEnergyVanishing :=
      (H.toEnergyMean HS).toCofinalEnergy
    rcases HE.cofinally_small (ε / 2) hhalf (max N₀ 2) with
      ⟨N, hN, henergy⟩
    have hN₀ : N₀ ≤ N := (le_max_left N₀ 2).trans hN
    have hN2 : 2 ≤ N := (le_max_right N₀ 2).trans hN
    refine ⟨N, hN₀, hN2, ?_⟩
    have hlim := ehmFiniteCoupledBoundaryExpression_tendsto_energy HS N hN2
    rw [Metric.tendsto_atTop] at hlim
    rcases hlim (ε / 2) hhalf with ⟨J₀, hJ₀⟩
    have hevent : ∀ᶠ J : ℕ in atTop,
        |ehmFiniteCoupledBoundaryExpression
          BCFLogTaperEhm.ehmR1 N J| < ε := by
      filter_upwards [eventually_ge_atTop J₀] with J hJ
      have hdist := hJ₀ J hJ
      rw [Real.dist_eq] at hdist
      calc
        |ehmFiniteCoupledBoundaryExpression
            BCFLogTaperEhm.ehmR1 N J| =
            |(ehmFiniteCoupledBoundaryExpression
                BCFLogTaperEhm.ehmR1 N J - energy N) + energy N| := by ring_nf
        _ ≤ |ehmFiniteCoupledBoundaryExpression
              BCFLogTaperEhm.ehmR1 N J - energy N| + |energy N| :=
          abs_add_le _ _
        _ < ε / 2 + ε / 2 := by
          rw [abs_of_nonneg (energy_nonneg N)]
          exact add_lt_add hdist henergy
        _ = ε := by ring
    exact hevent.frequently

/-! ## Comparison with the stronger absolute first moment -/

/-- Absolute first-moment control implies the signed mean estimate with the
same majorant.  The converse is deliberately not asserted. -/
noncomputable def EhmDyadicBoundaryL1Vanishing.toSignedAverage
    (H : EhmDyadicBoundaryL1Vanishing BCFLogTaperEhm.ehmR1) :
    EhmDyadicSignedBoundaryAverageVanishing where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  cofinal_sum_bound X hX :=
    (H.cofinal_sum_bound X hX).mono fun J hJ ↦ by
      calc
        (∑ N ∈ ehmDyadicNBlock X,
            ehmFiniteCoupledBoundaryExpression
              BCFLogTaperEhm.ehmR1 N J) ≤
            ∑ N ∈ ehmDyadicNBlock X,
              |ehmFiniteCoupledBoundaryExpression
                BCFLogTaperEhm.ehmR1 N J| := by
          apply Finset.sum_le_sum
          intro N _
          exact le_abs_self _
        _ ≤ ((ehmDyadicNBlock X).card : ℝ) * H.eta X := hJ

/-! ## Exact signed near/far formulation -/

/-- The signed dyadic mean target in the exact near/far four-block
coordinates.  The four blocks, linear correction, and far subtraction are
summed before any outer estimate is applied. -/
structure EhmDyadicNearFarSignedAverageVanishing where
  D : ℕ → ℕ
  M : ℕ → ℕ
  D_ge : ∀ N, N ≤ D N
  M_le : ∀ N, M N ≤ N
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_sum_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      (∀ N ∈ ehmDyadicNBlock X, D N ≤ J) ∧
      (∑ N ∈ ehmDyadicNBlock X,
        ehmFiniteNearFarDispersionExpression
          BCFLogTaperEhm.ehmR1 N (D N) J (M N)) ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- The exact near/far identity transports the block-coordinate signed mean
to the original finite Ehm boundary signed mean. -/
noncomputable def EhmDyadicNearFarSignedAverageVanishing.toBoundaryAverage
    (H : EhmDyadicNearFarSignedAverageVanishing) :
    EhmDyadicSignedBoundaryAverageVanishing where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  cofinal_sum_bound X hX :=
    (H.cofinal_sum_bound X hX).mono fun J hJ ↦ by
      calc
        (∑ N ∈ ehmDyadicNBlock X,
            ehmFiniteCoupledBoundaryExpression
              BCFLogTaperEhm.ehmR1 N J) =
            ∑ N ∈ ehmDyadicNBlock X,
              ehmFiniteNearFarDispersionExpression
                BCFLogTaperEhm.ehmR1 N (H.D N) J (H.M N) := by
          apply Finset.sum_congr rfl
          intro N hNmem
          rw [ehmFiniteCoupledBoundaryExpression_eq_nearFarDispersion
            BCFLogTaperEhm.ehmR1 N (H.D N) J (H.M N)
            (hX.trans (Finset.mem_Icc.mp hNmem).1)
            (H.D_ge N) (H.M_le N) (hJ.1 N hNmem)]
        _ ≤ ((ehmDyadicNBlock X).card : ℝ) * H.eta X := hJ.2

/-- Current weakest dyadic mean-value closure: a one-sided signed estimate
for the exact near/far finite expression proves the Báez--Duarte criterion. -/
theorem baezDuarteCriterion_of_ehmDyadicNearFarSignedAverage
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicNearFarSignedAverageVanishing) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicSignedBoundaryAverage HS
    H.toBoundaryAverage

end RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage
