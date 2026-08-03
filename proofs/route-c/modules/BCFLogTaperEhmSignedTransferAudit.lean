import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage

/-!
# Signed dyadic transfer: exact strength audit

The finite Ehm boundary is signed, but at every fixed outer cutoff it tends
to the exact nonnegative BCF log-taper energy.  Consequently a null signed
dyadic upper bound cannot obtain its saving merely from persistent
cancellation between outer cutoffs: after the hyperbolic cutoff tends to
infinity, it is precisely a null dyadic mean bound for the exact energies.

This file proves both reverse transfers which make that statement exact:

* a vanishing exact-energy dyadic mean gives a signed finite-boundary mean,
  with the explicit harmless slack `1/(X+1)`;
* cofinal smallness of the exact energy gives double-cofinal smallness of the
  finite Ehm boundary.

Together with the previously proved forward transfers, these give
equivalences at the level of existence of proof packages.  No inhabitant of
either side is constructed here; doing so is the remaining H15 analytic
problem.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedTransferAudit

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperCofinalEnergy
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary

/-! ## Reverse signed-average transfer -/

/-- Explicit vanishing slack used to pass from a limit inequality back to
an eventually strict finite-boundary inequality. -/
noncomputable def ehmSignedTransferSlack (X : ℕ) : ℝ :=
  1 / ((X : ℝ) + 1)

theorem ehmSignedTransferSlack_pos (X : ℕ) :
    0 < ehmSignedTransferSlack X := by
  unfold ehmSignedTransferSlack
  positivity

theorem ehmSignedTransferSlack_tendsto_zero :
    Tendsto ehmSignedTransferSlack atTop (nhds 0) := by
  unfold ehmSignedTransferSlack
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- A null dyadic mean of the exact energies gives a signed finite-boundary
mean.  The majorant is enlarged only by `1/(X+1)`, which tends to zero.

Thus the signed finite transfer is not analytically weaker than exact-energy
mean vanishing; it is another presentation of the same asymptotic input. -/
noncomputable def DyadicLogTaperEnergyMeanVanishing.toSignedBoundaryAverage
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : DyadicLogTaperEnergyMeanVanishing) :
    EhmDyadicSignedBoundaryAverageVanishing where
  eta := fun X => H.eta X + ehmSignedTransferSlack X
  eta_nonneg X := add_nonneg (H.eta_nonneg X)
    (ehmSignedTransferSlack_pos X).le
  eta_tendsto_zero := by
    simpa using H.eta_tendsto_zero.add ehmSignedTransferSlack_tendsto_zero
  cofinal_sum_bound X hX := by
    let cardX : ℝ := ((ehmDyadicNBlock X).card : ℝ)
    let energySum : ℝ := ∑ N ∈ ehmDyadicNBlock X, energy N
    let target : ℝ := cardX *
      (H.eta X + ehmSignedTransferSlack X)
    have hcard : 0 < cardX := by
      dsimp only [cardX]
      exact_mod_cast (ehmDyadicNBlock_nonempty X).card_pos
    have hsum : energySum ≤ cardX * H.eta X := by
      exact H.sum_bound X hX
    have htarget : energySum < target := by
      dsimp only [target]
      have hgain : 0 < cardX * ehmSignedTransferSlack X :=
        mul_pos hcard (ehmSignedTransferSlack_pos X)
      nlinarith
    have hlim : Tendsto
        (fun J : ℕ => ∑ N ∈ ehmDyadicNBlock X,
          ehmFiniteCoupledBoundaryExpression ehmR1 N J)
        atTop (nhds energySum) := by
      exact ehmDyadicBoundarySum_tendsto_energySum HS X hX
    have hevent : ∀ᶠ J : ℕ in atTop,
        (∑ N ∈ ehmDyadicNBlock X,
          ehmFiniteCoupledBoundaryExpression ehmR1 N J) < target :=
      hlim.eventually (Iio_mem_nhds htarget)
    exact hevent.frequently.mono fun J hJ => hJ.le

/-- Existence of a signed dyadic boundary estimate is equivalent to
existence of a null dyadic mean bound for the exact nonnegative energies.
The two packages may use different null majorants because the reverse map
adds the explicit vanishing slack. -/
theorem nonempty_signedBoundaryAverage_iff_nonempty_energyMean
    (HS : EhmAutocorrelationR1RationalSeriesBridge) :
    Nonempty EhmDyadicSignedBoundaryAverageVanishing ↔
      Nonempty DyadicLogTaperEnergyMeanVanishing := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.toEnergyMean HS⟩
  · rintro ⟨H⟩
    exact ⟨DyadicLogTaperEnergyMeanVanishing.toSignedBoundaryAverage HS H⟩

/-! ## Reverse double-cofinal transfer -/

/-- Cofinal smallness of the exact log-taper energy gives double-cofinal
smallness of the finite Ehm boundary.  At the selected fixed `N`, convergence
in the hyperbolic cutoff supplies an eventual, hence frequent, bound. -/
noncomputable def CofinalLogTaperEnergyVanishing.toEhmDoubleCofinal
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : CofinalLogTaperEnergyVanishing) :
    EhmDoubleCofinalBoundaryVanishing ehmR1 where
  cofinally_small ε hε N₀ := by
    have hhalf : 0 < ε / 2 := half_pos hε
    rcases H.cofinally_small (ε / 2) hhalf (max N₀ 2) with
      ⟨N, hN, henergy⟩
    have hN₀ : N₀ ≤ N := (le_max_left N₀ 2).trans hN
    have hN2 : 2 ≤ N := (le_max_right N₀ 2).trans hN
    refine ⟨N, hN₀, hN2, ?_⟩
    have hlim := ehmFiniteCoupledBoundaryExpression_tendsto_energy HS N hN2
    rw [Metric.tendsto_atTop] at hlim
    rcases hlim (ε / 2) hhalf with ⟨J₀, hJ₀⟩
    have hevent : ∀ᶠ J : ℕ in atTop,
        |ehmFiniteCoupledBoundaryExpression ehmR1 N J| < ε := by
      filter_upwards [eventually_ge_atTop J₀] with J hJ
      have hdist := hJ₀ J hJ
      rw [Real.dist_eq] at hdist
      calc
        |ehmFiniteCoupledBoundaryExpression ehmR1 N J| =
            |(ehmFiniteCoupledBoundaryExpression ehmR1 N J - energy N) +
              energy N| := by ring_nf
        _ ≤ |ehmFiniteCoupledBoundaryExpression ehmR1 N J - energy N| +
              |energy N| := abs_add_le _ _
        _ < ε / 2 + ε / 2 := by
          rw [abs_of_nonneg (energy_nonneg N)]
          exact add_lt_add hdist henergy
        _ = ε := by ring
    exact hevent.frequently

/-- With the rational-series bridge fixed, the double-cofinal finite Ehm
package exists exactly when the explicit BCF energies are cofinally small.
This is an equivalence of the two finite/limit presentations, not a proof
that either package is inhabited. -/
theorem nonempty_ehmDoubleCofinal_iff_nonempty_cofinalEnergy
    (HS : EhmAutocorrelationR1RationalSeriesBridge) :
    Nonempty (EhmDoubleCofinalBoundaryVanishing ehmR1) ↔
      Nonempty CofinalLogTaperEnergyVanishing := by
  constructor
  · rintro ⟨H⟩
    exact ⟨cofinalLogTaperEnergyVanishing_of_ehmDoubleCofinal HS H⟩
  · rintro ⟨H⟩
    exact ⟨CofinalLogTaperEnergyVanishing.toEhmDoubleCofinal HS H⟩

end RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedTransferAudit
