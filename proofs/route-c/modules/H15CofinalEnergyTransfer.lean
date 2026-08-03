import RiemannHypothesis.Criteria.NymanBeurling.H15AveragedReciprocalPhase
import RiemannHypothesis.Criteria.NymanBeurling.H15IntegratedCancellation
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperCofinalEnergy

/-!
# Honest cofinal transfer from triangular H15 to certified energy

The reciprocal-phase module reaches cofinally small values of the centered
sawtooth residual for the project's **triangular** cutoff.  This file proves
the deterministic consequences of that result and stops exactly where the
coefficient-family mismatch begins.

There are two additional ingredients:

1. decay of the separately absolute smooth log-gamma component; and
2. a weight-matched domination of either the optimal Báez--Duarte distance or
   the BCF **logarithmic**-taper energy by the complete triangular H15
   residual plus a null remainder.

The first ingredient follows from the existing
`H15CenteredSmoothLogGammaBound`.  The second does not follow from the known
finite identities: triangular and logarithmic tapers are different
coefficient families.  It is therefore retained as an explicit structure.
No equality between those energies is asserted here.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open Filter Topology
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.CutoffMobiusKernels

/-! ## Recombining the cofinal sawtooth and smooth terms -/

/-- Cofinal smallness of the complete triangular-cutoff H15 residual. -/
structure CofinalH15CenteredResidualVanishing where
  good_cutoff : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
    ∃ N ≥ N₀, h15CenteredResidual N < ε

/-- A logarithmic-square bound for the smooth component implies ordinary
null convergence of that component. -/
theorem smoothLogGamma_tendsto_zero_of_logSqBound
    (H : H15CenteredSmoothLogGammaBound) :
    Tendsto (fun N ↦ |explicitQuadraticLogGammaComponent N|)
      atTop (nhds 0) := by
  have hlogC :
      Tendsto
        (fun N : ℕ ↦ H.C_smooth / Real.log (N + 2 : ℝ))
        atTop (nhds 0) :=
    AsymptoticEnergy.logEnergyBound_tendsto_zero
  have hlogOne :
      Tendsto
        (fun N : ℕ ↦ (1 : ℝ) / Real.log (N + 2 : ℝ))
        atTop (nhds 0) :=
    AsymptoticEnergy.logEnergyBound_tendsto_zero
  have hmajorant :
      Tendsto
        (fun N : ℕ ↦ H.C_smooth / Real.log (N + 2 : ℝ) ^ 2)
        atTop (nhds 0) := by
    have hmul := hlogC.mul hlogOne
    simpa only [zero_mul] using hmul.congr' (by
      filter_upwards [] with N
      have hlog_ne : Real.log (N + 2 : ℝ) ≠ 0 := by
        exact ne_of_gt (Real.log_pos (by norm_cast; omega))
      field_simp)
  exact squeeze_zero
    (fun N ↦ abs_nonneg (explicitQuadraticLogGammaComponent N))
    H.smooth_bound hmajorant

/-- The exact identity
`h15CenteredResidual = |smooth| + |sawtooth|`, together with uniform eventual
smallness of the smooth term and cofinal smallness of the sawtooth term,
gives cofinal smallness of the complete residual. -/
noncomputable def cofinalH15CenteredResidualVanishing_of_sawtooth_and_smooth
    (HS : CofinalH15CenteredSawtoothVanishing)
    (HG : Tendsto (fun N ↦ |explicitQuadraticLogGammaComponent N|)
      atTop (nhds 0)) :
    CofinalH15CenteredResidualVanishing where
  good_cutoff ε hε N₀ := by
    have hhalf : 0 < ε / 2 := by linarith
    have hGevent : ∀ᶠ N : ℕ in atTop,
        |explicitQuadraticLogGammaComponent N| < ε / 2 :=
      HG.eventually (Iio_mem_nhds hhalf)
    obtain ⟨N₁, hN₁⟩ := (eventually_atTop.1 hGevent)
    obtain ⟨N, hN, hS⟩ := HS.good_cutoff (ε / 2) hhalf (max N₀ N₁)
    refine ⟨N, (le_max_left N₀ N₁).trans hN, ?_⟩
    have hG := hN₁ N ((le_max_right N₀ N₁).trans hN)
    unfold h15CenteredResidual
    linarith

/-- The existing smooth logarithmic-square package is sufficient for the
smooth input of the cofinal recombination. -/
noncomputable def cofinalH15CenteredResidualVanishing_of_sawtooth
    (HS : CofinalH15CenteredSawtoothVanishing)
    (HG : H15CenteredSmoothLogGammaBound) :
    CofinalH15CenteredResidualVanishing :=
  cofinalH15CenteredResidualVanishing_of_sawtooth_and_smooth HS
    (smoothLogGamma_tendsto_zero_of_logSqBound HG)

/-! ## Weakest distance-level closure -/

/-- Cofinal residual vanishing and the existing weight-matched distance
transfer suffice for the Báez--Duarte criterion.  This is weaker than asking
for a pointwise limit of the residual: antitonicity of the optimal distance
upgrades arbitrarily large good cutoffs to eventual smallness. -/
theorem baezDuarteCriterion_of_cofinalH15CenteredResidual
    (H : CofinalH15CenteredResidualVanishing)
    (T : H15ResidualToBaezDuarteEnergyTransfer) :
    BaezDuarteCriterion := by
  rw [BaezDuarteCriterion, Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have herror : ∀ᶠ N : ℕ in atTop, T.linear_error N < ε / 2 :=
    T.linear_error_tendsto_zero.eventually (Iio_mem_nhds hhalf)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 herror
  obtain ⟨N, hN, hres⟩ := H.good_cutoff (ε / 2) hhalf N₁
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (baezDuarteDistance_nonneg n)]
  have hdistN : BaezDuarteDistance N < ε := by
    calc
      BaezDuarteDistance N
          ≤ h15CenteredResidual N + T.linear_error N := T.distance_bound N
      _ < ε / 2 + ε / 2 :=
        add_lt_add hres (hN₁ N hN)
      _ = ε := by ring
  exact (baezDuarteDistance_antitone hn).trans_lt hdistN

/-- Cofinal reciprocal-phase/Vaaler control closes the criterion only after
both missing interfaces are supplied: the smooth triangular term and the
weight-matched distance transfer. -/
theorem baezDuarteCriterion_of_averagedReciprocalPhase
    (H : AveragedReciprocalPhaseVaalerPackage)
    (A2 : AveragedH15SawtoothLogReduction H.sawtoothMajorant)
    (HG : H15CenteredSmoothLogGammaBound)
    (T : H15ResidualToBaezDuarteEnergyTransfer) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_cofinalH15CenteredResidual
    (cofinalH15CenteredResidualVanishing_of_sawtooth
      (cofinalH15CenteredSawtoothVanishing_of_averagedReciprocalPhase H A2)
      HG)
    T

/-! ## Stronger, explicit BCF log-taper transfer -/

/-- The exact missing bridge from the triangular H15 architecture to the BCF
logarithmic-taper energy.  Its `energy_bound` must be proved from a genuine
Gram/defect estimate for the two different coefficient families. -/
structure H15ResidualToLogTaperEnergyTransfer where
  transferError : ℕ → ℝ
  transferError_tendsto_zero : Tendsto transferError atTop (nhds 0)
  energy_bound : ∀ N,
    BCFLogTaper.energy N ≤ h15CenteredResidual N + transferError N

/-- An energy-level transfer implies the weaker pre-existing distance-level
transfer by the exact certification `BaezDuarteDistance ≤ log-taper energy`. -/
noncomputable def H15ResidualToLogTaperEnergyTransfer.toDistanceTransfer
    (T : H15ResidualToLogTaperEnergyTransfer) :
    H15ResidualToBaezDuarteEnergyTransfer where
  linear_error := T.transferError
  linear_error_tendsto_zero := T.transferError_tendsto_zero
  distance_bound N :=
    (BCFLogTaper.distance_le_energy N).trans (T.energy_bound N)

/-- With the explicit cross-taper domination, cofinal triangular-H15
residual decay gives cofinally small certified BCF logarithmic-taper energy. -/
noncomputable def cofinalLogTaperEnergy_of_cofinalH15Residual
    (H : CofinalH15CenteredResidualVanishing)
    (T : H15ResidualToLogTaperEnergyTransfer) :
    BCFLogTaperCofinalEnergy.CofinalLogTaperEnergyVanishing where
  cofinally_small ε hε N₀ := by
    have hhalf : 0 < ε / 2 := by linarith
    have herror : ∀ᶠ N : ℕ in atTop, T.transferError N < ε / 2 :=
      T.transferError_tendsto_zero.eventually (Iio_mem_nhds hhalf)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 herror
    obtain ⟨N, hN, hres⟩ := H.good_cutoff (ε / 2) hhalf (max N₀ N₁)
    refine ⟨N, (le_max_left N₀ N₁).trans hN, ?_⟩
    calc
      BCFLogTaper.energy N
          ≤ h15CenteredResidual N + T.transferError N := T.energy_bound N
      _ < ε / 2 + ε / 2 :=
        add_lt_add hres (hN₁ N ((le_max_right N₀ N₁).trans hN))
      _ = ε := by ring

/-- The stronger energy-level transfer reaches the criterion through the
proved cofinal log-taper energy theorem. -/
theorem baezDuarteCriterion_of_cofinalH15Residual_logTaper
    (H : CofinalH15CenteredResidualVanishing)
    (T : H15ResidualToLogTaperEnergyTransfer) :
    BaezDuarteCriterion :=
  BCFLogTaperCofinalEnergy.baezDuarteCriterion_of_cofinalLogTaperEnergy
    (cofinalLogTaperEnergy_of_cofinalH15Residual H T)

end RH.Criteria.NymanBeurling.QuadraticInteraction
