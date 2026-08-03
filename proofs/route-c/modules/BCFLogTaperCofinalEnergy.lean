import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaper

/-!
# Cofinal and averaged cutoff criteria for the BCF log taper

The explicit log-taper energy need not converge at every cutoff in order to
prove the Báez--Duarte criterion.  Since the optimal finite distance is
antitone, arbitrarily large cutoffs carrying arbitrarily small certified
energies already suffice.

This module also proves a deterministic averaging principle: convergence to
zero of the nonnegative dyadic block means produces such cofinally good
cutoffs.  The statements are purely functional analytic and introduce no
new arithmetic estimate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperCofinalEnergy

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper

/-- A nonnegative energy which bounds the optimal Báez--Duarte distance and
is arbitrarily small at arbitrarily large cutoffs. -/
structure CofinalEnergyCertificate (E : ℕ → ℝ) where
  distance_le : ∀ N : ℕ, BaezDuarteDistance N ≤ E N
  cofinally_small : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
    ∃ N : ℕ, N₀ ≤ N ∧ E N < ε

/-- Cofinally small certified energies suffice because the optimal distance
is antitone in the dimension. -/
theorem baezDuarteCriterion_of_cofinalEnergy
    {E : ℕ → ℝ} (H : CofinalEnergyCertificate E) :
    BaezDuarteCriterion := by
  rw [BaezDuarteCriterion, Metric.tendsto_atTop]
  intro ε hε
  rcases H.cofinally_small ε hε 0 with ⟨N, _, hEN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (baezDuarteDistance_nonneg n)]
  exact lt_of_le_of_lt
    ((baezDuarteDistance_antitone hn).trans (H.distance_le N)) hEN

/-- The concrete cofinal target for the BCF logarithmic taper. -/
structure CofinalLogTaperEnergyVanishing where
  cofinally_small : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
    ∃ N : ℕ, N₀ ≤ N ∧ energy N < ε

/-- A cofinal sequence of small log-taper energies proves the
Báez--Duarte criterion; no pointwise limit of `energy` is required. -/
noncomputable def CofinalLogTaperEnergyVanishing.toCertificate
    (H : CofinalLogTaperEnergyVanishing) :
    CofinalEnergyCertificate energy where
  distance_le := distance_le_energy
  cofinally_small := H.cofinally_small

theorem baezDuarteCriterion_of_cofinalLogTaperEnergy
    (H : CofinalLogTaperEnergyVanishing) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_cofinalEnergy H.toCertificate

/-- The arithmetic mean of an energy over the inclusive dyadic block
`[X,2X]`, whose cardinality is `X+1`. -/
noncomputable def dyadicBlockEnergyMean (E : ℕ → ℝ) (X : ℕ) : ℝ :=
  (∑ N ∈ Finset.Icc X (2 * X), E N) / ((X : ℝ) + 1)

/-- A nonnegative sequence with dyadic block means tending to zero. -/
structure DyadicBlockAverageVanishing (E : ℕ → ℝ) where
  nonneg : ∀ N : ℕ, 0 ≤ E N
  mean_tendsto_zero :
    Tendsto (dyadicBlockEnergyMean E) atTop (𝓝 0)

/-- A small dyadic mean contains a point below the same threshold. -/
theorem exists_lt_of_dyadicBlockEnergyMean_lt
    {E : ℕ → ℝ} (X : ℕ) {ε : ℝ}
    (hmean : dyadicBlockEnergyMean E X < ε) :
    ∃ N ∈ Finset.Icc X (2 * X), E N < ε := by
  classical
  by_contra hnot
  push Not at hnot
  have hsum : ((X : ℝ) + 1) * ε ≤
      ∑ N ∈ Finset.Icc X (2 * X), E N := by
    calc
      ((X : ℝ) + 1) * ε =
          ∑ _N ∈ Finset.Icc X (2 * X), ε := by
        have hcard : (Finset.Icc X (2 * X)).card = X + 1 := by
          rw [Nat.card_Icc]
          omega
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        push_cast
        ring
      _ ≤ ∑ N ∈ Finset.Icc X (2 * X), E N := by
        apply Finset.sum_le_sum
        intro N hN
        exact hnot N hN
  have hden : 0 < (X : ℝ) + 1 := by positivity
  have hεmean : ε ≤ dyadicBlockEnergyMean E X := by
    unfold dyadicBlockEnergyMean
    exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hsum)
  exact (not_lt_of_ge hεmean) hmean

/-- Correct generic constructor: a dyadic-average estimate together with a
certified distance upper bound yields a cofinal energy certificate. -/
noncomputable def CofinalEnergyCertificate.ofDyadicAverageAndBound
    {E : ℕ → ℝ}
    (H : DyadicBlockAverageVanishing E)
    (hbound : ∀ N : ℕ, BaezDuarteDistance N ≤ E N) :
    CofinalEnergyCertificate E where
  distance_le := hbound
  cofinally_small ε hε N₀ := by
    have hevent : ∀ᶠ X : ℕ in atTop, dyadicBlockEnergyMean E X < ε :=
      H.mean_tendsto_zero.eventually (Iio_mem_nhds hε)
    rcases (hevent.and (eventually_ge_atTop N₀)).exists with ⟨X, hmean, hXN₀⟩
    rcases exists_lt_of_dyadicBlockEnergyMean_lt X hmean with
      ⟨N, hNblock, hEN⟩
    exact ⟨N, hXN₀.trans (Finset.mem_Icc.mp hNblock).1, hEN⟩

/-- Dyadic mean convergence of the concrete log-taper energy is sufficient
for the Báez--Duarte criterion. -/
theorem baezDuarteCriterion_of_logTaperDyadicAverage
    (H : DyadicBlockAverageVanishing energy) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_cofinalEnergy
    (CofinalEnergyCertificate.ofDyadicAverageAndBound H distance_le_energy)

end RH.Criteria.NymanBeurling.BCFLogTaperCofinalEnergy
