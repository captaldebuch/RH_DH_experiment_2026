import RiemannHypothesis.Criteria.NymanBeurling.AsymptoticEnergy
import RiemannHypothesis.Certificates.NymanBeurlingCertificate
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace RH.Criteria.NymanBeurling.CoefficientFamilies

open RH.Criteria.NymanBeurling.AsymptoticEnergy
open RH.Certificates

-- ---------------------------------------------------------------------------
-- 1. Möbius/Mertens Coefficient Family
-- ---------------------------------------------------------------------------

/-- The canonical number-theoretic coefficient family based on the Möbius function.
    We use `k = i.val + 1` to map `Fin N` to `1 .. N`. -/
noncomputable def mobiusCoefficientFamily : BaezDuarteCoefficientFamily :=
{ coeff := fun N i => (ArithmeticFunction.moebius (i.val + 1) : ℝ) }

theorem distance_le_mobius_energy (N : ℕ) :
    BaezDuarte.BaezDuarteDistance N ≤ coefficientEnergy mobiusCoefficientFamily N :=
  BaezDuarteDistance_le_coefficientEnergy mobiusCoefficientFamily N

/-- Expansion of the Möbius energy into finite sums. -/
theorem mobiusCoefficientEnergy_eq_sum (N : ℕ) :
    coefficientEnergy mobiusCoefficientFamily N =
      ∑ h : Fin N, ∑ k : Fin N,
        (ArithmeticFunction.moebius (h.val + 1) : ℝ) * (ArithmeticFunction.moebius (k.val + 1) : ℝ) * VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1)
      - 2 * ∑ k : Fin N, (ArithmeticFunction.moebius (k.val + 1) : ℝ) * RH.Certificates.innerProductChiRho k.val
      + 1 := by
  unfold coefficientEnergy mobiusCoefficientFamily
  rfl

structure MobiusLogEnergyTarget where
  C : ℝ
  C_pos : 0 < C
  bound :
    ∀ N,
      coefficientEnergy mobiusCoefficientFamily N ≤ C / Real.log (N + 2 : ℝ)

theorem baezDuarteCriterion_of_mobius_log_energy
    (H : MobiusLogEnergyTarget) :
    BaezDuarte.BaezDuarteCriterion :=
  baezDuarteCriterion_of_log_controlled_coefficients
    mobiusCoefficientFamily
    { C := H.C, C_pos := H.C_pos, energy_bound := H.bound }

-- ---------------------------------------------------------------------------
-- 2. Cutoff-Möbius Coefficient Family (Phase 11E₂)
-- ---------------------------------------------------------------------------

/-- Cutoff variant of the Möbius function: - μ(k) * (1 - k/(N+1)).
    Numerical evidence suggests this strongly correlates with the optimal coefficients. -/
noncomputable def cutoffMobiusCoefficientFamily : BaezDuarteCoefficientFamily :=
{ coeff := fun N i =>
    - ((ArithmeticFunction.moebius (i.val + 1) : ℤ) : ℝ) * (1 - (((i.val + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))) }

theorem distance_le_cutoffMobius_energy (N : ℕ) :
    BaezDuarte.BaezDuarteDistance N ≤ coefficientEnergy cutoffMobiusCoefficientFamily N :=
  BaezDuarteDistance_le_coefficientEnergy cutoffMobiusCoefficientFamily N

theorem cutoffMobiusCoefficientEnergy_eq_sum (N : ℕ) :
    coefficientEnergy cutoffMobiusCoefficientFamily N =
      ∑ h : Fin N, ∑ k : Fin N,
        (- ((ArithmeticFunction.moebius (h.val + 1) : ℤ) : ℝ) * (1 - (((h.val + 1) : ℝ) / ((N + 1 : ℕ) : ℝ)))) *
        (- ((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ) * (1 - (((k.val + 1) : ℝ) / ((N + 1 : ℕ) : ℝ)))) *
        VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1)
      - 2 * ∑ k : Fin N,
        (- ((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ) * (1 - (((k.val + 1) : ℝ) / ((N + 1 : ℕ) : ℝ)))) *
        RH.Certificates.innerProductChiRho k.val
      + 1 := by
  unfold coefficientEnergy cutoffMobiusCoefficientFamily
  rfl

structure CutoffMobiusLogEnergyTarget where
  C : ℝ
  C_pos : 0 < C
  bound :
    ∀ N,
      coefficientEnergy cutoffMobiusCoefficientFamily N ≤ C / Real.log (N + 2 : ℝ)

theorem baezDuarteCriterion_of_cutoffMobius_log_energy
    (H : CutoffMobiusLogEnergyTarget) :
    BaezDuarte.BaezDuarteCriterion :=
  baezDuarteCriterion_of_log_controlled_coefficients
    cutoffMobiusCoefficientFamily
    { C := H.C, C_pos := H.C_pos, energy_bound := H.bound }

-- ---------------------------------------------------------------------------
-- 3. Decomposed Cutoff-Möbius Energy (Phase 11E₃ & 11E₄)
-- ---------------------------------------------------------------------------

noncomputable def cutoffMobiusLinearTerm (N : ℕ) : ℝ :=
  ∑ k : Fin N, (- ((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ) * (1 - (((k.val + 1) : ℝ) / ((N + 1 : ℕ) : ℝ)))) * RH.Certificates.innerProductChiRho k.val

noncomputable def cutoffMobiusQuadraticTerm (N : ℕ) : ℝ :=
  ∑ h : Fin N, ∑ k : Fin N,
    (- ((ArithmeticFunction.moebius (h.val + 1) : ℤ) : ℝ) * (1 - (((h.val + 1) : ℝ) / ((N + 1 : ℕ) : ℝ)))) *
    (- ((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ) * (1 - (((k.val + 1) : ℝ) / ((N + 1 : ℕ) : ℝ)))) *
    VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1)

theorem cutoffMobiusEnergy_decomposition (N : ℕ) :
    coefficientEnergy cutoffMobiusCoefficientFamily N =
      1 - 2 * cutoffMobiusLinearTerm N + cutoffMobiusQuadraticTerm N := by
  rw [cutoffMobiusCoefficientEnergy_eq_sum]
  unfold cutoffMobiusLinearTerm cutoffMobiusQuadraticTerm
  ring

structure CutoffMobiusAnalyticEstimates where
  C : ℝ
  C_pos : 0 < C
  asymptotic_bound :
    ∀ N, cutoffMobiusQuadraticTerm N - 2 * cutoffMobiusLinearTerm N + 1 ≤ C / Real.log (N + 2 : ℝ)

def cutoffMobius_log_energy_of_estimates
    (H : CutoffMobiusAnalyticEstimates) :
    CutoffMobiusLogEnergyTarget :=
  { C := H.C
    C_pos := H.C_pos
    bound := fun N => by
      rw [cutoffMobiusEnergy_decomposition]
      have h1 := H.asymptotic_bound N
      linarith }

-- ---------------------------------------------------------------------------
-- 4. Abstract Bounded Coefficient Family
-- ---------------------------------------------------------------------------

structure BoundedCoefficientFamily where
  family : BaezDuarteCoefficientFamily
  coeff_bound : ∀ N i, |family.coeff N i| ≤ 1000 -- placeholder generic bound

end RH.Criteria.NymanBeurling.CoefficientFamilies
