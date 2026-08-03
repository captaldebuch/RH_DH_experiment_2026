import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaper

/-!
# A compactly supported quadratic-taper BCF coefficient family

This module is the formal finite part of WP5.  It introduces a coefficient
family distinct from both the triangular H15 cutoff and the BCF logarithmic
taper.  Its rescaled profile is `(1 - u)^2` on `u ≤ 1` and zero thereafter,
so the cutoff has a vanishing first derivative at its endpoint.  The module
proves its own finite Gram identity and distance transfer; no formula is
inherited from either earlier family.
-/

namespace RH.Criteria.NymanBeurling.BCFQuadraticTaper

open scoped BigOperators
open Filter Topology
open RH.Criteria.NymanBeurling.AsymptoticEnergy
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper

/-- A compactly supported, rescaled quadratic cutoff.  On the range used by
the `N`-term family this is `(1 - n / (N + 1))^2`; it is zero at and beyond
the endpoint `n = N + 1`. -/
noncomputable def quadraticWeight (N n : ℕ) : ℝ :=
  if n ≤ N + 1 then
    (1 - (n : ℝ) / ((N + 1 : ℕ) : ℝ)) ^ 2
  else 0

theorem quadraticWeight_of_le {N n : ℕ} (hn : n ≤ N + 1) :
    quadraticWeight N n =
      (1 - (n : ℝ) / ((N + 1 : ℕ) : ℝ)) ^ 2 := by
  unfold quadraticWeight
  rw [if_pos hn]

theorem quadraticWeight_eq_zero_of_lt {N n : ℕ} (hN : N + 1 < n) :
    quadraticWeight N n = 0 := by
  unfold quadraticWeight
  rw [if_neg (Nat.not_le_of_lt hN)]

theorem quadraticWeight_nonneg (N n : ℕ) : 0 ≤ quadraticWeight N n := by
  unfold quadraticWeight
  split_ifs with h
  · exact sq_nonneg _
  · exact le_rfl

theorem quadraticWeight_cutoff (N : ℕ) : quadraticWeight N (N + 1) = 0 := by
  rw [quadraticWeight_of_le le_rfl]
  have hpos : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [div_self hpos]
  norm_num

/-- The Möbius coefficients associated with the quadratic taper.  The sign
matches the project's Nyman--Beurling approximation convention. -/
noncomputable def coefficientFamily : BaezDuarteCoefficientFamily :=
  { coeff := fun N i =>
      -((ArithmeticFunction.moebius (i.val + 1) : ℤ) : ℝ) *
        quadraticWeight N (i.val + 1) }

/-- The finite Nyman--Beurling approximant for the quadratic taper. -/
noncomputable def approximant (N : ℕ) (x : ℝ) : ℝ :=
  bdApprox N (coefficientFamily.coeff N) x

/-- Its finite positive-half-line squared error. -/
noncomputable def energy (N : ℕ) : ℝ :=
  BaezDuarteL2Error N (coefficientFamily.coeff N)

theorem energy_nonneg (N : ℕ) : 0 ≤ energy N :=
  baezDuarteL2Error_nonneg N (coefficientFamily.coeff N)

/-- Exact finite Gram expansion for this *new* coefficient family. -/
theorem energy_eq_finite_gram (N : ℕ) :
    energy N =
      ∑ h : Fin N, ∑ k : Fin N,
        coefficientFamily.coeff N h * coefficientFamily.coeff N k *
          VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1)
      - 2 * ∑ k : Fin N,
          coefficientFamily.coeff N k * RH.Certificates.innerProductChiRho k.val
      + 1 := by
  change BaezDuarteL2Error N (coefficientFamily.coeff N) = _
  exact RH.Certificates.baezDuarteL2Error_gram_expansion N
    (coefficientFamily.coeff N)

/-- The family-specific finite energy agrees with the generic coefficient
energy, allowing it to use the project-wide distance certificate. -/
theorem energy_eq_coefficientEnergy (N : ℕ) :
    energy N = coefficientEnergy coefficientFamily N := by
  simpa only [energy, coefficientEnergy] using
    RH.Certificates.baezDuarteL2Error_gram_expansion N
      (coefficientFamily.coeff N)

/-- This family has its own certified transfer to the optimal finite
Nyman--Beurling distance. -/
theorem distance_le_energy (N : ℕ) :
    BaezDuarteDistance N ≤ energy N := by
  calc
    BaezDuarteDistance N ≤ coefficientEnergy coefficientFamily N :=
      BaezDuarteDistance_le_coefficientEnergy coefficientFamily N
    _ = energy N := (energy_eq_coefficientEnergy N).symm

/-- A quantitative analytic estimate for the quadratic taper.  Its fields are
obligations for a future proof, rather than an assumed theorem. -/
structure QuadraticTaperLogEnergyBound where
  C : ℝ
  C_pos : 0 < C
  bound : ∀ N : ℕ, energy N ≤ C / Real.log (N + 2 : ℝ)

/-- A proved logarithmic estimate for the quadratic taper closes the
project-native Báez--Duarte criterion through its own energy transfer. -/
theorem baezDuarteCriterion_of_quadratic_log_energy
    (H : QuadraticTaperLogEnergyBound) :
    BaezDuarteCriterion := by
  apply baezDuarteCriterion_of_log_bound
  intro N
  exact (distance_le_energy N).trans (H.bound N)

/-- A certificate for selecting the quadratic taper through comparison with
the already-frozen BCF logarithmic family.  The comparison itself remains an
explicit analytic obligation. -/
structure QuadraticTaperComparisonToBCF where
  energy_le : ∀ N : ℕ, energy N ≤ BCFLogTaper.energy N

/-- A proved comparison transports vanishing of the BCF logarithmic-taper
energy to the separate quadratic-taper energy. -/
theorem energy_tendsto_zero_of_comparison_to_BCF
    (H : QuadraticTaperComparisonToBCF)
    (hBCF : Tendsto BCFLogTaper.energy atTop (nhds 0)) :
    Tendsto energy atTop (nhds 0) := by
  apply squeeze_zero
  · intro N
    exact energy_nonneg N
  · intro N
    exact H.energy_le N
  · exact hBCF

/-- WP5 selection theorem: the quadratic taper can replace the BCF logarithmic
taper only after the comparison is supplied; its independently proved distance
transfer then yields the criterion. -/
theorem baezDuarteCriterion_of_quadratic_taper_comparison
    (H : QuadraticTaperComparisonToBCF)
    (hBCF : Tendsto BCFLogTaper.energy atTop (nhds 0)) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_certified_energy_sequence energy distance_le_energy
    (energy_tendsto_zero_of_comparison_to_BCF H hBCF)

end RH.Criteria.NymanBeurling.BCFQuadraticTaper
