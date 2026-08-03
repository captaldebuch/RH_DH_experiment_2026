import RiemannHypothesis.Criteria.NymanBeurling.CoefficientFamilies
import Mathlib.Data.Finset.Interval

/-!
# The BCF logarithmic-taper coefficient family

This module freezes the coefficient family used by the logarithmically tapered
Möbius route.  It is intentionally independent of the existing triangular H15
cutoff.  The Dirichlet polynomial has the usual positive Möbius sign, while the
Nyman--Beurling vector has the opposite sign dictated by the project's
`rhoBD` approximation convention.

No Mellin/Plancherel identity is asserted here.  What is proved is the exact
finite Gram formula for the finite Nyman--Beurling approximation energy.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaper

open scoped BigOperators
open RH.Criteria.NymanBeurling.AsymptoticEnergy
open RH.Criteria.NymanBeurling.BaezDuarte

/-- The BCF logarithmic taper.  The `N < 2` branch makes the family total;
for `N ≥ 2` this is exactly `1 - log n / log N`. -/
noncomputable def weight (N n : ℕ) : ℝ :=
  if 2 ≤ N then 1 - Real.log (n : ℝ) / Real.log (N : ℝ) else 0

theorem weight_of_two_le {N n : ℕ} (hN : 2 ≤ N) :
    weight N n = 1 - Real.log (n : ℝ) / Real.log (N : ℝ) := by
  unfold weight
  rw [if_pos hN]

theorem weight_one {N : ℕ} (hN : 2 ≤ N) : weight N 1 = 1 := by
  rw [weight_of_two_le hN]
  norm_num

theorem weight_cutoff {N : ℕ} (hN : 2 ≤ N) : weight N N = 0 := by
  have hlog : Real.log (N : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    norm_cast
  rw [weight_of_two_le hN, div_self hlog]
  norm_num

/-- The coefficient of the logarithmically tapered Möbius Dirichlet
polynomial. -/
noncomputable def dirichletCoeff (N n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) * weight N n

/-- The finite BCF Dirichlet polynomial
`Σ_{1 ≤ n ≤ N} μ(n) (1 - log n / log N) n^{-s}` for `N ≥ 2`. -/
noncomputable def dirichletPolynomial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (dirichletCoeff N n : ℂ) * ((n : ℂ) ^ (-s))

theorem dirichletPolynomial_of_two_le (N : ℕ) (s : ℂ) (hN : 2 ≤ N) :
    dirichletPolynomial N s =
      ∑ n ∈ Finset.Icc 1 N,
        ((((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            (1 - Real.log (n : ℝ) / Real.log (N : ℝ)) : ℝ) : ℂ) *
          ((n : ℂ) ^ (-s)) := by
  unfold dirichletPolynomial
  apply Finset.sum_congr rfl
  intro n _
  unfold dirichletCoeff
  rw [weight_of_two_le hN]

/-- The coefficient family for the project's Nyman--Beurling convention.
The minus sign is separate from `dirichletCoeff`: it arises from approximating
`χ_(0,1]` by the `rhoBD` basis rather than from the reciprocal-zeta
Dirichlet-polynomial normalization. -/
noncomputable def coefficientFamily : BaezDuarteCoefficientFamily :=
  { coeff := fun N i => -dirichletCoeff N (i.val + 1) }

/-- The finite Nyman--Beurling approximant associated to the log taper. -/
noncomputable def approximant (N : ℕ) (x : ℝ) : ℝ :=
  bdApprox N (coefficientFamily.coeff N) x

theorem approximant_eq_sum (N : ℕ) (x : ℝ) :
    approximant N x =
      ∑ i : Fin N, -dirichletCoeff N (i.val + 1) * rhoBD i.val x := by
  rfl

/-- The exact finite Nyman--Beurling approximation energy of `approximant`.
This is not yet identified with any critical-line Mellin energy. -/
noncomputable def energy (N : ℕ) : ℝ :=
  BaezDuarteL2Error N (coefficientFamily.coeff N)

theorem energy_nonneg (N : ℕ) : 0 ≤ energy N :=
  baezDuarteL2Error_nonneg N (coefficientFamily.coeff N)

/-- Exact finite Gram expansion of the logarithmic-taper energy. -/
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

/-- The project-wide coefficient energy is exactly the finite energy above. -/
theorem energy_eq_coefficientEnergy (N : ℕ) :
    energy N = coefficientEnergy coefficientFamily N := by
  simpa only [energy, coefficientEnergy] using
    RH.Certificates.baezDuarteL2Error_gram_expansion N
    (coefficientFamily.coeff N)

/-- This explicit log-taper energy certifies an upper bound on the optimal
finite Nyman--Beurling distance. -/
theorem distance_le_energy (N : ℕ) :
    BaezDuarteDistance N ≤ energy N := by
  calc
    BaezDuarteDistance N ≤ coefficientEnergy coefficientFamily N :=
      BaezDuarteDistance_le_coefficientEnergy coefficientFamily N
    _ = energy N := (energy_eq_coefficientEnergy N).symm

end RH.Criteria.NymanBeurling.BCFLogTaper
