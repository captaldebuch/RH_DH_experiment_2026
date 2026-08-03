import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaper
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Finite contour infrastructure for the BCF logarithmic taper

This is the residue-free finite component of WP1.  The BCF Dirichlet
polynomial is entire, so its integral around every finite rectangle vanishes.
The theorem deliberately concerns only the finite polynomial: introducing the
zeta factor or identifying a contour expression with the BCF energy requires
the separate Mellin/Plancherel bridge and a pole accounting theorem.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperContour

open scoped BigOperators
open Complex Set
open RH.Criteria.NymanBeurling.BCFLogTaper

/-- The finite BCF Dirichlet polynomial is entire. -/
theorem differentiable_dirichletPolynomial (N : ℕ) :
    Differentiable ℂ (dirichletPolynomial N) := by
  unfold dirichletPolynomial
  rw [show (fun s : ℂ => ∑ n ∈ Finset.Icc 1 N,
      (dirichletCoeff N n : ℂ) * ((n : ℂ) ^ (-s))) =
      ∑ n ∈ Finset.Icc 1 N,
        fun s : ℂ => (dirichletCoeff N n : ℂ) * ((n : ℂ) ^ (-s)) by
    ext s
    simp]
  exact Differentiable.sum fun n hn => by
    apply Differentiable.const_mul
    apply Differentiable.const_cpow differentiable_id.neg
    left
    exact_mod_cast
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1))

/-- The explicit finite-height rectangular contour identity for the BCF
Dirichlet polynomial.  It is residue-free because this finite polynomial is
entire. -/
theorem dirichletPolynomial_boundary_rect_eq_zero (N : ℕ) (z w : ℂ) :
    (∫ x : ℝ in z.re..w.re, dirichletPolynomial N (x + z.im * I)) -
        (∫ x : ℝ in z.re..w.re, dirichletPolynomial N (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, dirichletPolynomial N (re w + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, dirichletPolynomial N (re z + y * I)) = 0 := by
  apply integral_boundary_rect_eq_zero_of_differentiableOn
  exact (differentiable_dirichletPolynomial N).differentiableOn

end RH.Criteria.NymanBeurling.BCFLogTaperContour
