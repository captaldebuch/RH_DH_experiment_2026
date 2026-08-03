import RiemannHypothesis.Criteria.NymanBeurling.BCFQuadraticTaper

/-!
# Exact finite transfer identities for the quadratic taper

The quadratic cutoff is not an independent mysterious profile: on the
`N`-term coefficient range it is exactly the square of the triangular cutoff
used by `cutoffMobiusCoefficientFamily`.  This module records that finite
identity and isolates the exact coefficient defects between the quadratic,
triangular, and logarithmic families.

These are algebraic decompositions, not energy comparisons.  In particular,
turning either pointwise approximant decomposition into convergence of the
quadratic energy still requires an `L²` estimate for the displayed defect.
-/

namespace RH.Criteria.NymanBeurling.BCFQuadraticTaperTransfer

open scoped BigOperators
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.CoefficientFamilies
open RH.Criteria.NymanBeurling.BCFLogTaper

/-- The triangular cutoff profile occurring in the project-native H15
coefficient family.  It is only used below on `1 ≤ n ≤ N`. -/
noncomputable def triangularWeight (N n : ℕ) : ℝ :=
  1 - (n : ℝ) / ((N + 1 : ℕ) : ℝ)

/-- On the finite coefficient range, the quadratic taper is exactly the
square of the triangular taper. -/
theorem quadraticWeight_eq_triangularWeight_sq
    {N n : ℕ} (hn : n ≤ N + 1) :
    BCFQuadraticTaper.quadraticWeight N n = triangularWeight N n ^ 2 := by
  rw [BCFQuadraticTaper.quadraticWeight_of_le hn]
  rfl

/-- The quadratic coefficient is the triangular H15 coefficient multiplied
entrywise by one additional triangular cutoff factor. -/
theorem quadraticCoeff_eq_cutoffCoeff_mul_weight (N : ℕ) (i : Fin N) :
    BCFQuadraticTaper.coefficientFamily.coeff N i =
      cutoffMobiusCoefficientFamily.coeff N i *
        triangularWeight N (i.val + 1) := by
  have hi : i.val + 1 ≤ N + 1 := by omega
  simp only [BCFQuadraticTaper.coefficientFamily,
    cutoffMobiusCoefficientFamily]
  rw [show BCFQuadraticTaper.quadraticWeight N (i.val + 1) =
      triangularWeight N (i.val + 1) ^ 2 from
    quadraticWeight_eq_triangularWeight_sq hi]
  simp only [triangularWeight, Nat.cast_add, Nat.cast_one]
  ring

/-- The explicit extra coefficient which changes the triangular cutoff into
the quadratic cutoff. -/
noncomputable def quadraticTriangularDefectCoeff
    (N : ℕ) (i : Fin N) : ℝ :=
  (((ArithmeticFunction.moebius (i.val + 1) : ℤ) : ℝ) *
    triangularWeight N (i.val + 1) *
      (1 - triangularWeight N (i.val + 1)))

/-- Exact coefficient-level triangular-to-quadratic decomposition. -/
theorem quadraticCoeff_eq_cutoffCoeff_add_defect (N : ℕ) (i : Fin N) :
    BCFQuadraticTaper.coefficientFamily.coeff N i =
      cutoffMobiusCoefficientFamily.coeff N i +
        quadraticTriangularDefectCoeff N i := by
  rw [quadraticCoeff_eq_cutoffCoeff_mul_weight]
  simp only [cutoffMobiusCoefficientFamily, quadraticTriangularDefectCoeff]
  simp only [triangularWeight, Nat.cast_add, Nat.cast_one]
  ring

/-- Consequently, the quadratic approximant is pointwise the triangular H15
approximant plus the finite defect combination. -/
theorem quadraticApproximant_eq_cutoffApprox_add_defect
    (N : ℕ) (x : ℝ) :
    BCFQuadraticTaper.approximant N x =
      bdApprox N (cutoffMobiusCoefficientFamily.coeff N) x +
        bdApprox N (quadraticTriangularDefectCoeff N) x := by
  unfold BCFQuadraticTaper.approximant bdApprox
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [quadraticCoeff_eq_cutoffCoeff_add_defect]
  ring

/-- The exact coefficient defect from the logarithmic BCF family to the
quadratic family. -/
noncomputable def quadraticLogDefectCoeff (N : ℕ) (i : Fin N) : ℝ :=
  BCFQuadraticTaper.coefficientFamily.coeff N i -
    BCFLogTaper.coefficientFamily.coeff N i

/-- Exact coefficient-level log-to-quadratic decomposition. -/
theorem quadraticCoeff_eq_logCoeff_add_defect (N : ℕ) (i : Fin N) :
    BCFQuadraticTaper.coefficientFamily.coeff N i =
      BCFLogTaper.coefficientFamily.coeff N i +
        quadraticLogDefectCoeff N i := by
  unfold quadraticLogDefectCoeff
  ring

/-- Exact pointwise decomposition relative to the BCF logarithmic taper.
This identifies the precise finite function whose `L²` control would be
needed for a genuine energy transfer theorem. -/
theorem quadraticApproximant_eq_logApprox_add_defect
    (N : ℕ) (x : ℝ) :
    BCFQuadraticTaper.approximant N x =
      BCFLogTaper.approximant N x +
        bdApprox N (quadraticLogDefectCoeff N) x := by
  unfold BCFQuadraticTaper.approximant BCFLogTaper.approximant bdApprox
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [quadraticCoeff_eq_logCoeff_add_defect]
  ring

end RH.Criteria.NymanBeurling.BCFQuadraticTaperTransfer
