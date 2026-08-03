import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorThreeTermTransfer

/-!
# Route C: the first nonzero Taylor coefficient

This module checks the normalization of the contour calculation at degree
two.  The logarithmic elementary row contributes `1/6`.  The first odd
Taylor residue of `g₀`, after transport through `z ↦ z/(1+z)`, contributes
`pi^2/18`.  Their sum is exactly Bettin--Conrey's displayed coefficient
`a₂`.

The calculation also retains an exact cubic remainder for the transported
`M=1` residue polynomial.  Thus the equality is coefficient-level data, not
a numerical comparison or a truncated approximation.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorBaseCoefficient

open Complex
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorInfiniteRectangle
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorThreeTermTransfer

/-- Coefficient of `u` in the `M=1` contour polynomial for `g₀`, written in
the literal Bernoulli--zeta normalization produced by the residue theorem. -/
noncomputable def routeCTaylorGZeroLinearResidueCoefficient : ℂ :=
  2 * (-1 : ℂ) ^ (1 : ℕ) * (((bernoulli 2 : ℚ) : ℂ)) /
      (Nat.factorial 2 : ℂ) *
    riemannZeta (-1 : ℂ) * (2 * Real.pi : ℂ)

/-- The first contour coefficient evaluates to `pi/36`. -/
theorem routeCTaylorGZeroLinearResidueCoefficient_eq :
    routeCTaylorGZeroLinearResidueCoefficient =
      (Real.pi : ℂ) / 36 := by
  unfold routeCTaylorGZeroLinearResidueCoefficient
  rw [show (-1 : ℂ) = -(1 : ℕ) by norm_num,
    riemannZeta_neg_nat_eq_bernoulli]
  norm_num [bernoulli_two]
  ring

/-- At order one, the complete finite `g₀` polynomial consists of exactly
the preceding linear monomial. -/
theorem bettinConreyGZeroFiniteTaylorPolynomial_one
    (z : ℂ) :
    bettinConreyGZeroFiniteTaylorPolynomial z 1 =
      routeCTaylorGZeroLinearResidueCoefficient * z := by
  unfold bettinConreyGZeroFiniteTaylorPolynomial
    routeCTaylorGZeroLinearResidueCoefficient
  norm_num [Finset.sum_Icc_succ_top, routeCTaylorPolePoint]
  ring

/-- Closed rational form of the transported first residue. -/
theorem routeCTaylorFinitePolynomialTransfer_one
    (z : ℂ) :
    routeCTaylorFinitePolynomialTransfer z 1 =
      (Real.pi : ℂ) ^ 2 / 36 *
        ((1 + z) * z - z / (1 + z)) := by
  unfold routeCTaylorFinitePolynomialTransfer
  rw [bettinConreyGZeroFiniteTaylorPolynomial_one,
    bettinConreyGZeroFiniteTaylorPolynomial_one,
    routeCTaylorGZeroLinearResidueCoefficient_eq]
  unfold routeCTaylorMobiusArgument
  ring

/-- Exact degree-two extraction from the first transported residue.  The
discarded part is displayed, rather than hidden behind `O(z^3)`. -/
theorem routeCTaylorFinitePolynomialTransfer_one_eq_base_add_cubic
    (z : ℂ) (hz : 1 + z ≠ 0) :
    routeCTaylorFinitePolynomialTransfer z 1 =
      (Real.pi : ℂ) ^ 2 / 18 * z ^ 2 -
        (Real.pi : ℂ) ^ 2 / 36 * (z ^ 3 / (1 + z)) := by
  rw [routeCTaylorFinitePolynomialTransfer_one]
  field_simp [hz]
  ring

/-- The elementary logarithmic Taylor row has degree-two coefficient
`1/(2*3)=1/6`.  It is named separately to keep the two analytic sources of
the base coefficient visible. -/
noncomputable def routeCTaylorElementaryBaseCoefficient : ℂ :=
  1 / 6

/-- The complete coefficient predicted by the contour transport at degree
two. -/
noncomputable def routeCTaylorContourBaseCoefficient : ℂ :=
  routeCTaylorElementaryBaseCoefficient + (Real.pi : ℂ) ^ 2 / 18

/-- Direct evaluation of Bettin--Conrey's displayed finite formula at
`m=2`. -/
theorem bettinConreyCentralTaylorCoefficient_two :
    bettinConreyCentralTaylorCoefficient 2 =
      1 / 6 + (Real.pi : ℂ) ^ 2 / 18 := by
  simp [bettinConreyCentralTaylorCoefficient,
    bettinConreyCentralTaylorB, bernoulli_two, riemannZeta_two]
  ring

/-- **Taylor base-case coefficient equality.**  The contour-derived
elementary-plus-residue coefficient is exactly the source coefficient `a₂`. -/
theorem routeCTaylorContourBaseCoefficient_eq_centralCoefficient :
    routeCTaylorContourBaseCoefficient =
      bettinConreyCentralTaylorCoefficient 2 := by
  rw [bettinConreyCentralTaylorCoefficient_two]
  rfl

/-- In the signed scalar convention used by the native power series, degree
two has the same value because `(-1)^2=1`. -/
theorem routeCTaylorContourBaseCoefficient_eq_scalarCoefficient_two :
    routeCTaylorContourBaseCoefficient =
      bettinConreyPsiZeroTaylorScalarCoefficient 2 := by
  rw [routeCTaylorContourBaseCoefficient_eq_centralCoefficient]
  simp [bettinConreyPsiZeroTaylorScalarCoefficient]

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorBaseCoefficient
