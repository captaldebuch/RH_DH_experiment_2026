import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorTransferredRemainder

/-!
# Route C: the exact finite transported-residue series

This file identifies the finite residue polynomial occurring in the central
three-term transfer with the sum of its individual transported residue rows.
It then sums the already established coefficient series for those rows.  The
result is an exact `HasSum` statement for the complete finite transfer, with
no asymptotic or analytic-continuation hypothesis.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFiniteTransferSeries

open Complex
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorGeneralCoefficient
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorInfiniteRectangle
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorThreeTermTransfer

/-- The exact contribution of the residue indexed by `n` after the central
three-term transformation. -/
noncomputable def routeCTaylorOneResidueTransferValue (n : ℕ) (z : ℂ) : ℂ :=
  2 * bettinConreyCentralTaylorB (2 * n) *
    ((1 + z) * z ^ (2 * n - 1) -
      (z / (1 + z)) ^ (2 * n - 1))

theorem bettinConreyGZeroFiniteTaylorPolynomial_eq_coefficient_sum
    (z : ℂ) (M : ℕ) :
    bettinConreyGZeroFiniteTaylorPolynomial z M =
      ∑ n ∈ Finset.Icc 1 M,
        routeCTaylorGZeroOddMonomialCoefficient n * z ^ (2 * n - 1) := by
  unfold bettinConreyGZeroFiniteTaylorPolynomial
    routeCTaylorGZeroOddMonomialCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_pow]
  ring

theorem routeCTaylorFinitePolynomialTransfer_eq_residueTransfer_sum
    (z : ℂ) (M : ℕ) :
    routeCTaylorFinitePolynomialTransfer z M =
      ∑ n ∈ Finset.Icc 1 M, routeCTaylorOneResidueTransferValue n z := by
  unfold routeCTaylorFinitePolynomialTransfer
  rw [bettinConreyGZeroFiniteTaylorPolynomial_eq_coefficient_sum,
    bettinConreyGZeroFiniteTaylorPolynomial_eq_coefficient_sum]
  rw [Finset.mul_sum, mul_sub, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  calc
    (Real.pi : ℂ) *
          ((1 + z) *
              (routeCTaylorGZeroOddMonomialCoefficient n *
                z ^ (2 * n - 1))) -
        (Real.pi : ℂ) *
          (routeCTaylorGZeroOddMonomialCoefficient n *
            routeCTaylorMobiusArgument z ^ (2 * n - 1)) =
        ((Real.pi : ℂ) * routeCTaylorGZeroOddMonomialCoefficient n) *
          ((1 + z) * z ^ (2 * n - 1) -
            routeCTaylorMobiusArgument z ^ (2 * n - 1)) := by ring
    _ = routeCTaylorOneResidueTransferValue n z := by
      rw [pi_mul_routeCTaylorGZeroOddMonomialCoefficient n hn1]
      unfold routeCTaylorOneResidueTransferValue routeCTaylorMobiusArgument
      rfl

/-- The complete finite transported residue polynomial has exactly the sum
of the scalar coefficient rows of its constituent residues. -/
theorem hasSum_routeCTaylorFinitePolynomialTransfer
    (z : ℂ) (hz : ‖z‖ < 1) (M : ℕ) :
    HasSum
      (fun m : ℕ =>
        (∑ n ∈ Finset.Icc 1 M,
          routeCTaylorOneResidueScalarCoefficient n m) * z ^ m)
      (routeCTaylorFinitePolynomialTransfer z M) := by
  have hs : HasSum
      (fun m : ℕ => ∑ n ∈ Finset.Icc 1 M,
        routeCTaylorOneResidueScalarCoefficient n m * z ^ m)
      (∑ n ∈ Finset.Icc 1 M, routeCTaylorOneResidueTransferValue n z) := by
    apply hasSum_sum
    intro n hn
    exact hasSum_routeCTaylorOneResidueScalarCoefficient n
      (Finset.mem_Icc.mp hn).1 z hz
  convert hs using 1
  · funext m
    rw [Finset.sum_mul]
  · exact routeCTaylorFinitePolynomialTransfer_eq_residueTransfer_sum z M

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFiniteTransferSeries
