/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryLinearTraceDecay

/-!
# NB12zzy: the localized Laurent-row projection

The raw H15 contour family is indexed by all valid primitive triples and both
orientations.  The active final boundary is first localized at a fixed gcd
slice `g` and a dyadic outer-modulus block `[Q,2Q)`.  This file applies that
same restriction to the verified Laurent family and proves the resulting
support and coefficient formulas.

This is only the coefficient-support part of the contour-to-boundary
projection.  The transformed frequency `r`, endpoint cutoff `U`, square-
divisor incidence and endpoint completion do not occur in the raw Laurent
row index and therefore remain genuine downstream ledgers.
-/

open Filter Complex
open scoped BigOperators Topology ArithmeticFunction.Moebius

namespace NBMellinTools.NB12

/-- The raw Laurent indices in one fixed gcd slice and one supported dyadic
primitive-denominator block. -/
def h15LocalizedLaurentRowIndices
    (N g Q : ℕ) : Finset (H15LaurentRowIndex N) :=
  Finset.univ.filter fun i =>
    h15LaurentG i = g ∧
      h15LaurentQ i ∈ h15BettinChandeeSupportedNatBlock N g Q

theorem mem_h15LocalizedLaurentRowIndices
    {N g Q : ℕ} {i : H15LaurentRowIndex N} :
    i ∈ h15LocalizedLaurentRowIndices N g Q ↔
      h15LaurentG i = g ∧
        h15LaurentQ i ∈ h15BettinChandeeSupportedNatBlock N g Q := by
  simp [h15LocalizedLaurentRowIndices]

/-- Every localized row has exactly the outer-modulus support used by the
active final boundary. -/
theorem h15LocalizedLaurentRow_outerModulus_bounds
    {N g Q : ℕ} {i : H15LaurentRowIndex N}
    (hi : i ∈ h15LocalizedLaurentRowIndices N g Q) :
    Q ≤ h15LaurentQ i ∧ h15LaurentQ i < 2 * Q ∧
      g * h15LaurentQ i ≤ N := by
  exact mem_h15BettinChandeeSupportedNatBlock.mp
    (mem_h15LocalizedLaurentRowIndices.mp hi).2

/-- On a valid localized row, the contour coefficient is literally the
fixed-`g` product of the two natural log-taper coefficients. -/
theorem h15LaurentRowWeight_eq_on_localized_valid
    {N g Q : ℕ} {i : H15LaurentRowIndex N}
    (hi : i ∈ h15LocalizedLaurentRowIndices N g Q)
    (hvalid : h15LaurentRowValid i) :
    h15LaurentRowWeight i =
      (h15NaturalLogTaperCoeff N (g * h15LaurentA i) *
        h15NaturalLogTaperCoeff N (g * h15LaurentQ i) /
        (g : ℝ) * Real.pi /
        ((h15LaurentA i : ℝ) * (h15LaurentQ i : ℝ)) : ℝ) := by
  have hg := (mem_h15LocalizedLaurentRowIndices.mp hi).1
  unfold h15LaurentRowWeight
  rw [if_pos hvalid, hg]

/-- The Estermann contour aggregate restricted to the same fixed gcd slice
and dyadic outer-modulus support as the active boundary. -/
noncomputable def h15LocalizedActiveContourAggregate
    (n g Q : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ h15LocalizedLaurentRowIndices (NB8.logTaperLength n) g Q,
    h15LaurentRowWeight i *
      bblsActiveReflectedExpression (h15ContourDamping n)
        (h15LaurentRow i).numerator (h15LaurentRow i).denominator s

/-- The complementary raw Laurent rows, retained as an exact ledger. -/
noncomputable def h15ComplementaryActiveContourAggregate
    (n g Q : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ (Finset.univ : Finset
      (H15LaurentRowIndex (NB8.logTaperLength n))).filter
        (fun i => i ∉ h15LocalizedLaurentRowIndices
          (NB8.logTaperLength n) g Q),
    h15LaurentRowWeight i *
      bblsActiveReflectedExpression (h15ContourDamping n)
        (h15LaurentRow i).numerator (h15LaurentRow i).denominator s

/-- Exact support projection of the raw contour family.  Nothing is thrown
away: rows outside the active `(g,Q)` slice remain in the complementary
ledger. -/
theorem h15ActiveContourAggregate_eq_localized_add_complement
    (n g Q : ℕ) (s : ℂ) :
    h15ActiveContourAggregate n s =
      h15LocalizedActiveContourAggregate n g Q s +
        h15ComplementaryActiveContourAggregate n g Q s := by
  classical
  unfold h15ActiveContourAggregate bblsFiniteActiveAggregate
    h15LocalizedActiveContourAggregate
    h15ComplementaryActiveContourAggregate
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset
      (H15LaurentRowIndex (NB8.logTaperLength n))))
    (p := fun i => i ∈ h15LocalizedLaurentRowIndices
      (NB8.logTaperLength n) g Q)]
  simp

/-- An unsupported dyadic slice has no localized contour contribution, in
agreement with the corresponding final-boundary support theorem. -/
theorem h15LocalizedActiveContourAggregate_eq_zero_of_lt
    {n g Q : ℕ} (h : NB8.logTaperLength n < g * Q) (s : ℂ) :
    h15LocalizedActiveContourAggregate n g Q s = 0 := by
  unfold h15LocalizedActiveContourAggregate h15LocalizedLaurentRowIndices
  rw [h15BettinChandeeSupportedNatBlock_eq_empty_of_lt h]
  simp

end NBMellinTools.NB12
