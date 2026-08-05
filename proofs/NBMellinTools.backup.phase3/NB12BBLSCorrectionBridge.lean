/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSActiveLaurent
import NBMellinTools.NB9QuadraticExpansion

/-!
# NB12q: global correction ledger for active Estermann residues

The `1/s` coefficient of one active reflected Estermann row is not its
finite-part term alone. It is the coupled expression

`w2/q - A1*w1 - F(1)`.

Consequently no pointwise statement identifying `F(1)` with the retained
H15 correction is mathematically justified.  Cancellation can only be
tested after the complete arithmetic weights and all rational rows have
been summed.

This file provides that exact finite ledger. It proves the weighted
row-by-row Laurent expansion and defines the global correction gap as the
retained H15 correction plus the complete first-order residue aggregate.
The actual vanishing of that gap remains an explicit theorem target; it is
not assumed or asserted.
-/

open scoped BigOperators Topology LSeries.notation
open Complex Filter Topology

namespace NBMellinTools.NB12

open NBMellinTools.NB9

/-- A reduced rational phase with positive denominator. This is the natural
index type for the active Estermann Laurent package. -/
structure BBLSReducedRational where
  numerator : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator
  coprime : Nat.Coprime numerator denominator

instance (r : BBLSReducedRational) : NeZero r.denominator :=
  ⟨r.denominator_pos.ne'⟩

/-- A fixed choice of the proved active triple-pole package.  The choice is
only of analytic remainder functions; all three polar coefficients are
fixed by the package identity. -/
noncomputable def bblsChosenActiveTriplePolePackage
    (damping : ℝ) (hdamping : 0 < damping)
    (r : BBLSReducedRational) :
    BBLSActiveTriplePolePackage damping r.numerator r.denominator :=
  Classical.choice
    (exists_bblsActiveTriplePolePackage damping hdamping
      r.numerator r.denominator r.coprime)

/-- The third-order coefficient of one reduced active row. -/
noncomputable def bblsActiveThirdOrderCoefficient
    (r : BBLSReducedRational) : ℂ :=
  -(r.denominator : ℂ)⁻¹

/-- The second-order coefficient of one reduced active row. -/
noncomputable def bblsActiveSecondOrderCoefficient
    (damping : ℝ) (r : BBLSReducedRational) : ℂ :=
  (r.denominator : ℂ)⁻¹ *
      (-((Real.eulerMascheroniConstant : ℂ) +
        Complex.log (damping : ℂ))) +
    2 * ((Real.eulerMascheroniConstant : ℂ) -
      Complex.log (r.denominator : ℂ)) / (r.denominator : ℂ)

/-- The complete first-order coefficient.  In particular, the finite-part
value is retained together with both Gamma--Abel Taylor contributions. -/
noncomputable def bblsActiveFirstOrderCoefficient
    (damping : ℝ) (hdamping : 0 < damping)
    (r : BBLSReducedRational) : ℂ :=
  (r.denominator : ℂ)⁻¹ *
      bblsActiveReflectedWeightSecondCoefficient damping -
    (2 * ((Real.eulerMascheroniConstant : ℂ) -
      Complex.log (r.denominator : ℂ)) / (r.denominator : ℂ)) *
        (-((Real.eulerMascheroniConstant : ℂ) +
          Complex.log (damping : ℂ))) -
    (bblsChosenActiveTriplePolePackage damping hdamping r).finitePart 1

/-- Analytic local remainder selected from the proved package. -/
noncomputable def bblsActiveLocalRemainder
    (damping : ℝ) (hdamping : 0 < damping)
    (r : BBLSReducedRational) : ℂ → ℂ :=
  (bblsChosenActiveTriplePolePackage damping hdamping r).remainder

/-- The selected local remainder remains analytic at zero. -/
theorem analyticAt_bblsActiveLocalRemainder
    (damping : ℝ) (hdamping : 0 < damping)
    (r : BBLSReducedRational) :
    AnalyticAt ℂ (bblsActiveLocalRemainder damping hdamping r) 0 :=
  (bblsChosenActiveTriplePolePackage damping hdamping r).remainder_analyticAt

/-- Exact Laurent identity for one selected reduced row. -/
theorem bblsActiveReflectedExpression_eq_selectedLaurent
    (damping : ℝ) (hdamping : 0 < damping)
    (r : BBLSReducedRational) {s : ℂ} (hs : s ≠ 0) :
    bblsActiveReflectedExpression damping
        r.numerator r.denominator s =
      bblsActiveThirdOrderCoefficient r / s ^ 3 +
        bblsActiveSecondOrderCoefficient damping r / s ^ 2 +
        bblsActiveFirstOrderCoefficient damping hdamping r / s +
        bblsActiveLocalRemainder damping hdamping r s := by
  exact (bblsChosenActiveTriplePolePackage
    damping hdamping r).active_identity hs

/-! ## Finite weighted aggregation -/

/-- The complete finite active-row aggregate. -/
noncomputable def bblsFiniteActiveAggregate
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational) (s : ℂ) : ℂ :=
  ∑ i : ι, weight i *
    bblsActiveReflectedExpression damping
      (row i).numerator (row i).denominator s

/-- The weighted third-order aggregate. -/
noncomputable def bblsFiniteThirdOrderAggregate
    {ι : Type*} [Fintype ι]
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) : ℂ :=
  ∑ i : ι, weight i * bblsActiveThirdOrderCoefficient (row i)

/-- The weighted second-order aggregate. -/
noncomputable def bblsFiniteSecondOrderAggregate
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational) : ℂ :=
  ∑ i : ι, weight i *
    bblsActiveSecondOrderCoefficient damping (row i)

/-- The complete weighted first-order residue aggregate. -/
noncomputable def bblsFiniteFirstOrderAggregate
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) : ℂ :=
  ∑ i : ι, weight i *
    bblsActiveFirstOrderCoefficient damping hdamping (row i)

/-- The weighted analytic local remainder. -/
noncomputable def bblsFiniteLocalRemainder
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) (s : ℂ) : ℂ :=
  ∑ i : ι, weight i *
    bblsActiveLocalRemainder damping hdamping (row i) s

/-- A finite weighted sum of the selected local remainders is analytic at
zero. -/
theorem analyticAt_bblsFiniteLocalRemainder
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    AnalyticAt ℂ
      (bblsFiniteLocalRemainder damping hdamping weight row) 0 := by
  unfold bblsFiniteLocalRemainder
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact analyticAt_const.mul
    (analyticAt_bblsActiveLocalRemainder damping hdamping (row i))

/-- Exact weighted Laurent expansion.  All finite arithmetic weights remain
inside their signed aggregates. -/
theorem bblsFiniteActiveAggregate_eq_laurent
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational)
    {s : ℂ} (hs : s ≠ 0) :
    bblsFiniteActiveAggregate damping weight row s =
      ∑ i : ι, weight i *
        (bblsActiveThirdOrderCoefficient (row i) / s ^ 3 +
          bblsActiveSecondOrderCoefficient damping (row i) / s ^ 2 +
          bblsActiveFirstOrderCoefficient damping hdamping (row i) / s +
          bblsActiveLocalRemainder damping hdamping (row i) s) := by
  unfold bblsFiniteActiveAggregate
  apply Finset.sum_congr rfl
  intro i _
  rw [bblsActiveReflectedExpression_eq_selectedLaurent
    damping hdamping (row i) hs]

/-- The same finite Laurent identity with each pole order collected into
one signed global coefficient.  This is the form needed by a rectangle
residue calculation: no absolute values or rowwise correction matching are
introduced. -/
theorem bblsFiniteActiveAggregate_eq_collectedLaurent
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational)
    {s : ℂ} (hs : s ≠ 0) :
    bblsFiniteActiveAggregate damping weight row s =
      bblsFiniteThirdOrderAggregate weight row / s ^ 3 +
        bblsFiniteSecondOrderAggregate damping weight row / s ^ 2 +
        bblsFiniteFirstOrderAggregate damping hdamping weight row / s +
        bblsFiniteLocalRemainder damping hdamping weight row s := by
  rw [bblsFiniteActiveAggregate_eq_laurent damping hdamping weight row hs]
  unfold bblsFiniteThirdOrderAggregate bblsFiniteSecondOrderAggregate
    bblsFiniteFirstOrderAggregate bblsFiniteLocalRemainder
  simp only [mul_add, Finset.sum_add_distrib, Finset.sum_div, mul_div_assoc]

/-! ## The exact correction gap -/

/-- The global correction gap.  The retained correction must be coupled to
the complete first-order residue aggregate, not to the finite-part term
alone. -/
noncomputable def bblsGlobalCorrectionGap
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (retainedCorrection : ℂ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational) : ℂ :=
  retainedCorrection +
    bblsFiniteFirstOrderAggregate damping hdamping weight row

/-- Exact proposition that the active residue reproduces the negative of
the retained correction.  This is the honest correction-matching target. -/
def BBLSGlobalCorrectionMatching
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (retainedCorrection : ℂ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational) : Prop :=
  bblsGlobalCorrectionGap damping hdamping
    retainedCorrection weight row = 0

/-- Correction matching is exactly equality of the complete residue
aggregate with the negative retained correction. -/
theorem bblsGlobalCorrectionMatching_iff
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (retainedCorrection : ℂ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational) :
    BBLSGlobalCorrectionMatching damping hdamping
        retainedCorrection weight row ↔
      bblsFiniteFirstOrderAggregate damping hdamping weight row =
        -retainedCorrection := by
  unfold BBLSGlobalCorrectionMatching bblsGlobalCorrectionGap
  constructor
  · intro h
    calc
      bblsFiniteFirstOrderAggregate damping hdamping weight row =
          (retainedCorrection +
              bblsFiniteFirstOrderAggregate damping hdamping weight row) -
            retainedCorrection := by ring
      _ = -retainedCorrection := by rw [h]; ring
  · intro h
    rw [h]
    ring

/-- Specialization of the ledger to the exact retained correction from the
Báez--Duarte quadratic form.  The row family and its complex scaling remain
parameters until the BBLS-to-H15 numerator completion is proved. -/
noncomputable def bblsH15CorrectionGap
    {ι : Type*} [Fintype ι]
    (N : ℕ) (coeffs : Fin N → ℝ)
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) : ℂ :=
  bblsGlobalCorrectionGap damping hdamping
    (bdCorrectionTerm N coeffs : ℂ) weight row

/-- The specialized H15 gap vanishes exactly when the complete weighted
first-order residue aggregate cancels the retained Báez--Duarte correction.
The theorem still leaves the H15 row realization and this equality to be
proved; it does not manufacture either one. -/
theorem bblsH15CorrectionGap_eq_zero_iff
    {ι : Type*} [Fintype ι]
    (N : ℕ) (coeffs : Fin N → ℝ)
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    bblsH15CorrectionGap N coeffs damping hdamping weight row = 0 ↔
      bblsFiniteFirstOrderAggregate damping hdamping weight row =
        -(bdCorrectionTerm N coeffs : ℂ) := by
  change BBLSGlobalCorrectionMatching damping hdamping
      (bdCorrectionTerm N coeffs : ℂ) weight row ↔ _
  exact bblsGlobalCorrectionMatching_iff damping hdamping
    (bdCorrectionTerm N coeffs : ℂ) weight row

end NBMellinTools.NB12
