/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15ThreeHalfLine

/-!
# NB12w: correction-preserving signed passage on the H15 right line

The rowwise absolute majorant on `Re(s)=3/2` loses a factor `q^2` and does
not pass the current cutoff stop test.  This file therefore records the
right replacement:

* an exact finite-rectangle identity in which the residue correction remains
  a separate conserved ledger;
* an exact compact/tail decomposition of the `L¹` mass **after** the signed
  H15 rows have been aggregated;
* the weakest cofinal compact-decay and tail-tightness package sufficient to
  pass to the infinite right edge.

No signed cancellation estimate is asserted here.  The package at the end is
the newly isolated arithmetic input.
-/

open scoped Topology Interval Real
open Complex Filter MeasureTheory Set

namespace NBMellinTools.NB12

/-! ## Exact correction-preserving finite rectangle -/

/-- The active H15 aggregate restricted to a vertical line. -/
noncomputable def h15VerticalAggregate
    (n : ℕ) (σ t : ℝ) : ℂ :=
  h15ActiveContourAggregate n ((σ : ℂ) + (t : ℂ) * I)

/-- The symmetric truncated integral of the active aggregate. -/
noncomputable def h15TruncatedVerticalIntegral
    (n : ℕ) (σ T : ℝ) : ℂ :=
  ∫ t : ℝ in -T..T, h15VerticalAggregate n σ t

/-- The right edge with the complete two-residue ledger retained rather than
absorbed into an absolute-value estimate. -/
noncomputable def h15CorrectedThreeHalfRightEdge
    (n : ℕ) (T : ℝ) : ℂ :=
  I * h15TruncatedVerticalIntegral n (3 / 2) T -
    2 * Real.pi * I * h15ContourResidueLedger n

/-- Exact finite transfer from the corrected right edge to the left edge and
the horizontal pair.  This is the correction-preserving form of the H15
rectangle: no residue is discarded and no triangle inequality is used. -/
theorem h15CorrectedThreeHalfRightEdge_eq_left_sub_horizontal
    (n : ℕ) (σL T : ℝ) (hL : σL < 0) (hT : 0 < T) :
    h15CorrectedThreeHalfRightEdge n T =
      I * h15TruncatedVerticalIntegral n σL T -
        symmetricHorizontalEdges (h15ActiveContourAggregate n)
          σL (3 / 2) T := by
  have hrect := rectangularBoundaryIntegral_h15ActiveContourAggregate
    n σL (3 / 2) T hL (by norm_num) (by norm_num) hT
  unfold rectangularBoundaryIntegral rectangularRightEdge rectangularLeftEdge
    at hrect
  simp only [symmetricLowerCorner, symmetricUpperCorner,
    Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, zero_sub, add_zero, Complex.sub_im,
    Complex.add_im, sub_self, zero_add] at hrect
  unfold h15CorrectedThreeHalfRightEdge h15TruncatedVerticalIntegral
    h15VerticalAggregate symmetricHorizontalEdges
  simp only [symmetricLowerCorner, symmetricUpperCorner]
  linear_combination hrect

/-! ## Signed `L¹` compact/tail split -/

/-- The complete vertical integral on the fixed right edge. -/
noncomputable def h15ThreeHalfVerticalIntegral (n : ℕ) : ℂ :=
  ∫ t : ℝ, h15VerticalAggregate n (3 / 2) t

/-- `L¹` mass of the already-aggregated signed H15 family.  The norm is taken
only after summing all rows, unlike the failed arithmetic-mass bound. -/
noncomputable def h15ThreeHalfSignedL1Mass (n : ℕ) : ℝ :=
  ∫ t : ℝ, ‖h15VerticalAggregate n (3 / 2) t‖

/-- Compact-window part of the signed aggregate mass. -/
noncomputable def h15ThreeHalfCompactL1Mass
    (n : ℕ) (T : ℝ) : ℝ :=
  ∫ t : ℝ in Icc (-T) T, ‖h15VerticalAggregate n (3 / 2) t‖

/-- Complementary tail of the signed aggregate mass. -/
noncomputable def h15ThreeHalfTailL1Mass
    (n : ℕ) (T : ℝ) : ℝ :=
  ∫ t : ℝ in (Icc (-T) T)ᶜ, ‖h15VerticalAggregate n (3 / 2) t‖

theorem integrable_norm_h15VerticalAggregate_threeHalf (n : ℕ) :
    Integrable (fun t : ℝ => ‖h15VerticalAggregate n (3 / 2) t‖) := by
  exact (integrable_h15ActiveContourAggregate_threeHalf n).norm

/-- Exact compact/tail partition.  Crucially, this is performed after signed
aggregation and hence does not reproduce the rowwise `q^2` loss. -/
theorem h15ThreeHalfSignedL1Mass_eq_compact_add_tail
    (n : ℕ) (T : ℝ) :
    h15ThreeHalfSignedL1Mass n =
      h15ThreeHalfCompactL1Mass n T +
        h15ThreeHalfTailL1Mass n T := by
  symm
  simpa [h15ThreeHalfSignedL1Mass, h15ThreeHalfCompactL1Mass,
    h15ThreeHalfTailL1Mass] using
    (integral_add_compl (μ := volume) measurableSet_Icc
      (integrable_norm_h15VerticalAggregate_threeHalf n))

theorem h15ThreeHalfSignedL1Mass_nonneg (n : ℕ) :
    0 ≤ h15ThreeHalfSignedL1Mass n := by
  unfold h15ThreeHalfSignedL1Mass
  exact integral_nonneg fun _ => norm_nonneg _

/-- Cofinal signed `L¹` control on the right line.  The compact and tail
estimates may use the same moving radius; requiring that radius to tend to
infinity prevents a vacuous fixed-window split. -/
structure H15SignedThreeHalfL1Tightness where
  radius : ℕ → ℝ
  radius_tendsto : Tendsto radius atTop atTop
  compact_decay : Tendsto
    (fun n => h15ThreeHalfCompactL1Mass n (radius n))
    atTop (nhds 0)
  tail_decay : Tendsto
    (fun n => h15ThreeHalfTailL1Mass n (radius n))
    atTop (nhds 0)

/-- Compact signed decay plus uniform tail tightness gives decay of the full
post-aggregation `L¹` mass. -/
theorem h15ThreeHalfSignedL1Mass_tendsto_zero
    (H : H15SignedThreeHalfL1Tightness) :
    Tendsto h15ThreeHalfSignedL1Mass atTop (nhds 0) := by
  have hsum : Tendsto
      (fun n => h15ThreeHalfCompactL1Mass n (H.radius n) +
        h15ThreeHalfTailL1Mass n (H.radius n))
      atTop (nhds 0) := by
    simpa using H.compact_decay.add H.tail_decay
  have heq : h15ThreeHalfSignedL1Mass =
      (fun n => h15ThreeHalfCompactL1Mass n (H.radius n) +
        h15ThreeHalfTailL1Mass n (H.radius n)) := by
    funext n
    exact h15ThreeHalfSignedL1Mass_eq_compact_add_tail n (H.radius n)
  rw [heq]
  exact hsum

/-- The signed `L¹` package is sufficient for the complete right-line
integral to vanish. -/
theorem h15ThreeHalfVerticalIntegral_tendsto_zero
    (H : H15SignedThreeHalfL1Tightness) :
    Tendsto h15ThreeHalfVerticalIntegral atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (g := h15ThreeHalfSignedL1Mass)
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · exact Eventually.of_forall fun n => by
      simpa [h15ThreeHalfVerticalIntegral, h15ThreeHalfSignedL1Mass,
        h15VerticalAggregate] using
        (norm_integral_le_integral_norm
          (fun t : ℝ => h15VerticalAggregate n (3 / 2) t))
  · exact h15ThreeHalfSignedL1Mass_tendsto_zero H

/-- With the correction ledger also decaying, the correction-preserving
right-edge expression tends to zero.  The ledger is an explicit hypothesis;
it has not been hidden in the analytic remainder. -/
theorem h15CorrectedThreeHalfInfiniteRightEdge_tendsto_zero
    (H : H15SignedThreeHalfL1Tightness)
    (hledger : Tendsto h15ContourResidueLedger atTop (nhds 0)) :
    Tendsto (fun n =>
      I * h15ThreeHalfVerticalIntegral n -
        2 * Real.pi * I * h15ContourResidueLedger n)
      atTop (nhds 0) := by
  simpa using
    ((h15ThreeHalfVerticalIntegral_tendsto_zero H).const_mul I).sub
      (hledger.const_mul (2 * Real.pi * I))

end NBMellinTools.NB12
