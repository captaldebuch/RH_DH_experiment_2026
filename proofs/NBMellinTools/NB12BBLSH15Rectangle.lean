/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSOnePoleRemoval

/-!
# NB12t: the correction-preserving rectangle for the actual H15 rows

This file specializes the constructive four-pole BBLS rectangle to the
canonical finite H15 Möbius/log-taper row family.  It introduces no analytic
estimate: every result below is an exact finite identity.

The adaptive damping removes the additional `s = 1` residue along the H15
sequence, but does not by itself control the remaining first-order ledger or
the individual contour edges.  Those two uniform estimates are stated
separately at the end of the file so that they cannot be confused with the
finite contour calculation.
-/

open scoped BigOperators Topology LSeries.notation
open Complex Filter MeasureTheory

namespace NBMellinTools.NB12

open NBMellinTools.NB8

/-! ## Canonical H15 specialization -/

/-- The positive adaptive Abel parameter attached to the actual H15 row
family. -/
noncomputable def h15ContourDamping (n : ℕ) : ℝ :=
  bblsAdaptiveResidueDamping n (h15AdditionalResidueAmplitude n)

theorem h15ContourDamping_pos (n : ℕ) : 0 < h15ContourDamping n :=
  bblsAdaptiveResidueDamping_pos n (h15AdditionalResidueAmplitude n)

theorem tendsto_h15ContourDamping_zero :
    Tendsto h15ContourDamping atTop (nhds 0) :=
  tendsto_bblsAdaptiveResidueDamping_zero h15AdditionalResidueAmplitude

/-- The actual finite signed active Estermann aggregate along the adaptive
H15 damping schedule. -/
noncomputable def h15ActiveContourAggregate (n : ℕ) : ℂ → ℂ :=
  bblsFiniteActiveAggregate (h15ContourDamping n)
    (h15LaurentRowWeight (N := logTaperLength n))
    (h15LaurentRow (N := logTaperLength n))

/-- The actual H15 aggregate after constructive removal of all four displayed
polar modes. -/
noncomputable def h15AllPoleRemoved (n : ℕ) : ℂ → ℂ :=
  bblsFiniteAllPoleRemoved (h15ContourDamping n)
    (h15ContourDamping_pos n)
    (h15LaurentRowWeight (N := logTaperLength n))
    (h15LaurentRow (N := logTaperLength n))

/-- The actual H15 first-order coefficient at `s = 0`. -/
noncomputable def h15GlobalFirstOrderCoefficient (n : ℕ) : ℂ :=
  bblsFiniteFirstOrderAggregate (h15ContourDamping n)
    (h15ContourDamping_pos n)
    (h15LaurentRowWeight (N := logTaperLength n))
    (h15LaurentRow (N := logTaperLength n))

/-- The actual H15 additional residue at `s = 1`. -/
noncomputable def h15GlobalAdditionalResidue (n : ℕ) : ℂ :=
  bblsFiniteAdditionalResidue (h15ContourDamping n)
    (h15LaurentRowWeight (N := logTaperLength n))
    (h15LaurentRow (N := logTaperLength n))

/-- The complete residue ledger visible to a closed H15 rectangle. -/
noncomputable def h15ContourResidueLedger (n : ℕ) : ℂ :=
  h15GlobalFirstOrderCoefficient n + h15GlobalAdditionalResidue n

theorem h15GlobalAdditionalResidue_eq_adaptive (n : ℕ) :
    h15GlobalAdditionalResidue n =
      (h15ContourDamping n : ℂ) * h15AdditionalResidueAmplitude n := by
  rfl

theorem norm_h15GlobalAdditionalResidue_le (n : ℕ) :
    ‖h15GlobalAdditionalResidue n‖ ≤
      1 / ((n + 1 : ℕ) : ℝ) := by
  rw [h15GlobalAdditionalResidue_eq_adaptive]
  exact norm_bblsAdaptiveAdditionalResidue_le n
    (h15AdditionalResidueAmplitude n)

/-- The additional `s=1` part of the specialized H15 ledger vanishes along
the explicit adaptive schedule. -/
theorem tendsto_h15GlobalAdditionalResidue_zero :
    Tendsto h15GlobalAdditionalResidue atTop (nhds 0) := by
  simpa [h15GlobalAdditionalResidue_eq_adaptive] using
    tendsto_h15AdditionalResidue_adaptive_zero

/-- The adaptive `s=1` residue is asymptotically harmless: decay of the
complete rectangle ledger is equivalent to decay of its `s=0` first-order
coefficient. -/
theorem tendsto_h15ContourResidueLedger_zero_iff :
    Tendsto h15ContourResidueLedger atTop (nhds 0) ↔
      Tendsto h15GlobalFirstOrderCoefficient atTop (nhds 0) := by
  constructor
  · intro hledger
    have h := hledger.sub tendsto_h15GlobalAdditionalResidue_zero
    simpa [h15ContourResidueLedger] using h
  · intro hfirst
    simpa [h15ContourResidueLedger] using
      hfirst.add tendsto_h15GlobalAdditionalResidue_zero

/-! ## Exact four-pole identity -/

/-- The generic four-pole decomposition specialized to the actual H15 rows.
The nonzero cubic and quadratic modes found by the stop test are retained. -/
theorem h15ActiveContourAggregate_eq_all_poles_removed
    (n : ℕ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    h15ActiveContourAggregate n s =
      h15AllPoleRemoved n s +
        h15GlobalThirdOrderCoefficient n / s ^ 3 +
        h15GlobalSecondOrderCoefficient (h15ContourDamping n) n / s ^ 2 +
        h15GlobalFirstOrderCoefficient n / s +
        h15GlobalAdditionalResidue n / (s - 1) := by
  exact bblsFiniteActiveAggregate_eq_all_poles_removed
    (h15ContourDamping n) (h15ContourDamping_pos n)
    (h15LaurentRowWeight (N := logTaperLength n))
    (h15LaurentRow (N := logTaperLength n)) hs0 hs1

/-- The specialized pole-removed H15 aggregate is analytic before the next
Gamma pole. -/
theorem analyticAt_h15AllPoleRemoved_of_re_lt_two
    (n : ℕ) {s : ℂ} (hs : s.re < 2) :
    AnalyticAt ℂ (h15AllPoleRemoved n) s := by
  exact analyticAt_bblsFiniteAllPoleRemoved_of_re_lt_two
    (h15ContourDamping n) (h15ContourDamping_pos n)
    (h15LaurentRowWeight (N := logTaperLength n))
    (h15LaurentRow (N := logTaperLength n)) hs

/-! ## Exact H15 rectangle -/

/-- The original active H15 aggregate has precisely the two simple residue
contributions on every admissible rectangle.  The cubic and quadratic modes
are essential locally but integrate to zero on the closed boundary. -/
theorem rectangularBoundaryIntegral_h15ActiveContourAggregate
    (n : ℕ) (σL σR T : ℝ)
    (hL : σL < 0) (hR : 1 < σR) (hR2 : σR < 2) (hT : 0 < T) :
    rectangularBoundaryIntegral (h15ActiveContourAggregate n)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      2 * Real.pi * I * h15ContourResidueLedger n := by
  exact rectangularBoundaryIntegral_bblsFiniteActiveAggregate
    (h15ContourDamping n) (h15ContourDamping_pos n)
    (h15LaurentRowWeight (N := logTaperLength n))
    (h15LaurentRow (N := logTaperLength n))
    σL σR T hL hR hR2 hT

/-- The closed boundary of the completely pole-removed H15 aggregate is
exactly zero. -/
theorem rectangularBoundaryIntegral_h15AllPoleRemoved
    (n : ℕ) (σL σR T : ℝ)
    (hσ : σL ≤ σR) (hR2 : σR < 2) :
    rectangularBoundaryIntegral (h15AllPoleRemoved n)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) = 0 := by
  apply rectangularBoundaryIntegral_eq_zero
  simpa [h15AllPoleRemoved, symmetricLowerCorner, symmetricUpperCorner,
    Complex.mul_re, Complex.mul_im] using
    (differentiableOn_bblsFiniteAllPoleRemoved_rectangle
    (h15ContourDamping n) (h15ContourDamping_pos n)
    (h15LaurentRowWeight (N := logTaperLength n))
    (h15LaurentRow (N := logTaperLength n)) (T := T) hσ hR2)

/-! ## The next uniform analytic gates -/

/-- Horizontal-edge disappearance along a height schedule coupled to the
growing H15 row family.  A height threshold independent of `n` would be an
unjustified strengthening because the Abel damping also moves with `n`. -/
def H15JointHorizontalVanishing : Prop :=
  ∀ σL σR : ℝ, σL < 0 → 1 < σR → σR < 2 →
    ∃ height : ℕ → ℝ,
      Tendsto height atTop atTop ∧
        (∀ n, 0 < height n) ∧
        Tendsto (fun n =>
          symmetricHorizontalEdges (h15AllPoleRemoved n)
            σL σR (height n)) atTop (nhds 0)

/-- The honest dominated-convergence input for the **original active
aggregate** on each fixed line in the absolutely convergent right strip.

It would be incorrect to request this envelope for `h15AllPoleRemoved`: after
global Laurent subtraction that function contains rational `1 / s^j` tails,
including a generally non-integrable first-order tail.  Pole subtraction is a
local holomorphy device for the finite rectangle; vertical absolute
integrability belongs to the original Gamma-damped aggregate, with the polar
ledger retained separately.

No such absolute envelope is requested on the left line, where
`delta_n^sigma` can grow and signed cancellation is essential. -/
def H15ActiveIntegrableMajorantAt (σ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∃ majorant : ℝ → ℝ,
    Integrable majorant ∧ (∀ t, 0 ≤ majorant t) ∧
      ∀ n ≥ n₀, ∀ t : ℝ,
        ‖h15ActiveContourAggregate n ((σ : ℂ) + (t : ℂ) * I)‖ ≤ majorant t

/-- Uniform right-line domination is the collection of the fixed-line
statements over the open strip `1 < Re(s) < 2`. -/
def H15UniformRightLineIntegrableMajorant : Prop :=
  ∀ σ : ℝ, 1 < σ → σ < 2 → H15ActiveIntegrableMajorantAt σ

/-- Exact statement of the now-isolated uniform contour input. -/
structure H15UniformContourPackage : Prop where
  horizontal : H15JointHorizontalVanishing
  rightLineMajorant : H15UniformRightLineIntegrableMajorant

/-- The original active aggregate is continuous on every vertical line in
the right strip.  This is independent of any cutoff-uniform estimate. -/
theorem continuous_h15ActiveContourAggregate_vertical
    (n : ℕ) (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ < 2) :
    Continuous (fun t : ℝ =>
      h15ActiveContourAggregate n ((σ : ℂ) + (t : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hfun :
      (fun u : ℝ =>
        h15ActiveContourAggregate n ((σ : ℂ) + (u : ℂ) * I)) =
      (fun u : ℝ =>
        h15AllPoleRemoved n ((σ : ℂ) + (u : ℂ) * I) +
          h15GlobalThirdOrderCoefficient n /
            ((σ : ℂ) + (u : ℂ) * I) ^ 3 +
          h15GlobalSecondOrderCoefficient (h15ContourDamping n) n /
            ((σ : ℂ) + (u : ℂ) * I) ^ 2 +
          h15GlobalFirstOrderCoefficient n /
            ((σ : ℂ) + (u : ℂ) * I) +
          h15GlobalAdditionalResidue n /
            ((σ : ℂ) + (u : ℂ) * I - 1)) := by
    funext u
    apply h15ActiveContourAggregate_eq_all_poles_removed
    · intro hzero
      have hre := congrArg Complex.re hzero
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        sub_zero, add_zero] at hre
      norm_num at hre
      linarith
    · intro hone
      have hre := congrArg Complex.re hone
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        sub_zero, add_zero, one_re] at hre
      linarith
  rw [hfun]
  have hline : ContinuousAt
      (fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) t := by fun_prop
  have hz0 : (σ : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero] at hre
    norm_num at hre
    linarith
  have hz1 : (σ : ℂ) + (t : ℂ) * I - 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero, one_re] at hre
    norm_num at hre
    linarith
  have hremoved : ContinuousAt (fun u : ℝ =>
      h15AllPoleRemoved n ((σ : ℂ) + (u : ℂ) * I)) t :=
    ContinuousAt.comp
      (f := fun u : ℝ => (σ : ℂ) + (u : ℂ) * I)
      (analyticAt_h15AllPoleRemoved_of_re_lt_two n
        (by simpa using hσ2)).continuousAt hline
  exact ((((hremoved.add
    (continuousAt_const.div (hline.pow 3) (pow_ne_zero 3 hz0))).add
    (continuousAt_const.div (hline.pow 2) (pow_ne_zero 2 hz0))).add
    (continuousAt_const.div hline hz0)).add
    (continuousAt_const.div (hline.sub continuousAt_const) hz1))

/-- The vertical-majorant field gives genuine integrability of every
sufficiently late original H15 aggregate on the chosen line. -/
theorem eventually_integrable_h15ActiveContourAggregate_vertical
    (H : H15UniformRightLineIntegrableMajorant)
    (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ < 2) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Integrable (fun t : ℝ =>
        h15ActiveContourAggregate n ((σ : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨n₀, majorant, hmajorant, hmajorant_nonneg, hbound⟩ :=
    H σ hσ1 hσ2
  refine ⟨n₀, fun n hn => ?_⟩
  have hcontinuous : Continuous (fun t : ℝ =>
      h15ActiveContourAggregate n ((σ : ℂ) + (t : ℂ) * I)) :=
    continuous_h15ActiveContourAggregate_vertical n σ hσ1 hσ2
  apply hmajorant.mono' hcontinuous.aestronglyMeasurable
  filter_upwards with t
  simpa [Real.norm_eq_abs, abs_of_nonneg (hmajorant_nonneg t)] using
    hbound n hn t

end NBMellinTools.NB12
