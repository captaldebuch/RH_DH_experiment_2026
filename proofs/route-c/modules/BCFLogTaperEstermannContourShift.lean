import Mathlib.Analysis.Complex.CauchyIntegral
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi

/-!
# Route B7: a finite rectangular Estermann contour shift

This file supplies the contour geometry which was deliberately absent from
`BCFLogTaperEstermannVoronoi`.  It proves the exact four-edge identity for a
holomorphic integrand, specializes it to a pole-subtracted Estermann
integrand, and identifies the coefficient of the possible double pole at the
crossed point `s = 0`.

The file does **not** assume that the horizontal edges vanish.  Nor does it
assert a Kuznetsov estimate.  Those are separate analytic inputs: Cauchy's
The Cauchy theorem fixes the signs and pole geometry, but it cannot provide decay or
signed cross-modulus cancellation.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift

open Complex Filter Set Topology
open scoped Interval Real
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFunctionalEquation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi

/-! ## Oriented edges of a rectangle -/

/-- The lower horizontal edge, oriented from the real part of `z` to that of
`w`. -/
noncomputable def rectangularLowerEdge
    (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  ∫ x : ℝ in z.re..w.re, f (x + z.im * I)

/-- The upper horizontal edge with the sign induced by positive boundary
orientation. -/
noncomputable def rectangularUpperEdge
    (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  -∫ x : ℝ in z.re..w.re, f (x + w.im * I)

/-- The right vertical edge, including the factor `ds = I dt`. -/
noncomputable def rectangularRightEdge
    (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  I * ∫ y : ℝ in z.im..w.im, f (w.re + y * I)

/-- The left vertical edge with the sign induced by positive boundary
orientation. -/
noncomputable def rectangularLeftEdge
    (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  -(I * ∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- The positively oriented integral around the rectangular boundary. -/
noncomputable def rectangularBoundaryIntegral
    (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  rectangularLowerEdge f z w + rectangularUpperEdge f z w +
    rectangularRightEdge f z w + rectangularLeftEdge f z w

/-- Cauchy--Goursat, expressed in the four-edge notation used by the
Estermann contour shift. -/
theorem rectangularBoundaryIntegral_eq_zero
    (f : ℂ → ℂ) (z w : ℂ)
    (hf : DifferentiableOn ℂ f
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectangularBoundaryIntegral f z w = 0 := by
  simpa [rectangularBoundaryIntegral, rectangularLowerEdge,
    rectangularUpperEdge, rectangularRightEdge, rectangularLeftEdge,
    smul_eq_mul] using
      (Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf)

/-- Exact finite contour movement: right vertical equals left vertical minus
the two horizontal contributions, with all orientations fixed. -/
theorem rectangularRightEdge_eq_of_differentiableOn
    (f : ℂ → ℂ) (z w : ℂ)
    (hf : DifferentiableOn ℂ f
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectangularRightEdge f z w =
      -rectangularLeftEdge f z w - rectangularLowerEdge f z w -
        rectangularUpperEdge f z w := by
  have h := rectangularBoundaryIntegral_eq_zero f z w hf
  unfold rectangularBoundaryIntegral at h
  linear_combination h

/-! ## Passage from finite rectangles to vertical lines -/

/-- Lower-left corner of the symmetric-height rectangle with real part
`σ`. -/
noncomputable def symmetricLowerCorner (σ T : ℝ) : ℂ :=
  (σ : ℂ) - (T : ℂ) * I

/-- Upper-right corner of the symmetric-height rectangle with real part
`σ`. -/
noncomputable def symmetricUpperCorner (σ T : ℝ) : ℂ :=
  (σ : ℂ) + (T : ℂ) * I

/-- A finite symmetric vertical integral, without the differential factor
`I`. -/
noncomputable def truncatedVerticalIntegral
    (f : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  ∫ t : ℝ in -T..T, f ((σ : ℂ) + (t : ℂ) * I)

/-- The sum of the two oriented horizontal edges of a symmetric-height
rectangle. -/
noncomputable def symmetricHorizontalEdges
    (f : ℂ → ℂ) (σL σR T : ℝ) : ℂ :=
  rectangularLowerEdge f (symmetricLowerCorner σL T)
      (symmetricUpperCorner σR T) +
    rectangularUpperEdge f (symmetricLowerCorner σL T)
      (symmetricUpperCorner σR T)

/-- A residue identity on every sufficiently high rectangle, convergence of
both truncated vertical integrals, and vanishing of the *coupled* horizontal
pair imply the infinite-line contour shift.  Notice the residue becomes
`2π r` after cancelling the common differential factor `I`. -/
theorem verticalLimit_eq_of_rectangularBoundary
    (f : ℂ → ℂ) (σL σR : ℝ) (r leftValue rightValue : ℂ)
    (hboundary : ∀ T : ℝ, 0 < T →
      rectangularBoundaryIntegral f (symmetricLowerCorner σL T)
        (symmetricUpperCorner σR T) = 2 * Real.pi * I * r)
    (hleft : Tendsto (truncatedVerticalIntegral f σL) atTop
      (nhds leftValue))
    (hright : Tendsto (truncatedVerticalIntegral f σR) atTop
      (nhds rightValue))
    (hhorizontal : Tendsto (symmetricHorizontalEdges f σL σR) atTop
      (nhds 0)) :
    rightValue = leftValue + 2 * Real.pi * r := by
  have hedge : Filter.Eventually (fun T : ℝ =>
      I * truncatedVerticalIntegral f σR T =
        I * truncatedVerticalIntegral f σL T -
          symmetricHorizontalEdges f σL σR T + 2 * Real.pi * I * r) atTop := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have h := hboundary T hT
    unfold rectangularBoundaryIntegral at h
    have hedge' :
        rectangularRightEdge f (symmetricLowerCorner σL T)
            (symmetricUpperCorner σR T) =
          -rectangularLeftEdge f (symmetricLowerCorner σL T)
              (symmetricUpperCorner σR T) -
            symmetricHorizontalEdges f σL σR T + 2 * Real.pi * I * r := by
      unfold symmetricHorizontalEdges
      linear_combination h
    simpa [rectangularRightEdge, rectangularLeftEdge,
      truncatedVerticalIntegral, symmetricLowerCorner,
      symmetricUpperCorner] using hedge'
  have hrightI : Tendsto
      (fun T : ℝ => I * truncatedVerticalIntegral f σR T) atTop
      (nhds (I * rightValue)) := tendsto_const_nhds.mul hright
  have hleftI : Tendsto
      (fun T : ℝ =>
        I * truncatedVerticalIntegral f σL T -
          symmetricHorizontalEdges f σL σR T + 2 * Real.pi * I * r)
      atTop (nhds (I * leftValue - 0 + 2 * Real.pi * I * r)) :=
    ((tendsto_const_nhds.mul hleft).sub hhorizontal).add tendsto_const_nhds
  have hrightI' : Tendsto
      (fun T : ℝ => I * truncatedVerticalIntegral f σR T) atTop
      (nhds (I * leftValue - 0 + 2 * Real.pi * I * r)) :=
    hleftI.congr' (hedge.mono fun _ h => h.symm)
  have heq := tendsto_nhds_unique hrightI hrightI'
  apply (mul_left_cancel₀ I_ne_zero)
  linear_combination heq

/-! ## The weighted Estermann integrand and its pole at zero -/

/-- The Mellin integrand on which the normalized Estermann functional
equation acts.  The possible pole of the continuation at `1` is transported
to `s = 0`. -/
noncomputable def estermannWeightedIntegrand
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ) (s : ℂ) : ℂ :=
  W s * estermannHurwitzContinuation a q (1 - s)

/-- Away from `s = 0`, holomorphy of the weight and the proved Hurwitz
continuation give holomorphy of the weighted Estermann integrand. -/
theorem differentiableAt_estermannWeightedIntegrand
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ) {s : ℂ}
    (hW : DifferentiableAt ℂ W s) (hs : s ≠ 0) :
    DifferentiableAt ℂ (estermannWeightedIntegrand a q W) s := by
  unfold estermannWeightedIntegrand
  apply hW.mul
  apply (differentiableAt_estermannHurwitzContinuation a q ?_).comp s
  · fun_prop
  · intro h
    apply hs
    linear_combination -h

/-- The leading coefficient of the possible double pole of the weighted
integrand at zero. -/
noncomputable def estermannWeightedDoublePoleCoefficient
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ) : ℂ :=
  W 0 * estermannDoublePoleCoefficient a q

/-- Orthogonality of the inner additive character, stated in the form needed
to evaluate the double-pole coefficient. -/
theorem sum_estermannResiduePhase
    (a q : ℕ) [NeZero q] (j : ZMod q) :
    ∑ k : ZMod q, estermannResiduePhase a j k =
      if (a : ZMod q) * j = 0 then (q : ℂ) else 0 := by
  have h := dft_estermannInnerCoefficient a j 0
  rw [ZMod.dft_apply] at h
  simpa [estermannInnerCoefficient, mul_comm, eq_comm] using h

/-- For a reduced numerator, the complete bilinear phase has total mass
`q`; only the zero outer residue survives. -/
theorem sum_sum_estermannResiduePhase_eq_modulus
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    ∑ j : ZMod q, ∑ k : ZMod q, estermannResiduePhase a j k = (q : ℂ) := by
  classical
  simp_rw [sum_estermannResiduePhase]
  have ha : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 hcop
  have hz : ∀ j : ZMod q, (a : ZMod q) * j = 0 ↔ j = 0 := by
    intro j
    rcases ha with ⟨u, hu⟩
    rw [← hu]
    simp
  simp only [hz]
  simp

/-- The possible double pole of a reduced Estermann twist has leading
coefficient `1/q`. -/
theorem estermannDoublePoleCoefficient_eq_inv_modulus
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    estermannDoublePoleCoefficient a q = ((q : ℂ)⁻¹) := by
  unfold estermannDoublePoleCoefficient
  rw [Complex.cpow_neg_one]
  rw [← Finset.mul_sum]
  rw [sum_sum_estermannResiduePhase_eq_modulus a q hcop]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  field_simp

/-! ### The simple Laurent coefficient -/

/-- The holomorphic part of one Hurwitz zeta factor at `s = 1`, using
Mathlib's gamma-normalized principal part. -/
noncomputable def hurwitzRegularPart
    (x : UnitAddCircle) (s : ℂ) : ℂ :=
  HurwitzZeta.hurwitzZeta x s -
    1 / (s - 1) / Complex.Gammaℝ s

/-- A globally defined replacement for `(s-1) · ζ(s,x)` at the pole. -/
noncomputable def hurwitzPoleRemovedFactor
    (x : UnitAddCircle) (s : ℂ) : ℂ :=
  (Complex.Gammaℝ s)⁻¹ + (s - 1) * hurwitzRegularPart x s

/-- The removed Hurwitz factor is differentiable at the formerly singular
point. -/
theorem differentiableAt_hurwitzPoleRemovedFactor
    (x : UnitAddCircle) :
    DifferentiableAt ℂ (hurwitzPoleRemovedFactor x) 1 := by
  unfold hurwitzPoleRemovedFactor hurwitzRegularPart
  exact Complex.differentiable_Gammaℝ_inv.differentiableAt.add
    ((differentiableAt_id.sub_const 1).mul
      (HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div x))

/-- Off the pole, the removed factor agrees with the original Hurwitz zeta
factor multiplied by `s-1`. -/
theorem hurwitzPoleRemovedFactor_eq_mul_hurwitzZeta
    (x : UnitAddCircle) {s : ℂ} (hs : s ≠ 1) :
    hurwitzPoleRemovedFactor x s =
      (s - 1) * HurwitzZeta.hurwitzZeta x s := by
  unfold hurwitzPoleRemovedFactor hurwitzRegularPart
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hcancel :
      (s - 1) * (1 / (s - 1) / Complex.Gammaℝ s) =
        1 / Complex.Gammaℝ s := by
    calc
      (s - 1) * (1 / (s - 1) / Complex.Gammaℝ s) =
          ((s - 1) * (s - 1)⁻¹) / Complex.Gammaℝ s := by
            simp only [one_div]
            ring
      _ = 1 / Complex.Gammaℝ s := by rw [mul_inv_cancel₀ hs']
  rw [mul_sub, hcancel]
  ring

/-- A holomorphic numerator for the possible double pole of the Estermann
continuation.  Off `s=1` it is exactly `(s-1)^2 D(s,a/q)`. -/
noncomputable def estermannPoleRemovedNumerator
    (a q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-s) *
    ∑ j : ZMod q,
      ((q : ℂ) ^ (-s) *
          ∑ k : ZMod q,
            estermannResiduePhase a j k *
              hurwitzPoleRemovedFactor (ZMod.toAddCircle k) s) *
        hurwitzPoleRemovedFactor (ZMod.toAddCircle j) s

/-- The pole-removed numerator is differentiable at one. -/
theorem differentiableAt_estermannPoleRemovedNumerator
    (a q : ℕ) [NeZero q] :
    DifferentiableAt ℂ (estermannPoleRemovedNumerator a q) 1 := by
  unfold estermannPoleRemovedNumerator
  have hq : DifferentiableAt ℂ (fun s : ℂ => (q : ℂ) ^ (-s)) 1 := by
    fun_prop
  apply hq.mul
  apply DifferentiableAt.fun_sum
  intro j _
  apply DifferentiableAt.mul
  · apply hq.mul
    apply DifferentiableAt.fun_sum
    intro k _
    exact (differentiableAt_hurwitzPoleRemovedFactor
      (ZMod.toAddCircle k)).const_mul _
  · exact differentiableAt_hurwitzPoleRemovedFactor (ZMod.toAddCircle j)

/-- The value of the holomorphic numerator at one is the leading Laurent
coefficient already obtained from the punctured limit. -/
theorem estermannPoleRemovedNumerator_one
    (a q : ℕ) [NeZero q] :
    estermannPoleRemovedNumerator a q 1 =
      estermannDoublePoleCoefficient a q := by
  unfold estermannPoleRemovedNumerator estermannDoublePoleCoefficient
  simp [hurwitzPoleRemovedFactor, Complex.Gammaℝ_one]

/-- Exact agreement of the holomorphic numerator with the original
Estermann continuation away from its pole. -/
theorem estermannPoleRemovedNumerator_eq
    (a q : ℕ) [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    estermannPoleRemovedNumerator a q s =
      (s - 1) ^ 2 * estermannHurwitzContinuation a q s := by
  unfold estermannPoleRemovedNumerator estermannHurwitzContinuation ZMod.LFunction
  simp_rw [hurwitzPoleRemovedFactor_eq_mul_hurwitzZeta _ hs]
  simp only [Finset.mul_sum, Finset.sum_mul]
  ring

/-- The simple Laurent coefficient of the Estermann continuation at one.
It is a derivative of an explicit finite Hurwitz expression. -/
noncomputable def estermannSimplePoleCoefficient
    (a q : ℕ) [NeZero q] : ℂ :=
  deriv (estermannPoleRemovedNumerator a q) 1

/-- The first-order Laurent quotient tends to the explicit simple-pole
coefficient. -/
theorem estermannHurwitzContinuation_simplePole_limit
    (a q : ℕ) [NeZero q] :
    Tendsto
      (fun s : ℂ =>
        ((s - 1) ^ 2 * estermannHurwitzContinuation a q s -
            estermannDoublePoleCoefficient a q) / (s - 1))
      (nhdsWithin (1 : ℂ) ({1}ᶜ : Set ℂ))
      (nhds (estermannSimplePoleCoefficient a q)) := by
  have hderiv :=
    (differentiableAt_estermannPoleRemovedNumerator a q).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hderiv
  apply hderiv.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := by simpa using hs
  rw [slope_def_field]
  rw [estermannPoleRemovedNumerator_eq a q hs1,
    estermannPoleRemovedNumerator_one]

/-- The existing double-pole limit at `1` transports exactly to `s = 0`.
This is the first pole coefficient needed in a Voronoi shift; it is proved,
not included as a contour hypothesis. -/
theorem estermannWeightedIntegrand_doublePole_limit
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ)
    (hW : ContinuousAt W 0) :
    Tendsto
      (fun s : ℂ => s ^ 2 * estermannWeightedIntegrand a q W s)
      (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (nhds (estermannWeightedDoublePoleCoefficient a q W)) := by
  have hsub : Tendsto (fun s : ℂ => 1 - s)
      (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (nhdsWithin (1 : ℂ) ({1}ᶜ : Set ℂ)) := by
    simpa using
      ((hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).sub
        (hasDerivAt_id (x := (0 : ℂ)))).tendsto_nhdsNE (by norm_num)
  have hD := (estermannHurwitzContinuation_doublePole_limit a q).comp hsub
  have hW' : Tendsto W (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (nhds (W 0)) :=
    hW.tendsto.mono_left inf_le_left
  have heq : (fun s : ℂ =>
      s ^ 2 * estermannWeightedIntegrand a q W s) =
      fun s : ℂ => W s *
        ((1 - s - 1) ^ 2 * estermannHurwitzContinuation a q (1 - s)) := by
    funext s
    unfold estermannWeightedIntegrand
    ring
  rw [heq]
  simpa [estermannWeightedDoublePoleCoefficient] using hW'.mul hD

/-- The residue of the weighted integrand at the crossed point.  It contains
both the derivative of the weight against the double-pole coefficient and
the reflected simple Laurent coefficient. -/
noncomputable def estermannWeightedResidueCoefficient
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ) : ℂ :=
  deriv W 0 * estermannDoublePoleCoefficient a q -
    W 0 * estermannSimplePoleCoefficient a q

/-- The weighted residue is a genuine punctured limit.  This theorem is the
local pole bookkeeping needed for the contour shift; no decay assumption is
used. -/
theorem estermannWeightedIntegrand_residue_limit
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ)
    (hW : DifferentiableAt ℂ W 0) :
    Tendsto
      (fun s : ℂ =>
        s * (estermannWeightedIntegrand a q W s -
          estermannWeightedDoublePoleCoefficient a q W / s ^ 2))
      (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (nhds (estermannWeightedResidueCoefficient a q W)) := by
  have hsub : Tendsto (fun s : ℂ => 1 - s)
      (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (nhdsWithin (1 : ℂ) ({1}ᶜ : Set ℂ)) := by
    simpa using
      ((hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).sub
        (hasDerivAt_id (x := (0 : ℂ)))).tendsto_nhdsNE (by norm_num)
  have hlead : Tendsto
      (fun s : ℂ => s ^ 2 *
        estermannHurwitzContinuation a q (1 - s))
      (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (nhds (estermannDoublePoleCoefficient a q)) := by
    simpa [estermannWeightedIntegrand,
      estermannWeightedDoublePoleCoefficient] using
        (estermannWeightedIntegrand_doublePole_limit a q
          (fun _ : ℂ => (1 : ℂ)) continuousAt_const)
  have hsimple :=
    (estermannHurwitzContinuation_simplePole_limit a q).comp hsub
  have hsimple' : Tendsto
      (fun s : ℂ =>
        (s ^ 2 * estermannHurwitzContinuation a q (1 - s) -
          estermannDoublePoleCoefficient a q) / s)
      (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (nhds (-estermannSimplePoleCoefficient a q)) := by
    apply hsimple.neg.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := by simpa using hs
    simp only [Function.comp_apply]
    field_simp [hs0]
    ring
  have hweight : Tendsto
      (fun s : ℂ => (W s - W 0) / s)
      (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (nhds (deriv W 0)) := by
    apply hW.hasDerivAt.tendsto_slope.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [slope_def_field]
    simp [div_eq_mul_inv, mul_comm]
  have hconst : Tendsto (fun _ : ℂ => W 0)
      (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ)) (nhds (W 0)) :=
    tendsto_const_nhds
  have hlim := (hweight.mul hlead).add (hconst.mul hsimple')
  have hlim' : Tendsto
      (fun s : ℂ =>
        ((W s - W 0) / s) *
            (s ^ 2 * estermannHurwitzContinuation a q (1 - s)) +
          W 0 * ((s ^ 2 * estermannHurwitzContinuation a q (1 - s) -
            estermannDoublePoleCoefficient a q) / s))
      (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (nhds (estermannWeightedResidueCoefficient a q W)) := by
    simpa [estermannWeightedResidueCoefficient] using hlim
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := by simpa using hs
  unfold estermannWeightedIntegrand estermannWeightedDoublePoleCoefficient
  field_simp [hs0]
  ring

/-- For a reduced numerator the weighted residue has the more transparent
leading term `W'(0)/q`. -/
theorem estermannWeightedResidueCoefficient_eq
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) (W : ℂ → ℂ) :
    estermannWeightedResidueCoefficient a q W =
      deriv W 0 * (q : ℂ)⁻¹ - W 0 * estermannSimplePoleCoefficient a q := by
  rw [estermannWeightedResidueCoefficient,
    estermannDoublePoleCoefficient_eq_inv_modulus a q hcop]

/-! ## Pole subtraction and the finite shift -/

/-- A Laurent subtraction package at `s = 0`.  The leading coefficient is
fixed by the theorem above, and the simple-pole coefficient is the canonical
weighted residue just computed.  Only the proof that this two-term
subtraction extends holomorphically remains local analytic work for a chosen
Mellin weight. -/
structure EstermannPoleSubtraction
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ) where
  regularized : ℂ → ℂ
  regularized_differentiable : Differentiable ℂ regularized
  decomposition : ∀ s : ℂ, s ≠ 0 →
    estermannWeightedIntegrand a q W s =
      regularized s + estermannWeightedDoublePoleCoefficient a q W / s ^ 2 +
        estermannWeightedResidueCoefficient a q W / s

/-- The pole-subtracted Estermann integrand obeys an exact rectangular
contour shift for every finite rectangle. -/
theorem EstermannPoleSubtraction.regularized_rectangular_shift
    {a q : ℕ} [NeZero q] {W : ℂ → ℂ}
    (H : EstermannPoleSubtraction a q W) (z w : ℂ) :
    rectangularRightEdge H.regularized z w =
      -rectangularLeftEdge H.regularized z w -
        rectangularLowerEdge H.regularized z w -
          rectangularUpperEdge H.regularized z w := by
  exact rectangularRightEdge_eq_of_differentiableOn H.regularized z w
    H.regularized_differentiable.differentiableOn

/-- A finite-height contour package keeps the three genuinely analytic
requirements distinct: local pole subtraction, the residue contribution to
the original boundary integral, and horizontal-edge control.  The equality
field is not a cancellation estimate. -/
structure EstermannFiniteContourShift
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ) where
  poleSubtraction : EstermannPoleSubtraction a q W
  leftCorner : ℂ
  rightCorner : ℂ
  crosses_zero : leftCorner.re < 0 ∧ 0 < rightCorner.re ∧
    leftCorner.im < 0 ∧ 0 < rightCorner.im
  original_boundary_eq_residue :
    rectangularBoundaryIntegral (estermannWeightedIntegrand a q W)
      leftCorner rightCorner =
        2 * Real.pi * I * estermannWeightedResidueCoefficient a q W

/-- Once the residue theorem has been supplied for the original integrand,
the exact four-edge identity exposes the two horizontal remainders without
hiding them in big-O notation. -/
theorem EstermannFiniteContourShift.rightEdge_eq
    {a q : ℕ} [NeZero q] {W : ℂ → ℂ}
    (H : EstermannFiniteContourShift a q W) :
    rectangularRightEdge (estermannWeightedIntegrand a q W)
        H.leftCorner H.rightCorner =
      -rectangularLeftEdge (estermannWeightedIntegrand a q W)
          H.leftCorner H.rightCorner -
        rectangularLowerEdge (estermannWeightedIntegrand a q W)
          H.leftCorner H.rightCorner -
        rectangularUpperEdge (estermannWeightedIntegrand a q W)
          H.leftCorner H.rightCorner +
        2 * Real.pi * I * estermannWeightedResidueCoefficient a q W := by
  have h := H.original_boundary_eq_residue
  unfold rectangularBoundaryIntegral at h
  linear_combination h

/-! ## The exact infinite-height Estermann interface -/

/-- Data sufficient to pass the finite Estermann rectangle to two complete
vertical lines.  The three analytic obligations are deliberately separate:
the residue theorem, convergence of the vertical truncations, and vanishing
of the coupled horizontal pair. -/
structure EstermannInfiniteContourShift
    (a q : ℕ) [NeZero q] (W : ℂ → ℂ) (σL σR : ℝ) where
  poleSubtraction : EstermannPoleSubtraction a q W
  left_of_zero : σL < 0
  right_of_zero : 0 < σR
  boundary_eq_residue : ∀ T : ℝ, 0 < T →
    rectangularBoundaryIntegral (estermannWeightedIntegrand a q W)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        2 * Real.pi * I * estermannWeightedResidueCoefficient a q W
  left_vertical_converges :
    Tendsto (truncatedVerticalIntegral
      (estermannWeightedIntegrand a q W) σL) atTop
      (nhds (estermannPrimalVerticalIntegral a q σL W))
  right_vertical_converges :
    Tendsto (truncatedVerticalIntegral
      (estermannWeightedIntegrand a q W) σR) atTop
      (nhds (estermannPrimalVerticalIntegral a q σR W))
  horizontal_pair_vanishes :
    Tendsto (symmetricHorizontalEdges
      (estermannWeightedIntegrand a q W) σL σR) atTop (nhds 0)

/-- The complete vertical-line contour shift with its canonical weighted
residue. -/
theorem EstermannInfiniteContourShift.primalVerticalIntegral_eq
    {a q : ℕ} [NeZero q] {W : ℂ → ℂ} {σL σR : ℝ}
    (H : EstermannInfiniteContourShift a q W σL σR) :
    estermannPrimalVerticalIntegral a q σR W =
      estermannPrimalVerticalIntegral a q σL W +
        2 * Real.pi * estermannWeightedResidueCoefficient a q W := by
  exact verticalLimit_eq_of_rectangularBoundary
    (estermannWeightedIntegrand a q W) σL σR
    (estermannWeightedResidueCoefficient a q W)
    (estermannPrimalVerticalIntegral a q σL W)
    (estermannPrimalVerticalIntegral a q σR W)
    H.boundary_eq_residue H.left_vertical_converges
      H.right_vertical_converges H.horizontal_pair_vanishes

/-- Combining the proved normalized functional equation on the right line
with the contour shift produces the rigorous pre-Voronoi identity. -/
theorem EstermannInfiniteContourShift.dualVerticalIntegral_eq
    {a q : ℕ} [NeZero q] {W : ℂ → ℂ} {σL σR : ℝ}
    (H : EstermannInfiniteContourShift a q W σL σR)
    (hcop : Nat.Coprime a q) (hσR1 : σR ≠ 1) :
    estermannDualVerticalIntegral a q hcop σR W =
      estermannPrimalVerticalIntegral a q σL W +
        2 * Real.pi * estermannWeightedResidueCoefficient a q W := by
  rw [← estermannPrimalVerticalIntegral_eq_dual
    a q hcop σR H.right_of_zero hσR1 W]
  exact H.primalVerticalIntegral_eq

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
