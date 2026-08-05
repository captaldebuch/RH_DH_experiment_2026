/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSPoleSubtractedRectangle
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# NB12s: constructive removal of the active pole at `s = 1`

The active reflected Estermann expression has residue

`delta * D(0,a/q)`

at `s = 1`.  This file upgrades the previously proved punctured limit to an
actual analytic extension.  The key numerator is

`Gamma (2-s) * delta^s / s * D(1-s,a/q)`.

Away from `s = 1` it is `(s-1)` times the active expression, and its value at
one is the residue.  Mathlib's analytic divided slope therefore removes the
pole without making an arbitrary choice at the singular point.
-/

open scoped BigOperators Topology LSeries.notation
open Complex Filter MeasureTheory Set Topology

namespace NBMellinTools.NB12

/-- The analytic numerator whose divided difference removes the active pole
at `s = 1`. -/
noncomputable def bblsActiveOnePoleNumerator
    (damping : ℝ) (a q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  Complex.Gamma (2 - s) * (damping : ℂ) ^ s / s *
    bblsEstermannHurwitzContinuation a q (1 - s)

/-- The numerator evaluates at one to the exact active residue. -/
@[simp] theorem bblsActiveOnePoleNumerator_one
    (damping : ℝ) (a q : ℕ) [NeZero q] :
    bblsActiveOnePoleNumerator damping a q 1 =
      (damping : ℂ) * bblsEstermannHurwitzContinuation a q 0 := by
  unfold bblsActiveOnePoleNumerator
  rw [show (2 : ℂ) - 1 = 1 by norm_num, Complex.Gamma_one,
    Complex.cpow_one]
  ring

/-- Off the two original singular points, the numerator is exactly
`(s-1)` times the active reflected expression. -/
theorem bblsActiveOnePoleNumerator_eq_mul_active
    (damping : ℝ) (a q : ℕ) [NeZero q]
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    bblsActiveOnePoleNumerator damping a q s =
      (s - 1) * bblsActiveReflectedExpression damping a q s := by
  have hgamma : Complex.Gamma (2 - s) =
      (1 - s) * Complex.Gamma (1 - s) := by
    convert Complex.Gamma_add_one (1 - s) (sub_ne_zero.mpr hs1.symm) using 1 <;>
      ring
  unfold bblsActiveOnePoleNumerator bblsActiveReflectedExpression
    bblsActiveReflectedWeight
  rw [hgamma]
  field_simp [hs0]
  ring

/-- The numerator is analytic at the point at which the active expression
has its additional simple pole. -/
theorem analyticAt_bblsActiveOnePoleNumerator
    (damping : ℝ) (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] :
    AnalyticAt ℂ (bblsActiveOnePoleNumerator damping a q) 1 := by
  have hd0 : (damping : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdamping.ne'
  have hgammaInner : AnalyticAt ℂ (fun s : ℂ => 2 - s) 1 := by
    fun_prop
  have hgamma : AnalyticAt ℂ
      (fun s : ℂ => Complex.Gamma (2 - s)) 1 := by
    exact analyticAt_Gamma_one_bbls.comp_of_eq'
      hgammaInner (by norm_num)
  have hpow : AnalyticAt ℂ (fun s : ℂ => (damping : ℂ) ^ s) 1 :=
    (differentiable_id.const_cpow (Or.inl hd0)).analyticAt 1
  have hdiv : AnalyticAt ℂ
      (fun s : ℂ => Complex.Gamma (2 - s) * (damping : ℂ) ^ s / s) 1 := by
    exact (hgamma.mul hpow).div analyticAt_id (by norm_num)
  have hD0 : AnalyticAt ℂ
      (bblsEstermannHurwitzContinuation a q) 0 := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_ne.mem_nhds (by norm_num : (0 : ℂ) ≠ 1)] with z hz
    exact differentiableAt_bblsEstermannHurwitzContinuation a q hz
  have hinner : AnalyticAt ℂ (fun s : ℂ => 1 - s) 1 := by
    fun_prop
  have hreflected : AnalyticAt ℂ
      (fun s : ℂ => bblsEstermannHurwitzContinuation a q (1 - s)) 1 := by
    exact hD0.comp_of_eq' hinner (by norm_num)
  exact hdiv.mul hreflected

/-- The canonical analytic extension of the active expression after its
`s=1` residue has been removed. -/
noncomputable def bblsActiveOnePoleRemoved
    (damping : ℝ) (a q : ℕ) [NeZero q] : ℂ → ℂ :=
  dslope (bblsActiveOnePoleNumerator damping a q) 1

/-- Divided slopes preserve analyticity near their base point. -/
theorem analyticAt_dslope_of_analyticAt
    {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    AnalyticAt ℂ (dslope f c) c := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf ⊢
  rcases eventually_nhds_iff.mp hf with ⟨U, hUdiff, hUopen, hcU⟩
  have hUnhds : U ∈ 𝓝 c := hUopen.mem_nhds hcU
  have hfOn : DifferentiableOn ℂ f U := by
    intro z hz
    exact (hUdiff z hz).differentiableWithinAt
  have hdsOn : DifferentiableOn ℂ (dslope f c) U :=
    (Complex.differentiableOn_dslope hUnhds).2 hfOn
  exact eventually_nhds_iff.mpr ⟨U, fun z hz =>
    hdsOn.differentiableAt (hUopen.mem_nhds hz), hUopen, hcU⟩

/-- The pole-removed row is genuinely analytic at `s=1`. -/
theorem analyticAt_bblsActiveOnePoleRemoved
    (damping : ℝ) (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] :
    AnalyticAt ℂ (bblsActiveOnePoleRemoved damping a q) 1 := by
  exact analyticAt_dslope_of_analyticAt
    (analyticAt_bblsActiveOnePoleNumerator damping hdamping a q)

/-- On the punctured domain, the canonical extension is exactly the active
expression with its residue term subtracted. -/
theorem bblsActiveOnePoleRemoved_eq_sub_residue
    (damping : ℝ) (a q : ℕ) [NeZero q]
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    bblsActiveOnePoleRemoved damping a q s =
      bblsActiveReflectedExpression damping a q s -
        ((damping : ℂ) * bblsEstermannHurwitzContinuation a q 0) /
          (s - 1) := by
  rw [bblsActiveOnePoleRemoved, dslope_of_ne _ hs1]
  rw [slope_def_field]
  rw [bblsActiveOnePoleNumerator_eq_mul_active damping a q hs0 hs1]
  rw [bblsActiveOnePoleNumerator_one]
  field_simp [sub_ne_zero.mpr hs1]

/-! ## Finite signed aggregation -/

/-- The canonical `s=1`-regularized finite signed aggregate.  The row
residues are removed before any absolute value is taken. -/
noncomputable def bblsFiniteOnePoleRemoved
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational) (s : ℂ) : ℂ :=
  ∑ i : ι, weight i * bblsActiveOnePoleRemoved damping
    (row i).numerator (row i).denominator s

/-- Finite signed aggregation preserves the rowwise analytic extension at
`s=1`. -/
theorem analyticAt_bblsFiniteOnePoleRemoved
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    AnalyticAt ℂ (bblsFiniteOnePoleRemoved damping weight row) 1 := by
  unfold bblsFiniteOnePoleRemoved
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact analyticAt_const.mul
    (analyticAt_bblsActiveOnePoleRemoved damping hdamping
      (row i).numerator (row i).denominator)

/-- Away from `s=0,1`, the finite analytic extension is exactly the complete
active aggregate minus the complete additional residue. -/
theorem bblsFiniteOnePoleRemoved_eq_sub_residue
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    bblsFiniteOnePoleRemoved damping weight row s =
      bblsFiniteActiveAggregate damping weight row s -
        bblsFiniteAdditionalResidue damping weight row / (s - 1) := by
  unfold bblsFiniteOnePoleRemoved bblsFiniteActiveAggregate
    bblsFiniteAdditionalResidue bblsFiniteAdditionalResidueAmplitude
  simp_rw [bblsActiveOnePoleRemoved_eq_sub_residue damping
    _ _ hs0 hs1, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact finite decomposition at `s=1`: the full signed residue remains
outside the analytic divided-difference term. -/
theorem bblsFiniteActiveAggregate_eq_one_pole_removed
    {ι : Type*} [Fintype ι]
    (damping : ℝ)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    bblsFiniteActiveAggregate damping weight row s =
      bblsFiniteOnePoleRemoved damping weight row s +
        bblsFiniteAdditionalResidue damping weight row / (s - 1) := by
  rw [bblsFiniteOnePoleRemoved_eq_sub_residue damping weight row hs0 hs1]
  ring

/-! ## Simultaneous removal at `s=0` and `s=1` -/

/-- The raw expression obtained by removing the three zero-pole terms from
the already `s=1`-regularized finite aggregate. -/
noncomputable def bblsFiniteAllPoleRemovedRaw
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) (s : ℂ) : ℂ :=
  bblsFiniteOnePoleRemoved damping weight row s -
    bblsFiniteThirdOrderAggregate weight row / s ^ 3 -
    bblsFiniteSecondOrderAggregate damping weight row / s ^ 2 -
    bblsFiniteFirstOrderAggregate damping hdamping weight row / s

/-- Near zero, the fully regularized expression is the selected analytic
Laurent remainder minus the analytic `s=1` residue term. -/
noncomputable def bblsFiniteZeroComparison
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) (s : ℂ) : ℂ :=
  bblsFiniteLocalRemainder damping hdamping weight row s -
    bblsFiniteAdditionalResidue damping weight row / (s - 1)

/-- Away from zero and one, the two descriptions of the fully regularized
finite aggregate agree exactly. -/
theorem bblsFiniteAllPoleRemovedRaw_eq_zeroComparison
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    bblsFiniteAllPoleRemovedRaw damping hdamping weight row s =
      bblsFiniteZeroComparison damping hdamping weight row s := by
  unfold bblsFiniteAllPoleRemovedRaw bblsFiniteZeroComparison
  rw [bblsFiniteOnePoleRemoved_eq_sub_residue damping weight row hs0 hs1]
  rw [bblsFiniteActiveAggregate_eq_collectedLaurent
    damping hdamping weight row hs0]
  ring

/-- The complete finite pole-removed function.  Updating the raw expression
at zero by its analytic Laurent value removes the last artificial value left
by totalized division. -/
noncomputable def bblsFiniteAllPoleRemoved
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) : ℂ → ℂ :=
  Function.update
    (bblsFiniteAllPoleRemovedRaw damping hdamping weight row)
    0 (bblsFiniteZeroComparison damping hdamping weight row 0)

/-- The zero-comparison expression is analytic at zero. -/
theorem analyticAt_bblsFiniteZeroComparison
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    AnalyticAt ℂ
      (bblsFiniteZeroComparison damping hdamping weight row) 0 := by
  unfold bblsFiniteZeroComparison
  have hpole : AnalyticAt ℂ (fun s : ℂ =>
      bblsFiniteAdditionalResidue damping weight row / (s - 1)) 0 := by
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (by norm_num)
  exact (analyticAt_bblsFiniteLocalRemainder
    damping hdamping weight row).sub hpole

/-- The complete finite pole-removed function is analytic at zero. -/
theorem analyticAt_bblsFiniteAllPoleRemoved_zero
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    AnalyticAt ℂ
      (bblsFiniteAllPoleRemoved damping hdamping weight row) 0 := by
  have heq : bblsFiniteAllPoleRemoved damping hdamping weight row =ᶠ[𝓝 0]
      bblsFiniteZeroComparison damping hdamping weight row := by
    filter_upwards [isOpen_ne.mem_nhds (by norm_num : (0 : ℂ) ≠ 1)] with s hs1
    by_cases hs0 : s = 0
    · subst s
      simp [bblsFiniteAllPoleRemoved]
    · rw [bblsFiniteAllPoleRemoved, Function.update_of_ne hs0]
      exact bblsFiniteAllPoleRemovedRaw_eq_zeroComparison
        damping hdamping weight row hs0 hs1
  exact (analyticAt_bblsFiniteZeroComparison
    damping hdamping weight row).congr heq.symm

/-- The raw all-pole-removed expression is analytic at one: the divided
difference handles the active pole and the three zero-pole terms are regular
there. -/
theorem analyticAt_bblsFiniteAllPoleRemovedRaw_one
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    AnalyticAt ℂ
      (bblsFiniteAllPoleRemovedRaw damping hdamping weight row) 1 := by
  unfold bblsFiniteAllPoleRemovedRaw
  have h3 : AnalyticAt ℂ (fun s : ℂ =>
      bblsFiniteThirdOrderAggregate weight row / s ^ 3) 1 :=
    analyticAt_const.div (analyticAt_id.pow 3) (by norm_num)
  have h2 : AnalyticAt ℂ (fun s : ℂ =>
      bblsFiniteSecondOrderAggregate damping weight row / s ^ 2) 1 :=
    analyticAt_const.div (analyticAt_id.pow 2) (by norm_num)
  have h1 : AnalyticAt ℂ (fun s : ℂ =>
      bblsFiniteFirstOrderAggregate damping hdamping weight row / s) 1 :=
    analyticAt_const.div analyticAt_id (by norm_num)
  exact (((analyticAt_bblsFiniteOnePoleRemoved
    damping hdamping weight row).sub h3).sub h2).sub h1

/-- The update at zero does not disturb analyticity at one. -/
theorem analyticAt_bblsFiniteAllPoleRemoved_one
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    AnalyticAt ℂ
      (bblsFiniteAllPoleRemoved damping hdamping weight row) 1 := by
  have heq : bblsFiniteAllPoleRemovedRaw damping hdamping weight row =ᶠ[𝓝 1]
      bblsFiniteAllPoleRemoved damping hdamping weight row := by
    filter_upwards [isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0)] with s hs0
    simp [bblsFiniteAllPoleRemoved, hs0]
  exact (analyticAt_bblsFiniteAllPoleRemovedRaw_one
    damping hdamping weight row).congr heq

/-- Exact four-pole decomposition of the actual finite active aggregate.
This is the constructive correction-preserving replacement for a mere list
of punctured residue limits. -/
theorem bblsFiniteActiveAggregate_eq_all_poles_removed
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    bblsFiniteActiveAggregate damping weight row s =
      bblsFiniteAllPoleRemoved damping hdamping weight row s +
        bblsFiniteThirdOrderAggregate weight row / s ^ 3 +
        bblsFiniteSecondOrderAggregate damping weight row / s ^ 2 +
        bblsFiniteFirstOrderAggregate damping hdamping weight row / s +
        bblsFiniteAdditionalResidue damping weight row / (s - 1) := by
  rw [bblsFiniteAllPoleRemoved, Function.update_of_ne hs0]
  unfold bblsFiniteAllPoleRemovedRaw
  rw [bblsFiniteActiveAggregate_eq_one_pole_removed
    damping weight row hs0 hs1]
  ring

/-! ## Holomorphy on the contour strip -/

/-- Gamma is analytic throughout the open right half-plane. -/
theorem analyticAt_Gamma_of_pos_re_bbls
    {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Complex.Gamma z := by
  let U : Set ℂ := {w | 0 < w.re}
  have hUopen : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have hzU : z ∈ U := hz
  have hdiff : DifferentiableOn ℂ Complex.Gamma U := by
    intro w hw
    apply (Complex.differentiableAt_Gamma w ?_).differentiableWithinAt
    intro n hn
    have hre := congrArg Complex.re hn
    have hnnonpos : (-((n : ℂ))).re ≤ 0 := by simp
    rw [← hre] at hnnonpos
    exact (not_lt_of_ge hnnonpos) hw
  exact hdiff.analyticAt (hUopen.mem_nhds hzU)

/-- Away from zero and before the next Gamma pole at real part two, the
active one-pole numerator is analytic. -/
theorem analyticAt_bblsActiveOnePoleNumerator_of_re_lt_two
    (damping : ℝ) (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] {s : ℂ}
    (hre : s.re < 2) (hs0 : s ≠ 0) :
    AnalyticAt ℂ (bblsActiveOnePoleNumerator damping a q) s := by
  have hd0 : (damping : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdamping.ne'
  have hgammaInner : AnalyticAt ℂ (fun z : ℂ => 2 - z) s := by
    fun_prop
  have hgamma : AnalyticAt ℂ
      (fun z : ℂ => Complex.Gamma (2 - z)) s := by
    apply (analyticAt_Gamma_of_pos_re_bbls
      (z := (2 : ℂ) - s) ?_).comp_of_eq' hgammaInner rfl
    simpa using sub_pos.mpr hre
  have hpow : AnalyticAt ℂ (fun z : ℂ => (damping : ℂ) ^ z) s :=
    (differentiable_id.const_cpow (Or.inl hd0)).analyticAt s
  have hdiv : AnalyticAt ℂ
      (fun z : ℂ => Complex.Gamma (2 - z) * (damping : ℂ) ^ z / z) s :=
    (hgamma.mul hpow).div analyticAt_id hs0
  have hD : AnalyticAt ℂ
      (bblsEstermannHurwitzContinuation a q) (1 - s) := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have hne : (1 : ℂ) - s ≠ 1 := by
      intro h
      apply hs0
      linear_combination -h
    filter_upwards [isOpen_ne.mem_nhds hne] with z hz
    exact differentiableAt_bblsEstermannHurwitzContinuation a q hz
  have hinner : AnalyticAt ℂ (fun z : ℂ => 1 - z) s := by
    fun_prop
  have hreflected : AnalyticAt ℂ
      (fun z : ℂ => bblsEstermannHurwitzContinuation a q (1 - z)) s :=
    hD.comp_of_eq' hinner rfl
  exact hdiv.mul hreflected

/-- Away from the divided-slope base point, analyticity of a function is
inherited by its divided slope. -/
theorem analyticAt_dslope_of_analyticAt_of_ne
    {f : ℂ → ℂ} {a b : ℂ} (hf : AnalyticAt ℂ f b) (hba : b ≠ a) :
    AnalyticAt ℂ (dslope f a) b := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [hf.eventually_analyticAt, isOpen_ne.mem_nhds hba] with z hz hza
  exact (differentiableAt_dslope_of_ne hza).2 hz.differentiableAt

/-- The rowwise `s=1` extension is analytic at every nonzero point of the
half-plane `Re(s)<2`. -/
theorem analyticAt_bblsActiveOnePoleRemoved_of_re_lt_two
    (damping : ℝ) (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] {s : ℂ}
    (hre : s.re < 2) (hs0 : s ≠ 0) :
    AnalyticAt ℂ (bblsActiveOnePoleRemoved damping a q) s := by
  by_cases hs1 : s = 1
  · subst s
    exact analyticAt_bblsActiveOnePoleRemoved damping hdamping a q
  · exact analyticAt_dslope_of_analyticAt_of_ne
      (analyticAt_bblsActiveOnePoleNumerator_of_re_lt_two
        damping hdamping a q hre hs0) hs1

/-- The fully pole-removed finite aggregate is analytic throughout the open
half-plane `Re(s)<2`.  Thus a rectangle with right edge below two contains
no remaining singularities. -/
theorem analyticAt_bblsFiniteAllPoleRemoved_of_re_lt_two
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational)
    {s : ℂ} (hre : s.re < 2) :
    AnalyticAt ℂ (bblsFiniteAllPoleRemoved
      damping hdamping weight row) s := by
  by_cases hs0 : s = 0
  · subst s
    exact analyticAt_bblsFiniteAllPoleRemoved_zero
      damping hdamping weight row
  · have hone : AnalyticAt ℂ
        (bblsFiniteOnePoleRemoved damping weight row) s := by
      unfold bblsFiniteOnePoleRemoved
      refine Finset.analyticAt_fun_sum _ fun i _ => ?_
      exact analyticAt_const.mul
        (analyticAt_bblsActiveOnePoleRemoved_of_re_lt_two
          damping hdamping (row i).numerator (row i).denominator hre hs0)
    have h3 : AnalyticAt ℂ (fun z : ℂ =>
        bblsFiniteThirdOrderAggregate weight row / z ^ 3) s :=
      analyticAt_const.div (analyticAt_id.pow 3) (pow_ne_zero 3 hs0)
    have h2 : AnalyticAt ℂ (fun z : ℂ =>
        bblsFiniteSecondOrderAggregate damping weight row / z ^ 2) s :=
      analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hs0)
    have h1 : AnalyticAt ℂ (fun z : ℂ =>
        bblsFiniteFirstOrderAggregate damping hdamping weight row / z) s :=
      analyticAt_const.div analyticAt_id hs0
    have hraw : AnalyticAt ℂ
        (bblsFiniteAllPoleRemovedRaw damping hdamping weight row) s := by
      unfold bblsFiniteAllPoleRemovedRaw
      exact (((hone.sub h3).sub h2).sub h1)
    have heq : bblsFiniteAllPoleRemovedRaw damping hdamping weight row =ᶠ[𝓝 s]
        bblsFiniteAllPoleRemoved damping hdamping weight row := by
      filter_upwards [isOpen_ne.mem_nhds hs0] with z hz
      rw [bblsFiniteAllPoleRemoved, Function.update_of_ne hz]
    exact hraw.congr heq

/-- The fully regularized finite aggregate is differentiable on every closed
rectangle whose right edge lies below the next Gamma pole at `s=2`. -/
theorem differentiableOn_bblsFiniteAllPoleRemoved_rectangle
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational)
    {σL σR T : ℝ} (hσ : σL ≤ σR) (hσR : σR < 2) :
    DifferentiableOn ℂ
      (bblsFiniteAllPoleRemoved damping hdamping weight row)
      (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) := by
  intro s hs
  apply (analyticAt_bblsFiniteAllPoleRemoved_of_re_lt_two
    damping hdamping weight row ?_).differentiableAt.differentiableWithinAt
  rw [mem_reProdIm, uIcc_of_le hσ] at hs
  exact lt_of_le_of_lt hs.1.2 hσR

/-! ## Concrete rectangle data -/

/-- Remove only the cubic zero-pole term.  The remaining function has the
double-plus-two-simple pole inventory already consumed by the proved
rectangle theorem. -/
noncomputable def bblsFiniteActiveAggregateWithoutThird
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational) (s : ℂ) : ℂ :=
  bblsFiniteActiveAggregate damping weight row s -
    bblsFiniteThirdOrderAggregate weight row * (s⁻¹) ^ 3

/-- The actual finite H15/BBLS aggregate, after only its boundary-invisible
cubic pole is removed, supplies the existing two-pole rectangle interface.
No meromorphicity field remains hypothetical. -/
noncomputable def bblsFiniteTwoPoleRectangleData
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    TwoPoleRectangleSubtractionData
      (bblsFiniteActiveAggregateWithoutThird damping weight row) where
  regularized := bblsFiniteAllPoleRemoved damping hdamping weight row
  doubleCoefficient := bblsFiniteSecondOrderAggregate damping weight row
  residueAtZero := bblsFiniteFirstOrderAggregate
    damping hdamping weight row
  residueAtOne := bblsFiniteAdditionalResidue damping weight row
  decomposition := by
    intro s hs0 hs1
    unfold bblsFiniteActiveAggregateWithoutThird
    rw [bblsFiniteActiveAggregate_eq_all_poles_removed
      damping hdamping weight row hs0 hs1]
    field_simp [hs0]
    ring

/-- Genuine two-pole rectangle identity for the finite signed aggregate
after removal of the cubic term.  The cubic term has zero closed-rectangle
integral by `rectangularBoundaryIntegral_triplePole`. -/
theorem rectangularBoundaryIntegral_bblsFinite_withoutThird
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational)
    (σL σR T : ℝ) (hL : σL < 0) (hR : 1 < σR)
    (hR2 : σR < 2) (hT : 0 < T) :
    rectangularBoundaryIntegral
        (bblsFiniteActiveAggregateWithoutThird damping weight row)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      2 * Real.pi * I *
        (bblsFiniteFirstOrderAggregate damping hdamping weight row +
          bblsFiniteAdditionalResidue damping weight row) := by
  let H := bblsFiniteTwoPoleRectangleData
    damping hdamping weight row
  have hσ : σL ≤ σR :=
    le_of_lt (lt_trans hL (lt_trans zero_lt_one hR))
  exact H.boundary_eq_of_differentiableOn σL σR T hL hR hT
    (differentiableOn_bblsFiniteAllPoleRemoved_rectangle
      damping hdamping weight row hσ hR2)

/-- The cubic-removed active aggregate is analytic away from the two pole
locations throughout `Re(s)<2`. -/
theorem analyticAt_bblsFiniteActiveAggregateWithoutThird
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational)
    {s : ℂ} (hre : s.re < 2) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ
      (bblsFiniteActiveAggregateWithoutThird damping weight row) s := by
  let H := bblsFiniteTwoPoleRectangleData damping hdamping weight row
  have hreg := analyticAt_bblsFiniteAllPoleRemoved_of_re_lt_two
    damping hdamping weight row hre
  have h2 : AnalyticAt ℂ (fun z : ℂ =>
      bblsFiniteSecondOrderAggregate damping weight row * (z⁻¹) ^ 2) s := by
    exact analyticAt_const.mul ((analyticAt_id.inv hs0).pow 2)
  have h0 : AnalyticAt ℂ (fun z : ℂ =>
      bblsFiniteFirstOrderAggregate damping hdamping weight row * z⁻¹) s := by
    exact analyticAt_const.mul (analyticAt_id.inv hs0)
  have h1 : AnalyticAt ℂ (fun z : ℂ =>
      bblsFiniteAdditionalResidue damping weight row * (z - 1)⁻¹) s := by
    exact analyticAt_const.mul
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs1))
  have hsum := ((hreg.add h2).add h0).add h1
  have heq : (fun z : ℂ =>
      bblsFiniteAllPoleRemoved damping hdamping weight row z +
        bblsFiniteSecondOrderAggregate damping weight row * (z⁻¹) ^ 2 +
        bblsFiniteFirstOrderAggregate damping hdamping weight row * z⁻¹ +
        bblsFiniteAdditionalResidue damping weight row * (z - 1)⁻¹) =ᶠ[𝓝 s]
      bblsFiniteActiveAggregateWithoutThird damping weight row := by
    filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1] with z hz0 hz1
    exact (H.decomposition z hz0 hz1).symm
  exact hsum.congr heq

/-- Boundary-integral linearity under the exact eight interval-integrability
hypotheses used by a symmetric rectangle. -/
theorem rectangularBoundaryIntegral_add_of_intervalIntegrable
    (f g : ℂ → ℂ) (σL σR T : ℝ)
    (hfm : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) - (T : ℂ) * I)) volume σL σR)
    (hgm : IntervalIntegrable
      (fun x : ℝ => g ((x : ℂ) - (T : ℂ) * I)) volume σL σR)
    (hfp : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (T : ℂ) * I)) volume σL σR)
    (hgp : IntervalIntegrable
      (fun x : ℝ => g ((x : ℂ) + (T : ℂ) * I)) volume σL σR)
    (hfl : IntervalIntegrable
      (fun y : ℝ => f ((σL : ℂ) + (y : ℂ) * I)) volume (-T) T)
    (hgl : IntervalIntegrable
      (fun y : ℝ => g ((σL : ℂ) + (y : ℂ) * I)) volume (-T) T)
    (hfr : IntervalIntegrable
      (fun y : ℝ => f ((σR : ℂ) + (y : ℂ) * I)) volume (-T) T)
    (hgr : IntervalIntegrable
      (fun y : ℝ => g ((σR : ℂ) + (y : ℂ) * I)) volume (-T) T) :
    rectangularBoundaryIntegral (fun s => f s + g s)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      rectangularBoundaryIntegral f
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) +
        rectangularBoundaryIntegral g
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) := by
  unfold rectangularBoundaryIntegral rectangularLowerEdge rectangularUpperEdge
    rectangularRightEdge rectangularLeftEdge symmetricLowerCorner
    symmetricUpperCorner
  simp [Complex.mul_re, Complex.mul_im]
  simp only [← sub_eq_add_neg]
  rw [intervalIntegral.integral_add hfm hgm]
  rw [intervalIntegral.integral_add hfp hgp]
  rw [intervalIntegral.integral_add hfr hgr]
  rw [intervalIntegral.integral_add hfl hgl]
  ring

/-- The original finite active aggregate itself satisfies the correction-
preserving rectangle identity.  The cubic term has been reattached here and
vanishes exactly on the closed rectangle. -/
theorem rectangularBoundaryIntegral_bblsFiniteActiveAggregate
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational)
    (σL σR T : ℝ) (hL : σL < 0) (hR : 1 < σR)
    (hR2 : σR < 2) (hT : 0 < T) :
    rectangularBoundaryIntegral
        (bblsFiniteActiveAggregate damping weight row)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      2 * Real.pi * I *
        (bblsFiniteFirstOrderAggregate damping hdamping weight row +
          bblsFiniteAdditionalResidue damping weight row) := by
  let f := bblsFiniteActiveAggregateWithoutThird damping weight row
  let g : ℂ → ℂ := fun s =>
    bblsFiniteThirdOrderAggregate weight row * (s⁻¹) ^ 3
  have hσ : σL ≤ σR :=
    le_of_lt (lt_trans hL (lt_trans zero_lt_one hR))
  have hminus0 : ∀ x : ℝ, (x : ℂ) - (T : ℂ) * I ≠ 0 := by
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have hplus0 : ∀ x : ℝ, (x : ℂ) + (T : ℂ) * I ≠ 0 := by
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have hleft0 : ∀ y : ℝ, (σL : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro y hy
    have hr := congrArg Complex.re hy
    simp at hr
    linarith
  have hright0 : ∀ y : ℝ, (σR : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro y hy
    have hr := congrArg Complex.re hy
    simp at hr
    linarith
  have hminus1 : ∀ x : ℝ, (x : ℂ) - (T : ℂ) * I ≠ 1 := by
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have hplus1 : ∀ x : ℝ, (x : ℂ) + (T : ℂ) * I ≠ 1 := by
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have hleft1 : ∀ y : ℝ, (σL : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro y hy
    have hr := congrArg Complex.re hy
    simp at hr
    linarith
  have hright1 : ∀ y : ℝ, (σR : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro y hy
    have hr := congrArg Complex.re hy
    simp at hr
    linarith
  have hfm : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) - (T : ℂ) * I)) volume σL σR := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hσ] at hx
    change ContinuousWithinAt
      (f ∘ fun y : ℝ => (y : ℂ) - (T : ℂ) * I) (uIcc σL σR) x
    exact (ContinuousAt.comp
      (f := fun y : ℝ => (y : ℂ) - (T : ℂ) * I)
      (analyticAt_bblsFiniteActiveAggregateWithoutThird
        damping hdamping weight row (by simpa using lt_of_le_of_lt hx.2 hR2)
        (hminus0 x) (hminus1 x)).continuousAt
      (by fun_prop)).continuousWithinAt
  have hfp : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (T : ℂ) * I)) volume σL σR := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hσ] at hx
    change ContinuousWithinAt
      (f ∘ fun y : ℝ => (y : ℂ) + (T : ℂ) * I) (uIcc σL σR) x
    exact (ContinuousAt.comp
      (f := fun y : ℝ => (y : ℂ) + (T : ℂ) * I)
      (analyticAt_bblsFiniteActiveAggregateWithoutThird
        damping hdamping weight row (by simpa using lt_of_le_of_lt hx.2 hR2)
        (hplus0 x) (hplus1 x)).continuousAt
      (by fun_prop)).continuousWithinAt
  have hfl : IntervalIntegrable
      (fun y : ℝ => f ((σL : ℂ) + (y : ℂ) * I)) volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    change ContinuousWithinAt
      (f ∘ fun x : ℝ => (σL : ℂ) + (x : ℂ) * I) (uIcc (-T) T) y
    exact (ContinuousAt.comp
      (f := fun x : ℝ => (σL : ℂ) + (x : ℂ) * I)
      (analyticAt_bblsFiniteActiveAggregateWithoutThird
        damping hdamping weight row (by simp; linarith)
        (hleft0 y) (hleft1 y)).continuousAt
      (by fun_prop)).continuousWithinAt
  have hfr : IntervalIntegrable
      (fun y : ℝ => f ((σR : ℂ) + (y : ℂ) * I)) volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    change ContinuousWithinAt
      (f ∘ fun x : ℝ => (σR : ℂ) + (x : ℂ) * I) (uIcc (-T) T) y
    exact (ContinuousAt.comp
      (f := fun x : ℝ => (σR : ℂ) + (x : ℂ) * I)
      (analyticAt_bblsFiniteActiveAggregateWithoutThird
        damping hdamping weight row (by simp; exact hR2)
        (hright0 y) (hright1 y)).continuousAt
      (by fun_prop)).continuousWithinAt
  have hgm : IntervalIntegrable
      (fun x : ℝ => g ((x : ℂ) - (T : ℂ) * I)) volume σL σR := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    exact continuous_const.mul
      (((by fun_prop : Continuous (fun x : ℝ =>
        (x : ℂ) - (T : ℂ) * I)).inv₀ hminus0).pow 3)
  have hgp : IntervalIntegrable
      (fun x : ℝ => g ((x : ℂ) + (T : ℂ) * I)) volume σL σR := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    exact continuous_const.mul
      (((by fun_prop : Continuous (fun x : ℝ =>
        (x : ℂ) + (T : ℂ) * I)).inv₀ hplus0).pow 3)
  have hgl : IntervalIntegrable
      (fun y : ℝ => g ((σL : ℂ) + (y : ℂ) * I)) volume (-T) T := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    exact continuous_const.mul
      (((by fun_prop : Continuous (fun y : ℝ =>
        (σL : ℂ) + (y : ℂ) * I)).inv₀ hleft0).pow 3)
  have hgr : IntervalIntegrable
      (fun y : ℝ => g ((σR : ℂ) + (y : ℂ) * I)) volume (-T) T := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    exact continuous_const.mul
      (((by fun_prop : Continuous (fun y : ℝ =>
        (σR : ℂ) + (y : ℂ) * I)).inv₀ hright0).pow 3)
  have hadd := rectangularBoundaryIntegral_add_of_intervalIntegrable
    f g σL σR T hfm hgm hfp hgp hfl hgl hfr hgr
  have hfun : bblsFiniteActiveAggregate damping weight row =
      fun s => f s + g s := by
    funext s
    dsimp [f, g, bblsFiniteActiveAggregateWithoutThird]
    ring
  rw [hfun, hadd]
  rw [rectangularBoundaryIntegral_const_mul]
  have htriple : rectangularBoundaryIntegral (fun s : ℂ => (s⁻¹) ^ 3)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) = 0 := by
    simpa using rectangularBoundaryIntegral_triplePole 0 σL σR T hL
      (lt_trans zero_lt_one hR) hT
  rw [htriple]
  rw [rectangularBoundaryIntegral_bblsFinite_withoutThird
    damping hdamping weight row σL σR T hL hR hR2 hT]
  ring

end NBMellinTools.NB12
