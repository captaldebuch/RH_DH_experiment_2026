/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSReflectedContour
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# NB12p: the active triple-pole Laurent package

The exact reflected active integrand is

`-Gamma(1-s) * delta^s / s * D(1-s,a/q)`.

For a reduced rational twist, `D` has a double pole at one.  The additional
active factor `1/s` therefore raises the pole at `s=0` to order three.  This
file combines the existing entire Estermann finite part with a second-order
Taylor expansion of the reflected Gamma--Abel weight.  It obtains an exact
triple-pole subtraction and an analytic local remainder.

The coefficient of `1/s` deliberately retains the value of the entire
Estermann finite part at one.  Identifying that value with the retained H15
correction is the next arithmetic theorem; it is not assumed here.
-/

open scoped BigOperators Topology LSeries.notation
open Complex Filter Set Topology

namespace NBMellinTools.NB12

/-- The active reflected Gamma--Abel weight after the exact `delta/s`
normalization has been reattached. -/
noncomputable def bblsActiveReflectedWeight
    (damping : ℝ) (s : ℂ) : ℂ :=
  -(Complex.Gamma (1 - s) * (damping : ℂ) ^ s)

/-- The second Taylor coefficient of the active reflected weight at zero. -/
noncomputable def bblsActiveReflectedWeightSecondCoefficient
    (damping : ℝ) : ℂ :=
  iteratedDeriv 2 (bblsActiveReflectedWeight damping) 0 /
    (Nat.factorial 2 : ℂ)

/-- The active expression written directly in the reflected coordinate. -/
noncomputable def bblsActiveReflectedExpression
    (damping : ℝ) (a q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  bblsActiveReflectedWeight damping s / s *
    bblsEstermannHurwitzContinuation a q (1 - s)

/-- The direct active expression is exactly the previously normalized
reflected integrand with its essential factor `delta/s`. -/
theorem bblsActiveReflectedExpression_eq_normalized
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] {s : ℂ} (hs : s ≠ 0) :
    bblsActiveReflectedExpression damping a q s =
      (damping : ℂ) / s *
        bblsNormalizedReflectedAbelIntegrand damping a q s := by
  have hd0 : (damping : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdamping.ne'
  have hpow : (damping : ℂ) ^ s =
      (damping : ℂ) * (damping : ℂ) ^ (s - 1) := by
    calc
      (damping : ℂ) ^ s =
          (damping : ℂ) ^ ((s - 1) + 1) := by ring_nf
      _ = (damping : ℂ) ^ (s - 1) *
          (damping : ℂ) ^ (1 : ℂ) := by
            rw [Complex.cpow_add _ _ hd0]
      _ = (damping : ℂ) *
          (damping : ℂ) ^ (s - 1) := by
            rw [Complex.cpow_one]
            ring
  unfold bblsActiveReflectedExpression bblsActiveReflectedWeight
    bblsNormalizedReflectedAbelIntegrand
    bblsNormalizedReflectedAbelWeight
  rw [hpow]
  field_simp [hs]

/-- The normalization identity also holds at zero because both sides use
Lean's totalized division.  This all-point form is convenient for transport
of punctured limits. -/
theorem bblsActiveReflectedExpression_eq_normalized_all
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (s : ℂ) :
    bblsActiveReflectedExpression damping a q s =
      (damping : ℂ) / s *
        bblsNormalizedReflectedAbelIntegrand damping a q s := by
  by_cases hs : s = 0
  · subst s
    simp [bblsActiveReflectedExpression]
  · exact bblsActiveReflectedExpression_eq_normalized
      hdamping a q hs

/-- The direct active expression has the additional simple residue
`delta * D(0,a/q)` at `s=1`. -/
theorem tendsto_bblsActiveReflectedExpression_residue_one
    (damping : ℝ) (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] :
    Tendsto
      (fun s : ℂ =>
        (s - 1) * bblsActiveReflectedExpression damping a q s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 ((damping : ℂ) *
        bblsEstermannHurwitzContinuation a q 0)) := by
  have hres := tendsto_bblsActiveReflectedIntegrand_residue_one
    damping hdamping a q
  apply hres.congr'
  filter_upwards with s
  rw [bblsActiveReflectedExpression_eq_normalized_all
    hdamping a q s]

/-! ## Local Taylor data for the active weight -/

/-- Gamma is analytic at one, proved from differentiability on the open
right half-plane. -/
theorem analyticAt_Gamma_one_bbls :
    AnalyticAt ℂ Complex.Gamma 1 := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hUmem : (1 : ℂ) ∈ U := by simp [U]
  have hdiff : DifferentiableOn ℂ Complex.Gamma U := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have hre := congrArg Complex.re hm
    have hmnonpos : (-((m : ℂ))).re ≤ 0 := by simp
    rw [← hre] at hmnonpos
    exact (not_lt_of_ge hmnonpos) hz
  exact hdiff.analyticAt (hUopen.mem_nhds hUmem)

/-- The active reflected weight is analytic at zero. -/
theorem analyticAt_bblsActiveReflectedWeight
    (damping : ℝ) (hdamping : 0 < damping) :
    AnalyticAt ℂ (bblsActiveReflectedWeight damping) 0 := by
  have hd0 : (damping : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdamping.ne'
  have hinner : AnalyticAt ℂ (fun s : ℂ => 1 - s) 0 := by
    fun_prop
  have hgamma : AnalyticAt ℂ
      (fun s : ℂ => Complex.Gamma (1 - s)) 0 := by
    exact analyticAt_Gamma_one_bbls.comp_of_eq'
      hinner (by norm_num)
  have hpow : AnalyticAt ℂ (fun s : ℂ => (damping : ℂ) ^ s) 0 :=
    (differentiable_id.const_cpow (Or.inl hd0)).analyticAt 0
  change AnalyticAt ℂ
    (fun s : ℂ => -(Complex.Gamma (1 - s) * (damping : ℂ) ^ s)) 0
  exact (hgamma.mul hpow).neg

/-- Value of the active weight at zero. -/
@[simp] theorem bblsActiveReflectedWeight_zero (damping : ℝ) :
    bblsActiveReflectedWeight damping 0 = -1 := by
  simp [bblsActiveReflectedWeight]

/-- First derivative of the active weight at zero. -/
theorem hasDerivAt_bblsActiveReflectedWeight_zero
    (damping : ℝ) (hdamping : 0 < damping) :
    HasDerivAt (bblsActiveReflectedWeight damping)
      (-((Real.eulerMascheroniConstant : ℂ) +
        Complex.log (damping : ℂ))) 0 := by
  have hd0 : (damping : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdamping.ne'
  have hgammaOne : HasDerivAt Complex.Gamma
      (-(Real.eulerMascheroniConstant : ℂ)) (1 : ℂ) :=
    Complex.hasDerivAt_Gamma_one
  have hgammaAt : HasDerivAt Complex.Gamma
      (-(Real.eulerMascheroniConstant : ℂ)) ((1 : ℂ) - 0) := by
    simpa using hgammaOne
  have hgamma := hgammaAt.comp_const_sub (1 : ℂ) 0
  have hpow := (hasDerivAt_id (x := (0 : ℂ))).const_cpow
    (c := (damping : ℂ)) (Or.inl hd0)
  convert (hgamma.mul hpow).neg using 1
  · simp

/-- A global exact second-order Taylor decomposition of the active weight,
with a remainder analytic at zero. -/
theorem exists_bblsActiveReflectedWeightTaylorRemainder
    (damping : ℝ) (hdamping : 0 < damping) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ ∀ s : ℂ,
      bblsActiveReflectedWeight damping s =
        -1 + s *
          (-((Real.eulerMascheroniConstant : ℂ) +
            Complex.log (damping : ℂ))) +
          s ^ 2 * bblsActiveReflectedWeightSecondCoefficient damping +
          s ^ 3 * H s := by
  have hA := analyticAt_bblsActiveReflectedWeight damping hdamping
  rcases hA.exists_eq_sum_add_pow_mul 3 with ⟨H, hH, hEq⟩
  refine ⟨H, hH, ?_⟩
  intro s
  have hderiv : deriv (bblsActiveReflectedWeight damping) 0 =
      -((Real.eulerMascheroniConstant : ℂ) +
        Complex.log (damping : ℂ)) :=
    (hasDerivAt_bblsActiveReflectedWeight_zero damping hdamping).deriv
  have he := hEq s
  simp only [Finset.sum_range_succ, iteratedDeriv_zero,
    iteratedDeriv_one, hderiv] at he
  unfold bblsActiveReflectedWeightSecondCoefficient
  convert he using 1
  all_goals norm_num
  ring

/-! ## Exact triple-pole package -/

/-- Complete local data for the active triple pole at zero.  The remainder
is analytic at zero and the displayed identity is exact on the punctured
plane away from the inherited Estermann pole. -/
structure BBLSActiveTriplePolePackage
    (damping : ℝ) (a q : ℕ) [NeZero q] where
  finitePart : ℂ → ℂ
  weightRemainder : ℂ → ℂ
  reflectedFiniteRemainder : ℂ → ℂ
  remainder : ℂ → ℂ
  finitePart_differentiable : Differentiable ℂ finitePart
  weightRemainder_analyticAt : AnalyticAt ℂ weightRemainder 0
  reflectedFiniteRemainder_analyticAt :
    AnalyticAt ℂ reflectedFiniteRemainder 0
  remainder_analyticAt : AnalyticAt ℂ remainder 0
  finitePart_identity : ∀ {z : ℂ}, z ≠ 1 →
    bblsEstermannHurwitzContinuation a q z =
      (q : ℂ)⁻¹ / (z - 1) ^ 2 +
        (2 * ((Real.eulerMascheroniConstant : ℂ) -
          Complex.log (q : ℂ)) / (q : ℂ)) / (z - 1) +
        finitePart z
  active_identity : ∀ {s : ℂ}, s ≠ 0 →
    bblsActiveReflectedExpression damping a q s =
      (-(q : ℂ)⁻¹) / s ^ 3 +
      ((q : ℂ)⁻¹ *
          (-((Real.eulerMascheroniConstant : ℂ) +
            Complex.log (damping : ℂ))) +
        2 * ((Real.eulerMascheroniConstant : ℂ) -
          Complex.log (q : ℂ)) / (q : ℂ)) / s ^ 2 +
      ((q : ℂ)⁻¹ *
          bblsActiveReflectedWeightSecondCoefficient damping -
        (2 * ((Real.eulerMascheroniConstant : ℂ) -
          Complex.log (q : ℂ)) / (q : ℂ)) *
            (-((Real.eulerMascheroniConstant : ℂ) +
              Complex.log (damping : ℂ))) -
        finitePart 1) / s +
      remainder s

/-- The active triple-pole package exists unconditionally for every reduced
rational twist and every positive Abel damping parameter. -/
theorem exists_bblsActiveTriplePolePackage
    (damping : ℝ) (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) :
    Nonempty (BBLSActiveTriplePolePackage damping a q) := by
  rcases exists_bblsEstermannDifferentiableFinitePart a q haq with
    ⟨F, hF, hFidentity⟩
  rcases exists_bblsActiveReflectedWeightTaylorRemainder damping hdamping with
    ⟨HW, hHW, hWidentity⟩
  have hinner : AnalyticAt ℂ (fun s : ℂ => 1 - s) 0 := by
    fun_prop
  have hM : AnalyticAt ℂ (fun s : ℂ => F (1 - s)) 0 := by
    exact (hF.analyticAt 1).comp_of_eq' hinner (by norm_num)
  rcases hM.exists_eq_sum_add_pow_mul 1 with ⟨J, hJ, hJidentity⟩
  let A0 : ℂ := (q : ℂ)⁻¹
  let A1 : ℂ := 2 * ((Real.eulerMascheroniConstant : ℂ) -
    Complex.log (q : ℂ)) / (q : ℂ)
  let w1 : ℂ := -((Real.eulerMascheroniConstant : ℂ) +
    Complex.log (damping : ℂ))
  let w2 : ℂ := bblsActiveReflectedWeightSecondCoefficient damping
  let R : ℂ → ℂ := fun s =>
    A0 * HW s - A1 * w2 - A1 * s * HW s +
      w1 * F 1 + w2 * s * F 1 + s ^ 2 * HW s * F 1 +
      bblsActiveReflectedWeight damping s * J s
  have hR : AnalyticAt ℂ R 0 := by
    dsimp [R]
    have hWeight := analyticAt_bblsActiveReflectedWeight damping hdamping
    exact ((((((analyticAt_const.mul hHW).sub analyticAt_const).sub
      ((analyticAt_const.mul analyticAt_id).mul hHW)).add
      analyticAt_const).add
      ((analyticAt_const.mul analyticAt_id).mul analyticAt_const)).add
      (((analyticAt_id.pow 2).mul hHW).mul analyticAt_const)).add
      (hWeight.mul hJ)
  refine ⟨{
    finitePart := F
    weightRemainder := HW
    reflectedFiniteRemainder := J
    remainder := R
    finitePart_differentiable := hF
    weightRemainder_analyticAt := hHW
    reflectedFiniteRemainder_analyticAt := hJ
    remainder_analyticAt := hR
    finitePart_identity := hFidentity
    active_identity := ?_ }⟩
  intro s hs
  have hD := hFidentity (s := 1 - s) (by
    intro h
    exact hs (sub_eq_self.mp h))
  have hW := hWidentity s
  have hJvalue := hJidentity s
  have hJvalue' : F (1 - s) = F 1 + s * J s := by
    simpa [Finset.sum_range_succ, iteratedDeriv_zero] using hJvalue
  unfold bblsActiveReflectedExpression
  rw [hD, hW, hJvalue']
  dsimp [A0, A1, w1, w2, R]
  rw [hW]
  field_simp [hs]
  ring

/-- The complete local pole inventory for the active reflected contour:
an exact triple-pole package at zero together with the simple residue at
one. -/
theorem bblsActiveTriplePlusSimplePoleData
    (damping : ℝ) (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) :
    Nonempty (BBLSActiveTriplePolePackage damping a q) ∧
      Tendsto
        (fun s : ℂ =>
          (s - 1) * bblsActiveReflectedExpression damping a q s)
        (𝓝[≠] (1 : ℂ))
        (𝓝 ((damping : ℂ) *
          bblsEstermannHurwitzContinuation a q 0)) :=
  ⟨exists_bblsActiveTriplePolePackage damping hdamping a q haq,
    tendsto_bblsActiveReflectedExpression_residue_one
      damping hdamping a q⟩

end NBMellinTools.NB12
