/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSEstermannVerticalGrowth
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# NB12o: reflected-contour normalization and the additional Abel residue

The active shifted Abel--Mellin integrand is

`delta^(-w) * Gamma(w) * D(1+w,a/q)`.

After the reflection `s = -w`, it is exactly `delta / s` times the
sign-normalized reflected integrand

`-Gamma(1-s) * delta^(s-1) * D(1-s,a/q)`.

Moving the active line from `Re(w)=1/2` to `Re(w)=-3/2` therefore crosses
the additional Gamma pole `w=-1`, equivalently `s=1`.  This file proves
that the corresponding reflected residue is exactly
`delta * D(0,a/q)` and hence vanishes in the Abel limit `delta -> 0+`.

No global rectangle identity or horizontal-edge estimate is asserted here.
-/

open scoped BigOperators Topology LSeries.notation
open Complex Filter Set Topology

namespace NBMellinTools.NB12

/-- The meromorphically continued version of the active shifted
Abel--Mellin integrand. -/
noncomputable def bblsActiveHurwitzAbelIntegrand
    (damping : ℝ) (a q : ℕ) [NeZero q] (w : ℂ) : ℂ :=
  (damping : ℂ) ^ (-w) * Complex.Gamma w *
    bblsEstermannHurwitzContinuation a q (1 + w)

/-- The sign-normalized reflected Gamma weight. Its residue at `s=1` is
one. -/
noncomputable def bblsNormalizedReflectedAbelWeight
    (damping : ℝ) (s : ℂ) : ℂ :=
  -(Complex.Gamma (1 - s) * (damping : ℂ) ^ (s - 1))

/-- The complete reflected integrand before the extra active factor
`delta/s` is reattached. -/
noncomputable def bblsNormalizedReflectedAbelIntegrand
    (damping : ℝ) (a q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  bblsNormalizedReflectedAbelWeight damping s *
    bblsEstermannHurwitzContinuation a q (1 - s)

/-- Exact normalization under `s=-w`. The factor `delta/s` is essential:
dropping it would change the pole order at zero and lose the active `1/n`
normalization. -/
theorem bblsActiveHurwitzAbelIntegrand_neg_eq_reflected
    {damping : ℝ} (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] {s : ℂ} (hs : s ≠ 0) :
    bblsActiveHurwitzAbelIntegrand damping a q (-s) =
      (damping : ℂ) / s *
        bblsNormalizedReflectedAbelIntegrand damping a q s := by
  have hd0 : (damping : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdamping.ne'
  have hgamma0 : -s ≠ 0 := neg_ne_zero.mpr hs
  have hgamma := Complex.Gamma_add_one (-s) hgamma0
  have hgamma' : Complex.Gamma (1 - s) =
      (-s) * Complex.Gamma (-s) := by
    convert hgamma using 1
    ring_nf
  have hpow : (damping : ℂ) ^ s =
      (damping : ℂ) * (damping : ℂ) ^ (s - 1) := by
    calc
      (damping : ℂ) ^ s =
          (damping : ℂ) ^ ((s - 1) + 1) := by ring_nf
      _ = (damping : ℂ) ^ (s - 1) * (damping : ℂ) ^ (1 : ℂ) := by
        rw [Complex.cpow_add _ _ hd0]
      _ = (damping : ℂ) * (damping : ℂ) ^ (s - 1) := by
        rw [Complex.cpow_one]
        ring
  unfold bblsActiveHurwitzAbelIntegrand
    bblsNormalizedReflectedAbelIntegrand
    bblsNormalizedReflectedAbelWeight
  rw [neg_neg, show 1 + -s = 1 - s by ring, hgamma']
  change (damping : ℂ) ^ s * Complex.Gamma (-s) *
      bblsEstermannHurwitzContinuation a q (1 - s) = _
  rw [hpow]
  field_simp [hs]

/-! ## The additional pole at `s=1` -/

/-- The sign-normalized reflected weight has unit residue at `s=1`. -/
theorem tendsto_bblsNormalizedReflectedAbelWeight_residue_one
    (damping : ℝ) (hdamping : 0 < damping) :
    Tendsto
      (fun s : ℂ =>
        (s - 1) * bblsNormalizedReflectedAbelWeight damping s)
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
  have hd0 : (damping : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdamping.ne'
  have hsub : Tendsto (fun s : ℂ => 1 - s)
      (𝓝[≠] (1 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    simpa using
      (((hasDerivAt_const (x := (1 : ℂ)) (c := (1 : ℂ))).sub
        (hasDerivAt_id (x := (1 : ℂ)))).tendsto_nhdsNE (by norm_num))
  have hgamma : Tendsto
      (fun s : ℂ => (1 - s) * Complex.Gamma (1 - s))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
    Complex.tendsto_self_mul_Gamma_nhds_zero.comp hsub
  have hpow : Tendsto (fun s : ℂ =>
      (damping : ℂ) ^ (s - 1))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
    have hcont : ContinuousAt (fun s : ℂ =>
        (damping : ℂ) ^ (s - 1)) 1 :=
      (continuousAt_const_cpow hd0).comp
        (continuousAt_id.sub continuousAt_const)
    simpa using hcont.tendsto.mono_left inf_le_left
  have hproduct := hgamma.mul hpow
  apply (show Tendsto
      (fun s : ℂ => ((1 - s) * Complex.Gamma (1 - s)) *
        (damping : ℂ) ^ (s - 1))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) by simpa using hproduct).congr'
  filter_upwards with s
  unfold bblsNormalizedReflectedAbelWeight
  ring

/-- The complete normalized reflected integrand has residue `D(0,a/q)` at
`s=1`. -/
theorem tendsto_bblsNormalizedReflectedAbelIntegrand_residue_one
    (damping : ℝ) (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] :
    Tendsto
      (fun s : ℂ =>
        (s - 1) *
          bblsNormalizedReflectedAbelIntegrand damping a q s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (bblsEstermannHurwitzContinuation a q 0)) := by
  have hweight :=
    tendsto_bblsNormalizedReflectedAbelWeight_residue_one damping hdamping
  have hDPoint : ContinuousAt
      (bblsEstermannHurwitzContinuation a q) 0 :=
    (differentiableAt_bblsEstermannHurwitzContinuation a q
      (by norm_num)).continuousAt
  have harg : Tendsto (fun s : ℂ => 1 - s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hcont : ContinuousAt (fun s : ℂ => 1 - s) 1 := by fun_prop
    simpa using hcont.tendsto.mono_left inf_le_left
  have hD : Tendsto (fun s : ℂ =>
      bblsEstermannHurwitzContinuation a q (1 - s))
      (𝓝[≠] (1 : ℂ))
      (𝓝 (bblsEstermannHurwitzContinuation a q 0)) :=
    hDPoint.tendsto.comp harg
  have hproduct := hweight.mul hD
  apply (show Tendsto
      (fun s : ℂ =>
        ((s - 1) * bblsNormalizedReflectedAbelWeight damping s) *
          bblsEstermannHurwitzContinuation a q (1 - s))
      (𝓝[≠] (1 : ℂ))
      (𝓝 (bblsEstermannHurwitzContinuation a q 0)) by
        simpa using hproduct).congr'
  filter_upwards with s
  unfold bblsNormalizedReflectedAbelIntegrand
  ring

/-- Reattaching the exact active factor `delta/s` makes the extra reflected
residue precisely `delta * D(0,a/q)`. -/
theorem tendsto_bblsActiveReflectedIntegrand_residue_one
    (damping : ℝ) (hdamping : 0 < damping)
    (a q : ℕ) [NeZero q] :
    Tendsto
      (fun s : ℂ =>
        (s - 1) * ((damping : ℂ) / s *
          bblsNormalizedReflectedAbelIntegrand damping a q s))
      (𝓝[≠] (1 : ℂ))
      (𝓝 ((damping : ℂ) *
        bblsEstermannHurwitzContinuation a q 0)) := by
  have hfactorCont : ContinuousAt (fun s : ℂ =>
      (damping : ℂ) / s) 1 :=
    continuousAt_const.div continuousAt_id (by norm_num)
  have hfactor : Tendsto (fun s : ℂ => (damping : ℂ) / s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (damping : ℂ)) := by
    simpa using hfactorCont.tendsto.mono_left inf_le_left
  have hres :=
    tendsto_bblsNormalizedReflectedAbelIntegrand_residue_one
      damping hdamping a q
  have hproduct := hfactor.mul hres
  apply (show Tendsto
      (fun s : ℂ => ((damping : ℂ) / s) *
        ((s - 1) *
          bblsNormalizedReflectedAbelIntegrand damping a q s))
      (𝓝[≠] (1 : ℂ))
      (𝓝 ((damping : ℂ) *
        bblsEstermannHurwitzContinuation a q 0)) by
          simpa using hproduct).congr'
  filter_upwards with s
  ring

/-- The additional residue is Abel-small: it vanishes as the positive
damping parameter tends to zero. -/
theorem tendsto_bblsAdditionalReflectedResidue_zero
    (a q : ℕ) [NeZero q] :
    Tendsto
      (fun damping : ℝ =>
        (damping : ℂ) * bblsEstermannHurwitzContinuation a q 0)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcont : ContinuousAt (fun damping : ℝ =>
      (damping : ℂ) * bblsEstermannHurwitzContinuation a q 0) 0 := by
    fun_prop
  simpa using hcont.tendsto.mono_left inf_le_left

end NBMellinTools.NB12
