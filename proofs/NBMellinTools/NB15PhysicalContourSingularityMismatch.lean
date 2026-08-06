/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15CompletedPairingKernel
import NBMellinTools.NB12BBLSH15PoleDiagnostic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Singularity-order stop test for the physical/contour normalization

The physical Mellin numerator has at most a simple singularity at `s = 0`:
after multiplication by `s ^ 3` it tends to zero.  The active H15 Estermann
aggregate has a certified nonzero cubic Laurent coefficient already at
cutoff `n = 2`.  Consequently the two one-variable functions cannot be
identified directly.

This does not rule out a completed normalization with explicit Gamma,
functional-equation, residue, or projection factors.  It proves that those
factors are mandatory and cannot be replaced by boundary interpolation.
-/

open scoped BigOperators Topology

namespace NBMellinTools.NB15

open Complex Filter
open NBMellinTools.NB12

/-- The numerator before division by the Mellin variable. -/
noncomputable def certifiedMellinRegularNumerator (n : ℕ) (s : ℂ) : ℂ :=
  1 - riemannZeta s * certifiedDirichletPolynomial n s

theorem continuousAt_certifiedDirichletPolynomial_zero (n : ℕ) :
    ContinuousAt (certifiedDirichletPolynomial n) 0 := by
  unfold certifiedDirichletPolynomial
  refine (continuous_finsetSum Finset.univ ?_).continuousAt
  intro k _
  apply continuous_const.mul
  apply continuous_neg.const_cpow
  left
  norm_cast

theorem continuousAt_certifiedMellinRegularNumerator_zero (n : ℕ) :
    ContinuousAt (certifiedMellinRegularNumerator n) 0 := by
  unfold certifiedMellinRegularNumerator
  exact continuousAt_const.sub
    ((differentiableAt_riemannZeta (by norm_num)).continuousAt.mul
      (continuousAt_certifiedDirichletPolynomial_zero n))

/-- Cubic renormalization kills the physical Mellin numerator at zero. -/
theorem tendsto_cubic_mul_certifiedMellinNumerator_zero (n : ℕ) :
    Tendsto (fun s : ℂ => s ^ 3 * certifiedMellinNumerator n s)
      (𝓝[≠] 0) (𝓝 0) := by
  have hregular :
      Tendsto (certifiedMellinRegularNumerator n) (𝓝[≠] 0)
        (𝓝 (certifiedMellinRegularNumerator n 0)) :=
    (continuousAt_certifiedMellinRegularNumerator_zero n).tendsto.mono_left
      inf_le_left
  have hsquared : Tendsto (fun s : ℂ => s ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have hzero : Tendsto (fun s : ℂ => s) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    simpa using hzero.pow 2
  have hproduct :
      Tendsto
        (fun s : ℂ => s ^ 2 * certifiedMellinRegularNumerator n s)
        (𝓝[≠] 0) (𝓝 0) := by
    simpa using hsquared.mul hregular
  refine hproduct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  rw [certifiedMellinNumerator, certifiedMellinRegularNumerator]
  field_simp [hs]

/-- Cubic renormalization of the active contour family recovers its leading
Laurent coefficient. -/
theorem tendsto_cubic_mul_h15ActiveContourAggregate_zero (n : ℕ) :
    Tendsto (fun s : ℂ => s ^ 3 * h15ActiveContourAggregate n s)
      (𝓝[≠] 0) (𝓝 (h15GlobalThirdOrderCoefficient n)) := by
  let rhs : ℂ → ℂ := fun s =>
    s ^ 3 * h15AllPoleRemoved n s +
      h15GlobalThirdOrderCoefficient n +
      s * h15GlobalSecondOrderCoefficient (h15ContourDamping n) n +
      s ^ 2 * h15GlobalFirstOrderCoefficient n +
      s ^ 3 * (h15GlobalAdditionalResidue n / (s - 1))
  have hremoved : ContinuousAt (h15AllPoleRemoved n) 0 :=
    (analyticAt_h15AllPoleRemoved_of_re_lt_two n (by norm_num)).continuousAt
  have hid : ContinuousAt (fun s : ℂ => s) 0 := continuousAt_id
  have hden : ContinuousAt (fun s : ℂ => s - 1) 0 :=
    hid.sub continuousAt_const
  have hrhs : ContinuousAt rhs 0 := by
    dsimp [rhs]
    have h₁ := (hid.pow 3).mul hremoved
    have h₂ := hid.mul (continuousAt_const :
      ContinuousAt (fun _ : ℂ =>
        h15GlobalSecondOrderCoefficient (h15ContourDamping n) n) 0)
    have h₃ := (hid.pow 2).mul (continuousAt_const :
      ContinuousAt (fun _ : ℂ => h15GlobalFirstOrderCoefficient n) 0)
    have hquot := (continuousAt_const :
      ContinuousAt (fun _ : ℂ => h15GlobalAdditionalResidue n) 0).div
        hden (by norm_num)
    have h₄ := (hid.pow 3).mul hquot
    exact (((h₁.add continuousAt_const).add h₂).add h₃).add h₄
  have hrhs0 : rhs 0 = h15GlobalThirdOrderCoefficient n := by
    simp [rhs]
  have hlim :
      Tendsto rhs (𝓝[≠] 0)
        (𝓝 (h15GlobalThirdOrderCoefficient n)) := by
    rw [← hrhs0]
    exact hrhs.tendsto.mono_left inf_le_left
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    eventually_ne_nhdsWithin (by norm_num : (0 : ℂ) ≠ 1)] with s hs0 hs1
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs0
  rw [h15ActiveContourAggregate_eq_all_poles_removed n hs0 hs1]
  dsimp [rhs]
  field_simp [hs0, hs1]

/-- The raw physical Mellin numerator and raw H15 Estermann aggregate are not
the same meromorphic function.  Their leading orders already disagree at the
certified cutoff `n = 2`. -/
theorem certifiedMellinNumerator_two_ne_h15ActiveContourAggregate :
    certifiedMellinNumerator 2 ≠ h15ActiveContourAggregate 2 := by
  intro h
  have hphysical := tendsto_cubic_mul_certifiedMellinNumerator_zero 2
  rw [h] at hphysical
  have hcoefficient := tendsto_nhds_unique hphysical
    (tendsto_cubic_mul_h15ActiveContourAggregate_zero 2)
  exact h15GlobalThirdOrderCoefficient_two_ne_zero hcoefficient.symm

/-- A scalar factor regular at zero cannot repair the singularity mismatch.
Any valid completion must itself carry a singular factor (or perform an
explicit residue/projection operation). -/
theorem no_continuous_scalar_normalization_at_zero
    (M : ℂ → ℂ) (hM : ContinuousAt M 0)
    (hmatch : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      M s * certifiedMellinNumerator 2 s =
        h15ActiveContourAggregate 2 s) : False := by
  have hphysical := tendsto_cubic_mul_certifiedMellinNumerator_zero 2
  have hMt : Tendsto M (𝓝[≠] 0) (𝓝 (M 0)) :=
    hM.tendsto.mono_left inf_le_left
  have hleft :
      Tendsto
        (fun s : ℂ => s ^ 3 *
          (M s * certifiedMellinNumerator 2 s))
        (𝓝[≠] 0) (𝓝 0) := by
    have hproduct := hphysical.mul hMt
    simpa [mul_assoc, mul_comm, mul_left_comm] using hproduct
  have hactiveZero :
      Tendsto (fun s : ℂ => s ^ 3 * h15ActiveContourAggregate 2 s)
        (𝓝[≠] 0) (𝓝 0) := by
    refine hleft.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      eventually_ne_nhdsWithin (by norm_num : (0 : ℂ) ≠ 1)] with s hs0 hs1
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs0
    rw [hmatch s hs0 hs1]
  have hcoefficient := tendsto_nhds_unique hactiveZero
    (tendsto_cubic_mul_h15ActiveContourAggregate_zero 2)
  exact h15GlobalThirdOrderCoefficient_two_ne_zero hcoefficient.symm

end NBMellinTools.NB15
