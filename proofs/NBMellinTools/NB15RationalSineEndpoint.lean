/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15DirichletAbelBoundary
import NBMellinTools.NB12RationalSineCotangent
import NBMellinTools.NB12BBLSEstermannCompatibility
import RiemannHypothesis.Criteria.NymanBeurling.BBLSPhiOne
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The rational sine endpoint

This file proves the conditionally convergent rational endpoint

`sinZeta(j/q, 1) = pi * (1/2 - j/q)`

for nonzero residue classes.  The proof uses the already active finite
sine--cotangent transform, periodic Abel summation from BBLS, and the generic
Dirichlet--Abelian boundary theorem.  No RH input occurs.
-/

open Complex Filter HurwitzZeta Topology ZMod
open scoped BigOperators

namespace NBMellinTools.NB15

open NBMellinTools.NB10
open NBMellinTools.NB12
open RH.Criteria.NymanBeurling.VasyuninGram

/-- Real boundary coefficient of the harmonic sine series. -/
noncomputable def rationalSineBoundaryTerm (x : ℝ) (n : ℕ) : ℝ :=
  Real.sin (2 * Real.pi * x * n) / (n : ℝ)

@[simp] theorem rationalSineBoundaryTerm_zero (x : ℝ) :
    rationalSineBoundaryTerm x 0 = 0 := by
  simp [rationalSineBoundaryTerm]

/-- The periodic rational sine coefficient. -/
noncomputable def rationalSinePeriodicTerm
    {q : ℕ} [NeZero q] (j : ZMod q) (n : ℕ) : ℝ :=
  Real.sin (2 * Real.pi * ((j.val : ℝ) / q) * n)

theorem rationalSinePeriodicTerm_eq_stdAddChar_im
    {q : ℕ} [NeZero q] (j : ZMod q) (n : ℕ) :
    rationalSinePeriodicTerm j n =
      (ZMod.stdAddChar (j * (n : ZMod q))).im := by
  have hphase := congrArg Complex.im
    (bblsAdditiveCharacter_rat_eq_stdAddChar j.val q n)
  have hcast : ((j.val * n : ℕ) : ZMod q) = j * (n : ZMod q) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hcast] at hphase
  rw [← hphase]
  simp [rationalSinePeriodicTerm, bblsAdditiveCharacter, Complex.exp_im]
  ring_nf

theorem rationalSinePeriodicTerm_periodic
    {q : ℕ} [NeZero q] (j : ZMod q) (n : ℕ) :
    rationalSinePeriodicTerm j (n + q) = rationalSinePeriodicTerm j n := by
  simp only [rationalSinePeriodicTerm_eq_stdAddChar_im]
  congr 2
  simp [Nat.cast_add]

@[simp] theorem rationalSinePeriodicTerm_zero
    {q : ℕ} [NeZero q] (j : ZMod q) :
    rationalSinePeriodicTerm j 0 = 0 := by
  simp [rationalSinePeriodicTerm]

@[simp] theorem rationalSinePeriodicTerm_modulus
    {q : ℕ} [NeZero q] (j : ZMod q) :
    rationalSinePeriodicTerm j q = 0 := by
  simpa using rationalSinePeriodicTerm_periodic j 0

private theorem stdAddChar_mul_nat_range_sum_eq_zero
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    (∑ n ∈ Finset.range q,
      ZMod.stdAddChar (j * (n : ZMod q))) = 0 := by
  have hchar : (∑ z : ZMod q, ZMod.stdAddChar (z * j)) = 0 := by
    simpa [hj] using AddChar.sum_mulShift (ψ := ZMod.stdAddChar) j
      (ZMod.isPrimitive_stdAddChar q)
  have hfin :
      (∑ n : Fin q, ZMod.stdAddChar ((ZMod.finEquiv q n) * j)) = 0 := by
    calc
      (∑ n : Fin q, ZMod.stdAddChar ((ZMod.finEquiv q n) * j)) =
          ∑ z : ZMod q, ZMod.stdAddChar (z * j) := by
            apply Fintype.sum_equiv (ZMod.finEquiv q)
            intro n
            rfl
      _ = 0 := hchar
  have hfinCast (n : Fin q) : ZMod.finEquiv q n = (n : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
        apply ZMod.val_injective (q + 1)
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt n.isLt]
        rfl
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ n : Fin q, ZMod.stdAddChar (j * (n : ZMod q))) =
        ∑ n : Fin q, ZMod.stdAddChar ((ZMod.finEquiv q n) * j) := by
          apply Finset.sum_congr rfl
          intro n _
          apply congrArg ZMod.stdAddChar
          rw [hfinCast n, mul_comm]
    _ = 0 := hfin

/-- A nontrivial rational sine coefficient has mean zero over one period. -/
theorem rationalSinePeriodicTerm_meanzero
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    (∑ n ∈ Finset.Ioc 0 q, rationalSinePeriodicTerm j n) = 0 := by
  have hrangeChar := stdAddChar_mul_nat_range_sum_eq_zero j hj
  have hrangeSine :
      (∑ n ∈ Finset.range q, rationalSinePeriodicTerm j n) = 0 := by
    calc
      (∑ n ∈ Finset.range q, rationalSinePeriodicTerm j n) =
          ∑ n ∈ Finset.range q,
            (ZMod.stdAddChar (j * (n : ZMod q))).im := by
              apply Finset.sum_congr rfl
              intro n _
              exact rationalSinePeriodicTerm_eq_stdAddChar_im j n
      _ = (∑ n ∈ Finset.range q,
            ZMod.stdAddChar (j * (n : ZMod q))).im := by
              rw [Complex.im_sum]
      _ = 0 := by rw [hrangeChar]; rfl
  have hins : Finset.range (q + 1) =
      insert 0 (Finset.Ioc 0 q) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hzeroNot : 0 ∉ Finset.Ioc 0 q := by simp
  have hleft :
      (∑ n ∈ Finset.range (q + 1), rationalSinePeriodicTerm j n) =
        ∑ n ∈ Finset.Ioc 0 q, rationalSinePeriodicTerm j n := by
    rw [hins, Finset.sum_insert hzeroNot,
      rationalSinePeriodicTerm_zero, zero_add]
  have hright :
      (∑ n ∈ Finset.range (q + 1), rationalSinePeriodicTerm j n) =
        ∑ n ∈ Finset.range q, rationalSinePeriodicTerm j n := by
    rw [Finset.sum_range_succ, rationalSinePeriodicTerm_modulus, add_zero]
  rw [← hleft, hright, hrangeSine]

/-! ## Finite cotangent evaluation -/

/-- The active NB12 finite transform gives the exact rational
sine--cotangent identity. -/
theorem rationalSineCotangentFiniteIdentity
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    (∑ r ∈ Finset.Ioc 0 (q - 1),
      rationalSinePeriodicTerm j r * cotangentTerm r q) =
        (q : ℝ) - 2 * (j.val : ℝ) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hjVal : j.val ≠ 0 := by
    intro hval
    apply hj
    apply ZMod.val_injective q
    simp [hval]
  have hset : Finset.Ioc 0 (q - 1) = Finset.Ico 1 q := by
    ext r
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset]
  calc
    (∑ r ∈ Finset.Ico 1 q,
        rationalSinePeriodicTerm j r * cotangentTerm r q) =
      ∑ r ∈ Finset.Ico 1 q,
        Real.sin
          (2 * Real.pi * (1 : ℝ) *
            (((r * j.val : ℕ) : ℝ) / (q : ℝ))) *
          cotangentTerm r q := by
            apply Finset.sum_congr rfl
            intro r _
            unfold rationalSinePeriodicTerm
            congr 2
            push_cast
            ring
    _ = rationalCotangentFourierMode j.val q 1 := by
      simpa using sum_sine_mul_cotangentTerm_eq_mode j.val q 1 hq
    _ = (q : ℝ) - 2 * (j.val : ℝ) := by
      unfold rationalCotangentFourierMode
      rw [one_mul, Nat.mod_eq_of_lt j.val_lt, if_neg hjVal]

/-! ## Ordered harmonic boundary -/

theorem rationalSine_digamma_value
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    (1 / (q : ℝ)) * ∑ r ∈ Finset.Ioc 0 q,
        rationalSinePeriodicTerm j r *
          bblsDigammaShift ((r : ℝ) / q) =
      Real.pi * (1 / 2 - (j.val : ℝ) / q) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsplitq : Finset.Ioc 0 q =
      insert q (Finset.Ioc 0 (q - 1)) := by
    ext r
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  have hqnotmem : q ∉ Finset.Ioc 0 (q - 1) := by
    simp only [Finset.mem_Ioc]
    omega
  rw [hsplitq, Finset.sum_insert hqnotmem,
    rationalSinePeriodicTerm_modulus, zero_mul, zero_add]
  let S : ℝ := ∑ r ∈ Finset.Ioc 0 (q - 1),
    rationalSinePeriodicTerm j r * bblsDigammaShift ((r : ℝ) / q)
  have hreindex : S = ∑ r ∈ Finset.Ioc 0 (q - 1),
      (-rationalSinePeriodicTerm j r) *
        bblsDigammaShift (1 - (r : ℝ) / q) := by
    unfold S
    apply Finset.sum_nbij' (i := fun r => q - r) (j := fun r => q - r)
    · intro r hr
      simp only [Finset.mem_Ioc] at hr ⊢
      omega
    · intro r hr
      simp only [Finset.mem_Ioc] at hr ⊢
      omega
    · intro r hr
      simp only [Finset.mem_Ioc] at hr
      omega
    · intro r hr
      simp only [Finset.mem_Ioc] at hr
      omega
    · intro r hr
      have hrmem := hr
      simp only [Finset.mem_Ioc] at hr
      have hrq : r ≤ q := by omega
      have hsine : rationalSinePeriodicTerm j (q - r) =
          -rationalSinePeriodicTerm j r := by
        unfold rationalSinePeriodicTerm
        push_cast [Nat.cast_sub hrq]
        have harg :
            2 * Real.pi * ((j.val : ℝ) / q) * ((q : ℝ) - r) =
              j.val * (2 * Real.pi) -
                2 * Real.pi * ((j.val : ℝ) / q) * r := by
          field_simp
        rw [harg, Real.sin_nat_mul_two_pi_sub]
      have harg : ((q - r : ℕ) : ℝ) / q =
          1 - (r : ℝ) / q := by
        push_cast [Nat.cast_sub hrq]
        field_simp
      rw [hsine, harg]
      ring_nf
  have hdouble : 2 * S = ∑ r ∈ Finset.Ioc 0 (q - 1),
      rationalSinePeriodicTerm j r *
        (Real.pi * Real.cot (Real.pi * ((r : ℝ) / q))) := by
    rw [show 2 * S = S + S by ring]
    nth_rewrite 2 [hreindex]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_Ioc] at hr
    have hr0 : (0 : ℝ) < (r : ℝ) / q := by
      exact div_pos (by exact_mod_cast hr.1) hqR
    have hr1 : (r : ℝ) / q < 1 := by
      rw [div_lt_one hqR]
      exact_mod_cast (show r < q by omega)
    have hrefl := bblsDigammaShift_reflection hr0 hr1
    calc
      rationalSinePeriodicTerm j r *
            bblsDigammaShift ((r : ℝ) / q) +
          (-rationalSinePeriodicTerm j r) *
            bblsDigammaShift (1 - (r : ℝ) / q) =
        rationalSinePeriodicTerm j r *
          (bblsDigammaShift ((r : ℝ) / q) -
            bblsDigammaShift (1 - (r : ℝ) / q)) := by ring
      _ = rationalSinePeriodicTerm j r *
          (Real.pi * Real.cot (Real.pi * ((r : ℝ) / q))) := by
            rw [hrefl]
  have hcot (r : ℕ) :
      Real.cot (Real.pi * ((r : ℝ) / q)) = cotangentTerm r q := by
    unfold cotangentTerm
    rw [Real.cot_eq_cos_div_sin]
    congr 2 <;> ring
  have h2S : 2 * S = Real.pi * ((q : ℝ) - 2 * (j.val : ℝ)) := by
    calc
      2 * S = Real.pi * ∑ r ∈ Finset.Ioc 0 (q - 1),
          rationalSinePeriodicTerm j r * cotangentTerm r q := by
            rw [hdouble, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r _
            rw [hcot r]
            ring
      _ = _ := by rw [rationalSineCotangentFiniteIdentity j hj]
  change (1 / (q : ℝ)) * S = _
  have hS : S = Real.pi * ((q : ℝ) - 2 * (j.val : ℝ)) / 2 := by
    linarith
  rw [hS]
  field_simp

/-- Ordered convergence of the rational harmonic sine series. -/
theorem tendsto_rationalSineBoundaryTerm
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
        rationalSineBoundaryTerm ((j.val : ℝ) / q) n)
      atTop
      (𝓝 (Real.pi * (1 / 2 - (j.val : ℝ) / q))) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have h := bbls_tendsto_sum_div_of_periodic_meanzero
    (fun n : ℕ => rationalSinePeriodicTerm j n) q hq
    (rationalSinePeriodicTerm_periodic j)
    (rationalSinePeriodicTerm_meanzero j hj)
  rw [rationalSine_digamma_value j hj] at h
  simpa [rationalSineBoundaryTerm, rationalSinePeriodicTerm] using h

/-! ## Compatibility with analytic `sinZeta` -/

theorem hasSum_rationalSineBoundary_displaced
    (x d : ℝ) (hd : 0 < d) :
    HasSum
      (fun n : ℕ => rationalSineBoundaryTerm x n * (n : ℝ) ^ (-d))
      (HurwitzZeta.sinZeta x (((1 + d : ℝ) : ℂ))).re := by
  have hs : 1 < ((((1 + d : ℝ) : ℂ))).re := by simp; linarith
  have hcomplex := Complex.hasSum_re
    (HurwitzZeta.hasSum_nat_sinZeta x hs)
  refine hcomplex.congr_fun ?_
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [rationalSineBoundaryTerm]
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hpow : (n : ℂ) ^ (((1 + d : ℝ) : ℂ)) =
        (((n : ℝ) ^ (1 + d) : ℝ) : ℂ) := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast]
      exact (Complex.ofReal_cpow (Nat.cast_nonneg n) (1 + d)).symm
    rw [hpow, ← Complex.ofReal_div]
    simp only [Complex.ofReal_re]
    unfold rationalSineBoundaryTerm
    rw [Real.rpow_add hnR, Real.rpow_one, Real.rpow_neg hnR.le]
    field_simp

private theorem sinZeta_real_on_one_add_pos (x d : ℝ) (hd : 0 < d) :
    (HurwitzZeta.sinZeta x (((1 + d : ℝ) : ℂ))).im = 0 := by
  have hs : 1 < ((((1 + d : ℝ) : ℂ))).re := by simp; linarith
  have him := Complex.hasSum_im (HurwitzZeta.hasSum_nat_sinZeta x hs)
  exact him.unique (hasSum_zero.congr_fun fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · have hpow : (n : ℂ) ^ (((1 + d : ℝ) : ℂ)) =
          (((n : ℝ) ^ (1 + d) : ℝ) : ℂ) := by
        rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast]
        exact (Complex.ofReal_cpow (Nat.cast_nonneg n) (1 + d)).symm
      rw [hpow, ← Complex.ofReal_div]
      exact Complex.ofReal_im _)

/-- The genuine analytic rational endpoint required by Hurwitz zeta at
zero. -/
theorem sinZeta_rational_apply_one
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    HurwitzZeta.sinZeta (ZMod.toAddCircle j) 1 =
      (Real.pi : ℂ) * ((1 : ℂ) / 2 - (j.val : ℂ) / (q : ℂ)) := by
  let x : ℝ := (j.val : ℝ) / q
  let ell : ℝ := Real.pi * (1 / 2 - (j.val : ℝ) / q)
  let F : ℝ → ℝ := fun d =>
    (HurwitzZeta.sinZeta x (((1 + d : ℝ) : ℂ))).re
  have hpartial : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
        rationalSineBoundaryTerm x n) atTop (𝓝 ell) := by
    simpa [x, ell] using tendsto_rationalSineBoundaryTerm j hj
  have habel : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 ell) :=
    dirichletAbelian_tendsto_of_partial_sum_tendsto
      (rationalSineBoundaryTerm x) F
      (rationalSineBoundaryTerm_zero x) hpartial
      (fun d hd => hasSum_rationalSineBoundary_displaced x d hd)
  have harg : Tendsto (fun d : ℝ => (((1 + d : ℝ) : ℂ)))
      (𝓝 0) (𝓝 1) := by
    simpa using
      (show ContinuousAt (fun d : ℝ => (((1 + d : ℝ) : ℂ))) 0 by
        fun_prop).tendsto
  have hsin : Tendsto (HurwitzZeta.sinZeta x) (𝓝 1)
      (𝓝 (HurwitzZeta.sinZeta x 1)) :=
    (HurwitzZeta.differentiableAt_sinZeta x 1).continuousAt
  have hreContinuous : Tendsto F (𝓝[>] (0 : ℝ))
      (𝓝 (HurwitzZeta.sinZeta x 1).re) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa [F] using
        Complex.continuous_re.continuousAt.tendsto.comp (hsin.comp harg))
  have hre : (HurwitzZeta.sinZeta x 1).re = ell :=
    tendsto_nhds_unique hreContinuous habel
  have himWithin : Tendsto
      (fun d : ℝ => (HurwitzZeta.sinZeta x
        (((1 + d : ℝ) : ℂ))).im)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact (sinZeta_real_on_one_add_pos x d hd).symm
  have himContinuous : Tendsto
      (fun d : ℝ => (HurwitzZeta.sinZeta x
        (((1 + d : ℝ) : ℂ))).im)
      (𝓝[>] (0 : ℝ)) (𝓝 (HurwitzZeta.sinZeta x 1).im) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa using
        Complex.continuous_im.continuousAt.tendsto.comp (hsin.comp harg))
  have him : (HurwitzZeta.sinZeta x 1).im = 0 :=
    tendsto_nhds_unique himContinuous himWithin
  have hrhs :
      (Real.pi : ℂ) * ((1 : ℂ) / 2 - (j.val : ℂ) / (q : ℂ)) =
        (ell : ℂ) := by
    simp only [ell, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.ofReal_natCast]
  rw [ZMod.toAddCircle_apply, hrhs]
  change HurwitzZeta.sinZeta x 1 = (ell : ℂ)
  apply Complex.ext
  · simpa using hre
  · simpa using him

end NBMellinTools.NB15
