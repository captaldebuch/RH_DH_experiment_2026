/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSAbelMellin
import Mathlib.NumberTheory.LSeries.ZMod

/-!
# NB12i: rational Hurwitz decomposition of the BBLS Estermann series

For a positive modulus `q`, this file identifies the rational BBLS
Estermann series with a finite double sum of Hurwitz zeta functions.  The
formula is implemented through Mathlib's congruence `ZMod.LFunction`, which
avoids invalid branch manipulations for complex powers.

On `Re(s) > 1` the finite continuation agrees exactly with

`D(s,a/q) = sum d(n) exp(2*pi*I*a*n/q) / n^s`.

The finite Hurwitz expression is defined on all of `ℂ` and is holomorphic
away from its possible pole at `s = 1`.  No functional equation, contour
shift, correction matching, or signed H15 decay is claimed here.
-/

open scoped BigOperators Topology LSeries.notation
open Complex Filter LSeries HurwitzZeta Topology ZMod

namespace NBMellinTools.NB12

/-! ## Product-indexed form of the rational Estermann series -/

/-- The product-indexed term before decomposition into residue classes. -/
noncomputable def bblsEstermannDoubleTerm
    (a q : ℕ) (s : ℂ) (p : ℕ × ℕ) : ℂ :=
  bblsAdditiveCharacter (p.1 * p.2) ((a : ℝ) / (q : ℝ)) *
    LSeries.term (1 : ℕ → ℂ) s p.1 *
      LSeries.term (1 : ℕ → ℂ) s p.2

/-- The rational product-indexed Estermann series is absolutely summable
throughout `Re(s) > 1`. -/
theorem summable_bblsEstermannDoubleTerm
    (a q : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (bblsEstermannDoubleTerm a q s) := by
  have hbase := summable_mul_of_summable_norm
    (LSeriesSummable_one_iff.mpr hs).norm
    (LSeriesSummable_one_iff.mpr hs).norm
  exact hbase.norm.of_norm_bounded fun p => by
    simp [bblsEstermannDoubleTerm]

/-- One rational Estermann coefficient is the sum of the product-indexed
terms in its multiplication fiber. -/
theorem term_bblsEstermannCoeff_rat_eq_fiberTsum
    (a q : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (bblsEstermannCoeff ((a : ℝ) / (q : ℝ))) s n =
      ∑' (p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n}),
        bblsEstermannDoubleTerm a q s p := by
  have hterm :
      LSeries.term (bblsEstermannCoeff ((a : ℝ) / (q : ℝ))) s n =
        bblsAdditiveCharacter n ((a : ℝ) / (q : ℝ)) *
          LSeries.term bblsEstermannDivisorCoeff s n := by
    by_cases hn : n = 0
    · simp [hn]
    · simp [LSeries.term_of_ne_zero hn, bblsEstermannCoeff]
      ring
  rw [hterm, bblsEstermannDivisorCoeff, LSeries.term_convolution']
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  have hp : p.val.1 * p.val.2 = n := by
    have hp' := p.property
    change p.val.1 * p.val.2 ∈ ({n} : Set ℕ) at hp'
    exact Set.mem_singleton_iff.mp hp'
  have hphase :
      bblsAdditiveCharacter n ((a : ℝ) / (q : ℝ)) =
        bblsAdditiveCharacter (p.val.1 * p.val.2)
          ((a : ℝ) / (q : ℝ)) := by
    rw [hp]
  unfold bblsEstermannDoubleTerm
  rw [hphase]
  ring

/-- On `Re(s) > 1`, the rational Estermann L-series is its absolutely
convergent product-indexed double series. -/
theorem bblsEstermannDirichletSeries_rat_eq_tsum_prod
    (a q : ℕ) {s : ℂ} (hs : 1 < s.re) :
    bblsEstermannDirichletSeries ((a : ℝ) / (q : ℝ)) s =
      ∑' p : ℕ × ℕ, bblsEstermannDoubleTerm a q s p := by
  unfold bblsEstermannDirichletSeries LSeries
  have hfiber :=
    (summable_bblsEstermannDoubleTerm a q hs).hasSum.tsum_fiberwise
      (fun p : ℕ × ℕ => p.1 * p.2)
  apply HasSum.tsum_eq
  convert hfiber using 1
  ext n
  exact term_bblsEstermannCoeff_rat_eq_fiberTsum a q s n

/-! ## Finite double Hurwitz continuation -/

/-- The bilinear standard additive character on two residue classes. -/
noncomputable def bblsEstermannResiduePhase
    (a : ℕ) {q : ℕ} [NeZero q] (j k : ZMod q) : ℂ :=
  ZMod.stdAddChar ((a : ZMod q) * j * k)

/-- The rational Estermann continuation, represented as a nested congruence
`LFunction`.  Mathlib expands each level into a finite Hurwitz-zeta sum. -/
noncomputable def bblsEstermannHurwitzContinuation
    (a q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  ZMod.LFunction
    (fun j : ZMod q =>
      ZMod.LFunction
        (fun k : ZMod q => bblsEstermannResiduePhase a j k) s)
    s

/-- The continuation displayed explicitly as a finite double Hurwitz-zeta
sum.  The nested association mirrors `ZMod.LFunction` definitionally. -/
noncomputable def bblsEstermannHurwitzFiniteSum
    (a q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-s) *
    ∑ j : ZMod q,
      ((q : ℂ) ^ (-s) *
          ∑ k : ZMod q,
            bblsEstermannResiduePhase a j k *
              HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) *
        HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s

/-- Unfolding the nested congruence L-functions gives the exact finite
double Hurwitz formula. -/
theorem bblsEstermannHurwitzContinuation_eq_finiteSum
    (a q : ℕ) [NeZero q] (s : ℂ) :
    bblsEstermannHurwitzContinuation a q s =
      bblsEstermannHurwitzFiniteSum a q s := by
  rfl

/-- On natural residue classes, the modular phase equals the active BBLS
rational additive character. -/
theorem bblsEstermannResiduePhase_natCast
    (a q m n : ℕ) [NeZero q] :
    bblsEstermannResiduePhase a (m : ZMod q) (n : ZMod q) =
      bblsAdditiveCharacter (m * n) ((a : ℝ) / (q : ℝ)) := by
  rw [bblsAdditiveCharacter_rat_eq_stdAddChar]
  unfold bblsEstermannResiduePhase
  congr 2
  push_cast
  ring

/-- An inner congruence-series row is the expected additive twist of the
ordinary zeta-series row. -/
theorem term_bblsEstermannResiduePhase_eq
    (a q m n : ℕ) [NeZero q] (s : ℂ) :
    LSeries.term
        (fun r : ℕ =>
          bblsEstermannResiduePhase a (m : ZMod q) (r : ZMod q)) s n =
      bblsAdditiveCharacter (m * n) ((a : ℝ) / (q : ℝ)) *
        LSeries.term (1 : ℕ → ℂ) s n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [bblsEstermannResiduePhase_natCast]
    simp [div_eq_mul_inv]

/-- The outer term of the nested Hurwitz continuation is one row of the
product-indexed rational Estermann sum. -/
theorem outer_term_bblsEstermannHurwitz_eq_inner_tsum
    (a q m : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    LSeries.term
        (fun r : ℕ =>
          ZMod.LFunction
            (fun k : ZMod q =>
              bblsEstermannResiduePhase a (r : ZMod q) k) s)
        s m =
      ∑' n : ℕ, bblsEstermannDoubleTerm a q s (m, n) := by
  by_cases hm : m = 0
  · subst m
    simp [bblsEstermannDoubleTerm]
  · rw [LSeries.term_of_ne_zero hm]
    rw [ZMod.LFunction_eq_LSeries _ hs]
    unfold LSeries
    rw [← tsum_div_const]
    apply tsum_congr
    intro n
    rw [term_bblsEstermannResiduePhase_eq]
    unfold bblsEstermannDoubleTerm
    rw [LSeries.term_of_ne_zero hm]
    simp only [Pi.one_apply, one_div]
    ring

/-- The finite double Hurwitz continuation agrees exactly with the active
rational BBLS Estermann Dirichlet series on `Re(s) > 1`. -/
theorem bblsEstermannHurwitzContinuation_eq_dirichletSeries
    (a q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    bblsEstermannHurwitzContinuation a q s =
      bblsEstermannDirichletSeries ((a : ℝ) / (q : ℝ)) s := by
  unfold bblsEstermannHurwitzContinuation
  rw [ZMod.LFunction_eq_LSeries _ hs]
  unfold LSeries
  rw [bblsEstermannDirichletSeries_rat_eq_tsum_prod a q hs]
  rw [(summable_bblsEstermannDoubleTerm a q hs).tsum_prod]
  apply tsum_congr
  intro m
  exact outer_term_bblsEstermannHurwitz_eq_inner_tsum a q m hs

/-! ## Meromorphic status visible from the finite formula -/

/-- The finite Hurwitz continuation is holomorphic away from its only
possible singular point `s = 1`. -/
theorem differentiableAt_bblsEstermannHurwitzContinuation
    (a q : ℕ) [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (bblsEstermannHurwitzContinuation a q) s := by
  rw [show bblsEstermannHurwitzContinuation a q =
      bblsEstermannHurwitzFiniteSum a q from rfl]
  unfold bblsEstermannHurwitzFiniteSum
  have hq : DifferentiableAt ℂ (fun z : ℂ => (q : ℂ) ^ (-z)) s := by
    fun_prop
  apply hq.mul
  apply DifferentiableAt.fun_sum
  intro j _
  apply DifferentiableAt.mul
  · apply hq.mul
    apply DifferentiableAt.fun_sum
    intro k _
    exact (HurwitzZeta.differentiableAt_hurwitzZeta _ hs).const_mul _
  · exact HurwitzZeta.differentiableAt_hurwitzZeta _ hs

/-- Hence the rational finite continuation is holomorphic on `ℂ \ {1}`. -/
theorem differentiableOn_bblsEstermannHurwitzContinuation_off_one
    (a q : ℕ) [NeZero q] :
    DifferentiableOn ℂ (bblsEstermannHurwitzContinuation a q)
      ({1}ᶜ : Set ℂ) := by
  intro s hs
  exact (differentiableAt_bblsEstermannHurwitzContinuation a q
    (by simpa using hs)).differentiableWithinAt

/-! ## Exact leading coefficient at the possible double pole -/

/-- The leading coefficient obtained after removing two powers of `s-1`.
The external prompt's claim that products of distinct Hurwitz factors do not
produce a double pole is false; every factor has the same pole at `s=1`.
The finite additive-character sum determines whether the leading coefficient
cancels. -/
noncomputable def bblsEstermannDoublePoleCoefficient
    (a q : ℕ) [NeZero q] : ℂ :=
  (q : ℂ) ^ (-(1 : ℂ)) *
    ∑ j : ZMod q,
      (q : ℂ) ^ (-(1 : ℂ)) *
        ∑ k : ZMod q, bblsEstermannResiduePhase a j k

/-- For a reduced rational parameter, the complete bilinear residue phase
has total mass `q`. -/
theorem sum_bblsEstermannResiduePhase_of_coprime
    (a q : ℕ) [NeZero q] (haq : a.Coprime q) :
    (∑ j : ZMod q, ∑ k : ZMod q,
      bblsEstermannResiduePhase a j k) = (q : ℂ) := by
  have ha : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 haq
  have hzero (j : ZMod q) : (a : ZMod q) * j = 0 ↔ j = 0 := by
    constructor
    · intro h
      apply ha.mul_left_cancel
      simpa using h
    · rintro rfl
      simp
  have hinner (j : ZMod q) :
      (∑ k : ZMod q, bblsEstermannResiduePhase a j k) =
        if (a : ZMod q) * j = 0 then (q : ℂ) else 0 := by
    simpa [bblsEstermannResiduePhase, mul_assoc, mul_comm, mul_left_comm]
      using AddChar.sum_mulShift ((a : ZMod q) * j)
        (ZMod.isPrimitive_stdAddChar q)
  simp_rw [hinner, hzero]
  simp

/-- For a reduced rational parameter, the possible double pole is genuine
and its leading coefficient is exactly `1/q`. -/
theorem bblsEstermannDoublePoleCoefficient_of_coprime
    (a q : ℕ) [NeZero q] (haq : a.Coprime q) :
    bblsEstermannDoublePoleCoefficient a q = ((q : ℂ) : ℂ)⁻¹ := by
  unfold bblsEstermannDoublePoleCoefficient
  rw [← Finset.mul_sum]
  rw [sum_bblsEstermannResiduePhase_of_coprime a q haq]
  rw [Complex.cpow_neg_one]
  field_simp

/-- Exact punctured limit after removing the possible double pole at one. -/
theorem bblsEstermannHurwitzContinuation_doublePole_limit
    (a q : ℕ) [NeZero q] :
    Tendsto
      (fun s : ℂ =>
        (s - 1) ^ 2 * bblsEstermannHurwitzContinuation a q s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (bblsEstermannDoublePoleCoefficient a q)) := by
  let regularized : ℂ → ℂ := fun s =>
    (q : ℂ) ^ (-s) *
      ∑ j : ZMod q,
        ((q : ℂ) ^ (-s) *
            ∑ k : ZMod q,
              bblsEstermannResiduePhase a j k *
                ((s - 1) *
                  HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s)) *
          ((s - 1) *
            HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s)
  have heq : (fun s : ℂ =>
      (s - 1) ^ 2 * bblsEstermannHurwitzContinuation a q s) =
      regularized := by
    funext s
    unfold regularized bblsEstermannHurwitzContinuation ZMod.LFunction
    simp only [Finset.mul_sum, Finset.sum_mul]
    ring_nf
  rw [heq]
  have hq : Tendsto (fun s : ℂ => (q : ℂ) ^ (-s))
      (𝓝[≠] (1 : ℂ)) (𝓝 ((q : ℂ) ^ (-(1 : ℂ)))) := by
    exact
      (by fun_prop : ContinuousAt (fun s : ℂ => (q : ℂ) ^ (-s)) 1).tendsto.mono_left
        nhdsWithin_le_nhds
  have hsum : Tendsto
      (fun s : ℂ =>
        ∑ j : ZMod q,
          ((q : ℂ) ^ (-s) *
              ∑ k : ZMod q,
                bblsEstermannResiduePhase a j k *
                  ((s - 1) *
                    HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s)) *
            ((s - 1) *
              HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s))
      (𝓝[≠] (1 : ℂ))
      (𝓝 (∑ j : ZMod q,
        (q : ℂ) ^ (-(1 : ℂ)) *
          ∑ k : ZMod q, bblsEstermannResiduePhase a j k)) := by
    apply tendsto_finsetSum
    intro j _
    have hinner : Tendsto
        (fun s : ℂ =>
          ∑ k : ZMod q,
            bblsEstermannResiduePhase a j k *
              ((s - 1) *
                HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s))
        (𝓝[≠] (1 : ℂ))
        (𝓝 (∑ k : ZMod q, bblsEstermannResiduePhase a j k)) := by
      apply tendsto_finsetSum
      intro k _
      simpa using
        (tendsto_const_nhds.mul
          (HurwitzZeta.hurwitzZeta_residue_one (ZMod.toAddCircle k)))
    simpa using
      ((hq.mul hinner).mul
        (HurwitzZeta.hurwitzZeta_residue_one (ZMod.toAddCircle j)))
  simpa [regularized, bblsEstermannDoublePoleCoefficient] using hq.mul hsum

end NBMellinTools.NB12
