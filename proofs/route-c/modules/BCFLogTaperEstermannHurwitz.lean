import Mathlib.NumberTheory.LSeries.ZMod
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannSeries

/-!
# Route B3: finite Hurwitz continuation of the Estermann series

For a positive modulus `q`, the continuation is expressed as a nested
congruence `LFunction`.  Since Mathlib constructs every congruence `LFunction`
as a finite linear combination of Hurwitz zeta functions, this is a genuine
finite Hurwitz-zeta continuation rather than another infinite series.

The main theorem of this module proves exact agreement with the classical
Estermann Dirichlet series on `re s > 1`.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz

open Complex Filter LSeries HurwitzZeta Topology ZMod
open scoped BigOperators LSeries.notation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries

/-- The bilinear standard additive character on two residue classes. -/
noncomputable def estermannResiduePhase
    (a : ℕ) {q : ℕ} [NeZero q] (j k : ZMod q) : ℂ :=
  ZMod.stdAddChar ((a : ZMod q) * j * k)

/-- The finite Hurwitz continuation, represented as a nested congruence
`LFunction`. -/
noncomputable def estermannHurwitzContinuation
    (a q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  ZMod.LFunction
    (fun j : ZMod q =>
      ZMod.LFunction (fun k : ZMod q => estermannResiduePhase a j k) s)
    s

/-- The same continuation displayed explicitly as a finite double Hurwitz-zeta
sum.  The association of factors mirrors Mathlib's `ZMod.LFunction`
definition and avoids any branch-law manipulation for complex powers. -/
noncomputable def estermannHurwitzFiniteSum
    (a q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-s) *
    ∑ j : ZMod q,
      ((q : ℂ) ^ (-s) *
          ∑ k : ZMod q,
            estermannResiduePhase a j k *
              HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) *
        HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s

/-- Unfolding the two congruence L-functions gives the finite double
Hurwitz-zeta formula definitionally. -/
theorem estermannHurwitzContinuation_eq_finiteSum
    (a q : ℕ) [NeZero q] (s : ℂ) :
    estermannHurwitzContinuation a q s =
      estermannHurwitzFiniteSum a q s := by
  rfl

/-- On natural residue classes, the modular phase is the explicit additive
phase used in the Dirichlet-series definition. -/
theorem estermannResiduePhase_natCast
    (a q m n : ℕ) [NeZero q] :
    estermannResiduePhase a (m : ZMod q) (n : ZMod q) =
      estermannAdditivePhase a q (m * n) := by
  rw [estermannAdditivePhase_eq_stdAddChar]
  unfold estermannResiduePhase
  congr 2
  push_cast
  ring

/-- The inner congruence L-series term is the expected additive twist of the
ordinary zeta-series term. -/
theorem term_residuePhase_eq
    (a q m n : ℕ) [NeZero q] (s : ℂ) :
    LSeries.term
        (fun r : ℕ =>
          estermannResiduePhase a (m : ZMod q) (r : ZMod q)) s n =
      estermannAdditivePhase a q (m * n) *
        LSeries.term (1 : ℕ → ℂ) s n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [estermannResiduePhase_natCast]
    simp [div_eq_mul_inv]

/-- The outer term of the nested continuation is the product-indexed inner
Estermann sum. -/
theorem outer_term_eq_inner_tsum
    (a q m : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    LSeries.term
        (fun r : ℕ =>
          ZMod.LFunction
            (fun k : ZMod q => estermannResiduePhase a (r : ZMod q) k) s)
        s m =
      ∑' n : ℕ, estermannDoubleTerm a q s (m, n) := by
  by_cases hm : m = 0
  · subst m
    simp [estermannDoubleTerm]
  · rw [LSeries.term_of_ne_zero hm]
    rw [ZMod.LFunction_eq_LSeries _ hs]
    unfold LSeries
    rw [← tsum_div_const]
    apply tsum_congr
    intro n
    rw [term_residuePhase_eq]
    unfold estermannDoubleTerm
    rw [LSeries.term_of_ne_zero hm]
    simp only [Pi.one_apply, one_div]
    ring

/-- The genuine finite Hurwitz continuation agrees with the classical
Estermann Dirichlet series throughout its half-plane of absolute convergence.
-/
theorem estermannHurwitzContinuation_eq_dirichletSeries
    (a q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    estermannHurwitzContinuation a q s =
      estermannDirichletSeries a q s := by
  unfold estermannHurwitzContinuation
  rw [ZMod.LFunction_eq_LSeries _ hs]
  unfold LSeries
  rw [estermannDirichletSeries_eq_tsum_prod a q hs]
  rw [(estermannDoubleTerm_summable a q hs).tsum_prod]
  apply tsum_congr
  intro m
  exact outer_term_eq_inner_tsum a q m hs

/-- The finite Hurwitz continuation is holomorphic away from its possible
pole at `s = 1`. -/
theorem differentiableAt_estermannHurwitzContinuation
    (a q : ℕ) [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (estermannHurwitzContinuation a q) s := by
  rw [show estermannHurwitzContinuation a q =
      estermannHurwitzFiniteSum a q from rfl]
  unfold estermannHurwitzFiniteSum
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

/-- Consequently, the continuation is holomorphic on `ℂ \ {1}`. -/
theorem differentiableOn_estermannHurwitzContinuation_off_one
    (a q : ℕ) [NeZero q] :
    DifferentiableOn ℂ (estermannHurwitzContinuation a q) ({1}ᶜ : Set ℂ) := by
  intro s hs
  exact (differentiableAt_estermannHurwitzContinuation a q
    (by simpa using hs)).differentiableWithinAt

/-- The leading coefficient after removing the possible double pole at one. -/
noncomputable def estermannDoublePoleCoefficient
    (a q : ℕ) [NeZero q] : ℂ :=
  (q : ℂ) ^ (-(1 : ℂ)) *
    ∑ j : ZMod q,
      (q : ℂ) ^ (-(1 : ℂ)) *
        ∑ k : ZMod q, estermannResiduePhase a j k

/-- The only possible singularity of the finite Hurwitz continuation is a
pole of order at most two at `s = 1`.  This is stated by exhibiting the
punctured limit after multiplication by `(s - 1)^2`. -/
theorem estermannHurwitzContinuation_doublePole_limit
    (a q : ℕ) [NeZero q] :
    Tendsto
      (fun s : ℂ => (s - 1) ^ 2 * estermannHurwitzContinuation a q s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (estermannDoublePoleCoefficient a q)) := by
  let regularized : ℂ → ℂ := fun s =>
    (q : ℂ) ^ (-s) *
      ∑ j : ZMod q,
        ((q : ℂ) ^ (-s) *
            ∑ k : ZMod q,
              estermannResiduePhase a j k *
                ((s - 1) * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s)) *
          ((s - 1) * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s)
  have heq : (fun s : ℂ =>
      (s - 1) ^ 2 * estermannHurwitzContinuation a q s) = regularized := by
    funext s
    unfold regularized estermannHurwitzContinuation ZMod.LFunction
    simp only [Finset.mul_sum, Finset.sum_mul]
    ring_nf
  rw [heq]
  have hq : Tendsto (fun s : ℂ => (q : ℂ) ^ (-s))
      (𝓝[≠] (1 : ℂ)) (𝓝 ((q : ℂ) ^ (-(1 : ℂ)))) := by
    exact (by fun_prop : ContinuousAt (fun s : ℂ => (q : ℂ) ^ (-s)) 1).tendsto.mono_left
      nhdsWithin_le_nhds
  have hsum : Tendsto
      (fun s : ℂ =>
        ∑ j : ZMod q,
          ((q : ℂ) ^ (-s) *
              ∑ k : ZMod q,
                estermannResiduePhase a j k *
                  ((s - 1) * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s)) *
            ((s - 1) * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s))
      (𝓝[≠] (1 : ℂ))
      (𝓝 (∑ j : ZMod q,
        (q : ℂ) ^ (-(1 : ℂ)) *
          ∑ k : ZMod q, estermannResiduePhase a j k)) := by
    apply tendsto_finsetSum
    intro j _
    have hinner : Tendsto
        (fun s : ℂ =>
          ∑ k : ZMod q,
            estermannResiduePhase a j k *
              ((s - 1) * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s))
        (𝓝[≠] (1 : ℂ))
        (𝓝 (∑ k : ZMod q, estermannResiduePhase a j k)) := by
      apply tendsto_finsetSum
      intro k _
      simpa using
        (tendsto_const_nhds.mul
          (HurwitzZeta.hurwitzZeta_residue_one (ZMod.toAddCircle k)))
    simpa using
      ((hq.mul hinner).mul
        (HurwitzZeta.hurwitzZeta_residue_one (ZMod.toAddCircle j)))
  simpa [regularized, estermannDoublePoleCoefficient] using hq.mul hsum

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
