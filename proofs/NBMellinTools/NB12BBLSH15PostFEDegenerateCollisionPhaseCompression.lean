/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEDegenerateEstimateMatchingAudit

/-!
# NB12zzzaY: phase compression on degenerate collision shells

Every atom in the degenerate quotient ledger is already supported on an
equal- or opposite-frequency collision.  This file uses that support instead
of applying another absolute estimate.

At an equal collision the pair character is the missing character; at an
opposite collision it is its complex conjugate.  Consequently the mixed
imaginary--real product splits exactly into:

* a frequency-independent diagonal term, with sign determined by the
  collision orientation; and
* an explicit doubled-frequency character.

The result is finite character algebra.  It does not estimate the surviving
second harmonic and therefore does not prove H15 or RH.
-/

open AddChar Complex ZMod
open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB12

/-! ## Generic equal/opposite character compression -/

theorem h15PostFEFrequencyCollides_character_eq_or_conj
    {M : ℕ} [NeZero M] {x y : ZMod M}
    (hxy : h15PostFEFrequencyCollides x y) (r : ℕ) :
    ZMod.stdAddChar ((r : ZMod M) * y) =
        ZMod.stdAddChar ((r : ZMod M) * x) ∨
      ZMod.stdAddChar ((r : ZMod M) * y) =
        conj (ZMod.stdAddChar ((r : ZMod M) * x)) := by
  rcases hxy with hxy | hxy
  · exact Or.inl (congrArg (fun z : ZMod M =>
      ZMod.stdAddChar ((r : ZMod M) * z)) hxy.symm)
  · right
    have hy : y = -x := by
      calc
        y = 0 + y := by simp
        _ = (-x + x) + y := by rw [neg_add_cancel]
        _ = -x + (x + y) := by ac_rfl
        _ = -x := by rw [hxy, add_zero]
    rw [hy, mul_neg, AddChar.map_neg_eq_conj]

theorem im_mul_re_mul_eq_secondHarmonic_sub_diagonal
    (c z : ℂ) (hz : Complex.normSq z = 1) :
    z.im * (c * z).re = ((c * z ^ 2).im - c.im) / 2 := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply,
    pow_two] at hz ⊢
  linear_combination -(c.im / 2) * hz

theorem im_mul_re_mul_conj_eq_secondHarmonic_add_diagonal
    (c z : ℂ) (hz : Complex.normSq z = 1) :
    z.im * (c * conj z).re =
      ((conj c * z ^ 2).im + c.im) / 2 := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply,
    conj_re, conj_im, pow_two] at hz ⊢
  linear_combination (c.im / 2) * hz

noncomputable def h15PostFECollidingPhaseDiagonal
    {M : ℕ} [NeZero M] (x y : ZMod M) (c : ℂ) : ℝ :=
  if x = y then -c.im / 2 else c.im / 2

noncomputable def h15PostFECollidingPhaseSecondHarmonic
    {M : ℕ} [NeZero M] (x y : ZMod M) (c z : ℂ) : ℝ :=
  if x = y then (c * z ^ 2).im / 2
  else (conj c * z ^ 2).im / 2

/-- Exact diagonal-plus-second-harmonic formula on an equal/opposite
collision. -/
theorem h15PostFECollidingCharacterProduct_eq_diagonal_add_secondHarmonic
    {M : ℕ} [NeZero M] {x y : ZMod M}
    (hxy : h15PostFEFrequencyCollides x y) (c : ℂ) (r : ℕ) :
    (ZMod.stdAddChar ((r : ZMod M) * x)).im *
        (c * ZMod.stdAddChar ((r : ZMod M) * y)).re =
      h15PostFECollidingPhaseDiagonal x y c +
        h15PostFECollidingPhaseSecondHarmonic x y c
          (ZMod.stdAddChar ((r : ZMod M) * x)) := by
  have hz : Complex.normSq
      (ZMod.stdAddChar ((r : ZMod M) * x)) = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.normSq_coe _
  by_cases heq : x = y
  · subst y
    unfold h15PostFECollidingPhaseDiagonal
      h15PostFECollidingPhaseSecondHarmonic
    rw [if_pos rfl, if_pos rfl]
    rw [im_mul_re_mul_eq_secondHarmonic_sub_diagonal _ _ hz]
    ring
  · have hopp : x + y = 0 := hxy.resolve_left heq
    have hy : y = -x := by
      calc
        y = 0 + y := by simp
        _ = (-x + x) + y := by rw [neg_add_cancel]
        _ = -x + (x + y) := by ac_rfl
        _ = -x := by rw [hopp, add_zero]
    unfold h15PostFECollidingPhaseDiagonal
      h15PostFECollidingPhaseSecondHarmonic
    rw [if_neg heq, if_neg heq]
    rw [hy, mul_neg, AddChar.map_neg_eq_conj]
    rw [im_mul_re_mul_conj_eq_secondHarmonic_add_diagonal _ _ hz]
    ring

/-! ## Genuine H15 collision support -/

theorem h15PostFEDegenerateCrossModulusCollisionSupport_collides
    {M n g U Q : ℕ} [NeZero M]
    {p : H15PostFEMissingPairAtomIndex}
    (hp : p ∈ h15PostFEDegenerateCrossModulusCollisionSupport
      M n g U Q) :
    h15PostFEFrequencyCollides
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1) := by
  unfold h15PostFEDegenerateCrossModulusCollisionSupport at hp
  exact (Finset.mem_filter.mp
    (Finset.mem_filter.mp
      (Finset.mem_filter.mp
        (Finset.mem_filter.mp hp).1).1).1).2

/-- On the genuine actual-superperiod support, the literal pair phase is
either the literal missing phase or its conjugate. -/
theorem h15PostFEDegenerateLiteralPairPhase_eq_or_conj_missingPhase
    {n g U Q : ℕ}
    [NeZero (h15PostFEActualCommonSuperperiod n g U Q)]
    (hQ : 0 < Q)
    {p : H15PostFEMissingPairAtomIndex}
    (hp : p ∈ h15PostFEDegenerateCrossModulusCollisionSupport
      (h15PostFEActualCommonSuperperiod n g U Q) n g U Q)
    (r : ℕ) :
    h15PostFECommonPairAdditivePhase p.2.2.1 p.2.2.2 r
        p.2.1.1.1 p.2.1.1.2 p.2.1.2.1 p.2.1.2.2 =
        h15PostFEReducedDoubledAdditivePhase r p.1.2 p.1.1 ∨
      h15PostFECommonPairAdditivePhase p.2.2.1 p.2.2.2 r
          p.2.1.1.1 p.2.1.1.2 p.2.1.2.1 p.2.1.2.2 =
        conj (h15PostFEReducedDoubledAdditivePhase r p.1.2 p.1.1) := by
  have hbase := h15PostFEDegenerateCrossModulusCollisionSupport_mem_base hp
  have hpair := (Finset.mem_product.mp hbase.2).1
  have hm := h15PostFEActualMissingPhase_eq_commonSuperperiod hQ hbase.1 r
  have hk := h15PostFEActualPairPhase_eq_commonSuperperiod hQ hpair
    p.2.2.1 p.2.2.2 r
  rw [hm, hk]
  exact h15PostFEFrequencyCollides_character_eq_or_conj
    (h15PostFEDegenerateCrossModulusCollisionSupport_collides hp) r

end NBMellinTools.NB12
