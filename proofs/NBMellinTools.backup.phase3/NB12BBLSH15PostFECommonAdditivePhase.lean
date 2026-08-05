/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEGlobalBoundaryTransfer

/-!
# NB12zzzk: common additive-character normalization of the post-FE frontier

The global boundary-transfer expression has four ordered phase populations
and one retained missing-residue trace.  This file places all of them in the
same additive-character language.

For an actual pair `(u,q),(v,q')`, the conjugated left phase times the right
phase is a single character modulo `q*q'`, with signed numerator

`-epsilon_left * u*r*q' + epsilon_right * v*r*q`.

The definition is zero-extended away from coprime rows, so the identity is
valid on the literal post-functional-equation support without deleting
invalid Laurent rows.  The missing-residue cross mode is likewise the
imaginary part of one zero-extended doubled character modulo `q`.

Thus the whole correction-coupled frontier is now an explicit finite signed
additive-character system.  No absolute value or decay estimate is used.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## One phase lifted to a common modulus -/

/-- Sign action on a residue class. -/
def h15PostFESignedCommonResidue
    (sign : BettinChandeeUnitSign) {M : ℕ} (x : ZMod M) : ZMod M :=
  match sign with
  | .positive => x
  | .negative => -x

/-- A signed phase of denominator `q` embedded into the common modulus
`q*q'`. -/
theorem h15DirectAdditiveReducedUnitPhase_eq_leftCommonModulus
    (sign : BettinChandeeUnitSign) (r u q q' : ℕ)
    (hq : 0 < q) (hq' : 0 < q') (huq : Nat.Coprime u q) :
    letI : NeZero q := ⟨hq.ne'⟩
    letI : NeZero (q * q') := ⟨Nat.mul_ne_zero hq.ne' hq'.ne'⟩
    h15DirectAdditiveReducedUnitPhase sign r u q =
      ZMod.stdAddChar
        (h15PostFESignedCommonResidue sign
          (((u * r * q' : ℕ) : ZMod (q * q')))) := by
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero (q * q') := ⟨Nat.mul_ne_zero hq.ne' hq'.ne'⟩
  have hpos :
      h15DirectAdditiveReducedUnitPhase .positive r u q =
        ZMod.stdAddChar (((u * r * q' : ℕ) : ZMod (q * q'))) := by
    rw [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ huq]
    unfold h15DirectAdditiveUnitPhase
    simp only [hq.ne', dite_false]
    rw [show (u : ZMod q) * (r : ZMod q) =
        ((u * r : ℕ) : ZMod q) by push_cast; rfl]
    rw [show ZMod.stdAddChar ((u * r : ℕ) : ZMod q) =
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * ((u * r : ℕ) : ℂ) /
            (q : ℂ)) by
      simpa using ZMod.stdAddChar_coe (N := q) ((u * r : ℕ) : ℤ)]
    rw [show ZMod.stdAddChar ((u * r * q' : ℕ) : ZMod (q * q')) =
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * ((u * r * q' : ℕ) : ℂ) /
            ((q * q' : ℕ) : ℂ)) by
      simpa using ZMod.stdAddChar_coe (N := q * q')
        ((u * r * q' : ℕ) : ℤ)]
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hq'C : (q' : ℂ) ≠ 0 := by exact_mod_cast hq'.ne'
    congr 1
    push_cast
    field_simp [hqC, hq'C]
  cases sign with
  | positive => exact hpos
  | negative =>
      rw [h15DirectAdditiveReducedUnitPhase_negative_eq_conj_positive
        r u q hq huq]
      change conj (h15DirectAdditiveReducedUnitPhase .positive r u q) =
        ZMod.stdAddChar (-(((u * r * q' : ℕ) : ZMod (q * q'))))
      rw [AddChar.map_neg_eq_conj]
      exact congrArg conj hpos

/-- A signed phase of denominator `q'` embedded into the same ordered common
modulus `q*q'`. -/
theorem h15DirectAdditiveReducedUnitPhase_eq_rightCommonModulus
    (sign : BettinChandeeUnitSign) (r v q q' : ℕ)
    (hq : 0 < q) (hq' : 0 < q') (hvq' : Nat.Coprime v q') :
    letI : NeZero q' := ⟨hq'.ne'⟩
    letI : NeZero (q * q') := ⟨Nat.mul_ne_zero hq.ne' hq'.ne'⟩
    h15DirectAdditiveReducedUnitPhase sign r v q' =
      ZMod.stdAddChar
        (h15PostFESignedCommonResidue sign
          (((v * r * q : ℕ) : ZMod (q * q')))) := by
  letI : NeZero q' := ⟨hq'.ne'⟩
  letI : NeZero (q * q') := ⟨Nat.mul_ne_zero hq.ne' hq'.ne'⟩
  have hpos :
      h15DirectAdditiveReducedUnitPhase .positive r v q' =
        ZMod.stdAddChar (((v * r * q : ℕ) : ZMod (q * q'))) := by
    rw [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ hvq']
    unfold h15DirectAdditiveUnitPhase
    simp only [hq'.ne', dite_false]
    rw [show (v : ZMod q') * (r : ZMod q') =
        ((v * r : ℕ) : ZMod q') by push_cast; rfl]
    rw [show ZMod.stdAddChar ((v * r : ℕ) : ZMod q') =
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * ((v * r : ℕ) : ℂ) /
            (q' : ℂ)) by
      simpa using ZMod.stdAddChar_coe (N := q') ((v * r : ℕ) : ℤ)]
    rw [show ZMod.stdAddChar ((v * r * q : ℕ) : ZMod (q * q')) =
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * ((v * r * q : ℕ) : ℂ) /
            ((q * q' : ℕ) : ℂ)) by
      simpa using ZMod.stdAddChar_coe (N := q * q')
        ((v * r * q : ℕ) : ℤ)]
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hq'C : (q' : ℂ) ≠ 0 := by exact_mod_cast hq'.ne'
    congr 1
    push_cast
    field_simp [hqC, hq'C]
  cases sign with
  | positive => exact hpos
  | negative =>
      rw [h15DirectAdditiveReducedUnitPhase_negative_eq_conj_positive
        r v q' hq' hvq']
      change conj (h15DirectAdditiveReducedUnitPhase .positive r v q') =
        ZMod.stdAddChar (-(((v * r * q : ℕ) : ZMod (q * q'))))
      rw [AddChar.map_neg_eq_conj]
      exact congrArg conj hpos

/-! ## One common character for an ordered phase pair -/

/-- Zero-extended common-denominator phase of an ordered signed pair. -/
noncomputable def h15PostFECommonPairAdditivePhase
    (left right : BettinChandeeUnitSign)
    (r u q v q' : ℕ) : ℂ :=
  if hM : q * q' = 0 then 0
  else
    letI : NeZero (q * q') := ⟨hM⟩
    if Nat.Coprime u q ∧ Nat.Coprime v q' then
      ZMod.stdAddChar
        (-h15PostFESignedCommonResidue left
            (((u * r * q' : ℕ) : ZMod (q * q'))) +
          h15PostFESignedCommonResidue right
            (((v * r * q : ℕ) : ZMod (q * q'))))
    else 0

/-- The product of two literal reduced phases is exactly one zero-extended
character on the common modulus. -/
theorem conj_reducedUnitPhase_mul_reducedUnitPhase_eq_commonPairPhase
    (left right : BettinChandeeUnitSign)
    (r u q v q' : ℕ) (hq : 0 < q) (hq' : 0 < q') :
    conj (h15DirectAdditiveReducedUnitPhase left r u q) *
        h15DirectAdditiveReducedUnitPhase right r v q' =
      h15PostFECommonPairAdditivePhase left right r u q v q' := by
  by_cases huq : Nat.Coprime u q
  · by_cases hvq' : Nat.Coprime v q'
    · letI : NeZero q := ⟨hq.ne'⟩
      letI : NeZero q' := ⟨hq'.ne'⟩
      letI : NeZero (q * q') := ⟨Nat.mul_ne_zero hq.ne' hq'.ne'⟩
      rw [h15DirectAdditiveReducedUnitPhase_eq_leftCommonModulus
          left r u q q' hq hq' huq,
        h15DirectAdditiveReducedUnitPhase_eq_rightCommonModulus
          right r v q q' hq hq' hvq']
      unfold h15PostFECommonPairAdditivePhase
      simp only [Nat.mul_ne_zero hq.ne' hq'.ne', dite_false]
      rw [if_pos ⟨huq, hvq'⟩]
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    · rw [h15DirectAdditiveReducedUnitPhase_of_not_coprime
          right r v q' hvq']
      unfold h15PostFECommonPairAdditivePhase
      simp [Nat.mul_ne_zero hq.ne' hq'.ne', hvq']
  · rw [h15DirectAdditiveReducedUnitPhase_of_not_coprime
        left r u q huq]
    unfold h15PostFECommonPairAdditivePhase
    simp [Nat.mul_ne_zero hq.ne' hq'.ne', huq]

/-! ## Archimedean weights and four populations -/

/-- Scalar multiplying one direct phase in the paired kernel. -/
noncomputable def h15PostFEOrientationArchimedeanFactor
    (sign : BettinChandeeUnitSign) (t : ℝ) : ℂ :=
  match sign with
  | .positive => 1
  | .negative =>
      Complex.cos ((Real.pi : ℂ) * bblsEstermannThreeHalfPoint t)

theorem h15PostFEKernelOrientationComponent_eq_factor_mul_phase
    (sign : BettinChandeeUnitSign) (t : ℝ) (r : ℕ) (z : ℕ × ℕ) :
    h15PostFEKernelOrientationComponent sign t r z =
      h15PostFEOrientationArchimedeanFactor sign t *
        h15DirectAdditiveReducedUnitPhase sign r z.1 z.2 := by
  cases sign <;>
    simp [h15PostFEKernelOrientationComponent,
      h15PostFEOrientationArchimedeanFactor]

/-- One residue-pair phase component as an Archimedean scalar times the
single common-denominator character. -/
theorem h15PostFEResiduePairPhaseComponent_eq_factor_mul_commonPhase
    (left right : BettinChandeeUnitSign) (t : ℝ)
    (r u q v q' : ℕ) (hq : 0 < q) (hq' : 0 < q') :
    h15PostFEResiduePairPhaseComponent left right t r ((u, q), (v, q')) =
      conj (h15PostFEOrientationArchimedeanFactor left t) *
        h15PostFEOrientationArchimedeanFactor right t *
        h15PostFECommonPairAdditivePhase left right r u q v q' := by
  unfold h15PostFEResiduePairPhaseComponent
  rw [h15PostFEKernelOrientationComponent_eq_factor_mul_phase,
    h15PostFEKernelOrientationComponent_eq_factor_mul_phase]
  simp only [map_mul]
  rw [show
      conj (h15PostFEOrientationArchimedeanFactor left t) *
          conj (h15DirectAdditiveReducedUnitPhase left r u q) *
          (h15PostFEOrientationArchimedeanFactor right t *
            h15DirectAdditiveReducedUnitPhase right r v q') =
        conj (h15PostFEOrientationArchimedeanFactor left t) *
          h15PostFEOrientationArchimedeanFactor right t *
          (conj (h15DirectAdditiveReducedUnitPhase left r u q) *
            h15DirectAdditiveReducedUnitPhase right r v q') by ring]
  rw [conj_reducedUnitPhase_mul_reducedUnitPhase_eq_commonPairPhase
    left right r u q v q' hq hq']

/-- One ordered population written entirely in the common additive-character
normalization. -/
noncomputable def h15PostFEOrderedPairCommonAdditivePopulation
    (left right : BettinChandeeUnitSign)
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ κ ∈ h15PostFEOrderedPairResidueSupport n g U Q,
    (h15PostFEOrderedPairCollectedScalar n g U Q r t κ *
      (conj (h15PostFEOrientationArchimedeanFactor left t) *
        h15PostFEOrientationArchimedeanFactor right t *
        h15PostFECommonPairAdditivePhase left right r
          κ.1.1 κ.1.2 κ.2.1 κ.2.2)).re

/-- Exact common-character form of each of the four ordered populations. -/
theorem h15PostFEOrderedPairPhasePopulation_eq_commonAdditive
    (left right : BettinChandeeUnitSign)
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15PostFEOrderedPairPhasePopulation left right n g U Q r t =
      h15PostFEOrderedPairCommonAdditivePopulation
        left right n g U Q r t := by
  unfold h15PostFEOrderedPairPhasePopulation
    h15PostFEOrderedPairCommonAdditivePopulation
  apply Finset.sum_congr rfl
  intro κ hκ
  have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hκ
  have hlt1 := h15PostFEResidueKey_fst_lt_snd hQ hactual.1
  have hlt2 := h15PostFEResidueKey_fst_lt_snd hQ hactual.2
  have hq1 : 0 < κ.1.2 := Nat.zero_lt_of_lt hlt1
  have hq2 : 0 < κ.2.2 := Nat.zero_lt_of_lt hlt2
  rw [h15PostFEResiduePairPhaseComponent_eq_factor_mul_commonPhase
    left right t r κ.1.1 κ.1.2 κ.2.1 κ.2.2 hq1 hq2]

/-! ## Missing-residue trace in the same language -/

/-- Zero-extended doubled character underlying the missing-residue cross
mode. -/
noncomputable def h15PostFEReducedDoubledAdditivePhase
    (r u q : ℕ) : ℂ :=
  if hq : q = 0 then 0
  else
    letI : NeZero q := ⟨hq⟩
    if Nat.Coprime u q then
      ZMod.stdAddChar (((2 * u * r : ℕ) : ZMod q))
    else 0

/-- The doubled phase used by the cross mode is exactly its explicit
zero-extended additive character. -/
theorem h15DoubledDirectAdditivePhase_eq_reducedDoubledAdditivePhase
    (r u q : ℕ) :
    h15DoubledDirectAdditivePhase r u q =
      h15PostFEReducedDoubledAdditivePhase r u q := by
  by_cases hq : q = 0
  · subst q
    unfold h15DoubledDirectAdditivePhase
      h15PostFEReducedDoubledAdditivePhase
    simp [h15DirectAdditiveReducedUnitPhase,
      h15DirectAdditiveUnitPhase]
  · letI : NeZero q := ⟨hq⟩
    by_cases huq : Nat.Coprime u q
    · unfold h15DoubledDirectAdditivePhase
        h15PostFEReducedDoubledAdditivePhase
      rw [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ huq]
      simp only [hq, dite_false]
      rw [if_pos huq]
      unfold h15DirectAdditiveUnitPhase
      simp only [hq, dite_false]
      rw [pow_two, ← AddChar.map_add_eq_mul]
      congr 2
      push_cast
      ring
    · unfold h15DoubledDirectAdditivePhase
        h15PostFEReducedDoubledAdditivePhase
      rw [h15DirectAdditiveReducedUnitPhase_of_not_coprime _ _ _ _ huq]
      simp [hq, huq]

/-- Missing-residue trace in explicit doubled-character form. -/
noncomputable def h15PostFEMissingResidueAdditiveTrace
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ q ∈ h15PostFEResidueModulusSupport n g U Q,
    h15PostFEResidueFiberMeanCoefficient n g U Q r t q *
      ∑ a ∈ h15PostFEMissingResidues n g U Q q,
        (h15PostFEReducedDoubledAdditivePhase r a q).im

theorem h15PostFEMissingResidueTrace_eq_additiveTrace
    (n g U Q r : ℕ) (t : ℝ) :
    h15PostFEMissingResidueTrace n g U Q r t =
      h15PostFEMissingResidueAdditiveTrace n g U Q r t := by
  unfold h15PostFEMissingResidueTrace h15PostFEMissingResidueAdditiveTrace
  apply Finset.sum_congr rfl
  intro q _hq
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  rw [h15PairedDirectCrossMode_eq_doubledPhase_im,
    h15DoubledDirectAdditivePhase_eq_reducedDoubledAdditivePhase]

/-! ## Fully normalized global frontier -/

/-- Complete boundary-transfer expression after common additive-character
normalization. -/
noncomputable def h15PostFECommonAdditiveBoundaryTransfer
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  h15PostFEMissingResidueAdditiveTrace n g U Q r t +
    4 *
      (h15PostFEOrderedPairCommonAdditivePopulation
          .positive .positive n g U Q r t +
        h15PostFEOrderedPairCommonAdditivePopulation
          .positive .negative n g U Q r t +
        h15PostFEOrderedPairCommonAdditivePopulation
          .negative .positive n g U Q r t +
        h15PostFEOrderedPairCommonAdditivePopulation
          .negative .negative n g U Q r t) /
      (2 * h15PairedHyperbolicCoefficient t)

theorem h15PostFEGlobalSignedBoundaryTransfer_eq_commonAdditive
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15PostFEGlobalSignedBoundaryTransfer n g U Q r t =
      h15PostFECommonAdditiveBoundaryTransfer n g U Q r t := by
  unfold h15PostFEGlobalSignedBoundaryTransfer
    h15PostFECommonAdditiveBoundaryTransfer
  rw [h15PostFEMissingResidueTrace_eq_additiveTrace,
    h15PostFEOrderedPairPhasePopulation_eq_commonAdditive
      .positive .positive n g U Q r t hQ,
    h15PostFEOrderedPairPhasePopulation_eq_commonAdditive
      .positive .negative n g U Q r t hQ,
    h15PostFEOrderedPairPhasePopulation_eq_commonAdditive
      .negative .positive n g U Q r t hQ,
    h15PostFEOrderedPairPhasePopulation_eq_commonAdditive
      .negative .negative n g U Q r t hQ]

/-- The centered post-FE defect in its final common additive-character
normalization. -/
theorem h15PostFECenteredLiftDefect_eq_meanZero_sub_commonAdditiveTransfer
    (n g U Q r : ℕ) (t : ℝ)
    (hQ : 0 < Q) (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PostFECenteredLiftDefect n g U Q r t =
      h15PostFEResidueMeanZeroVariation n g U Q r t -
        h15PostFECommonAdditiveBoundaryTransfer n g U Q r t := by
  rw [h15PostFECenteredLiftDefect_eq_meanZero_sub_globalBoundaryTransfer
      n g U Q r t hQ hS,
    h15PostFEGlobalSignedBoundaryTransfer_eq_commonAdditive
      n g U Q r t hQ]

end NBMellinTools.NB12
