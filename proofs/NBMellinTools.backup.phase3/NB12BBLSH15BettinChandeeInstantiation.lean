/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15BettinChandeeLedger

/-!
# NB12zb: exact Bettin--Chandee Theorem 1 interface for H15

This file records the precise published analytic input which can be applied
to the finite middle-frequency H15 blocks.  The source is Theorem 1 of

S. Bettin and V. Chandee, *Trilinear forms with Kloosterman fractions*,
February 2015, arXiv:1502.00769.

The paper studies arbitrary separated coefficients on dyadic intervals and
the phase `e(theta * a * mbar / n)`, where `mbar` is the inverse of `m`
modulo `n`.  H15 needs only the specializations `theta = 1` and `theta = -1`.
We therefore state the exact signed-unit corollary, with its genuine
epsilon-dependent constant, rather than silently replacing the published
Vinogradov notation by a uniform constant.

The local convention here is `[X,2X)`.  It embeds into the paper's
`[(2X)/2,2X]`, so every occurrence of the paper's endpoint parameters
`A,M,N` is replaced respectively by `2R,2U,2Q` below.

This module does **not** postulate Theorem 1 as an axiom and does not claim
the H15 middle-window estimate.  `BettinChandeeSignedUnitTheoremOne` is the
explicit literature-input structure which a formal proof of the published
theorem must inhabit.  The arithmetic phase identification itself is proved
exactly and unconditionally.
-/

open scoped BigOperators Topology LSeries.notation
open Complex

namespace NBMellinTools.NB12

/-! ## The exact signed Kloosterman fraction -/

/-- The two unit values of the paper's real parameter `theta` needed by the
two Estermann orientations in H15. -/
inductive BettinChandeeUnitSign
  | positive
  | negative
  deriving DecidableEq

/-- The signed inverse residue occurring in the Kloosterman fraction.

Writing the phase in `ZMod q` avoids any ambiguity in the choice of an
integer representative of the inverse.  The coprimality restriction is
implemented by setting the phase to zero off the reduced pairs, exactly as
one does when extending the paper's starred sum to a rectangular box. -/
noncomputable def bettinChandeeSignedUnitPhaseAux
    (sign : BettinChandeeUnitSign) (r u q : ℕ) [NeZero q] : ℂ :=
  if h : Nat.Coprime u q then
    let inverse : ZMod q :=
      ((ZMod.unitOfCoprime u h)⁻¹ : (ZMod q)ˣ).val
    ZMod.stdAddChar
      ((match sign with
        | .positive => inverse
        | .negative => -inverse) * (r : ZMod q))
  else 0

/-- Total version of the signed phase.  The zero modulus never occurs in a
positive dyadic Bettin--Chandee block, but defining it to be zero makes the
finite form convenient to use without carrying typeclass arguments. -/
noncomputable def bettinChandeeSignedUnitPhase
    (sign : BettinChandeeUnitSign) (r u q : ℕ) : ℂ :=
  if hq : q = 0 then 0
  else @bettinChandeeSignedUnitPhaseAux sign r u q ⟨hq⟩

@[simp] theorem bettinChandeeSignedUnitPhase_of_not_coprime
    (sign : BettinChandeeUnitSign) (r u q : ℕ)
    (h : ¬ Nat.Coprime u q) :
    bettinChandeeSignedUnitPhase sign r u q = 0 := by
  by_cases hq : q = 0
  · simp [bettinChandeeSignedUnitPhase, hq]
  · simp [bettinChandeeSignedUnitPhase,
      bettinChandeeSignedUnitPhaseAux, hq, h]

/-- For a reduced positive H15 row, the positive Bettin--Chandee phase is
exactly the additive character in the positive inverse Estermann series. -/
theorem bettinChandeeSignedUnitPhase_positive_eq_h15
    (r u q : ℕ) [NeZero q] (huq : Nat.Coprime u q) :
    bettinChandeeSignedUnitPhase .positive r u q =
      bblsAdditiveCharacter r
        ((bblsEstermannInverseNumerator u q huq : ℝ) / (q : ℝ)) := by
  rw [bblsAdditiveCharacter_rat_eq_stdAddChar]
  have hq : q ≠ 0 := NeZero.ne q
  rw [bettinChandeeSignedUnitPhase, dif_neg hq]
  rw [bettinChandeeSignedUnitPhaseAux, dif_pos huq]
  simp [
    bblsEstermannInverseNumerator,
    bblsEstermannInverseResidue, mul_comm]

/-- The negative specialization is exactly the character in the negative
inverse Estermann series.  This is the second of the two trilinear forms to
which Theorem 1 must be applied. -/
theorem bettinChandeeSignedUnitPhase_negative_eq_h15
    (r u q : ℕ) [NeZero q] (huq : Nat.Coprime u q) :
    bettinChandeeSignedUnitPhase .negative r u q =
      bblsAdditiveCharacter r
        ((bblsEstermannNegativeInverseNumerator u q huq : ℝ) / (q : ℝ)) := by
  rw [bblsAdditiveCharacter_rat_eq_stdAddChar]
  have hq : q ≠ 0 := NeZero.ne q
  rw [bettinChandeeSignedUnitPhase, dif_neg hq]
  rw [bettinChandeeSignedUnitPhaseAux, dif_pos huq]
  simp [
    bblsEstermannNegativeInverseNumerator,
    bblsEstermannInverseResidue, mul_comm]

/-! ## The H15 double-inversion stop test -/

/-- The natural representative used when building an H15 Laurent row really
is the inverse of the primitive numerator in `ZMod q`. -/
@[simp] theorem h15InverseResidueNumerator_cast
    (u q : ℕ) [NeZero q] (huq : Nat.Coprime u q) :
    (h15InverseResidueNumerator u q huq : ZMod q) =
      (((ZMod.unitOfCoprime u huq)⁻¹ : (ZMod q)ˣ).val) := by
  unfold h15InverseResidueNumerator
  exact ZMod.natCast_zmod_val _

/-- Applying the functional-equation inverse to the inverse numerator already
stored in an H15 Laurent row returns the original primitive numerator. -/
theorem bblsEstermannInverseResidue_h15InverseResidueNumerator
    (u q : ℕ) [NeZero q] (huq : Nat.Coprime u q) :
    bblsEstermannInverseResidue
        (h15InverseResidueNumerator u q huq)
        (h15InverseResidueNumerator_coprime u q huq) =
      (u : ZMod q) := by
  let U : (ZMod q)ˣ := ZMod.unitOfCoprime u huq
  have hunit :
      ZMod.unitOfCoprime (h15InverseResidueNumerator u q huq)
          (h15InverseResidueNumerator_coprime u q huq) = U⁻¹ := by
    apply Units.ext
    simp [U]
  unfold bblsEstermannInverseResidue
  rw [hunit, inv_inv]
  exact ZMod.coe_unitOfCoprime u huq

/-- Consequently the positive dual Estermann character of an H15 row is a
**direct additive fraction**, not a Kloosterman fraction. -/
theorem bblsAdditiveCharacter_h15_doubleInverse_eq_direct
    (r u q : ℕ) [NeZero q] (huq : Nat.Coprime u q) :
    bblsAdditiveCharacter r
        ((bblsEstermannInverseNumerator
            (h15InverseResidueNumerator u q huq) q
            (h15InverseResidueNumerator_coprime u q huq) : ℝ) /
          (q : ℝ)) =
      bblsAdditiveCharacter r ((u : ℝ) / (q : ℝ)) := by
  rw [bblsAdditiveCharacter_rat_eq_stdAddChar,
    bblsAdditiveCharacter_rat_eq_stdAddChar]
  simp [bblsEstermannInverseNumerator_cast,
    bblsEstermannInverseResidue_h15InverseResidueNumerator]

/-- The negative dual orientation similarly becomes the negative direct
additive fraction. -/
theorem bblsAdditiveCharacter_h15_doubleNegativeInverse_eq_direct
    (r u q : ℕ) [NeZero q] (huq : Nat.Coprime u q) :
    bblsAdditiveCharacter r
        ((bblsEstermannNegativeInverseNumerator
            (h15InverseResidueNumerator u q huq) q
            (h15InverseResidueNumerator_coprime u q huq) : ℝ) /
          (q : ℝ)) =
      ZMod.stdAddChar (-((u : ZMod q) * (r : ZMod q))) := by
  rw [bblsAdditiveCharacter_rat_eq_stdAddChar]
  simp [bblsEstermannNegativeInverseNumerator_cast,
    bblsEstermannInverseResidue_h15InverseResidueNumerator]

/-- Formal stop-test result: the direct positive H15 phase and the generic
Bettin--Chandee inverse phase are different expressions.  The paper's
Theorem 1 can only be used after an additional transformation which restores
an inverse residue; it cannot be applied merely by renaming the H15 primitive
variable. -/
def H15PostFunctionalEquationPhaseIsDirect : Prop :=
  ∀ (r u q : ℕ) [NeZero q] (huq : Nat.Coprime u q),
    bblsAdditiveCharacter r
        ((bblsEstermannInverseNumerator
            (h15InverseResidueNumerator u q huq) q
            (h15InverseResidueNumerator_coprime u q huq) : ℝ) /
          (q : ℝ)) =
      bblsAdditiveCharacter r ((u : ℝ) / (q : ℝ))

theorem h15PostFunctionalEquationPhaseIsDirect :
    H15PostFunctionalEquationPhaseIsDirect := by
  intro r u q _ huq
  exact bblsAdditiveCharacter_h15_doubleInverse_eq_direct r u q huq

/-- On an actual valid orientation-zero H15 index, the stored row numerator
is the inverse residue of the primitive variable `a` modulo `q`. -/
theorem h15LaurentRow_numerator_eq_inverse_of_orientation_zero
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i)
    (horientation : h15LaurentOrientation i = 0) :
    (h15LaurentRow i).numerator =
      h15InverseResidueNumerator (h15LaurentA i) (h15LaurentQ i)
        hvalid.2.2.2.2 := by
  unfold h15LaurentRow
  simp [horientation, hvalid.2.2.2.2.gcd_eq_one]

/-- The same statement for orientation one, where the primitive variables
are exchanged. -/
theorem h15LaurentRow_numerator_eq_inverse_of_orientation_one
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i)
    (horientation : h15LaurentOrientation i = 1) :
    (h15LaurentRow i).numerator =
      h15InverseResidueNumerator (h15LaurentQ i) (h15LaurentA i)
        hvalid.2.2.2.2.symm := by
  unfold h15LaurentRow
  have hne : h15LaurentOrientation i ≠ 0 := by omega
  simp [hne, hvalid.2.2.2.2.symm.gcd_eq_one]

/-- The double-inversion collapse on an actual valid orientation-zero H15
row. -/
theorem h15LaurentRow_positiveDualPhase_eq_direct_of_orientation_zero
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i)
    (horientation : h15LaurentOrientation i = 0) (r : ℕ) :
    let row := h15LaurentRow i
    letI : NeZero row.denominator := ⟨row.denominator_pos.ne'⟩
    bblsAdditiveCharacter r
        ((bblsEstermannInverseNumerator row.numerator row.denominator
            row.coprime : ℝ) / (row.denominator : ℝ)) =
      bblsAdditiveCharacter r
        ((h15LaurentA i : ℝ) / (h15LaurentQ i : ℝ)) := by
  dsimp only
  letI : NeZero (h15LaurentQ i) :=
    ⟨by simp [h15LaurentQ]⟩
  simpa [h15LaurentRow, horientation,
      hvalid.2.2.2.2.gcd_eq_one] using
    (bblsAdditiveCharacter_h15_doubleInverse_eq_direct
      r (h15LaurentA i) (h15LaurentQ i) hvalid.2.2.2.2)

/-- The double-inversion collapse on the exchanged orientation-one H15 row. -/
theorem h15LaurentRow_positiveDualPhase_eq_direct_of_orientation_one
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i)
    (horientation : h15LaurentOrientation i = 1) (r : ℕ) :
    let row := h15LaurentRow i
    letI : NeZero row.denominator := ⟨row.denominator_pos.ne'⟩
    bblsAdditiveCharacter r
        ((bblsEstermannInverseNumerator row.numerator row.denominator
            row.coprime : ℝ) / (row.denominator : ℝ)) =
      bblsAdditiveCharacter r
        ((h15LaurentQ i : ℝ) / (h15LaurentA i : ℝ)) := by
  dsimp only
  letI : NeZero (h15LaurentA i) :=
    ⟨by simp [h15LaurentA]⟩
  have hne : h15LaurentOrientation i ≠ 0 := by omega
  simpa [h15LaurentRow, hne,
      hvalid.2.2.2.2.symm.gcd_eq_one] using
    (bblsAdditiveCharacter_h15_doubleInverse_eq_direct
      r (h15LaurentQ i) (h15LaurentA i) hvalid.2.2.2.2.symm)

/-! ## Correct post-functional-equation model -/

/-- The actual signed phase after the H15 row inverse and the Estermann
functional-equation inverse have cancelled. -/
noncomputable def h15DirectAdditiveUnitPhase
    (sign : BettinChandeeUnitSign) (r u q : ℕ) : ℂ :=
  if hq : q = 0 then 0
  else
    letI : NeZero q := ⟨hq⟩
    ZMod.stdAddChar
      ((match sign with
        | .positive => (u : ZMod q)
        | .negative => -(u : ZMod q)) * (r : ZMod q))

/-- Exact positive phase collapse into the direct additive model. -/
theorem bblsAdditiveCharacter_h15_doubleInverse_eq_directPhase
    (r u q : ℕ) [NeZero q] (huq : Nat.Coprime u q) :
    bblsAdditiveCharacter r
        ((bblsEstermannInverseNumerator
            (h15InverseResidueNumerator u q huq) q
            (h15InverseResidueNumerator_coprime u q huq) : ℝ) /
          (q : ℝ)) =
      h15DirectAdditiveUnitPhase .positive r u q := by
  rw [bblsAdditiveCharacter_h15_doubleInverse_eq_direct r u q huq,
    bblsAdditiveCharacter_rat_eq_stdAddChar]
  have hq : q ≠ 0 := NeZero.ne q
  simp [h15DirectAdditiveUnitPhase, hq, mul_comm]

/-- Exact negative phase collapse into the direct additive model. -/
theorem bblsAdditiveCharacter_h15_doubleNegativeInverse_eq_directPhase
    (r u q : ℕ) [NeZero q] (huq : Nat.Coprime u q) :
    bblsAdditiveCharacter r
        ((bblsEstermannNegativeInverseNumerator
            (h15InverseResidueNumerator u q huq) q
            (h15InverseResidueNumerator_coprime u q huq) : ℝ) /
          (q : ℝ)) =
      h15DirectAdditiveUnitPhase .negative r u q := by
  rw [bblsAdditiveCharacter_h15_doubleNegativeInverse_eq_direct r u q huq]
  have hq : q ≠ 0 := NeZero.ne q
  simp [h15DirectAdditiveUnitPhase, hq, mul_comm]

/-- The corrected finite dyadic model which should replace a direct
Bettin--Chandee instantiation for the current H15 row convention. -/
noncomputable def h15DirectAdditiveTrilinearForm
    (sign : BettinChandeeUnitSign) (R U Q : ℕ)
    (alpha beta nu : ℕ → ℂ) : ℂ :=
  ∑ r ∈ h15BettinChandeeNatBlock R,
    ∑ u ∈ h15BettinChandeeNatBlock U,
      ∑ q ∈ h15BettinChandeeNatBlock Q,
        alpha u * beta q * nu r *
          h15DirectAdditiveUnitPhase sign r u q

/-! ## The paper's finite trilinear form -/

/-- A local `[X,2X)` dyadic block.  The paper uses `[X/2,X]`; the present
normalization is its specialization at endpoint `2X`, with the unused upper
endpoint coefficient set to zero. -/
def bettinChandeeLocalBlock (X : ℕ) : Finset ℕ :=
  Finset.Ico X (2 * X)

/-- The exact finite signed-unit specialization of the trilinear form in
Bettin--Chandee Theorem 1.  The coefficient order follows the paper:
`alpha` is on the inverted variable, `beta` on the modulus, and `nu` on the
extra averaging/frequency variable. -/
noncomputable def bettinChandeeSignedUnitTrilinearForm
    (sign : BettinChandeeUnitSign) (R U Q : ℕ)
    (alpha beta nu : ℕ → ℂ) : ℂ :=
  ∑ r ∈ bettinChandeeLocalBlock R,
    ∑ u ∈ bettinChandeeLocalBlock U,
      ∑ q ∈ bettinChandeeLocalBlock Q,
        alpha u * beta q * nu r *
          bettinChandeeSignedUnitPhase sign r u q

/-- Finite `L²` norm in the normalization used in Theorem 1. -/
noncomputable def bettinChandeeCoefficientNorm
    (X : ℕ) (c : ℕ → ℂ) : ℝ :=
  Real.sqrt
    (∑ x ∈ bettinChandeeLocalBlock X, ‖c x‖ ^ 2)

/-- The right-hand side of Bettin--Chandee Theorem 1, equation (1.2), after
translating the local blocks `[R,2R)`, `[U,2U)`, `[Q,2Q)` to the paper's
endpoint parameters `2R`, `2U`, `2Q`.

The first paper variable is the H15 frequency scale `R`; the other two are
the inverse and modulus scales `U,Q`. -/
noncomputable def bettinChandeeTheoremOneScale
    (epsilon : ℝ) (R U Q : ℕ) : ℝ :=
  let A : ℝ := 2 * (R : ℝ)
  let M : ℝ := 2 * (U : ℝ)
  let N : ℝ := 2 * (Q : ℝ)
  Real.sqrt (1 + A / (M * N)) *
    ((A * M * N) ^ ((7 / 20 : ℝ) + epsilon) *
        (M + N) ^ (1 / 4 : ℝ) +
      (A * M * N) ^ ((3 / 8 : ℝ) + epsilon) *
        (A * N + A * M) ^ (1 / 8 : ℝ))

/-- Faithful Lean interface to the signed-unit specialization of Theorem 1.

The source's `\ll_epsilon` notation is represented by `constant epsilon`;
there is deliberately no assertion that this constant is uniform as
`epsilon` tends to zero.  No field depends on H15 coefficients. -/
structure BettinChandeeSignedUnitTheoremOne where
  constant : ℝ → ℝ
  constant_nonneg : ∀ epsilon : ℝ, 0 ≤ constant epsilon
  bound : ∀ (epsilon : ℝ), 0 < epsilon →
    ∀ (sign : BettinChandeeUnitSign) (R U Q : ℕ),
      1 ≤ R → 1 ≤ U → 1 ≤ Q →
      ∀ alpha beta nu : ℕ → ℂ,
        ‖bettinChandeeSignedUnitTrilinearForm sign R U Q
            alpha beta nu‖ ≤
          constant epsilon *
            bettinChandeeCoefficientNorm U alpha *
            bettinChandeeCoefficientNorm Q beta *
            bettinChandeeCoefficientNorm R nu *
            bettinChandeeTheoremOneScale epsilon R U Q

/-! ## H15 variable dictionary -/

/-- The exact variable dictionary between one H15 dyadic key and equation
(1.2) of the paper.  It records a structural fact, not an estimate. -/
structure H15BettinChandeeVariableDictionary where
  paperA : ℕ
  paperM : ℕ
  paperN : ℕ
  thetaPositive : ℤ
  thetaNegative : ℤ

/-- In H15, the paper's extra variable is the Estermann frequency, its
inverted variable is the primitive numerator variable, and its modulus is
the primitive denominator variable. -/
def h15BettinChandeeVariableDictionary
    (key : H15BettinChandeeDyadicKey) :
    H15BettinChandeeVariableDictionary where
  paperA := 2 ^ (key.frequencyScale + 1)
  paperM := 2 ^ (key.inverseScale + 1)
  paperN := 2 ^ (key.modulusScale + 1)
  thetaPositive := 1
  thetaNegative := -1

@[simp] theorem h15BettinChandeeVariableDictionary_paperA
    (key : H15BettinChandeeDyadicKey) :
    (h15BettinChandeeVariableDictionary key).paperA =
      2 * 2 ^ key.frequencyScale := by
  simp [h15BettinChandeeVariableDictionary, pow_succ, Nat.mul_comm]

@[simp] theorem h15BettinChandeeVariableDictionary_paperM
    (key : H15BettinChandeeDyadicKey) :
    (h15BettinChandeeVariableDictionary key).paperM =
      2 * 2 ^ key.inverseScale := by
  simp [h15BettinChandeeVariableDictionary, pow_succ, Nat.mul_comm]

@[simp] theorem h15BettinChandeeVariableDictionary_paperN
    (key : H15BettinChandeeDyadicKey) :
    (h15BettinChandeeVariableDictionary key).paperN =
      2 * 2 ^ key.modulusScale := by
  simp [h15BettinChandeeVariableDictionary, pow_succ, Nat.mul_comm]

@[simp] theorem h15BettinChandeeVariableDictionary_thetaPositive
    (key : H15BettinChandeeDyadicKey) :
    (h15BettinChandeeVariableDictionary key).thetaPositive = 1 := rfl

@[simp] theorem h15BettinChandeeVariableDictionary_thetaNegative
    (key : H15BettinChandeeDyadicKey) :
    (h15BettinChandeeVariableDictionary key).thetaNegative = -1 := rfl

end NBMellinTools.NB12
