/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15BettinChandeeInstantiation

/-!
# NB12zc: direct-additive fixed-height reassembly for the H15 middle sector

The exact phase stop test in the preceding module shows that the two modular
inversions cancel on an actual H15 Laurent row.  This file records the
correct analytic object after that cancellation.

* The direct additive character is restricted to reduced numerator--modulus
  pairs, exactly as in the H15 row family.
* The factors `q^(2it)` and `r^(-it)` are isolated and proved to have norm
  one.
* The corresponding twisted H15 coefficient masses are proved to agree
  exactly with the untwisted masses already used in the dyadic ledger.
* A faithful direct-additive large-sieve interface and its balanced exponent
  stop test are stated.  The stop test shows that the elementary large sieve
  can only save power for frequency scale `R > N^2`; it does not close the
  whole finite middle window.

No large-sieve theorem, H15 decay, or Riemann-hypothesis statement is assumed
or proved here.
-/

open scoped BigOperators Topology LSeries.notation
open Complex

namespace NBMellinTools.NB12

/-! ## Reduced direct phases -/

/-- The post-functional-equation direct phase, extended by zero away from
the reduced numerator--modulus pairs occurring in H15. -/
noncomputable def h15DirectAdditiveReducedUnitPhase
    (sign : BettinChandeeUnitSign) (r u q : ℕ) : ℂ :=
  if Nat.Coprime u q then h15DirectAdditiveUnitPhase sign r u q else 0

@[simp] theorem h15DirectAdditiveReducedUnitPhase_of_coprime
    (sign : BettinChandeeUnitSign) (r u q : ℕ)
    (huq : Nat.Coprime u q) :
    h15DirectAdditiveReducedUnitPhase sign r u q =
      h15DirectAdditiveUnitPhase sign r u q := by
  simp [h15DirectAdditiveReducedUnitPhase, huq]

@[simp] theorem h15DirectAdditiveReducedUnitPhase_of_not_coprime
    (sign : BettinChandeeUnitSign) (r u q : ℕ)
    (huq : ¬ Nat.Coprime u q) :
    h15DirectAdditiveReducedUnitPhase sign r u q = 0 := by
  simp [h15DirectAdditiveReducedUnitPhase, huq]

/-- The actual direct-additive finite trilinear form, including the reduced
pair restriction inherited from the H15 Laurent rows. -/
noncomputable def h15DirectAdditiveReducedTrilinearForm
    (sign : BettinChandeeUnitSign) (R U Q : ℕ)
    (alpha beta nu : ℕ → ℂ) : ℂ :=
  ∑ r ∈ h15BettinChandeeNatBlock R,
    ∑ u ∈ h15BettinChandeeNatBlock U,
      ∑ q ∈ h15BettinChandeeNatBlock Q,
        alpha u * beta q * nu r *
          h15DirectAdditiveReducedUnitPhase sign r u q

/-! ## Exact vertical twists -/

/-- The modulus-dependent unitary factor left after extracting `q^2` from
the Estermann functional-equation factor on `Re(s)=3/2`. -/
noncomputable def h15ThreeHalfModulusUnitTwist (q : ℕ) (t : ℝ) : ℂ :=
  (q : ℂ) ^ ((2 : ℂ) * Complex.I * (t : ℂ))

/-- The frequency-dependent unitary factor left after extracting the real
Dirichlet weight `r^(-3/2)`. -/
noncomputable def h15ThreeHalfFrequencyUnitTwist (r : ℕ) (t : ℝ) : ℂ :=
  (r : ℂ) ^ (-(Complex.I * (t : ℂ)))

/-- The part of the Estermann functional-equation factor on `3/2+it`
which is independent of the modulus. -/
noncomputable def h15ThreeHalfArchimedeanFactor (t : ℝ) : ℂ :=
  let s := bblsEstermannThreeHalfPoint t
  2 * (2 * Real.pi : ℂ) ^ (-2 * s) * Complex.Gamma s ^ 2

@[simp] theorem norm_h15ThreeHalfModulusUnitTwist
    {q : ℕ} (hq : 0 < q) (t : ℝ) :
    ‖h15ThreeHalfModulusUnitTwist q t‖ = 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold h15ThreeHalfModulusUnitTwist
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hqR]
  have hre : ((2 : ℂ) * Complex.I * (t : ℂ)).re = 0 := by simp
  rw [hre, Real.rpow_zero]

@[simp] theorem norm_h15ThreeHalfFrequencyUnitTwist
    {r : ℕ} (hr : 0 < r) (t : ℝ) :
    ‖h15ThreeHalfFrequencyUnitTwist r t‖ = 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  unfold h15ThreeHalfFrequencyUnitTwist
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hrR]
  have hre : (-(Complex.I * (t : ℂ))).re = 0 := by simp
  rw [hre, Real.rpow_zero]

/-- Exact extraction of the algebraic modulus square and the unitary
`q^(2it)` twist from the classical Estermann factor. -/
theorem bblsEstermannClassicalFactor_threeHalf_eq_sq_mul_unitTwist
    {q : ℕ} (hq : 0 < q) (t : ℝ) :
    bblsEstermannClassicalFactor q (bblsEstermannThreeHalfPoint t) =
      (q : ℂ) ^ 2 * h15ThreeHalfModulusUnitTwist q t *
        h15ThreeHalfArchimedeanFactor t := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold bblsEstermannClassicalFactor
    h15ThreeHalfModulusUnitTwist h15ThreeHalfArchimedeanFactor
  dsimp only
  rw [show 2 * bblsEstermannThreeHalfPoint t - 1 =
      (2 : ℂ) + (2 : ℂ) * Complex.I * (t : ℂ) by
        unfold bblsEstermannThreeHalfPoint
        push_cast
        ring]
  rw [Complex.cpow_add _ _ hqC, Complex.cpow_two]
  ring

/-- The time-dependent modulus coefficient in the actual fixed-height H15
fiber. -/
noncomputable def h15DirectAdditiveModulusCoefficient
    (N g q : ℕ) (t : ℝ) : ℂ :=
  (h15BettinChandeeModulusCoefficient N g q : ℂ) *
    h15ThreeHalfModulusUnitTwist q t

/-- The time-dependent frequency coefficient in the actual fixed-height H15
fiber.  Its norm is independent of the vertical parameter. -/
noncomputable def h15DirectAdditiveFrequencyCoefficient
    (r : ℕ) (t : ℝ) : ℂ :=
  LSeries.term bblsEstermannDivisorCoeff
    (bblsEstermannThreeHalfPoint t) r

/-- Multiplication by `q^(2it)` preserves the exact finite squared modulus
mass on every positive supported block. -/
theorem h15DirectAdditiveModulusMass_eq
    {N g Q : ℕ} (hQ : 0 < Q) (t : ℝ) :
    (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ‖h15DirectAdditiveModulusCoefficient N g q t‖ ^ 2) =
      h15BettinChandeeModulusMass N g Q := by
  unfold h15BettinChandeeModulusMass
  apply Finset.sum_congr rfl
  intro q hq
  have hqmem := mem_h15BettinChandeeSupportedNatBlock.mp hq
  have hqpos : 0 < q := hQ.trans_le hqmem.1
  rw [h15DirectAdditiveModulusCoefficient, norm_mul,
    norm_h15ThreeHalfModulusUnitTwist hqpos t, mul_one]
  simp [Real.norm_eq_abs, sq_abs]

/-- Multiplication by `r^(-it)` preserves the exact finite squared frequency
mass on every positive dyadic block. -/
theorem h15DirectAdditiveFrequencyMass_eq
    (R : ℕ) (t : ℝ) :
    (∑ r ∈ h15BettinChandeeNatBlock R,
        ‖h15DirectAdditiveFrequencyCoefficient r t‖ ^ 2) =
      h15BettinChandeeFrequencyMass R := by
  unfold h15DirectAdditiveFrequencyCoefficient
    h15BettinChandeeFrequencyMass
    h15BettinChandeeFrequencyCoefficient
  apply Finset.sum_congr rfl
  intro r hr
  have hrange := Finset.mem_Ico.mp hr
  simp only [LSeries.norm_term_eq]
  congr 2
  norm_num [bblsEstermannThreeHalfPoint]

/-! ## Exact fixed-height row reassembly -/

/-- An Estermann Dirichlet term is its untwisted divisor term times the
additive character. -/
theorem bblsEstermannTerm_eq_divisorTerm_mul_character
    (x : ℝ) (s : ℂ) (r : ℕ) :
    LSeries.term (bblsEstermannCoeff x) s r =
      LSeries.term bblsEstermannDivisorCoeff s r *
        bblsAdditiveCharacter r x := by
  by_cases hr : r = 0
  · simp [hr]
  · simp only [LSeries.term_of_ne_zero hr, bblsEstermannCoeff]
    ring

/-- The frequency term on `3/2+it` is the real `3/2` term times the exact
unitary twist `r^(-it)`. -/
theorem h15DirectAdditiveFrequencyCoefficient_eq_base_mul_twist
    {r : ℕ} (hr : 0 < r) (t : ℝ) :
    h15DirectAdditiveFrequencyCoefficient r t =
      LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ) r *
        h15ThreeHalfFrequencyUnitTwist r t := by
  have hr0 : r ≠ 0 := hr.ne'
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
  unfold h15DirectAdditiveFrequencyCoefficient
    h15ThreeHalfFrequencyUnitTwist bblsEstermannThreeHalfPoint
  rw [LSeries.term_of_ne_zero hr0, LSeries.term_of_ne_zero hr0]
  rw [show ((3 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ) =
      (3 / 2 : ℂ) + Complex.I * (t : ℂ) by norm_num]
  rw [Complex.cpow_add _ _ hrC, Complex.cpow_neg]
  field_simp

/-- The primitive variables selected by an actual valid H15 row are
coprime, independently of its orientation. -/
theorem h15BettinChandeeInverse_coprime_modulus
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i) :
    Nat.Coprime (h15BettinChandeeInverseVariable i)
      (h15BettinChandeeModulusVariable i) := by
  rcases h15LaurentOrientation_eq_zero_or_one i with h | h
  · simpa [h15BettinChandeeInverseVariable,
      h15BettinChandeeModulusVariable, h] using hvalid.2.2.2.2
  · have hne : h15LaurentOrientation i ≠ 0 := by omega
    simpa [h15BettinChandeeInverseVariable,
      h15BettinChandeeModulusVariable, hne] using hvalid.2.2.2.2.symm

/-- Positive dual character of every actual H15 row in the
orientation-independent direct model. -/
theorem h15LaurentRow_positiveDualPhase_eq_direct
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i) (r : ℕ) :
    let row := h15LaurentRow i
    letI : NeZero row.denominator := ⟨row.denominator_pos.ne'⟩
    bblsAdditiveCharacter r
        ((bblsEstermannInverseNumerator row.numerator row.denominator
            row.coprime : ℝ) / (row.denominator : ℝ)) =
      h15DirectAdditiveReducedUnitPhase .positive r
        (h15BettinChandeeInverseVariable i)
        (h15BettinChandeeModulusVariable i) := by
  dsimp only
  rw [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _
    (h15BettinChandeeInverse_coprime_modulus i hvalid)]
  rcases h15LaurentOrientation_eq_zero_or_one i with h | h
  · letI : NeZero (h15LaurentQ i) := ⟨by simp [h15LaurentQ]⟩
    simpa [h15LaurentRow, h,
      h15BettinChandeeInverseVariable,
      h15BettinChandeeModulusVariable,
      hvalid.2.2.2.2.gcd_eq_one] using
        (bblsAdditiveCharacter_h15_doubleInverse_eq_directPhase
          r (h15LaurentA i) (h15LaurentQ i) hvalid.2.2.2.2)
  · have hne : h15LaurentOrientation i ≠ 0 := by omega
    letI : NeZero (h15LaurentA i) := ⟨by simp [h15LaurentA]⟩
    simpa [h15LaurentRow, hne,
      h15BettinChandeeInverseVariable,
      h15BettinChandeeModulusVariable,
      hvalid.2.2.2.2.symm.gcd_eq_one] using
        (bblsAdditiveCharacter_h15_doubleInverse_eq_directPhase
          r (h15LaurentQ i) (h15LaurentA i) hvalid.2.2.2.2.symm)

/-- Negative dual character of every actual H15 row in the
orientation-independent direct model. -/
theorem h15LaurentRow_negativeDualPhase_eq_direct
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i) (r : ℕ) :
    let row := h15LaurentRow i
    letI : NeZero row.denominator := ⟨row.denominator_pos.ne'⟩
    bblsAdditiveCharacter r
        ((bblsEstermannNegativeInverseNumerator row.numerator row.denominator
            row.coprime : ℝ) / (row.denominator : ℝ)) =
      h15DirectAdditiveReducedUnitPhase .negative r
        (h15BettinChandeeInverseVariable i)
        (h15BettinChandeeModulusVariable i) := by
  dsimp only
  rw [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _
    (h15BettinChandeeInverse_coprime_modulus i hvalid)]
  rcases h15LaurentOrientation_eq_zero_or_one i with h | h
  · letI : NeZero (h15LaurentQ i) := ⟨by simp [h15LaurentQ]⟩
    simpa [h15LaurentRow, h,
      h15BettinChandeeInverseVariable,
      h15BettinChandeeModulusVariable,
      hvalid.2.2.2.2.gcd_eq_one] using
        (bblsAdditiveCharacter_h15_doubleNegativeInverse_eq_directPhase
          r (h15LaurentA i) (h15LaurentQ i) hvalid.2.2.2.2)
  · have hne : h15LaurentOrientation i ≠ 0 := by omega
    letI : NeZero (h15LaurentA i) := ⟨by simp [h15LaurentA]⟩
    simpa [h15LaurentRow, hne,
      h15BettinChandeeInverseVariable,
      h15BettinChandeeModulusVariable,
      hvalid.2.2.2.2.symm.gcd_eq_one] using
        (bblsAdditiveCharacter_h15_doubleNegativeInverse_eq_directPhase
          r (h15LaurentQ i) (h15LaurentA i) hvalid.2.2.2.2.symm)

/-- Exact fixed-height reassembly of a genuine paired H15 frequency term.
Both Estermann orientations are retained inside one signed direct-additive
expression. -/
theorem bblsActiveThreeHalfFrequencyTerm_h15_eq_direct
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i)
    (damping : ℝ) (r : ℕ) (t : ℝ) :
    bblsActiveThreeHalfFrequencyTerm damping
        (h15LaurentRow i).numerator
        (h15LaurentRow i).denominator
        (h15LaurentRow i).coprime r t =
      let s := bblsEstermannThreeHalfPoint t
      Complex.Gamma (-s) * (damping : ℂ) ^ s *
        bblsEstermannClassicalFactor
          (h15LaurentRow i).denominator s *
        h15DirectAdditiveFrequencyCoefficient r t *
        (h15DirectAdditiveReducedUnitPhase .positive r
            (h15BettinChandeeInverseVariable i)
            (h15BettinChandeeModulusVariable i) +
          Complex.cos ((Real.pi : ℂ) * s) *
            h15DirectAdditiveReducedUnitPhase .negative r
              (h15BettinChandeeInverseVariable i)
              (h15BettinChandeeModulusVariable i)) := by
  dsimp only
  unfold bblsActiveThreeHalfFrequencyTerm
  simp only [bblsEstermannTerm_eq_divisorTerm_mul_character]
  rw [h15LaurentRow_positiveDualPhase_eq_direct i hvalid r,
    h15LaurentRow_negativeDualPhase_eq_direct i hvalid r]
  unfold h15DirectAdditiveFrequencyCoefficient
  ring

/-- Exact coefficient-separated fixed-height H15 summand.  The only
`q`- and `r`-dependent Archimedean factors are the unitary twists already
shown to preserve the finite `L²` masses. -/
theorem h15WeightedThreeHalfFrequencyTerm_eq_directSeparated
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i)
    (damping : ℝ) (r : ℕ) (t : ℝ) :
    h15LaurentRowWeight i *
        bblsActiveThreeHalfFrequencyTerm damping
          (h15LaurentRow i).numerator
          (h15LaurentRow i).denominator
          (h15LaurentRow i).coprime r t =
      let s := bblsEstermannThreeHalfPoint t
      let u := h15BettinChandeeInverseVariable i
      let q := h15BettinChandeeModulusVariable i
      (((Real.pi / (h15LaurentG i : ℝ)) *
          h15BettinChandeeInverseCoefficient N (h15LaurentG i) u : ℝ) : ℂ) *
        Complex.Gamma (-s) * (damping : ℂ) ^ s *
        h15ThreeHalfArchimedeanFactor t *
        h15DirectAdditiveModulusCoefficient N (h15LaurentG i) q t *
        h15DirectAdditiveFrequencyCoefficient r t *
        (h15DirectAdditiveReducedUnitPhase .positive r u q +
          Complex.cos ((Real.pi : ℂ) * s) *
            h15DirectAdditiveReducedUnitPhase .negative r u q) := by
  dsimp only
  rw [bblsActiveThreeHalfFrequencyTerm_h15_eq_direct i hvalid]
  rw [h15LaurentRow_denominator_eq_bettinChandeeModulus i hvalid]
  simp only [bblsEstermannClassicalFactor_threeHalf_eq_sq_mul_unitTwist
    (h15BettinChandeeModulusVariable_pos i) t]
  have hweight :=
    h15LaurentRowWeight_mul_denominator_sq_factorization_both i hvalid
  rw [h15LaurentRow_denominator_eq_bettinChandeeModulus i hvalid] at hweight
  rw [h15DirectAdditiveModulusCoefficient]
  push_cast at hweight ⊢
  ring_nf at hweight ⊢
  rw [hweight]

/-- The separated right-hand side of the preceding theorem, packaged as a
reusable summand. -/
noncomputable def h15DirectAdditiveSeparatedSummand
    (N : ℕ) (damping : ℝ) (i : H15LaurentRowIndex N)
    (r : ℕ) (t : ℝ) : ℂ :=
  let s := bblsEstermannThreeHalfPoint t
  let u := h15BettinChandeeInverseVariable i
  let q := h15BettinChandeeModulusVariable i
  (((Real.pi / (h15LaurentG i : ℝ)) *
      h15BettinChandeeInverseCoefficient N (h15LaurentG i) u : ℝ) : ℂ) *
    Complex.Gamma (-s) * (damping : ℂ) ^ s *
    h15ThreeHalfArchimedeanFactor t *
    h15DirectAdditiveModulusCoefficient N (h15LaurentG i) q t *
    h15DirectAdditiveFrequencyCoefficient r t *
    (h15DirectAdditiveReducedUnitPhase .positive r u q +
      Complex.cos ((Real.pi : ℂ) * s) *
        h15DirectAdditiveReducedUnitPhase .negative r u q)

/-- Invalid Laurent rows have zero H15 weight.  The valid rows are exactly
the separated direct-additive summands. -/
noncomputable def h15DirectAdditiveFixedHeightSummand
    (N : ℕ) (damping : ℝ) (ir : H15LaurentRowIndex N × ℕ)
    (t : ℝ) : ℂ := by
  classical
  exact if h15LaurentRowValid ir.1 then
      h15DirectAdditiveSeparatedSummand N damping ir.1 ir.2 t
    else 0

theorem h15WeightedFrequencyTerm_eq_directFixedHeightSummand
    (N : ℕ) (damping : ℝ) (ir : H15LaurentRowIndex N × ℕ)
    (t : ℝ) :
    h15LaurentRowWeight ir.1 *
        bblsActiveThreeHalfFrequencyTerm damping
          (h15LaurentRow ir.1).numerator
          (h15LaurentRow ir.1).denominator
          (h15LaurentRow ir.1).coprime ir.2 t =
      h15DirectAdditiveFixedHeightSummand N damping ir t := by
  by_cases hvalid : h15LaurentRowValid ir.1
  · rw [h15DirectAdditiveFixedHeightSummand, if_pos hvalid]
    exact h15WeightedThreeHalfFrequencyTerm_eq_directSeparated
      ir.1 hvalid damping ir.2 t
  · simp [h15DirectAdditiveFixedHeightSummand,
      h15LaurentRowWeight, hvalid]

/-- The genuine fixed-height dyadic H15 fiber before direct-phase
reassembly. -/
noncomputable def h15OriginalFixedHeightDyadicBlock
    (N K J : ℕ) (damping t : ℝ)
    (key : H15BettinChandeeDyadicKey) : ℂ :=
  ∑ ir ∈ h15BettinChandeeDyadicBlock N K J key,
    h15LaurentRowWeight ir.1 *
      bblsActiveThreeHalfFrequencyTerm damping
        (h15LaurentRow ir.1).numerator
        (h15LaurentRow ir.1).denominator
        (h15LaurentRow ir.1).coprime ir.2 t

/-- The same dyadic fiber written entirely with the paired direct additive
phases and separated fixed-height coefficients. -/
noncomputable def h15DirectAdditiveFixedHeightDyadicBlock
    (N K J : ℕ) (damping t : ℝ)
    (key : H15BettinChandeeDyadicKey) : ℂ :=
  ∑ ir ∈ h15BettinChandeeDyadicBlock N K J key,
    h15DirectAdditiveFixedHeightSummand N damping ir t

/-- Exact direct-additive reassembly of every finite H15 dyadic fiber at a
fixed contour height. -/
theorem h15OriginalFixedHeightDyadicBlock_eq_direct
    (N K J : ℕ) (damping t : ℝ)
    (key : H15BettinChandeeDyadicKey) :
    h15OriginalFixedHeightDyadicBlock N K J damping t key =
      h15DirectAdditiveFixedHeightDyadicBlock N K J damping t key := by
  unfold h15OriginalFixedHeightDyadicBlock
    h15DirectAdditiveFixedHeightDyadicBlock
  apply Finset.sum_congr rfl
  intro ir _
  exact h15WeightedFrequencyTerm_eq_directFixedHeightSummand
    N damping ir t

/-! ## Direct additive large-sieve stop test -/

/-- The scale produced by Cauchy--Schwarz followed by the classical additive
large sieve over reduced fractions.  This is an interface, not an imported
or assumed theorem. -/
noncomputable def h15DirectAdditiveLargeSieveScale
    (R Q : ℕ) : ℝ :=
  Real.sqrt ((2 * (Q : ℝ)) ^ 2 + 2 * (R : ℝ))

/-- Faithful theorem-level interface for the elementary direct additive
large-sieve estimate required by the current H15 phase convention. -/
structure H15DirectAdditiveLargeSieve where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound : ∀ (sign : BettinChandeeUnitSign) (R U Q : ℕ),
    1 ≤ R → 1 ≤ U → 1 ≤ Q →
    ∀ alpha beta nu : ℕ → ℂ,
      ‖h15DirectAdditiveReducedTrilinearForm sign R U Q
          alpha beta nu‖ ≤
        constant *
          bettinChandeeCoefficientNorm U alpha *
          bettinChandeeCoefficientNorm Q beta *
          bettinChandeeCoefficientNorm R nu *
          h15DirectAdditiveLargeSieveScale R Q

/-- Balanced power of the direct additive large-sieve bound when
`U,Q ~ N` and `R=N^kappa`, after inserting the proved H15 coefficient
norms. -/
noncomputable def h15DirectAdditiveBalancedExponent (kappa : ℝ) : ℝ :=
  if kappa ≤ 2 then 2 - kappa else 1 - kappa / 2

/-- The elementary additive large sieve gains a negative power precisely
above the quadratic frequency threshold. -/
theorem h15DirectAdditiveBalancedExponent_neg_iff (kappa : ℝ) :
    h15DirectAdditiveBalancedExponent kappa < 0 ↔ 2 < kappa := by
  unfold h15DirectAdditiveBalancedExponent
  split_ifs with h
  · constructor
    · intro hk
      linarith
    · intro hk
      linarith
  · constructor <;> intro hk <;> linarith

/-- At the quadratic transition the direct additive large-sieve exponent is
exactly zero, so the elementary estimate gives no power saving there. -/
@[simp] theorem h15DirectAdditiveBalancedExponent_two :
    h15DirectAdditiveBalancedExponent 2 = 0 := by
  simp [h15DirectAdditiveBalancedExponent]

end NBMellinTools.NB12
