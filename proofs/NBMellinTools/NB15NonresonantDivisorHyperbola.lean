/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15DirectAdditiveResonanceSplit

/-!
# NB15: exact divisor-hyperbola form of the nonresonant frequency window

The nonresonant middle-frequency sector has the direct additive phase
`e_q(±ru)`, but its frequency coefficient is not constant: it is the
Estermann divisor coefficient on `3/2+it`.  Consequently the literal H15
sum is neither a complete Ramanujan sum nor an unweighted geometric sum.

This file performs the first exact reduction needed for a geometric/Abel
argument.  It expands the divisor coefficient and reindexes the incomplete
frequency interval as positive factor pairs `r = a*b`, retaining:

* the precise half-open interval `K + 1 <= r < K + 1 + J`;
* the nonresonance condition `q ∤ r`;
* the full complex `r^(-3/2-it)` weight; and
* the direct additive phase, before any norm is taken.

No cancellation or asymptotic estimate is asserted.
-/

open scoped BigOperators Topology LSeries.notation

namespace NBMellinTools.NB12

/-! ## Literal nonresonant frequency and hyperbola supports -/

/-- The frequency interval in the actual H15 middle window, restricted to
the direct-additive nonresonant sector for modulus `q`. -/
def h15NonresonantFrequencySupport (K J q : ℕ) : Finset ℕ :=
  (Finset.Ico (K + 1) (K + 1 + J)).filter (fun r => ¬q ∣ r)

/-- Positive factor pairs whose product belongs to the literal nonresonant
frequency support.  The common bound `K+J` is exact enough because every
frequency in the half-open window is at most `K+J`. -/
def h15NonresonantDivisorHyperbolaSupport
    (K J q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (K + J)).product (Finset.Icc 1 (K + J))).filter
    (fun ab => ab.1 * ab.2 ∈ h15NonresonantFrequencySupport K J q)

/-- The admissible second factors after the first divisor `a` is fixed. -/
def h15NonresonantSecondFactorSupport
    (K J q a : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (K + J)).filter
    (fun b => a * b ∈ h15NonresonantFrequencySupport K J q)

theorem mem_h15NonresonantFrequencySupport
    {K J q r : ℕ} :
    r ∈ h15NonresonantFrequencySupport K J q ↔
      K + 1 ≤ r ∧ r < K + 1 + J ∧ ¬q ∣ r := by
  simp [h15NonresonantFrequencySupport, and_assoc]

theorem pos_of_mem_h15NonresonantFrequencySupport
    {K J q r : ℕ} (hr : r ∈ h15NonresonantFrequencySupport K J q) :
    0 < r := by
  have h := (mem_h15NonresonantFrequencySupport.mp hr).1
  omega

theorem le_cutoff_of_mem_h15NonresonantFrequencySupport
    {K J q r : ℕ} (hr : r ∈ h15NonresonantFrequencySupport K J q) :
    r ≤ K + J := by
  have h := (mem_h15NonresonantFrequencySupport.mp hr).2.1
  omega

theorem mem_h15NonresonantDivisorHyperbolaSupport
    {K J q : ℕ} {ab : ℕ × ℕ} :
    ab ∈ h15NonresonantDivisorHyperbolaSupport K J q ↔
      1 ≤ ab.1 ∧ ab.1 ≤ K + J ∧
      1 ≤ ab.2 ∧ ab.2 ≤ K + J ∧
      ab.1 * ab.2 ∈ h15NonresonantFrequencySupport K J q := by
  simp [h15NonresonantDivisorHyperbolaSupport, and_assoc]

theorem mem_h15NonresonantSecondFactorSupport
    {K J q a b : ℕ} :
    b ∈ h15NonresonantSecondFactorSupport K J q a ↔
      1 ≤ b ∧ b ≤ K + J ∧
        a * b ∈ h15NonresonantFrequencySupport K J q := by
  simp [h15NonresonantSecondFactorSupport, and_assoc]

/-! ## Exact finite divisor expansion -/

/-- On a positive frequency, the classical divisor coefficient is exactly
one copy of an arbitrary value for each positive factor pair. -/
theorem bblsEstermannDivisorCoeff_mul_eq_sum_divisorsAntidiagonal
    {r : ℕ} (hr : 0 < r) (z : ℂ) :
    bblsEstermannDivisorCoeff r * z =
      ∑ _ab ∈ r.divisorsAntidiagonal, z := by
  rw [bblsEstermannDivisorCoeff_apply]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := card_divisorsAntidiagonal_eq_card_divisors
    (⟨r, hr⟩ : ℕ+)
  simpa using congrArg (fun n : ℕ => (n : ℂ) * z) hcard.symm

/-- Exact finite hyperbolic reindexing on the literal nonresonant support.
The theorem is generic in the product-dependent complex summand, so later
applications can retain either the full H15 coefficient or an Abel weight. -/
theorem sum_nonresonant_divisorCoeff_eq_sum_hyperbola
    (K J q : ℕ) (value : ℕ → ℂ) :
    (∑ r ∈ h15NonresonantFrequencySupport K J q,
        bblsEstermannDivisorCoeff r * value r) =
      ∑ ab ∈ h15NonresonantDivisorHyperbolaSupport K J q,
        value (ab.1 * ab.2) := by
  classical
  let s := h15NonresonantDivisorHyperbolaSupport K J q
  let t := h15NonresonantFrequencySupport K J q
  let product : ℕ × ℕ → ℕ := fun ab => ab.1 * ab.2
  have hmap : ∀ ab ∈ s, product ab ∈ t := by
    intro ab hab
    exact (mem_h15NonresonantDivisorHyperbolaSupport.mp hab).2.2.2.2
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap (value ∘ product)
  calc
    (∑ r ∈ h15NonresonantFrequencySupport K J q,
        bblsEstermannDivisorCoeff r * value r) =
        ∑ r ∈ t, ∑ ab ∈ r.divisorsAntidiagonal, value r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [bblsEstermannDivisorCoeff_mul_eq_sum_divisorsAntidiagonal
        (pos_of_mem_h15NonresonantFrequencySupport hr)]
    _ = ∑ r ∈ t, ∑ ab ∈ s with product ab = r, value r := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrpos := pos_of_mem_h15NonresonantFrequencySupport hr
      have hrle := le_cutoff_of_mem_h15NonresonantFrequencySupport hr
      apply Finset.sum_congr
      · ext ab
        constructor
        · intro hab
          have hp := (Nat.mem_divisorsAntidiagonal.mp hab).1
          have habpos : 0 < ab.1 * ab.2 := by simpa [hp] using hrpos
          have ha : 0 < ab.1 := by
            apply Nat.pos_of_ne_zero
            intro ha0
            simp [ha0] at habpos
          have hb : 0 < ab.2 := by
            apply Nat.pos_of_ne_zero
            intro hb0
            simp [hb0] at habpos
          have hale : ab.1 ≤ K + J := by
            calc
              ab.1 ≤ ab.1 * ab.2 := Nat.le_mul_of_pos_right ab.1 hb
              _ = r := hp
              _ ≤ K + J := hrle
          have hble : ab.2 ≤ K + J := by
            calc
              ab.2 ≤ ab.1 * ab.2 := Nat.le_mul_of_pos_left ab.2 ha
              _ = r := hp
              _ ≤ K + J := hrle
          exact Finset.mem_filter.mpr
            ⟨(mem_h15NonresonantDivisorHyperbolaSupport.mpr
              ⟨ha, hale, hb, hble, by simpa [product, hp] using hr⟩),
              by simpa [product] using hp⟩
        · intro hab
          have hab' := Finset.mem_filter.mp hab
          have hp : ab.1 * ab.2 = r := by
            simpa [product] using hab'.2
          exact Nat.mem_divisorsAntidiagonal.mpr ⟨hp, hrpos.ne'⟩
      · intro ab hab
        have hp : product ab = r := (Finset.mem_filter.mp hab).2
        simpa [product, hp]
    _ = ∑ r ∈ t, ∑ ab ∈ s with product ab = r,
          (value ∘ product) ab := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro ab hab
      have hp : product ab = r := (Finset.mem_filter.mp hab).2
      simp [hp]
    _ = ∑ ab ∈ s, (value ∘ product) ab := hfiber
    _ = ∑ ab ∈ h15NonresonantDivisorHyperbolaSupport K J q,
          value (ab.1 * ab.2) := by rfl

/-- The hyperbola support can be sliced by its first factor without changing
any coefficient or phase. -/
theorem sum_h15NonresonantDivisorHyperbolaSupport_eq_fixedFirstFactor
    (K J q : ℕ) (value : ℕ × ℕ → ℂ) :
    (∑ ab ∈ h15NonresonantDivisorHyperbolaSupport K J q, value ab) =
      ∑ a ∈ Finset.Icc 1 (K + J),
        ∑ b ∈ h15NonresonantSecondFactorSupport K J q a,
          value (a, b) := by
  classical
  unfold h15NonresonantDivisorHyperbolaSupport
    h15NonresonantSecondFactorSupport
  simp only [Finset.sum_filter]
  rw [← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro ab _
  rfl

/-! ## Complete-period cancellation of the fixed-factor phase -/

/-- A nonzero additive frequency has exact mean zero over one complete
natural representative system modulo `q`. -/
theorem sum_range_stdAddChar_mul_eq_zero
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    (∑ b ∈ Finset.range q,
      ZMod.stdAddChar (j * (b : ZMod q))) = 0 := by
  have hchar : (∑ z : ZMod q, ZMod.stdAddChar (z * j)) = 0 := by
    simpa [hj] using AddChar.sum_mulShift (ψ := ZMod.stdAddChar) j
      (ZMod.isPrimitive_stdAddChar q)
  have hfin :
      (∑ b : Fin q, ZMod.stdAddChar ((ZMod.finEquiv q b) * j)) = 0 := by
    calc
      (∑ b : Fin q, ZMod.stdAddChar ((ZMod.finEquiv q b) * j)) =
          ∑ z : ZMod q, ZMod.stdAddChar (z * j) := by
            apply Fintype.sum_equiv (ZMod.finEquiv q)
            intro b
            rfl
      _ = 0 := hchar
  have hfinCast (b : Fin q) : ZMod.finEquiv q b = (b : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
        apply ZMod.val_injective (q + 1)
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt b.isLt]
        rfl
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ b : Fin q, ZMod.stdAddChar (j * (b : ZMod q))) =
        ∑ b : Fin q, ZMod.stdAddChar ((ZMod.finEquiv q b) * j) := by
          apply Finset.sum_congr rfl
          intro b _
          apply congrArg ZMod.stdAddChar
          rw [hfinCast b, mul_comm]
    _ = 0 := hfin

/-- Multiplication by a reduced numerator does not create a zero frequency:
`u*a` is nonzero modulo `q` exactly when the fixed factor `a` is
nonresonant. -/
theorem h15DirectAdditiveFixedFactor_ne_zero
    {q u a : ℕ} (huq : Nat.Coprime u q) (ha : ¬q ∣ a) :
    (u : ZMod q) * (a : ZMod q) ≠ 0 := by
  intro hzero
  have hcast : ((u * a : ℕ) : ZMod q) = 0 := by
    simpa only [Nat.cast_mul] using hzero
  have hdiv : q ∣ u * a := (ZMod.natCast_eq_zero_iff (u * a) q).mp hcast
  exact ha ((huq.symm.dvd_mul_left).mp hdiv)

/-- For either H15 orientation, every complete `q`-period in the second
factor cancels exactly whenever the first factor is nonresonant.  This is
the precise algebraic input for the subsequent incomplete-interval and Abel
estimates. -/
theorem sum_range_h15DirectAdditiveReducedUnitPhase_mul_eq_zero
    (sign : BettinChandeeUnitSign) {q u a : ℕ}
    (hq : 0 < q) (huq : Nat.Coprime u q) (ha : ¬q ∣ a) :
    (∑ b ∈ Finset.range q,
      h15DirectAdditiveReducedUnitPhase sign (a * b) u q) = 0 := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hj : (u : ZMod q) * (a : ZMod q) ≠ 0 :=
    h15DirectAdditiveFixedFactor_ne_zero huq ha
  cases sign with
  | positive =>
      calc
        (∑ b ∈ Finset.range q,
            h15DirectAdditiveReducedUnitPhase .positive (a * b) u q) =
            ∑ b ∈ Finset.range q,
              ZMod.stdAddChar
                (((u : ZMod q) * (a : ZMod q)) * (b : ZMod q)) := by
          apply Finset.sum_congr rfl
          intro b _
          simp only [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ huq]
          simp [h15DirectAdditiveUnitPhase, hq.ne']
          congr 1 <;> push_cast <;> ring
        _ = 0 := sum_range_stdAddChar_mul_eq_zero _ hj
  | negative =>
      have hjneg : -((u : ZMod q) * (a : ZMod q)) ≠ 0 := neg_ne_zero.mpr hj
      calc
        (∑ b ∈ Finset.range q,
            h15DirectAdditiveReducedUnitPhase .negative (a * b) u q) =
            ∑ b ∈ Finset.range q,
              ZMod.stdAddChar
                ((-((u : ZMod q) * (a : ZMod q))) * (b : ZMod q)) := by
          apply Finset.sum_congr rfl
          intro b _
          simp only [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ huq]
          simp [h15DirectAdditiveUnitPhase, hq.ne']
          congr 1 <;> push_cast <;> ring
        _ = 0 := sum_range_stdAddChar_mul_eq_zero _ hjneg

/-! ## Literal H15 specialization -/

/-- The full fixed-height nonresonant frequency fiber for fixed reduced
numerator and modulus. -/
noncomputable def h15DirectAdditiveNonresonantFrequencySum
    (sign : BettinChandeeUnitSign) (K J q u : ℕ) (t : ℝ) : ℂ :=
  ∑ r ∈ h15NonresonantFrequencySupport K J q,
    h15DirectAdditiveFrequencyCoefficient r t *
      h15DirectAdditiveReducedUnitPhase sign r u q

/-- Exact H15 divisor-hyperbola identity.  In particular the complex norm
is not taken until after all factor-pair contributions have been recombined. -/
theorem h15DirectAdditiveNonresonantFrequencySum_eq_hyperbola
    (sign : BettinChandeeUnitSign) (K J q u : ℕ) (t : ℝ) :
    h15DirectAdditiveNonresonantFrequencySum sign K J q u t =
      ∑ ab ∈ h15NonresonantDivisorHyperbolaSupport K J q,
        (ab.1 * ab.2 : ℂ) ^ (-(bblsEstermannThreeHalfPoint t)) *
          h15DirectAdditiveReducedUnitPhase sign (ab.1 * ab.2) u q := by
  unfold h15DirectAdditiveNonresonantFrequencySum
  rw [show (∑ r ∈ h15NonresonantFrequencySupport K J q,
      h15DirectAdditiveFrequencyCoefficient r t *
        h15DirectAdditiveReducedUnitPhase sign r u q) =
      ∑ r ∈ h15NonresonantFrequencySupport K J q,
        bblsEstermannDivisorCoeff r *
          ((r : ℂ) ^ (-(bblsEstermannThreeHalfPoint t)) *
            h15DirectAdditiveReducedUnitPhase sign r u q) by
    apply Finset.sum_congr rfl
    intro r hr
    have hr0 := (pos_of_mem_h15NonresonantFrequencySupport hr).ne'
    rw [h15DirectAdditiveFrequencyCoefficient, LSeries.term_of_ne_zero hr0]
    rw [Complex.cpow_neg]
    ring]
  simpa only [Nat.cast_mul] using
    (sum_nonresonant_divisorCoeff_eq_sum_hyperbola K J q
      (fun r => (r : ℂ) ^ (-(bblsEstermannThreeHalfPoint t)) *
        h15DirectAdditiveReducedUnitPhase sign r u q))

end NBMellinTools.NB12
