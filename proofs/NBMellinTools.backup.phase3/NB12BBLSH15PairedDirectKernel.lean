/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15DirectAdditiveReassembly

/-!
# NB12zd: the paired direct H15 kernel and its exact cross term

The preceding direct-additive reassembly keeps both Estermann orientations
inside one signed expression.  On the line `s = 3/2 + it` their coefficient
is especially rigid:

`cos (pi s) = i sinh (pi t)`.

Consequently, if `z` denotes the positive additive character, the paired
kernel is

`z + i sinh(pi t) * conj z`.

This file computes its squared modulus exactly.  Complete *unweighted*
reduced-residue families kill the resulting cross term by the involution
`u -> -u`.  The H15 dyadic and Möbius/log-taper weights do not disappear:
they leave an explicit signed weighted Ramanujan correlation.  Thus pairing
the two Estermann orientations does not by itself improve the power threshold
found by the additive-large-sieve stop test; it identifies the next genuine
analytic target.

No cancellation estimate, H15 decay, or Riemann-hypothesis statement is
assumed or proved here.
-/

open scoped BigOperators Topology LSeries.notation
open Complex

namespace NBMellinTools.NB12

/-! ## Exact pointwise paired kernel -/

/-- The hyperbolic coefficient coupling the two direct additive phases on
the three-halves line. -/
noncomputable def h15PairedHyperbolicCoefficient (t : ℝ) : ℝ :=
  Real.sinh (Real.pi * t)

/-- Exact cosine value on the three-halves line. -/
theorem cos_pi_mul_bblsEstermannThreeHalfPoint_eq_sinh_mul_I (t : ℝ) :
    Complex.cos ((Real.pi : ℂ) * bblsEstermannThreeHalfPoint t) =
      (h15PairedHyperbolicCoefficient t : ℂ) * Complex.I := by
  rw [cos_pi_mul_bblsEstermannThreeHalfPoint,
    cos_pi_mul_bblsEstermannCentralPoint]
  simp only [h15PairedHyperbolicCoefficient]
  ring

/-- On a reduced positive-modulus row the negative direct phase is the
inverse of the positive one. -/
theorem h15DirectAdditiveReducedUnitPhase_negative_eq_inv_positive
    (r u q : ℕ) (huq : Nat.Coprime u q) :
    h15DirectAdditiveReducedUnitPhase .negative r u q =
      (h15DirectAdditiveReducedUnitPhase .positive r u q)⁻¹ := by
  rw [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ huq,
    h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ huq]
  by_cases hq : q = 0
  · simp [h15DirectAdditiveUnitPhase, hq]
  · letI : NeZero q := ⟨hq⟩
    simp only [h15DirectAdditiveUnitPhase, hq, dite_false]
    rw [show (-(u : ZMod q)) * (r : ZMod q) =
        -((u : ZMod q) * (r : ZMod q)) by ring,
      AddChar.map_neg_eq_inv]

/-- Every positive direct phase on a reduced positive-modulus row has
complex norm-square one. -/
theorem normSq_h15DirectAdditiveReducedUnitPhase_positive
    (r u q : ℕ) (hq : 0 < q) (huq : Nat.Coprime u q) :
    Complex.normSq
        (h15DirectAdditiveReducedUnitPhase .positive r u q) = 1 := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ huq]
  unfold h15DirectAdditiveUnitPhase
  simp only [hq.ne', dite_false]
  rw [ZMod.stdAddChar_apply]
  exact Circle.normSq_coe _

/-- On a reduced positive-modulus row the negative direct phase is the
complex conjugate of the positive one. -/
theorem h15DirectAdditiveReducedUnitPhase_negative_eq_conj_positive
    (r u q : ℕ) (hq : 0 < q) (huq : Nat.Coprime u q) :
    h15DirectAdditiveReducedUnitPhase .negative r u q =
      starRingEnd ℂ
        (h15DirectAdditiveReducedUnitPhase .positive r u q) := by
  rw [h15DirectAdditiveReducedUnitPhase_negative_eq_inv_positive r u q huq]
  apply Complex.inv_eq_conj
  rw [Complex.norm_def,
    normSq_h15DirectAdditiveReducedUnitPhase_positive r u q hq huq,
    Real.sqrt_one]

/-- The paired direct additive kernel which occurs in the exact H15
fixed-height reassembly. -/
noncomputable def h15PairedDirectKernel
    (t : ℝ) (r u q : ℕ) : ℂ :=
  h15DirectAdditiveReducedUnitPhase .positive r u q +
    Complex.cos
        ((Real.pi : ℂ) * bblsEstermannThreeHalfPoint t) *
      h15DirectAdditiveReducedUnitPhase .negative r u q

/-- Exact conjugate-phase form of the paired kernel. -/
theorem h15PairedDirectKernel_eq_phase_add_sinh_mul_I_mul_conj
    (t : ℝ) (r u q : ℕ) (hq : 0 < q) (huq : Nat.Coprime u q) :
    h15PairedDirectKernel t r u q =
      h15DirectAdditiveReducedUnitPhase .positive r u q +
        (h15PairedHyperbolicCoefficient t : ℂ) * Complex.I *
          starRingEnd ℂ
            (h15DirectAdditiveReducedUnitPhase .positive r u q) := by
  unfold h15PairedDirectKernel
  rw [cos_pi_mul_bblsEstermannThreeHalfPoint_eq_sinh_mul_I,
    h15DirectAdditiveReducedUnitPhase_negative_eq_conj_positive
      r u q hq huq]

/-- Algebraic norm-square identity behind the H15 paired-kernel stop test.
The hypothesis says that `z` is on the unit circle. -/
theorem normSq_phase_add_real_mul_I_mul_conj
    (z : ℂ) (S : ℝ) (hz : Complex.normSq z = 1) :
    Complex.normSq (z + (S : ℂ) * Complex.I * starRingEnd ℂ z) =
      1 + S ^ 2 + 2 * S * (z ^ 2).im := by
  rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_conj, hz]
  simp only [Complex.normSq_ofReal, Complex.normSq_I, mul_one]
  simp [Complex.mul_re, Complex.mul_im, pow_two]
  ring

/-- Exact norm-square of the genuine paired direct H15 phase.  The final
term is the signed cross-orientation correlation which must remain coupled
to the arithmetic weights. -/
theorem normSq_h15PairedDirectKernel
    (t : ℝ) (r u q : ℕ) (hq : 0 < q) (huq : Nat.Coprime u q) :
    Complex.normSq (h15PairedDirectKernel t r u q) =
      1 + h15PairedHyperbolicCoefficient t ^ 2 +
        2 * h15PairedHyperbolicCoefficient t *
          ((h15DirectAdditiveReducedUnitPhase .positive r u q) ^ 2).im := by
  rw [h15PairedDirectKernel_eq_phase_add_sinh_mul_I_mul_conj
    t r u q hq huq]
  exact normSq_phase_add_real_mul_I_mul_conj _ _
    (normSq_h15DirectAdditiveReducedUnitPhase_positive r u q hq huq)

/-! ## Complete reduced-residue cancellation -/

/-- The imaginary part of a complete reduced-residue additive-character
sum is zero.  This is the finite involution `u -> -u`; no analytic estimate
is involved. -/
theorem sum_units_stdAddChar_im_eq_zero
    {q : ℕ} [NeZero q] (c : ZMod q) :
    (∑ u : (ZMod q)ˣ,
        (ZMod.stdAddChar (c * (u : ZMod q))).im) = 0 := by
  let f : (ZMod q)ˣ → ℝ := fun u =>
    (ZMod.stdAddChar (c * (u : ZMod q))).im
  have hneg (u : (ZMod q)ˣ) : f (-u) = -f u := by
    unfold f
    rw [show c * ((-u : (ZMod q)ˣ) : ZMod q) =
        -(c * (u : ZMod q)) by simp]
    rw [AddChar.map_neg_eq_inv, Complex.inv_im]
    have hnorm :
        Complex.normSq (ZMod.stdAddChar (c * (u : ZMod q))) = 1 := by
      rw [ZMod.stdAddChar_apply]
      exact Circle.normSq_coe _
    rw [hnorm, div_one]
  have hreindex : (∑ u : (ZMod q)ˣ, f (-u)) = ∑ u : (ZMod q)ˣ, f u := by
    exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
  have hself : (∑ u : (ZMod q)ˣ, f u) = -∑ u : (ZMod q)ˣ, f u := by
    calc
      (∑ u : (ZMod q)ˣ, f u) = ∑ u : (ZMod q)ˣ, f (-u) := hreindex.symm
      _ = ∑ u : (ZMod q)ˣ, -f u := by
        apply Finset.sum_congr rfl
        intro u _
        exact hneg u
      _ = -∑ u : (ZMod q)ˣ, f u := by simp
  have hzero : (∑ u : (ZMod q)ˣ, f u) = 0 := by linarith
  simpa [f] using hzero

/-- The squared positive phases have zero total imaginary part on a complete
reduced-residue system.  Equivalently, the relevant Ramanujan cross mode is
real. -/
theorem sum_units_sq_stdAddChar_im_eq_zero
    {q : ℕ} [NeZero q] (r : ZMod q) :
    (∑ u : (ZMod q)ˣ,
        ((ZMod.stdAddChar ((u : ZMod q) * r) : ℂ) ^ 2).im) = 0 := by
  calc
    (∑ u : (ZMod q)ˣ,
        ((ZMod.stdAddChar ((u : ZMod q) * r) : ℂ) ^ 2).im) =
      ∑ u : (ZMod q)ˣ,
        (ZMod.stdAddChar ((2 * r) * (u : ZMod q))).im := by
          apply Finset.sum_congr rfl
          intro u _
          congr 1
          rw [pow_two, ← AddChar.map_add_eq_mul]
          apply congrArg ZMod.stdAddChar
          ring
    _ = 0 := sum_units_stdAddChar_im_eq_zero (2 * r)

/-! ## The weighted H15 cross term -/

/-- The reduced part of a natural dyadic numerator block for a fixed
modulus. -/
def h15ReducedDyadicNumeratorBlock (U q : ℕ) : Finset ℕ :=
  (h15BettinChandeeNatBlock U).filter fun u => Nat.Coprime u q

/-- Squared coefficient mass on a reduced dyadic numerator block. -/
noncomputable def h15PairedDirectCoefficientMass
    (U q : ℕ) (alpha : ℕ → ℂ) : ℝ :=
  ∑ u ∈ h15ReducedDyadicNumeratorBlock U q,
    Complex.normSq (alpha u)

/-- The signed weighted Ramanujan correlation left by pairing the two
Estermann orientations.  Unlike its complete unweighted counterpart, this
quantity has no formal reason to vanish. -/
noncomputable def h15PairedDirectCrossCorrelation
    (r U q : ℕ) (alpha : ℕ → ℂ) : ℝ :=
  ∑ u ∈ h15ReducedDyadicNumeratorBlock U q,
    Complex.normSq (alpha u) *
      ((h15DirectAdditiveReducedUnitPhase .positive r u q) ^ 2).im

/-- Exact paired-kernel mass on a reduced dyadic numerator block. -/
noncomputable def h15PairedDirectWeightedMass
    (t : ℝ) (r U q : ℕ) (alpha : ℕ → ℂ) : ℝ :=
  ∑ u ∈ h15ReducedDyadicNumeratorBlock U q,
    Complex.normSq (alpha u * h15PairedDirectKernel t r u q)

/-- The weighted cross correlation admits the tautological coefficient-mass
majorant.  This is deliberately recorded as a stop test: it gives no saving
over the baseline mass and therefore cannot close H15 on its own. -/
theorem abs_h15PairedDirectCrossCorrelation_le_coefficientMass
    (r U q : ℕ) (alpha : ℕ → ℂ) (hq : 0 < q) :
    |h15PairedDirectCrossCorrelation r U q alpha| ≤
      h15PairedDirectCoefficientMass U q alpha := by
  unfold h15PairedDirectCrossCorrelation h15PairedDirectCoefficientMass
  calc
    |∑ u ∈ h15ReducedDyadicNumeratorBlock U q,
        Complex.normSq (alpha u) *
          ((h15DirectAdditiveReducedUnitPhase .positive r u q) ^ 2).im| ≤
      ∑ u ∈ h15ReducedDyadicNumeratorBlock U q,
        |Complex.normSq (alpha u) *
          ((h15DirectAdditiveReducedUnitPhase .positive r u q) ^ 2).im| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ h15ReducedDyadicNumeratorBlock U q,
        Complex.normSq (alpha u) := by
      apply Finset.sum_le_sum
      intro u hu
      have huq : Nat.Coprime u q := (Finset.mem_filter.mp hu).2
      rw [abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
      apply mul_le_of_le_one_right (Complex.normSq_nonneg _)
      calc
        |((h15DirectAdditiveReducedUnitPhase .positive r u q) ^ 2).im| ≤
            ‖(h15DirectAdditiveReducedUnitPhase .positive r u q) ^ 2‖ :=
          Complex.abs_im_le_norm _
        _ = 1 := by
          rw [norm_pow, Complex.norm_def,
            normSq_h15DirectAdditiveReducedUnitPhase_positive r u q hq huq,
            Real.sqrt_one, one_pow]

/-- Pointwise weighted paired-kernel decomposition. -/
theorem normSq_weight_mul_h15PairedDirectKernel
    (t : ℝ) (r u q : ℕ) (alpha : ℕ → ℂ)
    (hq : 0 < q) (huq : Nat.Coprime u q) :
    Complex.normSq (alpha u * h15PairedDirectKernel t r u q) =
      Complex.normSq (alpha u) *
          (1 + h15PairedHyperbolicCoefficient t ^ 2) +
        2 * h15PairedHyperbolicCoefficient t *
          (Complex.normSq (alpha u) *
            ((h15DirectAdditiveReducedUnitPhase .positive r u q) ^ 2).im) := by
  rw [Complex.normSq_mul, normSq_h15PairedDirectKernel t r u q hq huq]
  ring

/-- Exact finite mass ledger: baseline coefficient mass plus the signed
weighted cross-orientation correlation. -/
theorem h15PairedDirectWeightedMass_eq_baseline_add_cross
    (t : ℝ) (r U q : ℕ) (alpha : ℕ → ℂ) (hq : 0 < q) :
    h15PairedDirectWeightedMass t r U q alpha =
      (1 + h15PairedHyperbolicCoefficient t ^ 2) *
          h15PairedDirectCoefficientMass U q alpha +
        2 * h15PairedHyperbolicCoefficient t *
          h15PairedDirectCrossCorrelation r U q alpha := by
  unfold h15PairedDirectWeightedMass h15PairedDirectCoefficientMass
    h15PairedDirectCrossCorrelation
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have huq : Nat.Coprime u q :=
    (Finset.mem_filter.mp hu).2
  rw [normSq_weight_mul_h15PairedDirectKernel t r u q alpha hq huq]
  ring

/-- Exact condition under which pairing really removes the cross term on a
given dyadic H15 numerator block. -/
def H15PairedDirectCrossTermCancelsAt
    (r U q : ℕ) (alpha : ℕ → ℂ) : Prop :=
  h15PairedDirectCrossCorrelation r U q alpha = 0

/-- If the signed weighted Ramanujan correlation vanishes, the paired mass
is exactly the baseline mass. -/
theorem h15PairedDirectWeightedMass_eq_baseline_of_crossTerm
    (t : ℝ) (r U q : ℕ) (alpha : ℕ → ℂ) (hq : 0 < q)
    (hcross : H15PairedDirectCrossTermCancelsAt r U q alpha) :
    h15PairedDirectWeightedMass t r U q alpha =
      (1 + h15PairedHyperbolicCoefficient t ^ 2) *
        h15PairedDirectCoefficientMass U q alpha := by
  rw [h15PairedDirectWeightedMass_eq_baseline_add_cross
    t r U q alpha hq]
  change h15PairedDirectCrossCorrelation r U q alpha = 0 at hcross
  rw [hcross, mul_zero, add_zero]

end NBMellinTools.NB12
