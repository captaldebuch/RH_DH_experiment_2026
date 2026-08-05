/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryCollision

/-!
# NB12zt: even-modulus aliases and the signed dispersion gate

The H15 boundary transform uses the doubled additive character.  For an
even modulus, multiplication by two is not injective, but every frequency
has at most two preimages.  This file proves the resulting uniform
factor-two Parseval loss for every positive modulus.

The estimate is then lifted to the exact correction-preserving boundary
coefficients.  The final section packages the genuinely missing input as a
signed cross-`(q,d)` dispersion estimate relative to the complete frequency
energy.  No cross-modulus cancellation is asserted here.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## The two-torsion fiber -/

/-- An element killed by multiplication by two in `ZMod q` is either zero
or the half-modulus class.  The second alternative can coincide with zero
for odd `q`; the statement is deliberately uniform. -/
theorem h15TwoTorsion_eq_zero_or_eq_half
    (q : ℕ) [NeZero q] {z : ZMod q} (hz : 2 * z = 0) :
    z = 0 ∨ z = (q / 2 : ℕ) := by
  have hneg : -z = z := by
    rw [neg_eq_iff_add_eq_zero, ← two_mul]
    exact hz
  rcases (ZMod.neg_eq_self_iff z).mp hneg with hz0 | hval
  · exact Or.inl hz0
  · right
    apply ZMod.val_injective q
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    · omega
    · exact Nat.div_lt_self (NeZero.pos q) (by omega)

/-- Every fiber of the doubled-frequency map on `ZMod q` has cardinality
at most two. -/
theorem card_h15DoubleFrequencyFiber_le_two
    (q : ℕ) [NeZero q] (s : ZMod q) :
    ((Finset.univ : Finset (ZMod q)).filter
      (fun r : ZMod q => 2 * r = s)).card ≤ 2 := by
  classical
  by_cases hempty :
      ((Finset.univ : Finset (ZMod q)).filter
        (fun r : ZMod q => 2 * r = s)) = ∅
  · simp [hempty]
  · obtain ⟨r₀, hr₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hr₀eq : 2 * r₀ = s := (Finset.mem_filter.mp hr₀).2
    calc
      ((Finset.univ : Finset (ZMod q)).filter
          (fun r : ZMod q => 2 * r = s)).card ≤
          ({r₀, r₀ + (q / 2 : ℕ)} : Finset (ZMod q)).card := by
        apply Finset.card_le_card
        intro r hr
        have hreq : 2 * r = s := (Finset.mem_filter.mp hr).2
        have hker : 2 * (r - r₀) = 0 := by
          rw [mul_sub, hreq, hr₀eq, sub_self]
        rcases h15TwoTorsion_eq_zero_or_eq_half q hker with hz | hh
        · have : r = r₀ := sub_eq_zero.mp hz
          simp [this]
        · have : r = r₀ + (q / 2 : ℕ) := by
            rw [sub_eq_iff_eq_add] at hh
            simpa [add_comm] using hh
          simp [this]
      _ ≤ 2 := Finset.card_le_two

/-! ## Ordinary Parseval and doubled-frequency comparison -/

/-- Orthogonality for the ordinary finite Fourier character. -/
theorem sum_h15OrdinaryCharacterPair
    (q : ℕ) [NeZero q] (x y : ZMod q) :
    ∑ r : ZMod q,
        conj (ZMod.stdAddChar (r * x)) *
          ZMod.stdAddChar (r * y) =
      if y = x then (q : ℂ) else 0 := by
  calc
    (∑ r : ZMod q,
        conj (ZMod.stdAddChar (r * x)) *
          ZMod.stdAddChar (r * y)) =
        ∑ r : ZMod q, ZMod.stdAddChar (r * (y - x)) := by
      apply Fintype.sum_congr
      intro r
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = if y = x then (q : ℂ) else 0 := by
      by_cases h : y = x
      · subst y
        convert AddChar.sum_mulShift (0 : ZMod q)
          (ZMod.isPrimitive_stdAddChar q) using 1 <;> simp
      · rw [if_neg h]
        simpa [sub_ne_zero.mpr h] using AddChar.sum_mulShift (y - x)
          (ZMod.isPrimitive_stdAddChar q)

/-- Ordinary finite Parseval for the additive character normalization used
by the H15 boundary. -/
theorem sum_normSq_h15OrdinaryFourier
    (q : ℕ) [NeZero q] (c : ZMod q → ℂ) :
    ∑ r : ZMod q,
        Complex.normSq
          (∑ x : ZMod q, c x * ZMod.stdAddChar (r * x)) =
      (q : ℝ) * ∑ x : ZMod q, Complex.normSq (c x) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  calc
    (∑ r : ZMod q,
        (conj (∑ x : ZMod q, c x * ZMod.stdAddChar (r * x))) *
          (∑ y : ZMod q, c y * ZMod.stdAddChar (r * y))) =
        ∑ r : ZMod q, ∑ x : ZMod q, ∑ y : ZMod q,
          (conj (c x) * c y) *
            (conj (ZMod.stdAddChar (r * x)) *
              ZMod.stdAddChar (r * y)) := by
      apply Fintype.sum_congr
      intro r
      simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      apply Fintype.sum_congr
      intro x
      apply Fintype.sum_congr
      intro y
      ring
    _ = ∑ x : ZMod q, ∑ y : ZMod q,
          (conj (c x) * c y) *
            (∑ r : ZMod q,
              conj (ZMod.stdAddChar (r * x)) *
                ZMod.stdAddChar (r * y)) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro y
      rw [Finset.mul_sum]
    _ = ∑ x : ZMod q, ∑ y : ZMod q,
          conj (c x) * c y * (if y = x then (q : ℂ) else 0) := by
      simp_rw [sum_h15OrdinaryCharacterPair]
    _ = (q : ℂ) * ∑ x : ZMod q, conj (c x) * c x := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte]
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro x
      ring

/-- Pullback by the doubled-frequency map costs at most its maximal fiber
cardinality, namely two. -/
theorem sum_comp_h15DoubleFrequency_le_two_mul_sum
    (q : ℕ) [NeZero q] (f : ZMod q → ℝ)
    (hf : ∀ s, 0 ≤ f s) :
    ∑ r : ZMod q, f (2 * r) ≤ 2 * ∑ s : ZMod q, f s := by
  classical
  calc
    (∑ r : ZMod q, f (2 * r)) =
        ∑ s : ZMod q,
          ∑ r ∈ (Finset.univ : Finset (ZMod q)) with 2 * r = s,
            f (2 * r) := by
      symm
      exact Finset.sum_fiberwise
        (Finset.univ : Finset (ZMod q)) (fun r => 2 * r)
          (fun r => f (2 * r))
    _ = ∑ s : ZMod q,
          (((Finset.univ : Finset (ZMod q)).filter
            (fun r : ZMod q => 2 * r = s)).card : ℝ) * f s := by
      apply Fintype.sum_congr
      intro s
      calc
        (∑ r ∈ (Finset.univ : Finset (ZMod q)) with 2 * r = s,
            f (2 * r)) =
            ∑ _r ∈ (Finset.univ : Finset (ZMod q)).filter
              (fun r : ZMod q => 2 * r = s), f s := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [(Finset.mem_filter.mp hr).2]
        _ = (((Finset.univ : Finset (ZMod q)).filter
              (fun r : ZMod q => 2 * r = s)).card : ℝ) * f s := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ s : ZMod q, 2 * f s := by
      apply Finset.sum_le_sum
      intro s _hs
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_h15DoubleFrequencyFiber_le_two q s
      · exact hf s
    _ = 2 * ∑ s : ZMod q, f s := by rw [Finset.mul_sum]

/-- Uniform Parseval bound for the doubled H15 character.  Odd moduli have
factor one; even moduli cost at most the sharp two-torsion factor two. -/
theorem sum_normSq_h15DoubledFourier_le_two_mul
    (q : ℕ) [NeZero q] (c : ZMod q → ℂ) :
    ∑ r : ZMod q,
        Complex.normSq
          (∑ x : ZMod q,
            c x * ZMod.stdAddChar ((2 * r) * x)) ≤
      2 * (q : ℝ) * ∑ x : ZMod q, Complex.normSq (c x) := by
  calc
    (∑ r : ZMod q,
        Complex.normSq
          (∑ x : ZMod q,
            c x * ZMod.stdAddChar ((2 * r) * x))) ≤
        2 * ∑ s : ZMod q,
          Complex.normSq
            (∑ x : ZMod q, c x * ZMod.stdAddChar (s * x)) := by
      exact sum_comp_h15DoubleFrequency_le_two_mul_sum q
        (fun s => Complex.normSq
          (∑ x : ZMod q, c x * ZMod.stdAddChar (s * x)))
        (fun s => Complex.normSq_nonneg _)
    _ = 2 * ((q : ℝ) * ∑ x : ZMod q, Complex.normSq (c x)) := by
      rw [sum_normSq_h15OrdinaryFourier]
    _ = 2 * (q : ℝ) * ∑ x : ZMod q, Complex.normSq (c x) := by ring

/-! ## Uniform H15 boundary estimates -/

/-- The exact boundary mean square for every positive modulus, including
the even two-torsion aliases. -/
theorem h15NormalizedBoundaryFourierMeanSquare_le_two_mul_residueL2Mass
    (N g U L q d : ℕ) [NeZero q] :
    h15NormalizedBoundaryFourierMeanSquare N g U L q d ≤
      2 * (q : ℝ) * h15NormalizedBoundaryResidueL2Mass N g U L q d := by
  unfold h15NormalizedBoundaryFourierMeanSquare
    h15NormalizedBoundaryFourierSum
    h15NormalizedBoundaryResidueL2Mass
  exact sum_normSq_h15DoubledFourier_le_two_mul q
    (h15NormalizedBoundaryResidueCoefficient N g U L q d)

/-- Combining the alias and endpoint-collision costs gives the uniform
factor-four point-mass estimate. -/
theorem h15NormalizedBoundaryFourierMeanSquare_le_four_mul_pointL2Mass
    (N g U L q d : ℕ) [NeZero q]
    (hL : 0 < L) (hq : 0 < q) (hLq : Nat.Coprime L q) :
    h15NormalizedBoundaryFourierMeanSquare N g U L q d ≤
      4 * (q : ℝ) * h15NormalizedBoundaryPointL2Mass N g U L q d := by
  calc
    h15NormalizedBoundaryFourierMeanSquare N g U L q d ≤
        2 * (q : ℝ) *
          h15NormalizedBoundaryResidueL2Mass N g U L q d :=
      h15NormalizedBoundaryFourierMeanSquare_le_two_mul_residueL2Mass
        N g U L q d
    _ ≤ 2 * (q : ℝ) *
        (2 * h15NormalizedBoundaryPointL2Mass N g U L q d) := by
      gcongr
      exact h15NormalizedBoundaryResidueL2Mass_le_two_mul_pointL2Mass
        N g U L q d hL hq hLq
    _ = 4 * (q : ℝ) *
        h15NormalizedBoundaryPointL2Mass N g U L q d := by ring

/-- Fully explicit all-modulus mean-square estimate. -/
theorem h15NormalizedBoundaryFourierMeanSquare_le_explicit
    (N g U L q d : ℕ) [NeZero q]
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hL : 0 < L) (hq : 0 < q) (hLq : Nat.Coprime L q) :
    h15NormalizedBoundaryFourierMeanSquare N g U L q d ≤
      (8 * q * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 := by
  calc
    h15NormalizedBoundaryFourierMeanSquare N g U L q d ≤
        4 * (q : ℝ) *
          h15NormalizedBoundaryPointL2Mass N g U L q d :=
      h15NormalizedBoundaryFourierMeanSquare_le_four_mul_pointL2Mass
        N g U L q d hL hq hLq
    _ ≤ 4 * (q : ℝ) *
        ((2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 4) := by
      gcongr
      exact h15NormalizedBoundaryPointL2Mass_le hN hg hU hL hq
    _ = (8 * q * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 := by ring

/-- Uniform fixed-frequency consequence.  It retains the same balanced
power scale as the odd-modulus stop test. -/
theorem sq_h15NormalizedProgressionCoupledBoundaryPointRow_le_explicit
    (N g r U L q d : ℕ)
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hL : 0 < L) (hq : 0 < q) (hLq : Nat.Coprime L q) :
    (h15NormalizedProgressionCoupledBoundaryPointRow
      N g r U L q d) ^ 2 ≤
      (8 * q * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 := by
  letI : NeZero q := ⟨hq.ne'⟩
  exact
    (sq_h15NormalizedProgressionCoupledBoundaryPointRow_le_meanSquare
      N g r U L q d hq).trans
      (h15NormalizedBoundaryFourierMeanSquare_le_explicit
        N g U L q d hN hg hU hL hq hLq)

/-! ## The remaining signed cross-modulus gate -/

/-- Instance-free row-frequency energy. -/
noncomputable def h15NormalizedBoundaryFourierMeanSquareValue
    (N g U L q d : ℕ) : ℝ :=
  if hq : 0 < q then
    letI : NeZero q := ⟨hq.ne'⟩
    h15NormalizedBoundaryFourierMeanSquare N g U L q d
  else 0

theorem h15NormalizedBoundaryFourierMeanSquareValue_nonneg
    (N g U L q d : ℕ) :
    0 ≤ h15NormalizedBoundaryFourierMeanSquareValue N g U L q d := by
  unfold h15NormalizedBoundaryFourierMeanSquareValue
  split_ifs
  · exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  · exact le_rfl

/-- Sum of the complete per-row frequency energies over the active
cross-`(q,d)` incidence set.  This is a nonnegative normalization, not an
absolute-value replacement for the signed boundary aggregate. -/
noncomputable def h15NormalizedBoundaryCrossModulusFrequencyEnergy
    (N g U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedBoundaryFourierMeanSquareValue N g U
        (h15SquareDivisorProgressionModulus g d) q d

theorem h15NormalizedBoundaryCrossModulusFrequencyEnergy_nonneg
    (N g U Q : ℕ) :
    0 ≤ h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q := by
  unfold h15NormalizedBoundaryCrossModulusFrequencyEnergy
  exact Finset.sum_nonneg (fun _q _hq =>
    Finset.sum_nonneg (fun _d _hd =>
      h15NormalizedBoundaryFourierMeanSquareValue_nonneg _ _ _ _ _ _))

/-- The precise analytic gain still needed after the finite alias audit.
The full correction-preserving boundary is kept inside one signed sum.
`Δ` measures its square relative to the complete cross-modulus frequency
energy; proving a decaying `Δ` is the genuine dispersion problem. -/
def H15CorrectionCoupledCrossModulusFrequencyDispersion
    (N g r U Q : ℕ) (Δ : ℝ) : Prop :=
  0 ≤ Δ ∧
    |h15NormalizedBoundaryFourierAggregate N g r U Q| ^ 2 ≤
      Δ * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q

/-- A signed dispersion gain supplies the existing Fourier boundary gate
with its exact square-root normalization. -/
theorem h15CorrectionCoupledFinalBoundaryFourierEstimate_of_crossModulusDispersion
    {N g r U Q : ℕ} {Δ : ℝ}
    (hdisp :
      H15CorrectionCoupledCrossModulusFrequencyDispersion
        N g r U Q Δ) :
    H15CorrectionCoupledFinalBoundaryFourierEstimate N g r U Q
      (Real.sqrt
        (Δ * h15NormalizedBoundaryCrossModulusFrequencyEnergy N g U Q)) := by
  constructor
  · exact Real.sqrt_nonneg _
  · exact (Real.le_sqrt (abs_nonneg _)
      (mul_nonneg hdisp.1
        (h15NormalizedBoundaryCrossModulusFrequencyEnergy_nonneg N g U Q))).2
      hdisp.2

end NBMellinTools.NB12
