/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalSuperperiodBoundary
import Mathlib.Analysis.Fourier.ZMod

/-!
# NB12zr: Fourier folding of the correction-coupled final boundary

Step 4v-j showed that the final boundary has no universal zero mode.  The
next analytic representation folds its exact pointwise coefficients modulo
`q`.  The resulting boundary row is the imaginary part of one finite DFT
with completely explicit, correction-preserving coefficients.

This is the correct entry point for a signed endpoint large-sieve or
mean-square theorem.  No decay estimate is asserted here.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Complex pointwise character sum -/

/-- The complex additive-character lift whose imaginary part is the real
paired cross-mode boundary row. -/
noncomputable def h15NormalizedProgressionCoupledBoundaryComplexRow
    (N g r U L q d : ℕ) [NeZero q] : ℂ :=
  ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
    (h15NormalizedProgressionCoupledBoundaryPointWeight
        N g U L q d u : ℂ) *
      ZMod.stdAddChar
        ((2 * (r : ZMod q)) * (u : ZMod q))

/-- Every point on the final normalized boundary remains reduced modulo its
positive modulus. -/
theorem coprime_of_mem_h15NormalizedSuperperiodBoundarySupport
    {U L q u : ℕ}
    (hu : u ∈ h15NormalizedSuperperiodBoundarySupport U L q) :
    Nat.Coprime u q := by
  have huDyadic := (Finset.mem_sdiff.mp hu).1
  have huReduced := (Finset.mem_filter.mp huDyadic).1
  exact (Finset.mem_filter.mp huReduced).2

/-- The genuine real final-boundary row is exactly the imaginary part of
its complex additive-character lift. -/
theorem h15NormalizedProgressionCoupledBoundaryPointRow_eq_complex_im
    (N g r U L q d : ℕ) (hq : 0 < q) :
    h15NormalizedProgressionCoupledBoundaryPointRow N g r U L q d =
      (letI : NeZero q := ⟨hq.ne'⟩
       h15NormalizedProgressionCoupledBoundaryComplexRow
        N g r U L q d).im := by
  letI : NeZero q := ⟨hq.ne'⟩
  unfold h15NormalizedProgressionCoupledBoundaryPointRow
    h15NormalizedProgressionCoupledBoundaryComplexRow
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
    h15PairedDirectCrossMode_of_coprime r u q
      (coprime_of_mem_h15NormalizedSuperperiodBoundarySupport hu)]

/-! ## Folding modulo `q` -/

/-- All pointwise boundary coefficients with a fixed residue modulo `q`,
including both pieces of the correction weight. -/
noncomputable def h15NormalizedBoundaryResidueCoefficient
    (N g U L q d : ℕ) [NeZero q] (x : ZMod q) : ℂ :=
  ∑ u ∈ (h15NormalizedSuperperiodBoundarySupport U L q).filter
      (fun u : ℕ => (u : ZMod q) = x),
    (h15NormalizedProgressionCoupledBoundaryPointWeight
      N g U L q d u : ℂ)

/-- Finite Fourier sum of the folded endpoint coefficients. -/
noncomputable def h15NormalizedBoundaryFourierSum
    (N g U L q d : ℕ) [NeZero q] (r : ZMod q) : ℂ :=
  ∑ x : ZMod q,
    h15NormalizedBoundaryResidueCoefficient N g U L q d x *
      ZMod.stdAddChar ((2 * r) * x)

/-- Exact fiber collection: folding by the residue coordinate loses no
pointwise coefficient or sign. -/
theorem h15NormalizedProgressionCoupledBoundaryComplexRow_eq_fourierSum
    (N g r U L q d : ℕ) (hq : 0 < q) :
    (letI : NeZero q := ⟨hq.ne'⟩
     h15NormalizedProgressionCoupledBoundaryComplexRow N g r U L q d) =
      (letI : NeZero q := ⟨hq.ne'⟩
       h15NormalizedBoundaryFourierSum N g U L q d (r : ZMod q)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  classical
  unfold h15NormalizedProgressionCoupledBoundaryComplexRow
    h15NormalizedBoundaryFourierSum
    h15NormalizedBoundaryResidueCoefficient
  symm
  calc
    (∑ x : ZMod q,
        (∑ u ∈ (h15NormalizedSuperperiodBoundarySupport U L q).filter
            (fun u : ℕ => (u : ZMod q) = x),
          (h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L q d u : ℂ)) *
          ZMod.stdAddChar ((2 * (r : ZMod q)) * x)) =
        ∑ x : ZMod q,
          ∑ u ∈ (h15NormalizedSuperperiodBoundarySupport U L q).filter
              (fun u : ℕ => (u : ZMod q) = x),
            (h15NormalizedProgressionCoupledBoundaryPointWeight
              N g U L q d u : ℂ) *
              ZMod.stdAddChar ((2 * (r : ZMod q)) * x) := by
      simp_rw [Finset.sum_mul]
    _ = ∑ x : ZMod q,
          ∑ u ∈ (h15NormalizedSuperperiodBoundarySupport U L q).filter
              (fun u : ℕ => (u : ZMod q) = x),
            (h15NormalizedProgressionCoupledBoundaryPointWeight
              N g U L q d u : ℂ) *
              ZMod.stdAddChar
                ((2 * (r : ZMod q)) * (u : ZMod q)) := by
      apply Fintype.sum_congr
      intro x
      apply Finset.sum_congr rfl
      intro u hu
      rw [(Finset.mem_filter.mp hu).2]
    _ = ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
          (h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L q d u : ℂ) *
            ZMod.stdAddChar
              ((2 * (r : ZMod q)) * (u : ZMod q)) :=
      Finset.sum_fiberwise
        (h15NormalizedSuperperiodBoundarySupport U L q)
        (fun u : ℕ => (u : ZMod q))
        (fun u =>
          (h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L q d u : ℂ) *
            ZMod.stdAddChar
              ((2 * (r : ZMod q)) * (u : ZMod q)))

/-- Exact Step 4v-k Fourier bridge for one H15 boundary row. -/
theorem h15NormalizedProgressionCoupledBoundaryPointRow_eq_fourierSum_im
    (N g r U L q d : ℕ) (hq : 0 < q) :
    h15NormalizedProgressionCoupledBoundaryPointRow N g r U L q d =
      (letI : NeZero q := ⟨hq.ne'⟩
       h15NormalizedBoundaryFourierSum N g U L q d (r : ZMod q)).im := by
  rw [h15NormalizedProgressionCoupledBoundaryPointRow_eq_complex_im
      N g r U L q d hq,
    h15NormalizedProgressionCoupledBoundaryComplexRow_eq_fourierSum
      N g r U L q d hq]

/-! ## Exact frequency aliasing -/

/-- Orthogonality kernel for the doubled H15 frequency.  Unlike the ordinary
DFT kernel, it detects `2 * (y - x) = 0`; this distinction matters exactly
when the modulus is even. -/
theorem sum_h15DoubledCharacterPair
    (q : ℕ) [NeZero q] (x y : ZMod q) :
    ∑ r : ZMod q,
        conj (ZMod.stdAddChar ((2 * r) * x)) *
          ZMod.stdAddChar ((2 * r) * y) =
      if 2 * (y - x) = 0 then (q : ℂ) else 0 := by
  calc
    (∑ r : ZMod q,
        conj (ZMod.stdAddChar ((2 * r) * x)) *
          ZMod.stdAddChar ((2 * r) * y)) =
        ∑ r : ZMod q, ZMod.stdAddChar (r * (2 * (y - x))) := by
      apply Fintype.sum_congr
      intro r
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = if 2 * (y - x) = 0 then (q : ℂ) else 0 := by
      simpa using AddChar.sum_mulShift (2 * (y - x))
        (ZMod.isPrimitive_stdAddChar q)

/-- Exact mean-square ledger for the doubled finite transform.  The right
side displays the only possible cross terms: residue classes separated by
the two-torsion of `ZMod q`. -/
theorem sum_normSq_h15DoubledFourier
    (q : ℕ) [NeZero q] (c : ZMod q → ℂ) :
    ((∑ r : ZMod q,
        Complex.normSq
          (∑ x : ZMod q,
            c x * ZMod.stdAddChar ((2 * r) * x))) : ℝ) =
      (∑ x : ZMod q, ∑ y : ZMod q,
        conj (c x) * c y *
          (if 2 * (y - x) = 0 then (q : ℂ) else 0)) := by
  calc
    ((∑ r : ZMod q,
        Complex.normSq
          (∑ x : ZMod q,
            c x * ZMod.stdAddChar ((2 * r) * x))) : ℝ) =
        ∑ r : ZMod q,
          (conj (∑ x : ZMod q,
              c x * ZMod.stdAddChar ((2 * r) * x))) *
            (∑ y : ZMod q,
              c y * ZMod.stdAddChar ((2 * r) * y)) := by
      push_cast
      simp_rw [Complex.normSq_eq_conj_mul_self]
    _ = ∑ r : ZMod q, ∑ x : ZMod q, ∑ y : ZMod q,
          (conj (c x) * c y) *
            (conj (ZMod.stdAddChar ((2 * r) * x)) *
              ZMod.stdAddChar ((2 * r) * y)) := by
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
              conj (ZMod.stdAddChar ((2 * r) * x)) *
                ZMod.stdAddChar ((2 * r) * y)) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro y
      rw [Finset.mul_sum]
    _ = ∑ x : ZMod q, ∑ y : ZMod q,
          conj (c x) * c y *
            (if 2 * (y - x) = 0 then (q : ℂ) else 0) := by
      simp_rw [sum_h15DoubledCharacterPair]

/-- For odd modulus, multiplication by two is invertible and the alias
ledger collapses to the ordinary Parseval identity. -/
theorem sum_normSq_h15DoubledFourier_of_odd
    (q : ℕ) [NeZero q] (hqOdd : Odd q) (c : ZMod q → ℂ) :
    ∑ r : ZMod q,
        Complex.normSq
          (∑ x : ZMod q,
            c x * ZMod.stdAddChar ((2 * r) * x)) =
      (q : ℝ) * ∑ x : ZMod q, Complex.normSq (c x) := by
  have htwo : IsUnit (2 : ZMod q) :=
    (ZMod.isUnit_iff_coprime 2 q).2 hqOdd.coprime_two_left
  have halias (x y : ZMod q) : 2 * (y - x) = 0 ↔ y = x := by
    rw [htwo.mul_right_eq_zero, sub_eq_zero]
  apply Complex.ofReal_injective
  rw [sum_normSq_h15DoubledFourier]
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  simp_rw [halias]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro x
  ring

/-! ## Row mean squares and the aggregate gate -/

/-- Squared `ℓ²` mass of the correction-preserving coefficients after
folding the final boundary modulo `q`. -/
noncomputable def h15NormalizedBoundaryResidueL2Mass
    (N g U L q d : ℕ) [NeZero q] : ℝ :=
  ∑ x : ZMod q,
    Complex.normSq
      (h15NormalizedBoundaryResidueCoefficient N g U L q d x)

/-- Frequency mean square of the exact doubled-character boundary row. -/
noncomputable def h15NormalizedBoundaryFourierMeanSquare
    (N g U L q d : ℕ) [NeZero q] : ℝ :=
  ∑ r : ZMod q,
    Complex.normSq (h15NormalizedBoundaryFourierSum N g U L q d r)

/-- Exact alias ledger for the H15 boundary coefficients. -/
theorem h15NormalizedBoundaryFourierMeanSquare_eq_aliasLedger
    (N g U L q d : ℕ) [NeZero q] :
    (h15NormalizedBoundaryFourierMeanSquare N g U L q d : ℂ) =
      ∑ x : ZMod q, ∑ y : ZMod q,
        conj (h15NormalizedBoundaryResidueCoefficient N g U L q d x) *
          h15NormalizedBoundaryResidueCoefficient N g U L q d y *
          (if 2 * (y - x) = 0 then (q : ℂ) else 0) := by
  unfold h15NormalizedBoundaryFourierMeanSquare
    h15NormalizedBoundaryFourierSum
  exact sum_normSq_h15DoubledFourier q
    (h15NormalizedBoundaryResidueCoefficient N g U L q d)

/-- Odd moduli have no doubled-frequency aliases, so the boundary transform
has the usual exact Parseval normalization. -/
theorem h15NormalizedBoundaryFourierMeanSquare_eq_of_odd
    (N g U L q d : ℕ) [NeZero q] (hqOdd : Odd q) :
    h15NormalizedBoundaryFourierMeanSquare N g U L q d =
      (q : ℝ) * h15NormalizedBoundaryResidueL2Mass N g U L q d := by
  unfold h15NormalizedBoundaryFourierMeanSquare
    h15NormalizedBoundaryFourierSum
    h15NormalizedBoundaryResidueL2Mass
  exact sum_normSq_h15DoubledFourier_of_odd q hqOdd
    (h15NormalizedBoundaryResidueCoefficient N g U L q d)

/-- Instance-free value of one Fourier row.  The zero-modulus branch is
present only so that rows can be assembled before positivity of a supported
modulus is introduced. -/
noncomputable def h15NormalizedBoundaryFourierRowValue
    (N g r U L q d : ℕ) : ℝ :=
  if hq : 0 < q then
    letI : NeZero q := ⟨hq.ne'⟩
    (h15NormalizedBoundaryFourierSum
      N g U L q d (r : ZMod q)).im
  else 0

/-- On every positive modulus, the instance-free Fourier value is the
original correction-coupled point row. -/
theorem h15NormalizedBoundaryFourierRowValue_eq_pointRow
    (N g r U L q d : ℕ) (hq : 0 < q) :
    h15NormalizedBoundaryFourierRowValue N g r U L q d =
      h15NormalizedProgressionCoupledBoundaryPointRow
        N g r U L q d := by
  rw [h15NormalizedBoundaryFourierRowValue, dif_pos hq,
    h15NormalizedProgressionCoupledBoundaryPointRow_eq_fourierSum_im
      N g r U L q d hq]

/-- The complete active-incidence final boundary, expressed through the
finite Fourier rows without discarding the retained correction weight. -/
noncomputable def h15NormalizedBoundaryFourierAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
      h15NormalizedBoundaryFourierRowValue N g r U
        (h15SquareDivisorProgressionModulus g d) q d

/-- Exact aggregate Fourier bridge.  It is an identity of the full signed
boundary, not a termwise estimate. -/
theorem h15NormalizedBoundaryFourierAggregate_eq_pointAggregate
    {N g r U Q : ℕ} (hQ : 0 < Q) :
    h15NormalizedBoundaryFourierAggregate N g r U Q =
      h15NormalizedProgressionCoupledBoundaryPointAggregate N g r U Q := by
  unfold h15NormalizedBoundaryFourierAggregate
    h15NormalizedProgressionCoupledBoundaryPointAggregate
  apply Finset.sum_congr rfl
  intro q hqMem
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  apply Finset.sum_congr rfl
  intro d _hd
  rw [h15NormalizedBoundaryFourierRowValue_eq_pointRow
    N g r U (h15SquareDivisorProgressionModulus g d) q d hqPos]

/-- Signed Fourier form of the remaining final-boundary estimate. -/
def H15CorrectionCoupledFinalBoundaryFourierEstimate
    (N g r U Q : ℕ) (B : ℝ) : Prop :=
  0 ≤ B ∧ |h15NormalizedBoundaryFourierAggregate N g r U Q| ≤ B

/-- The Fourier gate is exactly sufficient for the pointwise gate used by
the two-Abel residual theorem. -/
theorem h15CorrectionCoupledFinalBoundaryEstimate_of_fourier
    {N g r U Q : ℕ} {B : ℝ} (hQ : 0 < Q)
    (hfourier :
      H15CorrectionCoupledFinalBoundaryFourierEstimate N g r U Q B) :
    H15CorrectionCoupledFinalBoundaryEstimate N g r U Q B := by
  constructor
  · exact hfourier.1
  · rw [← h15NormalizedBoundaryFourierAggregate_eq_pointAggregate hQ]
    exact hfourier.2

/-- Step 4v-k endpoint theorem: any signed Fourier estimate feeds directly
into the complete residual bound, with both Abel-prefix costs unchanged. -/
theorem abs_h15NormalizedProgressionRowToPointwiseResidual_le_fourierBoundaryGate
    {N g r U Q : ℕ} {P₁ P₂ B : ℝ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hQ : 0 < Q)
    (hprefix₁ : H15NormalizedProgressionAbelPrefixBound N g r U Q P₁)
    (hprefix₂ : H15NormalizedRowSuperperiodAbelPrefixBound N g r U Q P₂)
    (hfourier :
      H15CorrectionCoupledFinalBoundaryFourierEstimate N g r U Q B) :
    |h15NormalizedProgressionRowToPointwiseResidual N g r U Q| ≤
      2 * (g.divisors.card : ℝ) * P₁ +
        4 * (g.divisors.card : ℝ) * P₂ + B := by
  exact abs_h15NormalizedProgressionRowToPointwiseResidual_le_finalBoundaryGate
    hN hg hU hQ hprefix₁ hprefix₂
      (h15CorrectionCoupledFinalBoundaryEstimate_of_fourier hQ hfourier)

end NBMellinTools.NB12
