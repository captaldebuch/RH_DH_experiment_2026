/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFECrossRowResidueAlignment

/-!
# NB12zzzj: global signed phase populations after the functional equation

The preceding support audit shows that the linear missing-residue trace and
the ordered cross-row dispersion have disjoint literal supports.  This file
therefore stops searching for a termwise match and prepares the genuinely
global boundary-transfer problem.

Every ordered cross-row term is factored into

* a complex arithmetic scalar, containing the Laurent weight, gamma factor,
  damping, modulus twist, and frequency twist; and
* a universal paired-phase kernel depending only on the two residue keys.

The arithmetic scalars are then collected exactly by ordered residue-key
pairs.  Finally, the paired kernel is split into its four positive/negative
orientation populations.  All four populations remain inside the same signed
finite sum.  This is the canonical input for a reciprocity, Voronoi, or
bilinear spectral transformation; no absolute value or cancellation estimate
is introduced here.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Residue invariance of the complete paired phase -/

/-- Reduction of the inverse coordinate modulo a positive modulus preserves
each reduced direct additive phase, including its zero extension away from
coprime rows. -/
theorem h15DirectAdditiveReducedUnitPhase_mod
    (sign : BettinChandeeUnitSign) (r u q : ℕ) (hq : 0 < q) :
    h15DirectAdditiveReducedUnitPhase sign r (u % q) q =
      h15DirectAdditiveReducedUnitPhase sign r u q := by
  by_cases hcop : Nat.Coprime u q
  · have hcopmod : Nat.Coprime (u % q) q := by
      rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec q u, Nat.gcd_comm]
      exact hcop.gcd_eq_one
    rw [h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ hcopmod,
      h15DirectAdditiveReducedUnitPhase_of_coprime _ _ _ _ hcop]
    letI : NeZero q := ⟨hq.ne'⟩
    simp only [h15DirectAdditiveUnitPhase, hq.ne', dite_false]
    cases sign <;> simp
  · have hcopmod : ¬ Nat.Coprime (u % q) q := by
      intro hc
      apply hcop
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec q u]
      exact hc.gcd_eq_one
    rw [h15DirectAdditiveReducedUnitPhase_of_not_coprime _ _ _ _ hcopmod,
      h15DirectAdditiveReducedUnitPhase_of_not_coprime _ _ _ _ hcop]

/-- The complete paired direct kernel is a function of the residue class of
its inverse coordinate. -/
theorem h15PairedDirectKernel_mod
    (t : ℝ) (r u q : ℕ) (hq : 0 < q) :
    h15PairedDirectKernel t r (u % q) q =
      h15PairedDirectKernel t r u q := by
  unfold h15PairedDirectKernel
  rw [h15DirectAdditiveReducedUnitPhase_mod .positive r u q hq,
    h15DirectAdditiveReducedUnitPhase_mod .negative r u q hq]

/-! ## Complex arithmetic collection -/

/-- Complex arithmetic coefficient of one ordered Laurent-row pair. -/
noncomputable def h15PostFEOrderedPairScalar
    (n r : ℕ) (t : ℝ)
    (p : H15PostFEOrderedLaurentPairIndex (NB8.logTaperLength n)) : ℂ :=
  conj
      (h15DirectAdditiveTotalRowScalar (NB8.logTaperLength n)
        (h15ContourDamping n) p.1 r t) *
    h15DirectAdditiveTotalRowScalar (NB8.logTaperLength n)
      (h15ContourDamping n) p.2 r t

/-- Universal paired kernel attached to two post-FE residue keys. -/
noncomputable def h15PostFEResiduePairKernel
    (t : ℝ) (r : ℕ) (κ : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  conj (h15PairedDirectKernel t r κ.1.1 κ.1.2) *
    h15PairedDirectKernel t r κ.2.1 κ.2.2

/-- Exact scalar-kernel factorization of one orientation-zero ordered pair.
The orientation hypotheses identify the raw row variables with `(a,q)`; the
positive-modulus hypotheses justify reduction to the residue key. -/
theorem h15PostFEOrderedPairSummand_eq_scalar_mul_residueKernel_re
    (n r : ℕ) (t : ℝ)
    (p : H15PostFEOrderedLaurentPairIndex (NB8.logTaperLength n))
    (hz1 : h15LaurentOrientation p.1 = 0)
    (hz2 : h15LaurentOrientation p.2 = 0)
    (hq1 : 0 < h15LaurentQ p.1)
    (hq2 : 0 < h15LaurentQ p.2) :
    h15PostFEOrderedPairSummand n r t p =
      (h15PostFEOrderedPairScalar n r t p *
        h15PostFEResiduePairKernel t r
          (h15PostFEOrderedPairResidueKey p)).re := by
  rw [h15PostFEOrderedPairSummand,
    h15DirectAdditiveFixedHeightSummand_eq_scalar_mul_kernel,
    h15DirectAdditiveFixedHeightSummand_eq_scalar_mul_kernel]
  unfold h15PostFEOrderedPairScalar h15PostFEResiduePairKernel
    h15PostFEOrderedPairResidueKey h15PostFEOrientationZeroRowResidueKey
    h15PostFEResidueKey h15OrientationZeroLaurentRowKey
  simp only [h15BettinChandeeInverseVariable,
    h15BettinChandeeModulusVariable, hz1, hz2, if_true]
  rw [h15PairedDirectKernel_mod t r
      (h15LaurentA p.1) (h15LaurentQ p.1) hq1,
    h15PairedDirectKernel_mod t r
      (h15LaurentA p.2) (h15LaurentQ p.2) hq2]
  simp only [map_mul]
  ring_nf

/-- Complex version of finite collection over the image of an arithmetic
key. -/
theorem sum_complex_mul_kernel_eq_sum_image_collected
    {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (key : ι → κ) (coefficient : ι → ℂ)
    (kernel : κ → ℂ) :
    (∑ i ∈ S, coefficient i * kernel (key i)) =
      ∑ k ∈ S.image key,
        (∑ i ∈ S.filter (fun i => key i = k), coefficient i) * kernel k := by
  classical
  calc
    (∑ i ∈ S, coefficient i * kernel (key i)) =
        ∑ k ∈ S.image key,
          ∑ i ∈ S.filter (fun i => key i = k),
            coefficient i * kernel (key i) := by
      rw [Finset.sum_fiberwise_eq_sum_filter]
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · intro hi
          exact ⟨hi, i, hi, rfl⟩
        · exact fun hi => hi.1
      · intro i _hi
        rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]

/-- Complex pair coefficients collected at one ordered pair of residue keys. -/
noncomputable def h15PostFEOrderedPairCollectedScalar
    (n g U Q r : ℕ) (t : ℝ) (κ : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  ∑ p ∈ (h15PostFEOrderedLaurentPairIndices n g U Q).filter
      (fun p => h15PostFEOrderedPairResidueKey p = κ),
    h15PostFEOrderedPairScalar n r t p

/-- Canonical global separation of the ordered off-diagonal into collected
arithmetic scalars and a residue-pair phase kernel. -/
theorem h15OrientationZeroFrequencyOffDiagonal_eq_collectedScalarKernel
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15OrientationZeroFrequencyOffDiagonal n g U Q r t =
      ∑ κ ∈ h15PostFEOrderedPairResidueSupport n g U Q,
        (h15PostFEOrderedPairCollectedScalar n g U Q r t κ *
          h15PostFEResiduePairKernel t r κ).re := by
  rw [h15OrientationZeroFrequencyOffDiagonal_eq_orderedPairSum]
  calc
    (∑ p ∈ h15PostFEOrderedLaurentPairIndices n g U Q,
        h15PostFEOrderedPairSummand n r t p) =
      ∑ p ∈ h15PostFEOrderedLaurentPairIndices n g U Q,
        (h15PostFEOrderedPairScalar n r t p *
          h15PostFEResiduePairKernel t r
            (h15PostFEOrderedPairResidueKey p)).re := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.mem_sigma.mp hp
      have hi1 := hp'.1
      have hi2 := (Finset.mem_erase.mp hp'.2).2
      have hz1 := (mem_h15DoublyLocalizedOrientationZeroIndices.mp hi1).2
      have hz2 := (mem_h15DoublyLocalizedOrientationZeroIndices.mp hi2).2
      have hq1mem := (mem_h15DoublyLocalizedLaurentRowIndices.mp
        (mem_h15DoublyLocalizedOrientationZeroIndices.mp hi1).1).2.2
      have hq2mem := (mem_h15DoublyLocalizedLaurentRowIndices.mp
        (mem_h15DoublyLocalizedOrientationZeroIndices.mp hi2).1).2.2
      have hq1 : 0 < h15LaurentQ p.1 := hQ.trans_le
        (mem_h15BettinChandeeSupportedNatBlock.mp hq1mem).1
      have hq2 : 0 < h15LaurentQ p.2 := hQ.trans_le
        (mem_h15BettinChandeeSupportedNatBlock.mp hq2mem).1
      exact h15PostFEOrderedPairSummand_eq_scalar_mul_residueKernel_re
        n r t p hz1 hz2 hq1 hq2
    _ = _ := by
      have hcollect := sum_complex_mul_kernel_eq_sum_image_collected
        (h15PostFEOrderedLaurentPairIndices n g U Q)
        h15PostFEOrderedPairResidueKey
        (h15PostFEOrderedPairScalar n r t)
        (h15PostFEResiduePairKernel t r)
      have hre := congrArg Complex.re hcollect
      simpa [h15PostFEOrderedPairResidueSupport,
        h15PostFEOrderedPairCollectedScalar] using hre

/-! ## Four signed phase populations -/

/-- One of the two oriented summands in the paired direct kernel. -/
noncomputable def h15PostFEKernelOrientationComponent
    (sign : BettinChandeeUnitSign) (t : ℝ) (r : ℕ)
    (z : ℕ × ℕ) : ℂ :=
  match sign with
  | .positive => h15DirectAdditiveReducedUnitPhase .positive r z.1 z.2
  | .negative =>
      Complex.cos ((Real.pi : ℂ) * bblsEstermannThreeHalfPoint t) *
        h15DirectAdditiveReducedUnitPhase .negative r z.1 z.2

theorem h15PairedDirectKernel_eq_orientationComponents
    (t : ℝ) (r : ℕ) (z : ℕ × ℕ) :
    h15PairedDirectKernel t r z.1 z.2 =
      h15PostFEKernelOrientationComponent .positive t r z +
        h15PostFEKernelOrientationComponent .negative t r z := by
  rfl

/-- One of the four phase populations in a paired-kernel product. -/
noncomputable def h15PostFEResiduePairPhaseComponent
    (left right : BettinChandeeUnitSign) (t : ℝ) (r : ℕ)
    (κ : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  conj (h15PostFEKernelOrientationComponent left t r κ.1) *
    h15PostFEKernelOrientationComponent right t r κ.2

/-- Exact four-population expansion of the residue-pair kernel. -/
theorem h15PostFEResiduePairKernel_eq_four_phaseComponents
    (t : ℝ) (r : ℕ) (κ : (ℕ × ℕ) × (ℕ × ℕ)) :
    h15PostFEResiduePairKernel t r κ =
      h15PostFEResiduePairPhaseComponent .positive .positive t r κ +
      h15PostFEResiduePairPhaseComponent .positive .negative t r κ +
      h15PostFEResiduePairPhaseComponent .negative .positive t r κ +
      h15PostFEResiduePairPhaseComponent .negative .negative t r κ := by
  unfold h15PostFEResiduePairKernel h15PostFEResiduePairPhaseComponent
  rw [h15PairedDirectKernel_eq_orientationComponents,
    h15PairedDirectKernel_eq_orientationComponents]
  simp only [map_add]
  ring

/-- Global signed aggregate of one ordered phase population. -/
noncomputable def h15PostFEOrderedPairPhasePopulation
    (left right : BettinChandeeUnitSign)
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ κ ∈ h15PostFEOrderedPairResidueSupport n g U Q,
    (h15PostFEOrderedPairCollectedScalar n g U Q r t κ *
      h15PostFEResiduePairPhaseComponent left right t r κ).re

/-- The complete ordered post-FE dispersion is exactly the sum of its four
signed orientation populations.  This is the smallest global object on which
a correction-preserving boundary-transfer estimate can act. -/
theorem h15OrientationZeroFrequencyOffDiagonal_eq_four_phasePopulations
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15OrientationZeroFrequencyOffDiagonal n g U Q r t =
      h15PostFEOrderedPairPhasePopulation .positive .positive
          n g U Q r t +
        h15PostFEOrderedPairPhasePopulation .positive .negative
          n g U Q r t +
        h15PostFEOrderedPairPhasePopulation .negative .positive
          n g U Q r t +
        h15PostFEOrderedPairPhasePopulation .negative .negative
          n g U Q r t := by
  rw [h15OrientationZeroFrequencyOffDiagonal_eq_collectedScalarKernel
    n g U Q r t hQ]
  unfold h15PostFEOrderedPairPhasePopulation
  calc
    (∑ κ ∈ h15PostFEOrderedPairResidueSupport n g U Q,
        (h15PostFEOrderedPairCollectedScalar n g U Q r t κ *
          h15PostFEResiduePairKernel t r κ).re) =
      ∑ κ ∈ h15PostFEOrderedPairResidueSupport n g U Q,
        ((h15PostFEOrderedPairCollectedScalar n g U Q r t κ *
              h15PostFEResiduePairPhaseComponent
                .positive .positive t r κ).re +
          (h15PostFEOrderedPairCollectedScalar n g U Q r t κ *
              h15PostFEResiduePairPhaseComponent
                .positive .negative t r κ).re +
          (h15PostFEOrderedPairCollectedScalar n g U Q r t κ *
              h15PostFEResiduePairPhaseComponent
                .negative .positive t r κ).re +
          (h15PostFEOrderedPairCollectedScalar n g U Q r t κ *
              h15PostFEResiduePairPhaseComponent
                .negative .negative t r κ).re) := by
      apply Finset.sum_congr rfl
      intro κ _hκ
      rw [h15PostFEResiduePairKernel_eq_four_phaseComponents]
      simp only [mul_add, add_re]
    _ = _ := by
      simp only [Finset.sum_add_distrib]

/-! ## Correction-coupled global boundary-transfer frontier -/

/-- The literal missing-residue trace retained by Ramanujan completion. -/
noncomputable def h15PostFEMissingResidueTrace
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ q ∈ h15PostFEResidueModulusSupport n g U Q,
    h15PostFEResidueFiberMeanCoefficient n g U Q r t q *
      ∑ a ∈ h15PostFEMissingResidues n g U Q q,
        h15PairedDirectCrossMode r a q

/-- The complete signed boundary-transfer expression.  The linear
missing-residue trace and all four ordered phase populations remain coupled;
none is estimated separately. -/
noncomputable def h15PostFEGlobalSignedBoundaryTransfer
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  h15PostFEMissingResidueTrace n g U Q r t +
    4 *
      (h15PostFEOrderedPairPhasePopulation .positive .positive
          n g U Q r t +
        h15PostFEOrderedPairPhasePopulation .positive .negative
          n g U Q r t +
        h15PostFEOrderedPairPhasePopulation .negative .positive
          n g U Q r t +
        h15PostFEOrderedPairPhasePopulation .negative .negative
          n g U Q r t) /
      (2 * h15PairedHyperbolicCoefficient t)

/-- Final exact global frontier after support and phase-population
normalization.  Proving decay of the centered lift defect is now precisely a
signed comparison between the mean-zero residue variation and the complete
boundary-transfer expression. -/
theorem h15PostFECenteredLiftDefect_eq_meanZero_sub_globalBoundaryTransfer
    (n g U Q r : ℕ) (t : ℝ)
    (hQ : 0 < Q) (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PostFECenteredLiftDefect n g U Q r t =
      h15PostFEResidueMeanZeroVariation n g U Q r t -
        h15PostFEGlobalSignedBoundaryTransfer n g U Q r t := by
  rw [h15PostFECenteredLiftDefect_eq_meanZero_sub_missing_sub_dispersion
      n g U Q r t hQ hS,
    h15OrientationZeroFrequencyOffDiagonal_eq_four_phasePopulations
      n g U Q r t hQ]
  unfold h15PostFEGlobalSignedBoundaryTransfer
  unfold h15PostFEMissingResidueTrace
  ring

end NBMellinTools.NB12
