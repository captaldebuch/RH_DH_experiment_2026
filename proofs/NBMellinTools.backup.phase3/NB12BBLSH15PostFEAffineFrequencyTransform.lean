/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEResidueFrequencyFactorization

/-!
# NB12zzzaF: affine frequency decomposition of the signed transform

The complete reduced H15 transform is the sum of a frequency-independent
endpoint coefficient system and one common divisor-frequency norm square
times a frequency-independent Laurent-plus-pair system.  The phases still
depend on the row, as they must, but the arithmetic coefficient families no
longer do.

This is an exact signed identity.  No absolute value or asymptotic estimate is
used.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB12

theorem h15PostFEJointMissingTransform_add_scaled
    (modulusSupport : Finset ℕ) (missingSupport : ℕ → Finset ℕ)
    (A B : ℕ → ℝ) (c : ℝ) (r : ℕ) :
    h15PostFEJointMissingTransform modulusSupport missingSupport
        (fun q => A q + c * B q) r =
      h15PostFEJointMissingTransform modulusSupport missingSupport A r +
        c * h15PostFEJointMissingTransform modulusSupport missingSupport B r := by
  unfold h15PostFEJointMissingTransform
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  ring

theorem h15PostFEJointPairTransform_ofReal_mul
    (left right : BettinChandeeUnitSign)
    (support : Finset H15PostFEJointResiduePair)
    (B : H15PostFEJointResiduePair → ℂ)
    (c : ℝ) (r : ℕ) (t : ℝ) :
    h15PostFEJointPairTransform left right support
        (fun κ => (c : ℂ) * B κ) r t =
      c * h15PostFEJointPairTransform left right support B r t := by
  unfold h15PostFEJointPairTransform
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κ _hκ
  rw [show
      ((c : ℂ) * B κ *
          (conj (h15PostFEOrientationArchimedeanFactor left t) *
            h15PostFEOrientationArchimedeanFactor right t *
            h15PostFECommonPairAdditivePhase left right r
              κ.1.1 κ.1.2 κ.2.1 κ.2.2)).re =
        ((c : ℂ) *
          (B κ *
            (conj (h15PostFEOrientationArchimedeanFactor left t) *
              h15PostFEOrientationArchimedeanFactor right t *
              h15PostFECommonPairAdditivePhase left right r
                κ.1.1 κ.1.2 κ.2.1 κ.2.2))).re by ring]
  exact ofReal_mul_re c _

/-- The endpoint-only missing-residue transform. -/
noncomputable def h15PostFEEndpointFrequencyTransform
    (n g U Q r : ℕ) : ℝ :=
  h15PostFEJointMissingTransform
    (h15PostFEResidueModulusSupport n g U Q)
    (h15PostFEReducedMissingResidues n g U Q)
    (h15PostFEResidueFiberEndpointMeanCoefficient n g U Q) r

/-- The frequency-free Laurent-plus-four-orientation transform multiplying
the common divisor-frequency norm square. -/
noncomputable def h15PostFELaurentPairFrequencyTransform
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  -4 * h15PostFEJointMissingTransform
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q)
      (h15PostFEResidueFiberLaurentMeanCoefficientWithoutFrequency
        n g U Q t) r +
    4 *
      (h15PostFEJointPairTransform .positive .positive
          (h15PostFEReducedOrderedPairResidueSupport n g U Q)
          (h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t) r t +
        h15PostFEJointPairTransform .positive .negative
          (h15PostFEReducedOrderedPairResidueSupport n g U Q)
          (h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t) r t +
        h15PostFEJointPairTransform .negative .positive
          (h15PostFEReducedOrderedPairResidueSupport n g U Q)
          (h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t) r t +
        h15PostFEJointPairTransform .negative .negative
          (h15PostFEReducedOrderedPairResidueSupport n g U Q)
          (h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t) r t) /
      (2 * h15PairedHyperbolicCoefficient t)

/-- The affine scalar is independent of the vertical twist and is exactly the
square of the standard divisor-frequency coefficient. -/
theorem normSq_h15DirectAdditiveFrequencyCoefficient_eq
    {r : ℕ} (hr : 0 < r) (t : ℝ) :
    Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) =
      h15BettinChandeeFrequencyCoefficient r ^ 2 := by
  rw [h15DirectAdditiveFrequencyCoefficient_eq_base_mul_twist hr,
    Complex.normSq_mul, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq,
    norm_h15ThreeHalfFrequencyUnitTwist hr]
  simp [h15BettinChandeeFrequencyCoefficient]

theorem normSq_h15DirectAdditiveFrequencyCoefficient_eq_divisor
    {r : ℕ} (hr : 0 < r) (t : ℝ) :
    Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) =
      ((r.divisors.card : ℝ) / (r : ℝ) ^ (3 / 2 : ℝ)) ^ 2 := by
  rw [normSq_h15DirectAdditiveFrequencyCoefficient_eq hr,
    h15BettinChandeeFrequencyCoefficient_eq hr]

/-- Canonical affine decomposition of the complete literal signed transform. -/
theorem h15PostFEActualJointCorrectionTransform_eq_endpoint_add_frequencyNormSq_mul
    (n g U Q r : ℕ) (t : ℝ) :
    h15PostFEActualJointCorrectionTransform n g U Q r t =
      h15PostFEEndpointFrequencyTransform n g U Q r +
        Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
          h15PostFELaurentPairFrequencyTransform n g U Q r t := by
  rw [h15PostFEActualJointCorrectionTransform_eq_reducedSupports]
  unfold h15PostFEJointCorrectionTransform
  let c := Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t)
  have hmissing :
      (h15PostFEResidueFiberMeanCoefficient n g U Q r t) =
        fun q => h15PostFEResidueFiberEndpointMeanCoefficient n g U Q q +
          (-4 * c) *
            h15PostFEResidueFiberLaurentMeanCoefficientWithoutFrequency
              n g U Q t q := by
    funext q
    rw [h15PostFEResidueFiberMeanCoefficient_eq_affineFrequencyNormSq]
    dsimp only [c]
    ring
  have hpair :
      (h15PostFEOrderedPairCollectedScalar n g U Q r t) =
        fun κ => (c : ℂ) *
          h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t κ := by
    funext κ
    exact h15PostFEOrderedPairCollectedScalar_eq_frequencyNormSq_mul
      n g U Q r t κ
  rw [hmissing,
    h15PostFEJointMissingTransform_add_scaled,
    hpair,
    h15PostFEJointPairTransform_ofReal_mul,
    h15PostFEJointPairTransform_ofReal_mul,
    h15PostFEJointPairTransform_ofReal_mul,
    h15PostFEJointPairTransform_ofReal_mul]
  unfold h15PostFEEndpointFrequencyTransform
    h15PostFELaurentPairFrequencyTransform
  dsimp only [c]
  ring_nf

end NBMellinTools.NB12
