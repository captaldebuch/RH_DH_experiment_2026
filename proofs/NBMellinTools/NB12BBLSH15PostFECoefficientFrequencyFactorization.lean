/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFELiteralCollisionEnergy

/-!
# NB12zzzad: frequency factorization of the post-FE coefficients

The literal collision ledger has coefficients depending on the frequency row
`r`.  This file isolates that dependence exactly.  Every Laurent row contains
one common divisor-frequency factor.  Consequently:

* every ordered-pair coefficient contains its norm square as one common real
  scalar; and
* every collected Laurent diagonal contains the same norm square.

The endpoint-incidence coefficient is independent of `r`, so the diagonal
mismatch is affine, rather than homogeneous, in this common scalar.  This is
the precise structure needed by the next weighted-collision analysis.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB12

/-- A direct-additive row with the common frequency coefficient removed. -/
noncomputable def h15DirectAdditiveRowScalarWithoutFrequency
    (N : ℕ) (damping : ℝ) (i : H15LaurentRowIndex N) (t : ℝ) : ℂ :=
  let s := bblsEstermannThreeHalfPoint t
  let u := h15BettinChandeeInverseVariable i
  let q := h15BettinChandeeModulusVariable i
  (((Real.pi / (h15LaurentG i : ℝ)) *
      h15BettinChandeeInverseCoefficient N (h15LaurentG i) u : ℝ) : ℂ) *
    Complex.Gamma (-s) * (damping : ℂ) ^ s *
    h15ThreeHalfArchimedeanFactor t *
    h15DirectAdditiveModulusCoefficient N (h15LaurentG i) q t

theorem h15DirectAdditiveRowScalar_eq_withoutFrequency_mul
    (N : ℕ) (damping : ℝ) (i : H15LaurentRowIndex N)
    (r : ℕ) (t : ℝ) :
    h15DirectAdditiveRowScalar N damping i r t =
      h15DirectAdditiveRowScalarWithoutFrequency N damping i t *
        h15DirectAdditiveFrequencyCoefficient r t := by
  rfl

/-- Zero-extended frequency-free scalar on all raw Laurent rows. -/
noncomputable def h15DirectAdditiveTotalRowScalarWithoutFrequency
    (N : ℕ) (damping : ℝ) (i : H15LaurentRowIndex N) (t : ℝ) : ℂ := by
  classical
  exact if h15LaurentRowValid i then
    h15DirectAdditiveRowScalarWithoutFrequency N damping i t
  else 0

theorem h15DirectAdditiveTotalRowScalar_eq_withoutFrequency_mul
    (N : ℕ) (damping : ℝ) (i : H15LaurentRowIndex N)
    (r : ℕ) (t : ℝ) :
    h15DirectAdditiveTotalRowScalar N damping i r t =
      h15DirectAdditiveTotalRowScalarWithoutFrequency N damping i t *
        h15DirectAdditiveFrequencyCoefficient r t := by
  classical
  by_cases hi : h15LaurentRowValid i
  · simp [h15DirectAdditiveTotalRowScalar,
      h15DirectAdditiveTotalRowScalarWithoutFrequency, hi,
      h15DirectAdditiveRowScalar_eq_withoutFrequency_mul]
  · simp [h15DirectAdditiveTotalRowScalar,
      h15DirectAdditiveTotalRowScalarWithoutFrequency, hi]

/-- Frequency-free ordered Laurent-pair scalar. -/
noncomputable def h15PostFEOrderedPairScalarWithoutFrequency
    (n : ℕ) (t : ℝ)
    (p : H15PostFEOrderedLaurentPairIndex (NB8.logTaperLength n)) : ℂ :=
  conj
      (h15DirectAdditiveTotalRowScalarWithoutFrequency
        (NB8.logTaperLength n) (h15ContourDamping n) p.1 t) *
    h15DirectAdditiveTotalRowScalarWithoutFrequency
      (NB8.logTaperLength n) (h15ContourDamping n) p.2 t

theorem h15PostFEOrderedPairScalar_eq_frequencyNormSq_mul
    (n r : ℕ) (t : ℝ)
    (p : H15PostFEOrderedLaurentPairIndex (NB8.logTaperLength n)) :
    h15PostFEOrderedPairScalar n r t p =
      ((Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) : ℝ) : ℂ) *
        h15PostFEOrderedPairScalarWithoutFrequency n t p := by
  unfold h15PostFEOrderedPairScalar
    h15PostFEOrderedPairScalarWithoutFrequency
  rw [h15DirectAdditiveTotalRowScalar_eq_withoutFrequency_mul,
    h15DirectAdditiveTotalRowScalar_eq_withoutFrequency_mul]
  simp only [map_mul]
  rw [show
      conj
            (h15DirectAdditiveTotalRowScalarWithoutFrequency
              (NB8.logTaperLength n) (h15ContourDamping n) p.1 t) *
          conj (h15DirectAdditiveFrequencyCoefficient r t) *
          (h15DirectAdditiveTotalRowScalarWithoutFrequency
              (NB8.logTaperLength n) (h15ContourDamping n) p.2 t *
            h15DirectAdditiveFrequencyCoefficient r t) =
        (conj (h15DirectAdditiveFrequencyCoefficient r t) *
            h15DirectAdditiveFrequencyCoefficient r t) *
          (conj
              (h15DirectAdditiveTotalRowScalarWithoutFrequency
                (NB8.logTaperLength n) (h15ContourDamping n) p.1 t) *
            h15DirectAdditiveTotalRowScalarWithoutFrequency
              (NB8.logTaperLength n) (h15ContourDamping n) p.2 t) by ring]
  rw [show
      conj (h15DirectAdditiveFrequencyCoefficient r t) *
          h15DirectAdditiveFrequencyCoefficient r t =
        (Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) : ℂ) by
    exact Complex.normSq_eq_conj_mul_self.symm]

/-- Collected pair coefficient after removal of the common frequency norm
square. -/
noncomputable def h15PostFEOrderedPairCollectedScalarWithoutFrequency
    (n g U Q : ℕ) (t : ℝ)
    (κ : H15PostFEJointResiduePair) : ℂ :=
  ∑ p ∈ (h15PostFEOrderedLaurentPairIndices n g U Q).filter
      (fun p => h15PostFEOrderedPairResidueKey p = κ),
    h15PostFEOrderedPairScalarWithoutFrequency n t p

theorem h15PostFEOrderedPairCollectedScalar_eq_frequencyNormSq_mul
    (n g U Q r : ℕ) (t : ℝ) (κ : H15PostFEJointResiduePair) :
    h15PostFEOrderedPairCollectedScalar n g U Q r t κ =
      ((Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) : ℝ) : ℂ) *
        h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t κ := by
  unfold h15PostFEOrderedPairCollectedScalar
    h15PostFEOrderedPairCollectedScalarWithoutFrequency
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  exact h15PostFEOrderedPairScalar_eq_frequencyNormSq_mul n r t p

/-- Collected Laurent diagonal with the common frequency norm square
removed. -/
noncomputable def h15OrientationZeroCollectedDiagonalCoefficientWithoutFrequency
    (n g U Q : ℕ) (t : ℝ) (k : ℕ × ℕ) : ℝ :=
  ∑ i ∈ (h15DoublyLocalizedOrientationZeroIndices
      (NB8.logTaperLength n) g U Q).filter
      (fun i => h15OrientationZeroLaurentRowKey i = k),
    Complex.normSq
      (h15DirectAdditiveTotalRowScalarWithoutFrequency
        (NB8.logTaperLength n) (h15ContourDamping n) i t)

theorem h15OrientationZeroCollectedDiagonalCoefficient_eq_frequencyNormSq_mul
    (n g U Q r : ℕ) (t : ℝ) (k : ℕ × ℕ) :
    h15OrientationZeroCollectedDiagonalCoefficient n g U Q r t k =
      Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
        h15OrientationZeroCollectedDiagonalCoefficientWithoutFrequency
          n g U Q t k := by
  unfold h15OrientationZeroCollectedDiagonalCoefficient
    h15OrientationZeroCollectedDiagonalCoefficientWithoutFrequency
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [h15DirectAdditiveTotalRowScalar_eq_withoutFrequency_mul,
    Complex.normSq_mul]
  ring

/-- Exact affine frequency dependence of the collected endpoint-minus-
Laurent mismatch. -/
theorem h15PostFECollectedMismatchCoefficient_eq_affineFrequencyNormSq
    (n g U Q r : ℕ) (t : ℝ) (k : ℕ × ℕ) :
    h15PostFECollectedMismatchCoefficient n g U Q r t k =
      h15EndpointCollectedCoefficient (NB8.logTaperLength n) g U Q k -
        4 * Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
          h15OrientationZeroCollectedDiagonalCoefficientWithoutFrequency
            n g U Q t k := by
  unfold h15PostFECollectedMismatchCoefficient
  rw [h15OrientationZeroCollectedDiagonalCoefficient_eq_frequencyNormSq_mul]
  ring

end NBMellinTools.NB12
