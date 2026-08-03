/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFECoefficientFrequencyFactorization

/-!
# NB12zzzae: affine frequency factorization on residue fibers

The pointwise endpoint-minus-Laurent mismatch is affine in the common
frequency norm square.  Finite collection by residue class and averaging on
each active modulus preserve that affine form exactly.  This file records the
two frequency-independent coefficient families and proves the resulting
decomposition of the retained missing-residue coefficient.
-/

open Complex
open scoped BigOperators

namespace NBMellinTools.NB12

/-- Endpoint-incidence coefficient collected on one post-FE residue key. -/
noncomputable def h15PostFEResidueEndpointCoefficient
    (n g U Q : ℕ) (z : ℕ × ℕ) : ℝ :=
  ∑ k ∈ (h15PostFECollectedUnionKeySupport n g U Q).filter
      (fun k => h15PostFEResidueKey k = z),
    h15EndpointCollectedCoefficient (NB8.logTaperLength n) g U Q k

/-- Frequency-free Laurent diagonal collected on one post-FE residue key. -/
noncomputable def h15PostFEResidueLaurentCoefficientWithoutFrequency
    (n g U Q : ℕ) (t : ℝ) (z : ℕ × ℕ) : ℝ :=
  ∑ k ∈ (h15PostFECollectedUnionKeySupport n g U Q).filter
      (fun k => h15PostFEResidueKey k = z),
    h15OrientationZeroCollectedDiagonalCoefficientWithoutFrequency
      n g U Q t k

theorem h15PostFEResidueMismatchCoefficient_eq_affineFrequencyNormSq
    (n g U Q r : ℕ) (t : ℝ) (z : ℕ × ℕ) :
    h15PostFEResidueMismatchCoefficient n g U Q r t z =
      h15PostFEResidueEndpointCoefficient n g U Q z -
        4 * Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
          h15PostFEResidueLaurentCoefficientWithoutFrequency
            n g U Q t z := by
  unfold h15PostFEResidueMismatchCoefficient
    h15PostFEResidueEndpointCoefficient
    h15PostFEResidueLaurentCoefficientWithoutFrequency
  simp_rw [h15PostFECollectedMismatchCoefficient_eq_affineFrequencyNormSq]
  rw [Finset.sum_sub_distrib]
  rw [Finset.mul_sum]

/-- Endpoint part of the canonical coefficient mean on a residue fiber. -/
noncomputable def h15PostFEResidueFiberEndpointMeanCoefficient
    (n g U Q : ℕ) (q : ℕ) : ℝ :=
  (∑ z ∈ h15PostFEResidueFiber n g U Q q,
      h15PostFEResidueEndpointCoefficient n g U Q z) /
    (h15PostFEResidueFiber n g U Q q).card

/-- Frequency-free Laurent part of the canonical coefficient mean on a
residue fiber. -/
noncomputable def h15PostFEResidueFiberLaurentMeanCoefficientWithoutFrequency
    (n g U Q : ℕ) (t : ℝ) (q : ℕ) : ℝ :=
  (∑ z ∈ h15PostFEResidueFiber n g U Q q,
      h15PostFEResidueLaurentCoefficientWithoutFrequency n g U Q t z) /
    (h15PostFEResidueFiber n g U Q q).card

/-- Exact affine frequency dependence of the retained missing-residue mean. -/
theorem h15PostFEResidueFiberMeanCoefficient_eq_affineFrequencyNormSq
    (n g U Q r : ℕ) (t : ℝ) (q : ℕ) :
    h15PostFEResidueFiberMeanCoefficient n g U Q r t q =
      h15PostFEResidueFiberEndpointMeanCoefficient n g U Q q -
        4 * Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t) *
          h15PostFEResidueFiberLaurentMeanCoefficientWithoutFrequency
            n g U Q t q := by
  unfold h15PostFEResidueFiberMeanCoefficient
    h15PostFEResidueFiberEndpointMeanCoefficient
    h15PostFEResidueFiberLaurentMeanCoefficientWithoutFrequency
  simp_rw [h15PostFEResidueMismatchCoefficient_eq_affineFrequencyNormSq]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum
    (h15PostFEResidueFiber n g U Q q)
    (fun z => h15PostFEResidueLaurentCoefficientWithoutFrequency
      n g U Q t z)
    (4 * Complex.normSq (h15DirectAdditiveFrequencyCoefficient r t))]
  ring

end NBMellinTools.NB12
