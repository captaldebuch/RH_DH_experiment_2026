/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15OrientationNormalizedQuadratic

/-!
# NB12zzzd: coefficient expansion of the endpoint-aligned post-FE block

This file factors every direct-additive row into a scalar coefficient and the
paired phase kernel.  It then centers the squared norm of the correctly
post-functional-equation-localized block.

The resulting exact defect has two canonical pieces:

1. a diagonal incidence/coefficient mismatch between endpoint weights and
   squared Laurent coefficients;
2. the signed ordered cross-row dispersion term.

No absolute values, asymptotic estimate, or RH claim occurs here.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-- Everything in one separated direct-additive row except its paired phase
kernel. -/
noncomputable def h15DirectAdditiveRowScalar
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
    h15DirectAdditiveFrequencyCoefficient r t

theorem h15DirectAdditiveSeparatedSummand_eq_scalar_mul_kernel
    {N : ℕ} (damping : ℝ) (i : H15LaurentRowIndex N)
    (r : ℕ) (t : ℝ) :
    h15DirectAdditiveSeparatedSummand N damping i r t =
      h15DirectAdditiveRowScalar N damping i r t *
        h15PairedDirectKernel t r
          (h15BettinChandeeInverseVariable i)
          (h15BettinChandeeModulusVariable i) := by
  rfl

/-- Total scalar coefficient, zero on invalid raw Laurent rows. -/
noncomputable def h15DirectAdditiveTotalRowScalar
    (N : ℕ) (damping : ℝ) (i : H15LaurentRowIndex N)
    (r : ℕ) (t : ℝ) : ℂ := by
  classical
  exact if h15LaurentRowValid i then
      h15DirectAdditiveRowScalar N damping i r t
    else 0

theorem h15DirectAdditiveFixedHeightSummand_eq_scalar_mul_kernel
    {N : ℕ} (damping : ℝ) (i : H15LaurentRowIndex N)
    (r : ℕ) (t : ℝ) :
    h15DirectAdditiveFixedHeightSummand N damping (i, r) t =
      h15DirectAdditiveTotalRowScalar N damping i r t *
        h15PairedDirectKernel t r
          (h15BettinChandeeInverseVariable i)
          (h15BettinChandeeModulusVariable i) := by
  classical
  by_cases hvalid : h15LaurentRowValid i
  · rw [h15DirectAdditiveFixedHeightSummand, if_pos hvalid,
      h15DirectAdditiveTotalRowScalar, if_pos hvalid]
    exact h15DirectAdditiveSeparatedSummand_eq_scalar_mul_kernel
      damping i r t
  · rw [h15DirectAdditiveFixedHeightSummand, if_neg hvalid,
      h15DirectAdditiveTotalRowScalar, if_neg hvalid]
    simp

/-- Unsigned pointwise diagonal removed when centering one orientation-zero
block. -/
noncomputable def h15OrientationZeroUnsignedDiagonal
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ h15DoublyLocalizedOrientationZeroIndices
      (NB8.logTaperLength n) g U Q,
    Complex.normSq
        (h15DirectAdditiveTotalRowScalar (NB8.logTaperLength n)
          (h15ContourDamping n) i r t) *
      (1 + h15PairedHyperbolicCoefficient t ^ 2)

/-- Diagonal signed cross mode left after pointwise centering. -/
noncomputable def h15OrientationZeroCrossModeDiagonal
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ h15DoublyLocalizedOrientationZeroIndices
      (NB8.logTaperLength n) g U Q,
    Complex.normSq
        (h15DirectAdditiveTotalRowScalar (NB8.logTaperLength n)
          (h15ContourDamping n) i r t) *
      h15PairedDirectCrossMode r (h15LaurentA i) (h15LaurentQ i)

/-- Literal signed ordered cross-row sector in one orientation-zero block. -/
noncomputable def h15OrientationZeroFrequencyOffDiagonal
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ h15DoublyLocalizedOrientationZeroIndices
      (NB8.logTaperLength n) g U Q,
    ∑ j ∈ (h15DoublyLocalizedOrientationZeroIndices
        (NB8.logTaperLength n) g U Q).erase i,
      (conj
          (h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
            (h15ContourDamping n) (i, r) t) *
        h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
          (h15ContourDamping n) (j, r) t).re

/-- Pointwise norm-square formula on every row of an orientation-zero block. -/
theorem normSq_h15DirectAdditiveFixedHeightSummand_on_orientationZero
    {n g U Q r : ℕ} {i : H15LaurentRowIndex (NB8.logTaperLength n)}
    (hi : i ∈ h15DoublyLocalizedOrientationZeroIndices
      (NB8.logTaperLength n) g U Q)
    (hQ : 0 < Q) (t : ℝ) :
    Complex.normSq
        (h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
          (h15ContourDamping n) (i, r) t) =
      Complex.normSq
          (h15DirectAdditiveTotalRowScalar (NB8.logTaperLength n)
            (h15ContourDamping n) i r t) *
        (1 + h15PairedHyperbolicCoefficient t ^ 2 +
          2 * h15PairedHyperbolicCoefficient t *
            h15PairedDirectCrossMode r (h15LaurentA i) (h15LaurentQ i)) := by
  classical
  by_cases hvalid : h15LaurentRowValid i
  · have hzero :=
      (mem_h15DoublyLocalizedOrientationZeroIndices.mp hi).2
    have hraw := mem_h15DoublyLocalizedLaurentRowIndices.mp
      (mem_h15DoublyLocalizedOrientationZeroIndices.mp hi).1
    have hqMem := hraw.2.2
    have hqPos : 0 < h15LaurentQ i :=
      hQ.trans_le (mem_h15BettinChandeeSupportedNatBlock.mp hqMem).1
    have hcop : Nat.Coprime (h15LaurentA i) (h15LaurentQ i) :=
      hvalid.2.2.2.2
    rw [h15DirectAdditiveFixedHeightSummand_eq_scalar_mul_kernel,
      Complex.normSq_mul]
    simp only [h15DirectAdditiveTotalRowScalar, if_pos hvalid,
      h15BettinChandeeInverseVariable, h15BettinChandeeModulusVariable,
      hzero, if_true]
    rw [normSq_h15PairedDirectKernel t r
      (h15LaurentA i) (h15LaurentQ i) hqPos hcop]
    rfl
  · rw [h15DirectAdditiveFixedHeightSummand, if_neg hvalid,
      h15DirectAdditiveTotalRowScalar, if_neg hvalid]
    simp

/-- Exact centered norm-square expansion of one orientation-zero block. -/
theorem normSq_h15OrientationZeroDirectAdditiveFrequencySlice_eq
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q) :
    Complex.normSq
        (h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t) =
      h15OrientationZeroUnsignedDiagonal n g U Q r t +
        2 * h15PairedHyperbolicCoefficient t *
          h15OrientationZeroCrossModeDiagonal n g U Q r t +
        h15OrientationZeroFrequencyOffDiagonal n g U Q r t := by
  let S := h15DoublyLocalizedOrientationZeroIndices
    (NB8.logTaperLength n) g U Q
  let F := fun i : H15LaurentRowIndex (NB8.logTaperLength n) =>
    h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
      (h15ContourDamping n) (i, r) t
  calc
    Complex.normSq
        (h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t) =
      (∑ i ∈ S, Complex.normSq (F i)) +
        h15OrientationZeroFrequencyOffDiagonal n g U Q r t := by
          unfold h15OrientationZeroDirectAdditiveFrequencySlice
            h15OrientationZeroFrequencyOffDiagonal
          exact normSq_sum_eq_sum_normSq_add_orderedOffDiagonal S F
    _ = (∑ i ∈ S,
          (Complex.normSq
              (h15DirectAdditiveTotalRowScalar (NB8.logTaperLength n)
                (h15ContourDamping n) i r t) *
              (1 + h15PairedHyperbolicCoefficient t ^ 2) +
            2 * h15PairedHyperbolicCoefficient t *
              (Complex.normSq
                (h15DirectAdditiveTotalRowScalar (NB8.logTaperLength n)
                  (h15ContourDamping n) i r t) *
                h15PairedDirectCrossMode r
                  (h15LaurentA i) (h15LaurentQ i)))) +
        h15OrientationZeroFrequencyOffDiagonal n g U Q r t := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [normSq_h15DirectAdditiveFixedHeightSummand_on_orientationZero
            hi hQ t]
          ring
    _ = _ := by
      unfold h15OrientationZeroUnsignedDiagonal
        h15OrientationZeroCrossModeDiagonal
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Centered and normalized quadratic projection of one orientation-zero
block. -/
noncomputable def h15OrientationZeroCenteredQuadraticProjection
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  (Complex.normSq
      (h15OrientationZeroDirectAdditiveFrequencySlice n g U Q r t) -
    h15OrientationZeroUnsignedDiagonal n g U Q r t) /
      (2 * h15PairedHyperbolicCoefficient t)

theorem h15OrientationZeroCenteredQuadraticProjection_eq
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15OrientationZeroCenteredQuadraticProjection n g U Q r t =
      h15OrientationZeroCrossModeDiagonal n g U Q r t +
        h15OrientationZeroFrequencyOffDiagonal n g U Q r t /
          (2 * h15PairedHyperbolicCoefficient t) := by
  unfold h15OrientationZeroCenteredQuadraticProjection
  rw [normSq_h15OrientationZeroDirectAdditiveFrequencySlice_eq
    n g U Q r t hQ]
  field_simp [hS]
  ring

/-- Centered projection of the full endpoint-aligned post-FE block.  The
factor four is forced by the two identical raw orientations. -/
noncomputable def h15PostFECenteredQuadraticProjection
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  (Complex.normSq
      (h15PostFELocalizedDirectAdditiveFrequencySlice n g U Q r t) -
    4 * h15OrientationZeroUnsignedDiagonal n g U Q r t) /
      (2 * h15PairedHyperbolicCoefficient t)

theorem h15PostFECenteredQuadraticProjection_eq
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PostFECenteredQuadraticProjection n g U Q r t =
      4 * h15OrientationZeroCrossModeDiagonal n g U Q r t +
        4 * h15OrientationZeroFrequencyOffDiagonal n g U Q r t /
          (2 * h15PairedHyperbolicCoefficient t) := by
  unfold h15PostFECenteredQuadraticProjection
  rw [normSq_h15PostFELocalizedDirectAdditiveFrequencySlice,
    normSq_h15OrientationZeroDirectAdditiveFrequencySlice_eq
      n g U Q r t hQ]
  field_simp [hS]
  ring

/-- Exact diagonal endpoint-incidence/coefficient mismatch. -/
noncomputable def h15PostFEDiagonalIncidenceDefect
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  h15NormalizedBoundarySpectralAggregate
      (NB8.logTaperLength n) g r U Q t -
    4 * h15OrientationZeroCrossModeDiagonal n g U Q r t

/-- Defect between the endpoint spectral aggregate and the centered aligned
post-FE quadratic projection. -/
noncomputable def h15PostFECenteredLiftDefect
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  h15NormalizedBoundarySpectralAggregate
      (NB8.logTaperLength n) g r U Q t -
    h15PostFECenteredQuadraticProjection n g U Q r t

/-- Canonical two-piece lift-defect expansion: diagonal incidence mismatch
minus the signed ordered cross-row dispersion. -/
theorem h15PostFECenteredLiftDefect_eq_incidence_sub_dispersion
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PostFECenteredLiftDefect n g U Q r t =
      h15PostFEDiagonalIncidenceDefect n g U Q r t -
        4 * h15OrientationZeroFrequencyOffDiagonal n g U Q r t /
          (2 * h15PairedHyperbolicCoefficient t) := by
  unfold h15PostFECenteredLiftDefect h15PostFEDiagonalIncidenceDefect
  rw [h15PostFECenteredQuadraticProjection_eq n g U Q r t hQ hS]
  ring

end NBMellinTools.NB12
