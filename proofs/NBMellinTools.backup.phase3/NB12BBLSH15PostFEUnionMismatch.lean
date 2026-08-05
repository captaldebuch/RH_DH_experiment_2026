/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEIncidenceCollection

/-!
# NB12zzzf: union-support post-FE mismatch and dispersion gate

The endpoint-incidence and Laurent-diagonal coefficients are extended by zero
to the union of their finite arithmetic-key supports.  This turns their
difference into one literal coefficient function on `(u,q)`.

The final theorem of the file rewrites the centered lift defect as the sum of
that coefficient mismatch against the paired cross mode, minus the signed
ordered cross-row dispersion.  This is an exact identity, not a decay bound.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-- Arithmetic-key support of the endpoint-incidence coefficients. -/
def h15EndpointCollectedKeySupport
    (N g U Q : ℕ) : Finset (ℕ × ℕ) :=
  (h15EndpointIncidenceRowIndices N g U Q).image
    h15EndpointIncidenceRowKey

/-- Arithmetic-key support of the squared Laurent diagonal. -/
def h15LaurentCollectedKeySupport
    (n g U Q : ℕ) : Finset (ℕ × ℕ) :=
  (h15DoublyLocalizedOrientationZeroIndices
    (NB8.logTaperLength n) g U Q).image h15OrientationZeroLaurentRowKey

/-- Common finite support for the two collected coefficient families. -/
def h15PostFECollectedUnionKeySupport
    (n g U Q : ℕ) : Finset (ℕ × ℕ) :=
  h15EndpointCollectedKeySupport (NB8.logTaperLength n) g U Q ∪
    h15LaurentCollectedKeySupport n g U Q

/-- The collected endpoint coefficient vanishes off its image support. -/
theorem h15EndpointCollectedCoefficient_eq_zero_of_not_mem
    {N g U Q : ℕ} {k : ℕ × ℕ}
    (hk : k ∉ h15EndpointCollectedKeySupport N g U Q) :
    h15EndpointCollectedCoefficient N g U Q k = 0 := by
  classical
  unfold h15EndpointCollectedCoefficient
  apply Finset.sum_eq_zero
  intro p hp
  exfalso
  apply hk
  unfold h15EndpointCollectedKeySupport
  apply Finset.mem_image.mpr
  exact ⟨p, (Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2⟩

/-- The collected Laurent coefficient vanishes off its image support. -/
theorem h15OrientationZeroCollectedDiagonalCoefficient_eq_zero_of_not_mem
    {n g U Q r : ℕ} {t : ℝ} {k : ℕ × ℕ}
    (hk : k ∉ h15LaurentCollectedKeySupport n g U Q) :
    h15OrientationZeroCollectedDiagonalCoefficient n g U Q r t k = 0 := by
  classical
  unfold h15OrientationZeroCollectedDiagonalCoefficient
  apply Finset.sum_eq_zero
  intro i hi
  exfalso
  apply hk
  unfold h15LaurentCollectedKeySupport
  apply Finset.mem_image.mpr
  exact ⟨i, (Finset.mem_filter.mp hi).1,
    (Finset.mem_filter.mp hi).2⟩

/-- Exact zero-extension of the endpoint sum to the union support. -/
theorem sum_endpointCollected_eq_sum_union
    (n g U Q r : ℕ) :
    (∑ k ∈ h15EndpointCollectedKeySupport
        (NB8.logTaperLength n) g U Q,
      h15EndpointCollectedCoefficient
          (NB8.logTaperLength n) g U Q k *
        h15PairedDirectCrossMode r k.1 k.2) =
      ∑ k ∈ h15PostFECollectedUnionKeySupport n g U Q,
        h15EndpointCollectedCoefficient
            (NB8.logTaperLength n) g U Q k *
          h15PairedDirectCrossMode r k.1 k.2 := by
  classical
  apply Finset.sum_subset
  · intro k hk
    exact Finset.mem_union_left _ hk
  · intro k _hkUnion hkEndpoint
    rw [h15EndpointCollectedCoefficient_eq_zero_of_not_mem hkEndpoint,
      zero_mul]

/-- Exact zero-extension of the Laurent sum to the union support. -/
theorem sum_laurentCollected_eq_sum_union
    (n g U Q r : ℕ) (t : ℝ) :
    (∑ k ∈ h15LaurentCollectedKeySupport n g U Q,
      h15OrientationZeroCollectedDiagonalCoefficient n g U Q r t k *
        h15PairedDirectCrossMode r k.1 k.2) =
      ∑ k ∈ h15PostFECollectedUnionKeySupport n g U Q,
        h15OrientationZeroCollectedDiagonalCoefficient n g U Q r t k *
          h15PairedDirectCrossMode r k.1 k.2 := by
  classical
  apply Finset.sum_subset
  · intro k hk
    exact Finset.mem_union_right _ hk
  · intro k _hkUnion hkLaurent
    rw [h15OrientationZeroCollectedDiagonalCoefficient_eq_zero_of_not_mem
        hkLaurent,
      zero_mul]

/-- Literal coefficient mismatch on the common `(u,q)` support. -/
noncomputable def h15PostFECollectedMismatchCoefficient
    (n g U Q r : ℕ) (t : ℝ) (k : ℕ × ℕ) : ℝ :=
  h15EndpointCollectedCoefficient (NB8.logTaperLength n) g U Q k -
    4 * h15OrientationZeroCollectedDiagonalCoefficient n g U Q r t k

/-- The diagonal incidence defect is one signed cross-mode sum with the
literal pointwise coefficient mismatch. -/
theorem h15PostFEDiagonalIncidenceDefect_eq_union_mismatch
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PostFEDiagonalIncidenceDefect n g U Q r t =
      ∑ k ∈ h15PostFECollectedUnionKeySupport n g U Q,
        h15PostFECollectedMismatchCoefficient n g U Q r t k *
          h15PairedDirectCrossMode r k.1 k.2 := by
  rw [h15PostFEDiagonalIncidenceDefect_eq_collected_difference
      n g U Q r t hQ hS]
  have hEndpoint := sum_endpointCollected_eq_sum_union n g U Q r
  have hLaurent := sum_laurentCollected_eq_sum_union n g U Q r t
  rw [show (h15EndpointIncidenceRowIndices
        (NB8.logTaperLength n) g U Q).image h15EndpointIncidenceRowKey =
      h15EndpointCollectedKeySupport (NB8.logTaperLength n) g U Q by rfl,
    show (h15DoublyLocalizedOrientationZeroIndices
        (NB8.logTaperLength n) g U Q).image
          h15OrientationZeroLaurentRowKey =
      h15LaurentCollectedKeySupport n g U Q by rfl,
    hEndpoint, hLaurent]
  unfold h15PostFECollectedMismatchCoefficient
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- Canonical union-support form of the complete centered post-FE lift defect:
coefficient mismatch and ordered dispersion remain in one signed identity. -/
theorem h15PostFECenteredLiftDefect_eq_union_mismatch_sub_dispersion
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PostFECenteredLiftDefect n g U Q r t =
      (∑ k ∈ h15PostFECollectedUnionKeySupport n g U Q,
        h15PostFECollectedMismatchCoefficient n g U Q r t k *
          h15PairedDirectCrossMode r k.1 k.2) -
        4 * h15OrientationZeroFrequencyOffDiagonal n g U Q r t /
          (2 * h15PairedHyperbolicCoefficient t) := by
  rw [h15PostFECenteredLiftDefect_eq_incidence_sub_dispersion
      n g U Q r t hQ hS,
    h15PostFEDiagonalIncidenceDefect_eq_union_mismatch
      n g U Q r t hQ hS]

end NBMellinTools.NB12
