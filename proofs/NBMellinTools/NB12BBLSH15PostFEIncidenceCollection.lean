/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFECoefficientExpansion

/-!
# NB12zzze: arithmetic-key collection of the post-FE incidence defect

The endpoint projection and the Laurent diagonal initially have different
finite index types.  This file collects each of them by the same arithmetic
key `(u,q)`, where `u` is the primitive inverse variable and `q` is the
primitive modulus.

The result is an exact finite coefficient identity.  It does not estimate the
coefficient mismatch and does not use absolute values.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Generic finite coefficient collection -/

/-- A finite weighted kernel sum can be collected exactly over the image of
its arithmetic key. -/
theorem sum_mul_kernel_eq_sum_image_collected
    {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (key : ι → κ) (coefficient : ι → ℝ)
    (kernel : κ → ℝ) :
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

/-! ## Endpoint-incidence rows -/

/-- A row of the endpoint incidence projection: modulus, square-divisor row,
and primitive inverse variable. -/
abbrev H15EndpointIncidenceRowIndex := Σ _qd : (Σ _q : ℕ, ℕ), ℕ

/-- The complete finite endpoint-incidence row family on `(g,U,Q)`. -/
def h15EndpointIncidenceRowIndices
    (N g U Q : ℕ) : Finset H15EndpointIncidenceRowIndex :=
  ((h15BettinChandeeSupportedNatBlock N g Q).sigma fun q =>
      h15DyadicActivePeriodSquareDivisorIndices g U q).sigma fun qd =>
    h15NormalizedSuperperiodBoundarySupport U
      (h15SquareDivisorProgressionModulus g qd.2) qd.1

/-- Arithmetic key shared by endpoint and Laurent rows. -/
def h15EndpointIncidenceRowKey
    (p : H15EndpointIncidenceRowIndex) : ℕ × ℕ :=
  (p.2, p.1.1)

/-- Signed coefficient of one endpoint-incidence row. -/
noncomputable def h15EndpointIncidenceRowCoefficient
    (N g U : ℕ) (p : H15EndpointIncidenceRowIndex) : ℝ :=
  h15NormalizedProgressionCoupledBoundaryPointWeight N g U
    (h15SquareDivisorProgressionModulus g p.1.2) p.1.1 p.1.2 p.2

/-- Endpoint coefficients collected at a fixed arithmetic key `(u,q)`. -/
noncomputable def h15EndpointCollectedCoefficient
    (N g U Q : ℕ) (k : ℕ × ℕ) : ℝ :=
  ∑ p ∈ (h15EndpointIncidenceRowIndices N g U Q).filter
      (fun p => h15EndpointIncidenceRowKey p = k),
    h15EndpointIncidenceRowCoefficient N g U p

/-- The spectral endpoint aggregate is the literal signed sum over the
endpoint-incidence row family. -/
theorem h15NormalizedBoundarySpectralAggregate_eq_sum_endpointIncidenceRows
    (N g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15NormalizedBoundarySpectralAggregate N g r U Q t =
      ∑ p ∈ h15EndpointIncidenceRowIndices N g U Q,
        h15EndpointIncidenceRowCoefficient N g U p *
          h15PairedDirectCrossMode r p.2 p.1.1 := by
  calc
    h15NormalizedBoundarySpectralAggregate N g r U Q t =
        ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
          ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
            h15NormalizedProgressionCoupledBoundaryPointRow N g r U
              (h15SquareDivisorProgressionModulus g d) q d := by
      unfold h15NormalizedBoundarySpectralAggregate
      apply Finset.sum_congr rfl
      intro q hqMem
      have hqPos : 0 < q :=
        hQ.trans_le (mem_h15BettinChandeeSupportedNatBlock.mp hqMem).1
      apply Finset.sum_congr rfl
      intro d _hd
      exact h15NormalizedProgressionCoupledBoundarySpectralRow_eq_pointRow
        N g r U (h15SquareDivisorProgressionModulus g d) q d t hqPos hS
    _ = _ := by
      unfold h15NormalizedProgressionCoupledBoundaryPointRow
        h15EndpointIncidenceRowIndices h15EndpointIncidenceRowCoefficient
      rw [Finset.sum_sigma', Finset.sum_sigma']

/-- Exact endpoint projection collected by `(u,q)`. -/
theorem h15NormalizedBoundarySpectralAggregate_eq_collected
    (N g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15NormalizedBoundarySpectralAggregate N g r U Q t =
      ∑ k ∈ (h15EndpointIncidenceRowIndices N g U Q).image
          h15EndpointIncidenceRowKey,
        h15EndpointCollectedCoefficient N g U Q k *
          h15PairedDirectCrossMode r k.1 k.2 := by
  rw [h15NormalizedBoundarySpectralAggregate_eq_sum_endpointIncidenceRows
    N g U Q r t hQ hS]
  exact sum_mul_kernel_eq_sum_image_collected
    (h15EndpointIncidenceRowIndices N g U Q)
    h15EndpointIncidenceRowKey
    (h15EndpointIncidenceRowCoefficient N g U)
    (fun k => h15PairedDirectCrossMode r k.1 k.2)

/-! ## Laurent-diagonal rows -/

/-- Arithmetic key of an orientation-zero Laurent row. -/
def h15OrientationZeroLaurentRowKey
    {N : ℕ} (i : H15LaurentRowIndex N) : ℕ × ℕ :=
  (h15LaurentA i, h15LaurentQ i)

/-- Squared Laurent scalar coefficient collected at `(u,q)`. -/
noncomputable def h15OrientationZeroCollectedDiagonalCoefficient
    (n g U Q r : ℕ) (t : ℝ) (k : ℕ × ℕ) : ℝ :=
  ∑ i ∈ (h15DoublyLocalizedOrientationZeroIndices
      (NB8.logTaperLength n) g U Q).filter
      (fun i => h15OrientationZeroLaurentRowKey i = k),
    Complex.normSq
      (h15DirectAdditiveTotalRowScalar (NB8.logTaperLength n)
        (h15ContourDamping n) i r t)

/-- Exact Laurent diagonal collected by the same arithmetic key `(u,q)`. -/
theorem h15OrientationZeroCrossModeDiagonal_eq_collected
    (n g U Q r : ℕ) (t : ℝ) :
    h15OrientationZeroCrossModeDiagonal n g U Q r t =
      ∑ k ∈ (h15DoublyLocalizedOrientationZeroIndices
          (NB8.logTaperLength n) g U Q).image
          h15OrientationZeroLaurentRowKey,
        h15OrientationZeroCollectedDiagonalCoefficient n g U Q r t k *
          h15PairedDirectCrossMode r k.1 k.2 := by
  unfold h15OrientationZeroCrossModeDiagonal
    h15OrientationZeroLaurentRowKey
  exact sum_mul_kernel_eq_sum_image_collected
    (h15DoublyLocalizedOrientationZeroIndices
      (NB8.logTaperLength n) g U Q)
    (fun i => (h15LaurentA i, h15LaurentQ i))
    (fun i => Complex.normSq
      (h15DirectAdditiveTotalRowScalar (NB8.logTaperLength n)
        (h15ContourDamping n) i r t))
    (fun k => h15PairedDirectCrossMode r k.1 k.2)

/-- The incidence defect is exactly the difference of two coefficient sums
collected by the common key `(u,q)`. -/
theorem h15PostFEDiagonalIncidenceDefect_eq_collected_difference
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PostFEDiagonalIncidenceDefect n g U Q r t =
      (∑ k ∈ (h15EndpointIncidenceRowIndices
          (NB8.logTaperLength n) g U Q).image h15EndpointIncidenceRowKey,
        h15EndpointCollectedCoefficient
            (NB8.logTaperLength n) g U Q k *
          h15PairedDirectCrossMode r k.1 k.2) -
      4 * (∑ k ∈ (h15DoublyLocalizedOrientationZeroIndices
          (NB8.logTaperLength n) g U Q).image
            h15OrientationZeroLaurentRowKey,
        h15OrientationZeroCollectedDiagonalCoefficient n g U Q r t k *
          h15PairedDirectCrossMode r k.1 k.2) := by
  unfold h15PostFEDiagonalIncidenceDefect
  rw [h15NormalizedBoundarySpectralAggregate_eq_collected
      (NB8.logTaperLength n) g U Q r t hQ hS,
    h15OrientationZeroCrossModeDiagonal_eq_collected]

end NBMellinTools.NB12
