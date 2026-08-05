/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15EstermannRowAssembly
import NBMellinTools.NB12BBLSH15PostFEAffineFrequencyTransform

/-!
# Canonical global assembly of the local H15 PostFE transforms

The NB12 PostFE transform is indexed by one gcd slice and two dyadic
primitive scales.  The certified Nyman--Beurling energy, by contrast, uses
the complete finite Laurent row cube.  This module makes that distinction
formal.

We first attach to every cutoff-supported raw row its unique dyadic PostFE
block, using the scales `2 ^ log2 u` and `2 ^ log2 q`.  The resulting finite
block support is canonical and contains no arbitrary cutoff parameters.  We
then sum the already verified local correction transform, mean-zero
variation, and lift defect over that support.

The global sum satisfies the exact local NB12 identity block by block.  It is
not identified with the undamped Estermann endpoint amplitude: the latter is
linear in the Laurent rows, whereas the present PostFE object arises from a
quadratic projection at one frequency and one contour height.  The final
section therefore records their exact difference as a bridge defect.  This
prevents a local quadratic estimate from being mistaken for a proof of
decay of the certified energy.
-/

open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB15

open NBMellinTools.NB8
open NBMellinTools.NB12
open Complex

/-! ## Canonical dyadic blocks -/

/-- The canonical positive dyadic scale containing a positive natural
number. -/
def h15CanonicalDyadicScale (x : ℕ) : ℕ :=
  2 ^ Nat.log2 x

theorem h15CanonicalDyadicScale_pos (x : ℕ) :
    0 < h15CanonicalDyadicScale x := by
  unfold h15CanonicalDyadicScale
  positivity

theorem h15CanonicalDyadicScale_le
    {x : ℕ} (hx : x ≠ 0) :
    h15CanonicalDyadicScale x ≤ x := by
  unfold h15CanonicalDyadicScale
  rw [Nat.log2_eq_log_two]
  exact Nat.pow_log_le_self 2 hx

theorem lt_two_mul_h15CanonicalDyadicScale (x : ℕ) :
    x < 2 * h15CanonicalDyadicScale x := by
  unfold h15CanonicalDyadicScale
  rw [Nat.log2_eq_log_two]
  simpa [pow_succ'] using
    (Nat.lt_pow_succ_log_self Nat.one_lt_two x)

theorem h15CanonicalDyadicScale_eq_of_mem_same_block
    {x y : ℕ}
    (hlo : h15CanonicalDyadicScale x ≤ y)
    (hhi : y < 2 * h15CanonicalDyadicScale x) :
    h15CanonicalDyadicScale y = h15CanonicalDyadicScale x := by
  have hhi' : y < 2 ^ (Nat.log 2 x + 1) := by
    simpa [h15CanonicalDyadicScale, Nat.log2_eq_log_two, pow_succ'] using hhi
  have hlog : Nat.log 2 y = Nat.log 2 x :=
    Nat.log_eq_of_pow_le_of_lt_pow
      (by simpa [h15CanonicalDyadicScale, Nat.log2_eq_log_two] using hlo)
      hhi'
  simp [h15CanonicalDyadicScale, Nat.log2_eq_log_two, hlog]

/-- A global block key consists of the gcd slice, the PostFE inverse scale,
and the PostFE modulus scale. -/
abbrev H15GlobalPostFEBlockKey := (ℕ × ℕ) × ℕ

def h15GlobalPostFEBlockG (b : H15GlobalPostFEBlockKey) : ℕ := b.1.1
def h15GlobalPostFEBlockU (b : H15GlobalPostFEBlockKey) : ℕ := b.1.2
def h15GlobalPostFEBlockQ (b : H15GlobalPostFEBlockKey) : ℕ := b.2

/-- Raw rows satisfying the two hyperbolic cutoff inequalities.  Conditions
such as coprimality and the lower endpoints remain in `h15LaurentRowValid`;
they are deliberately not needed to define the dyadic geometry. -/
def h15PostFECutoffRowSupport (N : ℕ) :
    Finset (H15LaurentRowIndex N) :=
  Finset.univ.filter fun i =>
    h15LaurentG i * h15LaurentA i ≤ N ∧
      h15LaurentG i * h15LaurentQ i ≤ N

/-- The canonical endpoint-aligned dyadic block of one Laurent row. -/
def h15GlobalPostFERowBlockKey {N : ℕ}
    (i : H15LaurentRowIndex N) : H15GlobalPostFEBlockKey :=
  ((h15LaurentG i,
      h15CanonicalDyadicScale (h15BettinChandeeInverseVariable i)),
    h15CanonicalDyadicScale (h15BettinChandeeModulusVariable i))

/-- Complete finite support of nonempty endpoint-aligned dyadic blocks. -/
def h15GlobalPostFEBlockSupport (N : ℕ) :
    Finset H15GlobalPostFEBlockKey :=
  (h15PostFECutoffRowSupport N).image h15GlobalPostFERowBlockKey

/-- The canonical fiber of cutoff-supported rows belonging to one block. -/
def h15GlobalPostFERowFiber (N : ℕ)
    (b : H15GlobalPostFEBlockKey) : Finset (H15LaurentRowIndex N) :=
  (h15PostFECutoffRowSupport N).filter fun i =>
    h15GlobalPostFERowBlockKey i = b

/-- Intrinsic membership criterion for an endpoint-aligned PostFE block.
It makes the orientation swap invisible by stating the result directly in
the inverse and modulus variables. -/
theorem mem_h15PostFELocalizedLaurentRowIndices_iff
    {N g U Q : ℕ} {i : H15LaurentRowIndex N} :
    i ∈ h15PostFELocalizedLaurentRowIndices N g U Q ↔
      h15LaurentG i = g ∧
        h15BettinChandeeInverseVariable i ∈
          h15BettinChandeeSupportedNatBlock N g U ∧
        h15BettinChandeeModulusVariable i ∈
          h15BettinChandeeSupportedNatBlock N g Q := by
  constructor
  · intro hi
    have hs := h15PostFELocalizedLaurentRow_postFE_support hi
    rcases Finset.mem_union.mp hi with hi0 | hi1
    · exact ⟨(mem_h15DoublyLocalizedLaurentRowIndices.mp
          (mem_h15DoublyLocalizedOrientationZeroIndices.mp hi0).1).1,
        hs.1, hs.2⟩
    · exact ⟨(mem_h15DoublyLocalizedLaurentRowIndices.mp
          (mem_h15DoublyLocalizedOrientationOneIndices.mp hi1).1).1,
        hs.1, hs.2⟩
  · rintro ⟨hg, hu, hq⟩
    rcases h15LaurentOrientation_eq_zero_or_one i with hzero | hone
    · apply Finset.mem_union_left
      rw [mem_h15DoublyLocalizedOrientationZeroIndices,
        mem_h15DoublyLocalizedLaurentRowIndices]
      simpa [h15BettinChandeeInverseVariable,
        h15BettinChandeeModulusVariable, hzero] using
          And.intro hg (And.intro hu hq)
    · apply Finset.mem_union_right
      rw [mem_h15DoublyLocalizedOrientationOneIndices,
        mem_h15DoublyLocalizedLaurentRowIndices]
      have hne : h15LaurentOrientation i ≠ 0 := by omega
      simp only [h15BettinChandeeInverseVariable,
        h15BettinChandeeModulusVariable, hne] at hu hq
      exact ⟨⟨hg, hq, hu⟩, hone⟩

theorem sum_h15GlobalPostFERowFiber
    {M : Type*} [AddCommMonoid M] (N : ℕ)
    (f : H15LaurentRowIndex N → M) :
    (∑ b ∈ h15GlobalPostFEBlockSupport N,
        ∑ i ∈ h15GlobalPostFERowFiber N b, f i) =
      ∑ i ∈ h15PostFECutoffRowSupport N, f i := by
  classical
  unfold h15GlobalPostFEBlockSupport h15GlobalPostFERowFiber
  rw [Finset.sum_fiberwise_eq_sum_filter]
  have hfilter :
      (h15PostFECutoffRowSupport N).filter
          (fun i => h15GlobalPostFERowBlockKey i ∈
            (h15PostFECutoffRowSupport N).image
              h15GlobalPostFERowBlockKey) =
        h15PostFECutoffRowSupport N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · exact fun hi => hi.1
    · intro hi
      exact ⟨hi, ⟨i, hi, rfl⟩⟩
  rw [hfilter]

theorem h15GlobalPostFEBlockQ_pos
    {N : ℕ} {b : H15GlobalPostFEBlockKey}
    (hb : b ∈ h15GlobalPostFEBlockSupport N) :
    0 < h15GlobalPostFEBlockQ b := by
  classical
  rw [h15GlobalPostFEBlockSupport, Finset.mem_image] at hb
  rcases hb with ⟨i, _hi, rfl⟩
  exact h15CanonicalDyadicScale_pos _

/-- On every canonical block in the global support, the abstract row fiber
is exactly the existing endpoint-aligned NB12 localization.  This is the
finite coverage theorem needed to regard the subsequent sum as genuinely
global rather than as a list of unrelated local expressions. -/
theorem h15GlobalPostFERowFiber_eq_localized
    {N : ℕ} {b : H15GlobalPostFEBlockKey}
    (hb : b ∈ h15GlobalPostFEBlockSupport N) :
    h15GlobalPostFERowFiber N b =
      h15PostFELocalizedLaurentRowIndices N
        (h15GlobalPostFEBlockG b) (h15GlobalPostFEBlockU b)
        (h15GlobalPostFEBlockQ b) := by
  classical
  rw [h15GlobalPostFEBlockSupport, Finset.mem_image] at hb
  rcases hb with ⟨j, hj, rfl⟩
  ext i
  simp only [h15GlobalPostFERowFiber, Finset.mem_filter,
    mem_h15PostFELocalizedLaurentRowIndices_iff]
  constructor
  · rintro ⟨hiCutoff, hkey⟩
    have hcoords := Finset.mem_filter.mp hiCutoff
    simp only [Finset.mem_univ, true_and] at hcoords
    have hg : h15LaurentG i = h15LaurentG j := by
      exact congrArg (fun z : H15GlobalPostFEBlockKey => z.1.1) hkey
    have huEq :
        h15CanonicalDyadicScale (h15BettinChandeeInverseVariable i) =
          h15CanonicalDyadicScale (h15BettinChandeeInverseVariable j) := by
      exact congrArg (fun z : H15GlobalPostFEBlockKey => z.1.2) hkey
    have hqEq :
        h15CanonicalDyadicScale (h15BettinChandeeModulusVariable i) =
          h15CanonicalDyadicScale (h15BettinChandeeModulusVariable j) := by
      exact congrArg (fun z : H15GlobalPostFEBlockKey => z.2) hkey
    refine ⟨hg, ?_, ?_⟩
    · rw [mem_h15BettinChandeeSupportedNatBlock]
      refine ⟨?_, ?_, ?_⟩
      · change h15CanonicalDyadicScale
          (h15BettinChandeeInverseVariable j) ≤ _
        rw [← huEq]
        exact h15CanonicalDyadicScale_le
          (h15BettinChandeeInverseVariable_pos i).ne'
      · change _ < 2 * h15CanonicalDyadicScale
          (h15BettinChandeeInverseVariable j)
        rw [← huEq]
        exact lt_two_mul_h15CanonicalDyadicScale _
      · rcases h15LaurentOrientation_eq_zero_or_one i with hzero | hone
        · simpa [h15BettinChandeeInverseVariable, hzero, hg] using hcoords.1
        · have hne : h15LaurentOrientation i ≠ 0 := by omega
          simpa [h15BettinChandeeInverseVariable, hne, hg] using hcoords.2
    · rw [mem_h15BettinChandeeSupportedNatBlock]
      refine ⟨?_, ?_, ?_⟩
      · change h15CanonicalDyadicScale
          (h15BettinChandeeModulusVariable j) ≤ _
        rw [← hqEq]
        exact h15CanonicalDyadicScale_le
          (h15BettinChandeeModulusVariable_pos i).ne'
      · change _ < 2 * h15CanonicalDyadicScale
          (h15BettinChandeeModulusVariable j)
        rw [← hqEq]
        exact lt_two_mul_h15CanonicalDyadicScale _
      · rcases h15LaurentOrientation_eq_zero_or_one i with hzero | hone
        · simpa [h15BettinChandeeModulusVariable, hzero, hg] using hcoords.2
        · have hne : h15LaurentOrientation i ≠ 0 := by omega
          simpa [h15BettinChandeeModulusVariable, hne, hg] using hcoords.1
  · rintro ⟨hg, hu, hq⟩
    have huBounds := mem_h15BettinChandeeSupportedNatBlock.mp hu
    have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hq
    have huScale := h15CanonicalDyadicScale_eq_of_mem_same_block
      huBounds.1 huBounds.2.1
    have hqScale := h15CanonicalDyadicScale_eq_of_mem_same_block
      hqBounds.1 hqBounds.2.1
    refine ⟨?_, ?_⟩
    · rw [h15PostFECutoffRowSupport, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases h15LaurentOrientation_eq_zero_or_one i with hzero | hone
      · simpa [h15BettinChandeeInverseVariable,
          h15BettinChandeeModulusVariable, hzero, hg] using
            And.intro huBounds.2.2 hqBounds.2.2
      · have hne : h15LaurentOrientation i ≠ 0 := by omega
        simpa [h15BettinChandeeInverseVariable,
          h15BettinChandeeModulusVariable, hne, hg] using
            And.intro hqBounds.2.2 huBounds.2.2
    · apply Prod.ext
      · apply Prod.ext
        · exact hg
        · exact huScale
      · exact hqScale

/-- Summing the endpoint-aligned local row sets over the canonical block
support reproduces the complete cutoff-supported row box exactly. -/
theorem sum_h15PostFELocalizedLaurentRowIndices_global
    {M : Type*} [AddCommMonoid M] (N : ℕ)
    (f : H15LaurentRowIndex N → M) :
    (∑ b ∈ h15GlobalPostFEBlockSupport N,
        ∑ i ∈ h15PostFELocalizedLaurentRowIndices N
            (h15GlobalPostFEBlockG b) (h15GlobalPostFEBlockU b)
            (h15GlobalPostFEBlockQ b),
          f i) =
      ∑ i ∈ h15PostFECutoffRowSupport N, f i := by
  classical
  rw [← sum_h15GlobalPostFERowFiber N f]
  apply Finset.sum_congr rfl
  intro b hb
  rw [h15GlobalPostFERowFiber_eq_localized hb]

theorem h15LaurentRowWeight_eq_zero_of_not_mem_cutoff
    {N : ℕ} {i : H15LaurentRowIndex N}
    (hi : i ∉ h15PostFECutoffRowSupport N) :
    h15LaurentRowWeight i = 0 := by
  unfold h15LaurentRowWeight
  rw [if_neg]
  intro hvalid
  apply hi
  rw [h15PostFECutoffRowSupport, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hvalid.1, hvalid.2.1⟩

/-- Weighted global coverage of the literal Laurent cube.  Rows outside the
hyperbolic cutoff are present in the raw finite type but have exactly zero
H15 weight. -/
theorem sum_h15PostFELocalized_weighted_eq_fullLaurentCube
    (N : ℕ) (F : H15LaurentRowIndex N → ℂ) :
    (∑ b ∈ h15GlobalPostFEBlockSupport N,
        ∑ i ∈ h15PostFELocalizedLaurentRowIndices N
            (h15GlobalPostFEBlockG b) (h15GlobalPostFEBlockU b)
            (h15GlobalPostFEBlockQ b),
          h15LaurentRowWeight i * F i) =
      ∑ i : H15LaurentRowIndex N, h15LaurentRowWeight i * F i := by
  rw [sum_h15PostFELocalizedLaurentRowIndices_global]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _hi hiCutoff
  rw [h15LaurentRowWeight_eq_zero_of_not_mem_cutoff hiCutoff, zero_mul]

/-! ## Global linear functional-equation assembly -/

/-- The complete linear transformed-frequency slice, obtained by summing
the literal endpoint-aligned NB12 blocks over the canonical global support. -/
noncomputable def h15GlobalPostFELinearFrequencySlice
    (n r : ℕ) (t : ℝ) : ℂ :=
  ∑ b ∈ h15GlobalPostFEBlockSupport (logTaperLength n),
    h15PostFELocalizedDirectAdditiveFrequencySlice n
      (h15GlobalPostFEBlockG b) (h15GlobalPostFEBlockU b)
      (h15GlobalPostFEBlockQ b) r t

/-- The block assembly is exactly the complete Laurent-cube sum of one
functional-equation frequency. -/
theorem h15GlobalPostFELinearFrequencySlice_eq_fullLaurentCube
    (n r : ℕ) (t : ℝ) :
    h15GlobalPostFELinearFrequencySlice n r t =
      ∑ i : H15LaurentRowIndex (logTaperLength n),
        h15LaurentRowWeight i *
          bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
            (h15LaurentRow i).numerator
            (h15LaurentRow i).denominator
            (h15LaurentRow i).coprime r t := by
  classical
  unfold h15GlobalPostFELinearFrequencySlice
    h15PostFELocalizedDirectAdditiveFrequencySlice
  calc
    (∑ b ∈ h15GlobalPostFEBlockSupport (logTaperLength n),
        ∑ i ∈ h15PostFELocalizedLaurentRowIndices
            (logTaperLength n) (h15GlobalPostFEBlockG b)
            (h15GlobalPostFEBlockU b) (h15GlobalPostFEBlockQ b),
          h15DirectAdditiveFixedHeightSummand (logTaperLength n)
            (h15ContourDamping n) (i, r) t) =
      ∑ b ∈ h15GlobalPostFEBlockSupport (logTaperLength n),
        ∑ i ∈ h15PostFELocalizedLaurentRowIndices
            (logTaperLength n) (h15GlobalPostFEBlockG b)
            (h15GlobalPostFEBlockU b) (h15GlobalPostFEBlockQ b),
          h15LaurentRowWeight i *
            bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
              (h15LaurentRow i).numerator
              (h15LaurentRow i).denominator
              (h15LaurentRow i).coprime r t := by
        apply Finset.sum_congr rfl
        intro b _hb
        apply Finset.sum_congr rfl
        intro i _hi
        exact (h15WeightedFrequencyTerm_eq_directFixedHeightSummand
          (logTaperLength n) (h15ContourDamping n) (i, r) t).symm
    _ = _ := sum_h15PostFELocalized_weighted_eq_fullLaurentCube
      (logTaperLength n) (fun i =>
        bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
          (h15LaurentRow i).numerator
          (h15LaurentRow i).denominator
          (h15LaurentRow i).coprime r t)

/-- The complete finite low-frequency right-line aggregate is therefore a
finite sum of the globally assembled linear frequency slices. -/
theorem h15ThreeHalfLowFrequencyAggregate_eq_globalPostFESlices
    (n K : ℕ) (t : ℝ) :
    h15ThreeHalfLowFrequencyAggregate n K t =
      ∑ r ∈ Finset.range (K + 1),
        h15GlobalPostFELinearFrequencySlice n r t := by
  classical
  unfold h15ThreeHalfLowFrequencyAggregate
  simp_rw [bblsActiveThreeHalfLowFrequency_eq_sum_frequencyTerm,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  exact (h15GlobalPostFELinearFrequencySlice_eq_fullLaurentCube n r t).symm

/-! ## Cross-block quadratic ledger -/

/-- The signed ordered interaction between distinct canonical dyadic blocks.
This term is absent if one merely sums the norm squares of the local slices. -/
noncomputable def h15GlobalPostFECrossBlockInteraction
    (n r : ℕ) (t : ℝ) : ℝ :=
  ∑ b ∈ h15GlobalPostFEBlockSupport (logTaperLength n),
    ∑ c ∈ (h15GlobalPostFEBlockSupport (logTaperLength n)).erase b,
      (conj
          (h15PostFELocalizedDirectAdditiveFrequencySlice n
            (h15GlobalPostFEBlockG b) (h15GlobalPostFEBlockU b)
            (h15GlobalPostFEBlockQ b) r t) *
        h15PostFELocalizedDirectAdditiveFrequencySlice n
          (h15GlobalPostFEBlockG c) (h15GlobalPostFEBlockU c)
          (h15GlobalPostFEBlockQ c) r t).re

/-- Exact quadratic expansion of the globally assembled linear slice.  The
cross-block ledger is signed and cannot be discarded by summing local
quadratic estimates. -/
theorem normSq_h15GlobalPostFELinearFrequencySlice_eq_local_add_cross
    (n r : ℕ) (t : ℝ) :
    Complex.normSq (h15GlobalPostFELinearFrequencySlice n r t) =
      (∑ b ∈ h15GlobalPostFEBlockSupport (logTaperLength n),
        Complex.normSq
          (h15PostFELocalizedDirectAdditiveFrequencySlice n
            (h15GlobalPostFEBlockG b) (h15GlobalPostFEBlockU b)
            (h15GlobalPostFEBlockQ b) r t)) +
        h15GlobalPostFECrossBlockInteraction n r t := by
  unfold h15GlobalPostFELinearFrequencySlice
    h15GlobalPostFECrossBlockInteraction
  exact normSq_sum_eq_sum_normSq_add_orderedOffDiagonal
    (h15GlobalPostFEBlockSupport (logTaperLength n))
    (fun b => h15PostFELocalizedDirectAdditiveFrequencySlice n
      (h15GlobalPostFEBlockG b) (h15GlobalPostFEBlockU b)
      (h15GlobalPostFEBlockQ b) r t)

/-! ## Global sum of the literal local transforms -/

/-- Sum of the literal NB12 correction-preserving transform over every
canonical nonempty dyadic block.  Frequency and contour height remain
explicit parameters; neither is silently summed or integrated. -/
noncomputable def h15GlobalPostFEJointCorrectionTransform
    (n r : ℕ) (t : ℝ) : ℝ :=
  ∑ b ∈ h15GlobalPostFEBlockSupport (logTaperLength n),
    h15PostFEActualJointCorrectionTransform n
      (h15GlobalPostFEBlockG b) (h15GlobalPostFEBlockU b)
      (h15GlobalPostFEBlockQ b) r t

noncomputable def h15GlobalPostFEMeanZeroVariation
    (n r : ℕ) (t : ℝ) : ℝ :=
  ∑ b ∈ h15GlobalPostFEBlockSupport (logTaperLength n),
    h15PostFEResidueMeanZeroVariation n
      (h15GlobalPostFEBlockG b) (h15GlobalPostFEBlockU b)
      (h15GlobalPostFEBlockQ b) r t

noncomputable def h15GlobalPostFECenteredLiftDefect
    (n r : ℕ) (t : ℝ) : ℝ :=
  ∑ b ∈ h15GlobalPostFEBlockSupport (logTaperLength n),
    h15PostFECenteredLiftDefect n
      (h15GlobalPostFEBlockG b) (h15GlobalPostFEBlockU b)
      (h15GlobalPostFEBlockQ b) r t

/-- Exact global assembly of the local correction-preserving identity.  The
only analytic side condition is the nonvanishing of the common hyperbolic
normalization at the displayed contour height. -/
theorem h15GlobalPostFECenteredLiftDefect_eq_meanZero_sub_transform
    (n r : ℕ) (t : ℝ)
    (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15GlobalPostFECenteredLiftDefect n r t =
      h15GlobalPostFEMeanZeroVariation n r t -
        h15GlobalPostFEJointCorrectionTransform n r t := by
  classical
  unfold h15GlobalPostFECenteredLiftDefect
    h15GlobalPostFEMeanZeroVariation
    h15GlobalPostFEJointCorrectionTransform
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  exact h15PostFECenteredLiftDefect_eq_meanZero_sub_commonAdditiveTransfer
    n (h15GlobalPostFEBlockG b) (h15GlobalPostFEBlockU b)
      (h15GlobalPostFEBlockQ b) r t
      (h15GlobalPostFEBlockQ_pos hb) hS

/-! ## Exact bridge defect to the certified energy -/

/-- What is still missing after the literal global PostFE block sum: the
undamped, linear Estermann endpoint amplitude minus the fixed-frequency,
fixed-height quadratic PostFE transform. -/
noncomputable def h15UndampedPostFEBridgeDefect
    (n r : ℕ) (t : ℝ) : ℝ :=
  (h15AdditionalResidueAmplitude n).im -
    h15GlobalPostFEJointCorrectionTransform n r t

/-- Lossless energy identity with the global PostFE sum inserted.  This is
the strongest currently justified specialization: proving that the bridge
defect vanishes or has a usable integral representation is a separate
theorem, not finite algebra. -/
theorem logTaperL2Error_eq_elementaryEndpoint_add_globalPostFE_add_defect
    (n r : ℕ) (t : ℝ) :
    logTaperL2Error n =
      h15CertifiedElementaryEndpointLedger n +
        h15GlobalPostFEJointCorrectionTransform n r t +
        h15UndampedPostFEBridgeDefect n r t := by
  rw [logTaperL2Error_eq_elementaryEndpoint_add_additionalResidueAmplitude_im]
  unfold h15UndampedPostFEBridgeDefect
  ring

/-- The bridge closes exactly when the global PostFE sum equals the
undamped endpoint amplitude.  No local or damped estimate proves this
statement automatically. -/
theorem h15UndampedPostFEBridgeDefect_eq_zero_iff
    (n r : ℕ) (t : ℝ) :
    h15UndampedPostFEBridgeDefect n r t = 0 ↔
      h15GlobalPostFEJointCorrectionTransform n r t =
        (h15AdditionalResidueAmplitude n).im := by
  unfold h15UndampedPostFEBridgeDefect
  constructor <;> intro h <;> linarith

/-- Equivalent form exhibiting the inverse adaptive-damping loss in the
endpoint amplitude. -/
theorem h15UndampedPostFEBridgeDefect_eq_rescaledResidue_sub_transform
    (n r : ℕ) (t : ℝ) :
    h15UndampedPostFEBridgeDefect n r t =
      (((h15ContourDamping n : ℂ)⁻¹ *
          h15GlobalAdditionalResidue n).im) -
        h15GlobalPostFEJointCorrectionTransform n r t := by
  rw [h15ContourDamping_inv_mul_globalAdditionalResidue]
  rfl

end NBMellinTools.NB15
