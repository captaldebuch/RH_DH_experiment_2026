import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmHyperbolicKernelNormalForm
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmRectangularAbel

/-!
# Rectangular Abel instantiation for the Ehm near core

This file applies the generic rectangular Abel transform to the exact signed
Möbius-pair part of the H15 Ehm near core.

The shifted coordinates are

```text
m = i + 1,
d = X + 1 + j.
```

The arithmetic array is the pure sign product `mu(m) * mu(d)`.  Every taper,
reciprocal factor, hyperbolic `q`-row, and `R1` value remains in the kernel.
This makes the rectangular prefix factor exactly into two Mertens increments.

The completed main term and the linear remainder do not naturally live in
the same `(m,d)` coordinates.  They are therefore retained on the two sides
of the final exact identity rather than embedded at arbitrary cells.  The
result is a genuine correction-coupled decomposition, but the Abel inequality
controls only the near bilinear constituent.  A later analytic argument must
still compare its signed Abel terms with the retained main and linear pieces.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularInstantiation

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicNearCoreReindex
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbolicKernelNormalForm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit

/-! ## Shifted coefficient and complete near kernel -/

/-- Pure signed arithmetic coefficient on the shifted near rectangle. -/
noncomputable def ehmShiftedNearArithmeticCoeff
    (X i j : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
    ((ArithmeticFunction.moebius (X + 1 + j) : ℤ) : ℝ)

/-- Every non-sign factor in one shifted Ehm near summand. -/
noncomputable def ehmShiftedNearCompleteKernel
    (R1 : ℝ → ℝ) (X J i j : ℕ) : ℝ :=
  (ehmDyadicNearPairAmplitude X (i + 1) (X + 1 + j) /
      ((i + 1 : ℕ) : ℝ)) *
    ehmDyadicReciprocalQKernel R1 J (i + 1) (X + 1 + j)

/-- The shifted inclusive rectangle, with coordinate maxima `(M,L)`. -/
noncomputable def ehmShiftedNearRectangularSum
    (R1 : ℝ → ℝ) (X J M L : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (L + 1),
    ehmShiftedNearArithmeticCoeff X i j *
      ehmShiftedNearCompleteKernel R1 X J i j

private theorem sum_Icc_shift
    (f : ℕ → ℝ) (a L : ℕ) :
    (∑ n ∈ Finset.Icc a (a + L), f n) =
      ∑ j ∈ Finset.range (L + 1), f (a + j) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlength : a + L + 1 - a = L + 1 := by omega
  rw [hlength]

private theorem sum_Icc_one_succ
    (f : ℕ → ℝ) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 (M + 1), f n) =
      ∑ i ∈ Finset.range (M + 1), f (i + 1) := by
  simpa [Nat.add_comm] using sum_Icc_shift f 1 M

/-- Exact reindexing from the Ehm `(m,d)` interval to the shifted rectangle. -/
theorem ehmDyadicNearMobiusKernelMRange_eq_shiftedRectangle
    (R1 : ℝ → ℝ) (X J M L : ℕ) :
    ehmDyadicNearMobiusKernelMRange R1 X (X + 1 + L) J 1 (M + 1) =
      ehmShiftedNearRectangularSum R1 X J M L := by
  classical
  unfold ehmDyadicNearMobiusKernelMRange
    ehmShiftedNearRectangularSum
  rw [sum_Icc_one_succ (fun m =>
    ∑ d ∈ Finset.Icc (X + 1) (X + 1 + L),
      ((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)) / (m : ℝ)) *
        ehmDyadicNearPairAmplitude X m d *
          ehmDyadicReciprocalQKernel R1 J m d) M]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_Icc_shift]
  apply Finset.sum_congr rfl
  intro j _
  unfold ehmShiftedNearArithmeticCoeff ehmShiftedNearCompleteKernel
  ring

/-! ## Exact discrepancy factorization -/

/-- A shifted real Mertens increment with inclusive coordinate maximum `K`. -/
noncomputable def ehmShiftedMertensPrefix (a K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (K + 1),
    ((ArithmeticFunction.moebius (a + i) : ℤ) : ℝ)

/-- Every rectangular prefix of the pure sign array factors into two
one-dimensional Mertens increments. -/
theorem rectangularPrefix_ehmShiftedNearArithmeticCoeff
    (X i j : ℕ) :
    rectangularPrefix (ehmShiftedNearArithmeticCoeff X) i j =
      ehmShiftedMertensPrefix 1 i *
        ehmShiftedMertensPrefix (X + 1) j := by
  unfold rectangularPrefix ehmShiftedNearArithmeticCoeff
    ehmShiftedMertensPrefix
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  simp only [Nat.add_comm u 1]

/-- Unconditional termwise bound for a shifted Mertens prefix.  This is used
only as the baseline stop test; any arithmetic progress must improve it. -/
theorem abs_ehmShiftedMertensPrefix_le_length
    (a K : ℕ) :
    |ehmShiftedMertensPrefix a K| ≤ (K + 1 : ℕ) := by
  unfold ehmShiftedMertensPrefix
  calc
    |∑ i ∈ Finset.range (K + 1),
        ((ArithmeticFunction.moebius (a + i) : ℤ) : ℝ)| ≤
      ∑ i ∈ Finset.range (K + 1),
        |((ArithmeticFunction.moebius (a + i) : ℤ) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (K + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a + i)
    _ = (K + 1 : ℕ) := by simp

/-- Baseline rectangular discrepancy bound for the shifted sign array. -/
theorem abs_rectangularPrefix_ehmShiftedNearArithmeticCoeff_le_area
    (X i j : ℕ) :
    |rectangularPrefix (ehmShiftedNearArithmeticCoeff X) i j| ≤
      ((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
  rw [rectangularPrefix_ehmShiftedNearArithmeticCoeff, abs_mul]
  exact mul_le_mul
    (abs_ehmShiftedMertensPrefix_le_length 1 i)
    (abs_ehmShiftedMertensPrefix_le_length (X + 1) j)
    (abs_nonneg _) (by positivity)

/-! ## Instantiated Abel identity and transfer bounds -/

/-- Exact rectangular Abel decomposition of the shifted Ehm near sum. -/
theorem ehmShiftedNearRectangularSum_eq_abel
    (R1 : ℝ → ℝ) (X J M L : ℕ) :
    ehmShiftedNearRectangularSum R1 X J M L =
      rectangularPrefix (ehmShiftedNearArithmeticCoeff X) M L *
          ehmShiftedNearCompleteKernel R1 X J M L +
        (∑ i ∈ Finset.range M,
          rectangularPrefix (ehmShiftedNearArithmeticCoeff X) i L *
            firstForwardDifference
              (ehmShiftedNearCompleteKernel R1 X J) i L) +
        (∑ j ∈ Finset.range L,
          rectangularPrefix (ehmShiftedNearArithmeticCoeff X) M j *
            secondForwardDifference
              (ehmShiftedNearCompleteKernel R1 X J) M j) +
        ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range L,
          rectangularPrefix (ehmShiftedNearArithmeticCoeff X) i j *
            mixedForwardDifference
              (ehmShiftedNearCompleteKernel R1 X J) i j := by
  exact rectangularAbel_identity
    (ehmShiftedNearArithmeticCoeff X)
    (ehmShiftedNearCompleteKernel R1 X J) M L

/-- Direct signed transfer with the unconditional area discrepancy. -/
theorem abs_ehmShiftedNearRectangularSum_le_area_mul_variation
    (R1 : ℝ → ℝ) (X J M L : ℕ) :
    |ehmShiftedNearRectangularSum R1 X J M L| ≤
      (((M + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ)) *
        rectangularVariation (ehmShiftedNearCompleteKernel R1 X J) M L := by
  apply abs_rectangularSum_le_discrepancy_mul_variation
  intro i hi j hj
  exact (abs_rectangularPrefix_ehmShiftedNearArithmeticCoeff_le_area X i j).trans
    (mul_le_mul
      (by exact_mod_cast Nat.succ_le_succ hi)
      (by exact_mod_cast Nat.succ_le_succ hj)
      (by positivity) (by positivity))

/-- The localized specialization, retaining the exact Mertens prefix at each
kernel difference rather than replacing all prefixes by one supremum. -/
theorem abs_ehmShiftedNearRectangularSum_le_weightedAbelCost
    (R1 : ℝ → ℝ) (X J M L : ℕ) :
    |ehmShiftedNearRectangularSum R1 X J M L| ≤
      rectangularWeightedTransferCost
        (ehmShiftedNearArithmeticCoeff X)
        (ehmShiftedNearCompleteKernel R1 X J) M L := by
  exact abs_rectangularSum_le_weightedTransferCost
    (ehmShiftedNearArithmeticCoeff X)
    (ehmShiftedNearCompleteKernel R1 X J) M L

/-- Coarse product stop test after also replacing kernel variation by a
uniform pointwise bound on the rectangle and its one-step collar. -/
theorem abs_ehmShiftedNearRectangularSum_le_area_sq_mul_kernelSup
    (R1 : ℝ → ℝ) (X J M L : ℕ) (H : ℝ)
    (hK : ∀ i ≤ M + 1, ∀ j ≤ L + 1,
      |ehmShiftedNearCompleteKernel R1 X J i j| ≤ H) :
    |ehmShiftedNearRectangularSum R1 X J M L| ≤
      (((M + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ)) *
        (H * ((2 * M + 1 : ℕ) : ℝ) * ((2 * L + 1 : ℕ) : ℝ)) := by
  exact (abs_ehmShiftedNearRectangularSum_le_area_mul_variation
    R1 X J M L).trans (mul_le_mul_of_nonneg_left
      (rectangularVariation_le_of_abs_le
        (ehmShiftedNearCompleteKernel R1 X J) M L H hK)
      (by positivity))

/-! ## The exact H15 polynomial-cutoff rectangle -/

/-- Maximum shifted `m` coordinate for `1 <= m <= 2X`. -/
def ehmH15NearMMax (X : ℕ) : ℕ := 2 * X - 1

/-- Maximum shifted `d` coordinate for `X+1 <= d <= D(X)`. -/
def ehmH15NearDMax (X : ℕ) : ℕ :=
  ehmExplicitFarCutoff X - (X + 1)

theorem ehmH15NearMMax_add_one (X : ℕ) (hX : 1 ≤ X) :
    ehmH15NearMMax X + 1 = 2 * X := by
  unfold ehmH15NearMMax
  omega

theorem ehmH15NearDMax_restore (X : ℕ) (hX : 1 ≤ X) :
    X + 1 + ehmH15NearDMax X = ehmExplicitFarCutoff X := by
  unfold ehmH15NearDMax
  apply Nat.add_sub_of_le
  exact (show X + 1 ≤ 2 * X by omega).trans
    (two_mul_le_ehmExplicitFarCutoff X)

/-- The number of `d`-coordinates in the exact near rectangle is `D(X)-X`.
This is the source of the eighth-degree side length in the global stop test. -/
theorem ehmH15NearDMax_add_one (X : ℕ) (hX : 1 ≤ X) :
    ehmH15NearDMax X + 1 = ehmExplicitFarCutoff X - X := by
  have hcut : X + 1 ≤ ehmExplicitFarCutoff X :=
    (show X + 1 ≤ 2 * X by omega).trans
      (two_mul_le_ehmExplicitFarCutoff X)
  unfold ehmH15NearDMax
  omega

/-- The exact near Möbius kernel at the proved far cutoff is the shifted
rectangle to which the discrepancy and variation calculations apply. -/
theorem ehmH15NearMobiusKernel_eq_shiftedRectangle
    (R1 : ℝ → ℝ) (X J : ℕ) (hX : 1 ≤ X) :
    ehmDyadicNearMobiusKernelMRange R1 X (ehmExplicitFarCutoff X) J
        1 (2 * X) =
      ehmShiftedNearRectangularSum R1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X) := by
  rw [← ehmH15NearMMax_add_one X hX,
    ← ehmH15NearDMax_restore X hX]
  exact ehmDyadicNearMobiusKernelMRange_eq_shiftedRectangle
    R1 X J (ehmH15NearMMax X) (ehmH15NearDMax X)

/-- Exact-cutoff specialization of the unconditional discrepancy–variation
transfer.  The discrepancy factor is the full rectangle area
`2X * (D(X)-X)`; no asymptotic cancellation has been inserted. -/
theorem abs_ehmH15NearMobiusKernel_le_area_mul_variation
    (R1 : ℝ → ℝ) (X J : ℕ) (hX : 1 ≤ X) :
    |ehmDyadicNearMobiusKernelMRange R1 X (ehmExplicitFarCutoff X) J
        1 (2 * X)| ≤
      (((2 * X : ℕ) : ℝ) *
          ((ehmExplicitFarCutoff X - X : ℕ) : ℝ)) *
        rectangularVariation (ehmShiftedNearCompleteKernel R1 X J)
          (ehmH15NearMMax X) (ehmH15NearDMax X) := by
  rw [ehmH15NearMobiusKernel_eq_shiftedRectangle R1 X J hX]
  simpa [ehmH15NearMMax_add_one X hX,
    ehmH15NearDMax_add_one X hX] using
      abs_ehmShiftedNearRectangularSum_le_area_mul_variation R1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X)

/-- The exact-cutoff localized Abel certificate.  This is strictly more
informative than the global area-discrepancy bound, but proving that it tends
to zero still requires arithmetic compensation between the Mertens prefixes
and the complete coupled finite differences. -/
theorem abs_ehmH15NearMobiusKernel_le_weightedAbelCost
    (R1 : ℝ → ℝ) (X J : ℕ) (hX : 1 ≤ X) :
    |ehmDyadicNearMobiusKernelMRange R1 X (ehmExplicitFarCutoff X) J
        1 (2 * X)| ≤
      rectangularWeightedTransferCost
        (ehmShiftedNearArithmeticCoeff X)
        (ehmShiftedNearCompleteKernel R1 X J)
        (ehmH15NearMMax X) (ehmH15NearDMax X) := by
  rw [ehmH15NearMobiusKernel_eq_shiftedRectangle R1 X J hX]
  exact abs_ehmShiftedNearRectangularSum_le_weightedAbelCost R1 X J
    (ehmH15NearMMax X) (ehmH15NearDMax X)

/-- The corresponding pointwise-kernel stop test.  It records explicitly
that a uniform kernel bound alone pays both rectangle side lengths twice;
therefore it cannot supply the required decay at the polynomial cutoff. -/
theorem abs_ehmH15NearMobiusKernel_le_area_sq_mul_kernelSup
    (R1 : ℝ → ℝ) (X J : ℕ) (hX : 1 ≤ X) (H : ℝ)
    (hK : ∀ i ≤ ehmH15NearMMax X + 1,
      ∀ j ≤ ehmH15NearDMax X + 1,
        |ehmShiftedNearCompleteKernel R1 X J i j| ≤ H) :
    |ehmDyadicNearMobiusKernelMRange R1 X (ehmExplicitFarCutoff X) J
        1 (2 * X)| ≤
      (((2 * X : ℕ) : ℝ) *
          ((ehmExplicitFarCutoff X - X : ℕ) : ℝ)) *
        (H * ((2 * ehmH15NearMMax X + 1 : ℕ) : ℝ) *
          ((2 * ehmH15NearDMax X + 1 : ℕ) : ℝ)) := by
  rw [ehmH15NearMobiusKernel_eq_shiftedRectangle R1 X J hX]
  simpa [ehmH15NearMMax_add_one X hX,
    ehmH15NearDMax_add_one X hX] using
      abs_ehmShiftedNearRectangularSum_le_area_sq_mul_kernelSup
        R1 X J (ehmH15NearMMax X) (ehmH15NearDMax X) H hK

/-- The complete coupled H15 near core with its near constituent replaced by
the exact Abel rectangle.  Main and linear corrections retain their signs. -/
theorem ehmDyadicExplicitCutoffCoupledNearCore_eq_main_add_shifted_add_remainder
    (R1 : ℝ → ℝ) (X J : ℕ) (hX : 1 ≤ X) :
    ehmDyadicExplicitCoupledNearCore R1 X (ehmExplicitFarCutoff X) J =
      ehmDyadicFullMainJointSum R1 X J +
        ehmShiftedNearRectangularSum R1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) +
        ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N := by
  unfold ehmDyadicExplicitCoupledNearCore
  rw [ehmDyadicNearComplementaryJointSum_eq_neg_mobiusBilinear,
    sub_neg_eq_add]
  unfold ehmDyadicNearMobiusBilinearJointSum
  rw [ehmDyadicNearMobiusBilinearMRange_eq_kernelMRange]
  rw [ehmH15NearMobiusKernel_eq_shiftedRectangle R1 X J hX]

/-- The full correction-coupled near core written in its four exact Abel
pieces.  This is the canonical compensation target: the main and linear
terms must cancel against the *signed sum* of these pieces.  Applying
absolute values to the Abel pieces separately yields the weighted cost above
and loses precisely that remaining cancellation. -/
theorem ehmDyadicExplicitCutoffCoupledNearCore_eq_main_add_abel_add_remainder
    (R1 : ℝ → ℝ) (X J : ℕ) (hX : 1 ≤ X) :
    ehmDyadicExplicitCoupledNearCore R1 X (ehmExplicitFarCutoff X) J =
      ehmDyadicFullMainJointSum R1 X J +
        (rectangularPrefix (ehmShiftedNearArithmeticCoeff X)
            (ehmH15NearMMax X) (ehmH15NearDMax X) *
            ehmShiftedNearCompleteKernel R1 X J
              (ehmH15NearMMax X) (ehmH15NearDMax X) +
          (∑ i ∈ Finset.range (ehmH15NearMMax X),
            rectangularPrefix (ehmShiftedNearArithmeticCoeff X) i
                (ehmH15NearDMax X) *
              firstForwardDifference
                (ehmShiftedNearCompleteKernel R1 X J) i
                (ehmH15NearDMax X)) +
          (∑ j ∈ Finset.range (ehmH15NearDMax X),
            rectangularPrefix (ehmShiftedNearArithmeticCoeff X)
                (ehmH15NearMMax X) j *
              secondForwardDifference
                (ehmShiftedNearCompleteKernel R1 X J)
                (ehmH15NearMMax X) j) +
          ∑ i ∈ Finset.range (ehmH15NearMMax X),
            ∑ j ∈ Finset.range (ehmH15NearDMax X),
              rectangularPrefix (ehmShiftedNearArithmeticCoeff X) i j *
                mixedForwardDifference
                  (ehmShiftedNearCompleteKernel R1 X J) i j) +
        ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N := by
  rw [ehmDyadicExplicitCutoffCoupledNearCore_eq_main_add_shifted_add_remainder
    R1 X J hX]
  rw [ehmShiftedNearRectangularSum_eq_abel]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularInstantiation
