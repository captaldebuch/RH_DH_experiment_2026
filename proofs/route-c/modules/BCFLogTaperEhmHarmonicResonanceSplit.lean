import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmHarmonicAbel

/-!
# Resonant/nonresonant split of the normalized Ehm near form

This file partitions the normalized `(m,d)` character form according to the
exact resonance condition `(m : ℤ) ∣ h*d`.  The resonant row is written as a
finite harmonic sum.  The complementary row receives the Abel/geometric
denominator bound.

No absolute value is placed around the resonant form: it is retained for the
required signed coupling with the endpoint, main, and linear corrections.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmHarmonicResonanceSplit

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHarmonicAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerNormalizedCharacters

/-- The real signed coefficient of one normalized near character row. -/
noncomputable def ehmDyadicVaalerNormalizedNearCoefficient
    (X m d : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius m : ℤ) : ℝ) *
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ehmDyadicNearPairAmplitude X m d) / (d : ℝ)

theorem ehmDyadicVaalerNormalizedNearPhaseFormMRange_eq_coefficientSum
    (h : ℤ) (X D J mLo mHi : ℕ) :
    ehmDyadicVaalerNormalizedNearPhaseFormMRange
      h X D J mLo mHi =
        ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
          (ehmDyadicVaalerNormalizedNearCoefficient X m d : ℂ) *
            ehmVaalerHarmonicPhaseRow h J m d := by
  unfold ehmDyadicVaalerNormalizedNearPhaseFormMRange
    ehmDyadicVaalerNormalizedNearCoefficient
  rfl

/-- The exact divisibility-diagonal part of one near `m` interval. -/
noncomputable def ehmDyadicVaalerNormalizedNearResonantMRange
    (h : ℤ) (X D J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
    if (m : ℤ) ∣ h * (d : ℤ) then
      (ehmDyadicVaalerNormalizedNearCoefficient X m d : ℂ) *
        ehmVaalerHarmonicPhaseRow h J m d
    else 0

/-- The complementary genuinely nonresonant part. -/
noncomputable def ehmDyadicVaalerNormalizedNearNonresonantMRange
    (h : ℤ) (X D J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
    if ¬(m : ℤ) ∣ h * (d : ℤ) then
      (ehmDyadicVaalerNormalizedNearCoefficient X m d : ℂ) *
        ehmVaalerHarmonicPhaseRow h J m d
    else 0

/-- Exact partition into the divisibility diagonal and its complement. -/
theorem ehmDyadicVaalerNormalizedNearPhaseFormMRange_eq_resonant_add_nonresonant
    (h : ℤ) (X D J mLo mHi : ℕ) :
    ehmDyadicVaalerNormalizedNearPhaseFormMRange h X D J mLo mHi =
      ehmDyadicVaalerNormalizedNearResonantMRange
        h X D J mLo mHi +
      ehmDyadicVaalerNormalizedNearNonresonantMRange
        h X D J mLo mHi := by
  classical
  rw [ehmDyadicVaalerNormalizedNearPhaseFormMRange_eq_coefficientSum]
  unfold ehmDyadicVaalerNormalizedNearResonantMRange
    ehmDyadicVaalerNormalizedNearNonresonantMRange
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hdiv : (m : ℤ) ∣ h * (d : ℤ)
  · simp [hdiv]
  · simp [hdiv]

/-! ## Closed form of the resonant row -/

/-- On the divisibility diagonal every additive character in the `q` row is
one, so the row is exactly a finite harmonic sum. -/
theorem ehmVaalerHarmonicPhaseRow_of_dvd
    (h : ℤ) (J m d : ℕ) (hm : m ≠ 0)
    (hdiv : (m : ℤ) ∣ h * (d : ℤ)) :
    ehmVaalerHarmonicPhaseRow h J m d =
      ∑ q ∈ Finset.Icc 1 (J / d), (1 : ℂ) / (q : ℂ) := by
  have hphase : ehmVaalerRationalPhase h 1 d m = 1 :=
    (ehmVaalerRationalPhase_one_eq_one_iff_dvd h d m hm).2 hdiv
  unfold ehmVaalerHarmonicPhaseRow
  apply Finset.sum_congr rfl
  intro q _
  rw [ehmVaalerRationalPhase_eq_pow, hphase, one_pow]

/-- The resonant near form with its harmonic row displayed literally. -/
noncomputable def ehmDyadicVaalerNormalizedNearResonantClosedMRange
    (h : ℤ) (X D J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
    if (m : ℤ) ∣ h * (d : ℤ) then
      (ehmDyadicVaalerNormalizedNearCoefficient X m d : ℂ) *
        ∑ q ∈ Finset.Icc 1 (J / d), (1 : ℂ) / (q : ℂ)
    else 0

theorem ehmDyadicVaalerNormalizedNearResonantMRange_eq_closed
    (h : ℤ) (X D J mLo mHi : ℕ) (hmLo : 0 < mLo) :
    ehmDyadicVaalerNormalizedNearResonantMRange
      h X D J mLo mHi =
        ehmDyadicVaalerNormalizedNearResonantClosedMRange
          h X D J mLo mHi := by
  classical
  unfold ehmDyadicVaalerNormalizedNearResonantMRange
    ehmDyadicVaalerNormalizedNearResonantClosedMRange
  apply Finset.sum_congr rfl
  intro m hm
  have hmne : m ≠ 0 :=
    (lt_of_lt_of_le hmLo (Finset.mem_Icc.mp hm).1).ne'
  apply Finset.sum_congr rfl
  intro d _
  by_cases hdiv : (m : ℤ) ∣ h * (d : ℤ)
  · simp only [hdiv, if_true]
    rw [ehmVaalerHarmonicPhaseRow_of_dvd h J m d hmne hdiv]
  · simp [hdiv]

/-! ## Nonresonant majorant -/

/-- The exact termwise majorant supplied by the Abel bound off resonance. -/
noncomputable def ehmDyadicVaalerNormalizedNearNonresonantMajorantMRange
    (h : ℤ) (X D mLo mHi : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
    if ¬(m : ℤ) ∣ h * (d : ℤ) then
      |ehmDyadicVaalerNormalizedNearCoefficient X m d| *
        (2 / ‖ehmVaalerRationalPhase h 1 d m - 1‖)
    else 0

theorem norm_ehmDyadicVaalerNormalizedNearNonresonantMRange_le
    (h : ℤ) (X D J mLo mHi : ℕ) (hmLo : 0 < mLo) :
    ‖ehmDyadicVaalerNormalizedNearNonresonantMRange
      h X D J mLo mHi‖ ≤
        ehmDyadicVaalerNormalizedNearNonresonantMajorantMRange
          h X D mLo mHi := by
  classical
  unfold ehmDyadicVaalerNormalizedNearNonresonantMRange
    ehmDyadicVaalerNormalizedNearNonresonantMajorantMRange
  calc
    ‖∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
        if ¬(m : ℤ) ∣ h * (d : ℤ) then
          (ehmDyadicVaalerNormalizedNearCoefficient X m d : ℂ) *
            ehmVaalerHarmonicPhaseRow h J m d
        else 0‖ ≤
      ∑ m ∈ Finset.Icc mLo mHi,
        ‖∑ d ∈ Finset.Icc (X + 1) D,
          if ¬(m : ℤ) ∣ h * (d : ℤ) then
            (ehmDyadicVaalerNormalizedNearCoefficient X m d : ℂ) *
              ehmVaalerHarmonicPhaseRow h J m d
          else 0‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
        ‖if ¬(m : ℤ) ∣ h * (d : ℤ) then
          (ehmDyadicVaalerNormalizedNearCoefficient X m d : ℂ) *
            ehmVaalerHarmonicPhaseRow h J m d
        else 0‖ := by
      apply Finset.sum_le_sum
      intro m _
      exact norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
        if ¬(m : ℤ) ∣ h * (d : ℤ) then
          |ehmDyadicVaalerNormalizedNearCoefficient X m d| *
            (2 / ‖ehmVaalerRationalPhase h 1 d m - 1‖)
        else 0 := by
      apply Finset.sum_le_sum
      intro m hm
      have hmne : m ≠ 0 :=
        (lt_of_lt_of_le hmLo (Finset.mem_Icc.mp hm).1).ne'
      apply Finset.sum_le_sum
      intro d _
      by_cases hdiv : (m : ℤ) ∣ h * (d : ℤ)
      · simp [hdiv]
      · simp only [hdiv, not_false_eq_true, if_true, norm_mul,
          Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (norm_ehmVaalerHarmonicPhaseRow_le_of_not_dvd
            h J m d hmne hdiv)
          (abs_nonneg _)

/-! ## Full near-frequency split -/

noncomputable def ehmDyadicVaalerNormalizedKernelNearResonant
    (h : ℤ) (X D J U : ℕ) : ℂ :=
  ehmDyadicVaalerNormalizedNearResonantMRange h X D J 1 U +
    ehmDyadicVaalerNormalizedNearResonantMRange
      h X D J (U + 1) (2 * X)

noncomputable def ehmDyadicVaalerNormalizedKernelNearNonresonant
    (h : ℤ) (X D J U : ℕ) : ℂ :=
  ehmDyadicVaalerNormalizedNearNonresonantMRange h X D J 1 U +
    ehmDyadicVaalerNormalizedNearNonresonantMRange
      h X D J (U + 1) (2 * X)

/-- One full normalized frequency consists of the completed main form, the
near resonance diagonal, and the controlled nonresonant complement. -/
theorem ehmDyadicVaalerNormalizedKernelPhaseForm_eq_main_add_resonant_add_nonresonant
    (h : ℤ) (X D J U : ℕ) :
    ehmDyadicVaalerNormalizedKernelPhaseForm h X D J U =
      ehmDyadicVaalerNormalizedMainPhaseForm h X J +
        ehmDyadicVaalerNormalizedKernelNearResonant h X D J U +
        ehmDyadicVaalerNormalizedKernelNearNonresonant h X D J U := by
  unfold ehmDyadicVaalerNormalizedKernelPhaseForm
    ehmDyadicVaalerNormalizedKernelNearResonant
    ehmDyadicVaalerNormalizedKernelNearNonresonant
  rw [ehmDyadicVaalerNormalizedNearPhaseFormMRange_eq_resonant_add_nonresonant,
    ehmDyadicVaalerNormalizedNearPhaseFormMRange_eq_resonant_add_nonresonant]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmHarmonicResonanceSplit
