import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeResidues

/-!
# Resonant coordinates in the paired Ehm additive row

This module splits the exact paired main-plus-near additive row at the
coordinate resonance condition `m ∣ h*n`.  It also partitions the paired row
by residue classes and exposes an arbitrary reduced-residue baseline, whose
phase factor is the finite Ramanujan sum already defined for the main row.

All results are finite algebraic identities.  No cancellation estimate is
asserted for either part of the split.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedResonance

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerNormalizedCharacters
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeResidues

/-! ## One paired row -/

/-- One product-coordinate summand of the paired main-plus-near row. -/
noncomputable def ehmDyadicVaalerPairedAdditiveTerm
    (h : ℤ) (X D m n : ℕ) : ℂ :=
  ((ehmDyadicVaalerPairedProductCoefficient X D m n /
    (n : ℝ) : ℝ) : ℂ) * ehmVaalerRationalPhase h n 1 m

/-- Resonance of the product coordinate `n` at frequency `h` and reciprocal
denominator `m`. -/
def ehmDyadicVaalerPairedCoordinateResonant
    (h : ℤ) (m n : ℕ) : Prop :=
  (m : ℤ) ∣ h * (n : ℤ)

instance (h : ℤ) (m n : ℕ) :
    Decidable (ehmDyadicVaalerPairedCoordinateResonant h m n) := by
  unfold ehmDyadicVaalerPairedCoordinateResonant
  exact Int.decidableDvd _ _

/-- The coordinates at which the rational phase is exactly resonant. -/
noncomputable def ehmDyadicVaalerPairedResonantAdditiveRow
    (h : ℤ) (X D J m : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 J,
    if ehmDyadicVaalerPairedCoordinateResonant h m n then
      ehmDyadicVaalerPairedAdditiveTerm h X D m n
    else 0

/-- The complementary nonresonant coordinates of the same paired row. -/
noncomputable def ehmDyadicVaalerPairedNonresonantAdditiveRow
    (h : ℤ) (X D J m : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 J,
    if ehmDyadicVaalerPairedCoordinateResonant h m n then 0
    else ehmDyadicVaalerPairedAdditiveTerm h X D m n

/-- Exact coordinatewise reconstruction of one paired additive row. -/
theorem ehmDyadicVaalerPairedAdditiveRow_eq_resonant_add_nonresonant
    (h : ℤ) (X D J m : ℕ) :
    ehmDyadicVaalerPairedAdditiveRow h X D J m =
      ehmDyadicVaalerPairedResonantAdditiveRow h X D J m +
        ehmDyadicVaalerPairedNonresonantAdditiveRow h X D J m := by
  classical
  unfold ehmDyadicVaalerPairedAdditiveRow
    ehmDyadicVaalerPairedResonantAdditiveRow
    ehmDyadicVaalerPairedNonresonantAdditiveRow
    ehmDyadicVaalerPairedAdditiveTerm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : ehmDyadicVaalerPairedCoordinateResonant h m n <;>
    simp [hn]

/-- On a resonant coordinate the phase is one, so the resonant row is the
signed paired coefficient mass on those coordinates. -/
theorem ehmDyadicVaalerPairedResonantAdditiveRow_eq_coefficientMass
    (h : ℤ) (X D J m : ℕ) (hm : m ≠ 0) :
    ehmDyadicVaalerPairedResonantAdditiveRow h X D J m =
      ∑ n ∈ Finset.Icc 2 J,
        if ehmDyadicVaalerPairedCoordinateResonant h m n then
          ((ehmDyadicVaalerPairedProductCoefficient X D m n /
            (n : ℝ) : ℝ) : ℂ)
        else 0 := by
  classical
  unfold ehmDyadicVaalerPairedResonantAdditiveRow
    ehmDyadicVaalerPairedAdditiveTerm
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : ehmDyadicVaalerPairedCoordinateResonant h m n
  · simp only [hn, if_true]
    have hphase : ehmVaalerRationalPhase h n 1 m = 1 := by
      rw [ehmVaalerRationalPhase_eq_one_iff_dvd h n 1 m hm]
      simpa [ehmDyadicVaalerPairedCoordinateResonant] using hn
    rw [hphase, mul_one]
  · simp [hn]

/-! ## Exact reconstruction on an `m`-range -/

noncomputable def ehmDyadicVaalerPairedResonantRowsMRange
    (h : ℤ) (X D J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi,
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmDyadicVaalerPairedResonantAdditiveRow h X D J m)

noncomputable def ehmDyadicVaalerPairedNonresonantRowsMRange
    (h : ℤ) (X D J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi,
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmDyadicVaalerPairedNonresonantAdditiveRow h X D J m)

/-- The Möbius-weighted paired rows split exactly on every common
`m`-interval. -/
theorem ehmDyadicVaalerPairedAdditiveRowsMRange_eq_resonant_add_nonresonant
    (h : ℤ) (X D J mLo mHi : ℕ) :
    ehmDyadicVaalerPairedAdditiveRowsMRange h X D J mLo mHi =
      ehmDyadicVaalerPairedResonantRowsMRange h X D J mLo mHi +
        ehmDyadicVaalerPairedNonresonantRowsMRange
          h X D J mLo mHi := by
  classical
  unfold ehmDyadicVaalerPairedAdditiveRowsMRange
    ehmDyadicVaalerPairedResonantRowsMRange
    ehmDyadicVaalerPairedNonresonantRowsMRange
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [ehmDyadicVaalerPairedAdditiveRow_eq_resonant_add_nonresonant]
  ring

/-! ## Exact reconstruction on a frequency range -/

/-- An arbitrary weighted frequency range of paired rows.  This covers the
Vaaler frequency set without building any property of a particular package
into the finite identity. -/
noncomputable def ehmDyadicVaalerPairedFrequencyRange
    (frequencies : Finset ℤ) (coefficient : ℤ → ℂ)
    (X D J mLo mHi : ℕ) : ℂ :=
  ∑ h ∈ frequencies, coefficient h *
    ehmDyadicVaalerPairedAdditiveRowsMRange h X D J mLo mHi

noncomputable def ehmDyadicVaalerPairedResonantFrequencyRange
    (frequencies : Finset ℤ) (coefficient : ℤ → ℂ)
    (X D J mLo mHi : ℕ) : ℂ :=
  ∑ h ∈ frequencies, coefficient h *
    ehmDyadicVaalerPairedResonantRowsMRange h X D J mLo mHi

noncomputable def ehmDyadicVaalerPairedNonresonantFrequencyRange
    (frequencies : Finset ℤ) (coefficient : ℤ → ℂ)
    (X D J mLo mHi : ℕ) : ℂ :=
  ∑ h ∈ frequencies, coefficient h *
    ehmDyadicVaalerPairedNonresonantRowsMRange h X D J mLo mHi

/-- The resonant split commutes exactly with an arbitrary weighted finite
frequency sum. -/
theorem ehmDyadicVaalerPairedFrequencyRange_eq_resonant_add_nonresonant
    (frequencies : Finset ℤ) (coefficient : ℤ → ℂ)
    (X D J mLo mHi : ℕ) :
    ehmDyadicVaalerPairedFrequencyRange
        frequencies coefficient X D J mLo mHi =
      ehmDyadicVaalerPairedResonantFrequencyRange
          frequencies coefficient X D J mLo mHi +
        ehmDyadicVaalerPairedNonresonantFrequencyRange
          frequencies coefficient X D J mLo mHi := by
  classical
  unfold ehmDyadicVaalerPairedFrequencyRange
    ehmDyadicVaalerPairedResonantFrequencyRange
    ehmDyadicVaalerPairedNonresonantFrequencyRange
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [ehmDyadicVaalerPairedAdditiveRowsMRange_eq_resonant_add_nonresonant]
  ring

/-! ## Paired residue classes and the Ramanujan baseline -/

/-- The complete paired coefficient mass in one residue class.  Unlike the
main-only residue weight, this retains the near complementary-divisor term. -/
noncomputable def ehmDyadicVaalerPairedResidueWeight
    (X D J m r : ℕ) : ℂ :=
  ∑ n ∈ (Finset.Icc 2 J).filter (fun n ↦ n % m = r),
    ((ehmDyadicVaalerPairedProductCoefficient X D m n / (n : ℝ) : ℝ) : ℂ)

/-- The paired row reconstructed from its fixed-denominator residue
classes. -/
noncomputable def ehmDyadicVaalerPairedResidueForm
    (h : ℤ) (X D J m : ℕ) : ℂ :=
  ∑ r ∈ Finset.range m,
    ehmDyadicVaalerPairedResidueWeight X D J m r *
      ehmVaalerRationalPhase h r 1 m

/-- Exact residue partition of the paired main-plus-near row. -/
theorem ehmDyadicVaalerPairedAdditiveRow_eq_residueForm
    (h : ℤ) (X D J m : ℕ) (hm : m ≠ 0) :
    ehmDyadicVaalerPairedAdditiveRow h X D J m =
      ehmDyadicVaalerPairedResidueForm h X D J m := by
  classical
  let s : Finset ℕ := Finset.Icc 2 J
  let t : Finset ℕ := Finset.range m
  let g : ℕ → ℕ := fun n ↦ n % m
  let F : ℕ → ℂ := fun n ↦ ehmDyadicVaalerPairedAdditiveTerm h X D m n
  have hmap : ∀ n ∈ s, g n ∈ t := by
    intro n _
    simp only [g, t, Finset.mem_range]
    exact Nat.mod_lt n (Nat.pos_of_ne_zero hm)
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to (s := s) (t := t) hmap F
  unfold ehmDyadicVaalerPairedAdditiveRow
    ehmDyadicVaalerPairedResidueForm
  change (∑ n ∈ s, F n) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro r _
  unfold ehmDyadicVaalerPairedResidueWeight
  change
    (∑ n ∈ s with g n = r, F n) =
      (∑ n ∈ s with g n = r,
        ((ehmDyadicVaalerPairedProductCoefficient X D m n /
          (n : ℝ) : ℝ) : ℂ)) *
        ehmVaalerRationalPhase h r 1 m
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hnmod : n % m = r := by
    simpa only [g] using (Finset.mem_filter.mp hn).2
  unfold F ehmDyadicVaalerPairedAdditiveTerm
  rw [ehmVaalerRationalPhase_mod h n m hm, hnmod]

/-- The paired residue fluctuation after subtracting a common baseline on
the reduced residue classes. -/
noncomputable def ehmDyadicVaalerPairedCenteredResidueForm
    (h : ℤ) (X D J m : ℕ) (L : ℝ) : ℂ :=
  ∑ r ∈ Finset.range m,
    (ehmDyadicVaalerPairedResidueWeight X D J m r -
      if Nat.Coprime r m then (L : ℂ) else 0) *
        ehmVaalerRationalPhase h r 1 m

/-- Exact centered/Ramanujan decomposition of a paired row.  The baseline
is arbitrary; this theorem does not assert that any analytic correction has
already been identified with a particular choice of `L`. -/
theorem ehmDyadicVaalerPairedResidueForm_eq_centered_add_ramanujan
    (h : ℤ) (X D J m : ℕ) (L : ℝ) :
    ehmDyadicVaalerPairedResidueForm h X D J m =
      ehmDyadicVaalerPairedCenteredResidueForm h X D J m L +
        (L : ℂ) * ehmVaalerReducedResiduePhaseSum h m := by
  classical
  unfold ehmDyadicVaalerPairedResidueForm
    ehmDyadicVaalerPairedCenteredResidueForm
    ehmVaalerReducedResiduePhaseSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> ring

/-- The coordinate resonance split and centered/Ramanujan split are two
exact reconstructions of the same paired row.  Keeping this as one equality
prevents either side from being estimated termwise by this module. -/
theorem ehmDyadicVaalerPairedResonant_add_nonresonant_eq_centered_add_ramanujan
    (h : ℤ) (X D J m : ℕ) (L : ℝ) (hm : m ≠ 0) :
    ehmDyadicVaalerPairedResonantAdditiveRow h X D J m +
        ehmDyadicVaalerPairedNonresonantAdditiveRow h X D J m =
      ehmDyadicVaalerPairedCenteredResidueForm h X D J m L +
        (L : ℂ) * ehmVaalerReducedResiduePhaseSum h m := by
  rw [← ehmDyadicVaalerPairedAdditiveRow_eq_resonant_add_nonresonant,
    ehmDyadicVaalerPairedAdditiveRow_eq_residueForm h X D J m hm,
    ehmDyadicVaalerPairedResidueForm_eq_centered_add_ramanujan]

/-- Exact centered/Ramanujan reconstruction after the Möbius-weighted
`m`-sum. -/
theorem ehmDyadicVaalerPairedAdditiveRowsMRange_eq_centered_add_ramanujan
    (h : ℤ) (X D J mLo mHi : ℕ) (hmLo : 0 < mLo)
    (L : ℕ → ℝ) :
    ehmDyadicVaalerPairedAdditiveRowsMRange h X D J mLo mHi =
      ∑ m ∈ Finset.Icc mLo mHi,
        ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          (ehmDyadicVaalerPairedCenteredResidueForm
              h X D J m (L m) +
            (L m : ℂ) * ehmVaalerReducedResiduePhaseSum h m)) := by
  classical
  unfold ehmDyadicVaalerPairedAdditiveRowsMRange
  apply Finset.sum_congr rfl
  intro m hm
  have hmne : m ≠ 0 := by
    have hmge := (Finset.mem_Icc.mp hm).1
    omega
  rw [ehmDyadicVaalerPairedAdditiveRow_eq_residueForm h X D J m hmne,
    ehmDyadicVaalerPairedResidueForm_eq_centered_add_ramanujan]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedResonance
