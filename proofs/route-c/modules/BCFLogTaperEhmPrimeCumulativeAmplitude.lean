import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativePhase

/-!
# Exact amplitude formula for the cumulative prime taper

The cumulative outer taper is the sole real amplitude in the normalized
reciprocal-phase polynomial.  This module identifies its exact active
interval and splits it into first and second inverse-log moments.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeAmplitude

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeTaper

/-- The active outer cutoffs for the coefficient at `(k,m)`. -/
def ehmPrimeCumulativeActiveNBlock (X k m : ℕ) : Finset ℕ :=
  Finset.Icc (max X m) (min (2 * X) k)

/-- First inverse-log moment on the active interval. -/
noncomputable def ehmPrimeCumulativeInvLogMomentOne
    (X k m : ℕ) : ℝ :=
  ∑ N ∈ ehmPrimeCumulativeActiveNBlock X k m,
    1 / Real.log (N : ℝ)

/-- Second inverse-log moment on the active interval. -/
noncomputable def ehmPrimeCumulativeInvLogMomentTwo
    (X k m : ℕ) : ℝ :=
  ∑ N ∈ ehmPrimeCumulativeActiveNBlock X k m,
    1 / (Real.log (N : ℝ)) ^ 2

/-- The two filters in the original definition are one explicit interval. -/
theorem filter_ehmDyadicNBlock_le_and_ge
    (X k m : ℕ) :
    ((ehmDyadicNBlock X).filter (fun N ↦ N ≤ k)).filter
        (fun N ↦ m ≤ N) =
      ehmPrimeCumulativeActiveNBlock X k m := by
  ext N
  simp only [ehmDyadicNBlock, ehmPrimeCumulativeActiveNBlock,
    Finset.mem_filter, Finset.mem_Icc]
  omega

/-- Exact active-interval formula for the cumulative taper. -/
theorem ehmPrimeCumulativeOuterTaper_eq_activeSum
    (X k m : ℕ) :
    ehmPrimeCumulativeOuterTaper X k m =
      ∑ N ∈ ehmPrimeCumulativeActiveNBlock X k m,
        weight N m / Real.log N := by
  classical
  unfold ehmPrimeCumulativeOuterTaper
  rw [← Finset.sum_filter]
  have hfilter := filter_ehmDyadicNBlock_le_and_ge X k m
  rw [hfilter]

/-- For `X ≥ 2`, the amplitude is exactly a first inverse-log moment minus
`log m` times a second inverse-log moment. -/
theorem ehmPrimeCumulativeOuterTaper_eq_logMoments
    (X k m : ℕ) (hX : 2 ≤ X) :
    ehmPrimeCumulativeOuterTaper X k m =
      ehmPrimeCumulativeInvLogMomentOne X k m -
        Real.log (m : ℝ) * ehmPrimeCumulativeInvLogMomentTwo X k m := by
  rw [ehmPrimeCumulativeOuterTaper_eq_activeSum]
  unfold ehmPrimeCumulativeInvLogMomentOne
    ehmPrimeCumulativeInvLogMomentTwo
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro N hN
  have hNge : X ≤ N := (max_le_iff.mp (Finset.mem_Icc.mp hN).1).1
  rw [weight_of_two_le (hX.trans hNge)]
  ring

/-- Before the dyadic block starts, the cumulative amplitude is zero. -/
theorem ehmPrimeCumulativeOuterTaper_eq_zero_of_lt_X
    (X k m : ℕ) (hkX : k < X) :
    ehmPrimeCumulativeOuterTaper X k m = 0 := by
  rw [ehmPrimeCumulativeOuterTaper_eq_activeSum]
  apply Finset.sum_eq_zero
  intro N hN
  have hlow : X ≤ N :=
    (max_le_iff.mp (Finset.mem_Icc.mp hN).1).1
  have hupp : N ≤ k :=
    (Finset.mem_Icc.mp hN).2.trans (min_le_right _ _)
  omega

/-- Past `2X`, the amplitude has stabilized. -/
theorem ehmPrimeCumulativeOuterTaper_stabilizes
    (X k m : ℕ) (hk : 2 * X ≤ k) :
    ehmPrimeCumulativeOuterTaper X k m =
      ehmPrimeCumulativeOuterTaper X (2 * X) m := by
  rw [ehmPrimeCumulativeOuterTaper_eq_activeSum,
    ehmPrimeCumulativeOuterTaper_eq_activeSum]
  unfold ehmPrimeCumulativeActiveNBlock
  rw [min_eq_left hk, min_self]

private theorem sum_filter_le_succ
    {M : Type*} [AddCommMonoid M]
    (S : Finset ℕ) (f : ℕ → M) (k : ℕ) :
    (∑ N ∈ S.filter (fun N ↦ N ≤ k + 1), f N) =
      (∑ N ∈ S.filter (fun N ↦ N ≤ k), f N) +
        if k + 1 ∈ S then f (k + 1) else 0 := by
  classical
  by_cases hkS : k + 1 ∈ S
  · have heq : S.filter (fun N ↦ N ≤ k + 1) =
        insert (k + 1) (S.filter (fun N ↦ N ≤ k)) := by
      ext N
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · intro h
        by_cases hNk : N = k + 1
        · exact Or.inl hNk
        · exact Or.inr ⟨h.1, by omega⟩
      · rintro (hNk | h)
        · subst N
          exact ⟨hkS, le_rfl⟩
        · exact ⟨h.1, h.2.trans (Nat.le_succ k)⟩
    rw [heq, Finset.sum_insert (by simp), if_pos hkS]
    ac_rfl
  · have heq : S.filter (fun N ↦ N ≤ k + 1) =
        S.filter (fun N ↦ N ≤ k) := by
      ext N
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact ⟨h.1, by
          have hne : N ≠ k + 1 := fun hEq ↦ hkS (hEq ▸ h.1)
          omega⟩
      · intro h
        exact ⟨h.1, h.2.trans (Nat.le_succ k)⟩
    rw [heq, if_neg hkS, add_zero]

/-- One-step growth of the cumulative amplitude.  At most one outer cutoff
is added, and its contribution is displayed exactly. -/
theorem ehmPrimeCumulativeOuterTaper_succ_sub
    (X k m : ℕ) :
    ehmPrimeCumulativeOuterTaper X (k + 1) m -
        ehmPrimeCumulativeOuterTaper X k m =
      if k + 1 ∈ ehmDyadicNBlock X ∧ m ≤ k + 1 then
        weight (k + 1) m / Real.log (k + 1)
      else 0 := by
  classical
  unfold ehmPrimeCumulativeOuterTaper
  rw [sum_filter_le_succ]
  by_cases hkS : k + 1 ∈ ehmDyadicNBlock X
  · by_cases hm : m ≤ k + 1
    · simp [hkS, hm]
    · simp [hkS, hm]
  · simp [hkS]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeAmplitude
