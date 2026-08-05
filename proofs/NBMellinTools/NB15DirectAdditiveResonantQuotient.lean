/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15DirectAdditiveResonanceSplit

/-!
# NB15: quotient normal form for direct-phase resonances

This module reindexes the exact direct-phase resonance `q ∣ r` by
`r = q*k`.  It is a linear row--frequency identity for the finite H15 middle
window.  It must not be confused with the quadratic collision quotient
`q*q'/p` appearing after a norm-square expansion.

On the reindexed rows both Estermann orientations have phase one.  The
resonant term is consequently reduced to its arithmetic Möbius/log-taper
coefficients and Archimedean factors, with no hidden oscillation in the
primitive numerator.

No estimate or asymptotic decay is asserted.
-/

open scoped BigOperators Topology LSeries.notation
open Complex Filter

namespace NBMellinTools.NB12

/-! ## Exact finite quotient support -/

/-- Quotients `k` for which `r=q*k` lies in the half-open middle-frequency
window `K < r < K+1+J`. -/
def h15DirectAdditiveResonantQuotientSupport
    (q K J : ℕ) : Finset ℕ :=
  (Finset.range (K + 1 + J)).filter fun k =>
    K < q * k ∧ q * k < K + 1 + J

theorem mem_h15DirectAdditiveResonantQuotientSupport
    {q K J k : ℕ} :
    k ∈ h15DirectAdditiveResonantQuotientSupport q K J ↔
      k < K + 1 + J ∧ K < q * k ∧ q * k < K + 1 + J := by
  simp [h15DirectAdditiveResonantQuotientSupport]

/-- Exact reindexing of every finite resonant frequency sum by `r=q*k`. -/
theorem sum_h15DirectAdditive_resonantFrequencies_eq_quotients
    {R : Type*} [AddCommMonoid R]
    (q K J : ℕ) (hq : 0 < q) (f : ℕ → R) :
    (∑ r ∈ (Finset.Ico (K + 1) (K + 1 + J)).filter (fun r => q ∣ r),
      f r) =
      ∑ k ∈ h15DirectAdditiveResonantQuotientSupport q K J,
        f (q * k) := by
  classical
  symm
  apply Finset.sum_bij (fun k _ => q * k)
  · intro k hk
    have hk' := Finset.mem_filter.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨by omega, hk'.2.2⟩, dvd_mul_right q k⟩
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hq hab
  · intro r hr
    have hr' := Finset.mem_filter.mp hr
    have hrange := Finset.mem_Ico.mp hr'.1
    rcases hr'.2 with ⟨k, hk⟩
    subst r
    have hk_le : k ≤ q * k := Nat.le_mul_of_pos_left k hq
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩, rfl⟩
    · exact lt_of_le_of_lt hk_le hrange.2
    · exact ⟨by omega, hrange.2⟩
  · intro k hk
    rfl

/-! ## Complete resonant middle window -/

noncomputable def h15BettinChandeeResonantMiddleQuotientIntegral
    (n K J : ℕ) (T : ℝ) : ℂ :=
  ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
    ∑ k ∈ h15DirectAdditiveResonantQuotientSupport
        (h15BettinChandeeModulusVariable i) K J,
      h15BettinChandeeIntegratedSummand n T
        (i, h15BettinChandeeModulusVariable i * k)

/-- The literal resonant middle-frequency integral is exactly its quotient
normal form. -/
theorem h15BettinChandeeResonantMiddleFrequencyIntegral_eq_quotientIntegral
    (n K J : ℕ) (T : ℝ) :
    h15BettinChandeeResonantMiddleFrequencyIntegral n K J T =
      h15BettinChandeeResonantMiddleQuotientIntegral n K J T := by
  classical
  unfold h15BettinChandeeResonantMiddleFrequencyIntegral
    h15BettinChandeeResonantMiddleSupport
    h15BettinChandeeFiniteBox
    h15BettinChandeeResonantMiddleQuotientIntegral
  rw [Finset.sum_filter]
  calc
    (∑ a ∈ (Finset.univ : Finset
        (H15LaurentRowIndex (NB8.logTaperLength n))).product
          (Finset.Ico (K + 1) (K + 1 + J)),
        if h15DirectAdditiveFrequencyResonant a then
          h15BettinChandeeIntegratedSummand n T a else 0) =
      ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
        ∑ r ∈ Finset.Ico (K + 1) (K + 1 + J),
          if h15DirectAdditiveFrequencyResonant (i, r) then
            h15BettinChandeeIntegratedSummand n T (i, r) else 0 := by
      exact Finset.sum_product
        (Finset.univ : Finset
          (H15LaurentRowIndex (NB8.logTaperLength n)))
        (Finset.Ico (K + 1) (K + 1 + J)) _
    _ = ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
        ∑ r ∈ (Finset.Ico (K + 1) (K + 1 + J)).filter
          (fun r => h15DirectAdditiveFrequencyResonant (i, r)),
          h15BettinChandeeIntegratedSummand n T (i, r) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [h15DirectAdditiveFrequencyResonant] using
        (sum_h15DirectAdditive_resonantFrequencies_eq_quotients
          (h15BettinChandeeModulusVariable i) K J
          (h15BettinChandeeModulusVariable_pos i)
          (fun r => h15BettinChandeeIntegratedSummand n T (i, r)))

/-! ## Phase-free resonant kernel -/

/-- On a valid resonant H15 row the two direct additive phases are both one,
so their paired kernel is exactly `1 + cos(pi*s)`. -/
theorem bblsActiveThreeHalfFrequencyTerm_h15_eq_resonant
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i)
    (damping : ℝ) (r : ℕ) (t : ℝ)
    (hres : h15DirectAdditiveFrequencyResonant (i, r)) :
    bblsActiveThreeHalfFrequencyTerm damping
        (h15LaurentRow i).numerator
        (h15LaurentRow i).denominator
        (h15LaurentRow i).coprime r t =
      let s := bblsEstermannThreeHalfPoint t
      Complex.Gamma (-s) * (damping : ℂ) ^ s *
        bblsEstermannClassicalFactor
          (h15LaurentRow i).denominator s *
        h15DirectAdditiveFrequencyCoefficient r t *
        (1 + Complex.cos ((Real.pi : ℂ) * s)) := by
  rw [bblsActiveThreeHalfFrequencyTerm_h15_eq_direct i hvalid]
  dsimp only
  rw [h15DirectAdditiveReducedUnitPhase_eq_one_of_resonant
      .positive (i, r) hvalid hres,
    h15DirectAdditiveReducedUnitPhase_eq_one_of_resonant
      .negative (i, r) hvalid hres]
  ring

end NBMellinTools.NB12
