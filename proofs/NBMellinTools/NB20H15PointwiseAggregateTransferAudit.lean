/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15ActiveIncidence

/-!
# NB20: audit of the proposed H15 pointwise-aggregate to log-taper transfer

This file contains **no** new H15 object and **no** proxy for the certified
Nyman--Beurling energy.  It only records two exact facts about the objects
already defined in `NB8LogTaperTarget` and `NB12BBLSH15ActiveIncidence`,
together with the consequence they have for any statement of the form

`pointwise H15 aggregate decay  →  NB8.LogTaperL2Decay`.

The H15 pointwise aggregate `h15NormalizedProgressionSmoothPointwiseAggregate`
carries five independent parameters `(N, g, r, U, Q)`: the log-taper cutoff,
the gcd slice, the additive frequency, and the two dyadic block scales.  The
NB8 energy `logTaperL2Error` carries a single stage index `n`.  Any transfer
statement must therefore first *schedule* the four H15 parameters as functions
of the stage index.

The two theorems below show that the schedule cannot be left free:

* the aggregate is identically zero as soon as `N < g * Q`, because the
  supported Bettin--Chandee block is then empty;
* consequently the schedule-free reading of the transfer,
  `H15UnrestrictedPointwiseAggregateTransfer`, is *equivalent* to
  `NB8.LogTaperL2Decay` itself.  It has no arithmetic content: proving it is
  exactly as hard as proving the open NB8 target.

So a genuine transfer theorem has to carry an admissibility hypothesis on the
schedule (at least `g n * Q n ≤ logTaperLength n`) *and* an identity relating
the aggregated H15 blocks to the certified energy.  The missing identity is
described in `TRANSFER_GAP_REPORT.md`.
-/

open Filter

namespace NBMellinTools.NB20

open NBMellinTools.NB8
open NBMellinTools.NB12

/-! ## Degeneracy of the supported dyadic block -/

/-- Above the log-taper cutoff the supported Bettin--Chandee block is empty. -/
theorem h15BettinChandeeSupportedNatBlock_eq_empty_of_cutoff_lt
    {N g Q : ℕ} (h : N < g * Q) :
    h15BettinChandeeSupportedNatBlock N g Q = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨hQx, _, hgx⟩ := mem_h15BettinChandeeSupportedNatBlock.mp hx
  exact absurd ((Nat.mul_le_mul_left g hQx).trans hgx) (not_le.mpr h)

/-- The genuine H15 smooth pointwise aggregate vanishes identically once the
modulus block sits above the log-taper cutoff. -/
theorem h15NormalizedProgressionSmoothPointwiseAggregate_eq_zero_of_cutoff_lt
    {N g r U Q : ℕ} (h : N < g * Q) :
    h15NormalizedProgressionSmoothPointwiseAggregate N g r U Q = 0 := by
  unfold h15NormalizedProgressionSmoothPointwiseAggregate
  rw [h15BettinChandeeSupportedNatBlock_eq_empty_of_cutoff_lt h,
    Finset.sum_empty]

/-- The same degeneracy for the period-frozen pointwise aggregate. -/
theorem h15NormalizedProgressionFrozenPointwiseAggregate_eq_zero_of_cutoff_lt
    {N g r U Q : ℕ} (h : N < g * Q) :
    h15NormalizedProgressionFrozenPointwiseAggregate N g r U Q = 0 := by
  unfold h15NormalizedProgressionFrozenPointwiseAggregate
  rw [h15BettinChandeeSupportedNatBlock_eq_empty_of_cutoff_lt h,
    Finset.sum_empty]

/-! ## The schedule-free transfer statement has no arithmetic content -/

/-- The schedule-free reading of the proposed transfer: for *every* schedule
of the four H15 parameters, decay of the pointwise aggregate would imply the
NB8 log-taper target.  This is an audit object; it is not proposed as the
missing bridge. -/
def H15UnrestrictedPointwiseAggregateTransfer : Prop :=
  ∀ g r U Q : ℕ → ℕ,
    Tendsto (fun n : ℕ =>
        h15NormalizedProgressionSmoothPointwiseAggregate
          (logTaperLength n) (g n) (r n) (U n) (Q n))
      atTop (nhds 0) →
    LogTaperL2Decay

/-- Along any schedule whose modulus block leaves the log-taper cutoff, the
H15 pointwise aggregate is the zero sequence, hence trivially decaying. -/
theorem tendsto_h15SmoothPointwiseAggregate_of_cutoff_lt_schedule
    (g r U Q : ℕ → ℕ) (h : ∀ n, logTaperLength n < g n * Q n) :
    Tendsto (fun n : ℕ =>
        h15NormalizedProgressionSmoothPointwiseAggregate
          (logTaperLength n) (g n) (r n) (U n) (Q n))
      atTop (nhds 0) := by
  have hzero : (fun n : ℕ =>
      h15NormalizedProgressionSmoothPointwiseAggregate
        (logTaperLength n) (g n) (r n) (U n) (Q n)) = fun _ : ℕ => (0 : ℝ) := by
    funext n
    exact h15NormalizedProgressionSmoothPointwiseAggregate_eq_zero_of_cutoff_lt
      (h n)
  rw [hzero]
  exact tendsto_const_nhds

/-- Exact audit result.  The schedule-free transfer proposition is *equivalent*
to the open NB8 target, so it contains no H15 arithmetic input at all: the
degenerate schedule `g = 1`, `Q n = n + 3` already satisfies its hypothesis
vacuously. -/
theorem h15UnrestrictedPointwiseAggregateTransfer_iff_logTaperL2Decay :
    H15UnrestrictedPointwiseAggregateTransfer ↔ LogTaperL2Decay := by
  constructor
  · intro H
    refine H (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun n => n + 3)
      (tendsto_h15SmoothPointwiseAggregate_of_cutoff_lt_schedule _ _ _ _ ?_)
    intro n
    simp [logTaperLength]
  · intro hdecay _ _ _ _ _
    exact hdecay

/-- Consequently the schedule-free transfer statement is itself of
Riemann-hypothesis strength. -/
theorem riemannHypothesis_of_h15UnrestrictedPointwiseAggregateTransfer
    (H : H15UnrestrictedPointwiseAggregateTransfer) :
    RiemannHypothesis :=
  riemannHypothesis_of_logTaperL2Decay
    (h15UnrestrictedPointwiseAggregateTransfer_iff_logTaperL2Decay.mp H)

end NBMellinTools.NB20
