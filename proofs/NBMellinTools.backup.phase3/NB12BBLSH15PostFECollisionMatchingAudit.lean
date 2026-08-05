/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEWeightedCollisionSplit

/-!
# NB12zzzaL: collision-matching audit

The weighted collision partition does not by itself identify the collision
ledgers with the geometric mean of the two square sectors.  This file records
the exact mismatch and the exact signed off-diagonal contribution separately.
It then states the sharp sufficient asymptotic inputs without assuming either
one vanishes.

No analytic cancellation estimate is proved here.
-/

open Filter

namespace NBMellinTools.NB12

/-- Failure of the equal/opposite-frequency collision sector to reproduce the
negative Cauchy boundary. -/
noncomputable def h15PostFECollisionMatchingResidual
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  if hQ : 0 < Q then
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    Real.sqrt (h15PostFEEndpointFrequencyEnergy frequencySupport n g U Q) *
        Real.sqrt (h15PostFEWeightedLaurentPairFrequencyEnergy
          frequencySupport n g U Q t) -
      4 * h15PostFEWeightedMissingMissingCollisionLedger
        (h15PostFEActualCommonSuperperiod n g U Q)
        frequencySupport n g U Q t +
      h15PostFEWeightedMissingPairCollisionLedger
        (h15PostFEActualCommonSuperperiod n g U Q)
        frequencySupport n g U Q t
  else 0

/-- The two retained off-diagonal ledgers with their exact H15 signs. -/
noncomputable def h15PostFEWeightedOffDiagonalAlignmentLedger
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) : ℝ :=
  if hQ : 0 < Q then
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    (-4 * h15PostFEWeightedMissingMissingOffDiagonalLedger
        (h15PostFEActualCommonSuperperiod n g U Q)
        frequencySupport n g U Q t +
      h15PostFEWeightedMissingPairOffDiagonalLedger
        (h15PostFEActualCommonSuperperiod n g U Q)
        frequencySupport n g U Q t)
  else 0

/-- Exact collision-matching equation.  Thus zero mismatch is a substantive
identity, not a consequence of the support partition alone. -/
theorem h15PostFECollisionMatchingResidual_eq_zero_iff
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
      ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
    h15PostFECollisionMatchingResidual
        frequencySupport n g U Q t = 0 ↔
      4 * h15PostFEWeightedMissingMissingCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t -
        h15PostFEWeightedMissingPairCollisionLedger
          (h15PostFEActualCommonSuperperiod n g U Q)
          frequencySupport n g U Q t =
        Real.sqrt (h15PostFEEndpointFrequencyEnergy
          frequencySupport n g U Q) *
          Real.sqrt (h15PostFEWeightedLaurentPairFrequencyEnergy
            frequencySupport n g U Q t) := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  simp only [h15PostFECollisionMatchingResidual, dif_pos hQ]
  constructor <;> intro h <;> linarith

/-- Exact audit identity: alignment is collision mismatch plus the signed
off-diagonal ledger. -/
theorem h15PostFEAffineAlignmentResidual_eq_collisionMatching_add_offDiagonal
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15PostFEAffineAlignmentResidual frequencySupport n g U Q t =
      h15PostFECollisionMatchingResidual
          frequencySupport n g U Q t +
        h15PostFEWeightedOffDiagonalAlignmentLedger
          frequencySupport n g U Q t := by
  letI : NeZero (h15PostFEActualCommonSuperperiod n g U Q) :=
    ⟨(h15PostFEActualCommonSuperperiod_pos n g U Q hQ).ne'⟩
  rw [h15PostFEAffineAlignmentResidual_eq_collision_add_offDiagonal
    frequencySupport n g U Q t hQ]
  simp only [h15PostFECollisionMatchingResidual,
    h15PostFEWeightedOffDiagonalAlignmentLedger, dif_pos hQ]
  ring

/-- The full varying-row energy in collision-audit normal form. -/
theorem h15PostFEActualVaryingRowEnergy_eq_normImbalance_add_collisionAudit
    (frequencySupport : Finset ℕ)
    (n g U Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15PostFEActualVaryingRowEnergy frequencySupport n g U Q t =
      h15PostFEAffineNormImbalanceDefect frequencySupport n g U Q t +
        2 *
          (h15PostFECollisionMatchingResidual
              frequencySupport n g U Q t +
            h15PostFEWeightedOffDiagonalAlignmentLedger
              frequencySupport n g U Q t) := by
  rw [h15PostFEActualVaryingRowEnergy_eq_affineDefects,
    h15PostFEAffineAntiparallelDefect_eq_two_mul_alignmentResidual,
    h15PostFEAffineAlignmentResidual_eq_collisionMatching_add_offDiagonal
      frequencySupport n g U Q t hQ]

/-- Collision matching, signed off-diagonal decay, and norm balance are
sufficient for decay of the complete literal energy. -/
theorem tendsto_h15PostFEActualVaryingRowEnergy_zero_of_collisionAudit
    (frequencySupport : ℕ → Finset ℕ)
    (n g U Q : ℕ → ℕ) (t : ℕ → ℝ)
    (hQ : ∀ k, 0 < Q k)
    (hnorm :
      Tendsto
        (fun k => h15PostFEAffineNormImbalanceDefect
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0))
    (hcollision :
      Tendsto
        (fun k => h15PostFECollisionMatchingResidual
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0))
    (hoffDiagonal :
      Tendsto
        (fun k => h15PostFEWeightedOffDiagonalAlignmentLedger
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
        atTop (nhds 0)) :
    Tendsto
      (fun k => h15PostFEActualVaryingRowEnergy
        (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))
      atTop (nhds 0) := by
  have haudit :
      Tendsto
        (fun k => 2 *
          (h15PostFECollisionMatchingResidual
              (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) +
            h15PostFEWeightedOffDiagonalAlignmentLedger
              (frequencySupport k) (n k) (g k) (U k) (Q k) (t k)))
        atTop (nhds 0) := by
    simpa only [zero_add, add_zero, mul_zero] using
      (hcollision.add hoffDiagonal).const_mul 2
  rw [show
      (fun k => h15PostFEActualVaryingRowEnergy
        (frequencySupport k) (n k) (g k) (U k) (Q k) (t k)) =
      (fun k => h15PostFEAffineNormImbalanceDefect
          (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) +
        2 *
          (h15PostFECollisionMatchingResidual
              (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) +
            h15PostFEWeightedOffDiagonalAlignmentLedger
              (frequencySupport k) (n k) (g k) (U k) (Q k) (t k))) by
    funext k
    exact h15PostFEActualVaryingRowEnergy_eq_normImbalance_add_collisionAudit
      (frequencySupport k) (n k) (g k) (U k) (Q k) (t k) (hQ k)]
  simpa only [zero_add] using hnorm.add haudit

end NBMellinTools.NB12
