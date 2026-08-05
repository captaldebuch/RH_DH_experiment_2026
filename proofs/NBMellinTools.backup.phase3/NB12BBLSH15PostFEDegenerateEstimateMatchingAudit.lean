/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEDegenerateQuotientFrequency
import NBMellinTools.NB12BBLSH15PostFEJointTransformCompatibilityAudit

/-!
# NB12zzzaX: external-estimate stop test for the degenerate quotient ledger

The coefficient-aware quotient normal form is compared with the two immediate
published-tool models already audited for the complete post-functional-
equation transform.

Quotient reindexing does not change the additive character from a direct
residue phase into the inverse-residue phase required by the immediate
Bettin--Chandee trilinear theorem.  Its fixed-frequency comparison exponent
is still positive (`9/10`), while the elementary direct-additive comparison
has exponent `4`.  Moreover, the quotient support retains `O(Q)` possible
values.

These statements form a precise stop test: the new normal form is exact and
useful, but no direct application of either separated estimate closes its
low-frequency signed dispersion.  A successful continuation needs either an
additional transform (for example Voronoi/Estermann reciprocity) or a new
joint-coefficient, correction-preserving estimate.
-/

namespace NBMellinTools.NB12

def H15PostFEDegenerateEstimateMatchingAudit : Prop :=
  ¬ H15PostFEBettinChandeeLiteralPhaseCompatibility ∧
    h15PostFEBettinChandeePairExponent 0 = 9 / 10 ∧
      h15PostFEDirectAdditivePairExponent 0 = 4 ∧
        ∀ (M n g U Q : ℕ) [NeZero M], 0 < Q →
          (h15PostFEDegenerateQuotientSupport M n g U Q).card ≤ 4 * Q

theorem h15PostFEDegenerateEstimateMatchingAudit :
    H15PostFEDegenerateEstimateMatchingAudit := by
  refine ⟨not_h15PostFEBettinChandeeLiteralPhaseCompatibility,
    h15PostFEBettinChandeePairExponent_zero,
    h15PostFEDirectAdditivePairExponent_zero, ?_⟩
  intro M n g U Q _inst hQ
  exact card_h15PostFEDegenerateQuotientSupport_le M n g U Q hQ

end NBMellinTools.NB12
