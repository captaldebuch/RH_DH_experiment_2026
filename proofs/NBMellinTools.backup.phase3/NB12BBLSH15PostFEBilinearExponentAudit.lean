/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFECommonAdditivePhase
import NBMellinTools.NB12BBLSH15FinalBoundaryShellBlockLiteratureAudit

/-!
# NB12zzzl: correction-preserving bilinear exponent audit

The common-character normalization replaces every ordered phase pair by one
additive character modulo `q*q'`.  This file records what that normalization
does, and does not, preserve quantitatively.

* Both moduli remain in the dyadic block `[Q,2Q)`, so their product lies in
  `[Q^2,4Q^2)`.
* The two inverse coordinates have become reduced residues `u < q` and
  `v < q'`.  Their original dyadic `U` scale is therefore carried by the
  collected coefficient, not by the phase variables.
* Collection cannot increase the total `L¹` mass, but it does not produce a
  separated coefficient in `(u,q)` and `(v,q')`.
* The formal Bettin--Chandee exponent would pass above frequency exponent
  `3/4`, but its inverse-residue phase is not the H15 direct phase.  Applying
  the elementary direct-additive estimate independently to the two factors
  passes only above frequency exponent `2`.

Thus the common-denominator algebra does not create a new published-theorem
application.  The correction-coupled fixed/low-frequency sector remains the
analytic gate.  No external estimate, asymptotic decay, or RH conclusion is
asserted here.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Literal support after residue-pair collection -/

/-- Every residue key retains the dyadic modulus support of its source row. -/
theorem h15PostFEResidueSupport_modulus_mem
    {n g U Q : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ h15PostFEResidueSupport n g U Q) :
    z.2 ∈ h15BettinChandeeSupportedNatBlock
      (NB8.logTaperLength n) g Q := by
  classical
  rw [h15PostFEResidueSupport, Finset.mem_image] at hz
  rcases hz with ⟨k, hk, rfl⟩
  simpa [h15PostFEResidueKey] using
    h15PostFECollectedUnionKey_modulus_mem hk

/-- Exact residue and modulus ranges of both coordinates of an ordered
post-functional-equation pair. -/
theorem h15PostFEOrderedPairResidueSupport_ranges
    {n g U Q : ℕ} {κ : (ℕ × ℕ) × (ℕ × ℕ)}
    (hQ : 0 < Q)
    (hκ : κ ∈ h15PostFEOrderedPairResidueSupport n g U Q) :
    κ.1.1 < κ.1.2 ∧
      Q ≤ κ.1.2 ∧ κ.1.2 < 2 * Q ∧
        g * κ.1.2 ≤ NB8.logTaperLength n ∧
      κ.2.1 < κ.2.2 ∧
        Q ≤ κ.2.2 ∧ κ.2.2 < 2 * Q ∧
          g * κ.2.2 ≤ NB8.logTaperLength n := by
  have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hκ
  have hleftMod := mem_h15BettinChandeeSupportedNatBlock.mp
    (h15PostFEResidueSupport_modulus_mem hactual.1)
  have hrightMod := mem_h15BettinChandeeSupportedNatBlock.mp
    (h15PostFEResidueSupport_modulus_mem hactual.2)
  exact ⟨h15PostFEResidueKey_fst_lt_snd hQ hactual.1,
    hleftMod.1, hleftMod.2.1, hleftMod.2.2,
    h15PostFEResidueKey_fst_lt_snd hQ hactual.2,
    hrightMod.1, hrightMod.2.1, hrightMod.2.2⟩

/-- The common character modulus is genuinely a square-scale dyadic
quantity. -/
theorem h15PostFEOrderedPair_commonModulus_ranges
    {n g U Q : ℕ} {κ : (ℕ × ℕ) × (ℕ × ℕ)}
    (hQ : 0 < Q)
    (hκ : κ ∈ h15PostFEOrderedPairResidueSupport n g U Q) :
    Q ^ 2 ≤ κ.1.2 * κ.2.2 ∧
      κ.1.2 * κ.2.2 < 4 * Q ^ 2 := by
  have h := h15PostFEOrderedPairResidueSupport_ranges hQ hκ
  constructor <;> nlinarith

/-- A dyadically localized Estermann frequency retains its usual
half-open range independently of the residue-pair collection. -/
theorem h15PostFECommonAdditiveFrequency_ranges
    {R r : ℕ} (hr : r ∈ h15BettinChandeeNatBlock R) :
    R ≤ r ∧ r < 2 * R := by
  simpa [h15BettinChandeeNatBlock] using hr

/-! ## Coefficient mass retained by collection -/

/-- The norm of a raw ordered-pair scalar is the product of the two row
scalar norms. -/
theorem norm_h15PostFEOrderedPairScalar
    (n r : ℕ) (t : ℝ)
    (p : H15PostFEOrderedLaurentPairIndex (NB8.logTaperLength n)) :
    ‖h15PostFEOrderedPairScalar n r t p‖ =
      ‖h15DirectAdditiveTotalRowScalar (NB8.logTaperLength n)
          (h15ContourDamping n) p.1 r t‖ *
        ‖h15DirectAdditiveTotalRowScalar (NB8.logTaperLength n)
          (h15ContourDamping n) p.2 r t‖ := by
  simp [h15PostFEOrderedPairScalar]

/-- Residue-pair collection does not increase total `L¹` coefficient mass.
This is the unconditional norm statement available without a signed
bilinear estimate. -/
theorem sum_norm_h15PostFEOrderedPairCollectedScalar_le_raw
    (n g U Q r : ℕ) (t : ℝ) :
    (∑ κ ∈ h15PostFEOrderedPairResidueSupport n g U Q,
        ‖h15PostFEOrderedPairCollectedScalar n g U Q r t κ‖) ≤
      ∑ p ∈ h15PostFEOrderedLaurentPairIndices n g U Q,
        ‖h15PostFEOrderedPairScalar n r t p‖ := by
  classical
  unfold h15PostFEOrderedPairResidueSupport
    h15PostFEOrderedPairCollectedScalar
  calc
    (∑ κ ∈
        (h15PostFEOrderedLaurentPairIndices n g U Q).image
          h15PostFEOrderedPairResidueKey,
        ‖∑ p ∈ (h15PostFEOrderedLaurentPairIndices n g U Q).filter
            (fun p => h15PostFEOrderedPairResidueKey p = κ),
          h15PostFEOrderedPairScalar n r t p‖) ≤
      ∑ κ ∈
        (h15PostFEOrderedLaurentPairIndices n g U Q).image
          h15PostFEOrderedPairResidueKey,
        ∑ p ∈ (h15PostFEOrderedLaurentPairIndices n g U Q).filter
            (fun p => h15PostFEOrderedPairResidueKey p = κ),
          ‖h15PostFEOrderedPairScalar n r t p‖ := by
      apply Finset.sum_le_sum
      intro κ _hκ
      exact norm_sum_le _ _
    _ = ∑ p ∈ h15PostFEOrderedLaurentPairIndices n g U Q,
        ‖h15PostFEOrderedPairScalar n r t p‖ := by
      have hcollect := sum_mul_kernel_eq_sum_image_collected
        (h15PostFEOrderedLaurentPairIndices n g U Q)
        h15PostFEOrderedPairResidueKey
        (fun p => ‖h15PostFEOrderedPairScalar n r t p‖)
        (fun _κ : (ℕ × ℕ) × (ℕ × ℕ) => (1 : ℝ))
      simpa using hcollect.symm

/-! ## Candidate exponents and the quantitative stop test -/

/-- Formal exponent obtained by applying the hypothetical inverse-phase
Bettin--Chandee scale independently to the two factors.  This exponent is
recorded only for comparison: the phase hypothesis fails for H15. -/
noncomputable def h15PostFEBettinChandeePairExponent
    (kappa : ℝ) : ℝ :=
  2 * h15BettinChandeeWorstCompleteExponent kappa

theorem h15PostFEBettinChandeePairExponent_neg_iff (kappa : ℝ) :
    h15PostFEBettinChandeePairExponent kappa < 0 ↔
      3 / 4 < kappa := by
  unfold h15PostFEBettinChandeePairExponent
  constructor
  · intro h
    apply (h15BettinChandeeWorstCompleteExponent_neg_iff kappa).mp
    linarith
  · intro h
    have hneg :=
      (h15BettinChandeeWorstCompleteExponent_neg_iff kappa).mpr h
    linarith

theorem h15PostFEBettinChandeePairExponent_zero :
    h15PostFEBettinChandeePairExponent 0 = 9 / 10 := by
  rw [h15PostFEBettinChandeePairExponent]
  norm_num [h15BettinChandeeWorstCompleteExponent,
    h15BettinChandeeFirstCompleteExponent,
    h15BettinChandeeSecondCompleteExponent,
    h15BettinChandeePhaseLossExponent,
    h15BettinChandeeFirstScaledExponent,
    h15BettinChandeeSecondScaledExponent, max_eq_left]

/-- Exponent produced by treating the two direct-additive factors
independently.  Unlike the preceding comparison, this has the correct phase,
but it discards the correction-preserving signed coupling. -/
noncomputable def h15PostFEDirectAdditivePairExponent
    (kappa : ℝ) : ℝ :=
  2 * h15DirectAdditiveBalancedExponent kappa

theorem h15PostFEDirectAdditivePairExponent_neg_iff (kappa : ℝ) :
    h15PostFEDirectAdditivePairExponent kappa < 0 ↔ 2 < kappa := by
  unfold h15PostFEDirectAdditivePairExponent
  constructor
  · intro h
    apply (h15DirectAdditiveBalancedExponent_neg_iff kappa).mp
    linarith
  · intro h
    have hneg := (h15DirectAdditiveBalancedExponent_neg_iff kappa).mpr h
    linarith

theorem h15PostFEDirectAdditivePairExponent_zero :
    h15PostFEDirectAdditivePairExponent 0 = 4 := by
  norm_num [h15PostFEDirectAdditivePairExponent,
    h15DirectAdditiveBalancedExponent]

@[simp] theorem h15PostFEDirectAdditivePairExponent_two :
    h15PostFEDirectAdditivePairExponent 2 = 0 := by
  simp [h15PostFEDirectAdditivePairExponent]

/-- Compact formal record of the exponent audit.  The fixed-frequency
candidate exponents are nonnegative, while the literal H15 phase is direct.
This theorem is a stop test for the two audited published-tool applications,
not an impossibility result for other bilinear transforms. -/
def H15PostFECommonAdditiveExponentStopTest : Prop :=
  H15PostFunctionalEquationPhaseIsDirect ∧
    h15PostFEBettinChandeePairExponent 0 = 9 / 10 ∧
      h15PostFEDirectAdditivePairExponent 0 = 4 ∧
        h15PostFEDirectAdditivePairExponent 2 = 0

theorem h15PostFECommonAdditiveExponentStopTest :
    H15PostFECommonAdditiveExponentStopTest := by
  exact ⟨h15PostFunctionalEquationPhaseIsDirect,
    h15PostFEBettinChandeePairExponent_zero,
    h15PostFEDirectAdditivePairExponent_zero,
    h15PostFEDirectAdditivePairExponent_two⟩

end NBMellinTools.NB12
