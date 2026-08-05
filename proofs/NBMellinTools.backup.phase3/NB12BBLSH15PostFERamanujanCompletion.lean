/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEUnionMismatch

/-!
# NB12zzzg: Ramanujan completion of the post-FE mismatch ledger

The union-supported coefficient mismatch is collected once more, now by the
post-functional-equation residue key `(u mod q,q)`.  The direct cross mode is
periodic in `u`, so this is an exact finite reindexing.

An arbitrary modulus-dependent reference coefficient first splits the mismatch
into a reference-centered variation and an incomplete residue-class trace.  A
canonical fiber average is then defined and proved to give genuinely mean-zero
coefficients on every active modulus.  The final theorem keeps its trace next
to the ordered cross-row dispersion.  No absolute value or asymptotic estimate
is used.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-- Every arithmetic key in the post-FE union has modulus in the prescribed
dyadic modulus block. -/
theorem h15PostFECollectedUnionKey_modulus_mem
    {n g U Q : ℕ} {k : ℕ × ℕ}
    (hk : k ∈ h15PostFECollectedUnionKeySupport n g U Q) :
    k.2 ∈ h15BettinChandeeSupportedNatBlock
      (NB8.logTaperLength n) g Q := by
  classical
  rw [h15PostFECollectedUnionKeySupport, Finset.mem_union] at hk
  rcases hk with hk | hk
  · rw [h15EndpointCollectedKeySupport, Finset.mem_image] at hk
    rcases hk with ⟨p, hp, rfl⟩
    exact (Finset.mem_sigma.mp (Finset.mem_sigma.mp hp).1).1
  · rw [h15LaurentCollectedKeySupport, Finset.mem_image] at hk
    rcases hk with ⟨i, hi, rfl⟩
    exact (mem_h15DoublyLocalizedLaurentRowIndices.mp
      (mem_h15DoublyLocalizedOrientationZeroIndices.mp hi).1).2.2

/-- Every union key has positive modulus when the modulus scale is positive. -/
theorem h15PostFECollectedUnionKey_modulus_pos
    {n g U Q : ℕ} {k : ℕ × ℕ} (hQ : 0 < Q)
    (hk : k ∈ h15PostFECollectedUnionKeySupport n g U Q) :
    0 < k.2 := by
  exact hQ.trans_le
    (mem_h15BettinChandeeSupportedNatBlock.mp
      (h15PostFECollectedUnionKey_modulus_mem hk)).1

/-- Reduction of the inverse coordinate modulo the modulus does not change
the paired direct cross mode. -/
theorem h15PairedDirectCrossMode_mod
    (r u q : ℕ) (hq : 0 < q) :
    h15PairedDirectCrossMode r (u % q) q =
      h15PairedDirectCrossMode r u q := by
  have hperiod := h15PairedDirectCrossMode_add_period
    r (u % q) (u / q) q hq
  rw [Nat.div_add_mod'] at hperiod
  exact hperiod.symm

/-- Residue-class key of a post-FE arithmetic key. -/
def h15PostFEResidueKey (k : ℕ × ℕ) : ℕ × ℕ :=
  (k.1 % k.2, k.2)

/-- Finite residue-class support of the post-FE mismatch. -/
def h15PostFEResidueSupport
    (n g U Q : ℕ) : Finset (ℕ × ℕ) :=
  (h15PostFECollectedUnionKeySupport n g U Q).image h15PostFEResidueKey

/-- Mismatch coefficients collected over all inverse coordinates in the same
residue class modulo the same modulus. -/
noncomputable def h15PostFEResidueMismatchCoefficient
    (n g U Q r : ℕ) (t : ℝ) (z : ℕ × ℕ) : ℝ :=
  ∑ k ∈ (h15PostFECollectedUnionKeySupport n g U Q).filter
      (fun k => h15PostFEResidueKey k = z),
    h15PostFECollectedMismatchCoefficient n g U Q r t k

/-- Exact residue-class collection of the union-supported mismatch sum. -/
theorem h15PostFEUnionMismatch_eq_residueCollected
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q) :
    (∑ k ∈ h15PostFECollectedUnionKeySupport n g U Q,
        h15PostFECollectedMismatchCoefficient n g U Q r t k *
          h15PairedDirectCrossMode r k.1 k.2) =
      ∑ z ∈ h15PostFEResidueSupport n g U Q,
        h15PostFEResidueMismatchCoefficient n g U Q r t z *
          h15PairedDirectCrossMode r z.1 z.2 := by
  classical
  calc
    (∑ k ∈ h15PostFECollectedUnionKeySupport n g U Q,
        h15PostFECollectedMismatchCoefficient n g U Q r t k *
          h15PairedDirectCrossMode r k.1 k.2) =
      ∑ k ∈ h15PostFECollectedUnionKeySupport n g U Q,
        h15PostFECollectedMismatchCoefficient n g U Q r t k *
          h15PairedDirectCrossMode r (h15PostFEResidueKey k).1
            (h15PostFEResidueKey k).2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [h15PostFEResidueKey,
        h15PairedDirectCrossMode_mod r k.1 k.2
          (h15PostFECollectedUnionKey_modulus_pos hQ hk)]
    _ = _ := sum_mul_kernel_eq_sum_image_collected
      (h15PostFECollectedUnionKeySupport n g U Q)
      h15PostFEResidueKey
      (h15PostFECollectedMismatchCoefficient n g U Q r t)
      (fun z => h15PairedDirectCrossMode r z.1 z.2)

/-- Moduli occurring in the residue-collected mismatch. -/
def h15PostFEResidueModulusSupport
    (n g U Q : ℕ) : Finset ℕ :=
  (h15PostFEResidueSupport n g U Q).image Prod.snd

/-- Residue keys occurring above one fixed modulus. -/
def h15PostFEResidueFiber
    (n g U Q q : ℕ) : Finset (ℕ × ℕ) :=
  (h15PostFEResidueSupport n g U Q).filter fun z => z.2 = q

/-- Natural residue representatives occurring above one fixed modulus. -/
def h15PostFEResidueFiberResidues
    (n g U Q q : ℕ) : Finset ℕ :=
  (h15PostFEResidueFiber n g U Q q).image Prod.fst

/-- Residue representatives missing from the post-FE union fiber. -/
def h15PostFEMissingResidues
    (n g U Q q : ℕ) : Finset ℕ :=
  Finset.range q \ h15PostFEResidueFiberResidues n g U Q q

/-- Every residue key is represented by a natural number below its positive
modulus. -/
theorem h15PostFEResidueKey_fst_lt_snd
    {n g U Q : ℕ} {z : ℕ × ℕ} (hQ : 0 < Q)
    (hz : z ∈ h15PostFEResidueSupport n g U Q) :
    z.1 < z.2 := by
  classical
  rw [h15PostFEResidueSupport, Finset.mem_image] at hz
  rcases hz with ⟨k, hk, rfl⟩
  exact Nat.mod_lt _ (h15PostFECollectedUnionKey_modulus_pos hQ hk)

/-- The actual fiber residues form a subset of the complete natural residue
system. -/
theorem h15PostFEResidueFiberResidues_subset_range
    {n g U Q q : ℕ} (hQ : 0 < Q) :
    h15PostFEResidueFiberResidues n g U Q q ⊆ Finset.range q := by
  classical
  intro a ha
  rw [h15PostFEResidueFiberResidues, Finset.mem_image] at ha
  rcases ha with ⟨z, hz, rfl⟩
  have hz' := Finset.mem_filter.mp hz
  rw [Finset.mem_range, ← hz'.2]
  exact h15PostFEResidueKey_fst_lt_snd hQ hz'.1

/-- The cross mode has zero mean on the complete natural residue system;
non-coprime representatives contribute zero automatically. -/
theorem sum_range_h15PairedDirectCrossMode_eq_zero
    (r q : ℕ) (hq : 0 < q) :
    (∑ u ∈ Finset.range q, h15PairedDirectCrossMode r u q) = 0 := by
  have hred := sum_h15ReducedResidues_crossMode_eq_zero r q hq
  unfold h15ReducedResidues at hred
  rw [Finset.sum_filter] at hred
  calc
    (∑ u ∈ Finset.range q, h15PairedDirectCrossMode r u q) =
        ∑ u ∈ Finset.range q,
          if Nat.Coprime u q then h15PairedDirectCrossMode r u q else 0 := by
      apply Finset.sum_congr rfl
      intro u _hu
      by_cases hcop : Nat.Coprime u q
      · simp [hcop]
      · simp [hcop]
    _ = 0 := hred

/-- Pair-indexed and natural-residue-indexed versions of one fiber trace are
identical. -/
theorem sum_h15PostFEResidueFiber_crossMode_eq_residueSum
    (n g U Q r q : ℕ) :
    (∑ z ∈ h15PostFEResidueFiber n g U Q q,
        h15PairedDirectCrossMode r z.1 z.2) =
      ∑ a ∈ h15PostFEResidueFiberResidues n g U Q q,
        h15PairedDirectCrossMode r a q := by
  classical
  let S := h15PostFEResidueFiber n g U Q q
  have hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have hxq := (Finset.mem_filter.mp hx).2
    have hyq := (Finset.mem_filter.mp hy).2
    apply Prod.ext hxy
    exact hxq.trans hyq.symm
  symm
  calc
    (∑ a ∈ h15PostFEResidueFiberResidues n g U Q q,
        h15PairedDirectCrossMode r a q) =
      ∑ z ∈ S, h15PairedDirectCrossMode r z.1 q := by
        exact Finset.sum_image hinj
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2]

/-- The incomplete fiber trace is exactly the negative trace of the missing
residue representatives.  Thus the complete cross-mode residue mean
contributes no term of its own. -/
theorem sum_h15PostFEResidueFiber_crossMode_eq_neg_missing
    (n g U Q r q : ℕ) (hQ : 0 < Q) (hq : 0 < q) :
    (∑ z ∈ h15PostFEResidueFiber n g U Q q,
        h15PairedDirectCrossMode r z.1 z.2) =
      -(∑ a ∈ h15PostFEMissingResidues n g U Q q,
          h15PairedDirectCrossMode r a q) := by
  rw [sum_h15PostFEResidueFiber_crossMode_eq_residueSum]
  have hsplit := Finset.sum_sdiff
    (h15PostFEResidueFiberResidues_subset_range
      (n := n) (g := g) (U := U) (Q := Q) (q := q) hQ)
    (f := fun a => h15PairedDirectCrossMode r a q)
  unfold h15PostFEMissingResidues at hsplit
  rw [sum_range_h15PairedDirectCrossMode_eq_zero r q hq] at hsplit
  unfold h15PostFEMissingResidues
  linarith

/-- Coefficient variation after subtracting an arbitrary reference depending
only on the modulus. -/
noncomputable def h15PostFEResidueVariationAggregate
    (n g U Q r : ℕ) (t : ℝ) (reference : ℕ → ℝ) : ℝ :=
  ∑ z ∈ h15PostFEResidueSupport n g U Q,
    (h15PostFEResidueMismatchCoefficient n g U Q r t z - reference z.2) *
      h15PairedDirectCrossMode r z.1 z.2

/-- The incomplete residue-class trace retained after coefficient centering. -/
noncomputable def h15PostFEResidueConstantTrace
    (n g U Q r : ℕ) (reference : ℕ → ℝ) : ℝ :=
  ∑ q ∈ h15PostFEResidueModulusSupport n g U Q,
    reference q *
      ∑ z ∈ h15PostFEResidueFiber n g U Q q,
        h15PairedDirectCrossMode r z.1 z.2

/-- Canonical reference coefficient: the arithmetic mean of the collected
mismatch coefficients on one residue fiber.  It is defined as zero on an
empty fiber by the field convention `0 / 0 = 0`. -/
noncomputable def h15PostFEResidueFiberMeanCoefficient
    (n g U Q r : ℕ) (t : ℝ) (q : ℕ) : ℝ :=
  (∑ z ∈ h15PostFEResidueFiber n g U Q q,
      h15PostFEResidueMismatchCoefficient n g U Q r t z) /
    (h15PostFEResidueFiber n g U Q q).card

/-- A modulus in the residue-modulus support has a nonempty residue fiber. -/
theorem h15PostFEResidueFiber_nonempty_of_mem_modulusSupport
    {n g U Q q : ℕ}
    (hq : q ∈ h15PostFEResidueModulusSupport n g U Q) :
    (h15PostFEResidueFiber n g U Q q).Nonempty := by
  classical
  rw [h15PostFEResidueModulusSupport, Finset.mem_image] at hq
  rcases hq with ⟨z, hz, hzq⟩
  refine ⟨z, Finset.mem_filter.mpr ⟨hz, ?_⟩⟩
  exact hzq

/-- Subtracting the canonical fiber mean gives coefficients with exact zero
unweighted sum on every active modulus. -/
theorem sum_h15PostFEResidueMismatchCoefficient_sub_fiberMean_eq_zero
    {n g U Q r q : ℕ} {t : ℝ}
    (hq : q ∈ h15PostFEResidueModulusSupport n g U Q) :
    (∑ z ∈ h15PostFEResidueFiber n g U Q q,
        (h15PostFEResidueMismatchCoefficient n g U Q r t z -
          h15PostFEResidueFiberMeanCoefficient n g U Q r t q)) = 0 := by
  classical
  let S := h15PostFEResidueFiber n g U Q q
  have hcardPos : 0 < S.card :=
    Finset.card_pos.mpr
      (h15PostFEResidueFiber_nonempty_of_mem_modulusSupport hq)
  have hcardNe : (S.card : ℝ) ≠ 0 := by positivity
  unfold h15PostFEResidueFiberMeanCoefficient
  change (∑ z ∈ S,
    (h15PostFEResidueMismatchCoefficient n g U Q r t z -
      (∑ z ∈ S, h15PostFEResidueMismatchCoefficient n g U Q r t z) /
        S.card)) = 0
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul]
  field_simp [hcardNe]
  ring

/-- The canonical mean-centered coefficient variation. -/
noncomputable def h15PostFEResidueMeanZeroVariation
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  h15PostFEResidueVariationAggregate n g U Q r t
    (h15PostFEResidueFiberMeanCoefficient n g U Q r t)

/-- The constant trace associated with the canonical fiber averages. -/
noncomputable def h15PostFEResidueMeanTrace
    (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  h15PostFEResidueConstantTrace n g U Q r
    (h15PostFEResidueFiberMeanCoefficient n g U Q r t)

/-- Generic finite key-centering identity. -/
theorem sum_weighted_eq_variation_add_keyTrace
    {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (key : ι → κ) (weight kernel : ι → ℝ)
    (reference : κ → ℝ) :
    (∑ i ∈ S, weight i * kernel i) =
      (∑ i ∈ S, (weight i - reference (key i)) * kernel i) +
        ∑ k ∈ S.image key,
          reference k * ∑ i ∈ S.filter (fun i => key i = k), kernel i := by
  classical
  calc
    (∑ i ∈ S, weight i * kernel i) =
        (∑ i ∈ S, (weight i - reference (key i)) * kernel i) +
          ∑ i ∈ S, kernel i * reference (key i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = _ := by
      rw [sum_mul_kernel_eq_sum_image_collected S key kernel reference]
      apply congrArg (fun x : ℝ =>
        (∑ i ∈ S, (weight i - reference (key i)) * kernel i) + x)
      apply Finset.sum_congr rfl
      intro k _hk
      ring

/-- Exact reference split of the residue-collected H15 mismatch. -/
theorem h15PostFEResidueCollected_eq_variation_add_constantTrace
    (n g U Q r : ℕ) (t : ℝ) (reference : ℕ → ℝ) :
    (∑ z ∈ h15PostFEResidueSupport n g U Q,
        h15PostFEResidueMismatchCoefficient n g U Q r t z *
          h15PairedDirectCrossMode r z.1 z.2) =
      h15PostFEResidueVariationAggregate n g U Q r t reference +
        h15PostFEResidueConstantTrace n g U Q r reference := by
  exact sum_weighted_eq_variation_add_keyTrace
    (h15PostFEResidueSupport n g U Q) Prod.snd
    (h15PostFEResidueMismatchCoefficient n g U Q r t)
    (fun z => h15PairedDirectCrossMode r z.1 z.2) reference

/-- The retained constant trace is precisely the negative missing-residue
trace.  This is the exact boundary mode that remains available to cancel the
ordered cross-row dispersion. -/
theorem h15PostFEResidueConstantTrace_eq_neg_missing
    (n g U Q r : ℕ) (reference : ℕ → ℝ) (hQ : 0 < Q) :
    h15PostFEResidueConstantTrace n g U Q r reference =
      -(∑ q ∈ h15PostFEResidueModulusSupport n g U Q,
          reference q *
            ∑ a ∈ h15PostFEMissingResidues n g U Q q,
              h15PairedDirectCrossMode r a q) := by
  classical
  unfold h15PostFEResidueConstantTrace
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hqImage := Finset.mem_image.mp hq
  rcases hqImage with ⟨z, hz, rfl⟩
  have hqPos : 0 < z.2 := by
    rw [h15PostFEResidueSupport, Finset.mem_image] at hz
    rcases hz with ⟨k, hk, rfl⟩
    simpa [h15PostFEResidueKey] using
      (h15PostFECollectedUnionKey_modulus_pos
        (n := n) (g := g) (U := U) (Q := Q) hQ hk)
  rw [sum_h15PostFEResidueFiber_crossMode_eq_neg_missing
    n g U Q r z.2 hQ hqPos]
  ring

/-- The canonical mean trace is the corresponding mean-weighted negative
missing-residue trace. -/
theorem h15PostFEResidueMeanTrace_eq_neg_missing
    (n g U Q r : ℕ) (t : ℝ) (hQ : 0 < Q) :
    h15PostFEResidueMeanTrace n g U Q r t =
      -(∑ q ∈ h15PostFEResidueModulusSupport n g U Q,
          h15PostFEResidueFiberMeanCoefficient n g U Q r t q *
            ∑ a ∈ h15PostFEMissingResidues n g U Q q,
              h15PairedDirectCrossMode r a q) := by
  exact h15PostFEResidueConstantTrace_eq_neg_missing n g U Q r
    (h15PostFEResidueFiberMeanCoefficient n g U Q r t) hQ

/-- Canonical residue-completed form of the centered post-FE lift defect.
The incomplete constant trace remains coupled to the signed ordered
dispersion; neither is bounded separately. -/
theorem h15PostFECenteredLiftDefect_eq_residueVariation_add_trace_sub_dispersion
    (n g U Q r : ℕ) (t : ℝ) (reference : ℕ → ℝ)
    (hQ : 0 < Q) (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PostFECenteredLiftDefect n g U Q r t =
      h15PostFEResidueVariationAggregate n g U Q r t reference +
        h15PostFEResidueConstantTrace n g U Q r reference -
          4 * h15OrientationZeroFrequencyOffDiagonal n g U Q r t /
            (2 * h15PairedHyperbolicCoefficient t) := by
  rw [h15PostFECenteredLiftDefect_eq_union_mismatch_sub_dispersion
      n g U Q r t hQ hS,
    h15PostFEUnionMismatch_eq_residueCollected n g U Q r t hQ,
    h15PostFEResidueCollected_eq_variation_add_constantTrace]

/-- Canonical mean-zero form of the centered post-FE lift defect. -/
theorem h15PostFECenteredLiftDefect_eq_meanZeroVariation_add_trace_sub_dispersion
    (n g U Q r : ℕ) (t : ℝ)
    (hQ : 0 < Q) (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PostFECenteredLiftDefect n g U Q r t =
      h15PostFEResidueMeanZeroVariation n g U Q r t +
        h15PostFEResidueMeanTrace n g U Q r t -
          4 * h15OrientationZeroFrequencyOffDiagonal n g U Q r t /
            (2 * h15PairedHyperbolicCoefficient t) := by
  exact h15PostFECenteredLiftDefect_eq_residueVariation_add_trace_sub_dispersion
    n g U Q r t (h15PostFEResidueFiberMeanCoefficient n g U Q r t) hQ hS

/-- Fully expanded canonical frontier: fiber-mean-zero variation, the
mean-weighted missing-residue boundary, and ordered cross-row dispersion. -/
theorem h15PostFECenteredLiftDefect_eq_meanZero_sub_missing_sub_dispersion
    (n g U Q r : ℕ) (t : ℝ)
    (hQ : 0 < Q) (hS : h15PairedHyperbolicCoefficient t ≠ 0) :
    h15PostFECenteredLiftDefect n g U Q r t =
      h15PostFEResidueMeanZeroVariation n g U Q r t -
        (∑ q ∈ h15PostFEResidueModulusSupport n g U Q,
          h15PostFEResidueFiberMeanCoefficient n g U Q r t q *
            ∑ a ∈ h15PostFEMissingResidues n g U Q q,
              h15PairedDirectCrossMode r a q) -
        4 * h15OrientationZeroFrequencyOffDiagonal n g U Q r t /
          (2 * h15PairedHyperbolicCoefficient t) := by
  rw [h15PostFECenteredLiftDefect_eq_meanZeroVariation_add_trace_sub_dispersion
      n g U Q r t hQ hS,
    h15PostFEResidueMeanTrace_eq_neg_missing n g U Q r t hQ]
  ring

end NBMellinTools.NB12
