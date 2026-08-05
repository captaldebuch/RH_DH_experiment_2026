/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15DirectAdditiveResonantQuotient
import NBMellinTools.NB12BBLSH15FinalBoundaryCompletedCrossModulus

/-!
# NB15: fixed-height resonant quotient aggregate

This module inserts the missing fixed-height layer between the linear
resonant quotient sum and any quadratic collision analysis.  It proves:

* an exact finite quotient-pair support;
* finite sum--interval-integral interchange for the resonant contribution;
* the exact diagonal/ordered-cross-pair expansion of its norm square; and
* an exact partition of the cross-pair term by equality of the physical
  frequencies `q_i*k = q_j*l`.

The last partition is only a ledger identity.  At fixed height there is no
orthogonality theorem that kills the unequal-frequency sector.  In
particular, it is not identified with the older quadratic quotient
`q*q'/p`; that quotient belongs to a later character-average projection.

No estimate or asymptotic decay is asserted.
-/

open scoped BigOperators Topology LSeries.notation ComplexConjugate
open Complex
open MeasureTheory

namespace NBMellinTools.NB12

abbrev H15DirectAdditiveResonantQuotientIndex (n : ℕ) :=
  H15LaurentRowIndex (NB8.logTaperLength n) × ℕ

/-! ## Fixed-height quotient support and aggregate -/

/-- A quotient-indexed version of the finite resonant middle support.  The
second coordinate is the quotient `k`; its physical frequency is `q_i*k`. -/
noncomputable def h15DirectAdditiveResonantQuotientPairSupport
    (n K J : ℕ) :
    Finset (H15DirectAdditiveResonantQuotientIndex n) :=
  ((Finset.univ : Finset (H15LaurentRowIndex (NB8.logTaperLength n))).product
      (Finset.range (K + 1 + J))).filter fun ik =>
    ik.2 ∈ h15DirectAdditiveResonantQuotientSupport
      (h15BettinChandeeModulusVariable ik.1) K J

theorem mem_h15DirectAdditiveResonantQuotientPairSupport
    {n K J : ℕ}
    {ik : H15DirectAdditiveResonantQuotientIndex n} :
    ik ∈ h15DirectAdditiveResonantQuotientPairSupport n K J ↔
      ik.2 < K + 1 + J ∧
        K < h15BettinChandeeModulusVariable ik.1 * ik.2 ∧
        h15BettinChandeeModulusVariable ik.1 * ik.2 < K + 1 + J := by
  simp [h15DirectAdditiveResonantQuotientPairSupport,
    mem_h15DirectAdditiveResonantQuotientSupport]

/-- The physical Estermann frequency represented by a quotient-indexed
row. -/
def h15DirectAdditiveResonantPhysicalFrequency
    {n : ℕ} (ik : H15DirectAdditiveResonantQuotientIndex n) : ℕ :=
  h15BettinChandeeModulusVariable ik.1 * ik.2

/-- The literal H15 resonant quotient sum before integrating in the contour
height. -/
noncomputable def h15BettinChandeeResonantQuotientFixedHeightAggregate
    (n K J : ℕ) (t : ℝ) : ℂ :=
  ∑ ik ∈ h15DirectAdditiveResonantQuotientPairSupport n K J,
    h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
      (h15ContourDamping n)
      (ik.1, h15DirectAdditiveResonantPhysicalFrequency ik) t

theorem h15BettinChandeeResonantQuotientFixedHeightAggregate_eq_nested
    (n K J : ℕ) (t : ℝ) :
    h15BettinChandeeResonantQuotientFixedHeightAggregate n K J t =
      ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
        ∑ k ∈ h15DirectAdditiveResonantQuotientSupport
            (h15BettinChandeeModulusVariable i) K J,
          h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
            (h15ContourDamping n)
            (i, h15BettinChandeeModulusVariable i * k) t := by
  classical
  unfold h15BettinChandeeResonantQuotientFixedHeightAggregate
    h15DirectAdditiveResonantQuotientPairSupport
    h15DirectAdditiveResonantPhysicalFrequency
  rw [Finset.sum_filter]
  calc
    (∑ ik ∈
        (Finset.univ : Finset
          (H15LaurentRowIndex (NB8.logTaperLength n))).product
            (Finset.range (K + 1 + J)),
        if ik.2 ∈ h15DirectAdditiveResonantQuotientSupport
            (h15BettinChandeeModulusVariable ik.1) K J then
          h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
            (h15ContourDamping n)
            (ik.1, h15BettinChandeeModulusVariable ik.1 * ik.2) t
        else 0) =
      ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
        ∑ k ∈ Finset.range (K + 1 + J),
          if k ∈ h15DirectAdditiveResonantQuotientSupport
              (h15BettinChandeeModulusVariable i) K J then
            h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
              (h15ContourDamping n)
              (i, h15BettinChandeeModulusVariable i * k) t
          else 0 := by
        exact Finset.sum_product
          (Finset.univ : Finset
            (H15LaurentRowIndex (NB8.logTaperLength n)))
          (Finset.range (K + 1 + J)) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext k
        simp [h15DirectAdditiveResonantQuotientSupport]
      · intro k _
        rfl

/-! ## Exact finite sum--integral interchange -/

theorem h15BettinChandeeIntegratedSummand_eq_integral_fixedHeight
    (n : ℕ) (T : ℝ)
    (ir : H15LaurentRowIndex (NB8.logTaperLength n) × ℕ) :
    h15BettinChandeeIntegratedSummand n T ir =
      ∫ t : ℝ in -T..T,
        h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
          (h15ContourDamping n) ir t := by
  unfold h15BettinChandeeIntegratedSummand
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  exact h15WeightedFrequencyTerm_eq_directFixedHeightSummand
    (NB8.logTaperLength n) (h15ContourDamping n) ir t

theorem integrable_h15DirectAdditiveFixedHeightSummand
    (n : ℕ)
    (ir : H15LaurentRowIndex (NB8.logTaperLength n) × ℕ) :
    Integrable (fun t : ℝ =>
      h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
        (h15ContourDamping n) ir t) := by
  have h := (integrable_bblsActiveThreeHalfFrequencyTerm
    (h15ContourDamping_pos n)
    (h15LaurentRow ir.1).numerator
    (h15LaurentRow ir.1).denominator
    (h15LaurentRow ir.1).coprime ir.2).const_mul
      (h15LaurentRowWeight ir.1)
  convert h using 1
  funext t
  exact (h15WeightedFrequencyTerm_eq_directFixedHeightSummand
    (NB8.logTaperLength n) (h15ContourDamping n) ir t).symm

/-- The quotient integral introduced in the previous module is exactly the
interval integral of the fixed-height quotient aggregate. -/
theorem h15BettinChandeeResonantMiddleQuotientIntegral_eq_integral_fixedHeight
    (n K J : ℕ) (T : ℝ) :
    h15BettinChandeeResonantMiddleQuotientIntegral n K J T =
      ∫ t : ℝ in -T..T,
        h15BettinChandeeResonantQuotientFixedHeightAggregate n K J t := by
  classical
  have haggregate :
      (fun t : ℝ =>
        h15BettinChandeeResonantQuotientFixedHeightAggregate n K J t) =
        fun t : ℝ =>
          ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
            ∑ k ∈ h15DirectAdditiveResonantQuotientSupport
                (h15BettinChandeeModulusVariable i) K J,
              h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
                (h15ContourDamping n)
                (i, h15BettinChandeeModulusVariable i * k) t := by
    funext t
    exact h15BettinChandeeResonantQuotientFixedHeightAggregate_eq_nested
      n K J t
  rw [haggregate]
  unfold h15BettinChandeeResonantMiddleQuotientIntegral
  simp_rw [h15BettinChandeeIntegratedSummand_eq_integral_fixedHeight]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum]
    intro k _
    exact (integrable_h15DirectAdditiveFixedHeightSummand n
      (i, h15BettinChandeeModulusVariable i * k)).intervalIntegrable
  · intro i _
    have hfun :
        (fun t : ℝ =>
          ∑ k ∈ h15DirectAdditiveResonantQuotientSupport
              (h15BettinChandeeModulusVariable i) K J,
            h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
              (h15ContourDamping n)
              (i, h15BettinChandeeModulusVariable i * k) t) =
          ∑ k ∈ h15DirectAdditiveResonantQuotientSupport
              (h15BettinChandeeModulusVariable i) K J,
            (fun t : ℝ =>
              h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
                (h15ContourDamping n)
                (i, h15BettinChandeeModulusVariable i * k) t) := by
      funext t
      simp
    rw [hfun]
    exact IntervalIntegrable.sum
      (h15DirectAdditiveResonantQuotientSupport
        (h15BettinChandeeModulusVariable i) K J)
      (fun k _ =>
        (integrable_h15DirectAdditiveFixedHeightSummand n
          (i, h15BettinChandeeModulusVariable i * k)).intervalIntegrable)

/-! ## Exact fixed-height quadratic expansion -/

noncomputable def h15BettinChandeeResonantQuotientDiagonal
    (n K J : ℕ) (t : ℝ) : ℝ :=
  ∑ ik ∈ h15DirectAdditiveResonantQuotientPairSupport n K J,
    Complex.normSq
      (h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
        (h15ContourDamping n)
        (ik.1, h15DirectAdditiveResonantPhysicalFrequency ik) t)

noncomputable def h15BettinChandeeResonantQuotientOffDiagonal
    (n K J : ℕ) (t : ℝ) : ℝ :=
  let S := h15DirectAdditiveResonantQuotientPairSupport n K J
  let F := fun ik : H15DirectAdditiveResonantQuotientIndex n =>
    h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
      (h15ContourDamping n)
      (ik.1, h15DirectAdditiveResonantPhysicalFrequency ik) t
  ∑ ik ∈ S, ∑ jl ∈ S.erase ik, (conj (F ik) * F jl).re

theorem normSq_h15BettinChandeeResonantQuotientFixedHeightAggregate_eq
    (n K J : ℕ) (t : ℝ) :
    Complex.normSq
        (h15BettinChandeeResonantQuotientFixedHeightAggregate n K J t) =
      h15BettinChandeeResonantQuotientDiagonal n K J t +
        h15BettinChandeeResonantQuotientOffDiagonal n K J t := by
  unfold h15BettinChandeeResonantQuotientFixedHeightAggregate
    h15BettinChandeeResonantQuotientDiagonal
    h15BettinChandeeResonantQuotientOffDiagonal
  exact normSq_sum_eq_sum_normSq_add_orderedOffDiagonal
    (h15DirectAdditiveResonantQuotientPairSupport n K J)
    (fun ik => h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
      (h15ContourDamping n)
      (ik.1, h15DirectAdditiveResonantPhysicalFrequency ik) t)

/-! ## The actual quotient-pair frequency collision -/

def h15DirectAdditiveResonantQuotientFrequencyCollides
    {n : ℕ}
    (p : H15DirectAdditiveResonantQuotientIndex n ×
      H15DirectAdditiveResonantQuotientIndex n) : Prop :=
  h15DirectAdditiveResonantPhysicalFrequency p.1 =
    h15DirectAdditiveResonantPhysicalFrequency p.2

noncomputable instance h15DirectAdditiveResonantQuotientFrequencyCollides_decidable
    {n : ℕ}
    (p : H15DirectAdditiveResonantQuotientIndex n ×
      H15DirectAdditiveResonantQuotientIndex n) :
    Decidable (h15DirectAdditiveResonantQuotientFrequencyCollides p) :=
  Classical.dec _

/-- Canonical parametrization of the positive solutions to `q*k=q'*l`.
After removing `gcd(q,q')`, each quotient is a multiple of the opposite
reduced modulus, with one common multiplier. -/
theorem mul_eq_mul_iff_exists_reduced_commonMultiplier
    {q q' k l : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    q * k = q' * l ↔
      ∃ h : ℕ,
        k = (q' / q.gcd q') * h ∧
        l = (q / q.gcd q') * h := by
  let d := q.gcd q'
  let a := q / d
  let b := q' / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left q' hq
  have hqeq : q = d * a := by
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left q q')).symm
  have hq'eq : q' = d * b := by
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right q q')).symm
  have hcop : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hd
  have hb : 0 < b := by
    exact Nat.div_pos (Nat.le_of_dvd hq' (Nat.gcd_dvd_right q q')) hd
  change q * k = q' * l ↔ ∃ h : ℕ, k = b * h ∧ l = a * h
  constructor
  · intro heq
    have hred : a * k = b * l := by
      apply Nat.eq_of_mul_eq_mul_left hd
      simpa only [hqeq, hq'eq, mul_assoc] using heq
    have hbdiv : b ∣ k := by
      apply (hcop.symm.dvd_mul_left).mp
      rw [hred]
      exact dvd_mul_right b l
    rcases hbdiv with ⟨h, rfl⟩
    refine ⟨h, rfl, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hb
    calc
      b * l = a * (b * h) := hred.symm
      _ = b * (a * h) := by ring
  · rintro ⟨h, rfl, rfl⟩
    rw [hqeq, hq'eq]
    ring

/-- Therefore the collision equation arising from the fixed-height
resonant square has an exact gcd-reduced common-multiplier form. -/
theorem h15DirectAdditiveResonantQuotientFrequencyCollides_iff
    {n : ℕ}
    (p : H15DirectAdditiveResonantQuotientIndex n ×
      H15DirectAdditiveResonantQuotientIndex n) :
    h15DirectAdditiveResonantQuotientFrequencyCollides p ↔
      ∃ h : ℕ,
        p.1.2 =
            (h15BettinChandeeModulusVariable p.2.1 /
              (h15BettinChandeeModulusVariable p.1.1).gcd
                (h15BettinChandeeModulusVariable p.2.1)) * h ∧
          p.2.2 =
            (h15BettinChandeeModulusVariable p.1.1 /
              (h15BettinChandeeModulusVariable p.1.1).gcd
                (h15BettinChandeeModulusVariable p.2.1)) * h := by
  unfold h15DirectAdditiveResonantQuotientFrequencyCollides
    h15DirectAdditiveResonantPhysicalFrequency
  exact mul_eq_mul_iff_exists_reduced_commonMultiplier
    (h15BettinChandeeModulusVariable_pos p.1.1)
    (h15BettinChandeeModulusVariable_pos p.2.1)

noncomputable def h15BettinChandeeResonantQuotientCollisionOffDiagonal
    (n K J : ℕ) (t : ℝ) : ℝ :=
  let S := h15DirectAdditiveResonantQuotientPairSupport n K J
  let F := fun ik : H15DirectAdditiveResonantQuotientIndex n =>
    h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
      (h15ContourDamping n)
      (ik.1, h15DirectAdditiveResonantPhysicalFrequency ik) t
  ∑ ik ∈ S,
    ∑ jl ∈ (S.erase ik).filter fun jl =>
        h15DirectAdditiveResonantQuotientFrequencyCollides (ik, jl),
      (conj (F ik) * F jl).re

noncomputable def h15BettinChandeeResonantQuotientNoncollisionOffDiagonal
    (n K J : ℕ) (t : ℝ) : ℝ :=
  let S := h15DirectAdditiveResonantQuotientPairSupport n K J
  let F := fun ik : H15DirectAdditiveResonantQuotientIndex n =>
    h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
      (h15ContourDamping n)
      (ik.1, h15DirectAdditiveResonantPhysicalFrequency ik) t
  ∑ ik ∈ S,
    ∑ jl ∈ (S.erase ik).filter fun jl =>
        ¬ h15DirectAdditiveResonantQuotientFrequencyCollides (ik, jl),
      (conj (F ik) * F jl).re

theorem h15BettinChandeeResonantQuotientOffDiagonal_eq_collision_add_noncollision
    (n K J : ℕ) (t : ℝ) :
    h15BettinChandeeResonantQuotientOffDiagonal n K J t =
      h15BettinChandeeResonantQuotientCollisionOffDiagonal n K J t +
        h15BettinChandeeResonantQuotientNoncollisionOffDiagonal n K J t := by
  classical
  dsimp [h15BettinChandeeResonantQuotientOffDiagonal,
    h15BettinChandeeResonantQuotientCollisionOffDiagonal,
    h15BettinChandeeResonantQuotientNoncollisionOffDiagonal]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ik _
  exact (Finset.sum_filter_add_sum_filter_not
    ((h15DirectAdditiveResonantQuotientPairSupport n K J).erase ik)
    (fun jl => h15DirectAdditiveResonantQuotientFrequencyCollides (ik, jl))
    (fun jl =>
      (conj
        (h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
          (h15ContourDamping n)
          (ik.1, h15DirectAdditiveResonantPhysicalFrequency ik) t) *
        h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
          (h15ContourDamping n)
          (jl.1, h15DirectAdditiveResonantPhysicalFrequency jl) t).re)).symm

/-- Complete fixed-height ledger.  Unequal-frequency cross pairs are retained;
removing them would require an additional averaging/orthogonality theorem. -/
theorem normSq_h15BettinChandeeResonantQuotientFixedHeightAggregate_eq_threeSectors
    (n K J : ℕ) (t : ℝ) :
    Complex.normSq
        (h15BettinChandeeResonantQuotientFixedHeightAggregate n K J t) =
      h15BettinChandeeResonantQuotientDiagonal n K J t +
        h15BettinChandeeResonantQuotientCollisionOffDiagonal n K J t +
        h15BettinChandeeResonantQuotientNoncollisionOffDiagonal n K J t := by
  rw [normSq_h15BettinChandeeResonantQuotientFixedHeightAggregate_eq,
    h15BettinChandeeResonantQuotientOffDiagonal_eq_collision_add_noncollision]
  ring

end NBMellinTools.NB12
