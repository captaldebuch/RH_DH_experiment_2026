/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15CorrectionCoupledAbel

/-!
# NB12zn: smooth variation and the arithmetic-prefix threshold

The correction-coupled Abel identity isolates two genuinely different
inputs.  The smooth envelope is monotone, so its first differences have an
exact telescoping budget.  All arithmetic difficulty is consequently in the
zero-padded signed prefixes and in the terminal/incomplete boundary ledger.

This file proves the smooth statement and packages the precise finite
prefix norm which multiplies it.  It does not assert a new Möbius estimate.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius
open Complex

namespace NBMellinTools.NB12

/-! ## Monotonicity of the smooth envelope -/

/-- The supported log-tapered inverse-square envelope decreases with its
positive natural argument.  The cutoff at `N/g` preserves this monotonicity.
-/
theorem h15SupportedInverseSmoothEnvelope_antitone
    {N g u v : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hu : 0 < u) (huv : u ≤ v) :
    h15SupportedInverseSmoothEnvelope N g v ≤
      h15SupportedInverseSmoothEnvelope N g u := by
  have hv : 0 < v := hu.trans_le huv
  unfold h15SupportedInverseSmoothEnvelope
  split_ifs with hvN huN
  · have hNpos : 0 < (N : ℝ) := by positivity
    have hguPos : 0 < ((g * u : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hg hu
    have hgvPos : 0 < ((g * v : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hg hv
    have hguv : ((g * u : ℕ) : ℝ) ≤ ((g * v : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left g huv
    have hratioPosU : 0 < (N : ℝ) / ((g * u : ℕ) : ℝ) :=
      div_pos hNpos hguPos
    have hratioPosV : 0 < (N : ℝ) / ((g * v : ℕ) : ℝ) :=
      div_pos hNpos hgvPos
    have hratioVU :
        (N : ℝ) / ((g * v : ℕ) : ℝ) ≤
          (N : ℝ) / ((g * u : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_left hNpos.le hguPos hguv
    have hlogVU :
        Real.log ((N : ℝ) / ((g * v : ℕ) : ℝ)) ≤
          Real.log ((N : ℝ) / ((g * u : ℕ) : ℝ)) :=
      Real.log_le_log hratioPosV hratioVU
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hratioOneV :
        (1 : ℝ) ≤ (N : ℝ) / ((g * v : ℕ) : ℝ) :=
      (le_div_iff₀ hgvPos).2 (by
        norm_num
        exact_mod_cast hvN)
    have htaperVNonneg :
        0 ≤ Real.log ((N : ℝ) / ((g * v : ℕ) : ℝ)) /
          Real.log (N : ℝ) :=
      div_nonneg (Real.log_nonneg hratioOneV) hlogN.le
    have htaperVU :
        Real.log ((N : ℝ) / ((g * v : ℕ) : ℝ)) /
            Real.log (N : ℝ) ≤
          Real.log ((N : ℝ) / ((g * u : ℕ) : ℝ)) /
            Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right hlogVU hlogN.le
    have htaperSq :
        (Real.log ((N : ℝ) / ((g * v : ℕ) : ℝ)) /
            Real.log (N : ℝ)) ^ 2 ≤
          (Real.log ((N : ℝ) / ((g * u : ℕ) : ℝ)) /
            Real.log (N : ℝ)) ^ 2 := by
      nlinarith
    have huvSq : (u : ℝ) ^ 2 ≤ (v : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast huv) 2
    calc
      (Real.log ((N : ℝ) / ((g * v : ℕ) : ℝ)) /
            Real.log (N : ℝ)) ^ 2 / (v : ℝ) ^ 2 ≤
          (Real.log ((N : ℝ) / ((g * u : ℕ) : ℝ)) /
            Real.log (N : ℝ)) ^ 2 / (v : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right htaperSq (sq_nonneg _)
      _ ≤ (Real.log ((N : ℝ) / ((g * u : ℕ) : ℝ)) /
            Real.log (N : ℝ)) ^ 2 / (u : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_left (sq_nonneg _)
          (sq_pos_of_pos (by positivity : (0 : ℝ) < (u : ℝ))) huvSq
  · exfalso
    apply huN
    exact (Nat.mul_le_mul_left g huv).trans hvN
  · positivity
  · norm_num

/-! ## Exact first-difference geometry -/

/-- The subtraction of the frozen left endpoint disappears from consecutive
Abel increments. -/
theorem h15NormalizedProgressionEnvelopeIncrement_sub_succ
    (N g k q i : ℕ) :
    h15NormalizedProgressionEnvelopeIncrement N g k q i -
        h15NormalizedProgressionEnvelopeIncrement N g k q (i + 1) =
      h15SupportedInverseSmoothEnvelope N g (k * q + i) -
        h15SupportedInverseSmoothEnvelope N g (k * q + (i + 1)) := by
  unfold h15NormalizedProgressionEnvelopeIncrement
  ring

/-- Every consecutive Abel first difference is nonnegative on a positive
period. -/
theorem h15NormalizedProgressionEnvelopeIncrement_sub_succ_nonneg
    {N g k q i : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hkq : 0 < k * q) :
    0 ≤ h15NormalizedProgressionEnvelopeIncrement N g k q i -
      h15NormalizedProgressionEnvelopeIncrement N g k q (i + 1) := by
  rw [h15NormalizedProgressionEnvelopeIncrement_sub_succ]
  exact sub_nonneg.mpr (h15SupportedInverseSmoothEnvelope_antitone
    hN hg (hkq.trans_le (Nat.le_add_right (k * q) i)) (by omega))

/-- The first differences on one complete ordinary period telescope exactly
to the loss of smooth envelope between its first and last sampled points. -/
theorem sum_h15NormalizedProgressionEnvelope_firstDifferences
    (N g k q : ℕ) :
    (∑ i ∈ Finset.range (q - 1),
      (h15NormalizedProgressionEnvelopeIncrement N g k q i -
        h15NormalizedProgressionEnvelopeIncrement N g k q (i + 1))) =
      h15SupportedInverseSmoothEnvelope N g (k * q) -
        h15SupportedInverseSmoothEnvelope N g (k * q + (q - 1)) := by
  have hs := Finset.sum_range_sub'
    (fun i : ℕ => h15SupportedInverseSmoothEnvelope N g (k * q + i))
    (q - 1)
  simpa only [h15NormalizedProgressionEnvelopeIncrement_sub_succ,
    Nat.add_zero] using hs

/-- On a complete dyadic period, total smooth first-difference mass is at
most the dyadic inverse-square scale. -/
theorem sum_h15NormalizedProgressionEnvelope_firstDifferences_le
    {N g U k q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hq : 0 < q) (hk : k ∈ h15CompletePeriodIndices U q) :
    (∑ i ∈ Finset.range (q - 1),
      (h15NormalizedProgressionEnvelopeIncrement N g k q i -
        h15NormalizedProgressionEnvelopeIncrement N g k q (i + 1))) ≤
      (1 / (U : ℝ)) ^ 2 := by
  rw [sum_h15NormalizedProgressionEnvelope_firstDifferences N g k q]
  have hkBounds := (Finset.mem_filter.mp hk).2
  have hkUpper : k * q + q ≤ 2 * U := by
    simpa only [Nat.add_mul, one_mul] using hkBounds.2
  have hkqMem : k * q ∈ h15BettinChandeeNatBlock U :=
    Finset.mem_Ico.mpr ⟨hkBounds.1, (lt_of_lt_of_le
      (Nat.lt_add_of_pos_right hq) hkUpper)⟩
  have hleft := h15SupportedInverseSmoothEnvelope_le_of_mem_natBlock
    hN hg hU hkqMem
  have hright := h15SupportedInverseSmoothEnvelope_nonneg
    N g (k * q + (q - 1))
  linarith

/-! ## Number of complete ordinary periods -/

/-- Union of the full (not reduced-residue) ordinary periods used by the
completion.  This auxiliary support only records interval geometry. -/
def h15CompleteOrdinaryPeriodSupport (U q : ℕ) : Finset ℕ :=
  (h15CompletePeriodIndices U q).biUnion fun k =>
    Finset.Ico (k * q) ((k + 1) * q)

theorem h15CompleteOrdinaryPeriods_pairwiseDisjoint
    (U q : ℕ) :
    Set.PairwiseDisjoint (h15CompletePeriodIndices U q : Set ℕ)
      (fun k => Finset.Ico (k * q) ((k + 1) * q)) := by
  intro k _hk l _hl hkl
  apply Finset.disjoint_left.mpr
  intro u huk hul
  have hkRange := Finset.mem_Ico.mp huk
  have hlRange := Finset.mem_Ico.mp hul
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hmul : (k + 1) * q ≤ l * q :=
      Nat.mul_le_mul_right q (Nat.succ_le_of_lt hlt)
    omega
  · have hmul : (l + 1) * q ≤ k * q :=
      Nat.mul_le_mul_right q (Nat.succ_le_of_lt hgt)
    omega

theorem h15CompleteOrdinaryPeriodSupport_subset
    (U q : ℕ) :
    h15CompleteOrdinaryPeriodSupport U q ⊆ Finset.Ico U (2 * U) := by
  intro u hu
  rw [h15CompleteOrdinaryPeriodSupport, Finset.mem_biUnion] at hu
  obtain ⟨k, hk, huk⟩ := hu
  have hkBounds := (Finset.mem_filter.mp hk).2
  have huRange := Finset.mem_Ico.mp huk
  exact Finset.mem_Ico.mpr ⟨hkBounds.1.trans huRange.1,
    huRange.2.trans_le hkBounds.2⟩

/-- Complete periods consume disjoint intervals of length `q` inside the
dyadic interval of length `U`. -/
theorem card_h15CompletePeriodIndices_mul_le
    (U q : ℕ) :
    (h15CompletePeriodIndices U q).card * q ≤ U := by
  have hsum := Finset.card_biUnion
    (h15CompleteOrdinaryPeriods_pairwiseDisjoint U q)
  have hcardSupport :
      (h15CompleteOrdinaryPeriodSupport U q).card =
        ∑ k ∈ h15CompletePeriodIndices U q,
          (Finset.Ico (k * q) ((k + 1) * q)).card := by
    simpa [h15CompleteOrdinaryPeriodSupport] using hsum
  have hperiodCard (k : ℕ) :
      (Finset.Ico (k * q) ((k + 1) * q)).card = q := by
    simp only [Nat.card_Ico, Nat.add_mul, one_mul]
    omega
  have hcardSupport' :
      (h15CompleteOrdinaryPeriodSupport U q).card =
        (h15CompletePeriodIndices U q).card * q := by
    rw [hcardSupport]
    simp_rw [hperiodCard]
    simp [Finset.sum_const]
  have hsubset := Finset.card_le_card
    (h15CompleteOrdinaryPeriodSupport_subset U q)
  rw [hcardSupport'] at hsubset
  simp only [Nat.card_Ico] at hsubset
  omega

/-! ## Arithmetic-prefix threshold -/

/-- Uniform signed-prefix input on the exact active H15 incidence.  This is
the quantity the smooth Abel geometry multiplies; it is not assumed to
follow from an absolute character-sum estimate. -/
def H15NormalizedProgressionAbelPrefixBound
    (N g r U Q : ℕ) (P : ℝ) : Prop :=
  0 ≤ P ∧
    ∀ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
      ∀ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        ∀ k ∈ h15CompletePeriodIndices U q,
          ∀ i ∈ Finset.range (q - 1),
            |h15NormalizedProgressionAbelPrefix r k
              (h15SquareDivisorProgressionModulus g d) q d i| ≤ P

/-- A row whose signed arithmetic prefixes are bounded by `P` pays only the
telescoping smooth mass, not the number of points in its periods. -/
theorem abs_h15NormalizedProgressionAbelInteriorRow_le
    {N g r U L q d : ℕ} {P : ℝ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hq : 0 < q)
    (hP : 0 ≤ P)
    (hprefix : ∀ k ∈ h15CompletePeriodIndices U q,
      ∀ i ∈ Finset.range (q - 1),
        |h15NormalizedProgressionAbelPrefix r k L q d i| ≤ P) :
    |h15NormalizedProgressionAbelInteriorRow N g r U L q d| ≤
      ((h15CompletePeriodIndices U q).card : ℝ) *
        (P * (1 / (U : ℝ)) ^ 2) := by
  unfold h15NormalizedProgressionAbelInteriorRow
  calc
    |∑ k ∈ h15CompletePeriodIndices U q,
        ∑ i ∈ Finset.range (q - 1),
          h15NormalizedProgressionAbelPrefix r k L q d i *
            (h15NormalizedProgressionEnvelopeIncrement N g k q i -
              h15NormalizedProgressionEnvelopeIncrement N g k q (i + 1))| ≤
      ∑ k ∈ h15CompletePeriodIndices U q,
        |∑ i ∈ Finset.range (q - 1),
          h15NormalizedProgressionAbelPrefix r k L q d i *
            (h15NormalizedProgressionEnvelopeIncrement N g k q i -
              h15NormalizedProgressionEnvelopeIncrement N g k q (i + 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ h15CompletePeriodIndices U q,
        P * (1 / (U : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkBounds := (Finset.mem_filter.mp hk).2
      have hkqPos : 0 < k * q := hU.trans_le hkBounds.1
      calc
        |∑ i ∈ Finset.range (q - 1),
            h15NormalizedProgressionAbelPrefix r k L q d i *
              (h15NormalizedProgressionEnvelopeIncrement N g k q i -
                h15NormalizedProgressionEnvelopeIncrement N g k q (i + 1))| ≤
          ∑ i ∈ Finset.range (q - 1),
            |h15NormalizedProgressionAbelPrefix r k L q d i *
              (h15NormalizedProgressionEnvelopeIncrement N g k q i -
                h15NormalizedProgressionEnvelopeIncrement N g k q (i + 1))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range (q - 1),
            P * (h15NormalizedProgressionEnvelopeIncrement N g k q i -
              h15NormalizedProgressionEnvelopeIncrement N g k q (i + 1)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hdiff :=
            h15NormalizedProgressionEnvelopeIncrement_sub_succ_nonneg
              hN hg hkqPos (i := i)
          rw [abs_mul, abs_of_nonneg hdiff]
          exact mul_le_mul_of_nonneg_right (hprefix k hk i hi) hdiff
        _ = P * ∑ i ∈ Finset.range (q - 1),
            (h15NormalizedProgressionEnvelopeIncrement N g k q i -
              h15NormalizedProgressionEnvelopeIncrement N g k q (i + 1)) := by
          rw [Finset.mul_sum]
        _ ≤ P * (1 / (U : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (sum_h15NormalizedProgressionEnvelope_firstDifferences_le
              hN hg hU hq hk) hP
    _ = ((h15CompletePeriodIndices U q).card : ℝ) *
        (P * (1 / (U : ℝ)) ^ 2) := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Exact finite geometric budget obtained after inserting a uniform signed
prefix bound into every active Abel row. -/
noncomputable def h15NormalizedProgressionAbelInteriorGeometryBudget
    (N g U Q : ℕ) (P : ℝ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
      (((h15CompletePeriodIndices U q).card : ℝ) *
        (P * (1 / (U : ℝ)) ^ 2))

theorem abs_h15NormalizedProgressionAbelInteriorAggregate_le_geometryBudget
    {N g r U Q : ℕ} {P : ℝ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hQ : 0 < Q)
    (hprefix : H15NormalizedProgressionAbelPrefixBound N g r U Q P) :
    |h15NormalizedProgressionAbelInteriorAggregate N g r U Q| ≤
      h15NormalizedProgressionAbelInteriorGeometryBudget N g U Q P := by
  rcases hprefix with ⟨hP, hprefix⟩
  unfold h15NormalizedProgressionAbelInteriorAggregate
    h15NormalizedProgressionAbelInteriorGeometryBudget
  calc
    |∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          h15NormalizedProgressionAbelInteriorRow N g r U
            (h15SquareDivisorProgressionModulus g d) q d| ≤
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        |∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          h15NormalizedProgressionAbelInteriorRow N g r U
            (h15SquareDivisorProgressionModulus g d) q d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
          (((h15CompletePeriodIndices U q).card : ℝ) *
            (P * (1 / (U : ℝ)) ^ 2)) := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
      have hqPos : 0 < q := hQ.trans_le hqBounds.1
      calc
        |∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
            h15NormalizedProgressionAbelInteriorRow N g r U
              (h15SquareDivisorProgressionModulus g d) q d| ≤
          ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
            |h15NormalizedProgressionAbelInteriorRow N g r U
              (h15SquareDivisorProgressionModulus g d) q d| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
            ((h15CompletePeriodIndices U q).card : ℝ) *
              (P * (1 / (U : ℝ)) ^ 2) := by
          apply Finset.sum_le_sum
          intro d hd
          exact abs_h15NormalizedProgressionAbelInteriorRow_le
            hN hg hU hqPos hP (hprefix q hqMem d hd)
        _ = ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
            (((h15CompletePeriodIndices U q).card : ℝ) *
              (P * (1 / (U : ℝ)) ^ 2)) := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- On one modulus, the active-divisor count and the number of complete
ordinary periods exactly cancel the two powers of the dyadic scale. -/
theorem h15NormalizedProgressionAbelGeometryRow_le
    {g U q : ℕ} {P : ℝ} (hg : 0 < g) (hU : 0 < U)
    (hq : 0 < q) (hP : 0 ≤ P) :
    ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
        (((h15CompletePeriodIndices U q).card : ℝ) *
          (P * (1 / (U : ℝ)) ^ 2)) ≤
      2 * (g.divisors.card : ℝ) * P / (q : ℝ) := by
  have hd := card_h15DyadicActivePeriodSquareDivisorIndices_le
    (q := q) hg hU
  have hd' :
      ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) ≤
        ((2 * U : ℕ) : ℝ) * (g.divisors.card : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd
  have hkNat := card_h15CompletePeriodIndices_mul_le U q
  have hk :
      ((h15CompletePeriodIndices U q).card : ℝ) * (q : ℝ) ≤
        (U : ℝ) := by
    exact_mod_cast hkNat
  have hcombined :
      ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
          ((h15CompletePeriodIndices U q).card : ℝ) * (q : ℝ) ≤
        2 * (U : ℝ) ^ 2 * (g.divisors.card : ℝ) := by
    calc
      ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
          ((h15CompletePeriodIndices U q).card : ℝ) * (q : ℝ) ≤
        ((2 * U : ℕ) : ℝ) * (g.divisors.card : ℝ) *
          ((h15CompletePeriodIndices U q).card : ℝ) * (q : ℝ) := by
            have hKqNonneg :
                0 ≤ ((h15CompletePeriodIndices U q).card : ℝ) *
                  (q : ℝ) := by positivity
            have hmul := mul_le_mul_of_nonneg_right hd' hKqNonneg
            convert hmul using 1 <;> ring
      _ = ((2 * U : ℕ) : ℝ) * (g.divisors.card : ℝ) *
          (((h15CompletePeriodIndices U q).card : ℝ) * (q : ℝ)) := by ring
      _ ≤ ((2 * U : ℕ) : ℝ) * (g.divisors.card : ℝ) * (U : ℝ) := by
        gcongr
      _ = 2 * (U : ℝ) ^ 2 * (g.divisors.card : ℝ) := by
        push_cast
        ring
  have hfactor :
      0 ≤ P / ((U : ℝ) ^ 2 * (q : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcombined hfactor
  calc
    ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
        (((h15CompletePeriodIndices U q).card : ℝ) *
          (P * (1 / (U : ℝ)) ^ 2)) =
      (((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
          ((h15CompletePeriodIndices U q).card : ℝ) * (q : ℝ)) *
        (P / ((U : ℝ) ^ 2 * (q : ℝ))) := by
          field_simp
    _ ≤ (2 * (U : ℝ) ^ 2 * (g.divisors.card : ℝ)) *
        (P / ((U : ℝ) ^ 2 * (q : ℝ))) := hmul
    _ = 2 * (g.divisors.card : ℝ) * P / (q : ℝ) := by
      field_simp

/-- Global exponent audit.  After exact period geometry, a uniform prefix
bound `P` costs only `2 * τ(g) * P`, independently of `U` and `Q`.  Thus for
fixed `g` the Abel interior needs merely `P=o(1)`; no power saving in the
dyadic scale is forced by the smooth sector. -/
theorem h15NormalizedProgressionAbelInteriorGeometryBudget_le
    {N g U Q : ℕ} {P : ℝ} (hg : 0 < g) (hU : 0 < U)
    (hQ : 0 < Q) (hP : 0 ≤ P) :
    h15NormalizedProgressionAbelInteriorGeometryBudget N g U Q P ≤
      2 * (g.divisors.card : ℝ) * P := by
  unfold h15NormalizedProgressionAbelInteriorGeometryBudget
  calc
    (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
      ((h15DyadicActivePeriodSquareDivisorIndices g U q).card : ℝ) *
        (((h15CompletePeriodIndices U q).card : ℝ) *
          (P * (1 / (U : ℝ)) ^ 2))) ≤
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        2 * (g.divisors.card : ℝ) * P / (q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
      exact h15NormalizedProgressionAbelGeometryRow_le hg hU
        (hQ.trans_le hqBounds.1) hP
    _ ≤ ∑ _q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        2 * (g.divisors.card : ℝ) * P / (Q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hqMem
      apply div_le_div_of_nonneg_left (by positivity)
        (by positivity : (0 : ℝ) < (Q : ℝ))
      exact_mod_cast hqBounds.1
    _ = ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
        (2 * (g.divisors.card : ℝ) * P / (Q : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) *
        (2 * (g.divisors.card : ℝ) * P / (Q : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15BettinChandeeSupportedNatBlock_le N g Q
    _ = 2 * (g.divisors.card : ℝ) * P := by
      field_simp

/-- Combined quantitative consequence for the Abel interior. -/
theorem abs_h15NormalizedProgressionAbelInteriorAggregate_le
    {N g r U Q : ℕ} {P : ℝ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hQ : 0 < Q)
    (hprefix : H15NormalizedProgressionAbelPrefixBound N g r U Q P) :
    |h15NormalizedProgressionAbelInteriorAggregate N g r U Q| ≤
      2 * (g.divisors.card : ℝ) * P :=
  (abs_h15NormalizedProgressionAbelInteriorAggregate_le_geometryBudget
      hN hg hU hQ hprefix).trans
    (h15NormalizedProgressionAbelInteriorGeometryBudget_le
      (show 0 < g by omega) hU hQ hprefix.1)

/-- Sufficient complete-residual estimate.  The boundary hypothesis is on
the already coupled terminal-plus-incomplete ledger; its two constituents
are never bounded separately.  This corollary deliberately does not claim
that separate interior and boundary decay is necessary. -/
theorem abs_h15NormalizedProgressionRowToPointwiseResidual_le
    {N g r U Q : ℕ} {P B : ℝ}
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hQ : 0 < Q)
    (hprefix : H15NormalizedProgressionAbelPrefixBound N g r U Q P)
    (hboundary :
      |h15NormalizedProgressionCorrectionCoupledAbelBoundaryAggregate
        N g r U Q| ≤ B) :
    |h15NormalizedProgressionRowToPointwiseResidual N g r U Q| ≤
      2 * (g.divisors.card : ℝ) * P + B := by
  rw [h15NormalizedProgressionRowToPointwiseResidual_eq_abelInterior_add_boundary]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_h15NormalizedProgressionAbelInteriorAggregate_le
      hN hg hU hQ hprefix) hboundary)

end NBMellinTools.NB12
