/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15SquarefreeDivisorExpansion

/-!
# NB12zh: gcd stratification of the H15 square-divisor rows

The squarefree fluctuation is an exact sum of rows with incidence
`d^2 | g*u`.  This file removes the fixed common factor with `g`.  With

`c = gcd(d^2,g)` and `L = d^2/c`,

the incidence is exactly `L | u`.  Since every H15 numerator in the row is
coprime to `q`, a row vanishes unless `L` is coprime to `q`.  The degenerate
mode `L=1` also vanishes by complete-period additive-character cancellation.

The remaining family is therefore canonically restricted to

`2 <= L`, `Coprime L q`, `L | u`.

All statements here are exact finite arithmetic.  No dispersion bound is
asserted.  The final structure records precisely the signed progression
estimate still required.
-/

open scoped BigOperators Topology LSeries.notation ArithmeticFunction.Moebius
open Complex

namespace NBMellinTools.NB12

/-! ## Normalized progression modulus -/

def h15SquareDivisorCommonFactor (g d : ℕ) : ℕ :=
  Nat.gcd (d ^ 2) g

def h15SquareDivisorProgressionModulus (g d : ℕ) : ℕ :=
  d ^ 2 / h15SquareDivisorCommonFactor g d

theorem h15SquareDivisorCommonFactor_pos
    {g d : ℕ} (hd : 0 < d) :
    0 < h15SquareDivisorCommonFactor g d := by
  unfold h15SquareDivisorCommonFactor
  exact Nat.gcd_pos_of_pos_left g (pow_pos hd 2)

theorem h15SquareDivisorProgressionModulus_pos
    {g d : ℕ} (hd : 0 < d) :
    0 < h15SquareDivisorProgressionModulus g d := by
  unfold h15SquareDivisorProgressionModulus
    h15SquareDivisorCommonFactor
  exact Nat.div_pos (Nat.gcd_le_left g (pow_pos hd 2))
    (h15SquareDivisorCommonFactor_pos (g := g) hd)

/-- Exact normalization of `d^2 | g*u` after removing its gcd with `g`. -/
theorem h15_sq_dvd_mul_iff_progressionModulus_dvd
    {g d u : ℕ} (hd : 0 < d) :
    d ^ 2 ∣ g * u ↔ h15SquareDivisorProgressionModulus g d ∣ u := by
  let a : ℕ := d ^ 2
  let c : ℕ := Nat.gcd a g
  let A : ℕ := a / c
  let G : ℕ := g / c
  have haPos : 0 < a := pow_pos hd 2
  have hcPos : 0 < c := Nat.gcd_pos_of_pos_left g haPos
  have hca : c ∣ a := Nat.gcd_dvd_left a g
  have hcg : c ∣ g := Nat.gcd_dvd_right a g
  have ha : a = c * A := by
    dsimp [A]
    rw [mul_comm, Nat.div_mul_cancel hca]
  have hg : g = c * G := by
    dsimp [G]
    rw [mul_comm, Nat.div_mul_cancel hcg]
  have hcop : Nat.Coprime A G := by
    exact Nat.coprime_div_gcd_div_gcd hcPos
  change a ∣ g * u ↔ A ∣ u
  rw [ha, hg, show c * G * u = c * (G * u) by rw [Nat.mul_assoc],
    Nat.mul_dvd_mul_iff_left hcPos,
    hcop.dvd_mul_left]

theorem h15SquareDivisorCommonFactor_dvd_g
    (g d : ℕ) :
    h15SquareDivisorCommonFactor g d ∣ g :=
  Nat.gcd_dvd_right (d ^ 2) g

theorem h15SquareDivisorCommonFactor_dvd_sq
    (g d : ℕ) :
    h15SquareDivisorCommonFactor g d ∣ d ^ 2 :=
  Nat.gcd_dvd_left (d ^ 2) g

theorem h15SquareDivisorProgressionModulus_le_sq
    (g d : ℕ) :
    h15SquareDivisorProgressionModulus g d ≤ d ^ 2 := by
  unfold h15SquareDivisorProgressionModulus
  exact Nat.div_le_self _ _

/-! ## Exact pruning of inactive normalized rows -/

/-- A divisor in a natural square-divisor support is positive. -/
theorem pos_of_mem_h15SquareDivisorSupport
    {n d : ℕ} (hd : d ∈ h15SquareDivisorSupport n) :
    0 < d := by
  exact Nat.pos_of_mem_divisors hd

/-- If a coefficient is nonzero then its divisor index is positive. -/
theorem pos_of_h15SquareDivisorCoefficient_ne_zero
    {n d : ℕ} (hcoeff : h15SquareDivisorCoefficient n d ≠ 0) :
    0 < d := by
  unfold h15SquareDivisorCoefficient at hcoeff
  split_ifs at hcoeff with hd
  · exact pos_of_mem_h15SquareDivisorSupport hd
  · exact (hcoeff rfl).elim

/-- Every actual incidence in a reduced row forces the normalized progression
modulus to be coprime to the additive modulus. -/
theorem progressionModulus_coprime_of_incidence_of_reduced
    {g d u q : ℕ} (hd : 0 < d) (hinc : d ^ 2 ∣ g * u)
    (huq : Nat.Coprime u q) :
    Nat.Coprime (h15SquareDivisorProgressionModulus g d) q := by
  apply huq.of_dvd_left
  exact (h15_sq_dvd_mul_iff_progressionModulus_dvd hd).mp hinc

/-- A complete-period row vanishes unless its normalized progression modulus
is coprime to `q`. -/
theorem h15PeriodSquareDivisorCrossRow_eq_zero_of_not_coprime_progression
    {g r k q d : ℕ} (hg : 0 < g) (hkq : 0 < k * q)
    (hbad : ¬ Nat.Coprime
      (h15SquareDivisorProgressionModulus g d) q) :
    h15PeriodSquareDivisorCrossRow g r k q d = 0 := by
  unfold h15PeriodSquareDivisorCrossRow
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hcoeff : h15SquareDivisorCoefficient (g * u) d = 0
  · simp [hcoeff]
  · have hdPos := pos_of_h15SquareDivisorCoefficient_ne_zero hcoeff
    have huRange := Finset.mem_Ico.mp (Finset.mem_filter.mp hu).1
    have huPos : 0 < u := hkq.trans_le huRange.1
    have hgu : g * u ≠ 0 := Nat.mul_ne_zero hg.ne' huPos.ne'
    have hinc : d ^ 2 ∣ g * u := by
      by_contra hnot
      have := h15SquareDivisorCoefficient_eq_ite_sq_dvd hgu (d := d)
      rw [if_neg hnot] at this
      exact hcoeff this
    have huq : Nat.Coprime u q := (Finset.mem_filter.mp hu).2
    exact (hbad
      (progressionModulus_coprime_of_incidence_of_reduced
        hdPos hinc huq)).elim

/-- The normalized modulus-one row is the complete unweighted character
mode and therefore vanishes exactly. -/
theorem h15PeriodSquareDivisorCrossRow_eq_zero_of_progressionModulus_one
    {g r k q d : ℕ} (hg : 0 < g) (hkq : 0 < k * q) (hq : 0 < q)
    (hL : h15SquareDivisorProgressionModulus g d = 1) :
    h15PeriodSquareDivisorCrossRow g r k q d = 0 := by
  rw [h15PeriodSquareDivisorCrossRow_eq_incidence hg hkq]
  have hdPos : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    subst d
    simp [h15SquareDivisorProgressionModulus,
      h15SquareDivisorCommonFactor] at hL
  calc
    (∑ u ∈ h15ReducedNaturalPeriod k q,
        if d ^ 2 ∣ g * u then
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            h15PairedDirectCrossMode r u q
        else 0) =
      ∑ u ∈ h15ReducedNaturalPeriod k q,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          h15PairedDirectCrossMode r u q := by
        apply Finset.sum_congr rfl
        intro u _
        have hinc : d ^ 2 ∣ g * u := by
          apply (h15_sq_dvd_mul_iff_progressionModulus_dvd hdPos).mpr
          rw [hL]
          exact one_dvd u
        rw [if_pos hinc]
    _ = ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        ∑ u ∈ h15ReducedNaturalPeriod k q,
          h15PairedDirectCrossMode r u q := by
      rw [Finset.mul_sum]
    _ = 0 := by
      rw [sum_h15ReducedNaturalPeriod_crossMode_eq_zero r k q hq,
        mul_zero]

/-- The same divisor row written directly with its normalized progression
modulus. -/
noncomputable def h15PeriodNormalizedProgressionRow
    (g r k q d : ℕ) : ℝ :=
  ∑ u ∈ h15ReducedNaturalPeriod k q,
    (if h15SquareDivisorProgressionModulus g d ∣ u then
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        h15PairedDirectCrossMode r u q
    else 0)

theorem h15PeriodSquareDivisorCrossRow_eq_normalizedProgression
    {g r k q d : ℕ} (hg : 0 < g) (hkq : 0 < k * q) (hd : 0 < d) :
    h15PeriodSquareDivisorCrossRow g r k q d =
      h15PeriodNormalizedProgressionRow g r k q d := by
  rw [h15PeriodSquareDivisorCrossRow_eq_incidence hg hkq]
  unfold h15PeriodNormalizedProgressionRow
  apply Finset.sum_congr rfl
  intro u _
  simp only [h15_sq_dvd_mul_iff_progressionModulus_dvd hd]

/-- Active divisor indices after both exact pruning rules. -/
def h15ActivePeriodSquareDivisorIndices
    (g k q : ℕ) : Finset ℕ :=
  (h15PeriodSquareDivisorIndices g k q).filter fun d =>
    2 ≤ h15SquareDivisorProgressionModulus g d ∧
      Nat.Coprime (h15SquareDivisorProgressionModulus g d) q

theorem mem_h15ActivePeriodSquareDivisorIndices
    {g k q d : ℕ} :
    d ∈ h15ActivePeriodSquareDivisorIndices g k q ↔
      d ∈ h15PeriodSquareDivisorIndices g k q ∧
      2 ≤ h15SquareDivisorProgressionModulus g d ∧
      Nat.Coprime (h15SquareDivisorProgressionModulus g d) q := by
  simp [h15ActivePeriodSquareDivisorIndices]

theorem card_h15ActivePeriodSquareDivisorIndices_le
    (g k q : ℕ) :
    (h15ActivePeriodSquareDivisorIndices g k q).card ≤
      (h15PeriodSquareDivisorIndices g k q).card := by
  unfold h15ActivePeriodSquareDivisorIndices
  exact Finset.card_filter_le _ _

/-- Square-divisor coefficients have absolute value at most one. -/
theorem abs_h15SquareDivisorCoefficient_le_one
    (n d : ℕ) :
    |h15SquareDivisorCoefficient n d| ≤ 1 := by
  unfold h15SquareDivisorCoefficient
  split_ifs
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  · simp

/-- The elementary row estimate.  It deliberately ignores both the
progression density and additive oscillation, and is recorded to identify
what a genuine dispersion theorem must improve. -/
theorem abs_h15PeriodSquareDivisorCrossRow_le_card
    {g r k q d : ℕ} (hq : 0 < q) :
    |h15PeriodSquareDivisorCrossRow g r k q d| ≤
      ((h15ReducedNaturalPeriod k q).card : ℝ) := by
  unfold h15PeriodSquareDivisorCrossRow
  calc
    |∑ u ∈ h15ReducedNaturalPeriod k q,
        h15SquareDivisorCoefficient (g * u) d *
          h15PairedDirectCrossMode r u q| ≤
      ∑ u ∈ h15ReducedNaturalPeriod k q,
        |h15SquareDivisorCoefficient (g * u) d *
          h15PairedDirectCrossMode r u q| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u ∈ h15ReducedNaturalPeriod k q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro u _
      rw [abs_mul]
      calc
        |h15SquareDivisorCoefficient (g * u) d| *
            |h15PairedDirectCrossMode r u q| ≤ 1 * 1 :=
          mul_le_mul
            (abs_h15SquareDivisorCoefficient_le_one (g * u) d)
            (abs_h15PairedDirectCrossMode_le_one r u q hq)
            (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    _ = ((h15ReducedNaturalPeriod k q).card : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- On a positive complete period, the full signed divisor-row sum is exactly
the sum over active normalized progression moduli. -/
theorem sum_h15PeriodSquareDivisorRows_eq_active
    {g r k q : ℕ} (hg : 0 < g) (hkq : 0 < k * q) (hq : 0 < q) :
    (∑ d ∈ h15PeriodSquareDivisorIndices g k q,
        h15PeriodSquareDivisorCrossRow g r k q d) =
      ∑ d ∈ h15ActivePeriodSquareDivisorIndices g k q,
        h15PeriodSquareDivisorCrossRow g r k q d := by
  unfold h15ActivePeriodSquareDivisorIndices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hdIndex
  by_cases hactive :
      2 ≤ h15SquareDivisorProgressionModulus g d ∧
        Nat.Coprime (h15SquareDivisorProgressionModulus g d) q
  · rw [if_pos hactive]
  · rw [if_neg hactive]
    obtain ⟨u, _, hdu⟩ := Finset.mem_biUnion.mp hdIndex
    have hdPos : 0 < d := pos_of_mem_h15SquareDivisorSupport hdu
    have hLpos := h15SquareDivisorProgressionModulus_pos (g := g) hdPos
    by_cases hLtwo : 2 ≤ h15SquareDivisorProgressionModulus g d
    · have hnotcop :
          ¬ Nat.Coprime (h15SquareDivisorProgressionModulus g d) q :=
        fun hcop => hactive ⟨hLtwo, hcop⟩
      exact h15PeriodSquareDivisorCrossRow_eq_zero_of_not_coprime_progression
        hg hkq hnotcop
    · have hLone : h15SquareDivisorProgressionModulus g d = 1 := by omega
      exact h15PeriodSquareDivisorCrossRow_eq_zero_of_progressionModulus_one
        hg hkq hq hLone

/-- After inactive rows are removed, every surviving row is exactly an
ordinary divisibility progression with modulus at least two and coprime to
`q`. -/
theorem sum_h15PeriodSquareDivisorRows_eq_activeNormalized
    {g r k q : ℕ} (hg : 0 < g) (hkq : 0 < k * q) (hq : 0 < q) :
    (∑ d ∈ h15PeriodSquareDivisorIndices g k q,
        h15PeriodSquareDivisorCrossRow g r k q d) =
      ∑ d ∈ h15ActivePeriodSquareDivisorIndices g k q,
        h15PeriodNormalizedProgressionRow g r k q d := by
  rw [sum_h15PeriodSquareDivisorRows_eq_active hg hkq hq]
  apply Finset.sum_congr rfl
  intro d hdActive
  have hdIndex := (mem_h15ActivePeriodSquareDivisorIndices.mp hdActive).1
  obtain ⟨u, _, hdu⟩ := Finset.mem_biUnion.mp hdIndex
  exact h15PeriodSquareDivisorCrossRow_eq_normalizedProgression
    hg hkq (pos_of_mem_h15SquareDivisorSupport hdu)

/-! ## Gcd strata -/

def h15PeriodSquareDivisorGCDStratum
    (g k q c : ℕ) : Finset ℕ :=
  (h15PeriodSquareDivisorIndices g k q).filter fun d =>
    h15SquareDivisorCommonFactor g d = c

noncomputable def h15PeriodSquareDivisorGCDRow
    (g r k q c : ℕ) : ℝ :=
  ∑ d ∈ h15PeriodSquareDivisorGCDStratum g k q c,
    h15PeriodSquareDivisorCrossRow g r k q d

/-- Exact partition of every divisor-row sum by `gcd(d^2,g)`. -/
theorem sum_h15PeriodSquareDivisorRows_eq_gcdStrata
    {g r k q : ℕ} (hg : 0 < g) :
    (∑ d ∈ h15PeriodSquareDivisorIndices g k q,
        h15PeriodSquareDivisorCrossRow g r k q d) =
      ∑ c ∈ g.divisors,
        h15PeriodSquareDivisorGCDRow g r k q c := by
  unfold h15PeriodSquareDivisorGCDRow
    h15PeriodSquareDivisorGCDStratum
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  let c := h15SquareDivisorCommonFactor g d
  have hc : c ∈ g.divisors := Nat.mem_divisors.mpr
    ⟨h15SquareDivisorCommonFactor_dvd_g g d, hg.ne'⟩
  rw [Finset.sum_eq_single c]
  · simp [c]
  · intro b hb hbc
    simp [c, Ne.symm hbc]
  · intro hcnot
    exact (hcnot hc).elim

/-- Gcd-stratified version of one period's squarefree fluctuation. -/
theorem h15PeriodSquarefreeFluctuationDefect_eq_gcdStrata
    {N g r k q : ℕ} (hg : 0 < g) (hq : 0 < q) :
    h15PeriodSquarefreeFluctuationDefect N g r k q =
      h15SupportedInverseSmoothEnvelope N g (k * q) *
        ∑ c ∈ g.divisors,
          h15PeriodSquareDivisorGCDRow g r k q c := by
  rw [h15PeriodSquarefreeFluctuationDefect_eq_squareDivisorRows
    N g r k q hq,
    sum_h15PeriodSquareDivisorRows_eq_gcdStrata hg]

/-! ## Exact signed progression gate -/

/-- Dyadic aggregate written with the normalized gcd strata. -/
noncomputable def h15GCDStratifiedSquareDivisorAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ k ∈ h15CompletePeriodIndices U q,
      h15SupportedInverseSmoothEnvelope N g (k * q) *
        ∑ c ∈ g.divisors,
          h15PeriodSquareDivisorGCDRow g r k q c

/-- The same global object in its explicit active progression form. -/
noncomputable def h15NormalizedProgressionAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    ∑ k ∈ h15CompletePeriodIndices U q,
      h15SupportedInverseSmoothEnvelope N g (k * q) *
        ∑ d ∈ h15ActivePeriodSquareDivisorIndices g k q,
          h15PeriodNormalizedProgressionRow g r k q d

theorem h15RamanujanSignedSquareDivisorAggregate_eq_gcdStratified
    {N g r U Q : ℕ} (hg : 0 < g) (hQ : 0 < Q) :
    h15RamanujanSignedSquareDivisorAggregate N g r U Q =
      h15GCDStratifiedSquareDivisorAggregate N g r U Q := by
  unfold h15RamanujanSignedSquareDivisorAggregate
    h15DyadicSquareDivisorExpansion
    h15GCDStratifiedSquareDivisorAggregate
  apply Finset.sum_congr rfl
  intro q hq
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hq
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_h15PeriodSquareDivisorRows_eq_gcdStrata hg]

theorem h15RamanujanSignedSquareDivisorAggregate_eq_normalizedProgression
    {N g r U Q : ℕ} (hg : 0 < g) (hU : 0 < U) (hQ : 0 < Q) :
    h15RamanujanSignedSquareDivisorAggregate N g r U Q =
      h15NormalizedProgressionAggregate N g r U Q := by
  unfold h15RamanujanSignedSquareDivisorAggregate
    h15DyadicSquareDivisorExpansion h15NormalizedProgressionAggregate
  apply Finset.sum_congr rfl
  intro q hq
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hq
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  apply Finset.sum_congr rfl
  intro k hk
  have hkBounds := (Finset.mem_filter.mp hk).2
  have hkqPos : 0 < k * q := hU.trans_le hkBounds.1
  rw [sum_h15PeriodSquareDivisorRows_eq_activeNormalized hg hkqPos hqPos]

theorem h15NormalizedProgressionAggregate_eq_gcdStratified
    {N g r U Q : ℕ} (hg : 0 < g) (hU : 0 < U) (hQ : 0 < Q) :
    h15NormalizedProgressionAggregate N g r U Q =
      h15GCDStratifiedSquareDivisorAggregate N g r U Q := by
  rw [← h15RamanujanSignedSquareDivisorAggregate_eq_normalizedProgression
      hg hU hQ,
    h15RamanujanSignedSquareDivisorAggregate_eq_gcdStratified hg hQ]

/-- The normalized aggregate is controlled by the already proved absolute
square-divisor budget.  Hence exact gcd pruning alone does not improve the
balanced exponent. -/
theorem abs_h15GCDStratifiedSquareDivisorAggregate_le_budget
    {N g r U Q : ℕ} (hg : 0 < g) (hQ : 0 < Q) :
    |h15GCDStratifiedSquareDivisorAggregate N g r U Q| ≤
      h15RamanujanSquareDivisorAbsoluteBudget N g r U Q := by
  rw [← h15RamanujanSignedSquareDivisorAggregate_eq_gcdStratified hg hQ]
  exact abs_h15RamanujanSignedSquareDivisorAggregate_le_budget N g r U Q

theorem abs_h15GCDStratifiedSquareDivisorAggregate_balanced_le
    {N g r U : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) :
    |h15GCDStratifiedSquareDivisorAggregate N g r U U| ≤ 1 := by
  calc
    |h15GCDStratifiedSquareDivisorAggregate N g r U U| ≤
        h15RamanujanSquareDivisorAbsoluteBudget N g r U U :=
      abs_h15GCDStratifiedSquareDivisorAggregate_le_budget
        (show 0 < g by omega) hU
    _ ≤ 1 :=
      h15RamanujanSquareDivisorAbsoluteBudget_balanced_le hN hg hU

/-- The normalized signed progression estimate.  This is equivalent, by the
exact reindexing above, to the lower-middle square-divisor power saving. -/
structure H15GCDStratifiedProgressionPowerSaving where
  C : ℝ
  η : ℝ
  C_nonneg : 0 ≤ C
  η_pos : 0 < η
  bound : ∀ {N g r U Q : ℕ},
    2 ≤ N → 1 ≤ g → 0 < U → 0 < Q → Q ≤ U →
    |h15GCDStratifiedSquareDivisorAggregate N g r U Q| ≤
      C / (U : ℝ) ^ η

/-- Exact transfer from the gcd-stratified progression estimate to the
previous square-divisor gate. -/
noncomputable def H15GCDStratifiedProgressionPowerSaving.toSquareDivisor
    (H : H15GCDStratifiedProgressionPowerSaving) :
    H15SignedSquareDivisorPowerSaving where
  C := H.C
  η := H.η
  C_nonneg := H.C_nonneg
  η_pos := H.η_pos
  bound := by
    intro N g r U Q hN hg hU hQ hQU
    rw [h15RamanujanSignedSquareDivisorAggregate_eq_gcdStratified
      (show 0 < g by omega) hQ]
    exact H.bound hN hg hU hQ hQU

/-- Gcd normalization and exact inactive-row pruning do not, by themselves,
alter the already proved absolute exponent.  A negative exponent must enter
through the signed estimate above. -/
noncomputable def h15GCDStratifiedAbsoluteBalancedExponent : ℝ := 0

theorem h15GCDStratifiedAbsoluteBalancedExponent_not_neg :
    ¬ h15GCDStratifiedAbsoluteBalancedExponent < 0 := by
  norm_num [h15GCDStratifiedAbsoluteBalancedExponent]

end NBMellinTools.NB12
