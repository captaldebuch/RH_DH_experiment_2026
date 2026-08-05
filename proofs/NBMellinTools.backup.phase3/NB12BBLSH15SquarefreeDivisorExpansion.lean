/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15RamanujanVariationAudit
import Mathlib.Data.Nat.Factorization.Root

/-!
# NB12zg: square-divisor expansion of the H15 Ramanujan fluctuation

The balanced absolute-completion audit isolated the squarefree factor
`mu (g*u) ^ 2` as the discontinuous part of the H15 coefficient.  This file
opens that factor by the exact finite identity

`1_squarefree(n) = sum_{d^2 | n} mu(d)`.

Mathlib's `Nat.floorRoot` makes the identity particularly clean: the integers
whose square divides `n` are precisely the divisors of `floorRoot 2 n`.
Möbius inversion then evaluates their signed sum.

On a complete modulus period the frozen reference indicator multiplies a
zero additive-character mode.  The remaining squarefree fluctuation is
therefore reindexed exactly as a signed square-divisor/incidence sum.  This
does not itself supply decay; it identifies the arithmetic cancellation that
must be retained in the next estimate.
-/

open scoped BigOperators Topology LSeries.notation ArithmeticFunction.Moebius
open Complex

namespace NBMellinTools.NB12

/-! ## The square-divisor Möbius identity -/

/-- Finite support of the positive square divisors of `n`, represented by
the divisors of its second flooring root. -/
def h15SquareDivisorSupport (n : ℕ) : Finset ℕ :=
  (Nat.floorRoot 2 n).divisors

/-- Membership in the flooring-root support is exactly square divisibility.
The nonzero hypothesis excludes the deliberately exceptional value of
`Nat.divisors 0`. -/
theorem mem_h15SquareDivisorSupport_iff
    {n d : ℕ} (hn : n ≠ 0) :
    d ∈ h15SquareDivisorSupport n ↔ d ^ 2 ∣ n := by
  unfold h15SquareDivisorSupport
  rw [Nat.mem_divisors]
  have hroot : Nat.floorRoot 2 n ≠ 0 :=
    Nat.floorRoot_ne_zero.mpr ⟨by norm_num, hn⟩
  rw [and_iff_left hroot]
  exact Nat.pow_dvd_iff_dvd_floorRoot.symm

/-- A positive natural number is squarefree exactly when its second flooring
root is one. -/
theorem squarefree_iff_floorRoot_two_eq_one
    {n : ℕ} :
    Squarefree n ↔ Nat.floorRoot 2 n = 1 := by
  constructor
  · intro hsquarefree
    have hunit : IsUnit (Nat.floorRoot 2 n) := by
      apply hsquarefree
      simpa [pow_two] using Nat.floorRoot_pow_dvd (n := 2) (a := n)
    exact Nat.isUnit_iff.mp hunit
  · intro hroot d hd
    apply isUnit_iff_dvd_one.mpr
    rw [← hroot]
    apply Nat.pow_dvd_iff_dvd_floorRoot.mp
    simpa [pow_two] using hd

/-- Integer form of the classical squarefree-indicator identity. -/
theorem sum_moebius_h15SquareDivisorSupport
    (n : ℕ) :
    (∑ d ∈ h15SquareDivisorSupport n,
        ArithmeticFunction.moebius d) =
      if Squarefree n then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [h15SquareDivisorSupport, ArithmeticFunction.moebius]
  · have hroot : Nat.floorRoot 2 n ≠ 0 :=
      Nat.floorRoot_ne_zero.mpr ⟨by norm_num, hn⟩
    calc
      (∑ d ∈ h15SquareDivisorSupport n,
          ArithmeticFunction.moebius d) =
          (ArithmeticFunction.moebius *
            (ArithmeticFunction.zeta : ArithmeticFunction ℤ))
              (Nat.floorRoot 2 n) := by
            rw [ArithmeticFunction.coe_mul_zeta_apply]
            rfl
      _ = (1 : ArithmeticFunction ℤ) (Nat.floorRoot 2 n) := by
            rw [ArithmeticFunction.moebius_mul_coe_zeta]
      _ = if Nat.floorRoot 2 n = 1 then 1 else 0 := by
            rw [ArithmeticFunction.one_apply]
      _ = if Squarefree n then 1 else 0 := by
            simp only [squarefree_iff_floorRoot_two_eq_one]

/-- Real-valued form used by the H15 coefficient ledger. -/
theorem h15SquarefreeIndicator_eq_sum_squareDivisors
    (n : ℕ) :
    h15SquarefreeIndicator n =
      ∑ d ∈ h15SquareDivisorSupport n,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
  unfold h15SquarefreeIndicator
  rw [← Int.cast_sum, sum_moebius_h15SquareDivisorSupport]
  split_ifs <;> norm_num

/-! ## A common square-divisor index and exact period reindexing -/

/-- A square-divisor Möbius coefficient, extended by zero away from its
finite natural support. -/
noncomputable def h15SquareDivisorCoefficient (n d : ℕ) : ℝ :=
  if d ∈ h15SquareDivisorSupport n then
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)
  else 0

/-- The coefficient is the expected square-divisibility incidence whenever
the integer being tested is nonzero. -/
theorem h15SquareDivisorCoefficient_eq_ite_sq_dvd
    {n d : ℕ} (hn : n ≠ 0) :
    h15SquareDivisorCoefficient n d =
      if d ^ 2 ∣ n then
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)
      else 0 := by
  unfold h15SquareDivisorCoefficient
  simp only [mem_h15SquareDivisorSupport_iff hn]

/-- All square divisors occurring anywhere on one complete natural period. -/
def h15PeriodSquareDivisorIndices (g k q : ℕ) : Finset ℕ :=
  (h15ReducedNaturalPeriod k q).biUnion fun u =>
    h15SquareDivisorSupport (g * u)

theorem h15SquareDivisorSupport_subset_periodIndices
    {g k q u : ℕ} (hu : u ∈ h15ReducedNaturalPeriod k q) :
    h15SquareDivisorSupport (g * u) ⊆
      h15PeriodSquareDivisorIndices g k q := by
  intro d hd
  exact Finset.mem_biUnion.mpr ⟨u, hu, hd⟩

/-- The indicator expansion can be extended to the common period index:
coefficients outside the local square-divisor support are exactly zero. -/
theorem h15SquarefreeIndicator_eq_sum_periodSquareDivisorCoefficients
    {g k q u : ℕ} (hu : u ∈ h15ReducedNaturalPeriod k q) :
    h15SquarefreeIndicator (g * u) =
      ∑ d ∈ h15PeriodSquareDivisorIndices g k q,
        h15SquareDivisorCoefficient (g * u) d := by
  calc
    h15SquarefreeIndicator (g * u) =
        ∑ d ∈ h15SquareDivisorSupport (g * u),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) :=
      h15SquarefreeIndicator_eq_sum_squareDivisors (g * u)
    _ = ∑ d ∈ h15SquareDivisorSupport (g * u),
        h15SquareDivisorCoefficient (g * u) d := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [h15SquareDivisorCoefficient, hd]
    _ = ∑ d ∈ h15PeriodSquareDivisorIndices g k q,
        h15SquareDivisorCoefficient (g * u) d := by
      apply Finset.sum_subset
        (h15SquareDivisorSupport_subset_periodIndices hu)
      intro d _ hnot
      simp [h15SquareDivisorCoefficient, hnot]

/-- The signed additive-character row attached to one square divisor.  Its
incidence condition is `d^2 | g*u`; the smooth envelope remains outside the
row because it was frozen at the period endpoint in the exact variation
decomposition. -/
noncomputable def h15PeriodSquareDivisorCrossRow
    (g r k q d : ℕ) : ℝ :=
  ∑ u ∈ h15ReducedNaturalPeriod k q,
    h15SquareDivisorCoefficient (g * u) d *
      h15PairedDirectCrossMode r u q

/-- On a positive complete period the row displays its divisor-congruence
condition explicitly. -/
theorem h15PeriodSquareDivisorCrossRow_eq_incidence
    {g r k q d : ℕ} (hg : 0 < g) (hkq : 0 < k * q) :
    h15PeriodSquareDivisorCrossRow g r k q d =
      ∑ u ∈ h15ReducedNaturalPeriod k q,
        (if d ^ 2 ∣ g * u then
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            h15PairedDirectCrossMode r u q
        else 0) := by
  unfold h15PeriodSquareDivisorCrossRow
  apply Finset.sum_congr rfl
  intro u hu
  have huRange := Finset.mem_Ico.mp (Finset.mem_filter.mp hu).1
  have huPos : 0 < u := hkq.trans_le huRange.1
  have hgu : g * u ≠ 0 := Nat.mul_ne_zero hg.ne' huPos.ne'
  rw [h15SquareDivisorCoefficient_eq_ite_sq_dvd hgu]
  split_ifs <;> ring

/-- Nonsquarefree divisor indices vanish before any analytic estimate. -/
theorem h15SquareDivisorCoefficient_eq_zero_of_not_squarefree
    {n d : ℕ} (hd : ¬ Squarefree d) :
    h15SquareDivisorCoefficient n d = 0 := by
  unfold h15SquareDivisorCoefficient
  split_ifs
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    norm_num
  · rfl

theorem h15PeriodSquareDivisorCrossRow_eq_zero_of_not_squarefree
    (g r k q : ℕ) {d : ℕ} (hd : ¬ Squarefree d) :
    h15PeriodSquareDivisorCrossRow g r k q d = 0 := by
  unfold h15PeriodSquareDivisorCrossRow
  simp [h15SquareDivisorCoefficient_eq_zero_of_not_squarefree hd]

/-- In the sector where the square divisor is coprime to the fixed gcd
parameter, the coupled incidence becomes the ordinary progression
`d^2 | u`. -/
theorem h15PeriodSquareDivisorCrossRow_eq_progression_of_coprime
    {g r k q d : ℕ} (hg : 0 < g) (hkq : 0 < k * q)
    (hdg : Nat.Coprime (d ^ 2) g) :
    h15PeriodSquareDivisorCrossRow g r k q d =
      ∑ u ∈ h15ReducedNaturalPeriod k q,
        (if d ^ 2 ∣ u then
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            h15PairedDirectCrossMode r u q
        else 0) := by
  rw [h15PeriodSquareDivisorCrossRow_eq_incidence hg hkq]
  apply Finset.sum_congr rfl
  intro u _
  simp only [hdg.dvd_mul_left]

/-- The constant squarefree reference term vanishes on every complete
period.  This is where the exact unweighted additive-character cancellation
is used before any absolute values are taken. -/
theorem h15PeriodSquarefreeFluctuationDefect_eq_unfrozen
    (N g r k q : ℕ) (hq : 0 < q) :
    h15PeriodSquarefreeFluctuationDefect N g r k q =
      h15SupportedInverseSmoothEnvelope N g (k * q) *
        ∑ u ∈ h15ReducedNaturalPeriod k q,
          h15SquarefreeIndicator (g * u) *
            h15PairedDirectCrossMode r u q := by
  unfold h15PeriodSquarefreeFluctuationDefect
  have hzero := sum_h15ReducedNaturalPeriod_crossMode_eq_zero r k q hq
  calc
    (∑ u ∈ h15ReducedNaturalPeriod k q,
        (h15SquarefreeIndicator (g * u) -
          h15SquarefreeIndicator (g * (k * q))) *
          h15SupportedInverseSmoothEnvelope N g (k * q) *
          h15PairedDirectCrossMode r u q) =
      (∑ u ∈ h15ReducedNaturalPeriod k q,
        h15SquarefreeIndicator (g * u) *
          h15SupportedInverseSmoothEnvelope N g (k * q) *
          h15PairedDirectCrossMode r u q) -
        h15SquarefreeIndicator (g * (k * q)) *
          h15SupportedInverseSmoothEnvelope N g (k * q) *
          (∑ u ∈ h15ReducedNaturalPeriod k q,
            h15PairedDirectCrossMode r u q) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro u _
        ring
    _ = ∑ u ∈ h15ReducedNaturalPeriod k q,
        h15SquarefreeIndicator (g * u) *
          h15SupportedInverseSmoothEnvelope N g (k * q) *
          h15PairedDirectCrossMode r u q := by rw [hzero, mul_zero, sub_zero]
    _ = h15SupportedInverseSmoothEnvelope N g (k * q) *
        ∑ u ∈ h15ReducedNaturalPeriod k q,
          h15SquarefreeIndicator (g * u) *
            h15PairedDirectCrossMode r u q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          ring

/-- Exact square-divisor reindexing of one complete-period H15 fluctuation. -/
theorem h15PeriodSquarefreeFluctuationDefect_eq_squareDivisorRows
    (N g r k q : ℕ) (hq : 0 < q) :
    h15PeriodSquarefreeFluctuationDefect N g r k q =
      h15SupportedInverseSmoothEnvelope N g (k * q) *
        ∑ d ∈ h15PeriodSquareDivisorIndices g k q,
          h15PeriodSquareDivisorCrossRow g r k q d := by
  rw [h15PeriodSquarefreeFluctuationDefect_eq_unfrozen N g r k q hq]
  congr 1
  calc
    (∑ u ∈ h15ReducedNaturalPeriod k q,
        h15SquarefreeIndicator (g * u) *
          h15PairedDirectCrossMode r u q) =
      ∑ u ∈ h15ReducedNaturalPeriod k q,
        (∑ d ∈ h15PeriodSquareDivisorIndices g k q,
          h15SquareDivisorCoefficient (g * u) d) *
            h15PairedDirectCrossMode r u q := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [h15SquarefreeIndicator_eq_sum_periodSquareDivisorCoefficients hu]
    _ = ∑ u ∈ h15ReducedNaturalPeriod k q,
        ∑ d ∈ h15PeriodSquareDivisorIndices g k q,
          h15SquareDivisorCoefficient (g * u) d *
            h15PairedDirectCrossMode r u q := by
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_mul]
    _ = ∑ d ∈ h15PeriodSquareDivisorIndices g k q,
        ∑ u ∈ h15ReducedNaturalPeriod k q,
          h15SquareDivisorCoefficient (g * u) d *
            h15PairedDirectCrossMode r u q := by
          rw [Finset.sum_comm]
    _ = ∑ d ∈ h15PeriodSquareDivisorIndices g k q,
        h15PeriodSquareDivisorCrossRow g r k q d := by
          rfl

/-! ## Dyadic square-divisor expansion -/

/-- The exact square-divisor expansion over all complete periods. -/
noncomputable def h15DyadicSquareDivisorExpansion
    (N g r U q : ℕ) : ℝ :=
  ∑ k ∈ h15CompletePeriodIndices U q,
    h15SupportedInverseSmoothEnvelope N g (k * q) *
      ∑ d ∈ h15PeriodSquareDivisorIndices g k q,
        h15PeriodSquareDivisorCrossRow g r k q d

theorem h15DyadicSquarefreeFluctuationDefect_eq_squareDivisorExpansion
    (N g r U q : ℕ) (hq : 0 < q) :
    h15DyadicSquarefreeFluctuationDefect N g r U q =
      h15DyadicSquareDivisorExpansion N g r U q := by
  unfold h15DyadicSquarefreeFluctuationDefect
    h15DyadicSquareDivisorExpansion
  apply Finset.sum_congr rfl
  intro k _
  exact h15PeriodSquarefreeFluctuationDefect_eq_squareDivisorRows
    N g r k q hq

/-! ## Absolute stop test after opening the squarefree factor -/

theorem h15SquarefreeIndicator_nonneg (n : ℕ) :
    0 ≤ h15SquarefreeIndicator n := by
  unfold h15SquarefreeIndicator
  split_ifs <;> norm_num

theorem h15SquarefreeIndicator_le_one (n : ℕ) :
    h15SquarefreeIndicator n ≤ 1 := by
  unfold h15SquarefreeIndicator
  split_ifs <;> norm_num

theorem h15SupportedInverseSmoothEnvelope_nonneg
    (N g u : ℕ) :
    0 ≤ h15SupportedInverseSmoothEnvelope N g u := by
  unfold h15SupportedInverseSmoothEnvelope
  split_ifs <;> positivity

/-- The smooth envelope, unlike the complete H15 square weight, has no
squarefree factor.  It nevertheless obeys the same inverse-square dyadic
majorant on its actual cutoff support. -/
theorem h15SupportedInverseSmoothEnvelope_le_of_mem_natBlock
    {N g U u : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hu : u ∈ h15BettinChandeeNatBlock U) :
    h15SupportedInverseSmoothEnvelope N g u ≤
      (1 / (U : ℝ)) ^ 2 := by
  unfold h15SupportedInverseSmoothEnvelope
  split_ifs with hsupport
  · have huBounds := Finset.mem_Ico.mp hu
    have huPos : 0 < u := hU.trans_le huBounds.1
    have hguPos : 0 < g * u := Nat.mul_pos hg huPos
    have hNpos : 0 < (N : ℝ) := by positivity
    have hguCastPos : 0 < ((g * u : ℕ) : ℝ) := by exact_mod_cast hguPos
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hratioOne :
        (1 : ℝ) ≤ (N : ℝ) / ((g * u : ℕ) : ℝ) :=
      (le_div_iff₀ hguCastPos).2 (by
        norm_num
        exact_mod_cast hsupport)
    have hratioPos :
        0 < (N : ℝ) / ((g * u : ℕ) : ℝ) :=
      div_pos hNpos hguCastPos
    have hguOne : (1 : ℝ) ≤ ((g * u : ℕ) : ℝ) := by
      exact_mod_cast hguPos
    have hratioN :
        (N : ℝ) / ((g * u : ℕ) : ℝ) ≤ (N : ℝ) := by
      apply (div_le_iff₀ hguCastPos).2
      nlinarith
    have hlogRatioNonneg :
        0 ≤ Real.log ((N : ℝ) / ((g * u : ℕ) : ℝ)) :=
      Real.log_nonneg hratioOne
    have hlogRatioLe :
        Real.log ((N : ℝ) / ((g * u : ℕ) : ℝ)) ≤
          Real.log (N : ℝ) :=
      Real.log_le_log hratioPos hratioN
    let taper : ℝ :=
      Real.log ((N : ℝ) / ((g * u : ℕ) : ℝ)) /
        Real.log (N : ℝ)
    have htaperNonneg : 0 ≤ taper :=
      div_nonneg hlogRatioNonneg hlogN.le
    have htaperLe : taper ≤ 1 :=
      (div_le_one hlogN).2 hlogRatioLe
    have htaperSq : taper ^ 2 ≤ 1 := by nlinarith
    have huCast : (U : ℝ) ≤ (u : ℝ) := by exact_mod_cast huBounds.1
    have huSq : (U : ℝ) ^ 2 ≤ (u : ℝ) ^ 2 := by nlinarith
    have hUSqPos : 0 < (U : ℝ) ^ 2 := by positivity
    calc
      taper ^ 2 / (u : ℝ) ^ 2 ≤ 1 / (u : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right htaperSq (by positivity)
      _ ≤ 1 / (U : ℝ) ^ 2 :=
        one_div_le_one_div_of_le hUSqPos huSq
      _ = (1 / (U : ℝ)) ^ 2 := by ring
  · positivity

/-- One complete period contributes at most its cardinality times `U^-2`
after absolute values.  The signed square-divisor expansion is not used in
this estimate; this is deliberately the comparison stop test. -/
theorem abs_h15PeriodSquarefreeFluctuationDefect_le
    {N g r U q k : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hq : 0 < q)
    (hk : k ∈ h15CompletePeriodIndices U q) :
    |h15PeriodSquarefreeFluctuationDefect N g r k q| ≤
      ((h15ReducedNaturalPeriod k q).card : ℝ) *
        (1 / (U : ℝ)) ^ 2 := by
  rw [h15PeriodSquarefreeFluctuationDefect_eq_unfrozen N g r k q hq,
    abs_mul]
  have hkBounds := (Finset.mem_filter.mp hk).2
  have hkqMem : k * q ∈ h15BettinChandeeNatBlock U :=
    Finset.mem_Ico.mpr (by
      refine ⟨hkBounds.1, ?_⟩
      exact (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self k) hq).trans_le
        hkBounds.2)
  have henv := h15SupportedInverseSmoothEnvelope_le_of_mem_natBlock
    hN hg hU hkqMem
  have henvNonneg :=
    h15SupportedInverseSmoothEnvelope_nonneg N g (k * q)
  have hsum :
      |∑ u ∈ h15ReducedNaturalPeriod k q,
          h15SquarefreeIndicator (g * u) *
            h15PairedDirectCrossMode r u q| ≤
        ((h15ReducedNaturalPeriod k q).card : ℝ) := by
    calc
      |∑ u ∈ h15ReducedNaturalPeriod k q,
          h15SquarefreeIndicator (g * u) *
            h15PairedDirectCrossMode r u q| ≤
        ∑ u ∈ h15ReducedNaturalPeriod k q,
          |h15SquarefreeIndicator (g * u) *
            h15PairedDirectCrossMode r u q| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u ∈ h15ReducedNaturalPeriod k q, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro u _
        rw [abs_mul, abs_of_nonneg (h15SquarefreeIndicator_nonneg (g * u))]
        calc
          h15SquarefreeIndicator (g * u) *
              |h15PairedDirectCrossMode r u q| ≤
            h15SquarefreeIndicator (g * u) * 1 :=
              mul_le_mul_of_nonneg_left
                (abs_h15PairedDirectCrossMode_le_one r u q hq)
                (h15SquarefreeIndicator_nonneg (g * u))
          _ ≤ 1 := by
            simpa using h15SquarefreeIndicator_le_one (g * u)
      _ = ((h15ReducedNaturalPeriod k q).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  rw [abs_of_nonneg henvNonneg]
  calc
    h15SupportedInverseSmoothEnvelope N g (k * q) *
        |∑ u ∈ h15ReducedNaturalPeriod k q,
          h15SquarefreeIndicator (g * u) *
            h15PairedDirectCrossMode r u q| ≤
      (1 / (U : ℝ)) ^ 2 *
        ((h15ReducedNaturalPeriod k q).card : ℝ) :=
          mul_le_mul henv hsum (abs_nonneg _) (by positivity)
    _ = ((h15ReducedNaturalPeriod k q).card : ℝ) *
        (1 / (U : ℝ)) ^ 2 := by ring

/-- Total absolute squarefree fluctuation on complete periods. -/
theorem abs_h15DyadicSquarefreeFluctuationDefect_le
    {N g r U q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hq : 0 < q) :
    |h15DyadicSquarefreeFluctuationDefect N g r U q| ≤
      1 / (U : ℝ) := by
  unfold h15DyadicSquarefreeFluctuationDefect
  calc
    |∑ k ∈ h15CompletePeriodIndices U q,
        h15PeriodSquarefreeFluctuationDefect N g r k q| ≤
      ∑ k ∈ h15CompletePeriodIndices U q,
        |h15PeriodSquarefreeFluctuationDefect N g r k q| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ h15CompletePeriodIndices U q,
        ((h15ReducedNaturalPeriod k q).card : ℝ) *
          (1 / (U : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact abs_h15PeriodSquarefreeFluctuationDefect_le
        hN hg hU hq hk
    _ = ((h15CompletePeriodSupport U q).card : ℝ) *
        (1 / (U : ℝ)) ^ 2 := by
      rw [← sum_card_h15ReducedNaturalPeriod U q, Finset.sum_mul]
    _ ≤ (U : ℝ) * (1 / (U : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15CompletePeriodSupport_le U q
    _ = 1 / (U : ℝ) := by
      have hU0 : (U : ℝ) ≠ 0 := by positivity
      field_simp

/-- The signed cross-modulus square-divisor aggregate.  Future work must
estimate this expression before taking absolute values in `q`, `k`, or `d`. -/
noncomputable def h15RamanujanSignedSquareDivisorAggregate
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    h15DyadicSquareDivisorExpansion N g r U q

/-- Its comparison absolute budget, which intentionally discards the signed
cross-modulus information. -/
noncomputable def h15RamanujanSquareDivisorAbsoluteBudget
    (N g r U Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    |h15DyadicSquareDivisorExpansion N g r U q|

theorem abs_h15RamanujanSignedSquareDivisorAggregate_le_budget
    (N g r U Q : ℕ) :
    |h15RamanujanSignedSquareDivisorAggregate N g r U Q| ≤
      h15RamanujanSquareDivisorAbsoluteBudget N g r U Q := by
  unfold h15RamanujanSignedSquareDivisorAggregate
    h15RamanujanSquareDivisorAbsoluteBudget
  exact Finset.abs_sum_le_sum_abs _ _

/-- Opening the squarefree factor and then applying triangle inequality gives
only `Q/U`; it introduces no balanced power saving. -/
theorem h15RamanujanSquareDivisorAbsoluteBudget_le
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hQ : 0 < Q) :
    h15RamanujanSquareDivisorAbsoluteBudget N g r U Q ≤
      (Q : ℝ) / (U : ℝ) := by
  unfold h15RamanujanSquareDivisorAbsoluteBudget
  calc
    (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        |h15DyadicSquareDivisorExpansion N g r U q|) ≤
      ∑ _q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        1 / (U : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hq
      have hqPos : 0 < q := hQ.trans_le hqBounds.1
      rw [← h15DyadicSquarefreeFluctuationDefect_eq_squareDivisorExpansion
        N g r U q hqPos]
      exact abs_h15DyadicSquarefreeFluctuationDefect_le hN hg hU hqPos
    _ = ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
        (1 / (U : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * (1 / (U : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15BettinChandeeSupportedNatBlock_le N g Q
    _ = (Q : ℝ) / (U : ℝ) := by ring

theorem h15RamanujanSquareDivisorAbsoluteBudget_balanced_le
    {N g r U : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) :
    h15RamanujanSquareDivisorAbsoluteBudget N g r U U ≤ 1 := by
  calc
    h15RamanujanSquareDivisorAbsoluteBudget N g r U U ≤
        (U : ℝ) / (U : ℝ) :=
      h15RamanujanSquareDivisorAbsoluteBudget_le hN hg hU hU
    _ = 1 := by field_simp

/-- Balanced exponent produced by the absolute square-divisor route. -/
noncomputable def h15RamanujanSquareDivisorAbsoluteBalancedExponent : ℝ := 0

theorem h15RamanujanSquareDivisorAbsoluteBalancedExponent_not_neg :
    ¬ h15RamanujanSquareDivisorAbsoluteBalancedExponent < 0 := by
  norm_num [h15RamanujanSquareDivisorAbsoluteBalancedExponent]

/-- Exact lower-middle arithmetic gate left by the audit.  An inhabitant must
retain cancellation jointly across square divisors, periods, and moduli. -/
structure H15SignedSquareDivisorPowerSaving where
  C : ℝ
  η : ℝ
  C_nonneg : 0 ≤ C
  η_pos : 0 < η
  bound : ∀ {N g r U Q : ℕ},
    2 ≤ N → 1 ≤ g → 0 < U → 0 < Q → Q ≤ U →
    |h15RamanujanSignedSquareDivisorAggregate N g r U Q| ≤
      C / (U : ℝ) ^ η

end NBMellinTools.NB12
