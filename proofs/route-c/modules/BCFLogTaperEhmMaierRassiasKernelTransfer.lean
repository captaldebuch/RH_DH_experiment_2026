import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDirectFeasibility
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
import RiemannHypothesis.Criteria.NymanBeurling.MobiusSummatoryClassical

/-!
# Exact finite transfer from the Maier--Rassias kernel to Ehm's `R₁`

This file performs the first pass/fail test in the Ehm-direct programme.
The endpoint-corrected Maier--Rassias Fourier kernel contains the periodic
Bernoulli modes

`g_L(x) = -2 * sum_{1 ≤ l ≤ L} B₁(l*x) / l`.

Finite Möbius inversion extracts its first mode exactly.  The resulting
identity expresses Ehm's `R₁` as its smooth and endpoint parts plus a finite
hyperbolic Möbius average of truncated Maier--Rassias kernels.

The identity preserves every pre-existing H15 coefficient and taper.  It
does not, however, reduce H15 to one Maier--Rassias row: it introduces an
additional dilation variable `k`, and at `x = d*q/m` its kernel is evaluated
at `k*d*q/m`.  Thus the exact transfer exposes, rather than removes, the
joint arithmetic coupling.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMaierRassiasKernelTransfer

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDirectFeasibility
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit
open RH.Criteria.NymanBeurling.MobiusSummatory
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## The finite Möbius transform of truncated Maier--Rassias kernels -/

/-- A finite hyperbolic Möbius average of truncated Maier--Rassias kernels.
The cutoff `K / k` is essential: it makes the frequency region exactly
`k*l ≤ K`. -/
noncomputable def maierRassiasMobiusHyperbolicPartial
    (K : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K,
    (((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ)) *
      maierRassiasKernelPartialSum (K / k) ((k : ℝ) * x)

/-- The same hyperbolic average with the product cutoff written explicitly. -/
noncomputable def maierRassiasMobiusExpandedPartial
    (K : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 K,
    if k * l ≤ K then
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
        (-2 * bernoulliB1 (((k * l : ℕ) : ℝ) * x)) /
          ((k * l : ℕ) : ℝ)
    else 0

/-- The product-grouped form of the same average. -/
noncomputable def maierRassiasMobiusGroupedPartial
    (K : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 K,
    (((∑ k ∈ n.divisors, ArithmeticFunction.moebius k : ℤ) : ℝ) *
      (-2 * bernoulliB1 ((n : ℝ) * x)) / (n : ℝ))

private theorem cutoffRow_eq_hyperbolicRow
    (f : ℕ → ℝ) (k K : ℕ) (hk : 0 < k) :
    (∑ l ∈ Finset.Icc 1 (K / k), f l) =
      ∑ l ∈ Finset.Icc 1 K, if k * l ≤ K then f l else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext l
  simp only [Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro ⟨hl1, hlK⟩
    have hklK : k * l ≤ K := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk).1 hlK
    have hlkl : l ≤ k * l := by
      calc
        l = 1 * l := by simp
        _ ≤ k * l := Nat.mul_le_mul_right l (by omega)
    exact ⟨⟨hl1, hlkl.trans hklK⟩, hklK⟩
  · rintro ⟨⟨hl1, _⟩, hklK⟩
    exact ⟨hl1, (Nat.le_div_iff_mul_le hk).2
      (by simpa [Nat.mul_comm] using hklK)⟩

private theorem hyperbolicRow_eq_divisibleRow
    (f : ℕ → ℝ) (k K : ℕ) (hk : 0 < k) :
    (∑ l ∈ Finset.Icc 1 K, if k * l ≤ K then f (k * l) else 0) =
      ∑ n ∈ Finset.Icc 1 K, if k ∣ n then f n else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun l _ ↦ k * l)
  · intro l hl
    rcases Finset.mem_filter.mp hl with ⟨hlIcc, hklK⟩
    rcases Finset.mem_Icc.mp hlIcc with ⟨hl1, _⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨Nat.mul_pos hk (lt_of_lt_of_le Nat.zero_lt_one hl1), hklK⟩,
        dvd_mul_right k l⟩
  · intro a _ b _ hab
    exact Nat.mul_left_cancel hk hab
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hkn⟩
    rcases Finset.mem_Icc.mp hnIcc with ⟨hn1, hnK⟩
    refine ⟨n / k, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      have hquotPos : 0 < n / k :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hkn) hk
      exact ⟨Finset.mem_Icc.mpr
        ⟨hquotPos, (Nat.div_le_self n k).trans hnK⟩, by
          rw [Nat.mul_div_cancel' hkn]
          exact hnK⟩
    · exact Nat.mul_div_cancel' hkn
  · intro l _
    rfl

private theorem positiveDivisors_filter_eq
    (K n : ℕ) (hn : 0 < n) (hnK : n ≤ K) :
    (Finset.Icc 1 K).filter (fun k ↦ k ∣ n) = n.divisors := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hk1, _⟩, hkn⟩
    exact ⟨hkn, Nat.ne_of_gt hn⟩
  · rintro ⟨hkn, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hkn hn,
      (Nat.le_of_dvd hn hkn).trans hnK⟩, hkn⟩

/-- Expanding each truncated kernel turns the nested cutoff `K/k` into the
single hyperbolic region `k*l ≤ K`. -/
theorem maierRassiasMobiusHyperbolicPartial_eq_expanded
    (K : ℕ) (x : ℝ) :
    maierRassiasMobiusHyperbolicPartial K x =
      maierRassiasMobiusExpandedPartial K x := by
  classical
  unfold maierRassiasMobiusHyperbolicPartial
    maierRassiasMobiusExpandedPartial
  apply Finset.sum_congr rfl
  intro k hkMem
  have hk : 0 < k :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hkMem).1
  rw [maierRassiasKernelPartialSum,
    cutoffRow_eq_hyperbolicRow
      (fun l ↦ -2 * bernoulliB1 ((l : ℝ) * ((k : ℝ) * x)) / (l : ℝ))
      k K hk,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hlMem
  by_cases hkl : k * l ≤ K
  · simp only [hkl, if_true]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hl : 0 < l :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hlMem).1
    have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
    push_cast
    field_simp [hkR, hlR]
  · simp [hkl]

/-- Grouping the hyperbolic region by `n = k*l` produces the finite divisor
sum of the Möbius function as the coefficient of the `n`th Bernoulli mode. -/
theorem maierRassiasMobiusExpandedPartial_eq_grouped
    (K : ℕ) (x : ℝ) :
    maierRassiasMobiusExpandedPartial K x =
      maierRassiasMobiusGroupedPartial K x := by
  classical
  unfold maierRassiasMobiusExpandedPartial
    maierRassiasMobiusGroupedPartial
  calc
    (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 K,
      if k * l ≤ K then
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
          (-2 * bernoulliB1 (((k * l : ℕ) : ℝ) * x)) /
            ((k * l : ℕ) : ℝ)
      else 0) =
        ∑ k ∈ Finset.Icc 1 K, ∑ n ∈ Finset.Icc 1 K,
          if k ∣ n then
            ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
              (-2 * bernoulliB1 ((n : ℝ) * x)) / (n : ℝ)
          else 0 := by
      apply Finset.sum_congr rfl
      intro k hkMem
      exact hyperbolicRow_eq_divisibleRow
        (fun n ↦ ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
          (-2 * bernoulliB1 ((n : ℝ) * x)) / (n : ℝ))
        k K (lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp hkMem).1)
    _ = ∑ n ∈ Finset.Icc 1 K, ∑ k ∈ Finset.Icc 1 K,
          if k ∣ n then
            ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
              (-2 * bernoulliB1 ((n : ℝ) * x)) / (n : ℝ)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.Icc 1 K,
        (((∑ k ∈ n.divisors, ArithmeticFunction.moebius k : ℤ) : ℝ) *
          (-2 * bernoulliB1 ((n : ℝ) * x)) / (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hnMem
      have hn : 0 < n :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnMem).1
      have hnK : n ≤ K := (Finset.mem_Icc.mp hnMem).2
      rw [← Finset.sum_filter,
        positiveDivisors_filter_eq K n hn hnK]
      rw [← Finset.sum_div, ← Finset.sum_mul]
      push_cast
      rfl

/-- Finite Möbius inversion kills every Bernoulli frequency except the
first.  This is the exact kernel-transfer mechanism. -/
theorem maierRassiasMobiusGroupedPartial_eq_firstMode
    (K : ℕ) (x : ℝ) (hK : 1 ≤ K) :
    maierRassiasMobiusGroupedPartial K x = -2 * bernoulliB1 x := by
  classical
  unfold maierRassiasMobiusGroupedPartial
  rw [Finset.sum_eq_single 1]
  · simp
  · intro n hnMem hn1
    rw [sum_moebius_divisors_int]
    simp [hn1]
  · simp [hK]

/-- The complete exact finite transfer identity for the periodic Bernoulli
mode. -/
theorem maierRassiasMobiusHyperbolicPartial_eq_firstMode
    (K : ℕ) (x : ℝ) (hK : 1 ≤ K) :
    maierRassiasMobiusHyperbolicPartial K x = -2 * bernoulliB1 x := by
  rw [maierRassiasMobiusHyperbolicPartial_eq_expanded,
    maierRassiasMobiusExpandedPartial_eq_grouped,
    maierRassiasMobiusGroupedPartial_eq_firstMode K x hK]

/-- At an H15 rational argument, expansion of the transfer introduces the
joint numerator `k*d*q` over the original denominator `m`.  This theorem is
the exact finite form of the coupling obstruction. -/
theorem maierRassiasMobiusHyperbolicPartial_at_h15Ratio
    (K d q m : ℕ) :
    maierRassiasMobiusHyperbolicPartial K
        (((d * q : ℕ) : ℝ) / (m : ℝ)) =
      ∑ k ∈ Finset.Icc 1 K,
        (((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ)) *
          maierRassiasKernelPartialSum (K / k)
            (((k * d * q : ℕ) : ℝ) / (m : ℝ)) := by
  classical
  unfold maierRassiasMobiusHyperbolicPartial
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  push_cast
  ring

/-! ## Exact pointwise and H15-row transfer -/

/-- The expression obtained by replacing Ehm's Bernoulli constituent by
the exact finite Maier--Rassias Möbius transform. -/
noncomputable def ehmR1ViaMaierRassias
    (K : ℕ) (x : ℝ) : ℝ :=
  ehmR1SmoothPart x + ehmR1IntegerEndpointPart x +
    maierRassiasMobiusHyperbolicPartial K x / (2 * x)

/-- Exact pointwise transfer.  The only excluded point is `x = 0`, where
the displayed quotient is not the representation used for `R₁`. -/
theorem ehmR1_eq_viaMaierRassias
    (K : ℕ) (x : ℝ) (hK : 1 ≤ K) (hx : x ≠ 0) :
    ehmR1 x = ehmR1ViaMaierRassias K x := by
  rw [ehmR1_eq_smooth_sub_bernoulli_add_endpoint,
    ehmR1ViaMaierRassias,
    maierRassiasMobiusHyperbolicPartial_eq_firstMode K x hK]
  unfold ehmR1BernoulliSawtoothPart
  field_simp [hx]
  ring

/-- The exact kernel transfer lifts through the actual `q = 1` H15 row
without changing its Möbius coefficient, interval, cutoff, or taper-pair
amplitude. -/
theorem ehmTypeIQOneInnerRow_eq_viaMaierRassias
    (K X D J m : ℕ) (hK : 1 ≤ K) (hm : 0 < m) :
    ehmTypeIQOneInnerRow ehmR1 X D J m =
      ehmTypeIQOneInnerRow (ehmR1ViaMaierRassias K) X D J m := by
  classical
  unfold ehmTypeIQOneInnerRow
  apply Finset.sum_congr rfl
  intro d hdMem
  have hd : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one
      ((Nat.succ_le_succ (Nat.zero_le X)).trans
        (Finset.mem_Icc.mp hdMem).1)
  by_cases hdJ : d ≤ J
  · simp only [hdJ, if_true]
    rw [ehmR1_eq_viaMaierRassias K _ hK]
    exact div_ne_zero (by exact_mod_cast hd.ne')
      (by exact_mod_cast hm.ne')
  · simp [hdJ]

/-- The exact transfer lifts through the complete outer `q = 1` sector. -/
theorem ehmDyadicNearTypeIQOne_eq_viaMaierRassias
    (K X D J U : ℕ) (hK : 1 ≤ K) :
    ehmDyadicNearTypeIQOne ehmR1 X D J U =
      ehmDyadicNearTypeIQOne (ehmR1ViaMaierRassias K) X D J U := by
  rw [ehmDyadicNearTypeIQOne_eq_outer_rows,
    ehmDyadicNearTypeIQOne_eq_outer_rows]
  apply Finset.sum_congr rfl
  intro m hmMem
  rw [ehmTypeIQOneInnerRow_eq_viaMaierRassias K X D J m hK]
  exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hmMem).1

/-- The transfer also lifts through every `q ≥ 2` row.  Its argument is now
`k*d*q/m` inside `maierRassiasMobiusHyperbolicPartial`; hence this exact
identity preserves the H15 taper but introduces an additional dilation
variable rather than separating the existing `(q,m)` dependence. -/
theorem ehmDyadicNearTypeIQGeTwo_eq_viaMaierRassias
    (K X D J U : ℕ) (hK : 1 ≤ K) :
    ehmDyadicNearTypeIQGeTwo ehmR1 X D J U =
      ehmDyadicNearTypeIQGeTwo (ehmR1ViaMaierRassias K) X D J U := by
  classical
  unfold ehmDyadicNearTypeIQGeTwo
  apply Finset.sum_congr rfl
  intro m hmMem
  have hm : 0 < m :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hmMem).1
  apply Finset.sum_congr rfl
  intro d hdMem
  have hd : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one
      ((Nat.succ_le_succ (Nat.zero_le X)).trans
        (Finset.mem_Icc.mp hdMem).1)
  apply Finset.sum_congr rfl
  intro q hqMem
  have hq : 0 < q :=
    lt_of_lt_of_le Nat.zero_lt_one
      ((show 1 ≤ 2 by omega).trans (Finset.mem_Icc.mp hqMem).1)
  by_cases hdq : d * q ≤ J
  · simp only [hdq, if_true]
    rw [ehmR1_eq_viaMaierRassias K _ hK]
    exact div_ne_zero (by positivity) (by exact_mod_cast hm.ne')
  · simp [hdq]

/-- Priority-1 conclusion: the transfer is exact on the entire H15 Type-I
sector and preserves the existing taper.  Combined with
`maierRassiasMobiusHyperbolicPartial_at_h15Ratio`, it also proves that this
transfer does not separate the `q` and `m` variables. -/
theorem ehmDyadicNearTypeI_eq_viaMaierRassias
    (K X D J U : ℕ) (hK : 1 ≤ K) (hJ : 1 ≤ J) :
    ehmDyadicNearTypeI ehmR1 X D J U =
      ehmDyadicNearTypeI (ehmR1ViaMaierRassias K) X D J U := by
  rw [ehmDyadicNearTypeI_eq_qOne_add_qGeTwo _ X D J U hJ,
    ehmDyadicNearTypeI_eq_qOne_add_qGeTwo _ X D J U hJ,
    ehmDyadicNearTypeIQOne_eq_viaMaierRassias K X D J U hK,
    ehmDyadicNearTypeIQGeTwo_eq_viaMaierRassias K X D J U hK]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMaierRassiasKernelTransfer
