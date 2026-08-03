import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhm
import RiemannHypothesis.Criteria.NymanBeurling.MobiusSummatoryClassical

/-!
# Ehm--MacLeod finite Möbius-inversion identity

This module formalizes the exact `q = 1` identity in Proposition 8.2 of
Werner Ehm, *On certain Gram matrices and their associated series* (2024).
It is a finite identity at a natural cutoff.  No asymptotic estimate for its
Möbius transform is asserted.

The proof isolates the elementary hyperbolic convolution behind Ehm's
argument: the Möbius transform of
`W(x) = x H(x) - floor(x)` is `x - 1` at positive natural `x`.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMacLeod

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.MobiusSummatory

/-- Ehm's auxiliary function `W(x) = x H(x) - floor(x)` from the proof of
Proposition 8.2. -/
noncomputable def ehmMacLeodW (x : ℝ) : ℝ :=
  x * ehmHarmonic x - ⌊x⌋₊

/-- Ehm's transform `Φ₁(N) = Σₙ≤N μ(n) (N/n) R₁(N/n)`, at a
positive natural cutoff. -/
noncomputable def ehmMacLeodPhi1 (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
      (((N : ℝ) / (n : ℝ)) * ehmR1 ((N : ℝ) / (n : ℝ)))

/-- Ehm's centered first Landau moment. -/
noncomputable def ehmCenteredRawL1 (N : ℕ) : ℝ :=
  rawMobiusHarmonicMoment 1 N + 1

/-- Ehm's first log-taper difference
`Δ L̄₀(N) = L₀(N) - L̄₁(N) / log N`. -/
noncomputable def ehmDeltaCenteredRawL0 (N : ℕ) : ℝ :=
  rawMobiusHarmonicMoment 0 N - ehmCenteredRawL1 N / Real.log N

private theorem hyperbolicRow_eq_divisibleRow
    (f : ℕ → ℝ) (d J : ℕ) (hd : 0 < d) :
    (∑ k ∈ Finset.Icc 1 J, if d * k ≤ J then f (d * k) else 0) =
      ∑ j ∈ Finset.Icc 1 J, if d ∣ j then f j else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ ↦ d * k)
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkIcc, hdkJ⟩
    rcases Finset.mem_Icc.mp hkIcc with ⟨hk1, _⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hd (lt_of_lt_of_le Nat.zero_lt_one hk1), hdkJ⟩,
      dvd_mul_right d k⟩
  · intro a _ b _ hab
    exact Nat.mul_left_cancel hd hab
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjIcc, hdj⟩
    rcases Finset.mem_Icc.mp hjIcc with ⟨hj1, hjJ⟩
    refine ⟨j / d, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      have hdjpos : 0 < j / d :=
        Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hj1) hdj) hd
      exact ⟨Finset.mem_Icc.mpr
        ⟨hdjpos, (Nat.div_le_self j d).trans hjJ⟩, by
          rw [Nat.mul_div_cancel' hdj]
          exact hjJ⟩
    · exact Nat.mul_div_cancel' hdj
  · intro k _
    rfl

private theorem positiveDivisors_filter_eq
    (N j : ℕ) (hj : 0 < j) (hjN : j ≤ N) :
    (Finset.Icc 1 N).filter (fun d ↦ d ∣ j) = j.divisors := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd1, _⟩, hdj⟩
    exact ⟨hdj, Nat.ne_of_gt hj⟩
  · rintro ⟨hdj, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdj hj,
      (Nat.le_of_dvd hj hdj).trans hjN⟩, hdj⟩

private theorem ehmHarmonic_ratio_eq_hyperbolicRow
    (N d : ℕ) (hd : 0 < d) :
    ((N : ℝ) / (d : ℝ)) * ehmHarmonic ((N : ℝ) / (d : ℝ)) =
      ∑ k ∈ Finset.Icc 1 N,
        if d * k ≤ N then (N : ℝ) / ((d * k : ℕ) : ℝ) else 0 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold ehmHarmonic
  rw [Nat.floor_div_eq_div]
  rw [Finset.mul_sum]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Icc 1 N).filter (fun k ↦ d * k ≤ N) =
        Finset.Icc 1 (N / d) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, _⟩, hdk⟩
      exact ⟨hk1, (Nat.le_div_iff_mul_le hd).2 (by simpa [Nat.mul_comm] using hdk)⟩
    · rintro ⟨hk1, hkdiv⟩
      have hdk : d * k ≤ N := by
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).1 hkdiv
      have hkdk : k ≤ d * k := by
        calc
          k = 1 * k := by simp
          _ ≤ d * k := Nat.mul_le_mul_right k (by omega)
      exact ⟨⟨hk1, hkdk.trans hdk⟩, hdk⟩
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro k hk
  have hk : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp [hdR, hkR]

/-- Finite hyperbolic identity underlying Ehm's Proposition 8.2:
`Σₙ≤N μ(n) (N/n) H(N/n) = N`. -/
theorem ehm_mobius_harmonic_hyperbola_identity (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (((N : ℝ) / (d : ℝ)) * ehmHarmonic ((N : ℝ) / (d : ℝ)))) =
      N := by
  classical
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          if d * k ≤ N then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              ((N : ℝ) / ((d * k : ℕ) : ℝ))
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hdmem
      have hd : 0 < d :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdmem).1
      rw [ehmHarmonic_ratio_eq_hyperbolicRow N d hd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split <;> simp_all
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          if d ∣ j then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              ((N : ℝ) / (j : ℝ))
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hdmem
      exact hyperbolicRow_eq_divisibleRow
        (fun j ↦ ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          ((N : ℝ) / (j : ℝ))) d N
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdmem).1)
    _ = ∑ j ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
          if d ∣ j then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              ((N : ℝ) / (j : ℝ))
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.Icc 1 N,
          (if j = 1 then (N : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro j hjmem
      have hj : 0 < j :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hjmem).1
      have hjN : j ≤ N := (Finset.mem_Icc.mp hjmem).2
      rw [← Finset.sum_filter, positiveDivisors_filter_eq N j hj hjN]
      rw [← Finset.sum_mul]
      have hmu := congrArg (fun z : ℤ ↦ (z : ℝ))
        (sum_moebius_divisors_int j)
      push_cast at hmu
      rw [hmu]
      split <;> simp_all
    _ = N := by
      rw [Finset.sum_eq_single 1]
      · simp
      · intro b hb _
        simp_all
      · simp [hN]

/-- The Möbius transform of Ehm's auxiliary `W` is exactly `N - 1`.
This is the finite Möbius-inversion step in Proposition 8.2. -/
theorem ehm_mobius_W_identity (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
        ehmMacLeodW ((N : ℝ) / (n : ℝ))) = (N : ℝ) - 1 := by
  unfold ehmMacLeodW
  have hfloor :
      (∑ n ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          (⌊(N : ℝ) / (n : ℝ)⌋₊ : ℝ)) = 1 := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ))
      (mobius_floor_hyperbola_identity N hN)
    push_cast at h
    simpa [Nat.floor_div_eq_div] using h
  calc
    _ = (∑ n ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            ((N : ℝ) / (n : ℝ) * ehmHarmonic ((N : ℝ) / (n : ℝ)))) -
        ∑ n ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            (⌊(N : ℝ) / (n : ℝ)⌋₊ : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by
      rw [ehm_mobius_harmonic_hyperbola_identity N hN, hfloor]

/-- The centered difference in Proposition 8.2 is the existing BCF
log-tapered Landau moment, with only the explicit centering term removed. -/
theorem ehmDeltaCenteredRawL0_eq_ehmL_sub (N : ℕ) (hN : 2 ≤ N) :
    ehmDeltaCenteredRawL0 N = ehmL 0 N - 1 / Real.log N := by
  rw [ehmL_eq_rawMobiusHarmonicMoments 0 N hN]
  simp only [Nat.zero_add]
  unfold ehmDeltaCenteredRawL0 ehmCenteredRawL1
  ring

/-- Exact natural-cutoff form of Ehm (2024), Proposition 8.2, equation (57).
It rewrites the centered log-taper difference in terms of the Mertens and
Landau moments and the signed transform `Φ₁`; it does not estimate any of
those quantities. -/
theorem ehm_macleod_proposition_8_2 (N : ℕ) (hN : 2 ≤ N) :
    (1 - Real.eulerMascheroniConstant) * rawMobiusHarmonicMoment 0 N -
        (1 / 2 : ℝ) * rawMobiusMoment 0 N / N =
      ehmDeltaCenteredRawL0 N * Real.log N - ehmMacLeodPhi1 N / N + 1 / N := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hlog : Real.log (N : ℝ) ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by exact_mod_cast (by omega : N ≠ 1))
  have hW := ehm_mobius_W_identity N (by omega)
  have hPhi :
      ehmMacLeodPhi1 N =
        (N : ℝ) * Real.log N * rawMobiusHarmonicMoment 0 N -
          (N : ℝ) * rawMobiusHarmonicMoment 1 N +
          (Real.eulerMascheroniConstant - 1) * (N : ℝ) *
            rawMobiusHarmonicMoment 0 N -
          ((N : ℝ) - 1) + (1 / 2 : ℝ) * rawMobiusMoment 0 N := by
    unfold ehmMacLeodPhi1 rawMobiusHarmonicMoment rawMobiusMoment
    calc
      _ = ∑ n ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            (((N : ℝ) / (n : ℝ)) *
              (Real.log (N : ℝ) - Real.log (n : ℝ) +
                Real.eulerMascheroniConstant - 1) -
              ehmMacLeodW ((N : ℝ) / (n : ℝ)) + 1 / 2) := by
        apply Finset.sum_congr rfl
        intro n hnmem
        have hn : 0 < n :=
          lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnmem).1
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        have hy : 0 ≤ (N : ℝ) / (n : ℝ) := by positivity
        have hfract : Int.fract ((N : ℝ) / (n : ℝ)) =
            (N : ℝ) / (n : ℝ) -
              (⌊(N : ℝ) / (n : ℝ)⌋₊ : ℝ) := by
          calc
            Int.fract ((N : ℝ) / (n : ℝ)) =
                (N : ℝ) / (n : ℝ) -
                  ((⌊(N : ℝ) / (n : ℝ)⌋ : ℤ) : ℝ) := by
              linarith [Int.floor_add_fract ((N : ℝ) / (n : ℝ))]
            _ = _ := by rw [← natCast_floor_eq_intCast_floor hy]
        have hinner :
            ((N : ℝ) / (n : ℝ)) * ehmR1 ((N : ℝ) / (n : ℝ)) =
              ((N : ℝ) / (n : ℝ)) *
                  (Real.log (N : ℝ) - Real.log (n : ℝ) +
                    Real.eulerMascheroniConstant - 1) -
                ehmMacLeodW ((N : ℝ) / (n : ℝ)) + 1 / 2 := by
          unfold ehmR1 ehmMacLeodW
          rw [Real.log_div hNR hnR, hfract]
          field_simp [hNR, hnR]
          ring
        rw [hinner]
      _ = _ := by
        simp only [pow_zero, mul_one]
        have hA :
            (∑ n ∈ Finset.Icc 1 N,
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                ((N : ℝ) / (n : ℝ) * Real.log (N : ℝ))) =
              (N : ℝ) * Real.log N *
                ∑ n ∈ Finset.Icc 1 N,
                  ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          ring
        have hB :
            (∑ n ∈ Finset.Icc 1 N,
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                ((N : ℝ) / (n : ℝ) * Real.log (n : ℝ))) =
              (N : ℝ) *
                ∑ n ∈ Finset.Icc 1 N,
                  ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                    Real.log (n : ℝ) / (n : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          ring
        have hC :
            (∑ n ∈ Finset.Icc 1 N,
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                ((N : ℝ) / (n : ℝ) *
                  (Real.eulerMascheroniConstant - 1))) =
              (Real.eulerMascheroniConstant - 1) * (N : ℝ) *
                ∑ n ∈ Finset.Icc 1 N,
                  ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          ring
        have hHalf :
            (∑ n ∈ Finset.Icc 1 N,
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (1 / 2 : ℝ)) =
              (1 / 2 : ℝ) *
                ∑ n ∈ Finset.Icc 1 N,
                  ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          ring
        have hsplit :
            (∑ n ∈ Finset.Icc 1 N,
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                ((N : ℝ) / (n : ℝ) *
                    (Real.log N - Real.log n +
                      Real.eulerMascheroniConstant - 1) -
                  ehmMacLeodW ((N : ℝ) / (n : ℝ)) + 1 / 2)) =
              (∑ n ∈ Finset.Icc 1 N,
                ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                  ((N : ℝ) / (n : ℝ) * Real.log N)) -
              (∑ n ∈ Finset.Icc 1 N,
                ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                  ((N : ℝ) / (n : ℝ) * Real.log n)) +
              (∑ n ∈ Finset.Icc 1 N,
                ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                  ((N : ℝ) / (n : ℝ) *
                    (Real.eulerMascheroniConstant - 1))) -
              (∑ n ∈ Finset.Icc 1 N,
                ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
                  ehmMacLeodW ((N : ℝ) / (n : ℝ))) +
              ∑ n ∈ Finset.Icc 1 N,
                ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (1 / 2 : ℝ) := by
          simp only [mul_add, mul_sub, Finset.sum_add_distrib,
            Finset.sum_sub_distrib]
          ring
        calc
          _ = _ := hsplit
          _ = _ := by
            rw [hA, hB, hC, hW, hHalf]
            simp only [pow_one]
  rw [hPhi]
  unfold ehmDeltaCenteredRawL0 ehmCenteredRawL1
  field_simp [hNR, hlog]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMacLeod
