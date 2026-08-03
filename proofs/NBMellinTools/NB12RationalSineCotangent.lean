/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12VaalerTail

/-!
# NB12a: exact rational sine--cotangent modes

This module proves the finite trigonometric identity behind the rational
Fourier rows in `NB12VaalerTail`.  For a positive modulus `q`, the complete
cotangent transform of the rational sine mode is

`sum_{1 <= a < q} sin(2*pi*n*a/q) cot(pi*a/q)
  = 0` if `q | n`, and `q - 2*(n mod q)` otherwise.

Combining this finite identity with the already verified BBLS rational
harmonic-series theorem gives fixed-row convergence of the exact NB12
Fourier remainder.  No uniformity in the moving moduli or Möbius-weighted
bilinear aggregate is claimed here.
-/

open Filter
open scoped BigOperators Topology

namespace NBMellinTools.NB12

open NBMellinTools.NB8
open NBMellinTools.NB10
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## Finite cosine sums -/

/-- The real cosine coefficient at a rational frequency. -/
noncomputable def rationalCosinePeriodicTermNB12
    (n q a : ℕ) : ℝ :=
  Real.cos (2 * Real.pi * ((n : ℝ) / q) * a)

/-- The rational cosine coefficient is the real part of the standard
additive character on `ZMod q`. -/
theorem rationalCosinePeriodicTermNB12_eq_stdAddChar_re
    (n q a : ℕ) [NeZero q] :
    rationalCosinePeriodicTermNB12 n q a =
      (ZMod.stdAddChar (((n * a : ℕ) : ZMod q))).re := by
  rw [ZMod.stdAddChar_apply]
  have h := ZMod.toCircle_intCast (N := q) ((n * a : ℕ) : ℤ)
  have h' : ((ZMod.toCircle ((n * a : ℕ) : ZMod q) : Circle) : ℂ) =
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (n * a : ℂ) / (q : ℂ)) := by
    simpa using h
  rw [h']
  simp [rationalCosinePeriodicTermNB12, Complex.exp_re]
  congr 1
  field_simp

/-- A nontrivial standard additive character sums to zero over the canonical
natural representatives of `ZMod q`. -/
theorem stdAddChar_mul_nat_range_sum_eq_zeroNB12
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    (∑ a ∈ Finset.range q,
      ZMod.stdAddChar (j * (a : ZMod q))) = 0 := by
  have hchar : (∑ z : ZMod q, ZMod.stdAddChar (z * j)) = 0 := by
    simpa [hj] using AddChar.sum_mulShift (ψ := ZMod.stdAddChar) j
      (ZMod.isPrimitive_stdAddChar q)
  have hfin :
      (∑ a : Fin q,
        ZMod.stdAddChar ((ZMod.finEquiv q a) * j)) = 0 := by
    calc
      (∑ a : Fin q, ZMod.stdAddChar ((ZMod.finEquiv q a) * j)) =
          ∑ z : ZMod q, ZMod.stdAddChar (z * j) := by
            apply Fintype.sum_equiv (ZMod.finEquiv q)
            intro a
            rfl
      _ = 0 := hchar
  have hfinCast (a : Fin q) :
      ZMod.finEquiv q a = (a : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
        apply ZMod.val_injective (q + 1)
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
        rfl
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ a : Fin q, ZMod.stdAddChar (j * (a : ZMod q))) =
        ∑ a : Fin q,
          ZMod.stdAddChar ((ZMod.finEquiv q a) * j) := by
            apply Finset.sum_congr rfl
            intro a _
            apply congrArg ZMod.stdAddChar
            rw [hfinCast a, mul_comm]
    _ = 0 := hfin

/-- Every nonzero cosine frequency below the modulus has sum `-1` over the
nonzero residue representatives. -/
theorem sum_rationalCosinePeriodicTermNB12_eq_neg_one
    {q n : ℕ} [NeZero q] (hn0 : 0 < n) (hnq : n < q) :
    (∑ a ∈ Finset.Ioc 0 (q - 1),
      rationalCosinePeriodicTermNB12 n q a) = -1 := by
  have hj : (n : ZMod q) ≠ 0 := by
    intro hj0
    have hval := congrArg ZMod.val hj0
    rw [ZMod.val_natCast_of_lt hnq] at hval
    simp only [ZMod.val_zero] at hval
    omega
  have hchar := stdAddChar_mul_nat_range_sum_eq_zeroNB12
    (j := (n : ZMod q)) hj
  have hrange :
      (∑ a ∈ Finset.range q,
        rationalCosinePeriodicTermNB12 n q a) = 0 := by
    calc
      (∑ a ∈ Finset.range q,
          rationalCosinePeriodicTermNB12 n q a) =
        ∑ a ∈ Finset.range q,
          (ZMod.stdAddChar
            (((n * a : ℕ) : ZMod q))).re := by
              apply Finset.sum_congr rfl
              intro a _
              exact rationalCosinePeriodicTermNB12_eq_stdAddChar_re n q a
      _ = (∑ a ∈ Finset.range q,
          ZMod.stdAddChar ((n : ZMod q) * (a : ZMod q))).re := by
            simp_rw [Nat.cast_mul]
            rw [Complex.re_sum]
      _ = 0 := by rw [hchar]; rfl
  have hq : 0 < q := hn0.trans hnq
  have hset : Finset.range q =
      insert 0 (Finset.Ioc 0 (q - 1)) := by
    ext a
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hzeroNot : 0 ∉ Finset.Ioc 0 (q - 1) := by simp
  rw [hset, Finset.sum_insert hzeroNot] at hrange
  have hzero : rationalCosinePeriodicTermNB12 n q 0 = 1 := by
    simp [rationalCosinePeriodicTermNB12]
  rw [hzero] at hrange
  linarith

/-! ## Dirichlet-kernel evaluation -/

/-- The finite cosine kernel used in the sine--cotangent identity. -/
noncomputable def dirichletCosineKernelNB12 (m : ℕ) (x : ℝ) : ℝ :=
  1 + Real.cos (2 * (m : ℝ) * x) +
    2 * ∑ n ∈ Finset.Ico 1 m,
      Real.cos (2 * (n : ℝ) * x)

/-- Pointwise Dirichlet-kernel identity. -/
theorem sin_two_nat_mul_cot_eq_dirichletCosineKernelNB12
    (m : ℕ) (hm : 0 < m) (x : ℝ) (hx : Real.sin x ≠ 0) :
    Real.sin (2 * (m : ℝ) * x) *
        (Real.cos x / Real.sin x) =
      dirichletCosineKernelNB12 m x := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  induction n with
  | zero =>
      simp [dirichletCosineKernelNB12, Real.sin_two_mul,
        Real.cos_two_mul]
      field_simp
  | succ n ih =>
      have hsum :
          (∑ k ∈ Finset.Ico 1 (n + 2),
              Real.cos (2 * (k : ℝ) * x)) =
            (∑ k ∈ Finset.Ico 1 (n + 1),
              Real.cos (2 * (k : ℝ) * x)) +
              Real.cos (2 * ((n + 1 : ℕ) : ℝ) * x) := by
        rw [Finset.sum_Ico_succ_top (by omega)]
      have hangle :
          2 * ((n + 2 : ℕ) : ℝ) * x =
            2 * ((n + 1 : ℕ) : ℝ) * x + 2 * x := by
        push_cast
        ring
      have hstep :
          Real.sin (2 * ((n + 2 : ℕ) : ℝ) * x) *
              (Real.cos x / Real.sin x) =
            Real.sin (2 * ((n + 1 : ℕ) : ℝ) * x) *
                (Real.cos x / Real.sin x) +
              Real.cos (2 * ((n + 2 : ℕ) : ℝ) * x) +
              Real.cos (2 * ((n + 1 : ℕ) : ℝ) * x) := by
        rw [hangle, Real.sin_add, Real.cos_add,
          Real.sin_two_mul, Real.cos_two_mul]
        field_simp
        have hcosSq : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
          nlinarith [Real.sin_sq_add_cos_sq x]
        rw [hcosSq]
        ring_nf
        rw [hcosSq]
        ring
      rw [hstep, ih (Nat.succ_pos n)]
      unfold dirichletCosineKernelNB12
      rw [hsum]
      ring

/-- Summing the Dirichlet kernel over the nonzero rational grid gives the
linear sawtooth coefficient `q - 2m`. -/
theorem sum_dirichletCosineKernelNB12
    {q m : ℕ} [NeZero q] (hm0 : 0 < m) (hmq : m < q) :
    (∑ a ∈ Finset.Ioc 0 (q - 1),
      dirichletCosineKernelNB12 m
        (Real.pi * (a : ℝ) / (q : ℝ))) =
      (q : ℝ) - 2 * (m : ℝ) := by
  let S := Finset.Ioc 0 (q - 1)
  let T := Finset.Ico 1 m
  have hcardS : S.card = q - 1 := by simp [S]
  have hmain :
      (∑ a ∈ S, rationalCosinePeriodicTermNB12 m q a) = -1 :=
    sum_rationalCosinePeriodicTermNB12_eq_neg_one hm0 hmq
  have hinner :
      (∑ n ∈ T, ∑ a ∈ S,
        rationalCosinePeriodicTermNB12 n q a) =
          -((m - 1 : ℕ) : ℝ) := by
    calc
      (∑ n ∈ T, ∑ a ∈ S,
          rationalCosinePeriodicTermNB12 n q a) =
          ∑ n ∈ T, (-1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro n hn
            simp only [T, Finset.mem_Ico] at hn
            exact sum_rationalCosinePeriodicTermNB12_eq_neg_one
              hn.1 (hn.2.trans hmq)
      _ = -((m - 1 : ℕ) : ℝ) := by simp [T]
  have hcos (n a : ℕ) :
      Real.cos (2 * (n : ℝ) *
          (Real.pi * (a : ℝ) / (q : ℝ))) =
        rationalCosinePeriodicTermNB12 n q a := by
    unfold rationalCosinePeriodicTermNB12
    congr 1
    ring
  have htail :
      (∑ a ∈ Finset.Ioc 0 (q - 1),
          2 * ∑ n ∈ Finset.Ico 1 m,
            rationalCosinePeriodicTermNB12 n q a) =
        2 * (-((m - 1 : ℕ) : ℝ)) := by
    calc
      (∑ a ∈ Finset.Ioc 0 (q - 1),
          2 * ∑ n ∈ Finset.Ico 1 m,
            rationalCosinePeriodicTermNB12 n q a) =
          2 * ∑ a ∈ Finset.Ioc 0 (q - 1),
            ∑ n ∈ Finset.Ico 1 m,
              rationalCosinePeriodicTermNB12 n q a := by
                rw [Finset.mul_sum]
      _ = 2 * ∑ n ∈ Finset.Ico 1 m,
            ∑ a ∈ Finset.Ioc 0 (q - 1),
              rationalCosinePeriodicTermNB12 n q a := by
                congr 1
                exact Finset.sum_comm
      _ = 2 * (-((m - 1 : ℕ) : ℝ)) := by
            rw [show (∑ n ∈ Finset.Ico 1 m,
                ∑ a ∈ Finset.Ioc 0 (q - 1),
                  rationalCosinePeriodicTermNB12 n q a) =
                -((m - 1 : ℕ) : ℝ) by simpa [S, T] using hinner]
  simp_rw [dirichletCosineKernelNB12, hcos]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_const, nsmul_eq_mul, hcardS, hmain]
  rw [htail]
  rw [Nat.cast_sub (by omega : 1 ≤ q),
    Nat.cast_sub (by omega : 1 ≤ m)]
  norm_num
  ring

/-! ## Exact rational Fourier mode -/

/-- The value of one rational sine--cotangent Fourier mode. -/
noncomputable def rationalCotangentFourierMode
    (h k m : ℕ) : ℝ :=
  let r := (m * h) % k
  if r = 0 then 0 else (k : ℝ) - 2 * (r : ℝ)

/-- The complete rational sine--cotangent transform. -/
theorem sum_sine_mul_cotangentTerm_eq_mode
    (h k m : ℕ) (hk : 0 < k) :
    (∑ a ∈ Finset.Ico 1 k,
      Real.sin
          (2 * Real.pi * (m : ℝ) *
            (((a * h : ℕ) : ℝ) / (k : ℝ))) *
        cotangentTerm a k) =
      rationalCotangentFourierMode h k m := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hset : Finset.Ico 1 k = Finset.Ioc 0 (k - 1) := by
    ext a
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [hset]
  unfold rationalCotangentFourierMode
  let r := (m * h) % k
  have hrk : r < k := Nat.mod_lt _ hk
  by_cases hr0 : r = 0
  · rw [if_pos hr0]
    subst r
    apply Finset.sum_eq_zero
    intro a _
    have hdiv : k ∣ m * h := Nat.dvd_of_mod_eq_zero hr0
    obtain ⟨c, hc⟩ := hdiv
    have harg :
        2 * Real.pi * (m : ℝ) *
            (((a * h : ℕ) : ℝ) / (k : ℝ)) =
          ((2 * c * a : ℕ) : ℝ) * Real.pi := by
      calc
        2 * Real.pi * (m : ℝ) *
              (((a * h : ℕ) : ℝ) / (k : ℝ)) =
            2 * Real.pi * ((m * h : ℕ) : ℝ) * (a : ℝ) /
              (k : ℝ) := by
                push_cast
                ring
        _ = ((2 * c * a : ℕ) : ℝ) * Real.pi := by
              rw [hc]
              push_cast
              field_simp
    rw [harg, Real.sin_nat_mul_pi, zero_mul]
  · rw [if_neg hr0]
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hpoint : ∀ a : ℕ,
        Real.sin
            (2 * Real.pi * (m : ℝ) *
              (((a * h : ℕ) : ℝ) / (k : ℝ))) =
          Real.sin
            (2 * (r : ℝ) *
              (Real.pi * (a : ℝ) / (k : ℝ))) := by
      intro a
      have hmod : m * h = k * ((m * h) / k) + r := by
        calc
          m * h = (m * h) % k + k * ((m * h) / k) :=
            (Nat.mod_add_div (m * h) k).symm
          _ = k * ((m * h) / k) + r := by
            simp [r, add_comm]
      rw [show 2 * Real.pi * (m : ℝ) *
            (((a * h : ℕ) : ℝ) / (k : ℝ)) =
          2 * Real.pi * ((m * h : ℕ) : ℝ) * (a : ℝ) / (k : ℝ) by
            push_cast; ring]
      rw [hmod]
      push_cast
      rw [show 2 * Real.pi *
            ((k : ℝ) * (((m * h) / k : ℕ) : ℝ) + (r : ℝ)) *
              (a : ℝ) / (k : ℝ) =
          2 * (r : ℝ) * (Real.pi * (a : ℝ) / (k : ℝ)) +
            ((((m * h) / k) * a : ℕ) : ℝ) * (2 * Real.pi) by
              field_simp
              push_cast
              ring]
      rw [Real.sin_add_nat_mul_two_pi]
    simp_rw [hpoint]
    have hqR : (0 : ℝ) < k := by exact_mod_cast hk
    have hterm : ∀ a ∈ Finset.Ioc 0 (k - 1),
        Real.sin
              (2 * (r : ℝ) *
                (Real.pi * (a : ℝ) / (k : ℝ))) *
            cotangentTerm a k =
          dirichletCosineKernelNB12 r
            (Real.pi * (a : ℝ) / (k : ℝ)) := by
      intro a ha
      simp only [Finset.mem_Ioc] at ha
      have ha0 : 0 < a := ha.1
      have hak : a < k := by omega
      have hx0 : 0 < Real.pi * (a : ℝ) / (k : ℝ) := by positivity
      have hxpi : Real.pi * (a : ℝ) / (k : ℝ) < Real.pi := by
        rw [div_lt_iff₀ hqR]
        exact mul_lt_mul_of_pos_left (by exact_mod_cast hak) Real.pi_pos
      have hxsin : Real.sin (Real.pi * (a : ℝ) / (k : ℝ)) ≠ 0 :=
        ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx0 hxpi)
      exact sin_two_nat_mul_cot_eq_dirichletCosineKernelNB12
        r hrpos (Real.pi * (a : ℝ) / (k : ℝ)) hxsin
    calc
      (∑ a ∈ Finset.Ioc 0 (k - 1),
          Real.sin
              (2 * (r : ℝ) *
                (Real.pi * (a : ℝ) / (k : ℝ))) *
            cotangentTerm a k) =
          ∑ a ∈ Finset.Ioc 0 (k - 1),
            dirichletCosineKernelNB12 r
              (Real.pi * (a : ℝ) / (k : ℝ)) := by
                apply Finset.sum_congr rfl
                exact hterm
      _ = (k : ℝ) - 2 * (r : ℝ) :=
        sum_dirichletCosineKernelNB12 hrpos hrk

/-! ## Identification with the BBLS rational harmonic series -/

/-- One rational sine--cotangent mode is `-2k` times the matching Dedekind
sawtooth value. -/
theorem rationalCotangentFourierMode_eq_bernoulliB1
    (h k m : ℕ) (hk : 0 < k) :
    rationalCotangentFourierMode h k m =
      -2 * (k : ℝ) *
        bernoulliB1 ((m : ℝ) * ((h : ℝ) / (k : ℝ))) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have harg :
      (m : ℝ) * ((h : ℝ) / (k : ℝ)) =
        ((m * h : ℕ) : ℝ) / (k : ℝ) := by
    push_cast
    ring
  rw [harg]
  unfold rationalCotangentFourierMode bernoulliB1
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  by_cases hr0 : (m * h) % k = 0
  · rw [if_pos hr0]
    simp [hr0]
  · rw [if_neg hr0]
    have hfract :
        (((m * h) % k : ℕ) : ℝ) / (k : ℝ) ≠ 0 := by
      exact div_ne_zero (by exact_mod_cast hr0) hkR
    rw [if_neg hfract]
    field_simp
    ring

/-- The BBLS partial rational harmonic series, rescaled to the Vasyunin-row
normalization. -/
noncomputable def bblsCotangentRowPartial
    (h k M : ℕ) : ℝ :=
  (2 * (k : ℝ) / Real.pi) *
    ∑ m ∈ Finset.Icc 1 M,
      bernoulliB1 ((m : ℝ) * ((h : ℝ) / (k : ℝ))) / (m : ℝ)

/-- The finite NB12 sine polynomial is exactly the corresponding BBLS
rational harmonic partial sum after applying the finite cotangent transform. -/
theorem vasyuninFourierLowRow_eq_bblsCotangentRowPartial
    (h k M : ℕ) (hk : 0 < k) :
    vasyuninFourierLowRow h k M =
      bblsCotangentRowPartial h k M := by
  classical
  have hcot : (∑ a ∈ Finset.Ico 1 k, cotangentTerm a k) = 0 := by
    have hjump := rationalJumpCotangentSum_eq_zero 0 k hk
    simpa [rationalJumpCotangentSum] using hjump
  have hswap :
      (∑ a ∈ Finset.Ico 1 k,
          fourierSawtoothApprox M
              (((a * h : ℕ) : ℝ) / (k : ℝ)) *
            cotangentTerm a k) =
        ∑ m ∈ Finset.Icc 1 M,
          -(1 / (Real.pi * (m : ℝ))) *
            rationalCotangentFourierMode h k m := by
    unfold fourierSawtoothApprox
    calc
      (∑ a ∈ Finset.Ico 1 k,
          (∑ m ∈ Finset.Icc 1 M,
            -(Real.sin
                (2 * Real.pi * (m : ℝ) *
                  (((a * h : ℕ) : ℝ) / (k : ℝ))) /
                (Real.pi * (m : ℝ)))) *
            cotangentTerm a k) =
        ∑ m ∈ Finset.Icc 1 M,
          ∑ a ∈ Finset.Ico 1 k,
            -(Real.sin
                (2 * Real.pi * (m : ℝ) *
                  (((a * h : ℕ) : ℝ) / (k : ℝ))) /
                (Real.pi * (m : ℝ))) *
              cotangentTerm a k := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro m _
                rw [Finset.sum_mul]
      _ = ∑ m ∈ Finset.Icc 1 M,
          -(1 / (Real.pi * (m : ℝ))) *
            rationalCotangentFourierMode h k m := by
            apply Finset.sum_congr rfl
            intro m _
            rw [← sum_sine_mul_cotangentTerm_eq_mode h k m hk]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
  unfold vasyuninFourierLowRow fourierFractApprox
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hconst :
      (∑ a ∈ Finset.Ico 1 k,
        (1 / 2 : ℝ) * cotangentTerm a k) = 0 := by
    rw [← Finset.mul_sum, hcot, mul_zero]
  rw [hconst, zero_add, hswap]
  unfold bblsCotangentRowPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_Icc] at hm
  rw [rationalCotangentFourierMode_eq_bernoulliB1 h k m hk]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm.1)
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

/-- For every fixed positive rational row, the finite NB12 Fourier row
converges to the exact Vasyunin cotangent row. -/
theorem tendsto_vasyuninFourierLowRow_fixed
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    Tendsto (fun M : ℕ => vasyuninFourierLowRow h k M)
      atTop (nhds (vasyuninCotangentSum h k)) := by
  have hseries := tendsto_bernoulliB1_sum_div_rat h k hh hk
  have hscaled :=
    (tendsto_const_nhds (x := 2 * (k : ℝ) / Real.pi)).mul hseries
  have hlimit :
      (2 * (k : ℝ) / Real.pi) *
          (Real.pi / (2 * (k : ℝ)) * cotangentSumVFormula h k) =
        vasyuninCotangentSum h k := by
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    unfold vasyuninCotangentSum cotangentSumVFormula
      cotangentTerm cotangentTermV
    field_simp
  rw [hlimit] at hscaled
  exact hscaled.congr' (Eventually.of_forall fun M =>
    (vasyuninFourierLowRow_eq_bblsCotangentRowPartial h k M hk).symm)

/-- For every fixed positive rational row, the exact NB12 Fourier remainder
tends to zero.  The unresolved H15 step is uniform control after the row
indices and Möbius-weighted bilinear aggregate move with `N`. -/
theorem tendsto_vasyuninFourierRemainderRow_fixed
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    Tendsto (fun M : ℕ => vasyuninFourierRemainderRow h k M)
      atTop (nhds 0) := by
  have hlow := tendsto_vasyuninFourierLowRow_fixed h k hh hk
  have hsub : Tendsto
      (fun M : ℕ =>
        vasyuninCotangentSum h k - vasyuninFourierLowRow h k M)
      atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds (x := vasyuninCotangentSum h k)).sub hlow
  refine hsub.congr' (Eventually.of_forall fun M => ?_)
  have hsplit := vasyuninCotangentSum_eq_fourierLow_add_remainder h k M
  linarith

/-! ## Exact aggregate BBLS-tail target -/

/-- The exact tail of the rescaled BBLS rational harmonic series in one
Vasyunin row. -/
noncomputable def bblsCotangentRowTail
    (h k M : ℕ) : ℝ :=
  vasyuninCotangentSum h k - bblsCotangentRowPartial h k M

/-- The NB12 pointwise Fourier remainder row is exactly the BBLS rational
harmonic tail. -/
theorem vasyuninFourierRemainderRow_eq_bblsCotangentRowTail
    (h k M : ℕ) (hk : 0 < k) :
    vasyuninFourierRemainderRow h k M =
      bblsCotangentRowTail h k M := by
  rw [bblsCotangentRowTail,
    ← vasyuninFourierLowRow_eq_bblsCotangentRowPartial h k M hk]
  have hsplit := vasyuninCotangentSum_eq_fourierLow_add_remainder h k M
  linarith

/-- The complete signed Möbius-weighted BBLS tail in the normalization of
`vaalerHighModeTail`. -/
noncomputable def bblsCotangentBilinearTail
    (N : ℕ) (coeffs : Fin N → ℝ) (M : ℕ) : ℝ :=
  ∑ j : Fin N, ∑ k : Fin N,
    coeffs j * coeffs k *
      (-Real.pi /
          (2 * ((j.val + 1 : ℕ) : ℝ) * ((k.val + 1 : ℕ) : ℝ)) *
        (bblsCotangentRowTail (j.val + 1) (k.val + 1) M +
          bblsCotangentRowTail (k.val + 1) (j.val + 1) M))

/-- Exact global rewrite of the active Fourier high-mode tail as the complete
signed bilinear aggregate of BBLS periodic harmonic tails. -/
theorem vaalerHighModeTail_eq_bblsCotangentBilinearTail
    (N : ℕ) (coeffs : Fin N → ℝ) (M : ℕ) :
    vaalerHighModeTail N coeffs M =
      bblsCotangentBilinearTail N coeffs M := by
  classical
  unfold vaalerHighModeTail bblsCotangentBilinearTail
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [vasyuninFourierRemainderRow_eq_bblsCotangentRowTail
      (j.val + 1) (k.val + 1) M (Nat.succ_pos _),
    vasyuninFourierRemainderRow_eq_bblsCotangentRowTail
      (k.val + 1) (j.val + 1) M (Nat.succ_pos _)]

/-- A log-power estimate stated directly on the exact BBLS periodic-tail
aggregate.  This is the sharp replacement for the unsupported continuous
Fejér-to-discrete-cotangent transfer in the dataset note. -/
structure BBLSBilinearTailLogEstimate where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ n : ℕ,
    |bblsCotangentBilinearTail
        (logTaperLength n) (logTaperCoeffs n) (vaalerModeCutoff n)| ≤
      C / (Real.log (((n + 2 : ℕ) : ℝ))) ^ α

/-- The BBLS periodic-tail estimate supplies the exact quantitative Fourier
remainder interface. -/
noncomputable def BBLSBilinearTailLogEstimate.toFourierRemainderLogEstimate
    (H : BBLSBilinearTailLogEstimate) :
    FourierRemainderLogEstimate where
  C := H.C
  C_pos := H.C_pos
  α := H.α
  α_pos := H.α_pos
  bound n := by
    rw [vaalerHighModeTail_eq_bblsCotangentBilinearTail]
    exact H.bound n

/-- A log-power bound for the signed BBLS rational harmonic tail proves the
active `FourierRemainderDecay` target. -/
theorem fourierRemainderDecay_of_bblsBilinearTailLogEstimate
    (H : BBLSBilinearTailLogEstimate) :
    FourierRemainderDecay :=
  fourierRemainderDecay_of_logEstimate H.toFourierRemainderLogEstimate

end NBMellinTools.NB12
