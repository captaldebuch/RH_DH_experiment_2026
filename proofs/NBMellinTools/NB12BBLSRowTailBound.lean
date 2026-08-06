/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12RationalSineCotangent

/-!
# NB12b: a quantitative BBLS row-tail bound

The BBLS rational harmonic theorem gives convergence for every fixed rational
row.  This file makes the elementary Dirichlet/Abel remainder quantitative.

For a `q`-periodic mean-zero sequence `g`, if

`B = ∑_{1 ≤ r ≤ q} |g r|`,

then the error after `M` terms is at most `2 B / (M + 1)`.  For the Dedekind
sawtooth this gives `q / (M + 1)` before Vasyunin rescaling and
`2 q^2 / (π (M + 1))` for one complete cotangent row.

This is deliberately weaker than the open bilinear estimate.  In particular,
it shows why a claimed uniform `O(log q / M)` row bound cannot be obtained from
the BBLS periodic partial-sum argument: its natural modulus cost is linear
before, and quadratic after, row rescaling.
-/

open Filter
open scoped BigOperators Topology

namespace NBMellinTools.NB12

open NBMellinTools.NB10
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## Finite Abel inequality on a positive natural interval -/

private theorem finiteAbelFrom
    (a b : ℕ → ℝ) (A B : ℕ) (hAB : A ≤ B) :
    (∑ k ∈ Finset.Icc A B, a k * b k) =
      (∑ j ∈ Finset.Icc A B, a j) * b (B + 1) +
        ∑ k ∈ Finset.Icc A B,
          (∑ j ∈ Finset.Icc A k, a j) * (b k - b (k + 1)) := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp
      ring
  | succ B hAB ih =>
      have hAB' : A ≤ B + 1 := by omega
      rw [Finset.sum_Icc_succ_top hAB', Finset.sum_Icc_succ_top hAB',
        Finset.sum_Icc_succ_top hAB']
      rw [ih]
      rw [Finset.sum_Icc_succ_top hAB']
      ring

private theorem sumSubSuccAddEndpoint
    (b : ℕ → ℝ) (A B : ℕ) (hAB : A ≤ B) :
    b (B + 1) + ∑ k ∈ Finset.Icc A B, (b k - b (k + 1)) = b A := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp
  | succ B hAB ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      linarith

/-- Dirichlet's finite remainder inequality for the harmonic weight on a
positive natural interval. -/
private theorem absSumIccDivLeOfPartialSumLe
    (a : ℕ → ℝ) (A B : ℕ) (D : ℝ)
    (hA : 0 < A) (hAB : A ≤ B)
    (hpartial : ∀ k ∈ Finset.Icc A B,
      |∑ j ∈ Finset.Icc A k, a j| ≤ D) :
    |∑ k ∈ Finset.Icc A B, a k / (k : ℝ)| ≤ D / (A : ℝ) := by
  let w : ℕ → ℝ := fun k => 1 / (k : ℝ)
  have hw_nonneg : ∀ k ∈ Finset.Icc A (B + 1), 0 ≤ w k := by
    intro k hk
    have hkpos : 0 < k := hA.trans_le (Finset.mem_Icc.mp hk).1
    unfold w
    positivity
  have hw_antitone : ∀ k ∈ Finset.Icc A B, w (k + 1) ≤ w k := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by
      exact_mod_cast hA.trans_le (Finset.mem_Icc.mp hk).1
    unfold w
    exact one_div_le_one_div_of_le hkpos (by norm_num)
  have hdiff_nonneg : ∀ k ∈ Finset.Icc A B, 0 ≤ w k - w (k + 1) := by
    intro k hk
    exact sub_nonneg.mpr (hw_antitone k hk)
  have hBmem : B ∈ Finset.Icc A B := Finset.mem_Icc.mpr ⟨hAB, le_rfl⟩
  have hB1mem : B + 1 ∈ Finset.Icc A (B + 1) :=
    Finset.mem_Icc.mpr ⟨hAB.trans (by omega), le_rfl⟩
  have hrewrite :
      (∑ k ∈ Finset.Icc A B, a k / (k : ℝ)) =
        ∑ k ∈ Finset.Icc A B, a k * w k := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [w, div_eq_mul_inv]
    ring
  rw [hrewrite, finiteAbelFrom a w A B hAB]
  calc
    |(∑ j ∈ Finset.Icc A B, a j) * w (B + 1) +
        ∑ k ∈ Finset.Icc A B,
          (∑ j ∈ Finset.Icc A k, a j) * (w k - w (k + 1))| ≤
        |(∑ j ∈ Finset.Icc A B, a j) * w (B + 1)| +
          |∑ k ∈ Finset.Icc A B,
            (∑ j ∈ Finset.Icc A k, a j) * (w k - w (k + 1))| :=
      abs_add_le _ _
    _ ≤ D * w (B + 1) +
        ∑ k ∈ Finset.Icc A B, D * (w k - w (k + 1)) := by
      gcongr
      · rw [abs_mul, abs_of_nonneg (hw_nonneg _ hB1mem)]
        exact mul_le_mul_of_nonneg_right (hpartial B hBmem)
          (hw_nonneg _ hB1mem)
      · calc
          |∑ k ∈ Finset.Icc A B,
              (∑ j ∈ Finset.Icc A k, a j) * (w k - w (k + 1))| ≤
              ∑ k ∈ Finset.Icc A B,
                |(∑ j ∈ Finset.Icc A k, a j) * (w k - w (k + 1))| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.Icc A B,
              D * (w k - w (k + 1)) := by
            apply Finset.sum_le_sum
            intro k hk
            rw [abs_mul, abs_of_nonneg (hdiff_nonneg k hk)]
            exact mul_le_mul_of_nonneg_right (hpartial k hk)
              (hdiff_nonneg k hk)
    _ = D * w A := by
      rw [← Finset.mul_sum, ← mul_add,
        sumSubSuccAddEndpoint w A B hAB]
    _ = D / (A : ℝ) := by
      simp only [w, div_eq_mul_inv]
      ring

/-! ## Quantitative periodic harmonic remainder -/

/-- The BBLS periodic mean-zero convergence theorem with its elementary
quantitative remainder. -/
theorem bblsPeriodicSumDivErrorLe
    (g : ℕ → ℝ) (q M : ℕ) (hq : 0 < q)
    (hper : ∀ k, g (k + q) = g k)
    (hmean : (∑ r ∈ Finset.Ioc 0 q, g r) = 0) :
    |(1 / (q : ℝ)) *
          ∑ r ∈ Finset.Ioc 0 q,
            g r * bblsDigammaShift ((r : ℝ) / q) -
        ∑ k ∈ Finset.Icc 1 M, g k / (k : ℝ)| ≤
      2 * (∑ r ∈ Finset.Ioc 0 q, |g r|) / ((M + 1 : ℕ) : ℝ) := by
  let S : ℕ → ℝ := fun R => ∑ k ∈ Finset.Icc 1 R, g k / (k : ℝ)
  let L : ℝ := (1 / (q : ℝ)) *
    ∑ r ∈ Finset.Ioc 0 q,
      g r * bblsDigammaShift ((r : ℝ) / q)
  let B : ℝ := ∑ r ∈ Finset.Ioc 0 q, |g r|
  have hglobal : ∀ k : ℕ,
      |∑ j ∈ Finset.Icc 1 k, g j| ≤ B := by
    intro k
    have hIccIoc : Finset.Icc 1 k = Finset.Ioc 0 k := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hIccIoc]
    exact bbls_partial_sum_bounded g q hq hper hmean k
  have hlimit : Tendsto S atTop (nhds L) := by
    exact bbls_tendsto_sum_div_of_periodic_meanzero g q hq hper hmean
  have habsLimit : Tendsto (fun R => |S R - S M|) atTop (nhds |L - S M|) :=
    (hlimit.sub_const (S M)).abs
  apply le_of_tendsto habsLimit
  filter_upwards [eventually_ge_atTop (M + 1)] with R hMR
  have hMleR : M ≤ R := by omega
  have hsplit (f : ℕ → ℝ) (K : ℕ) (hMK : M ≤ K) :
      (∑ k ∈ Finset.Icc 1 K, f k) - (∑ k ∈ Finset.Icc 1 M, f k) =
        ∑ k ∈ Finset.Icc (M + 1) K, f k := by
    have hIccIoc (K : ℕ) : Finset.Icc 1 K = Finset.Ioc 0 K := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have htail : Finset.Ioc M K = Finset.Icc (M + 1) K := by
      ext j
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    have hconsecutive := Finset.sum_Ioc_consecutive f (Nat.zero_le M) hMK
    rw [← hIccIoc K, ← hIccIoc M, htail] at hconsecutive
    linarith
  have hlocal : ∀ k ∈ Finset.Icc (M + 1) R,
      |∑ j ∈ Finset.Icc (M + 1) k, g j| ≤ 2 * B := by
    intro k hk
    have hMk : M ≤ k := Nat.le_of_succ_le (Finset.mem_Icc.mp hk).1
    have hlocsplit := hsplit g k hMk
    calc
      |∑ j ∈ Finset.Icc (M + 1) k, g j| =
          |(∑ j ∈ Finset.Icc 1 k, g j) -
            ∑ j ∈ Finset.Icc 1 M, g j| := by rw [← hlocsplit]
      _ ≤ |∑ j ∈ Finset.Icc 1 k, g j| +
          |∑ j ∈ Finset.Icc 1 M, g j| := abs_sub _ _
      _ ≤ B + B := add_le_add (hglobal k) (hglobal M)
      _ = 2 * B := by ring
  have htailBound := absSumIccDivLeOfPartialSumLe
    g (M + 1) R (2 * B) (by omega) hMR hlocal
  have hSM : S R - S M =
      ∑ k ∈ Finset.Icc (M + 1) R, g k / (k : ℝ) := by
    exact hsplit (fun k => g k / (k : ℝ)) R hMleR
  rw [hSM]
  simpa [Nat.cast_add, S, L, B] using htailBound

/-! ## Dedekind-sawtooth and Vasyunin-row specialization -/

/-- The Dedekind first Bernoulli function has absolute value at most `1/2`. -/
theorem absBernoulliB1LeHalf (x : ℝ) : |bernoulliB1 x| ≤ 1 / 2 := by
  unfold bernoulliB1
  by_cases hx : Int.fract x = 0
  · simp [hx]
  · rw [if_neg hx]
    rw [abs_le]
    constructor <;> linarith [Int.fract_nonneg x, Int.fract_lt_one x]

/-- The absolute mass of one complete rational Bernoulli period is at most
`q/2`. -/
theorem bernoulliB1RatPeriodMassLe (p q : ℕ) :
    (∑ r ∈ Finset.Ioc 0 q,
      |bernoulliB1 ((r : ℝ) * ((p : ℝ) / q))|) ≤ (q : ℝ) / 2 := by
  calc
    (∑ r ∈ Finset.Ioc 0 q,
      |bernoulliB1 ((r : ℝ) * ((p : ℝ) / q))|) ≤
        ∑ _r ∈ Finset.Ioc 0 q, (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      exact absBernoulliB1LeHalf _
    _ = (q : ℝ) / 2 := by
      simp
      ring_nf

/-- Correct modulus-dependent quantitative form of the BBLS rational harmonic
remainder. -/
theorem bernoulliB1SumDivRatErrorLe
    (p q M : ℕ) (hp : 0 < p) (hq : 0 < q) :
    |Real.pi / (2 * q) * cotangentSumVFormula p q -
        ∑ k ∈ Finset.Icc 1 M,
          bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) / (k : ℝ)| ≤
      (q : ℝ) / ((M + 1 : ℕ) : ℝ) := by
  have h := bblsPeriodicSumDivErrorLe
    (fun k : ℕ => bernoulliB1 ((k : ℝ) * ((p : ℝ) / q))) q M hq
    (fun k => bernoulliB1_rat_periodic p q hq k)
    (bernoulliB1_rat_meanzero p q hp hq)
  rw [bbls_phi1_value p q hp hq] at h
  calc
    |Real.pi / (2 * q) * cotangentSumVFormula p q -
        ∑ k ∈ Finset.Icc 1 M,
          bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) / (k : ℝ)| ≤
        2 * (∑ r ∈ Finset.Ioc 0 q,
          |bernoulliB1 ((r : ℝ) * ((p : ℝ) / q))|) /
            ((M + 1 : ℕ) : ℝ) := h
    _ ≤ 2 * ((q : ℝ) / 2) / ((M + 1 : ℕ) : ℝ) := by
      gcongr
      exact bernoulliB1RatPeriodMassLe p q
    _ = (q : ℝ) / ((M + 1 : ℕ) : ℝ) := by ring

/-- One complete Vasyunin row has the unconditional quantitative bound
`2 q^2 / (π (M+1))`. -/
theorem absBblsCotangentRowTailLe
    (p q M : ℕ) (hp : 0 < p) (hq : 0 < q) :
    |bblsCotangentRowTail p q M| ≤
      2 * (q : ℝ) ^ 2 / (Real.pi * ((M + 1 : ℕ) : ℝ)) := by
  have hraw := bernoulliB1SumDivRatErrorLe p q M hp hq
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hrow : bblsCotangentRowTail p q M =
      (2 * (q : ℝ) / Real.pi) *
        (Real.pi / (2 * q) * cotangentSumVFormula p q -
          ∑ k ∈ Finset.Icc 1 M,
            bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) / (k : ℝ)) := by
    have hv : vasyuninCotangentSum p q = cotangentSumVFormula p q := by rfl
    unfold bblsCotangentRowTail bblsCotangentRowPartial
    rw [hv]
    let P : ℝ := ∑ k ∈ Finset.Icc 1 M,
      bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) / (k : ℝ)
    change cotangentSumVFormula p q - (2 * (q : ℝ) / Real.pi) * P =
      (2 * (q : ℝ) / Real.pi) *
        (Real.pi / (2 * q) * cotangentSumVFormula p q - P)
    have hmain :
        (2 * (q : ℝ) / Real.pi) *
            (Real.pi / (2 * q) * cotangentSumVFormula p q) =
          cotangentSumVFormula p q := by
      field_simp [hqR, hpi]
    calc
      cotangentSumVFormula p q - (2 * (q : ℝ) / Real.pi) * P =
          (2 * (q : ℝ) / Real.pi) *
              (Real.pi / (2 * q) * cotangentSumVFormula p q) -
            (2 * (q : ℝ) / Real.pi) * P := by rw [hmain]
      _ = (2 * (q : ℝ) / Real.pi) *
          (Real.pi / (2 * q) * cotangentSumVFormula p q - P) := by ring
  rw [hrow, abs_mul, abs_of_pos (div_pos (by positivity) Real.pi_pos)]
  calc
    (2 * (q : ℝ) / Real.pi) *
        |Real.pi / (2 * q) * cotangentSumVFormula p q -
          ∑ k ∈ Finset.Icc 1 M,
            bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) / (k : ℝ)| ≤
        (2 * (q : ℝ) / Real.pi) *
          ((q : ℝ) / ((M + 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hraw (div_nonneg (by positivity) Real.pi_pos.le)
    _ = 2 * (q : ℝ) ^ 2 /
        (Real.pi * ((M + 1 : ℕ) : ℝ)) := by ring

/-! ## What the pointwise lift actually supplies -/

/-- The explicit majorant obtained by inserting the quantitative fixed-row
bound term by term into the complete signed bilinear tail.  Its moving-modulus
factors make clear that this is not the desired log-power estimate. -/
noncomputable def bblsCotangentBilinearAbsoluteMajorant
    (N : ℕ) (coeffs : Fin N → ℝ) (M : ℕ) : ℝ :=
  ∑ j : Fin N, ∑ k : Fin N,
    |coeffs j * coeffs k| *
      ((((k.val + 1 : ℕ) : ℝ) / ((j.val + 1 : ℕ) : ℝ) +
          ((j.val + 1 : ℕ) : ℝ) / ((k.val + 1 : ℕ) : ℝ)) /
        ((M + 1 : ℕ) : ℝ))

/-- Absolute lifting of the fixed-row BBLS estimate.  This theorem is
unconditional, but it deliberately takes absolute values and therefore does
not prove `BBLSBilinearTailLogEstimate`. -/
theorem absBblsCotangentBilinearTailLeAbsoluteMajorant
    (N : ℕ) (coeffs : Fin N → ℝ) (M : ℕ) :
    |bblsCotangentBilinearTail N coeffs M| ≤
      bblsCotangentBilinearAbsoluteMajorant N coeffs M := by
  classical
  unfold bblsCotangentBilinearTail
    bblsCotangentBilinearAbsoluteMajorant
  calc
    |∑ j : Fin N, ∑ k : Fin N,
        coeffs j * coeffs k *
          (-Real.pi /
              (2 * ((j.val + 1 : ℕ) : ℝ) * ((k.val + 1 : ℕ) : ℝ)) *
            (bblsCotangentRowTail (j.val + 1) (k.val + 1) M +
              bblsCotangentRowTail (k.val + 1) (j.val + 1) M))| ≤
        ∑ j : Fin N, |∑ k : Fin N,
          coeffs j * coeffs k *
            (-Real.pi /
                (2 * ((j.val + 1 : ℕ) : ℝ) * ((k.val + 1 : ℕ) : ℝ)) *
              (bblsCotangentRowTail (j.val + 1) (k.val + 1) M +
                bblsCotangentRowTail (k.val + 1) (j.val + 1) M))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin N, ∑ k : Fin N,
        |coeffs j * coeffs k *
          (-Real.pi /
              (2 * ((j.val + 1 : ℕ) : ℝ) * ((k.val + 1 : ℕ) : ℝ)) *
            (bblsCotangentRowTail (j.val + 1) (k.val + 1) M +
              bblsCotangentRowTail (k.val + 1) (j.val + 1) M))| := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin N, ∑ k : Fin N,
        |coeffs j * coeffs k| *
          ((((k.val + 1 : ℕ) : ℝ) / ((j.val + 1 : ℕ) : ℝ) +
              ((j.val + 1 : ℕ) : ℝ) / ((k.val + 1 : ℕ) : ℝ)) /
            ((M + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      let J : ℝ := ((j.val + 1 : ℕ) : ℝ)
      let K : ℝ := ((k.val + 1 : ℕ) : ℝ)
      let A : ℝ := ((M + 1 : ℕ) : ℝ)
      have hJ : 0 < J := by unfold J; positivity
      have hK : 0 < K := by unfold K; positivity
      have hA : 0 < A := by unfold A; positivity
      have hjk := absBblsCotangentRowTailLe
        (j.val + 1) (k.val + 1) M (Nat.succ_pos _) (Nat.succ_pos _)
      have hkj := absBblsCotangentRowTailLe
        (k.val + 1) (j.val + 1) M (Nat.succ_pos _) (Nat.succ_pos _)
      have hsum :
          |bblsCotangentRowTail (j.val + 1) (k.val + 1) M +
              bblsCotangentRowTail (k.val + 1) (j.val + 1) M| ≤
            2 * K ^ 2 / (Real.pi * A) +
              2 * J ^ 2 / (Real.pi * A) := by
        calc
          |bblsCotangentRowTail (j.val + 1) (k.val + 1) M +
              bblsCotangentRowTail (k.val + 1) (j.val + 1) M| ≤
              |bblsCotangentRowTail (j.val + 1) (k.val + 1) M| +
                |bblsCotangentRowTail (k.val + 1) (j.val + 1) M| :=
            abs_add_le _ _
          _ ≤ 2 * K ^ 2 / (Real.pi * A) +
              2 * J ^ 2 / (Real.pi * A) := by
            simpa [J, K, A] using add_le_add hjk hkj
      have hweight :
          0 ≤ Real.pi / (2 * J * K) := by positivity
      have habsWeight :
          |-Real.pi / (2 * J * K)| = Real.pi / (2 * J * K) := by
        rw [abs_div, abs_neg, abs_of_pos Real.pi_pos,
          abs_of_pos (by positivity : 0 < 2 * J * K)]
      calc
        |coeffs j * coeffs k *
            (-Real.pi / (2 * J * K) *
              (bblsCotangentRowTail (j.val + 1) (k.val + 1) M +
                bblsCotangentRowTail (k.val + 1) (j.val + 1) M))| =
            |coeffs j * coeffs k| *
              (Real.pi / (2 * J * K)) *
              |bblsCotangentRowTail (j.val + 1) (k.val + 1) M +
                bblsCotangentRowTail (k.val + 1) (j.val + 1) M| := by
          simp only [abs_mul, habsWeight]
          ring
        _ ≤ |coeffs j * coeffs k| *
              (Real.pi / (2 * J * K)) *
              (2 * K ^ 2 / (Real.pi * A) +
                2 * J ^ 2 / (Real.pi * A)) := by
          exact mul_le_mul_of_nonneg_left hsum
            (mul_nonneg (abs_nonneg _) hweight)
        _ = |coeffs j * coeffs k| * ((K / J + J / K) / A) := by
          have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
          field_simp [hJ.ne', hK.ne', hA.ne', hpi]

end NBMellinTools.NB12
