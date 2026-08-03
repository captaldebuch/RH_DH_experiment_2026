import RiemannHypothesis.Criteria.NymanBeurling.H14ZetaEM

/-!
# A2: transporting vertical growth to the left strip

Slice A2a: the elementary series bound `‖ζ(s)‖ ≤ 9` for `Re s ≥ 9/8`,
via termwise norms and the sum–integral comparison.
-/

namespace RH.Criteria.NymanBeurling.H14ZetaFETransport

open Complex MeasureTheory Set Filter Topology intervalIntegral

/-- Sum–integral comparison for the `9/8`-series: partial sums stay below 9. -/
theorem sum_range_rpow_nine_eighths_le (N : ℕ) :
    (∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ))) ≤ 9 := by
  induction N with
  | zero => simp
  | succ M _ =>
    clear ‹_›
    have hanti : AntitoneOn (fun u : ℝ => u ^ (-(9 / 8 : ℝ)))
        (Icc (1 : ℝ) (1 + M)) := by
      intro u hu v hv huv
      have h1 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu.1
      have h2 : (0 : ℝ) < v := lt_of_lt_of_le h1 huv
      simp only
      rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le, ← one_div, ← one_div]
      apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos h1 _)
      exact Real.rpow_le_rpow h1.le huv (by norm_num)
    have hcomp := hanti.sum_le_integral (x₀ := (1 : ℝ)) (a := M)
    have hint : (∫ x in (1 : ℝ)..(1 + M : ℝ), x ^ (-(9 / 8 : ℝ))) ≤ 8 := by
      have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + M : ℝ) := by
        rw [Set.uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg M))]
        intro h
        exact absurd h.1 (by norm_num)
      rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
      have hpow : (0 : ℝ) < (1 + (M : ℝ)) ^ (-(9 / 8 : ℝ) + 1) := by
        apply Real.rpow_pos_of_pos
        positivity
      rw [Real.one_rpow]
      rw [show (-(9 / 8 : ℝ) + 1) = -(1 / 8 : ℝ) from by norm_num] at hpow ⊢
      have : ((1 + (M : ℝ)) ^ (-(1 / 8 : ℝ)) - 1) / (-(1 / 8 : ℝ)) =
          8 * (1 - (1 + (M : ℝ)) ^ (-(1 / 8 : ℝ))) := by ring
      rw [this]
      nlinarith [hpow]
    rw [Finset.sum_range_succ']
    have hzero : ((0 + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ)) = 1 := by
      norm_num
    rw [hzero]
    have hmatch : (∑ i ∈ Finset.range M, ((i + 1 + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ))) =
        ∑ i ∈ Finset.range M, (fun u : ℝ => u ^ (-(9 / 8 : ℝ))) ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      push_cast
      ring
    rw [hmatch]
    linarith [le_trans hcomp hint]

/-- A2a: the elementary zeta bound on `Re s ≥ 9/8`. -/
theorem norm_riemannZeta_le_of_re_ge {s : ℂ} (hs : (9 / 8 : ℝ) ≤ s.re) :
    ‖riemannZeta s‖ ≤ 9 := by
  have hs1 : 1 < s.re := lt_of_lt_of_le (by norm_num) hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1]
  have hnorm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ s‖ ≤
      ((n + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ)) := by
    intro n
    have hcast : ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have h1le : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
    rw [norm_div, norm_one, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos,
      one_div, ← Real.rpow_neg hpos.le]
    apply Real.rpow_le_rpow_of_exponent_le h1le
    linarith
  have hsummaj : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ)) := by
    have h1 := Real.summable_nat_rpow.mpr (show (-(9/8) : ℝ) < -1 by norm_num)
    have h2 := h1.comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) from fun a b hab => by
        simpa using hab)
    apply h2.congr
    intro n
    simp only [Function.comp_apply]
  have hnormsum : Summable fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ s‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm hsummaj
  calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s‖
      ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) ^ s‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ)) :=
        hnormsum.tsum_le_tsum hnorm hsummaj
    _ ≤ 9 := Real.tsum_le_of_sum_range_le (fun n => by positivity)
        sum_range_rpow_nine_eighths_le

/-! ## A2b: sqrt- and log-strength exports from the A1 components

Numerics gates (recorded): `max |ζ|/√(|t|+2) = 0.72` on `σ∈[1/2,2]` (claim 6),
`max |ζ|/(1+log(|t|+2)) = 0.60` on `σ∈[1,2]` (claim 4). -/

open RH.Criteria.NymanBeurling.H14ZetaEM

/-- Harmonic partial sums: `Σ_{n<N} 1/(n+1) ≤ 1 + log (N)` for `N ≥ 1`,
in the inclusive form `≤ 1 + log (N + 1)` valid for all `N`. -/
theorem sum_range_inv_le (N : ℕ) :
    (∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ))⁻¹) ≤ 1 + Real.log (N + 1) := by
  induction N with
  | zero => simp
  | succ M _ =>
    clear ‹_›
    have hanti : AntitoneOn (fun u : ℝ => u⁻¹) (Icc (1 : ℝ) (1 + M)) := by
      intro u hu v hv huv
      have h1 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu.1
      simp only
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le h1 huv
    have hcomp := hanti.sum_le_integral (x₀ := (1 : ℝ)) (a := M)
    have hint : (∫ x in (1 : ℝ)..(1 + M : ℝ), x⁻¹) = Real.log (1 + M) := by
      rw [integral_inv (by
        rw [Set.uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg M))]
        intro h
        exact absurd h.1 (by norm_num))]
      rw [div_eq_mul_inv, mul_comm, ← div_eq_inv_mul]
      norm_num
    rw [Finset.sum_range_succ']
    have hzero : (((0 + 1 : ℕ) : ℝ))⁻¹ = 1 := by norm_num
    rw [hzero]
    have hmatch : (∑ i ∈ Finset.range M, (((i + 1 + 1 : ℕ) : ℝ))⁻¹) =
        ∑ i ∈ Finset.range M, (fun u : ℝ => u⁻¹) ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      push_cast
      ring
    have hlogmono : Real.log (1 + M) ≤ Real.log (M + 1 + 1) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    rw [hmatch]
    push_cast
    have := le_trans hcomp (le_of_eq hint)
    push_cast at this hlogmono
    linarith

/-- Floor cutoff comparisons used repeatedly below. -/
theorem floorX_le {t : ℝ} : ((⌊|t|⌋₊ + 2 : ℕ) : ℝ) ≤ |t| + 2 := by
  push_cast
  linarith [Nat.floor_le (abs_nonneg t)]

theorem le_floorX {t : ℝ} : |t| + 1 ≤ ((⌊|t|⌋₊ + 2 : ℕ) : ℝ) := by
  push_cast
  linarith [Nat.lt_floor_add_one |t|]

/-- A2b sqrt-strength: `‖ζ(σ+it)‖ ≤ 6√(|t|+2)` on `σ ∈ [1/2,2]`, `|t| ≥ 1`. -/
theorem norm_riemannZeta_le_sqrt {σ t : ℝ} (hσl : (1 / 2 : ℝ) ≤ σ)
    (hσh : σ ≤ 2) (ht : (1 : ℝ) ≤ |t|) :
    ‖riemannZeta (σ + Complex.I * t : ℂ)‖ ≤ 6 * Real.sqrt (|t| + 2) := by
  set X : ℕ := ⌊|t|⌋₊ + 2 with hXdef
  have htabs : (0 : ℝ) < |t| := lt_of_lt_of_le one_pos ht
  have hX1 : (1 : ℝ) ≤ ((X : ℕ) : ℝ) := le_trans (by linarith) le_floorX
  have hXpos : (0 : ℝ) < ((X : ℕ) : ℝ) := lt_of_lt_of_le one_pos hX1
  have hsq2 : (0 : ℝ) < Real.sqrt (|t| + 2) := Real.sqrt_pos.mpr (by linarith)
  have hdec := zetaRightHalfEulerMaclaurinComponents.decomposition
    (σ := σ) (t := t) hσl hσh (by simpa using ht)
  -- unfold the instance fields
  simp only [zetaRightHalfEulerMaclaurinComponents] at hdec
  rw [hdec]
  have hsre : (σ + Complex.I * t : ℂ).re = σ := re_sigma_add_I_mul σ t
  -- partial
  have hpartial : ‖∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖ ≤
      2 * Real.sqrt (|t| + 2) := by
    calc ‖∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖
        ≤ 2 * Real.sqrt ((X : ℕ) : ℝ) := partialSum_norm_le hσl t X
      _ ≤ 2 * Real.sqrt (|t| + 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.sqrt_le_sqrt floorX_le
  -- pole
  have hpole : ‖((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) /
      ((σ + Complex.I * t : ℂ) - 1)‖ ≤ Real.sqrt (|t| + 2) := by
    have hXposn : (0 : ℕ) < X := by omega
    have hnum : ‖((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ))‖ =
        ((X : ℕ) : ℝ) ^ (1 - σ) := by
      rw [Complex.norm_natCast_cpow_of_pos hXposn]
      congr 1
      rw [Complex.sub_re, Complex.one_re, hsre]
    have hden : (1 : ℝ) ≤ ‖(σ + Complex.I * t : ℂ) - 1‖ := by
      calc (1 : ℝ) ≤ |t| := ht
        _ = |((σ + Complex.I * t : ℂ) - 1).im| := by
            rw [Complex.sub_im, Complex.one_im, im_sigma_add_I_mul]
            simp
        _ ≤ ‖(σ + Complex.I * t : ℂ) - 1‖ := Complex.abs_im_le_norm _
    rw [norm_div, hnum]
    calc ((X : ℕ) : ℝ) ^ (1 - σ) / ‖(σ + Complex.I * t : ℂ) - 1‖
        ≤ ((X : ℕ) : ℝ) ^ (1 - σ) / 1 := by
          apply div_le_div_of_nonneg_left _ one_pos hden
          positivity
      _ = ((X : ℕ) : ℝ) ^ (1 - σ) := div_one _
      _ ≤ ((X : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = Real.sqrt ((X : ℕ) : ℝ) := (Real.sqrt_eq_rpow _).symm
      _ ≤ Real.sqrt (|t| + 2) := Real.sqrt_le_sqrt floorX_le
  -- tail
  have htail : ‖-((σ + Complex.I * t : ℂ) *
      emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖ ≤ 3 * Real.sqrt (|t| + 2) := by
    have htl : ‖emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ)‖ ≤
        ((X : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * 2 := by
      calc ‖emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ)‖
          ≤ ((X : ℕ) : ℝ) ^ (-(σ + Complex.I * t : ℂ).re) /
              (σ + Complex.I * t : ℂ).re :=
            emTail_norm_le (by rw [hsre]; exact hσl) hX1
        _ ≤ ((X : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * 2 := by
            rw [hsre]
            rw [div_eq_mul_inv]
            apply mul_le_mul
            · exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
            · rw [← one_div]
              rw [div_le_iff₀ (by linarith)]
              linarith
            · positivity
            · positivity
    have hs_norm : ‖(σ + Complex.I * t : ℂ)‖ ≤ |t| + 2 := by
      calc ‖(σ + Complex.I * t : ℂ)‖ ≤ ‖(σ : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ :=
            norm_add_le _ _
        _ = |σ| + |t| := by
            rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul,
              Complex.norm_real]
            simp [Real.norm_eq_abs]
        _ ≤ 2 + |t| := by
            have : |σ| ≤ 2 := abs_le.mpr ⟨by linarith, hσh⟩
            linarith
        _ = |t| + 2 := by ring
    have hXlow : ((X : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        Real.sqrt 2 / Real.sqrt (|t| + 2) := by
      have h2X : |t| + 2 ≤ 2 * ((X : ℕ) : ℝ) := by
        have := le_floorX (t := t)
        linarith
      rw [Real.rpow_neg hXpos.le, ← Real.sqrt_eq_rpow, ← one_div,
        div_le_div_iff₀ (Real.sqrt_pos.mpr hXpos) hsq2]
      rw [one_mul, ← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_le_sqrt
      linarith
    calc ‖-((σ + Complex.I * t : ℂ) * emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖
        = ‖(σ + Complex.I * t : ℂ)‖ * ‖emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ)‖ := by
          rw [norm_neg, norm_mul]
      _ ≤ (|t| + 2) * (((X : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * 2) := by
          apply mul_le_mul hs_norm htl (norm_nonneg _) (by positivity)
      _ ≤ (|t| + 2) * (Real.sqrt 2 / Real.sqrt (|t| + 2) * 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hXlow (by norm_num)
      _ = 2 * Real.sqrt 2 * ((|t| + 2) / Real.sqrt (|t| + 2)) := by ring
      _ = 2 * Real.sqrt 2 * Real.sqrt (|t| + 2) := by
          rw [Real.div_sqrt]
      _ ≤ 3 * Real.sqrt (|t| + 2) := by
          apply mul_le_mul_of_nonneg_right _ hsq2.le
          nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
            Real.sqrt_nonneg (2 : ℝ)]
  calc ‖(∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))) +
        ((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) / ((σ + Complex.I * t : ℂ) - 1) +
        -((σ + Complex.I * t : ℂ) * emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))) +
          ((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) / ((σ + Complex.I * t : ℂ) - 1)‖ +
        ‖-((σ + Complex.I * t : ℂ) * emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖ :=
        norm_add_le _ _
    _ ≤ (‖∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖ +
        ‖((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) / ((σ + Complex.I * t : ℂ) - 1)‖) +
        ‖-((σ + Complex.I * t : ℂ) * emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ (2 * Real.sqrt (|t| + 2) + Real.sqrt (|t| + 2)) + 3 * Real.sqrt (|t| + 2) := by
        gcongr
    _ = 6 * Real.sqrt (|t| + 2) := by ring

/-! ## A2b (log-strength) and A2c: the functional-equation transport -/

/-- A2b log-strength: `‖ζ(σ+it)‖ ≤ 4(1 + log(|t|+2))` on `σ ∈ [1,2]`, `|t| ≥ 1`. -/
theorem norm_riemannZeta_le_log {σ t : ℝ} (hσl : (1 : ℝ) ≤ σ)
    (hσh : σ ≤ 2) (ht : (1 : ℝ) ≤ |t|) :
    ‖riemannZeta (σ + Complex.I * t : ℂ)‖ ≤ 4 * (1 + Real.log (|t| + 2)) := by
  set X : ℕ := ⌊|t|⌋₊ + 2 with hXdef
  have htabs : (0 : ℝ) < |t| := lt_of_lt_of_le one_pos ht
  have hX1 : (1 : ℝ) ≤ ((X : ℕ) : ℝ) := le_trans (by linarith) le_floorX
  have hXpos : (0 : ℝ) < ((X : ℕ) : ℝ) := lt_of_lt_of_le one_pos hX1
  have hL1 : (1 : ℝ) ≤ Real.log (|t| + 2) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith
  have hdec := zetaRightHalfEulerMaclaurinComponents.decomposition
    (σ := σ) (t := t) (by linarith) hσh (by simpa using ht)
  simp only [zetaRightHalfEulerMaclaurinComponents] at hdec
  rw [hdec]
  have hsre : (σ + Complex.I * t : ℂ).re = σ := re_sigma_add_I_mul σ t
  -- partial: harmonic bound
  have hpartial : ‖∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖ ≤
      2 + Real.log (|t| + 2) := by
    have hterm : ∀ n ∈ Finset.Icc 1 X,
        ‖(n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖ ≤ ((n : ℕ) : ℝ)⁻¹ := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnr : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hn1
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      have hre : (-(σ + Complex.I * t : ℂ)).re = -σ := by
        rw [Complex.neg_re, hsre]
      rw [hre]
      calc ((n : ℕ) : ℝ) ^ (-σ) ≤ ((n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hnr (by linarith)
        _ = ((n : ℕ) : ℝ)⁻¹ := by
            rw [Real.rpow_neg (by positivity), Real.rpow_one]
    have hicc : (∑ n ∈ Finset.Icc 1 X, ((n : ℕ) : ℝ)⁻¹) =
        ∑ i ∈ Finset.range X, (((i + 1 : ℕ) : ℝ))⁻¹ := by
      rw [show Finset.Icc 1 X = Finset.Ico 1 (X + 1) from by ext n; simp,
        Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      push_cast
      ring
    have hlogX : Real.log ((X : ℝ) + 1) ≤ 1 + Real.log (|t| + 2) := by
      have hXle : ((X : ℕ) : ℝ) + 1 ≤ Real.exp 1 * (|t| + 2) := by
        have h1 := floorX_le (t := t)
        have h2e : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ)
          linarith
        nlinarith [abs_nonneg t,
          mul_nonneg (sub_nonneg.mpr h2e) (show (0:ℝ) ≤ |t| + 2 by positivity)]
      calc Real.log ((X : ℝ) + 1) ≤ Real.log (Real.exp 1 * (|t| + 2)) :=
            Real.log_le_log (by positivity) hXle
        _ = 1 + Real.log (|t| + 2) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
    calc ‖∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖
        ≤ ∑ n ∈ Finset.Icc 1 X, ‖(n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 X, ((n : ℕ) : ℝ)⁻¹ := Finset.sum_le_sum hterm
      _ = ∑ i ∈ Finset.range X, (((i + 1 : ℕ) : ℝ))⁻¹ := hicc
      _ ≤ 1 + Real.log ((X : ℝ) + 1) := sum_range_inv_le X
      _ ≤ 2 + Real.log (|t| + 2) := by linarith
  -- pole ≤ 1
  have hpole : ‖((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) /
      ((σ + Complex.I * t : ℂ) - 1)‖ ≤ 1 := by
    have hXposn : (0 : ℕ) < X := by omega
    have hnum : ‖((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ))‖ =
        ((X : ℕ) : ℝ) ^ (1 - σ) := by
      rw [Complex.norm_natCast_cpow_of_pos hXposn]
      congr 1
      rw [Complex.sub_re, Complex.one_re, hsre]
    have hden : (1 : ℝ) ≤ ‖(σ + Complex.I * t : ℂ) - 1‖ := by
      calc (1 : ℝ) ≤ |t| := ht
        _ = |((σ + Complex.I * t : ℂ) - 1).im| := by
            rw [Complex.sub_im, Complex.one_im, im_sigma_add_I_mul]
            simp
        _ ≤ ‖(σ + Complex.I * t : ℂ) - 1‖ := Complex.abs_im_le_norm _
    rw [norm_div, hnum]
    have hnum1 : ((X : ℕ) : ℝ) ^ (1 - σ) ≤ 1 := by
      calc ((X : ℕ) : ℝ) ^ (1 - σ) ≤ ((X : ℕ) : ℝ) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
        _ = 1 := Real.rpow_zero _
    calc ((X : ℕ) : ℝ) ^ (1 - σ) / ‖(σ + Complex.I * t : ℂ) - 1‖
        ≤ 1 / 1 := by
          apply div_le_div₀ (by norm_num) hnum1 one_pos hden
      _ = 1 := by norm_num
  -- tail ≤ 2
  have htail : ‖-((σ + Complex.I * t : ℂ) *
      emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖ ≤ 2 := by
    have htl : ‖emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ)‖ ≤
        ((X : ℕ) : ℝ)⁻¹ := by
      calc ‖emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ)‖
          ≤ ((X : ℕ) : ℝ) ^ (-(σ + Complex.I * t : ℂ).re) /
              (σ + Complex.I * t : ℂ).re :=
            emTail_norm_le (by rw [hsre]; linarith) hX1
        _ ≤ ((X : ℕ) : ℝ) ^ (-(1 : ℝ)) / 1 := by
            rw [hsre]
            apply div_le_div₀ _ _ one_pos hσl
            · positivity
            · exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
        _ = ((X : ℕ) : ℝ)⁻¹ := by
            rw [div_one, Real.rpow_neg (by positivity), Real.rpow_one]
    have hs_norm : ‖(σ + Complex.I * t : ℂ)‖ ≤ |t| + 2 := by
      calc ‖(σ + Complex.I * t : ℂ)‖ ≤ ‖(σ : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ :=
            norm_add_le _ _
        _ = |σ| + |t| := by
            rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul,
              Complex.norm_real]
            simp [Real.norm_eq_abs]
        _ ≤ 2 + |t| := by
            have : |σ| ≤ 2 := abs_le.mpr ⟨by linarith, hσh⟩
            linarith
        _ = |t| + 2 := by ring
    have hXinv : ((X : ℕ) : ℝ)⁻¹ ≤ 2 / (|t| + 2) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hXpos (by linarith)]
      have := le_floorX (t := t)
      linarith
    calc ‖-((σ + Complex.I * t : ℂ) * emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖
        = ‖(σ + Complex.I * t : ℂ)‖ *
            ‖emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ)‖ := by
          rw [norm_neg, norm_mul]
      _ ≤ (|t| + 2) * (2 / (|t| + 2)) := by
          apply mul_le_mul hs_norm (le_trans htl hXinv) (norm_nonneg _) (by positivity)
      _ = 2 := by field_simp
  calc ‖(∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))) +
        ((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) / ((σ + Complex.I * t : ℂ) - 1) +
        -((σ + Complex.I * t : ℂ) * emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))) +
          ((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) / ((σ + Complex.I * t : ℂ) - 1)‖ +
        ‖-((σ + Complex.I * t : ℂ) * emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖ :=
        norm_add_le _ _
    _ ≤ (‖∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖ +
        ‖((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) / ((σ + Complex.I * t : ℂ) - 1)‖) +
        ‖-((σ + Complex.I * t : ℂ) * emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ((2 + Real.log (|t| + 2)) + 1) + 2 := by gcongr
    _ ≤ 4 * (1 + Real.log (|t| + 2)) := by linarith

/-! ## A2c: the functional-equation factor and the transport -/

/-- The χ-factor of the functional equation, in the `1−w` form. -/
noncomputable def zetaFEFactor (w : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (w - 1) * Complex.Gamma (1 - w) *
    Complex.cos ((Real.pi : ℂ) * (1 - w) / 2)

/-- The functional equation in factor form, valid off the real axis. -/
theorem riemannZeta_eq_zetaFEFactor_mul {w : ℂ} (hw : w.im ≠ 0) :
    riemannZeta w = zetaFEFactor w * riemannZeta (1 - w) := by
  have hn : ∀ n : ℕ, (1 - w) ≠ -(n : ℂ) := by
    intro n h
    apply hw
    have := congrArg Complex.im h
    simp at this
    linarith [this]
  have h1 : (1 - w) ≠ 1 := by
    intro h
    apply hw
    have : w = 0 := by linear_combination -h
    rw [this]
    exact Complex.zero_im
  have h := riemannZeta_one_sub hn h1
  rw [show (1 : ℂ) - (1 - w) = w from by ring] at h
  rw [h]
  unfold zetaFEFactor
  rw [show (-(1 - w) : ℂ) = w - 1 from by ring]

/-- A2c debt: the vertical Stirling bound for the FE factor.  The numerics
gate found `sup |factor|/(|t|+2)^{1/2−σ} = 1.0000` exactly (attained on the
critical line where the factor is unimodular); any `C ≥ 1` is admissible and
the intended instantiation is `C = 2`.  Mathlib currently has no vertical
Gamma asymptotics, so this single bound is the isolated remaining content. -/
structure ZetaFEFactorVerticalBound where
  C : ℝ
  C_nonneg : 0 ≤ C
  factor_bound :
    ∀ {σ t : ℝ}, -(1 / 2 : ℝ) ≤ σ → σ ≤ (1 / 2 : ℝ) → 1 ≤ |t| →
      ‖zetaFEFactor (σ + Complex.I * t : ℂ)‖ ≤
        C * (|t| + 2) ^ ((1 / 2 : ℝ) - σ)

/-- A2 assembled: the FE-factor bound transports the proved right-half
estimates to the frozen left-strip vertical-growth target. -/
noncomputable def zetaLeftStripLinearVerticalGrowthAtHeight_of_factorBound
    (G : ZetaFEFactorVerticalBound) :
    RH.Criteria.NymanBeurling.MobiusSummatory.ZetaLeftStripLinearVerticalGrowthAtHeight where
  t₀ := 1
  t₀_pos := one_pos
  t₀_le_one := le_rfl
  C := 15 * G.C
  C_nonneg := mul_nonneg (by norm_num) G.C_nonneg
  left_strip_growth := by
    intro σ t hσlow hσhigh ht
    have htabs : (0 : ℝ) < |t| := lt_of_lt_of_le one_pos ht
    have hu1 : (1 : ℝ) ≤ |t| + 2 := by linarith
    have hupos : (0 : ℝ) < |t| + 2 := by linarith
    have him : (σ + Complex.I * t : ℂ).im ≠ 0 := by
      rw [im_sigma_add_I_mul]
      intro h
      rw [h] at ht
      simp at ht
      linarith
    have hfe := riemannZeta_eq_zetaFEFactor_mul him
    have hshape : (1 : ℂ) - (σ + Complex.I * t) =
        ((1 - σ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ) := by
      push_cast
      ring
    have habs : |(-t : ℝ)| = |t| := abs_neg t
    have hfac := G.factor_bound hσlow hσhigh ht
    have hexp_le : ((1 / 2 : ℝ) - σ) ≤ 1 := by linarith
    have hpow_le : (|t| + 2) ^ ((1 / 2 : ℝ) - σ) ≤ (|t| + 2) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu1 hexp_le
    rw [hfe, norm_mul]
    rcases le_total σ (-(1 / 8 : ℝ)) with hreg1 | hreg1
    · -- regime 1: series bound
      have hz : ‖riemannZeta ((1 : ℂ) - (σ + Complex.I * t))‖ ≤ 9 := by
        apply norm_riemannZeta_le_of_re_ge
        rw [hshape, re_sigma_add_I_mul]
        linarith
      calc ‖zetaFEFactor (σ + Complex.I * t : ℂ)‖ *
            ‖riemannZeta ((1 : ℂ) - (σ + Complex.I * t))‖
          ≤ (G.C * (|t| + 2) ^ ((1 / 2 : ℝ) - σ)) * 9 := by
            apply mul_le_mul hfac hz (norm_nonneg _) (mul_nonneg G.C_nonneg (by positivity))
        _ ≤ (G.C * (|t| + 2) ^ (1 : ℝ)) * 9 := by
            apply mul_le_mul_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hpow_le G.C_nonneg
        _ = 9 * G.C * (|t| + 2) := by
            rw [Real.rpow_one]
            ring
        _ ≤ 15 * G.C * (|t| + 2) := by nlinarith [mul_nonneg G.C_nonneg hupos.le]
    · rcases le_total σ 0 with hreg2 | hreg2
      · -- regime 2: log bound, exponent ≤ 5/8
        have hz : ‖riemannZeta ((1 : ℂ) - (σ + Complex.I * t))‖ ≤
            4 * (1 + Real.log (|t| + 2)) := by
          rw [hshape]
          have := norm_riemannZeta_le_log (σ := 1 - σ) (t := -t)
            (by linarith) (by linarith) (by rw [habs]; exact ht)
          rwa [habs] at this
        have hlog : 1 + Real.log (|t| + 2) ≤ (11 / 3 : ℝ) * (|t| + 2) ^ (3 / 8 : ℝ) := by
          have hloglem := RH.Criteria.NymanBeurling.H14ZetaEM.log_le_rpow_div_self
            (u := |t| + 2) hu1 (show (0:ℝ) < 3/8 by norm_num)
          have hone : (1 : ℝ) ≤ (|t| + 2) ^ (3 / 8 : ℝ) := by
            rw [show (1 : ℝ) = (|t| + 2) ^ (0 : ℝ) from (Real.rpow_zero _).symm]
            exact Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
          have h83 : (|t| + 2) ^ (3 / 8 : ℝ) / (3 / 8 : ℝ) =
              (8 / 3 : ℝ) * (|t| + 2) ^ (3 / 8 : ℝ) := by ring
          rw [h83] at hloglem
          linarith
        have hexp58 : (|t| + 2) ^ ((1 / 2 : ℝ) - σ) ≤ (|t| + 2) ^ (5 / 8 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
        calc ‖zetaFEFactor (σ + Complex.I * t : ℂ)‖ *
              ‖riemannZeta ((1 : ℂ) - (σ + Complex.I * t))‖
            ≤ (G.C * (|t| + 2) ^ ((1 / 2 : ℝ) - σ)) *
                (4 * (1 + Real.log (|t| + 2))) := by
              apply mul_le_mul hfac hz (norm_nonneg _) (mul_nonneg G.C_nonneg (by positivity))
          _ ≤ (G.C * (|t| + 2) ^ (5 / 8 : ℝ)) *
                (4 * ((11 / 3 : ℝ) * (|t| + 2) ^ (3 / 8 : ℝ))) := by
              have hL0 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg hu1
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hexp58 G.C_nonneg
              · exact mul_le_mul_of_nonneg_left hlog (by norm_num)
              · linarith
              · exact mul_nonneg G.C_nonneg (by positivity)
          _ = (44 / 3 : ℝ) * G.C *
                ((|t| + 2) ^ (5 / 8 : ℝ) * (|t| + 2) ^ (3 / 8 : ℝ)) := by ring
          _ = (44 / 3 : ℝ) * G.C * (|t| + 2) := by
              rw [← Real.rpow_add hupos]
              norm_num
          _ ≤ 15 * G.C * (|t| + 2) := by nlinarith [mul_nonneg G.C_nonneg hupos.le]
      · -- regime 3: sqrt bound
        have hz : ‖riemannZeta ((1 : ℂ) - (σ + Complex.I * t))‖ ≤
            6 * Real.sqrt (|t| + 2) := by
          rw [hshape]
          have := norm_riemannZeta_le_sqrt (σ := 1 - σ) (t := -t)
            (by linarith) (by linarith) (by rw [habs]; exact ht)
          rwa [habs] at this
        have hsqrt : Real.sqrt (|t| + 2) = (|t| + 2) ^ (1 / 2 : ℝ) :=
          Real.sqrt_eq_rpow _
        calc ‖zetaFEFactor (σ + Complex.I * t : ℂ)‖ *
              ‖riemannZeta ((1 : ℂ) - (σ + Complex.I * t))‖
            ≤ (G.C * (|t| + 2) ^ ((1 / 2 : ℝ) - σ)) * (6 * Real.sqrt (|t| + 2)) := by
              apply mul_le_mul hfac hz (norm_nonneg _) (mul_nonneg G.C_nonneg (by positivity))
          _ = 6 * G.C * ((|t| + 2) ^ ((1 / 2 : ℝ) - σ) * (|t| + 2) ^ (1 / 2 : ℝ)) := by
              rw [hsqrt]
              ring
          _ = 6 * G.C * (|t| + 2) ^ (1 - σ) := by
              rw [← Real.rpow_add hupos]
              norm_num
              exact Or.inl (by
                rw [show (1 / 2 - σ + 1 / 2 : ℝ) = 1 - σ from by ring])
          _ ≤ 6 * G.C * (|t| + 2) ^ (1 : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) G.C_nonneg)
              exact Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
          _ = 6 * G.C * (|t| + 2) := by rw [Real.rpow_one]
          _ ≤ 15 * G.C * (|t| + 2) := by nlinarith [mul_nonneg G.C_nonneg hupos.le]

end RH.Criteria.NymanBeurling.H14ZetaFETransport
