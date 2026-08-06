import NBMellinTools.NB17Mellin

/-!
# The Mellin transform of the fractional part

The classical formula

`∫_0^∞ {1/x} x^{s-1} dx = ∫_0^∞ {u} u^{-s-1} du = -ζ(s)/s`  for `0 < Re s < 1`,

which is the analytic heart of the Báez-Duarte form of the Nyman–Beurling criterion.

## Proof strategy

Write `∫_0^∞ {u} u^{-s-1} du = ∫_0^1 u^{-s} du + G(s)` with `G(s) = ∫_1^∞ {u} u^{-s-1} du`
(`NB17ZetaFract.gTail`).  The first integral is `1/(1-s)`.  The function `G` is holomorphic on
the whole half-plane `Re s > 0` (the integrand is `O(u^{-Re s-1})` at infinity and the function
vanishes near `0`), while for `Re s > 1` a direct computation using
`⌊u⌋ = ∑_{n ≥ 1} 1_{[n,∞)}(u)` gives `G(s) = 1/(s-1) - ζ(s)/s`.  By the identity theorem on the
connected open set `{Re s > 0} \ {1}` the same formula holds on the critical strip, whence

`∫_0^∞ {u} u^{-s-1} du = 1/(1-s) + 1/(s-1) - ζ(s)/s = -ζ(s)/s`.
-/

open MeasureTheory Set Filter Complex Topology Asymptotics

noncomputable section

namespace NB17ZetaFract

open NB17Mellin

/-! ## The fractional part as a complex-valued function -/

/-- The fractional part, viewed as a complex-valued function. -/
def fractC (u : ℝ) : ℂ := ((Int.fract u : ℝ) : ℂ)

lemma measurable_fractC : Measurable fractC := Complex.measurable_ofReal.comp measurable_fract

lemma norm_fractC_le_one (u : ℝ) : ‖fractC u‖ ≤ 1 := by
  rw [fractC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg u)]
  exact (Int.fract_lt_one u).le

lemma fractC_eq_sub_floor (u : ℝ) : fractC u = (u : ℂ) - ((⌊u⌋ : ℤ) : ℂ) := by
  rw [fractC, Int.fract]
  push_cast
  ring

lemma aesm_cpow_mul (a : ℂ) {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Ioi (0:ℝ)) :
    AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ a * fractC u) (volume.restrict S) := by
  refine AEStronglyMeasurable.mul ?_ measurable_fractC.aestronglyMeasurable
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) hS
  exact (Complex.continuousAt_ofReal_cpow_const _ _
    (Or.inr (ne_of_gt (hSsub ht)))).continuousWithinAt

lemma aesm_cpow (a : ℂ) {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Ioi (0:ℝ)) :
    AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ a) (volume.restrict S) := by
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) hS
  exact (Complex.continuousAt_ofReal_cpow_const _ _
    (Or.inr (ne_of_gt (hSsub ht)))).continuousWithinAt

/-! ## Integrability -/

lemma integrableOn_tail {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1) * fractC u) (Ioi 1) := by
  have hdom : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hsub : Ioi (1:ℝ) ⊆ Ioi (0:ℝ) := Ioi_subset_Ioi zero_le_one
  refine Integrable.mono' hdom (aesm_cpow_mul _ measurableSet_Ioi hsub) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
  have hu0 : (0:ℝ) < u := hsub hu
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  have h1 : ‖fractC u‖ ≤ 1 := norm_fractC_le_one u
  have hre : (-s - 1).re = -s.re - 1 := by simp
  have h2 : (0:ℝ) ≤ u ^ ((-s - 1).re) := Real.rpow_nonneg hu0.le _
  rw [hre] at h2 ⊢
  nlinarith

lemma integrableOn_head {s : ℂ} (hs : s.re < 1) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1) * fractC u) (Ioc 0 1) := by
  have hdom : IntegrableOn (fun u : ℝ => u ^ (-s.re)) (Ioc 0 1) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -s.re)
      (by linarith)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
  refine Integrable.mono' hdom (aesm_cpow_mul _ measurableSet_Ioc Ioc_subset_Ioi_self) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
  obtain ⟨hu0, hu1⟩ := hu
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  have hre : (-s - 1).re = -s.re - 1 := by simp
  have hfr : ‖fractC u‖ ≤ u := by
    rw [fractC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg u)]
    rcases lt_or_eq_of_le hu1 with h | h
    · rw [Int.fract_eq_self.2 ⟨hu0.le, h⟩]
    · rw [h]; simp
  have h2 : (0:ℝ) < u ^ (-s.re - 1) := Real.rpow_pos_of_pos hu0 _
  rw [hre]
  calc u ^ (-s.re - 1) * ‖fractC u‖ ≤ u ^ (-s.re - 1) * u := by nlinarith
    _ = u ^ (-s.re) := by
        nth_rewrite 2 [show u = u ^ (1:ℝ) from (Real.rpow_one u).symm]
        rw [← Real.rpow_add hu0]
        norm_num

/-! ## The tail integral `G(s) = ∫_1^∞ {u} u^{-s-1} du` -/

/-- `gTail s = ∫_1^∞ {u} u^{-s-1} du`. -/
def gTail (s : ℂ) : ℂ := ∫ u in Ioi (1:ℝ), (u : ℂ) ^ (-s - 1) * fractC u

/-- The indicator of `(1,∞)` times the fractional part; its Mellin transform is `gTail`. -/
def fractTail (u : ℝ) : ℂ := Set.indicator (Ioi (1:ℝ)) fractC u

lemma gTail_eq_mellin (s : ℂ) : gTail s = mellin fractTail (-s) := by
  rw [gTail, mellin]
  rw [show (Ioi (1:ℝ)) = Ioi (1:ℝ) from rfl]
  have : ∀ u : ℝ, (u : ℂ) ^ (-s - 1) • fractTail u
      = Set.indicator (Ioi (1:ℝ)) (fun u : ℝ => (u : ℂ) ^ (-s - 1) * fractC u) u := by
    intro u
    by_cases hu : u ∈ Ioi (1:ℝ)
    · simp [fractTail, Set.indicator_of_mem hu, smul_eq_mul]
    · simp [fractTail, Set.indicator_of_notMem hu]
  calc (∫ u in Ioi (1:ℝ), (u : ℂ) ^ (-s - 1) * fractC u)
      = ∫ u in Ioi (0:ℝ),
          Set.indicator (Ioi (1:ℝ)) (fun u : ℝ => (u : ℂ) ^ (-s - 1) * fractC u) u := by
        rw [MeasureTheory.integral_indicator measurableSet_Ioi,
          Measure.restrict_restrict measurableSet_Ioi]
        congr 1
        rw [Set.inter_eq_left.2 (Ioi_subset_Ioi zero_le_one)]
    _ = ∫ u in Ioi (0:ℝ), (u : ℂ) ^ ((-s) - 1) • fractTail u := by
        refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
        rw [this u]

/-! ### The value of `gTail` for `Re s > 1` -/

lemma floor_eq_tsum {u : ℝ} (hu : 1 ≤ u) :
    ((⌊u⌋ : ℤ) : ℂ) = ∑' n : ℕ, (if ((n : ℝ) + 1) ≤ u then (1:ℂ) else 0) := by
  classical
  set m : ℕ := ⌊u⌋.toNat with hm
  have hfl : (0:ℤ) ≤ ⌊u⌋ := Int.le_floor.2 (by exact_mod_cast le_trans zero_le_one hu)
  have hmz : (⌊u⌋ : ℤ) = (m : ℤ) := by rw [hm, Int.toNat_of_nonneg hfl]
  have hiff : ∀ n : ℕ, (((n : ℝ) + 1) ≤ u ↔ n ∈ Finset.range m) := by
    intro n
    rw [Finset.mem_range]
    constructor
    · intro h
      have h2 : ((n : ℤ) + 1) ≤ ⌊u⌋ := Int.le_floor.2 (by push_cast; exact h)
      omega
    · intro h
      have h2 : ((n : ℤ) + 1) ≤ ⌊u⌋ := by omega
      have h3 := Int.le_floor.1 h2
      push_cast at h3
      exact h3
  have key : ∀ n : ℕ, (if ((n : ℝ) + 1) ≤ u then (1:ℂ) else 0)
      = if n ∈ Finset.range m then 1 else 0 := by
    intro n
    by_cases h : ((n : ℝ) + 1) ≤ u
    · rw [if_pos h, if_pos ((hiff n).1 h)]
    · rw [if_neg h, if_neg (fun hc => h ((hiff n).2 hc))]
  rw [tsum_congr key,
    tsum_eq_sum (s := Finset.range m) (fun b hb => by rw [if_neg hb]),
    Finset.sum_congr rfl (fun b hb => if_pos hb)]
  simp [hmz]

/-- The `n`-th piece of the decomposition `⌊u⌋ u^{-s-1} = ∑_n 1_{[n+1,∞)}(u) u^{-s-1}`. -/
def floorPiece (s : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  Set.indicator (Ici ((n : ℝ) + 1)) (fun u : ℝ => (u : ℂ) ^ (-s - 1)) u

lemma integrableOn_cpow_tail {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Ioi 1) := by
  refine integrableOn_Ioi_cpow_of_lt ?_ one_pos
  simp only [sub_re, neg_re, one_re]
  linarith

lemma integrableOn_floorPiece {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (floorPiece s n) (Ioi 1) :=
  (integrableOn_cpow_tail hs).indicator measurableSet_Ici

lemma integral_floorPiece {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ u in Ioi (1:ℝ), floorPiece s n u) = ((n : ℂ) + 1) ^ (-s) / s := by
  have ha : (1:ℝ) ≤ (n : ℝ) + 1 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have ha0 : (0:ℝ) < (n : ℝ) + 1 := lt_of_lt_of_le zero_lt_one ha
  simp only [floorPiece]
  rw [MeasureTheory.integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have h2 : (Ioi ((n : ℝ) + 1) ∩ Ioi (1:ℝ) : Set ℝ) = Ioi ((n : ℝ) + 1) := by
    rw [Set.inter_eq_left]
    intro x hx
    simp only [mem_Ioi] at hx ⊢
    linarith
  have hset : ((Ici ((n : ℝ) + 1) ∩ Ioi (1:ℝ) : Set ℝ)) =ᵐ[volume] (Ioi ((n : ℝ) + 1) : Set ℝ) := by
    have h1 : ((Ici ((n : ℝ) + 1) ∩ Ioi (1:ℝ) : Set ℝ))
        =ᵐ[volume] ((Ioi ((n : ℝ) + 1) ∩ Ioi (1:ℝ) : Set ℝ)) :=
      (Ioi_ae_eq_Ici (a := (n : ℝ) + 1)).symm.inter (ae_eq_refl _)
    rw [← h2]
    exact h1
  rw [setIntegral_congr_set hset]
  have hre : (-s - 1).re < -1 := by
    simp only [sub_re, neg_re, one_re]
    linarith
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  rw [integral_Ioi_cpow_of_lt hre ha0, show (-s - 1 + 1) = -s from by ring]
  push_cast
  field_simp

lemma integral_norm_floorPiece {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ u in Ioi (1:ℝ), ‖floorPiece s n u‖) = ((n : ℝ) + 1) ^ (-s.re) / s.re := by
  have ha : (1:ℝ) ≤ (n : ℝ) + 1 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have ha0 : (0:ℝ) < (n : ℝ) + 1 := lt_of_lt_of_le zero_lt_one ha
  have hnorm : ∀ u : ℝ, ‖floorPiece s n u‖
      = Set.indicator (Ici ((n : ℝ) + 1)) (fun u : ℝ => ‖(u : ℂ) ^ (-s - 1)‖) u := by
    intro u
    by_cases hu : u ∈ Ici ((n : ℝ) + 1)
    · rw [floorPiece, Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    · rw [floorPiece, Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, norm_zero]
  simp_rw [hnorm]
  rw [MeasureTheory.integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have h2 : (Ioi ((n : ℝ) + 1) ∩ Ioi (1:ℝ) : Set ℝ) = Ioi ((n : ℝ) + 1) := by
    rw [Set.inter_eq_left]
    intro x hx
    simp only [mem_Ioi] at hx ⊢
    linarith
  have hset : ((Ici ((n : ℝ) + 1) ∩ Ioi (1:ℝ) : Set ℝ)) =ᵐ[volume] (Ioi ((n : ℝ) + 1) : Set ℝ) := by
    have h1 : ((Ici ((n : ℝ) + 1) ∩ Ioi (1:ℝ) : Set ℝ))
        =ᵐ[volume] ((Ioi ((n : ℝ) + 1) ∩ Ioi (1:ℝ) : Set ℝ)) :=
      (Ioi_ae_eq_Ici (a := (n : ℝ) + 1)).symm.inter (ae_eq_refl _)
    rw [← h2]
    exact h1
  rw [setIntegral_congr_set hset]
  have hcongr : ∀ u ∈ Ioi ((n : ℝ) + 1), ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    intro u hu
    have hu0 : (0:ℝ) < u := lt_trans ha0 hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) ha0,
    show (-s.re - 1 + 1) = -s.re from by ring, neg_div, div_neg, neg_neg]

lemma summable_integral_norm_floorPiece {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ∫ u in Ioi (1:ℝ), ‖floorPiece s n u‖) := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have hEq : ∀ n : ℕ, (∫ u in Ioi (1:ℝ), ‖floorPiece s n u‖)
      = (((n : ℝ) + 1) ^ (-s.re)) / s.re := fun n => integral_norm_floorPiece hs0 n
  simp_rw [hEq]
  refine Summable.div_const ?_ _
  have h4 : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re)) := by
    have h5 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ (s.re)) :=
      (Real.summable_one_div_nat_rpow (p := s.re)).2 hs
    refine h5.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
  have h3 : Summable (fun n : ℕ => (((n + 1 : ℕ)) : ℝ) ^ (-s.re)) := (summable_nat_add_iff 1).2 h4
  refine h3.congr fun n => ?_
  push_cast
  ring_nf

lemma tsum_floorPiece {s : ℂ} {u : ℝ} (hu : 1 < u) :
    ∑' n : ℕ, floorPiece s n u = (u : ℂ) ^ (-s - 1) * ((⌊u⌋ : ℤ) : ℂ) := by
  have hpiece : ∀ n : ℕ, floorPiece s n u
      = (u : ℂ) ^ (-s - 1) * (if ((n : ℝ) + 1) ≤ u then (1:ℂ) else 0) := by
    intro n
    by_cases hn : ((n : ℝ) + 1) ≤ u
    · rw [floorPiece, Set.indicator_of_mem (by exact hn), if_pos hn, mul_one]
    · rw [floorPiece, Set.indicator_of_notMem (by exact hn), if_neg hn, mul_zero]
  rw [tsum_congr hpiece, tsum_mul_left, ← floor_eq_tsum hu.le]

lemma gTail_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    gTail s = 1 / (s - 1) - riemannZeta s / s := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have hs0' : s ≠ 0 := by intro h; rw [h] at hs0; simp at hs0
  -- integrability of the two pieces
  have hint1 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s)) (Ioi 1) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ one_pos
    simp only [neg_re]
    linarith
  have hint2 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1) * ((⌊u⌋ : ℤ) : ℂ)) (Ioi 1) := by
    have hsum := integrableOn_tail hs0
    have hdiff : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s) - (u : ℂ) ^ (-s - 1) * fractC u)
        (Ioi 1) := hint1.sub hsum
    refine MeasureTheory.IntegrableOn.congr_fun hdiff (fun u hu => ?_) measurableSet_Ioi
    have hu0 : (0:ℝ) < u := lt_trans one_pos hu
    have hune : (u : ℂ) ≠ 0 := by
      simpa using ne_of_gt hu0
    have hcpow : (u : ℂ) ^ (-s) = (u : ℂ) ^ (-s - 1) * (u : ℂ) := by
      have h := Complex.cpow_add (-s - 1) 1 hune
      rw [Complex.cpow_one, show (-s - 1 + 1 : ℂ) = -s from by ring] at h
      exact h
    rw [fractC_eq_sub_floor, hcpow]
    ring
  -- split the integral
  have hsplit : gTail s = (∫ u in Ioi (1:ℝ), (u : ℂ) ^ (-s))
      - ∫ u in Ioi (1:ℝ), (u : ℂ) ^ (-s - 1) * ((⌊u⌋ : ℤ) : ℂ) := by
    rw [gTail, ← MeasureTheory.integral_sub hint1 hint2]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0:ℝ) < u := lt_trans one_pos hu
    have hune : (u : ℂ) ≠ 0 := by simpa using ne_of_gt hu0
    have hcpow : (u : ℂ) ^ (-s) = (u : ℂ) ^ (-s - 1) * (u : ℂ) := by
      have h := Complex.cpow_add (-s - 1) 1 hune
      rw [Complex.cpow_one, show (-s - 1 + 1 : ℂ) = -s from by ring] at h
      exact h
    rw [fractC_eq_sub_floor, hcpow]
    ring
  -- the first integral
  have hP1 : (∫ u in Ioi (1:ℝ), (u : ℂ) ^ (-s)) = 1 / (s - 1) := by
    have hre : (-s).re < -1 := by simp only [neg_re]; linarith
    rw [integral_Ioi_cpow_of_lt hre one_pos]
    have h1 : ((1:ℝ) : ℂ) = 1 := by norm_num
    rw [h1, Complex.one_cpow]
    have : (-s + 1) = -(s - 1) := by ring
    rw [this]
    field_simp
  -- the second integral
  have hP2 : (∫ u in Ioi (1:ℝ), (u : ℂ) ^ (-s - 1) * ((⌊u⌋ : ℤ) : ℂ)) = riemannZeta s / s := by
    have hswap := integral_tsum_of_summable_integral_norm
      (F := fun n : ℕ => floorPiece s n) (μ := volume.restrict (Ioi (1:ℝ)))
      (fun n => integrableOn_floorPiece hs0 n) (summable_integral_norm_floorPiece hs)
    have hlhs : (∑' n : ℕ, ∫ u in Ioi (1:ℝ), floorPiece s n u)
        = riemannZeta s / s := by
      have hEq : ∀ n : ℕ, (∫ u in Ioi (1:ℝ), floorPiece s n u) = ((n : ℂ) + 1) ^ (-s) / s :=
        fun n => integral_floorPiece hs0 n
      rw [tsum_congr hEq]
      rw [tsum_div_const]
      congr 1
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
      refine tsum_congr fun n => ?_
      rw [Complex.cpow_neg, one_div]
    have hrhs : (∫ u in Ioi (1:ℝ), ∑' n : ℕ, floorPiece s n u)
        = ∫ u in Ioi (1:ℝ), (u : ℂ) ^ (-s - 1) * ((⌊u⌋ : ℤ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      exact tsum_floorPiece hu
    rw [← hrhs, ← hswap, hlhs]
  rw [hsplit, hP1, hP2]

/-! ### Holomorphy of `gTail` on the half-plane `Re s > 0` -/

lemma locallyIntegrableOn_fractTail : LocallyIntegrableOn fractTail (Ioi (0:ℝ)) volume := by
  intro x hx
  refine ⟨Ioo (x / 2) (x + 1), ?_, ?_⟩
  · refine mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ?_ ?_)
    · have : (0:ℝ) < x := hx
      linarith
    · linarith
  · refine Measure.integrableOn_of_bounded (M := 1) ?_ ?_ ?_
    · exact (measure_Ioo_lt_top).ne
    · exact (measurable_fractC.indicator measurableSet_Ioi).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun u => ?_
      by_cases hu : u ∈ Ioi (1:ℝ)
      · rw [fractTail, Set.indicator_of_mem hu]
        exact norm_fractC_le_one u
      · rw [fractTail, Set.indicator_of_notMem hu, norm_zero]
        norm_num

lemma isBigO_fractTail_atTop : fractTail =O[atTop] fun x : ℝ => x ^ (-(0:ℝ)) := by
  refine Asymptotics.isBigO_of_le _ fun x => ?_
  rw [neg_zero, Real.rpow_zero]
  by_cases hx : x ∈ Ioi (1:ℝ)
  · rw [fractTail, Set.indicator_of_mem hx]
    simpa using norm_fractC_le_one x
  · rw [fractTail, Set.indicator_of_notMem hx, norm_zero]
    simp

lemma isBigO_fractTail_zero (b : ℝ) : fractTail =O[𝓝[>] (0:ℝ)] fun x : ℝ => x ^ (-b) := by
  have hzero : fractTail =ᶠ[𝓝[>] (0:ℝ)] fun _ => (0:ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one)] with x hx
    have : x ∉ Ioi (1:ℝ) := by
      simp only [mem_Ioi, not_lt]
      exact hx.2.le
    rw [fractTail, Set.indicator_of_notMem this]
  exact hzero.trans_isBigO (Asymptotics.isBigO_zero _ _)

lemma differentiableAt_gTail {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ gTail s := by
  have hmellin : DifferentiableAt ℂ (mellin fractTail) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
      locallyIntegrableOn_fractTail isBigO_fractTail_atTop ?_ (isBigO_fractTail_zero _) ?_
    · simpa using hs
    · simp only [neg_re]
      linarith
  have hcomp : DifferentiableAt ℂ (fun s : ℂ => mellin fractTail (-s)) s := by
    exact hmellin.comp s (differentiable_neg.differentiableAt)
  refine hcomp.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun z => gTail_eq_mellin z

/-! ### The identity theorem -/

/-- The domain `{Re s > 0} \ {1}`, on which `gTail` and `1/(s-1) - ζ(s)/s` are both analytic. -/
def punctHalfPlane : Set ℂ := {s : ℂ | 0 < s.re} \ {1}

lemma isOpen_punctHalfPlane : IsOpen punctHalfPlane := by
  refine IsOpen.sdiff ?_ isClosed_singleton
  exact isOpen_lt continuous_const Complex.continuous_re

lemma isPreconnected_punctHalfPlane : IsPreconnected punctHalfPlane := by
  set A : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im} with hA
  set B : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0} with hB
  set C : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1} with hC
  set D : Set ℂ := {s : ℂ | 1 < s.re} with hD
  have hAc : IsPreconnected A :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hBc : IsPreconnected B :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hCc : IsPreconnected C :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hDc : IsPreconnected D := (convex_halfSpace_re_gt 1).isPreconnected
  have hCA : IsPreconnected (C ∪ A) := by
    refine IsPreconnected.union (⟨1/2, 1⟩ : ℂ) ?_ ?_ hCc hAc
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩
  have hCAB : IsPreconnected ((C ∪ A) ∪ B) := by
    refine IsPreconnected.union (⟨1/2, -1⟩ : ℂ) ?_ ?_ hCA hBc
    · exact Or.inl ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩
  have hall : IsPreconnected (((C ∪ A) ∪ B) ∪ D) := by
    refine IsPreconnected.union (⟨2, 1⟩ : ℂ) ?_ ?_ hCAB hDc
    · exact Or.inl (Or.inr ⟨by norm_num, by norm_num⟩)
    · show (1:ℝ) < (2:ℝ)
      norm_num
  have hset : punctHalfPlane = ((C ∪ A) ∪ B) ∪ D := by
    ext z
    constructor
    · rintro ⟨hz, hz1⟩
      have hzre : 0 < z.re := hz
      rcases lt_trichotomy z.im 0 with him | him | him
      · exact Or.inl (Or.inr ⟨hzre, him⟩)
      · -- z is real
        rcases lt_trichotomy z.re 1 with hre | hre | hre
        · exact Or.inl (Or.inl (Or.inl ⟨hzre, hre⟩))
        · exact absurd (Complex.ext hre him) hz1
        · exact Or.inr hre
      · exact Or.inl (Or.inl (Or.inr ⟨hzre, him⟩))
    · rintro ((((⟨h1, h2⟩) | (⟨h1, h2⟩)) | ⟨h1, h2⟩) | h)
      · exact ⟨h1, by intro hc; rw [hc] at h2; simp at h2⟩
      · exact ⟨h1, by intro hc; rw [hc] at h2; simp at h2⟩
      · exact ⟨h1, by intro hc; rw [hc] at h2; simp at h2⟩
      · have hre1 : (1:ℝ) < z.re := h
        refine ⟨by simp only [mem_setOf_eq]; linarith, ?_⟩
        intro hc
        rw [hc] at hre1
        simp at hre1
  rw [hset]
  exact hall

/-- The explicit formula, analytic on the punctured half-plane. -/
def gModel (s : ℂ) : ℂ := 1 / (s - 1) - riemannZeta s / s

lemma differentiableOn_gModel : DifferentiableOn ℂ gModel punctHalfPlane := by
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  have hs0' : (0:ℝ) < s.re := hs0
  have hsne : s ≠ 0 := by
    intro h; rw [h] at hs0'; simp at hs0'
  have hs1' : s ≠ 1 := hs1
  have h1 : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - 1)) s := by
    refine DifferentiableAt.div (differentiableAt_const 1) ?_ ?_
    · exact (differentiableAt_id.sub (differentiableAt_const 1))
    · intro hc
      exact hs1' (by linear_combination hc)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => riemannZeta z / z) s :=
    (differentiableAt_riemannZeta hs1').div differentiableAt_id hsne
  exact ((h1.sub h2)).differentiableWithinAt

lemma differentiableOn_gTail : DifferentiableOn ℂ gTail punctHalfPlane := by
  intro s hs
  exact (differentiableAt_gTail hs.1).differentiableWithinAt

/-- `gTail` agrees with the explicit formula on the whole punctured half-plane. -/
lemma gTail_eq_gModel {s : ℂ} (hs : s ∈ punctHalfPlane) : gTail s = gModel s := by
  have hopen := isOpen_punctHalfPlane
  have hana1 : AnalyticOnNhd ℂ gTail punctHalfPlane :=
    differentiableOn_gTail.analyticOnNhd hopen
  have hana2 : AnalyticOnNhd ℂ gModel punctHalfPlane :=
    differentiableOn_gModel.analyticOnNhd hopen
  have h2mem : (2 : ℂ) ∈ punctHalfPlane := by
    constructor
    · show (0:ℝ) < (2:ℂ).re
      norm_num
    · intro hc
      have := congrArg Complex.re hc
      norm_num at this
  have hlocal : gTail =ᶠ[𝓝 (2 : ℂ)] gModel := by
    have hD : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      show (1:ℝ) < (2:ℂ).re
      norm_num
    refine Filter.eventuallyEq_of_mem (hD.mem_nhds hmem) fun z hz => ?_
    exact gTail_eq_of_one_lt_re hz
  exact hana1.eqOn_of_preconnected_of_eventuallyEq hana2 isPreconnected_punctHalfPlane h2mem
    hlocal hs

/-! ## The main formula -/

/-- **The Mellin transform of the fractional part of the reciprocal.**
For `0 < Re s < 1`, `∫_0^∞ {1/x} x^{s-1} dx = -ζ(s)/s`. -/
theorem zetaFractMellin : ZetaFractMellinFormula := by
  intro s h0 h1
  have hsne : s ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
  -- convergence
  have hconv : MellinConvergent fractInv s := by
    have hsplit : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi (0:ℝ) := Ioc_union_Ioi_eq_Ioi zero_le_one
    rw [MellinConvergent, ← hsplit]
    refine IntegrableOn.union ?_ ?_
    · -- on `(0,1]` we bound `{1/x}` by `1`
      have hdom : IntegrableOn (fun u : ℝ => u ^ (s.re - 1)) (Ioc 0 1) := by
        have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := s.re - 1)
          (by linarith)
        rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
      have hmeas : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ (s - 1) • fractInv u)
          (volume.restrict (Ioc (0:ℝ) 1)) := by
        refine AEStronglyMeasurable.mul ?_ ?_
        · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
          exact (Complex.continuousAt_ofReal_cpow_const _ _
            (Or.inr (ne_of_gt (Ioc_subset_Ioi_self ht)))).continuousWithinAt
        · exact (Complex.measurable_ofReal.comp (measurable_fract.comp
            measurable_inv)).aestronglyMeasurable
      refine Integrable.mono' hdom hmeas ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
      have hu0 : (0:ℝ) < u := hu.1
      rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      have hfr : ‖fractInv u‖ ≤ 1 := by
        rw [fractInv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Int.fract_nonneg _)]
        exact (Int.fract_lt_one _).le
      have hre : (s - 1).re = s.re - 1 := by simp
      have h2 : (0:ℝ) ≤ u ^ ((s - 1).re) := Real.rpow_nonneg hu0.le _
      rw [hre] at h2 ⊢
      nlinarith
    · -- on `(1,∞)` we have `{1/x} = 1/x`
      have hEq : ∀ u ∈ Ioi (1:ℝ), (u : ℂ) ^ (s - 1) • fractInv u = (u : ℂ) ^ (s - 2) := by
        intro u hu
        have hu0 : (0:ℝ) < u := lt_trans one_pos hu
        have hune : (u : ℂ) ≠ 0 := by simpa using ne_of_gt hu0
        have hfr : fractInv u = ((u⁻¹ : ℝ) : ℂ) := by
          rw [fractInv, Int.fract_eq_self.2 ⟨by positivity, by
            rw [inv_lt_one_iff₀]; exact Or.inr hu⟩]
        rw [hfr, smul_eq_mul, Complex.ofReal_inv]
        rw [show (s - 2 : ℂ) = (s - 1) + (-1) from by ring, Complex.cpow_add _ _ hune]
        rw [Complex.cpow_neg_one]
      rw [integrableOn_congr_fun hEq measurableSet_Ioi]
      refine integrableOn_Ioi_cpow_of_lt ?_ one_pos
      simp only [sub_re]
      norm_num
      linarith
  refine ⟨hconv, ?_⟩
  -- the value
  rw [show fractInv = fun x : ℝ => fractC x⁻¹ from rfl, mellin_comp_inv fractC s]
  -- split `mellin fractC (-s)` into the head and the tail
  have hhead : IntegrableOn (fun u : ℝ => (u : ℂ) ^ ((-s) - 1) • fractC u) (Ioc 0 1) := by
    have := integrableOn_head h1
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioc
    rw [smul_eq_mul]
  have htail : IntegrableOn (fun u : ℝ => (u : ℂ) ^ ((-s) - 1) • fractC u) (Ioi 1) := by
    have := integrableOn_tail h0
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [smul_eq_mul]
  have hsplit : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi (0:ℝ) := Ioc_union_Ioi_eq_Ioi zero_le_one
  have hmellin : mellin fractC (-s)
      = (∫ u in Ioc (0:ℝ) 1, (u : ℂ) ^ ((-s) - 1) • fractC u)
        + ∫ u in Ioi (1:ℝ), (u : ℂ) ^ ((-s) - 1) • fractC u := by
    rw [mellin, ← hsplit]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hhead htail
  have hheadval : (∫ u in Ioc (0:ℝ) 1, (u : ℂ) ^ ((-s) - 1) • fractC u) = 1 / (1 - s) := by
    have hEq : ∀ u ∈ Ioo (0:ℝ) 1, (u : ℂ) ^ ((-s) - 1) • fractC u = (u : ℂ) ^ (-s) := by
      intro u hu
      obtain ⟨hu0, hu1⟩ := hu
      have hune : (u : ℂ) ≠ 0 := by simpa using ne_of_gt hu0
      have hfr : fractC u = (u : ℂ) := by
        rw [fractC, Int.fract_eq_self.2 ⟨hu0.le, hu1⟩]
      have hcpow : (u : ℂ) ^ (-s) = (u : ℂ) ^ ((-s) - 1) * (u : ℂ) := by
        have h := Complex.cpow_add ((-s) - 1) 1 hune
        rw [Complex.cpow_one, show ((-s) - 1 + 1 : ℂ) = -s from by ring] at h
        exact h
      rw [hfr, smul_eq_mul, hcpow]
    have hne1 : (1 : ℂ) - s ≠ 0 := by
      intro hc
      exact hs1 (by linear_combination -hc)
    rw [← setIntegral_congr_set (Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := 1)),
      setIntegral_congr_fun measurableSet_Ioo hEq,
      setIntegral_congr_set (Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := 1)),
      ← intervalIntegral.integral_of_le zero_le_one,
      integral_cpow (Or.inl (by simp only [neg_re]; linarith))]
    rw [show ((1:ℝ) : ℂ) = 1 from by norm_num, Complex.one_cpow,
      show ((0:ℝ) : ℂ) = 0 from by norm_num, Complex.zero_cpow (by
        intro hc
        exact hs1 (by linear_combination -hc))]
    rw [show (-s + 1 : ℂ) = 1 - s from by ring]
    ring
  have htailval : (∫ u in Ioi (1:ℝ), (u : ℂ) ^ ((-s) - 1) • fractC u) = gTail s := by
    rw [gTail]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [smul_eq_mul]
  have hne1 : (1 : ℂ) - s ≠ 0 := by
    intro hc
    exact hs1 (by linear_combination -hc)
  have hne1' : s - 1 ≠ 0 := by
    intro hc
    exact hs1 (by linear_combination hc)
  rw [hmellin, hheadval, htailval,
    gTail_eq_gModel ⟨h0, by simpa using hs1⟩, gModel]
  field_simp
  ring

end NB17ZetaFract
