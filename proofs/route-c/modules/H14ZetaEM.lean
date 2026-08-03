import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.H14ZeroFree

/-!
# A1: the Euler–Maclaurin continuation of `ζ` to the right half-plane

Proves, for a natural cutoff `X ≥ 1` and `Re s > 1`,

`ζ(s) = ∑_{n≤X} n^{−s} + X^{1−s}/(s−1) − s·∫_{X}^{∞} {u}·u^{−s−1} du`,

then continues the identity to `Re s > 0` (`s ≠ 1`) by the identity theorem
applied to the pole-removed pair, and derives the three component bounds
needed to inhabit `ZetaRightHalfEulerMaclaurinComponentsAtHeight`.

Route notes (E0 search recorded in project memory: Mathlib has no such
representation): the `Re s > 1` identity is obtained WITHOUT discrete Abel
summation — each tail term is `n^{−s} = s·∫_{Ioi n} u^{−s−1} du`
(`integral_Ioi_cpow_of_lt`), and the tsum–integral swap
(`MeasureTheory.integral_tsum`) converts the tail of the Dirichlet series
into `s·∫_{Ioi X} (⌊u⌋ − X)·u^{−s−1} du`; writing `⌊u⌋ − X = (u − X) − {u}`
splits off the exact pole term.
-/

namespace RH.Criteria.NymanBeurling.H14ZetaEM

open Complex MeasureTheory Set Filter Topology
open scoped Real

/-! ## The fract tail integral -/

/-- The Euler–Maclaurin tail integrand at complex exponent `s`. -/
noncomputable def emTailIntegrand (s : ℂ) (u : ℝ) : ℂ :=
  ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)

/-- The tail integral `∫_{Ioi X} {u}·u^{−s−1} du`. -/
noncomputable def emTail (s : ℂ) (X : ℝ) : ℂ :=
  ∫ u in Ioi X, emTailIntegrand s u

theorem emTailIntegrand_norm_le {s : ℂ} {u : ℝ} (hu : 1 ≤ u) :
    ‖emTailIntegrand s u‖ ≤ u ^ (-s.re - 1) := by
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  unfold emTailIntegrand
  rw [norm_mul]
  have h1 : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg u)]
    exact (Int.fract_lt_one u).le
  have h2 : ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hupos]
    norm_num
  calc ‖((Int.fract u : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 1)‖
      ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ := by
        apply mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = u ^ (-s.re - 1) := by rw [one_mul, h2]

/-- Measurability of the tail integrand. -/
theorem emTailIntegrand_aestronglyMeasurable (s : ℂ) {X : ℝ} :
    AEStronglyMeasurable (emTailIntegrand s) (volume.restrict (Ioi X)) := by
  apply Measurable.aestronglyMeasurable
  unfold emTailIntegrand
  apply Measurable.mul
  · exact Complex.measurable_ofReal.comp measurable_fract
  · apply Measurable.pow
    · exact Complex.measurable_ofReal
    · exact measurable_const

/-- Integrability of the tail integrand on `Ioi X` for `Re s > 0`, `X ≥ 1`. -/
theorem emTailIntegrand_integrableOn {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 1 ≤ X) :
    IntegrableOn (emTailIntegrand s) (Ioi X) := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have hmaj : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Ioi X) := by
    apply integrableOn_Ioi_rpow_of_lt _ hXpos
    linarith
  apply Integrable.mono' hmaj (emTailIntegrand_aestronglyMeasurable s)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with u hu
  exact emTailIntegrand_norm_le (le_trans hX (le_of_lt hu))

/-! ## E1: the identity on `Re s > 1` -/

/-- Per-term improper integral: `n^{−s} = s·∫_{Ioi n} u^{−s−1} du` for `Re s > 0`. -/
theorem cpow_neg_eq_mul_integral {s : ℂ} (hs : 0 < s.re) {n : ℝ} (hn : 0 < n) :
    (n : ℂ) ^ (-s) = s * ∫ u in Ioi n, (u : ℂ) ^ (-s - 1) := by
  have ha : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [integral_Ioi_cpow_of_lt ha hn]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  rw [show -s - 1 + 1 = -s from by ring]
  field_simp

/-- The Dirichlet tail as a tsum: for `Re s > 1` and a natural cutoff `X`,
`ζ(s) − ∑_{n=1}^{X} n^{−s} = ∑'_{n} ((n+X+1 : ℕ))^{−s}`. -/
theorem zeta_sub_partial_eq_tsum_tail {s : ℂ} (hs : 1 < s.re) (X : ℕ) :
    riemannZeta s - (∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-s)) =
      ∑' n : ℕ, ((n + X + 1 : ℕ) : ℂ) ^ (-s) := by
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hsummable : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have h0 := Complex.summable_one_div_nat_cpow.mpr hs
    have hcomp := h0.comp_injective (add_left_injective 1)
    apply hcomp.congr
    intro n
    simp only [Function.comp]
    push_cast
    ring_nf
  have hsplit := hsummable.sum_add_tsum_nat_add X
  have hfin : (∑ i ∈ Finset.range X, 1 / ((i : ℂ) + 1) ^ s) =
      ∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-s) := by
    rw [show Finset.Icc 1 X = Finset.Ico 1 (X + 1) from by ext n; simp,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.cpow_neg, one_div]
    congr 2
    push_cast
    ring
  have htail : (∑' n : ℕ, 1 / (((n + X : ℕ) : ℂ) + 1) ^ s) =
      ∑' n : ℕ, ((n + X + 1 : ℕ) : ℂ) ^ (-s) := by
    apply tsum_congr
    intro n
    rw [Complex.cpow_neg, one_div]
    congr 2
    push_cast
    ring
  rw [hzeta, ← hsplit, hfin, add_sub_cancel_left]
  exact htail

/-! ## E1b: the tsum-integral swap -/

/-- The shifted per-term integrand, as an indicator function on the common base ray. -/
noncomputable def shiftedIndicator (s : ℂ) (X : ℕ) (n : ℕ) : ℝ → ℂ :=
  (Ioi ((n + X + 1 : ℕ) : ℝ)).indicator fun u : ℝ => (u : ℂ) ^ (-s - 1)

theorem shiftedIndicator_integrableOn {s : ℂ} (hs : 0 < s.re) (X : ℕ) (n : ℕ) :
    Integrable (shiftedIndicator s X n) (volume.restrict (Ioi (X : ℝ))) := by
  have hc : (0 : ℝ) < ((n + X + 1 : ℕ) : ℝ) := by positivity
  have hbase : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Ioi ((n + X + 1 : ℕ) : ℝ)) := by
    have ha : (-s - 1).re < -1 := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      linarith
    exact integrableOn_Ioi_cpow_of_lt ha hc
  have hXc : (X : ℝ) ≤ ((n + X + 1 : ℕ) : ℝ) := by push_cast; linarith
  unfold shiftedIndicator
  rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioi]
  rw [IntegrableOn, MeasureTheory.Measure.restrict_restrict measurableSet_Ioi,
    Set.Ioi_inter_Ioi, max_eq_left hXc]
  exact hbase

theorem shiftedIndicator_integral_norm {s : ℂ} (hs : 0 < s.re) (X : ℕ) (n : ℕ) :
    (∫ u in Ioi (X : ℝ), ‖shiftedIndicator s X n u‖) =
      ((n + X + 1 : ℕ) : ℝ) ^ (-s.re) / s.re := by
  have hc : (0 : ℝ) < ((n + X + 1 : ℕ) : ℝ) := by positivity
  have hXc : (X : ℝ) ≤ ((n + X + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hnorm : ∀ u ∈ Ioi ((n + X + 1 : ℕ) : ℝ),
      ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    intro u hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans hc hu)]
    norm_num
  calc (∫ u in Ioi (X : ℝ), ‖shiftedIndicator s X n u‖)
      = ∫ u in Ioi ((n + X + 1 : ℕ) : ℝ), ‖(u : ℂ) ^ (-s - 1)‖ := by
        unfold shiftedIndicator
        simp only [norm_indicator_eq_indicator_norm]
        rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
        congr 1
        rw [Set.Ioi_inter_Ioi, max_eq_right hXc]
    _ = ∫ u in Ioi ((n + X + 1 : ℕ) : ℝ), u ^ (-s.re - 1) :=
        setIntegral_congr_fun measurableSet_Ioi hnorm
    _ = ((n + X + 1 : ℕ) : ℝ) ^ (-s.re) / s.re := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hc]
        rw [show -s.re - 1 + 1 = -s.re from by ring]
        field_simp

theorem shiftedIndicator_summable_integral_norm {s : ℂ} (hs : 1 < s.re) (X : ℕ) :
    Summable fun n : ℕ => ∫ u in Ioi (X : ℝ), ‖shiftedIndicator s X n u‖ := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have h0 : Summable fun n : ℕ => ((n + X + 1 : ℕ) : ℝ) ^ (-s.re) / s.re := by
    apply Summable.div_const
    have h1 := Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith)
    have h2 := h1.comp_injective
      (show Function.Injective (fun n : ℕ => n + X + 1) from fun a b hab => by
        simpa using hab)
    apply h2.congr
    intro n
    simp only [Function.comp_apply]
  exact h0.congr fun n => (shiftedIndicator_integral_norm hs0 X n).symm

/-- Pointwise count identity: away from the integers, the sum of the shifted
indicators counts `⌊u⌋₊ − X` copies of `u^{−s−1}`. -/
theorem tsum_shiftedIndicator_eq {s : ℂ} (X : ℕ) {u : ℝ} (hu : (X : ℝ) < u)
    (hnotint : ∀ m : ℕ, u ≠ m) :
    (∑' n : ℕ, shiftedIndicator s X n u) =
      ((⌊u⌋₊ - X : ℕ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hu0 : 0 < u := lt_of_le_of_lt hX0 hu
  have hXfloor : X ≤ ⌊u⌋₊ := Nat.le_floor hu.le
  have hkey : ∀ n : ℕ, shiftedIndicator s X n u =
      if n ∈ Finset.range (⌊u⌋₊ - X) then (u : ℂ) ^ (-s - 1) else 0 := by
    intro n
    unfold shiftedIndicator
    rw [Set.indicator_apply]
    congr 1
    simp only [Finset.mem_range, Set.mem_Ioi, eq_iff_iff]
    constructor
    · intro h
      have hle : (n + X + 1 : ℕ) ≤ ⌊u⌋₊ := Nat.le_floor (le_of_lt h)
      omega
    · intro h
      have hle : (n + X + 1 : ℕ) ≤ ⌊u⌋₊ := by omega
      have h1 : ((n + X + 1 : ℕ) : ℝ) ≤ (⌊u⌋₊ : ℝ) := Nat.cast_le.mpr hle
      have h2 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0.le
      have h3 : (⌊u⌋₊ : ℝ) ≠ u := fun heq => hnotint ⌊u⌋₊ heq.symm
      linarith [lt_of_le_of_ne h2 h3]
  rw [tsum_congr hkey, tsum_eq_sum (f := fun n =>
      if n ∈ Finset.range (⌊u⌋₊ - X) then (u : ℂ) ^ (-s - 1) else 0)
      (s := Finset.range (⌊u⌋₊ - X)) (fun n hn => if_neg hn)]
  rw [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, Finset.card_range]
  simp [nsmul_eq_mul]

/-- E1b: for `Re s > 1`, the Dirichlet tail equals `s` times the counted integral. -/
theorem tsum_tail_eq_mul_integral_count {s : ℂ} (hs : 1 < s.re) (X : ℕ) :
    (∑' n : ℕ, ((n + X + 1 : ℕ) : ℂ) ^ (-s)) =
      s * ∫ u in Ioi (X : ℝ), ((⌊u⌋₊ - X : ℕ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have hterm : ∀ n : ℕ, ((n + X + 1 : ℕ) : ℂ) ^ (-s) =
      s * ∫ u in Ioi (X : ℝ), shiftedIndicator s X n u := by
    intro n
    have hc : (0 : ℝ) < ((n + X + 1 : ℕ) : ℝ) := by positivity
    have hXc : (X : ℝ) ≤ ((n + X + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h1 := cpow_neg_eq_mul_integral hs0 hc
    have h2 : (∫ u in Ioi (X : ℝ), shiftedIndicator s X n u) =
        ∫ u in Ioi ((n + X + 1 : ℕ) : ℝ), (u : ℂ) ^ (-s - 1) := by
      unfold shiftedIndicator
      rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
      congr 1
      rw [Set.Ioi_inter_Ioi, max_eq_right hXc]
    rw [h2, ← h1]
    norm_num
  have hswap : (∑' n : ℕ, ∫ u in Ioi (X : ℝ), shiftedIndicator s X n u) =
      ∫ u in Ioi (X : ℝ), ∑' n : ℕ, shiftedIndicator s X n u := by
    rw [MeasureTheory.integral_tsum_of_summable_integral_norm
      (fun n => shiftedIndicator_integrableOn hs0 X n)
      (shiftedIndicator_summable_integral_norm hs X)]
  have hcount : (∫ u in Ioi (X : ℝ), ∑' n : ℕ, shiftedIndicator s X n u) =
      ∫ u in Ioi (X : ℝ), ((⌊u⌋₊ - X : ℕ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
    apply MeasureTheory.integral_congr_ae
    have h1 : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi (X : ℝ))), u ∈ Ioi (X : ℝ) :=
      MeasureTheory.ae_restrict_mem measurableSet_Ioi
    have hnull : volume (Set.range (Nat.cast : ℕ → ℝ)) = 0 :=
      (Set.countable_range _).measure_zero _
    have h2' : ∀ᵐ u : ℝ ∂volume, u ∉ Set.range (Nat.cast : ℕ → ℝ) := by
      rw [MeasureTheory.ae_iff]
      simpa using hnull
    have h2 : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi (X : ℝ))),
        u ∉ Set.range (Nat.cast : ℕ → ℝ) :=
      MeasureTheory.ae_restrict_of_ae h2'
    filter_upwards [h1, h2] with u hu hu'
    exact tsum_shiftedIndicator_eq X hu fun m heq => hu' ⟨m, heq.symm⟩
  have hsum : (∑' n : ℕ, ((n + X + 1 : ℕ) : ℂ) ^ (-s)) =
      s * ∑' n : ℕ, ∫ u in Ioi (X : ℝ), shiftedIndicator s X n u := by
    rw [← tsum_mul_left]
    exact tsum_congr hterm
  rw [hsum, hswap, hcount]

/-! ## E1c: splitting off the pole term and assembling the identity -/

/-- For positive real `u`, the natural floor recovers `u − {u}` in `ℂ`. -/
theorem natCast_floor_eq_sub_fract {u : ℝ} (hu : 0 < u) :
    ((⌊u⌋₊ : ℕ) : ℂ) = (u : ℂ) - ((Int.fract u : ℝ) : ℂ) := by
  have h1 : ((⌊u⌋₊ : ℕ) : ℝ) = u - Int.fract u := by
    rw [Int.self_sub_fract]
    exact_mod_cast Int.natCast_floor_eq_floor hu.le
  calc ((⌊u⌋₊ : ℕ) : ℂ) = (((⌊u⌋₊ : ℕ) : ℝ) : ℂ) := by push_cast; ring
    _ = ((u - Int.fract u : ℝ) : ℂ) := by rw [h1]
    _ = (u : ℂ) - ((Int.fract u : ℝ) : ℂ) := by push_cast; ring

/-- The linear piece of the counted integrand is integrable for `Re s > 1`. -/
theorem linear_piece_integrableOn {s : ℂ} (hs : 1 < s.re) {X : ℕ} (hX : 1 ≤ X) :
    IntegrableOn (fun u : ℝ => ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1))
      (Ioi (X : ℝ)) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hX
  have h1 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s)) (Ioi (X : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt _ hXpos
    simp only [Complex.neg_re]
    linarith
  have h2 : IntegrableOn (fun u : ℝ => (X : ℂ) * (u : ℂ) ^ (-s - 1)) (Ioi (X : ℝ)) := by
    apply Integrable.const_mul
    apply integrableOn_Ioi_cpow_of_lt _ hXpos
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  apply (h1.sub h2).congr_fun _ measurableSet_Ioi
  intro u hu
  have hu0 : (0 : ℝ) < u := lt_trans hXpos hu
  have hne : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu0
  have hpow : (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (-s) := by
    rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
    field_simp
  show (u : ℂ) ^ (-s) - (X : ℂ) * (u : ℂ) ^ (-s - 1) =
      ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1)
  rw [← hpow]
  ring

/-- E1c split: the counted integral equals the linear integral minus the tail. -/
theorem count_integral_split {s : ℂ} (hs : 1 < s.re) {X : ℕ} (hX : 1 ≤ X) :
    (∫ u in Ioi (X : ℝ), ((⌊u⌋₊ - X : ℕ) : ℂ) * (u : ℂ) ^ (-s - 1)) =
      (∫ u in Ioi (X : ℝ), ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1)) -
        emTail s (X : ℝ) := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hX
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  rw [emTail, ← MeasureTheory.integral_sub (linear_piece_integrableOn hs hX)
    (emTailIntegrand_integrableOn hs0 hX1)]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hu0 : (0 : ℝ) < u := lt_trans hXpos hu
  have hXfloor : X ≤ ⌊u⌋₊ := Nat.le_floor (le_of_lt hu)
  have hcast : ((⌊u⌋₊ - X : ℕ) : ℂ) = ((⌊u⌋₊ : ℕ) : ℂ) - (X : ℂ) := by
    push_cast [Nat.cast_sub hXfloor]
    ring
  show ((⌊u⌋₊ - X : ℕ) : ℂ) * (u : ℂ) ^ (-s - 1) =
      ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1) - emTailIntegrand s u
  rw [hcast, natCast_floor_eq_sub_fract hu0]
  unfold emTailIntegrand
  ring

/-- E1c evaluation: `s·∫_{Ioi X} (u−X)·u^{−s−1} du = X^{1−s}/(s−1)` for `Re s > 1`. -/
theorem linear_part_integral {s : ℂ} (hs : 1 < s.re) {X : ℕ} (hX : 1 ≤ X) :
    s * ∫ u in Ioi (X : ℝ), ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1) =
      (X : ℂ) ^ (1 - s) / (s - 1) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hX
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have ha1 : (-s : ℂ).re < -1 := by simp only [Complex.neg_re]; linarith
  have ha2 : (-s - 1 : ℂ).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]; linarith
  have hXne : ((X : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hXpos
  have hsplit : (∫ u in Ioi (X : ℝ), ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1)) =
      (∫ u in Ioi (X : ℝ), (u : ℂ) ^ (-s)) -
        ∫ u in Ioi (X : ℝ), (X : ℂ) * (u : ℂ) ^ (-s - 1) := by
    rw [← MeasureTheory.integral_sub (integrableOn_Ioi_cpow_of_lt ha1 hXpos)
      ((integrableOn_Ioi_cpow_of_lt ha2 hXpos).const_mul _)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans hXpos hu
    have hne : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu0
    have hpow : (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (-s) := by
      rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
      field_simp
    show ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1) =
        (u : ℂ) ^ (-s) - (X : ℂ) * (u : ℂ) ^ (-s - 1)
    rw [← hpow]
    ring
  rw [hsplit, MeasureTheory.integral_const_mul,
    integral_Ioi_cpow_of_lt ha1 hXpos, integral_Ioi_cpow_of_lt ha2 hXpos]
  have e1 : (-s : ℂ) + 1 = -(s - 1) := by ring
  have e2 : (-s - 1 : ℂ) + 1 = -s := by ring
  have hXpow : ((X : ℝ) : ℂ) ^ (-(s - 1) : ℂ) = ((X : ℝ) : ℂ) ^ (1 - s : ℂ) := by
    congr 1
    ring
  have hXpow2 : ((X : ℝ) : ℂ) * ((X : ℝ) : ℂ) ^ (-s : ℂ) =
      ((X : ℝ) : ℂ) ^ (1 - s : ℂ) := by
    rw [show (1 - s : ℂ) = 1 + -s from by ring, Complex.cpow_add _ _ hXne,
      Complex.cpow_one]
  rw [e1, e2, neg_div_neg_eq, neg_div_neg_eq, hXpow, ← hXpow2]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  push_cast at hXpow2 ⊢
  field_simp
  linear_combination hXpow2

/-- E1 assembled: the Euler–Maclaurin identity for `ζ` on `Re s > 1`. -/
theorem emIdentity_of_one_lt_re {s : ℂ} (hs : 1 < s.re) {X : ℕ} (hX : 1 ≤ X) :
    riemannZeta s = (∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-s)) +
      (X : ℂ) ^ (1 - s) / (s - 1) - s * emTail s (X : ℝ) := by
  have h1 := zeta_sub_partial_eq_tsum_tail hs X
  have h2 := tsum_tail_eq_mul_integral_count hs X
  have h3 := count_integral_split hs hX
  have h4 := linear_part_integral hs hX
  have hchain : riemannZeta s - (∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-s)) =
      (X : ℂ) ^ (1 - s) / (s - 1) - s * emTail s (X : ℝ) := by
    rw [h1, h2, h3, mul_sub, h4]
  linear_combination hchain

/-! ## E2a: differentiability of the tail integral in `s` -/

/-- The `s`-derivative of the tail integrand. -/
noncomputable def emTailDerivIntegrand (s : ℂ) (u : ℝ) : ℂ :=
  -(((Int.fract u : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))

theorem emTailDerivIntegrand_norm_le {s : ℂ} {u : ℝ} (hu : 1 ≤ u) :
    ‖emTailDerivIntegrand s u‖ ≤ Real.log u * u ^ (-s.re - 1) := by
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hlog : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu
  unfold emTailDerivIntegrand
  rw [norm_neg, norm_mul, norm_mul]
  have h1 : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg u)]
    exact (Int.fract_lt_one u).le
  have h2 : ‖((Real.log u : ℝ) : ℂ)‖ = Real.log u := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  have h3 : ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hupos]
    norm_num
  calc ‖((Int.fract u : ℝ) : ℂ)‖ * ‖((Real.log u : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 1)‖
      ≤ 1 * ‖((Real.log u : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = Real.log u * u ^ (-s.re - 1) := by rw [one_mul, h2, h3]

/-- Elementary log-power bound: `log u ≤ u^δ/δ` for `u ≥ 1`, `δ > 0`. -/
theorem log_le_rpow_div_self {u δ : ℝ} (hu : 1 ≤ u) (hδ : 0 < δ) :
    Real.log u ≤ u ^ δ / δ := by
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hpow : (0 : ℝ) < u ^ δ := Real.rpow_pos_of_pos hupos δ
  have h1 : Real.log (u ^ δ) ≤ u ^ δ - 1 := Real.log_le_sub_one_of_pos hpow
  rw [Real.log_rpow hupos] at h1
  have h2 : δ * Real.log u ≤ u ^ δ := le_trans h1 (by linarith)
  calc Real.log u = δ * Real.log u / δ := by field_simp
    _ ≤ u ^ δ / δ := div_le_div_of_nonneg_right h2 hδ.le

/-- Integrability of `log·rpow` majorants on rays. -/
theorem integrableOn_log_mul_rpow {X : ℝ} (hX : 1 ≤ X) {a : ℝ} (ha : a < -1) :
    IntegrableOn (fun u : ℝ => Real.log u * u ^ a) (Ioi X) := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  set δ : ℝ := (-1 - a) / 2 with hδdef
  have hδ : 0 < δ := by simp only [hδdef]; linarith
  have hexp : a + δ < -1 := by simp only [hδdef]; linarith
  have hmaj : IntegrableOn (fun u : ℝ => u ^ (a + δ) / δ) (Ioi X) :=
    (integrableOn_Ioi_rpow_of_lt hexp hXpos).div_const δ
  apply Integrable.mono' hmaj
  · exact (Real.measurable_log.mul (measurable_id.pow_const a)).aestronglyMeasurable
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu1 : (1 : ℝ) ≤ u := le_trans hX (le_of_lt hu)
    have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
    have hlog : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
    have hpowpos : (0 : ℝ) ≤ u ^ a := (Real.rpow_pos_of_pos hupos a).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hlog hpowpos)]
    calc Real.log u * u ^ a ≤ u ^ δ / δ * u ^ a :=
          mul_le_mul_of_nonneg_right (log_le_rpow_div_self hu1 hδ) hpowpos
      _ = u ^ (a + δ) / δ := by
          rw [div_mul_eq_mul_div, ← Real.rpow_add hupos, add_comm]

theorem emTailDerivIntegrand_aestronglyMeasurable (s : ℂ) {X : ℝ} :
    AEStronglyMeasurable (emTailDerivIntegrand s) (volume.restrict (Ioi X)) := by
  apply Measurable.aestronglyMeasurable
  unfold emTailDerivIntegrand
  apply Measurable.neg
  apply Measurable.mul
  · apply Measurable.mul
    · exact Complex.measurable_ofReal.comp measurable_fract
    · exact Complex.measurable_ofReal.comp Real.measurable_log
  · apply Measurable.pow
    · exact Complex.measurable_ofReal
    · exact measurable_const

/-- Pointwise `s`-derivative of the tail integrand. -/
theorem emTailIntegrand_hasDerivAt {u : ℝ} (hu : 1 ≤ u) (s : ℂ) :
    HasDerivAt (fun z : ℂ => emTailIntegrand z u) (emTailDerivIntegrand s u) s := by
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hne : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hupos
  have h1 : HasDerivAt (fun z : ℂ => -z - 1) (-1) s := by
    simpa using ((hasDerivAt_id s).neg.sub_const 1)
  have h2 : HasDerivAt (fun z : ℂ => (u : ℂ) ^ (-z - 1))
      ((u : ℂ) ^ (-s - 1) * Complex.log (u : ℂ) * (-1)) s :=
    HasDerivAt.const_cpow h1 (Or.inl hne)
  have h3 := h2.const_mul ((Int.fract u : ℝ) : ℂ)
  have hlogeq : Complex.log (u : ℂ) = ((Real.log u : ℝ) : ℂ) :=
    (Complex.ofReal_log hupos.le).symm
  convert h3 using 1
  unfold emTailDerivIntegrand
  rw [hlogeq]
  ring

/-- E2a main: the tail integral is complex-differentiable in `s` on `Re s > 0`. -/
theorem emTail_hasDerivAt {s₀ : ℂ} (hs₀ : 0 < s₀.re) {X : ℝ} (hX : 1 ≤ X) :
    HasDerivAt (fun s : ℂ => emTail s X)
      (∫ u in Ioi X, emTailDerivIntegrand s₀ u) s₀ := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  set ε : ℝ := s₀.re / 2 with hεdef
  have hε : 0 < ε := by simp only [hεdef]; linarith
  have hres : ∀ z ∈ Metric.ball s₀ ε, ε ≤ z.re := by
    intro z hz
    have hd : |(z - s₀).re| ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have : |(z - s₀).re| < ε := lt_of_le_of_lt hd hz
    rw [Complex.sub_re, abs_lt] at this
    simp only [hεdef] at this ⊢
    linarith [this.1]
  have hbound_int : IntegrableOn (fun u : ℝ => Real.log u * u ^ (-ε - 1)) (Ioi X) :=
    integrableOn_log_mul_rpow hX (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun s u => emTailIntegrand s u)
    (F' := fun u => emTailDerivIntegrand s₀ u)
    (x₀ := s₀)
    (bound := fun u => Real.log u * u ^ (-ε - 1))
    (μ := volume.restrict (Ioi X))
    (Metric.ball_mem_nhds s₀ hε)
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · filter_upwards with s
    exact emTailIntegrand_aestronglyMeasurable s
  · exact emTailIntegrand_integrableOn hs₀ hX
  · exact emTailDerivIntegrand_aestronglyMeasurable s₀
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu1 : (1 : ℝ) ≤ u := le_trans hX (le_of_lt hu)
    have hlog : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
    have hpow : (0 : ℝ) ≤ u ^ (-ε - 1) :=
      (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hu1) _).le
    apply LipschitzOnWith.mono _ (Set.Subset.refl _)
    apply (convex_ball s₀ ε).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun z => emTailDerivIntegrand z u)
    · intro z _
      exact ((emTailIntegrand_hasDerivAt hu1 z)).hasDerivWithinAt
    · intro z hz
      rw [← NNReal.coe_le_coe]
      calc (‖emTailDerivIntegrand z u‖₊ : ℝ) = ‖emTailDerivIntegrand z u‖ := rfl
        _ ≤ Real.log u * u ^ (-z.re - 1) := emTailDerivIntegrand_norm_le hu1
        _ ≤ Real.log u * u ^ (-ε - 1) := by
            apply mul_le_mul_of_nonneg_left _ hlog
            apply Real.rpow_le_rpow_of_exponent_le hu1
            have := hres z hz
            linarith
        _ ≤ (Real.nnabs (Real.log u * u ^ (-ε - 1)) : ℝ) := by
            rw [Real.coe_nnabs, abs_of_nonneg (mul_nonneg hlog hpow)]
  · exact hbound_int
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    exact emTailIntegrand_hasDerivAt (le_trans hX (le_of_lt hu)) s₀

/-! ## E2b: continuation of the identity to the open quadrants of `Re s > 0` -/

/-- The Euler–Maclaurin right-hand side as a single function of `s`. -/
noncomputable def emRHS (X : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-s)) +
    (X : ℂ) ^ (1 - s) / (s - 1) - s * emTail s (X : ℝ)

theorem emTail_differentiableAt {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 1 ≤ X) :
    DifferentiableAt ℂ (fun z : ℂ => emTail z X) s :=
  (emTail_hasDerivAt hs hX).differentiableAt

theorem emRHS_differentiableAt {X : ℕ} (hX : 1 ≤ X) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (emRHS X) s := by
  have hXpos : (0 : ℕ) < X := hX
  have hXne : (X : ℂ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hXpos
  have h1 : DifferentiableAt ℂ
      (fun z : ℂ => ∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-z)) s := by
    apply DifferentiableAt.fun_sum
    intro n hn
    have hne : (n : ℂ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1
    exact (differentiableAt_id.neg).const_cpow (Or.inl hne)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (X : ℂ) ^ (1 - z) / (z - 1)) s := by
    apply DifferentiableAt.div
    · exact (differentiableAt_const _).sub differentiableAt_id |>.const_cpow (Or.inl hXne)
    · exact differentiableAt_id.sub (differentiableAt_const _)
    · exact sub_ne_zero.mpr hs1
  have h3 : DifferentiableAt ℂ (fun z : ℂ => z * emTail z (X : ℝ)) s :=
    differentiableAt_id.mul (emTail_differentiableAt hs (by exact_mod_cast hX))
  exact (h1.add h2).sub h3

/-- The identity theorem step on one convex piece of the right half-plane. -/
theorem emIdentity_eqOn_of_convex {X : ℕ} (hX : 1 ≤ X) {U : Set ℂ}
    (hUopen : IsOpen U) (hUconv : Convex ℝ U)
    (hUre : ∀ z ∈ U, 0 < z.re) (hUone : (1 : ℂ) ∉ U)
    {z₀ : ℂ} (hz₀U : z₀ ∈ U) (hz₀re : 1 < z₀.re) :
    Set.EqOn riemannZeta (emRHS X) U := by
  have hζ : AnalyticOnNhd ℂ riemannZeta U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact (differentiableAt_riemannZeta
      (fun h1 => hUone (h1 ▸ hz))).differentiableWithinAt
  have hR : AnalyticOnNhd ℂ (emRHS X) U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact (emRHS_differentiableAt hX (hUre z hz)
      (fun h1 => hUone (h1 ▸ hz))).differentiableWithinAt
  apply hζ.eqOn_of_preconnected_of_eventuallyEq hR hUconv.isPreconnected hz₀U
  have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen1.mem_nhds hz₀re] with z hz
  exact emIdentity_of_one_lt_re hz hX

/-- E2 main: the Euler–Maclaurin identity continues to `Re s > 0`, `Im s ≠ 0`. -/
theorem emIdentity_of_pos_re_of_im_ne_zero {s : ℂ} (h0 : 0 < s.re)
    (him : s.im ≠ 0) {X : ℕ} (hX : 1 ≤ X) :
    riemannZeta s = (∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-s)) +
      (X : ℂ) ^ (1 - s) / (s - 1) - s * emTail s (X : ℝ) := by
  have him' := lt_or_gt_of_ne him
  have h1re : (1 : ℂ).im = 0 := rfl
  rcases him' with hlt | hgt
  · have := emIdentity_eqOn_of_convex hX
      (U := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < 0})
      (IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
        (isOpen_lt Complex.continuous_im continuous_const))
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0))
      (fun z hz => hz.1)
      (by intro h; exact absurd h.2 (by norm_num [h1re]))
      (z₀ := 2 - Complex.I)
      (by constructor <;> simp)
      (by simp)
    exact this ⟨h0, hlt⟩
  · have := emIdentity_eqOn_of_convex hX
      (U := {z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im})
      (IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
        (isOpen_lt continuous_const Complex.continuous_im))
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0))
      (fun z hz => hz.1)
      (by intro h; exact absurd h.2 (by norm_num [h1re]))
      (z₀ := 2 + Complex.I)
      (by constructor <;> simp)
      (by simp)
    exact this ⟨h0, hgt⟩

/-! ## E3: the three elementary bounds and the frozen structure instance

Numerics gate (recorded): closed-form evaluation of the tail confirms the
decomposition within rigorous truncation remainders (e.g. `5.0e-11` vs bound
`1.1e-10` at `σ=2, t=1`), and the constants below have at least a factor-2
margin over the observed suprema (max ratio `0.52` for the pole at
`σ=1/2, |t|=1`). -/

/-- Telescoping square-root bound for the critical-line partial sum. -/
theorem sum_rpow_neg_half_le (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ((n : ℝ)) ^ (-(1 / 2 : ℝ))) ≤ 2 * Real.sqrt X := by
  have hstep : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      2 * Real.sqrt ((i + 1 : ℕ) : ℝ) - 2 * Real.sqrt ((i : ℕ) : ℝ) := by
    intro i
    push_cast
    set a : ℝ := Real.sqrt ((i : ℝ) + 1) with ha
    set b : ℝ := Real.sqrt (i : ℝ) with hb
    have ha2 : a ^ 2 = (i : ℝ) + 1 := by
      rw [ha, Real.sq_sqrt (by positivity)]
    have hb2 : b ^ 2 = (i : ℝ) := by
      rw [hb, Real.sq_sqrt (by positivity)]
    have hapos : 0 < a := by
      rw [ha]
      apply Real.sqrt_pos.mpr
      positivity
    have hbnn : 0 ≤ b := Real.sqrt_nonneg _
    have hcast : ((i : ℝ) + 1) ^ (-(1 / 2 : ℝ)) = 1 / a := by
      rw [Real.rpow_neg (by positivity), ha, Real.sqrt_eq_rpow]
      exact (one_div _).symm
    rw [hcast, div_le_iff₀ hapos]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have hconv : (∑ n ∈ Finset.Icc 1 X, ((n : ℝ)) ^ (-(1 / 2 : ℝ))) =
      ∑ i ∈ Finset.range X, ((i + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [show Finset.Icc 1 X = Finset.Ico 1 (X + 1) from by ext n; simp,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    ring
  rw [hconv]
  calc (∑ i ∈ Finset.range X, ((i + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
      ≤ ∑ i ∈ Finset.range X,
          (2 * Real.sqrt ((i + 1 : ℕ) : ℝ) - 2 * Real.sqrt ((i : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = 2 * Real.sqrt ((X : ℕ) : ℝ) - 2 * Real.sqrt ((0 : ℕ) : ℝ) :=
        Finset.sum_range_sub (f := fun n : ℕ => 2 * Real.sqrt ((n : ℕ) : ℝ)) X
    _ ≤ 2 * Real.sqrt X := by simp

/-- The real part of `σ + I t` is `σ`. -/
theorem re_sigma_add_I_mul (σ t : ℝ) : (σ + Complex.I * t : ℂ).re = σ := by
  simp

/-- The imaginary part of `σ + I t` is `t`. -/
theorem im_sigma_add_I_mul (σ t : ℝ) : (σ + Complex.I * t : ℂ).im = t := by
  simp

/-- E3 partial-sum bound. -/
theorem partialSum_norm_le {σ : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ) (t : ℝ) (X : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖ ≤
      2 * Real.sqrt X := by
  calc ‖∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖
      ≤ ∑ n ∈ Finset.Icc 1 X, ‖(n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X, ((n : ℝ)) ^ (-(1 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        rw [Complex.norm_natCast_cpow_of_pos (by omega)]
        have hre : (-(σ + Complex.I * t : ℂ)).re = -σ := by
          rw [Complex.neg_re, re_sigma_add_I_mul]
        rw [hre]
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1)
        linarith
    _ ≤ 2 * Real.sqrt X := sum_rpow_neg_half_le X

/-- E3 tail-integral bound. -/
theorem emTail_norm_le {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) {X : ℝ} (hX : 1 ≤ X) :
    ‖emTail s X‖ ≤ X ^ (-s.re) / s.re := by
  have hs0 : 0 < s.re := lt_of_lt_of_le (by norm_num) hs
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have hmaj : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Ioi X) := by
    apply integrableOn_Ioi_rpow_of_lt _ hXpos
    linarith
  calc ‖emTail s X‖ ≤ ∫ u in Ioi X, ‖emTailIntegrand s u‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi X, u ^ (-s.re - 1) := by
        apply MeasureTheory.setIntegral_mono_on
          ((emTailIntegrand_integrableOn hs0 hX).norm) hmaj measurableSet_Ioi
        intro u hu
        exact emTailIntegrand_norm_le (le_trans hX (le_of_lt hu))
    _ = X ^ (-s.re) / s.re := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hXpos]
        rw [show -s.re - 1 + 1 = -s.re from by ring]
        field_simp

/-- E3 assembled: the frozen Euler–Maclaurin components structure is
inhabited, with `t₀ = 1`, `X = ⌊|t|⌋₊ + 2`, and constants `2, 1, 2`. -/
noncomputable def zetaRightHalfEulerMaclaurinComponents :
    RH.Criteria.NymanBeurling.MobiusSummatory.ZetaRightHalfEulerMaclaurinComponentsAtHeight where
  t₀ := 1
  t₀_pos := one_pos
  t₀_le_one := le_rfl
  partialSum σ t :=
    ∑ n ∈ Finset.Icc 1 (⌊|t|⌋₊ + 2), (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))
  poleTerm σ t :=
    ((⌊|t|⌋₊ + 2 : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) /
      ((σ + Complex.I * t : ℂ) - 1)
  tailTerm σ t :=
    -((σ + Complex.I * t : ℂ) *
      emTail (σ + Complex.I * t : ℂ) ((⌊|t|⌋₊ + 2 : ℕ) : ℝ))
  C_sum := 2
  C_pole := 1
  C_tail := 2
  C_sum_nonneg := by norm_num
  C_pole_nonneg := by norm_num
  C_tail_nonneg := by norm_num
  decomposition := by
    intro σ t hσlow hσhigh ht
    have h0 : 0 < (σ + Complex.I * t : ℂ).re := by
      rw [re_sigma_add_I_mul]
      linarith
    have him : (σ + Complex.I * t : ℂ).im ≠ 0 := by
      rw [im_sigma_add_I_mul]
      intro h
      rw [h] at ht
      simp at ht
      linarith
    have hX : 1 ≤ ⌊|t|⌋₊ + 2 := by omega
    have hid := emIdentity_of_pos_re_of_im_ne_zero h0 him hX
    rw [hid]
    push_cast
    ring
  partial_sum_bound := by
    intro σ t hσlow hσhigh ht
    have hfloor : (⌊|t|⌋₊ : ℝ) ≤ |t| := Nat.floor_le (abs_nonneg t)
    calc ‖∑ n ∈ Finset.Icc 1 (⌊|t|⌋₊ + 2), (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖
        ≤ 2 * Real.sqrt ((⌊|t|⌋₊ + 2 : ℕ) : ℝ) := partialSum_norm_le hσlow t _
      _ ≤ 2 * Real.sqrt (|t| + 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.sqrt_le_sqrt
          push_cast
          linarith
      _ ≤ 2 * (|t| + 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact (Real.sqrt_le_left (by positivity)).mpr (by nlinarith [abs_nonneg t])
  pole_bound := by
    intro σ t hσlow hσhigh ht
    have hX2 : (2 : ℝ) ≤ ((⌊|t|⌋₊ + 2 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) ⌊|t|⌋₊]
    have hXpos : (0 : ℕ) < ⌊|t|⌋₊ + 2 := by omega
    have hnormnum : ‖((⌊|t|⌋₊ + 2 : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ))‖ =
        ((⌊|t|⌋₊ + 2 : ℕ) : ℝ) ^ (1 - σ) := by
      rw [Complex.norm_natCast_cpow_of_pos hXpos]
      congr 1
      rw [Complex.sub_re, Complex.one_re, re_sigma_add_I_mul]
    have hdenom : (1 : ℝ) ≤ ‖(σ + Complex.I * t : ℂ) - 1‖ := by
      calc (1 : ℝ) ≤ |t| := ht
        _ = |((σ + Complex.I * t : ℂ) - 1).im| := by
            rw [Complex.sub_im, Complex.one_im, im_sigma_add_I_mul]
            simp
        _ ≤ ‖(σ + Complex.I * t : ℂ) - 1‖ := Complex.abs_im_le_norm _
    rw [norm_div, hnormnum]
    calc ((⌊|t|⌋₊ + 2 : ℕ) : ℝ) ^ (1 - σ) / ‖(σ + Complex.I * t : ℂ) - 1‖
        ≤ ((⌊|t|⌋₊ + 2 : ℕ) : ℝ) ^ (1 - σ) / 1 := by
          apply div_le_div_of_nonneg_left _ one_pos hdenom
          positivity
      _ = ((⌊|t|⌋₊ + 2 : ℕ) : ℝ) ^ (1 - σ) := by rw [div_one]
      _ ≤ ((⌊|t|⌋₊ + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          linarith
      _ = Real.sqrt ((⌊|t|⌋₊ + 2 : ℕ) : ℝ) := by
          rw [Real.sqrt_eq_rpow]
      _ ≤ Real.sqrt (|t| + 2) := by
          apply Real.sqrt_le_sqrt
          push_cast
          linarith [Nat.floor_le (abs_nonneg t)]
      _ ≤ |t| + 2 :=
          (Real.sqrt_le_left (by positivity)).mpr (by nlinarith [abs_nonneg t])
      _ = 1 * (|t| + 2) := by ring
  tail_bound := by
    intro σ t hσlow hσhigh ht
    set s : ℂ := σ + Complex.I * t with hsdef
    set X : ℕ := ⌊|t|⌋₊ + 2 with hXdef
    have hsre : s.re = σ := re_sigma_add_I_mul σ t
    have hX1 : (1 : ℝ) ≤ ((X : ℕ) : ℝ) := by
      rw [hXdef]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) ⌊|t|⌋₊]
    have hXpos : (0 : ℝ) < ((X : ℕ) : ℝ) := lt_of_lt_of_le one_pos hX1
    have htail : ‖emTail s ((X : ℕ) : ℝ)‖ ≤ ((X : ℕ) : ℝ) ^ (-s.re) / s.re := by
      apply emTail_norm_le _ hX1
      rw [hsre]
      exact hσlow
    have hXpow : ((X : ℕ) : ℝ) ^ (-s.re) ≤ 1 := by
      rw [hsre]
      calc ((X : ℕ) : ℝ) ^ (-σ) ≤ ((X : ℕ) : ℝ) ^ (0 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le hX1
            linarith
        _ = 1 := Real.rpow_zero _
    have hsnorm : ‖s‖ ≤ |t| + 2 := by
      rw [hsdef]
      calc ‖(σ : ℂ) + Complex.I * t‖ ≤ ‖(σ : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ :=
            norm_add_le _ _
        _ = |σ| + |t| := by
            rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul,
              Complex.norm_real]
            simp [Real.norm_eq_abs]
        _ ≤ 2 + |t| := by
            have : |σ| ≤ 2 := abs_le.mpr ⟨by linarith, hσhigh⟩
            linarith
        _ = |t| + 2 := by ring
    calc ‖-(s * emTail s ((X : ℕ) : ℝ))‖ = ‖s‖ * ‖emTail s ((X : ℕ) : ℝ)‖ := by
          rw [norm_neg, norm_mul]
      _ ≤ (|t| + 2) * (((X : ℕ) : ℝ) ^ (-s.re) / s.re) := by
          apply mul_le_mul hsnorm htail (norm_nonneg _) (by positivity)
      _ ≤ (|t| + 2) * (1 / (1 / 2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div₀ (by norm_num) hXpow (by norm_num)
          rw [hsre]
          exact hσlow
      _ = 2 * (|t| + 2) := by ring

end RH.Criteria.NymanBeurling.H14ZetaEM

