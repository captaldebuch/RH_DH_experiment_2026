/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB2Mellin
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Phase NB2: the fractional-part Mellin evaluation

This file discharges the one analytic input isolated in `NB2Mellin`.  The
proof first establishes the classical fractional-part tail identity for
`Re s > 1` by Abel summation, and then continues it through the strip using
holomorphy of the tail integral.  Combining the tail with the elementary
integral over `(0, 1]` gives

`mellin (fun x => ({1 / x} : ℂ)) s = -riemannZeta s / s`

for `0 < Re s < 1`.
-/

open MeasureTheory Set Complex Filter Topology Asymptotics

namespace NBMellinTools.NB2

/-! ## The fractional-part tail and its holomorphy -/

/-- The Euler--Maclaurin fractional-part tail integrand. -/
noncomputable def fractTailIntegrand (s : ℂ) (u : ℝ) : ℂ :=
  ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)

/-- The tail integral `∫_X^∞ {u} u^(-s-1) du`. -/
noncomputable def fractTail (s : ℂ) (X : ℝ) : ℂ :=
  ∫ u in Ioi X, fractTailIntegrand s u

theorem fractTailIntegrand_norm_le {s : ℂ} {u : ℝ} (hu : 1 ≤ u) :
    ‖fractTailIntegrand s u‖ ≤ u ^ (-s.re - 1) := by
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  unfold fractTailIntegrand
  rw [norm_mul]
  have h1 : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg u)]
    exact (Int.fract_lt_one u).le
  have h2 : ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hupos]
    norm_num
  calc
    ‖((Int.fract u : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 1)‖
        ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = u ^ (-s.re - 1) := by rw [one_mul, h2]

theorem fractTailIntegrand_aestronglyMeasurable (s : ℂ) {X : ℝ} :
    AEStronglyMeasurable (fractTailIntegrand s) (volume.restrict (Ioi X)) := by
  apply Measurable.aestronglyMeasurable
  unfold fractTailIntegrand
  apply Measurable.mul
  · exact Complex.measurable_ofReal.comp measurable_fract
  · exact Complex.measurable_ofReal.pow measurable_const

theorem fractTailIntegrand_integrableOn {s : ℂ} (hs : 0 < s.re)
    {X : ℝ} (hX : 1 ≤ X) :
    IntegrableOn (fractTailIntegrand s) (Ioi X) := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have hmaj : IntegrableOn (fun u : ℝ ↦ u ^ (-s.re - 1)) (Ioi X) := by
    apply integrableOn_Ioi_rpow_of_lt _ hXpos
    linarith
  apply Integrable.mono' hmaj (fractTailIntegrand_aestronglyMeasurable s)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with u hu
  exact fractTailIntegrand_norm_le (le_trans hX (le_of_lt hu))

/-- Elementary domination used to differentiate the tail under the integral. -/
theorem log_le_rpow_div_self {u δ : ℝ} (hu : 1 ≤ u) (hδ : 0 < δ) :
    Real.log u ≤ u ^ δ / δ := by
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hpow : (0 : ℝ) < u ^ δ := Real.rpow_pos_of_pos hupos δ
  have h1 : Real.log (u ^ δ) ≤ u ^ δ - 1 := Real.log_le_sub_one_of_pos hpow
  rw [Real.log_rpow hupos] at h1
  have h2 : δ * Real.log u ≤ u ^ δ := le_trans h1 (by linarith)
  calc
    Real.log u = δ * Real.log u / δ := by field_simp
    _ ≤ u ^ δ / δ := div_le_div_of_nonneg_right h2 hδ.le

theorem integrableOn_log_mul_rpow {X : ℝ} (hX : 1 ≤ X)
    {a : ℝ} (ha : a < -1) :
    IntegrableOn (fun u : ℝ ↦ Real.log u * u ^ a) (Ioi X) := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  set δ : ℝ := (-1 - a) / 2 with hδdef
  have hδ : 0 < δ := by simp only [hδdef]; linarith
  have hexp : a + δ < -1 := by simp only [hδdef]; linarith
  have hmaj : IntegrableOn (fun u : ℝ ↦ u ^ (a + δ) / δ) (Ioi X) :=
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
    calc
      Real.log u * u ^ a ≤ u ^ δ / δ * u ^ a :=
        mul_le_mul_of_nonneg_right (log_le_rpow_div_self hu1 hδ) hpowpos
      _ = u ^ (a + δ) / δ := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hupos, add_comm]

noncomputable def fractTailDerivIntegrand (s : ℂ) (u : ℝ) : ℂ :=
  -(((Int.fract u : ℝ) : ℂ) * ((Real.log u : ℝ) : ℂ) *
    (u : ℂ) ^ (-s - 1))

theorem fractTailDerivIntegrand_norm_le {s : ℂ} {u : ℝ} (hu : 1 ≤ u) :
    ‖fractTailDerivIntegrand s u‖ ≤ Real.log u * u ^ (-s.re - 1) := by
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hlog : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu
  unfold fractTailDerivIntegrand
  rw [norm_neg, norm_mul, norm_mul]
  have h1 : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg u)]
    exact (Int.fract_lt_one u).le
  have h2 : ‖((Real.log u : ℝ) : ℂ)‖ = Real.log u := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  have h3 : ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hupos]
    norm_num
  calc
    ‖((Int.fract u : ℝ) : ℂ)‖ * ‖((Real.log u : ℝ) : ℂ)‖ *
          ‖(u : ℂ) ^ (-s - 1)‖
        ≤ 1 * ‖((Real.log u : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = Real.log u * u ^ (-s.re - 1) := by rw [one_mul, h2, h3]

theorem fractTailDerivIntegrand_aestronglyMeasurable (s : ℂ) {X : ℝ} :
    AEStronglyMeasurable (fractTailDerivIntegrand s)
      (volume.restrict (Ioi X)) := by
  apply Measurable.aestronglyMeasurable
  unfold fractTailDerivIntegrand
  apply Measurable.neg
  apply Measurable.mul
  · apply Measurable.mul
    · exact Complex.measurable_ofReal.comp measurable_fract
    · exact Complex.measurable_ofReal.comp Real.measurable_log
  · exact Complex.measurable_ofReal.pow measurable_const

theorem fractTailIntegrand_hasDerivAt {u : ℝ} (hu : 1 ≤ u) (s : ℂ) :
    HasDerivAt (fun z : ℂ ↦ fractTailIntegrand z u)
      (fractTailDerivIntegrand s u) s := by
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hne : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hupos
  have h1 : HasDerivAt (fun z : ℂ ↦ -z - 1) (-1) s := by
    simpa using ((hasDerivAt_id s).neg.sub_const 1)
  have h2 : HasDerivAt (fun z : ℂ ↦ (u : ℂ) ^ (-z - 1))
      ((u : ℂ) ^ (-s - 1) * Complex.log (u : ℂ) * (-1)) s :=
    HasDerivAt.const_cpow h1 (Or.inl hne)
  have h3 := h2.const_mul ((Int.fract u : ℝ) : ℂ)
  have hlogeq : Complex.log (u : ℂ) = ((Real.log u : ℝ) : ℂ) :=
    (Complex.ofReal_log hupos.le).symm
  convert h3 using 1
  unfold fractTailDerivIntegrand
  rw [hlogeq]
  ring

theorem fractTail_hasDerivAt {s₀ : ℂ} (hs₀ : 0 < s₀.re)
    {X : ℝ} (hX : 1 ≤ X) :
    HasDerivAt (fun s : ℂ ↦ fractTail s X)
      (∫ u in Ioi X, fractTailDerivIntegrand s₀ u) s₀ := by
  set ε : ℝ := s₀.re / 2 with hεdef
  have hε : 0 < ε := by simp only [hεdef]; linarith
  have hres : ∀ z ∈ Metric.ball s₀ ε, ε ≤ z.re := by
    intro z hz
    have hd : |(z - s₀).re| ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h : |(z - s₀).re| < ε := lt_of_le_of_lt hd hz
    rw [Complex.sub_re, abs_lt] at h
    simp only [hεdef] at h ⊢
    linarith [h.1]
  have hbound_int :
      IntegrableOn (fun u : ℝ ↦ Real.log u * u ^ (-ε - 1)) (Ioi X) :=
    integrableOn_log_mul_rpow hX (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun s u ↦ fractTailIntegrand s u)
    (F' := fun u ↦ fractTailDerivIntegrand s₀ u)
    (x₀ := s₀)
    (bound := fun u ↦ Real.log u * u ^ (-ε - 1))
    (μ := volume.restrict (Ioi X))
    (Metric.ball_mem_nhds s₀ hε)
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · filter_upwards with s
    exact fractTailIntegrand_aestronglyMeasurable s
  · exact fractTailIntegrand_integrableOn hs₀ hX
  · exact fractTailDerivIntegrand_aestronglyMeasurable s₀
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu1 : (1 : ℝ) ≤ u := le_trans hX (le_of_lt hu)
    have hlog : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
    have hpow : (0 : ℝ) ≤ u ^ (-ε - 1) :=
      (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hu1) _).le
    apply LipschitzOnWith.mono _ (Set.Subset.refl _)
    apply (convex_ball s₀ ε).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun z ↦ fractTailDerivIntegrand z u)
    · intro z _
      exact (fractTailIntegrand_hasDerivAt hu1 z).hasDerivWithinAt
    · intro z hz
      rw [← NNReal.coe_le_coe]
      calc
        (‖fractTailDerivIntegrand z u‖₊ : ℝ) =
            ‖fractTailDerivIntegrand z u‖ := rfl
        _ ≤ Real.log u * u ^ (-z.re - 1) :=
          fractTailDerivIntegrand_norm_le hu1
        _ ≤ Real.log u * u ^ (-ε - 1) := by
          apply mul_le_mul_of_nonneg_left _ hlog
          apply Real.rpow_le_rpow_of_exponent_le hu1
          linarith [hres z hz]
        _ ≤ (Real.nnabs (Real.log u * u ^ (-ε - 1)) : ℝ) := by
          rw [Real.coe_nnabs, abs_of_nonneg (mul_nonneg hlog hpow)]
  · exact hbound_int
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    exact fractTailIntegrand_hasDerivAt (le_trans hX (le_of_lt hu)) s₀

theorem fractTail_differentiableAt {s : ℂ} (hs : 0 < s.re)
    {X : ℝ} (hX : 1 ≤ X) :
    DifferentiableAt ℂ (fun z : ℂ ↦ fractTail z X) s :=
  (fractTail_hasDerivAt hs hX).differentiableAt

/-! ## The tail identity for `Re s > 1` -/

lemma natFloor_eq_sub_fract_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    (⌊t⌋₊ : ℝ) = t - Int.fract t := by
  calc
    (⌊t⌋₊ : ℝ) = (⌊t⌋ : ℝ) := natCast_floor_eq_intCast_floor ht
    _ = t - Int.fract t := by linarith [Int.floor_add_fract t]

/-- Abel summation for the constant Dirichlet coefficients on `Re s > 1`. -/
theorem riemannZeta_eq_floor_cpow_integral {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s =
      s * ∫ t : ℝ in Ioi (1 : ℝ),
        (((Nat.floor t : ℕ) : ℂ) * (t : ℂ) ^ (-s - 1)) := by
  have hS : LSeriesSummable (fun _ : ℕ ↦ (1 : ℂ)) s :=
    LSeriesSummable_one_iff.mpr hs
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
    refine (isBigO_iff_isBigOWith).2 ⟨1, ?_⟩
    rw [isBigOWith_iff]
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simp [Real.rpow_one]
  rw [← LSeries_one_eq_riemannZeta hs]
  have h := LSeries_eq_mul_integral (fun _ : ℕ ↦ (1 : ℂ))
    (r := 1) zero_le_one hs hS hO
  rw [show -s - 1 = -(s + 1) by ring]
  simpa using h

/-- The exact fractional-part tail identity on its initial half-plane. -/
theorem fractTail_one_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    fractTail s 1 = 1 / (s - 1) - riemannZeta s / s := by
  have hfloor := riemannZeta_eq_floor_cpow_integral hs
  have hsplit :
      (∫ t : ℝ in Ioi (1 : ℝ),
          (((Nat.floor t : ℕ) : ℂ) * (t : ℂ) ^ (-s - 1))) =
        ∫ t : ℝ in Ioi (1 : ℝ),
          ((t : ℂ) - ((Int.fract t : ℝ) : ℂ)) *
            (t : ℂ) ^ (-s - 1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 ≤ t := by linarith [show (1 : ℝ) < t from ht]
    change ((Nat.floor t : ℕ) : ℂ) * (t : ℂ) ^ (-s - 1) =
      ((t : ℂ) - ((Int.fract t : ℝ) : ℂ)) * (t : ℂ) ^ (-s - 1)
    rw [show ((Nat.floor t : ℕ) : ℂ) =
        (t : ℂ) - ((Int.fract t : ℝ) : ℂ) by
      norm_cast
      exact natFloor_eq_sub_fract_of_nonneg ht0]
  have hcpow : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1))
      (Ioi (1 : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt
    · have he : (-s - 1).re = -s.re - 1 := by norm_num
      rw [he]
      linarith
    · exact one_pos
  have hfrac : IntegrableOn
      (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
      (Ioi (1 : ℝ)) := by
    simpa only [fractTailIntegrand] using
      fractTailIntegrand_integrableOn (s := s) (by linarith) le_rfl
  have hbase : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-s))
      (Ioi (1 : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt
    · have he : (-s).re = -s.re := by norm_num
      rw [he]
      linarith
    · exact one_pos
  have hmul : ∀ t : ℝ, 0 < t →
      (t : ℂ) * (t : ℂ) ^ (-s - 1) = (t : ℂ) ^ (-s) := by
    intro t ht
    calc
      (t : ℂ) * (t : ℂ) ^ (-s - 1) =
          (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-s - 1) := by simp
      _ = (t : ℂ) ^ ((1 : ℂ) + (-s - 1)) :=
        (Complex.cpow_add (1 : ℂ) (-s - 1)
          (Complex.ofReal_ne_zero.mpr ht.ne')).symm
      _ = (t : ℂ) ^ (-s) := by
        rw [show (1 : ℂ) + (-s - 1) = -s by ring]
  have hmain : IntegrableOn
      (fun t : ℝ ↦ (t : ℂ) * (t : ℂ) ^ (-s - 1))
      (Ioi (1 : ℝ)) := by
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro t ht
    change (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-s - 1)
    exact (hmul t (by linarith [show (1 : ℝ) < t from ht])).symm
  have hmain_eq :
      (∫ t : ℝ in Ioi (1 : ℝ),
          (t : ℂ) * (t : ℂ) ^ (-s - 1)) =
        ∫ t : ℝ in Ioi (1 : ℝ), (t : ℂ) ^ (-s) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hmul t (by linarith [show (1 : ℝ) < t from ht])
  have hcalc :
      (∫ t : ℝ in Ioi (1 : ℝ),
          ((t : ℂ) - ((Int.fract t : ℝ) : ℂ)) * (t : ℂ) ^ (-s - 1)) =
        (∫ t : ℝ in Ioi (1 : ℝ), (t : ℂ) ^ (-s)) -
          (∫ t : ℝ in Ioi (1 : ℝ),
            ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) := by
    calc
      _ = ∫ t : ℝ in Ioi (1 : ℝ),
          ((fun u : ℝ ↦ (u : ℂ) * (u : ℂ) ^ (-s - 1)) t -
            (fun u : ℝ ↦ ((Int.fract u : ℝ) : ℂ) *
              (u : ℂ) ^ (-s - 1)) t) := by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _ = (∫ t : ℝ in Ioi (1 : ℝ),
          (t : ℂ) * (t : ℂ) ^ (-s - 1)) -
          (∫ t : ℝ in Ioi (1 : ℝ),
            ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) :=
        integral_sub hmain hfrac
      _ = _ := by rw [hmain_eq]
  rw [hsplit, hcalc, integral_Ioi_cpow_of_lt (by
    have he : (-s).re = -s.re := by norm_num
    rw [he]
    linarith) one_pos] at hfloor
  have hsne : s ≠ 0 := ne_zero_of_re_pos (by linarith [hs])
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  simp only [ofReal_one, one_cpow] at hfloor
  have hfloor' : riemannZeta s = s * (-1 / (-s + 1) - fractTail s 1) := by
    simpa [fractTail, fractTailIntegrand] using hfloor
  rw [hfloor']
  field_simp [hsne, hs1]
  rw [show (-s + 1 : ℂ) = -(s - 1) by ring]
  have hneg : 1 / (-(s - 1)) = -(1 / (s - 1)) := by
    rw [div_eq_mul_inv, inv_neg]
    simp
  rw [hneg]
  ring

/-! ## Analytic continuation of the tail identity -/

/-- The pole-separated right-hand side of the one-cutoff Euler--Maclaurin
identity. -/
noncomputable def zetaTailRHS (s : ℂ) : ℂ :=
  1 + 1 / (s - 1) - s * fractTail s 1

theorem zeta_eq_zetaTailRHS_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = zetaTailRHS s := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (lt_trans one_pos hs)
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [zetaTailRHS, fractTail_one_eq_of_one_lt_re hs]
  field_simp [hs0, hs1']
  ring

theorem zetaTailRHS_differentiableAt {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ zetaTailRHS s := by
  unfold zetaTailRHS
  have hpole : DifferentiableAt ℂ (fun z : ℂ ↦ 1 / (z - 1)) s := by
    exact (differentiableAt_const (c := (1 : ℂ))).div
      (differentiableAt_id.sub (differentiableAt_const (c := (1 : ℂ))))
      (sub_ne_zero.mpr hs1)
  have htail : DifferentiableAt ℂ (fun z : ℂ ↦ z * fractTail z 1) s :=
    differentiableAt_id.mul (fractTail_differentiableAt hs le_rfl)
  exact ((differentiableAt_const (c := (1 : ℂ))).add hpole).sub htail

/-- The identity theorem step on a convex subset of the punctured right
half-plane. -/
theorem zeta_eq_zetaTailRHS_on_convex {U : Set ℂ}
    (hUopen : IsOpen U) (hUconv : Convex ℝ U)
    (hUre : ∀ z ∈ U, 0 < z.re) (hUone : (1 : ℂ) ∉ U)
    {z₀ : ℂ} (hz₀U : z₀ ∈ U) (hz₀re : 1 < z₀.re) :
    Set.EqOn riemannZeta zetaTailRHS U := by
  have hζ : AnalyticOnNhd ℂ riemannZeta U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact (differentiableAt_riemannZeta
      (fun h1 ↦ hUone (h1 ▸ hz))).differentiableWithinAt
  have hR : AnalyticOnNhd ℂ zetaTailRHS U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact (zetaTailRHS_differentiableAt (hUre z hz)
      (fun h1 ↦ hUone (h1 ▸ hz))).differentiableWithinAt
  apply hζ.eqOn_of_preconnected_of_eventuallyEq hR
    hUconv.isPreconnected hz₀U
  have hopen1 : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen1.mem_nhds hz₀re] with z hz
  exact zeta_eq_zetaTailRHS_of_one_lt_re hz

/-- The continued identity away from the real axis in the right half-plane. -/
theorem zeta_eq_zetaTailRHS_of_pos_re_of_im_ne_zero {s : ℂ}
    (h0 : 0 < s.re) (him : s.im ≠ 0) :
    riemannZeta s = zetaTailRHS s := by
  have him' := lt_or_gt_of_ne him
  have h1im : (1 : ℂ).im = 0 := rfl
  rcases him' with hlt | hgt
  · have h := zeta_eq_zetaTailRHS_on_convex
      (U := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < 0})
      (IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
        (isOpen_lt Complex.continuous_im continuous_const))
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0))
      (fun z hz ↦ hz.1)
      (by intro h; exact absurd h.2 (by norm_num [h1im]))
      (z₀ := 2 - Complex.I)
      (by constructor <;> simp)
      (by simp)
    exact h ⟨h0, hlt⟩
  · have h := zeta_eq_zetaTailRHS_on_convex
      (U := {z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im})
      (IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
        (isOpen_lt continuous_const Complex.continuous_im))
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0))
      (fun z hz ↦ hz.1)
      (by intro h; exact absurd h.2 (by norm_num [h1im]))
      (z₀ := 2 + Complex.I)
      (by constructor <;> simp)
      (by simp)
    exact h ⟨h0, hgt⟩

/-- The continued Euler--Maclaurin identity on the whole critical strip. -/
theorem zeta_eq_zetaTailRHS_on_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta s = zetaTailRHS s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hUconv : Convex ℝ U :=
    (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have hz₀mem : ((1 / 2 : ℂ) + (1 / 2 : ℂ) * Complex.I) ∈ U := by
    constructor <;> norm_num
  have hζ : AnalyticOnNhd ℂ riemannZeta U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      have hzlt : z.re < 1 := hz.2
      norm_num at hre
      linarith
    exact (differentiableAt_riemannZeta hz1).differentiableWithinAt
  have hR : AnalyticOnNhd ℂ zetaTailRHS U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      have hzlt : z.re < 1 := hz.2
      norm_num at hre
      linarith
    exact (zetaTailRHS_differentiableAt hz.1 hz1).differentiableWithinAt
  have heq := hζ.eqOn_of_preconnected_of_eventuallyEq hR
    hUconv.isPreconnected hz₀mem ?_
  · exact heq ⟨h0, h1⟩
  · have hopen2 : IsOpen (U ∩ {z : ℂ | 0 < z.im}) :=
      hUopen.inter (isOpen_lt continuous_const Complex.continuous_im)
    have hz₀mem2 : ((1 / 2 : ℂ) + (1 / 2 : ℂ) * Complex.I) ∈
        U ∩ {z : ℂ | 0 < z.im} := by
      refine ⟨hz₀mem, ?_⟩
      norm_num
    filter_upwards [hopen2.mem_nhds hz₀mem2] with z hz
    exact zeta_eq_zetaTailRHS_of_pos_re_of_im_ne_zero hz.1.1
      (ne_of_gt hz.2)

/-- Closed form of the fractional-part tail throughout `0 < Re s < 1`. -/
theorem fractTail_one_eq_on_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    fractTail s 1 = (1 + 1 / (s - 1) - riemannZeta s) / s := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos h0
  have hid := zeta_eq_zetaTailRHS_on_strip h0 h1
  unfold zetaTailRHS at hid
  rw [eq_div_iff hs0]
  linear_combination hid

/-! ## Assembly of the full Mellin transform -/

/-- Head piece: `∫_(0,1] t^(-s-1) {t} dt = 1/(1-s)`. -/
theorem integral_Ioc_fract_cpow {s : ℂ} (h1 : s.re < 1) :
    (∫ t : ℝ in Ioc (0 : ℝ) 1,
        (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) =
      1 / (1 - s) := by
  have hre : (-1 : ℝ) < (-s).re := by
    simp only [Complex.neg_re]
    linarith
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    apply absurd (congrArg Complex.re h)
    simp only [Complex.one_re]
    linarith
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hcongr :
      (∫ t : ℝ in Ioo (0 : ℝ) 1,
          (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) =
        ∫ t : ℝ in Ioo (0 : ℝ) 1, (t : ℂ) ^ (-s) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have hfr : Int.fract t = t :=
      Int.fract_eq_self.mpr ⟨ht.1.le, ht.2⟩
    have hne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht.1
    change (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) =
      (t : ℂ) ^ (-s)
    rw [hfr, Complex.cpow_sub _ _ hne, Complex.cpow_one]
    field_simp
  rw [hcongr, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl hre)]
  rw [show (-s : ℂ) + 1 = 1 - s from by ring,
    show ((1 : ℝ) : ℂ) = 1 from by norm_num,
    show ((0 : ℝ) : ℂ) = 0 from by norm_num,
    Complex.one_cpow, Complex.zero_cpow h1s]
  ring

/-- Splitting the fractional-part Mellin integral at `1`. -/
theorem mellin_fract_eq_head_add_fractTail {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin (fun x : ℝ ↦ ((Int.fract x : ℝ) : ℂ)) (-s) =
      1 / (1 - s) + fractTail s 1 := by
  have hre : (-1 : ℝ) < (-s).re := by
    simp only [Complex.neg_re]
    linarith
  have hInt1 : IntegrableOn
      (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ))
      (Ioc (0 : ℝ) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    have hbase : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-s))
        (Ioo (0 : ℝ) 1) := by
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      have h :=
        (intervalIntegral.intervalIntegrable_cpow' (r := -s) hre :
          IntervalIntegrable (fun x : ℝ ↦ (x : ℂ) ^ (-s)) volume 0 1)
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
    apply hbase.congr_fun _ measurableSet_Ioo
    intro t ht
    have hfr : Int.fract t = t :=
      Int.fract_eq_self.mpr ⟨ht.1.le, ht.2⟩
    have hne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht.1
    change (t : ℂ) ^ (-s) =
      (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)
    rw [hfr, Complex.cpow_sub _ _ hne, Complex.cpow_one]
    field_simp
  have hInt2 : IntegrableOn
      (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ))
      (Ioi (1 : ℝ)) := by
    apply (fractTailIntegrand_integrableOn h0 le_rfl).congr_fun _
      measurableSet_Ioi
    intro t _
    unfold fractTailIntegrand
    ring
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  unfold mellin
  simp only [smul_eq_mul]
  rw [show (-s : ℂ) - 1 = -s - 1 from rfl]
  rw [← hunion, MeasureTheory.setIntegral_union
    (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hInt1 hInt2]
  congr 1
  · exact integral_Ioc_fract_cpow h1
  · unfold fractTail
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    unfold fractTailIntegrand
    ring

/-- The ordinary fractional-part Mellin transform evaluated at the inverted
critical-strip parameter. -/
theorem mellin_fract_inv_eq_neg_zeta_div {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin (fun x : ℝ ↦ ((Int.fract x : ℝ) : ℂ)) (-s) =
      -riemannZeta s / s := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos h0
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at h1
    norm_num at h1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  rw [mellin_fract_eq_head_add_fractTail h0 h1,
    fractTail_one_eq_on_strip h0 h1]
  field_simp [hs0, hs1', h1s]
  ring

/-- The unconditional base fractional-part Mellin evaluation. -/
theorem mellin_rhoBase {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin (fun x : ℝ ↦ (rhoBase x : ℂ)) s =
      -(riemannZeta s) / s := by
  rw [mellin_rhoBase_eq_mellin_fract_inv]
  exact mellin_fract_inv_eq_neg_zeta_div h0 h1

/-- The unconditional Mellin formula for every positive Nyman dilation. -/
theorem mellin_rhoTheta {θ : ℝ} (hθ : 0 < θ) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin (fun x : ℝ ↦ (rhoTheta θ x : ℂ)) s =
      (θ : ℂ) ^ s * (-(riemannZeta s) / s) :=
  mellin_rhoTheta_of_base hθ s (mellin_rhoBase h0 h1)

/-- The unconditional Mellin formula for the zero-based Báez--Duarte
generators. -/
theorem mellin_rhoBD (k : ℕ) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin (fun x : ℝ ↦ (rhoBD k x : ℂ)) s =
      -(riemannZeta s) /
        (s * ((((k + 1 : ℕ) : ℝ) : ℂ) ^ s)) :=
  mellin_rhoBD_of_base k s (mellin_rhoBase h0 h1)

end NBMellinTools.NB2
