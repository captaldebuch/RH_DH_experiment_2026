import RiemannHypothesis.Criteria.NymanBeurling.H15RhoBDBaseIntegral
import RiemannHypothesis.Criteria.NymanBeurling.H14ZetaEM

/-!
# Discharging the base Mellin debt

Proves `RhoBDBaseMellinFormula`: `mellin (fun x => ({1/x} : ℂ)) s = -ζ(s)/s`
on the critical strip `0 < Re s < 1`.

Route: `mellin_comp_inv` reduces to `mellin ({·}) (-s)`; splitting the ray at
`1` gives the exact head `1/(1-s)` plus the Euler–Maclaurin tail
`emTail s 1` from `H14ZetaEM`; the continued identity there evaluates the
tail off the real axis, and one more convex-strip identity-theorem
application removes the `Im s ≠ 0` restriction.
-/

namespace RH.Criteria.NymanBeurling.BaezDuarte

open MeasureTheory Set Complex Filter Topology
open RH.Criteria.NymanBeurling.H14ZetaEM

/-- Head piece: `∫_{Ioc 0 1} t^{−s−1}·{t} dt = 1/(1−s)` for `Re s < 1`. -/
theorem integral_Ioc_fract_cpow {s : ℂ} (h1 : s.re < 1) :
    (∫ t : ℝ in Ioc (0 : ℝ) 1, (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) =
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
  have hcongr : (∫ t : ℝ in Ioo (0 : ℝ) 1,
      (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) =
      ∫ t : ℝ in Ioo (0 : ℝ) 1, (t : ℂ) ^ (-s) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht.1.le, ht.2⟩
    have hne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht.1
    show (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) = (t : ℂ) ^ (-s)
    rw [hfr, Complex.cpow_sub _ _ hne, Complex.cpow_one]
    field_simp
  rw [hcongr, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl hre)]
  rw [show (-s : ℂ) + 1 = 1 - s from by ring,
    show ((1 : ℝ) : ℂ) = 1 from by norm_num,
    show ((0 : ℝ) : ℂ) = 0 from by norm_num,
    Complex.one_cpow, Complex.zero_cpow h1s]
  ring

/-- Splitting the Mellin integral of the fractional part at `1`. -/
theorem mellin_fract_eq_head_add_emTail {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) (-s) =
      1 / (1 - s) + emTail s 1 := by
  have hre : (-1 : ℝ) < (-s).re := by
    simp only [Complex.neg_re]
    linarith
  have hInt1 : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ))
      (Ioc (0 : ℝ) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    have hbase : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioo (0 : ℝ) 1) := by
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      have := (intervalIntegral.intervalIntegrable_cpow' (r := -s) hre :
        IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume 0 1)
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    apply hbase.congr_fun _ measurableSet_Ioo
    intro t ht
    have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht.1.le, ht.2⟩
    have hne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht.1
    show (t : ℂ) ^ (-s) = (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)
    rw [hfr, Complex.cpow_sub _ _ hne, Complex.cpow_one]
    field_simp
  have hInt2 : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ))
      (Ioi (1 : ℝ)) := by
    apply (emTailIntegrand_integrableOn h0 le_rfl).congr_fun _ measurableSet_Ioi
    intro t _
    show emTailIntegrand s t = (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)
    unfold emTailIntegrand
    ring
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  unfold mellin
  simp only [smul_eq_mul]
  rw [show (-s : ℂ) - 1 = -s - 1 from rfl]
  rw [← hunion, MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi hInt1 hInt2]
  congr 1
  · exact integral_Ioc_fract_cpow h1
  · unfold emTail
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    show (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) = emTailIntegrand s t
    unfold emTailIntegrand
    ring

/-- Off-axis evaluation of the tail via the continued EM identity. -/
theorem emTail_one_eq_of_im_ne_zero {s : ℂ} (h0 : 0 < s.re) (him : s.im ≠ 0) :
    emTail s 1 = (1 + 1 / (s - 1) - riemannZeta s) / s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at him
    simp at him
  have hid := emIdentity_of_pos_re_of_im_ne_zero h0 him (X := 1) le_rfl
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_cpow] at hid
  rw [eq_div_iff hs0]
  linear_combination hid

/-- The tail identity extends to the whole open strip by the identity
theorem on the convex set `0 < Re < 1`. -/
theorem emTail_one_eq_on_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    emTail s 1 = (1 + 1 / (s - 1) - riemannZeta s) / s := by
  have hUopen : IsOpen ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hUconv : Convex ℝ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}) :=
    (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have hz₀mem : ((1 / 2 : ℂ) + (1 / 2 : ℂ) * Complex.I) ∈
      ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}) := by
    constructor <;> norm_num
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => emTail z 1)
      ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}) := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact (emTail_differentiableAt hz.1 le_rfl).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ
      (fun z : ℂ => (1 + 1 / (z - 1) - riemannZeta z) / z)
      ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}) := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      exact absurd hz.2 (by norm_num)
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      exact absurd hz.1 (by norm_num)
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div _ differentiableAt_id hz0
    apply DifferentiableAt.sub
    · apply DifferentiableAt.add (differentiableAt_const _)
      exact (differentiableAt_const _).div
        (differentiableAt_id.sub (differentiableAt_const _))
        (sub_ne_zero.mpr hz1)
    · exact differentiableAt_riemannZeta hz1
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg
    hUconv.isPreconnected hz₀mem ?_
  · exact heq ⟨h0, h1⟩
  · have hopen2 : IsOpen (({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}) ∩
        {z : ℂ | 0 < z.im}) :=
      hUopen.inter (isOpen_lt continuous_const Complex.continuous_im)
    have hz₀mem2 : ((1 / 2 : ℂ) + (1 / 2 : ℂ) * Complex.I) ∈
        (({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}) ∩ {z : ℂ | 0 < z.im}) := by
      refine ⟨hz₀mem, ?_⟩
      norm_num
    filter_upwards [hopen2.mem_nhds hz₀mem2] with z hz
    exact emTail_one_eq_of_im_ne_zero hz.1.1 (ne_of_gt hz.2)

/-- The classical base Mellin evaluation on the critical strip. -/
theorem mellin_fract_inv_eq_neg_zeta_div {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) (-s) = -riemannZeta s / s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hs1 h.symm
  rw [mellin_fract_eq_head_add_emTail h0 h1, emTail_one_eq_on_strip h0 h1]
  field_simp
  ring

/-- The frozen base Mellin debt is now a theorem. -/
noncomputable def rhoBDBaseMellinFormula_proved : RhoBDBaseMellinFormula where
  formula := by
    intro s h0 h1 hne
    rw [rhoBDBase_mellin_eq_mellin_fract_inv,
      mellin_fract_inv_eq_neg_zeta_div h0 h1]

/-- NB0's `mellin_generator_eval` statement, unconditionally. -/
theorem mellin_generator_eval_proved (k : ℕ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsne : s ≠ 0) :
    mellin (fun x : ℝ => (rhoBD k x : ℂ)) s =
      -(riemannZeta s) / (s * ((k + 1 : ℕ) : ℂ) ^ s) :=
  rhoBD_mellin_formula_of_base_nb0 rhoBDBaseMellinFormula_proved k s hs0 hs1 hsne

end RH.Criteria.NymanBeurling.BaezDuarte
