import RiemannHypothesis.Criteria.NymanBeurling.RHBridge
import RiemannHypothesis.Criteria.NymanBeurling.H15RhoBDBaseDischarge

/-!
# The χ-side Mellin evaluation

Discharges the `mellin_chi_eval` field of `MellinNymanBridgeDebts`:
`mellin χ_{(0,1]} s = 1/s` on `0 < Re s` (stated on the NB0 strip).
-/

namespace RH.Criteria.NymanBeurling.BaezDuarte

open MeasureTheory Set Complex intervalIntegral

/-- `chi01` as a complex-valued function is the indicator of `Ioc 0 1`. -/
theorem chi01_eq_indicator (x : ℝ) :
    ((chi01 x : ℝ) : ℂ) = (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) x := by
  unfold chi01
  by_cases h : 0 < x ∧ x ≤ 1
  · rw [if_pos h, Set.indicator_of_mem (by exact h)]
    norm_num
  · rw [if_neg h, Set.indicator_of_notMem (by exact h)]
    norm_num

/-- The χ-side Mellin evaluation on `Re s > 0`. -/
theorem mellin_chi01_eq {s : ℂ} (h0 : 0 < s.re) :
    mellin (fun x : ℝ => ((chi01 x : ℝ) : ℂ)) s = 1 / s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
  have hre : (-1 : ℝ) < (s - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  unfold mellin
  simp only [smul_eq_mul]
  have hcongr : (∫ t : ℝ in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * ((chi01 t : ℝ) : ℂ)) =
      ∫ t : ℝ in Ioi (0 : ℝ),
        (Ioc (0 : ℝ) 1).indicator (fun u : ℝ => (u : ℂ) ^ (s - 1)) t := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    show (t : ℂ) ^ (s - 1) * ((chi01 t : ℝ) : ℂ) =
        (Ioc (0 : ℝ) 1).indicator (fun u : ℝ => (u : ℂ) ^ (s - 1)) t
    rw [chi01_eq_indicator]
    by_cases h : t ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      ring
  rw [hcongr, MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc (0 : ℝ) 1 = Ioc (0 : ℝ) 1 from
      Set.inter_eq_self_of_subset_right (fun x hx => hx.1),
    ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl hre)]
  rw [show (s - 1 : ℂ) + 1 = s from by ring,
    show ((1 : ℝ) : ℂ) = 1 from by norm_num,
    show ((0 : ℝ) : ℂ) = 0 from by norm_num,
    Complex.one_cpow, Complex.zero_cpow hs0]
  ring

/-- The exact NB0 `mellin_chi_eval` field statement, unconditionally. -/
theorem mellin_chi_eval_proved :
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → s ≠ 0 →
      mellin (fun x : ℝ => (chi01 x : ℂ)) s = 1 / s := by
  intro s h0 _ _
  exact mellin_chi01_eq (by linarith)

end RH.Criteria.NymanBeurling.BaezDuarte
