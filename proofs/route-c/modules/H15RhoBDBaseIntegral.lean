import RiemannHypothesis.Criteria.NymanBeurling.H15RhoBDMellin

/-!
Re(s) > 1 floor and fractional-part integrals for the Báez--Duarte base
function.  The floor identity is a direct specialization of Mathlib's
`LSeries_eq_mul_integral`; the fractional-part identity is then ordinary
linear algebra of Bochner integrals.  Analytic continuation to the critical
strip is intentionally not asserted here.
-/

namespace RH.Criteria.NymanBeurling.BaezDuarte

open MeasureTheory Set Filter Asymptotics Complex Topology
open scoped BigOperators

lemma natFloor_eq_sub_fract_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    (⌊t⌋₊ : ℝ) = t - Int.fract t := by
  calc
    (⌊t⌋₊ : ℝ) = (⌊t⌋ : ℝ) := natCast_floor_eq_intCast_floor ht
    _ = t - Int.fract t := by linarith [Int.floor_add_fract t]

/-- Abel summation for the constant Dirichlet coefficients on `Re s > 1`. -/
theorem riemannZeta_eq_floor_cpow_integral {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s =
      s * ∫ t : ℝ in Set.Ioi (1 : ℝ),
        (((Nat.floor t : ℕ) : ℂ) * (t : ℂ) ^ (-s - 1)) := by
  have hS : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) s :=
    LSeriesSummable_one_iff.mpr hs
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    refine (isBigO_iff_isBigOWith).2 ⟨1, ?_⟩
    rw [isBigOWith_iff]
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simp [Real.rpow_one]
  rw [← LSeries_one_eq_riemannZeta hs]
  have h := LSeries_eq_mul_integral (fun _ : ℕ => (1 : ℂ))
    (r := 1) zero_le_one hs hS hO
  rw [show -s - 1 = -(s + 1) by ring]
  simpa using h

/-- The fractional-part tail identity, still restricted to `Re s > 1`. -/
theorem fract_cpow_tail_integral_eq {s : ℂ} (hs : 1 < s.re) :
    (∫ t : ℝ in Set.Ioi (1 : ℝ),
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) =
      1 / (s - 1) - riemannZeta s / s := by
  have hfloor := riemannZeta_eq_floor_cpow_integral hs
  have hsplit :
      (∫ t : ℝ in Set.Ioi (1 : ℝ),
          (((Nat.floor t : ℕ) : ℂ) * (t : ℂ) ^ (-s - 1))) =
        (∫ t : ℝ in Set.Ioi (1 : ℝ),
          ((t : ℂ) - ((Int.fract t : ℝ) : ℂ)) * (t : ℂ) ^ (-s - 1)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht' : 1 < t := ht
    have ht0 : 0 ≤ t := by linarith
    change ((Nat.floor t : ℕ) : ℂ) * (t : ℂ) ^ (-s - 1) =
      ((t : ℂ) - ((Int.fract t : ℝ) : ℂ)) * (t : ℂ) ^ (-s - 1)
    rw [show ((Nat.floor t : ℕ) : ℂ) =
        (t : ℂ) - ((Int.fract t : ℝ) : ℂ) by
      norm_cast
      exact natFloor_eq_sub_fract_of_nonneg ht0]
  have hcpow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1))
      (Set.Ioi (1 : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt
    · have he : (-s - 1).re = -s.re - 1 := by norm_num
      rw [he]
      linarith
    · exact one_pos
  have hfrac : IntegrableOn
      (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
      (Set.Ioi (1 : ℝ)) := by
    have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-s - 1))
        (Set.Ioi (1 : ℝ)) := by
      apply continuousOn_of_forall_continuousAt
      intro t ht
      exact continuousAt_ofReal_cpow_const t (-s - 1)
        (Or.inr (by linarith [show (1 : ℝ) < t from ht]))
    have haes : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-s - 1))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      hcont.aestronglyMeasurable measurableSet_Ioi
    have hfractaes : AEStronglyMeasurable
        (fun t : ℝ => ((Int.fract t : ℝ) : ℂ))
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
      exact (Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable.restrict
    have hprod := hfractaes.mul haes
    have hcpow' : Integrable (fun t : ℝ => ‖(t : ℂ) ^ (-s - 1)‖)
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      integrableOn_Ioi_norm_cpow_of_lt (by
        have he : (-s - 1).re = -s.re - 1 := by norm_num
        rw [he]
        linarith) one_pos
    apply Integrable.mono' hcpow'
    · simpa only [IntegrableOn] using hprod
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with t ht
      rw [norm_mul]
      have hnn : 0 ≤ (Int.fract t : ℝ) := Int.fract_nonneg t
      have hlt : (Int.fract t : ℝ) ≤ 1 := (Int.fract_lt_one t).le
      simp only [Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hlt
          (norm_nonneg ((t : ℂ) ^ (-s - 1))))
  have hbase : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s))
      (Set.Ioi (1 : ℝ)) := by
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
      (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-s - 1))
      (Set.Ioi (1 : ℝ)) := by
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := by linarith [show (1 : ℝ) < t from ht]
    change (t : ℂ) ^ (-s) =
      (t : ℂ) * (t : ℂ) ^ (-s - 1)
    exact (hmul t ht0).symm
  have hmain_eq :
      (∫ t : ℝ in Set.Ioi (1 : ℝ),
          (t : ℂ) * (t : ℂ) ^ (-s - 1)) =
        ∫ t : ℝ in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := by linarith [show (1 : ℝ) < t from ht]
    exact hmul t ht0
  have hcalc :
      (∫ t : ℝ in Set.Ioi (1 : ℝ),
          ((t : ℂ) - ((Int.fract t : ℝ) : ℂ)) * (t : ℂ) ^ (-s - 1)) =
        (∫ t : ℝ in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s)) -
          (∫ t : ℝ in Set.Ioi (1 : ℝ),
            ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) := by
    calc
      _ = ∫ t : ℝ in Set.Ioi (1 : ℝ),
          ((fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) t -
            (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) *
              (u : ℂ) ^ (-s - 1)) t) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        ring
      _ = (∫ t : ℝ in Set.Ioi (1 : ℝ),
          (t : ℂ) * (t : ℂ) ^ (-s - 1)) -
          (∫ t : ℝ in Set.Ioi (1 : ℝ),
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
  simp at hfloor
  let F : ℂ := ∫ t : ℝ in Set.Ioi (1 : ℝ),
    ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)
  have hfloor' : riemannZeta s = s * (-1 / (-s + 1) - F) := by
    simpa [F] using hfloor
  change F = 1 / (s - 1) - riemannZeta s / s
  rw [hfloor']
  field_simp [hsne, hs1]
  rw [show (-s + 1 : ℂ) = -(s - 1) by ring]
  have hneg : 1 / (-(s - 1)) = -(1 / (s - 1)) := by
    rw [div_eq_mul_inv, inv_neg]
    simp
  rw [hneg]
  ring

end RH.Criteria.NymanBeurling.BaezDuarte
