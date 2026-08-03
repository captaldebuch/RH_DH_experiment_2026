import RiemannHypothesis.Criteria.NymanBeurling.NymanBeurlingMellinContinuity

/-!
# NB Field 2: zero-detection transport

This file proves the transport implication from the already-proved Mellin
continuity estimate.  The proof uses the criterion directly with an
arbitrarily small error, rather than choosing a separate sequence of
approximants.  The finite Mellin linearity needed for the argument is proved
locally, including the elementary integrability check for the fractional-part
generators.
-/

namespace RH.Criteria.NymanBeurling.RHBridge

open scoped BigOperators
open MeasureTheory Set Complex
open RH.Criteria.NymanBeurling.BaezDuarte

private noncomputable def mellinKernel (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1)

private noncomputable def rhoMellinIntegrand (k : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  mellinKernel s x * ((rhoBD k x : ℝ) : ℂ)

private theorem measurable_rhoBD (k : ℕ) : Measurable (rhoBD k) := by
  unfold rhoBD
  measurability

private theorem rhoBD_eq_inv_on_Ioi (k : ℕ) {x : ℝ} (hx : 1 < x) :
    rhoBD k x = 1 / (((k : ℝ) + 1) * x) := by
  unfold rhoBD
  rw [Int.fract_eq_self.mpr]
  constructor
  · positivity
  · have hden : (1 : ℝ) < ((k : ℝ) + 1) * x := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have ha : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
      calc
        (1 : ℝ) < 1 * x := by nlinarith
        _ ≤ ((k : ℝ) + 1) * x :=
          mul_le_mul_of_nonneg_right ha
            (le_of_lt (lt_trans zero_lt_one hx))
    have hfrac : (1 : ℝ) / (((k : ℝ) + 1) * x) < 1 := by
      apply (div_lt_iff₀ (by positivity :
        (0 : ℝ) < ((k : ℝ) + 1) * x)).2
      simpa only [one_mul] using hden
    exact hfrac

private theorem rho_mellin_integrableOn_Ioc01
    {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    IntegrableOn (rhoMellinIntegrand k s) (Ioc (0 : ℝ) 1) := by
  have hk := intervalIntegral.intervalIntegrable_cpow'
    (r := s - 1) (a := (0 : ℝ)) (b := 1) (by
      rw [Complex.sub_re, Complex.one_re]
      linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hk
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => ((rhoBD k x : ℝ) : ℂ))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (measurable_rhoBD k).complex_ofReal.aestronglyMeasurable.restrict
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖((rhoBD k x : ℝ) : ℂ)‖ ≤ (1 : ℝ) := by
    filter_upwards with x
    unfold rhoBD
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have hnon : 0 ≤ Int.fract (1 / (((k : ℝ) + 1) * x)) := Int.fract_nonneg _
    rw [abs_of_nonneg hnon]
    exact (Int.fract_lt_one _).le
  have hmul := hk.mul_bdd hmeas hbound
  simpa [rhoMellinIntegrand, mellinKernel, smul_eq_mul] using hmul

private theorem rho_mellin_integrableOn_Ioi
    {s : ℂ} (hs : s.re < 1) (k : ℕ) :
    IntegrableOn (rhoMellinIntegrand k s) (Ioi (1 : ℝ)) := by
  have hcpow : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s - 2)) (Ioi (1 : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt
    · change s.re - 2 < -1
      linarith
    · exact one_pos
  have ha : (0 : ℂ) ≠ (((k : ℝ) + 1 : ℝ) : ℂ) := by
    intro h
    have h' : ((k : ℝ) + 1) = 0 := by exact_mod_cast h
    have hpos : 0 < ((k : ℝ) + 1) := by positivity
    linarith
  have hmodel : IntegrableOn
      (fun x : ℝ => (((k : ℝ) + 1 : ℝ) : ℂ)⁻¹ * (x : ℂ) ^ (s - 2))
      (Ioi (1 : ℝ)) := by
    exact hcpow.const_mul _
  apply hmodel.congr_fun _ measurableSet_Ioi
  intro x hx
  have hx0 : (x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hx))
  dsimp [rhoMellinIntegrand, mellinKernel]
  rw [rhoBD_eq_inv_on_Ioi k hx]
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  rw [show s - 2 = (s - 1) - 1 by ring,
    Complex.cpow_sub (s - 1) 1 hx0, Complex.cpow_one]
  field_simp
  simp

private theorem rho_mellin_integrableOn_Ioi_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (k : ℕ) :
    IntegrableOn (rhoMellinIntegrand k s) (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (rho_mellin_integrableOn_Ioc01 hs0 k).union
    (rho_mellin_integrableOn_Ioi hs1 k)

private theorem mellin_rho_eq_integral_integrand
    (k : ℕ) (s : ℂ) :
    mellin (fun x : ℝ => (rhoBD k x : ℂ)) s =
      ∫ x in Ioi (0 : ℝ), rhoMellinIntegrand k s x := by
  rfl

private theorem mellin_bdApprox_zero_of_generators_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hgens : ∀ k : ℕ,
      mellin (fun x : ℝ => (rhoBD k x : ℂ)) s = 0)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    mellin (fun x : ℝ => (bdApprox N coeffs x : ℂ)) s = 0 := by
  unfold mellin bdApprox
  rw [show (fun x : ℝ => (x : ℂ) ^ (s - 1) •
      (↑(∑ k, coeffs k * rhoBD k.val x) : ℂ)) =
      (fun x : ℝ => ∑ k : Fin N,
        (x : ℂ) ^ (s - 1) * (coeffs k : ℂ) *
          (rhoBD k.val x : ℂ)) by
        funext x
        push_cast
        simp only [Complex.ofReal_mul, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro k hk
    rw [show (fun x : ℝ => (x : ℂ) ^ (s - 1) *
        (coeffs k : ℂ) * (rhoBD k.val x : ℂ)) =
        (fun x : ℝ => (coeffs k : ℂ) *
          ((x : ℂ) ^ (s - 1) * (rhoBD k.val x : ℂ))) by
          funext x
          ring]
    rw [MeasureTheory.integral_const_mul]
    have hz : (∫ x in Ioi (0 : ℝ),
        (x : ℂ) ^ (s - 1) * (rhoBD k.val x : ℂ)) = 0 := by
      simpa [mellin, smul_eq_mul] using hgens k.val
    rw [hz]
    simp
  · intro k hk
    have h := rho_mellin_integrableOn_Ioi_zero hs0 hs1 k.val
    simpa [rhoMellinIntegrand, mellinKernel, smul_eq_mul,
      mul_assoc, mul_left_comm, mul_comm] using
      h.const_mul (coeffs k : ℂ)

private theorem chi_mellin_integrableOn
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun x : ℝ => mellinKernel s x * ((chi01 x : ℝ) : ℂ))
      (Ioi (0 : ℝ)) := by
  have hk := intervalIntegral.intervalIntegrable_cpow'
    (r := s - 1) (a := (0 : ℝ)) (b := 1) (by
      rw [Complex.sub_re, Complex.one_re]
      linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hk
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  have hlocal : IntegrableOn
      (fun x : ℝ => mellinKernel s x * ((chi01 x : ℝ) : ℂ))
      (Ioc (0 : ℝ) 1) := by
    apply hk.congr_fun _ measurableSet_Ioc
    intro x hx
    have hchi : chi01 x = 1 := by
      simp [chi01, hx.1, hx.2]
    simp [mellinKernel, hchi]
  have htail : IntegrableOn
      (fun x : ℝ => mellinKernel s x * ((chi01 x : ℝ) : ℂ))
      (Ioi (1 : ℝ)) := by
    apply integrableOn_zero.congr_fun _ measurableSet_Ioi
    intro x hx
    have hx' : 1 < x := hx
    have hchi : chi01 x = 0 := by
      simp [chi01, not_le_of_gt hx']
    simp [hchi]
  exact hlocal.union htail

private theorem bdApprox_mellin_integrableOn
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    IntegrableOn
      (fun x : ℝ => mellinKernel s x * ((bdApprox N coeffs x : ℝ) : ℂ))
      (Ioi (0 : ℝ)) := by
  have hsum : IntegrableOn
      (fun x : ℝ => ∑ k : Fin N,
        mellinKernel s x * (coeffs k : ℂ) * (rhoBD k.val x : ℂ))
      (Ioi (0 : ℝ)) := by
    apply MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin N))
    intro k hk
    have h := rho_mellin_integrableOn_Ioi_zero hs0 hs1 k.val
    simpa [mellinKernel, rhoMellinIntegrand, smul_eq_mul, mul_assoc,
      mul_left_comm, mul_comm] using h.const_mul (coeffs k : ℂ)
  apply hsum.congr_fun _ measurableSet_Ioi
  intro x hx
  unfold bdApprox
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem mellin_sub_chi_bdApprox
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    mellin (fun x : ℝ => ((chi01 x - bdApprox N coeffs x : ℝ) : ℂ)) s =
      mellin (fun x : ℝ => (chi01 x : ℂ)) s -
        mellin (fun x : ℝ => (bdApprox N coeffs x : ℂ)) s := by
  have hchi := chi_mellin_integrableOn (s := s) hs0
  have hbd := bdApprox_mellin_integrableOn hs0 hs1 N coeffs
  unfold mellin
  simp only [smul_eq_mul]
  have hsub := MeasureTheory.integral_sub hchi hbd
  change (∫ x in Ioi (0 : ℝ), mellinKernel s x *
      (((chi01 x - bdApprox N coeffs x : ℝ) : ℂ))) =
    (∫ x in Ioi (0 : ℝ), mellinKernel s x * ((chi01 x : ℝ) : ℂ)) -
      ∫ x in Ioi (0 : ℝ), mellinKernel s x *
        ((bdApprox N coeffs x : ℝ) : ℂ)
  have hfun :
      (fun x : ℝ => mellinKernel s x *
        (((chi01 x - bdApprox N coeffs x : ℝ) : ℂ))) =
      (fun x : ℝ => mellinKernel s x * ((chi01 x : ℝ) : ℂ) -
        mellinKernel s x * ((bdApprox N coeffs x : ℝ) : ℂ)) := by
    funext x
    rw [Complex.ofReal_sub]
    ring
  rw [hfun]
  exact hsub

/-- Field 2 from the Field 1 continuity estimate. -/
theorem vanishing_transport_of_field_1
    (hfield1 :
      ∀ s₀ : ℂ, 1 / 2 < s₀.re → s₀.re < 1 → s₀ ≠ 0 →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ (N : ℕ) (coeffs : Fin N → ℝ),
            ‖mellin
                (fun x : ℝ =>
                  ((chi01 x - bdApprox N coeffs x : ℝ) : ℂ)) s₀‖ ≤
              C * Real.sqrt (BaezDuarteL2Error N coeffs))
    (s₀ : ℂ) (hs0 : 1 / 2 < s₀.re) (hs1 : s₀.re < 1) (hsne : s₀ ≠ 0)
    (hcriterion : NymanBeurlingCriterion)
    (hgens : ∀ k : ℕ,
      mellin (fun x : ℝ => (rhoBD k x : ℂ)) s₀ = 0) :
    mellin (fun x : ℝ => (chi01 x : ℂ)) s₀ = 0 := by
  obtain ⟨C, hC, hbound⟩ := hfield1 s₀ hs0 hs1 hsne
  by_contra hchi_ne
  have hR : 0 < ‖mellin (fun x : ℝ => (chi01 x : ℂ)) s₀‖ :=
    (norm_pos_iff.mpr hchi_ne)
  by_cases hCzero : C = 0
  · obtain ⟨N, coeffs, herr⟩ := hcriterion 1 zero_lt_one
    have hbdzero := mellin_bdApprox_zero_of_generators_zero
      (by linarith [hs0]) hs1 hgens N coeffs
    have hsub := mellin_sub_chi_bdApprox (by linarith [hs0]) hs1 N coeffs
    have herr_norm := hbound N coeffs
    rw [hsub, hbdzero, sub_zero, hCzero, zero_mul] at herr_norm
    have hzero :
        mellin (fun x : ℝ => ((chi01 x : ℝ) : ℂ)) s₀ = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm herr_norm (norm_nonneg _)
    exact hchi_ne hzero
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have htarget : 0 < (‖mellin (fun x : ℝ => (chi01 x : ℂ)) s₀‖ / C) ^ 2 := by
      positivity
    obtain ⟨N, coeffs, herr⟩ := hcriterion _ htarget
    have hbdzero := mellin_bdApprox_zero_of_generators_zero
      (by linarith [hs0]) hs1 hgens N coeffs
    have hsub := mellin_sub_chi_bdApprox (by linarith [hs0]) hs1 N coeffs
    have herr_nonneg : 0 ≤ BaezDuarteL2Error N coeffs :=
      baezDuarteL2Error_nonneg N coeffs
    have hsqrt : Real.sqrt (BaezDuarteL2Error N coeffs) <
        ‖mellin (fun x : ℝ => (chi01 x : ℂ)) s₀‖ / C := by
      apply (Real.sqrt_lt' (by positivity)).2
      simpa only [div_pow] using herr
    have hnorm := hbound N coeffs
    rw [hsub, hbdzero, sub_zero] at hnorm
    have hstrict : C * Real.sqrt (BaezDuarteL2Error N coeffs) <
        ‖mellin (fun x : ℝ => (chi01 x : ℂ)) s₀‖ := by
      calc
        C * Real.sqrt (BaezDuarteL2Error N coeffs) <
            C * (‖mellin (fun x : ℝ => (chi01 x : ℂ)) s₀‖ / C) :=
          mul_lt_mul_of_pos_left hsqrt hCpos
        _ = ‖mellin (fun x : ℝ => (chi01 x : ℂ)) s₀‖ := by
          field_simp
    exact (not_lt_of_ge hnorm) hstrict

/-- The zero-transport debt package obtained from a supplied Field 1 proof. -/
noncomputable def mellinNymanBridgeDebts_complete
    (hfield1 :
      ∀ s₀ : ℂ, 1 / 2 < s₀.re → s₀.re < 1 → s₀ ≠ 0 →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ (N : ℕ) (coeffs : Fin N → ℝ),
            ‖mellin
                (fun x : ℝ =>
                  ((chi01 x - bdApprox N coeffs x : ℝ) : ℂ)) s₀‖ ≤
              C * Real.sqrt (BaezDuarteL2Error N coeffs)) :
    MellinNymanBridgeDebts := by
  refine
    { mellin_chi_eval := BaezDuarte.mellin_chi_eval_proved
      mellin_generator_eval := ?_
      eval_functional_continuous := hfield1
      vanishing_transport := ?_ }
  · intro k s hsright hslt hsne
    exact BaezDuarte.mellin_generator_eval_proved k s (by linarith) hslt hsne
  · intro s hsright hslt hsne hcriterion hgens
    exact vanishing_transport_of_field_1 hfield1 s hsright hslt hsne
      hcriterion hgens

/-- Instantiation using the theorem-level Field 1 proof from the preceding
Mellin-continuity file. -/
noncomputable def mellinNymanBridgeDebts_complete_proved :
    MellinNymanBridgeDebts :=
  mellinNymanBridgeDebts_complete
    RH.Criteria.NymanBeurling.mellin_evaluation_continuous_on_critical_strip

/-- The forward bridge obtained after supplying the proved Field 1 and Field 2
transport.  This is additive; existing RH bridge consumers remain unchanged. -/
theorem NBForward_of_complete_mellinNymanBridgeDebts : NBForward :=
  NBForward_of_mellin_transport_debts
    { eval_functional_continuous :=
        RH.Criteria.NymanBeurling.mellin_evaluation_continuous_on_critical_strip
      vanishing_transport := by
        intro s hsright hslt hsne hcriterion hgens
        exact vanishing_transport_of_field_1
          RH.Criteria.NymanBeurling.mellin_evaluation_continuous_on_critical_strip
          s hsright hslt hsne hcriterion hgens }

end RH.Criteria.NymanBeurling.RHBridge
