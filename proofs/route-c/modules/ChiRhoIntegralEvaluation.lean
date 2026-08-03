import Mathlib

open scoped BigOperators

namespace RH.Criteria.NymanBeurling.ChiRhoIntegralEvaluation

open MeasureTheory

noncomputable def chiRhoBaseIntegrand (x : ℝ) : ℝ := Int.fract (1 / x)

def chiRhoShell (n : ℕ) : Set ℝ :=
  Set.Ioc (1 / ((n + 2 : ℕ) : ℝ)) (1 / ((n + 1 : ℕ) : ℝ))

theorem measurable_chiRhoBaseIntegrand : Measurable chiRhoBaseIntegrand := by
  unfold chiRhoBaseIntegrand
  measurability

theorem norm_chiRhoBaseIntegrand_le_one (x : ℝ) :
    ‖chiRhoBaseIntegrand x‖ ≤ 1 := by
  unfold chiRhoBaseIntegrand
  rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

theorem integrableOn_chiRhoBaseIntegrand_Ioc_zero_one :
    IntegrableOn chiRhoBaseIntegrand (Set.Ioc (0 : ℝ) 1) := by
  apply Integrable.mono' (g := fun _ : ℝ => (1 : ℝ))
  · exact integrableOn_const measure_Ioc_lt_top.ne
  · exact measurable_chiRhoBaseIntegrand.aestronglyMeasurable.restrict
  · exact Filter.Eventually.of_forall (fun x => norm_chiRhoBaseIntegrand_le_one x)

theorem fract_inv_eq_sub_nat_on_shell (n : ℕ) {x : ℝ}
    (hx : x ∈ chiRhoShell n) :
    chiRhoBaseIntegrand x = 1 / x - (n + 1 : ℕ) := by
  have hmpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hMpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hleft : 1 / (((n + 2 : ℕ) : ℝ)) < x := hx.1
  have hright : x ≤ 1 / (((n + 1 : ℕ) : ℝ)) := hx.2
  have hxpos : 0 < x := (one_div_pos.mpr hMpos).trans hleft
  have hlower : (((n + 1 : ℕ) : ℝ)) ≤ 1 / x := by
    rw [le_div_iff₀ hxpos]
    calc
      ((n + 1 : ℕ) : ℝ) * x
          ≤ ((n + 1 : ℕ) : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hright hmpos.le
      _ = 1 := by field_simp
  have hupper : 1 / x < (((n + 2 : ℕ) : ℝ)) := by
    rw [div_lt_iff₀ hxpos]
    calc
      1 = ((n + 2 : ℕ) : ℝ) * (1 / ((n + 2 : ℕ) : ℝ)) :=
        by field_simp
      _ < ((n + 2 : ℕ) : ℝ) * x := mul_lt_mul_of_pos_left hleft hMpos
  have hfloor : ⌊1 / x⌋ = ((n + 1 : ℕ) : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · exact_mod_cast hlower
    · exact_mod_cast hupper
  unfold chiRhoBaseIntegrand Int.fract
  rw [hfloor]
  push_cast
  rfl

theorem chiRho_shell_integral (n : ℕ) :
    (∫ x in chiRhoShell n, chiRhoBaseIntegrand x) =
      Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) -
        1 / (((n + 2 : ℕ) : ℝ)) := by
  let a : ℝ := 1 / (((n + 2 : ℕ) : ℝ))
  let b : ℝ := 1 / (((n + 1 : ℕ) : ℝ))
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    apply one_div_le_one_div_of_le (by positivity)
    norm_num
  have hpoint : ∀ x ∈ Set.Ioc a b,
      chiRhoBaseIntegrand x = 1 / x - ((n + 1 : ℕ) : ℝ) := by
    intro x hx
    exact fract_inv_eq_sub_nat_on_shell n hx
  rw [show chiRhoShell n = Set.Ioc a b by rfl]
  rw [setIntegral_congr_fun measurableSet_Ioc hpoint]
  rw [← intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_sub]
  · rw [integral_one_div_of_pos ha hb]
    simp only [intervalIntegral.integral_const]
    dsimp [a, b]
    have hm : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hM : (((n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
    rw [show (1 / (((n + 1 : ℕ) : ℝ))) / (1 / (((n + 2 : ℕ) : ℝ))) =
        (((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ)) by field_simp]
    field_simp
    push_cast
    ring
  · apply intervalIntegral.intervalIntegrable_one_div
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ne_of_gt (ha.trans_le hx.1)
    · exact continuousOn_id
  · exact intervalIntegral.intervalIntegrable_const

theorem Ioc_zero_one_eq_iUnion_chiRhoShell :
    Set.Ioc (0 : ℝ) 1 = ⋃ n : ℕ, chiRhoShell n := by
  ext x
  simp only [Set.mem_Ioc, Set.mem_iUnion]
  constructor
  · intro hx
    have hxpos : 0 < x := hx.1
    have ht_nonneg : 0 ≤ 1 / x := (one_div_pos.mpr hxpos).le
    have ht_one : 1 ≤ 1 / x := by
      rw [le_div_iff₀ hxpos]
      simpa using hx.2
    let m : ℕ := ⌊1 / x⌋₊
    have hmpos : 0 < m := by
      dsimp [m]
      exact Nat.floor_pos.mpr ht_one
    have hm_le : (m : ℝ) ≤ 1 / x := by
      dsimp [m]
      exact Nat.floor_le ht_nonneg
    have ht_lt : 1 / x < (m : ℝ) + 1 := by
      dsimp [m]
      exact Nat.lt_floor_add_one _
    refine ⟨m - 1, ?_⟩
    have hm_eq : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hmpos.ne')
    have hm2_eq : m - 1 + 2 = m + 1 := by omega
    rw [chiRhoShell, Set.mem_Ioc, hm_eq, hm2_eq]
    constructor
    · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m + 1 : ℕ))]
      rw [div_lt_iff₀ hxpos] at ht_lt
      push_cast at ht_lt ⊢
      nlinarith
    · rw [le_div_iff₀ (by exact_mod_cast hmpos)]
      rw [le_div_iff₀ hxpos] at hm_le
      simpa [mul_comm] using hm_le
  · rintro ⟨n, hn⟩
    rw [chiRhoShell, Set.mem_Ioc] at hn
    constructor
    · exact (one_div_pos.mpr (by positivity)).trans hn.1
    · calc
        x ≤ 1 / (((n + 1 : ℕ) : ℝ)) := hn.2
        _ ≤ 1 := by
          simpa only [one_div_one] using
            (one_div_le_one_div_of_le zero_lt_one
              (show (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by norm_num))

theorem pairwiseDisjoint_chiRhoShell :
    Pairwise (fun i j : ℕ => Disjoint (chiRhoShell i) (chiRhoShell j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  rw [chiRhoShell, Set.mem_Ioc] at hxi hxj
  rcases lt_trichotomy i j with hijlt | hijeq | hjilt
  · have hnat : i + 2 ≤ j + 1 := by omega
    have hinv : 1 / (((j + 1 : ℕ) : ℝ)) ≤ 1 / (((i + 2 : ℕ) : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast hnat
    linarith
  · exact hij hijeq
  · have hnat : j + 2 ≤ i + 1 := by omega
    have hinv : 1 / (((i + 1 : ℕ) : ℝ)) ≤ 1 / (((j + 2 : ℕ) : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast hnat
    linarith

theorem hasSum_chiRho_shell_integrals :
    HasSum (fun n : ℕ => ∫ x in chiRhoShell n, chiRhoBaseIntegrand x)
      (∫ x in Set.Ioc (0 : ℝ) 1, chiRhoBaseIntegrand x) := by
  have hsum : HasSum
      (fun n : ℕ => ∫ x in chiRhoShell n, chiRhoBaseIntegrand x)
      (∫ x in ⋃ n : ℕ, chiRhoShell n, chiRhoBaseIntegrand x) := by
    apply hasSum_integral_iUnion
    · intro n
      exact measurableSet_Ioc
    · exact pairwiseDisjoint_chiRhoShell
    · rw [← Ioc_zero_one_eq_iUnion_chiRhoShell]
      exact integrableOn_chiRhoBaseIntegrand_Ioc_zero_one
  rwa [← Ioc_zero_one_eq_iUnion_chiRhoShell] at hsum

noncomputable def chiRhoShellTerm (n : ℕ) : ℝ :=
  Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) -
    1 / (((n + 2 : ℕ) : ℝ))

theorem hasSum_chiRhoShellTerm_integral :
    HasSum chiRhoShellTerm
      (∫ x in Set.Ioc (0 : ℝ) 1, chiRhoBaseIntegrand x) := by
  have hfun : chiRhoShellTerm =
      (fun n : ℕ => ∫ x in chiRhoShell n, chiRhoBaseIntegrand x) := by
    funext n
    exact (chiRho_shell_integral n).symm
  rw [hfun]
  exact hasSum_chiRho_shell_integrals

theorem sum_range_chiRhoShellTerm (N : ℕ) :
    ∑ n ∈ Finset.range N, chiRhoShellTerm n =
      Real.log ((N + 1 : ℕ) : ℝ) + 1 - (harmonic (N + 1) : ℝ) := by
  induction N with
  | zero => norm_num [chiRhoShellTerm, harmonic]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    unfold chiRhoShellTerm
    push_cast
    have hharm : (harmonic (N + 1 + 1) : ℝ) =
        (harmonic (N + 1) : ℝ) + 1 / ((N : ℝ) + 2) := by
      rw [harmonic_succ]
      push_cast
      ring_nf
    rw [hharm]
    have hNp1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have hNp2 : (N : ℝ) + 2 ≠ 0 := by positivity
    rw [Real.log_div hNp2 hNp1]
    ring_nf

theorem chiRhoShellTerm_partial_sums_tendsto :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, chiRhoShellTerm n)
      Filter.atTop (nhds (1 - Real.eulerMascheroniConstant)) := by
  have hharm : Filter.Tendsto
      (fun N : ℕ => (harmonic (N + 1) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ))
      Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    exact Real.tendsto_harmonic_sub_log.comp (Filter.tendsto_add_atTop_nat 1)
  have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub hharm
  convert hsub using 1
  funext N
  rw [sum_range_chiRhoShellTerm]
  ring

theorem chiRhoBaseIntegral_formula :
    (∫ x in Set.Ioc (0 : ℝ) 1, chiRhoBaseIntegrand x) =
      1 - Real.eulerMascheroniConstant := by
  exact tendsto_nhds_unique
    hasSum_chiRhoShellTerm_integral.tendsto_sum_nat
    chiRhoShellTerm_partial_sums_tendsto

noncomputable def chiRhoIntegral (K : ℕ) : ℝ :=
  ∫ x in Set.Ioc (0 : ℝ) 1, Int.fract (1 / ((K : ℝ) * x))

noncomputable def chiRhoIntegrand (K : ℕ) (x : ℝ) : ℝ :=
  Int.fract (1 / ((K : ℝ) * x))

theorem measurable_chiRhoIntegrand (K : ℕ) : Measurable (chiRhoIntegrand K) := by
  unfold chiRhoIntegrand
  measurability

theorem norm_chiRhoIntegrand_le_one (K : ℕ) (x : ℝ) :
    ‖chiRhoIntegrand K x‖ ≤ 1 := by
  unfold chiRhoIntegrand
  rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

theorem integrableOn_chiRhoIntegrand_Ioc (K : ℕ) (a b : ℝ) :
    IntegrableOn (chiRhoIntegrand K) (Set.Ioc a b) := by
  apply Integrable.mono' (g := fun _ : ℝ => (1 : ℝ))
  · exact integrableOn_const measure_Ioc_lt_top.ne
  · exact (measurable_chiRhoIntegrand K).aestronglyMeasurable.restrict
  · exact Filter.Eventually.of_forall (fun x => norm_chiRhoIntegrand_le_one K x)

theorem chiRhoIntegrand_eq_scaled_base (K : ℕ) (x : ℝ) :
    chiRhoIntegrand K x = chiRhoBaseIntegrand ((K : ℝ) * x) := by
  rfl

theorem chiRhoIntegral_low (K : ℕ) (hK : 0 < K) :
    (∫ x in Set.Ioc (0 : ℝ) (1 / (K : ℝ)), chiRhoIntegrand K x) =
      (1 - Real.eulerMascheroniConstant) / (K : ℝ) := by
  have hKreal : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  have hKne : (K : ℝ) ≠ 0 := hKreal.ne'
  rw [← intervalIntegral.integral_of_le (one_div_nonneg.mpr hKreal.le)]
  have hscale := intervalIntegral.mul_integral_comp_mul_left
    (f := chiRhoBaseIntegrand) (a := (0 : ℝ)) (b := 1 / (K : ℝ)) (K : ℝ)
  have hscale' : (K : ℝ) *
      (∫ x in (0 : ℝ)..(1 / (K : ℝ)), chiRhoIntegrand K x) =
      ∫ x in (0 : ℝ)..1, chiRhoBaseIntegrand x := by
    simpa only [chiRhoIntegrand_eq_scaled_base, mul_zero, mul_one_div_cancel hKne] using hscale
  have hbaseInterval : (∫ x in (0 : ℝ)..1, chiRhoBaseIntegrand x) =
      1 - Real.eulerMascheroniConstant := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact chiRhoBaseIntegral_formula
  rw [hbaseInterval] at hscale'
  apply (eq_div_iff hKne).2
  nlinarith

theorem chiRhoIntegrand_eq_inv_on_top (K : ℕ) (hK : 0 < K) {x : ℝ}
    (hx : x ∈ Set.Ioc (1 / (K : ℝ)) 1) :
    chiRhoIntegrand K x = 1 / ((K : ℝ) * x) := by
  have hKreal : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  have hxpos : 0 < x := (one_div_pos.mpr hKreal).trans hx.1
  have hargpos : 0 < 1 / ((K : ℝ) * x) := one_div_pos.mpr (mul_pos hKreal hxpos)
  have harglt : 1 / ((K : ℝ) * x) < 1 := by
    rw [div_lt_one (mul_pos hKreal hxpos)]
    calc
      1 = (K : ℝ) * (1 / (K : ℝ)) := by field_simp
      _ < (K : ℝ) * x := mul_lt_mul_of_pos_left hx.1 hKreal
  unfold chiRhoIntegrand
  exact Int.fract_eq_self.mpr ⟨hargpos.le, harglt⟩

theorem chiRhoIntegral_top (K : ℕ) (hK : 0 < K) :
    (∫ x in Set.Ioc (1 / (K : ℝ)) 1, chiRhoIntegrand K x) =
      Real.log (K : ℝ) / (K : ℝ) := by
  have hKreal : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  have hKne : (K : ℝ) ≠ 0 := hKreal.ne'
  have hKone : (1 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hK
  have hle : 1 / (K : ℝ) ≤ 1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one hKone
  rw [setIntegral_congr_fun measurableSet_Ioc
    (fun x hx => chiRhoIntegrand_eq_inv_on_top K hK hx)]
  rw [← intervalIntegral.integral_of_le hle]
  have hfun : (fun x : ℝ => 1 / ((K : ℝ) * x)) =
      (fun x : ℝ => (1 / (K : ℝ)) * (1 / x)) := by
    funext x
    field_simp
  rw [hfun, intervalIntegral.integral_const_mul]
  rw [integral_one_div_of_pos (one_div_pos.mpr hKreal) zero_lt_one]
  rw [show (1 : ℝ) / (1 / (K : ℝ)) = (K : ℝ) by field_simp]
  field_simp

theorem chiRhoIntegral_formula (K : ℕ) (hK : 0 < K) :
    chiRhoIntegral K =
      (Real.log (K : ℝ) + 1 - Real.eulerMascheroniConstant) / (K : ℝ) := by
  have hKreal : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  have hKone : (1 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hK
  have hsplit : Set.Ioc (0 : ℝ) 1 =
      Set.Ioc 0 (1 / (K : ℝ)) ∪ Set.Ioc (1 / (K : ℝ)) 1 := by
    ext x
    simp only [Set.mem_Ioc, Set.mem_union]
    constructor
    · intro hx
      by_cases h : x ≤ 1 / (K : ℝ)
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨lt_of_not_ge h, hx.2⟩
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.trans (by
          simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one hKone)⟩
      · exact ⟨(one_div_pos.mpr hKreal).trans hx.1, hx.2⟩
  have hdisjoint : Disjoint (Set.Ioc (0 : ℝ) (1 / (K : ℝ)))
      (Set.Ioc (1 / (K : ℝ)) 1) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy.1
  unfold chiRhoIntegral
  change (∫ x in Set.Ioc (0 : ℝ) 1, chiRhoIntegrand K x) = _
  rw [hsplit, setIntegral_union hdisjoint measurableSet_Ioc
    (integrableOn_chiRhoIntegrand_Ioc K _ _)
    (integrableOn_chiRhoIntegrand_Ioc K _ _)]
  rw [chiRhoIntegral_low K hK, chiRhoIntegral_top K hK]
  ring


end RH.Criteria.NymanBeurling.ChiRhoIntegralEvaluation
