import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace RH.Criteria.NymanBeurling.VasyuninGram

open scoped MeasureTheory

/-- The Euler-Mascheroni constant γ, mapped to Mathlib's formal definition -/
noncomputable def EulerGamma : ℝ := Real.eulerMascheroniConstant

noncomputable def G11OriginalIntegrand (x : ℝ) : ℝ :=
  (Int.fract (1 / x)) ^ 2

noncomputable def G11Integral : ℝ :=
  ∫ x in Set.Ioi (0:ℝ), G11OriginalIntegrand x

noncomputable def G11TransformedIntegrand (t : ℝ) : ℝ :=
  (Int.fract t) ^ 2 / t ^ 2

noncomputable def G11TransformedIntegral : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), G11TransformedIntegrand t

noncomputable def invPositiveMap (x : ℝ) : ℝ := 1 / x

noncomputable def G11OriginalTruncation (R : ℝ) : ℝ :=
  ∫ x in Set.Ioc (1 / R) R, G11OriginalIntegrand x

noncomputable def G11TransformedTruncation (R : ℝ) : ℝ :=
  ∫ t in Set.Ioc (1 / R) R, G11TransformedIntegrand t

theorem one_div_pos_of_one_lt {R : ℝ} (hR : 1 < R) :
    0 < 1 / R := by
  positivity

theorem one_div_le_self_of_one_lt {R : ℝ} (hR : 1 < R) :
    1 / R ≤ R := by
  have hRpos : 0 < R := by linarith
  have h1 : 1 / R < 1 := (div_lt_one hRpos).mpr hR
  linarith

theorem G11OriginalTruncation_eq_intervalIntegral
    {R : ℝ} (hR : 1 < R) :
    G11OriginalTruncation R =
      ∫ x in (1 / R)..R, G11OriginalIntegrand x := by
  unfold G11OriginalTruncation
  rw [intervalIntegral.integral_of_le (one_div_le_self_of_one_lt hR)]

theorem G11TransformedTruncation_eq_intervalIntegral
    {R : ℝ} (hR : 1 < R) :
    G11TransformedTruncation R =
      ∫ t in (1 / R)..R, G11TransformedIntegrand t := by
  unfold G11TransformedTruncation
  rw [intervalIntegral.integral_of_le (one_div_le_self_of_one_lt hR)]

noncomputable def G11OpenOriginalTruncation (R : ℝ) : ℝ :=
  ∫ x in Set.Ioo (1 / R) R, G11OriginalIntegrand x

noncomputable def G11OpenTransformedTruncation (R : ℝ) : ℝ :=
  ∫ t in Set.Ioo (1 / R) R, G11TransformedIntegrand t

theorem intervalIntegral_eq_open_setIntegral_original
    {R : ℝ} (hR : 1 < R) :
    (∫ x in (1 / R)..R, G11OriginalIntegrand x)
      =
    G11OpenOriginalTruncation R := by
  have hRpos : 0 < R := by linarith
  have h_le : 1 / R ≤ R := by
    have h1 : 1 / R < 1 := (div_lt_one hRpos).mpr hR
    linarith
  rw [intervalIntegral.integral_of_le h_le]
  unfold G11OpenOriginalTruncation
  exact MeasureTheory.integral_Ioc_eq_integral_Ioo

theorem intervalIntegral_eq_open_setIntegral_transformed
    {R : ℝ} (hR : 1 < R) :
    (∫ t in (1 / R)..R, G11TransformedIntegrand t)
      =
    G11OpenTransformedTruncation R := by
  have hRpos : 0 < R := by linarith
  have h_le : 1 / R ≤ R := by
    have h1 : 1 / R < 1 := (div_lt_one hRpos).mpr hR
    linarith
  rw [intervalIntegral.integral_of_le h_le]
  unfold G11OpenTransformedTruncation
  exact MeasureTheory.integral_Ioc_eq_integral_Ioo

theorem G11OriginalIntegrand_inv_mul_abs_deriv_eq_transformed
    {t : ℝ} (_ht : t ≠ 0) :
    G11OriginalIntegrand (1 / t) * (1 / t ^ 2)
      =
    G11TransformedIntegrand t := by
  unfold G11OriginalIntegrand G11TransformedIntegrand
  have h1 : 1 / (1 / t) = t := one_div_one_div t
  rw [h1]
  ring

axiom setIntegral_Ioo_inv_substitution_bridge
    {R : ℝ} (hR : 1 < R)
    {f : ℝ → ℝ}
    (hf_meas : Measurable f)
    (hf_int : MeasureTheory.IntegrableOn f (Set.Ioo (1 / R) R)) :
    (∫ x in Set.Ioo (1 / R) R, f (1 / x))
      =
    (∫ t in Set.Ioo (1 / R) R, f t * (1 / t ^ 2))

/-- Int.fract squared is Borel-measurable on ℝ.
    Follows from measurability of Int.fract (Mathlib: `measurable_fract`) and
    closure of Measurable under polynomial operations. -/
theorem intFract_sq_measurable : Measurable (fun t : ℝ => (Int.fract t)^2) :=
  measurable_fract.pow_const 2

/-- Int.fract squared is integrable on any open interval (1/R, R) with R > 1.
    Proof: (Int.fract t)^2 ≤ 1 everywhere, so we dominate by the constant 1 on
    the finite-measure interval Ioo (1/R) R. -/
theorem intFract_sq_integrableOn_Ioo {R : ℝ} (hR : 1 < R) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Int.fract t)^2) (Set.Ioo (1 / R) R) := by
  apply MeasureTheory.Measure.integrableOn_of_bounded (M := 1) (measure_Ioo_lt_top.ne)
  · exact intFract_sq_measurable.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t
    have h1 : Int.fract t < 1 := Int.fract_lt_one t
    have h2 : 0 ≤ Int.fract t := Int.fract_nonneg t
    have h3 : (Int.fract t) ^ 2 ≤ 1 := by nlinarith
    have h4 : 0 ≤ (Int.fract t) ^ 2 := sq_nonneg _
    simp only [Real.norm_eq_abs, abs_of_nonneg h4]
    exact h3

theorem open_inverse_substitution_truncation
    {R : ℝ} (hR : 1 < R) :
    G11OpenOriginalTruncation R =
    G11OpenTransformedTruncation R := by
  unfold G11OpenOriginalTruncation G11OpenTransformedTruncation
  have h1 : (∫ x in Set.Ioo (1 / R) R, G11OriginalIntegrand x) =
            (∫ x in Set.Ioo (1 / R) R, (fun t => (Int.fract t)^2) (1 / x)) := by
    apply MeasureTheory.setIntegral_congr_fun
    · exact measurableSet_Ioo
    · intro x hx
      unfold G11OriginalIntegrand
      rfl
  rw [h1]
  have h2 := setIntegral_Ioo_inv_substitution_bridge hR
    (f := fun t => (Int.fract t)^2)
    (hf_meas := intFract_sq_measurable)
    (hf_int := intFract_sq_integrableOn_Ioo hR)
  rw [h2]
  apply MeasureTheory.setIntegral_congr_fun
  · exact measurableSet_Ioo
  · intro t ht
    have ht_ne : t ≠ 0 := by
      have hRpos : 0 < R := by linarith
      have hleft : 0 < 1 / R := one_div_pos.mpr hRpos
      exact ne_of_gt (lt_trans hleft ht.1)
    unfold G11TransformedIntegrand
    ring

theorem intervalIntegral_inv_substitution
    {R : ℝ} (hR : 1 < R) :
    (∫ x in (1 / R)..R, G11OriginalIntegrand x)
      =
    (∫ t in (1 / R)..R, G11TransformedIntegrand t) := by
  rw [
    intervalIntegral_eq_open_setIntegral_original hR,
    intervalIntegral_eq_open_setIntegral_transformed hR
  ]
  exact open_inverse_substitution_truncation hR

theorem finite_inverse_substitution_truncation
    {R : ℝ} (hR : 1 < R) :
    G11OriginalTruncation R = G11TransformedTruncation R := by
  rw [G11OriginalTruncation_eq_intervalIntegral hR]
  rw [G11TransformedTruncation_eq_intervalIntegral hR]
  exact intervalIntegral_inv_substitution hR



noncomputable def G11UnitIntegral (n : ℕ) : ℝ :=
  ∫ t in ((n : ℝ))..((n + 1 : ℝ)),
    G11TransformedIntegrand t

noncomputable def G11IntervalSeries : ℝ :=
  ∑' n : ℕ, G11UnitIntegral n

noncomputable def G11UnitSetIntegral (n : ℕ) : ℝ :=
  ∫ t in Set.Ioc ((n : ℝ)) ((n + 1 : ℝ)),
    G11TransformedIntegrand t

noncomputable def G11SetIntegralSeries : ℝ :=
  ∑' n : ℕ, G11UnitSetIntegral n

theorem Ioi_zero_eq_iUnion_Ioc_nat :
  Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Ioc ((n : ℝ)) ((n + 1 : ℝ)) := by
  ext x
  simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
  constructor
  · intro hx
    use ⌈x⌉₊ - 1
    have h1 : 1 ≤ ⌈x⌉₊ := Nat.ceil_pos.mpr hx
    have h2 : ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 = (⌈x⌉₊ : ℝ) := by
      rw [Nat.cast_sub h1, Nat.cast_one, sub_add_cancel]
    constructor
    · rw [Nat.cast_sub h1, Nat.cast_one]
      have h3 := Nat.ceil_lt_add_one hx.le
      linarith
    · rw [h2]
      exact Nat.le_ceil x
  · rintro ⟨n, hn₁, _⟩
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

theorem pairwiseDisjoint_Ioc_nat :
  Pairwise (fun i j : ℕ => Disjoint (Set.Ioc ((i : ℝ)) ((i + 1 : ℝ))) (Set.Ioc ((j : ℝ)) ((j + 1 : ℝ)))) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx hy
  rw [Set.mem_Ioc] at hx hy
  rcases lt_trichotomy i j with h | h | h
  · have h1 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    linarith
  · exact hij h
  · have h1 : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    linarith

theorem G11TransformedIntegrand_nonneg
    {t : ℝ} (_ : 0 < t) :
    0 ≤ G11TransformedIntegrand t := by
  unfold G11TransformedIntegrand
  apply div_nonneg
  · exact sq_nonneg _
  · exact sq_nonneg _

theorem abs_G11TransformedIntegrand_eq
    {t : ℝ} (ht : 0 < t) :
    ‖G11TransformedIntegrand t‖ = G11TransformedIntegrand t := by
  rw [Real.norm_eq_abs, abs_of_nonneg]
  exact G11TransformedIntegrand_nonneg ht

theorem G11TransformedIntegrand_le_inv_sq_on_Ioi_one
    {t : ℝ} (ht : t ∈ Set.Ioi (1 : ℝ)) :
    ‖G11TransformedIntegrand t‖ ≤ 1 / t^2 := by
  rw [Set.mem_Ioi] at ht
  have ht_pos : 0 < t := by linarith
  rw [abs_G11TransformedIntegrand_eq ht_pos]
  unfold G11TransformedIntegrand
  have h1 : (Int.fract t)^2 ≤ 1 := by
    have h2 : Int.fract t < 1 := Int.fract_lt_one t
    have h3 : 0 ≤ Int.fract t := Int.fract_nonneg t
    nlinarith
  have h_t_sq_pos : 0 < t^2 := sq_pos_of_ne_zero (ne_of_gt ht_pos)
  exact div_le_div_of_nonneg_right h1 (sq_nonneg t)

theorem one_div_sq_eq_rpow_neg_two_on_Ioi_one
    {t : ℝ} (ht : t ∈ Set.Ioi (1 : ℝ)) :
    1 / t^2 = t ^ (-2 : ℝ) := by
  have ht_gt_one : 1 < t := ht
  have ht_pos : 0 < t := lt_trans zero_lt_one ht_gt_one
  rw [Real.rpow_neg ht_pos.le]
  have h_rpow_two : t ^ (2 : ℝ) = t ^ 2 := by
    exact Real.rpow_two t
  rw [h_rpow_two]
  exact one_div (t ^ 2)

theorem integrableOn_inv_sq_Ioi_one :
  MeasureTheory.IntegrableOn (fun t : ℝ => 1 / t^2) (Set.Ioi (1 : ℝ)) := by
  have h_rpow : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) := by
    apply integrableOn_Ioi_rpow_of_lt
    · norm_num
    · exact zero_lt_one
  apply MeasureTheory.IntegrableOn.congr_fun h_rpow
  · intro t ht
    exact (one_div_sq_eq_rpow_neg_two_on_Ioi_one ht).symm
  · exact measurableSet_Ioi

theorem G11TransformedIntegrand_eq_one_on_Ioo_zero_one
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 : ℝ)) :
    G11TransformedIntegrand t = 1 := by
  unfold G11TransformedIntegrand
  have hfract : Int.fract t = t := by
    rw [Int.fract_eq_self]
    exact ⟨le_of_lt ht.1, ht.2⟩
  have ht_ne : t ≠ 0 := ne_of_gt ht.1
  rw [hfract]
  have hsq_ne : t^2 ≠ 0 := pow_ne_zero 2 ht_ne
  exact div_self hsq_ne

theorem ae_G11TransformedIntegrand_eq_one_on_Ioc_zero_one :
  G11TransformedIntegrand =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (1 : ℝ))] (fun _ : ℝ => 1) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  have hae : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), t ≠ (1 : ℝ) := by
    apply MeasureTheory.ae_iff.mpr
    have : {t : ℝ | ¬t ≠ 1} = {1} := by ext t; simp
    rw [this]
    exact MeasureTheory.measure_singleton 1
  filter_upwards [hae] with t ht_ne ht_mem
  have ht_ioo : t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) := ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht_ne⟩
  exact G11TransformedIntegrand_eq_one_on_Ioo_zero_one ht_ioo

theorem integrableOn_one_Ioc_zero_one :
  MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) (1 : ℝ)) := by
  exact MeasureTheory.integrableOn_const (ne_of_lt measure_Ioc_lt_top)

theorem integrableOn_G11TransformedIntegrand_Ioc_zero_one :
  MeasureTheory.IntegrableOn G11TransformedIntegrand (Set.Ioc (0 : ℝ) (1 : ℝ)) := by
  have hs : (fun _ : ℝ => (1 : ℝ)) =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (1 : ℝ))] G11TransformedIntegrand :=
    ae_G11TransformedIntegrand_eq_one_on_Ioc_zero_one.symm
  exact MeasureTheory.IntegrableOn.congr_fun_ae integrableOn_one_Ioc_zero_one hs

theorem measurable_G11TransformedIntegrand : Measurable G11TransformedIntegrand := by
  unfold G11TransformedIntegrand
  measurability

theorem aestronglyMeasurableOn_G11TransformedIntegrand_Ioi_one :
  MeasureTheory.AEStronglyMeasurable G11TransformedIntegrand (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
  exact measurable_G11TransformedIntegrand.aestronglyMeasurable.restrict

theorem integrableOn_G11TransformedIntegrand_Ioi_one :
  MeasureTheory.IntegrableOn G11TransformedIntegrand (Set.Ioi (1 : ℝ)) := by
  refine MeasureTheory.Integrable.mono' integrableOn_inv_sq_Ioi_one aestronglyMeasurableOn_G11TransformedIntegrand_Ioi_one ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  exact G11TransformedIntegrand_le_inv_sq_on_Ioi_one ht

theorem Ioi_zero_eq_Ioc_zero_one_union_Ioi_one :
  Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) (1 : ℝ) ∪ Set.Ioi (1 : ℝ) := by
  ext x
  simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
  constructor
  · intro hx
    by_cases h : x ≤ 1
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr (lt_of_not_ge h)
  · rintro (⟨hx, _⟩ | hx)
    · exact hx
    · linarith

theorem integrableOn_G11TransformedIntegrand_Ioi :
  MeasureTheory.IntegrableOn G11TransformedIntegrand (Set.Ioi (0 : ℝ)) := by
  rw [Ioi_zero_eq_Ioc_zero_one_union_Ioi_one]
  exact MeasureTheory.IntegrableOn.union
    integrableOn_G11TransformedIntegrand_Ioc_zero_one
    integrableOn_G11TransformedIntegrand_Ioi_one

theorem integral_iUnion_disjoint_unit_intervals_theorem
  {f : ℝ → ℝ}
  (hf : MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ))) :
  (∫ t in Set.Ioi (0 : ℝ), f t)
    =
  ∑' n : ℕ,
    ∫ t in Set.Ioc ((n : ℝ)) ((n + 1 : ℝ)), f t := by
  have hs : HasSum (fun n : ℕ => ∫ t in Set.Ioc (n : ℝ) (n + 1 : ℝ), f t) (∫ t in ⋃ n : ℕ, Set.Ioc (n : ℝ) (n + 1 : ℝ), f t) := by
    apply MeasureTheory.hasSum_integral_iUnion
    · intro _
      exact measurableSet_Ioc
    · exact pairwiseDisjoint_Ioc_nat
    · rw [← Ioi_zero_eq_iUnion_Ioc_nat]
      exact hf
  rw [Ioi_zero_eq_iUnion_Ioc_nat]
  exact hs.tsum_eq.symm

theorem integral_Ioi_eq_tsum_unit_set_integrals_theorem :
  (∫ t in Set.Ioi (0 : ℝ), G11TransformedIntegrand t)
    =
  G11SetIntegralSeries := by
  unfold G11SetIntegralSeries G11UnitSetIntegral
  exact integral_iUnion_disjoint_unit_intervals_theorem integrableOn_G11TransformedIntegrand_Ioi

def G11SymmetricTruncationSet (n : ℕ) : Set ℝ :=
  Set.Ioc (1 / (n + 2 : ℝ)) (n + 2 : ℝ)

theorem Ioi_zero_eq_iUnion_symmetric_truncations :
  Set.Ioi (0 : ℝ)
    =
  ⋃ n : ℕ, G11SymmetricTruncationSet n := by
  ext x
  simp only [Set.mem_Ioi, Set.mem_iUnion, G11SymmetricTruncationSet, Set.mem_Ioc]
  constructor
  · intro hx
    have h1 : ∃ n₁ : ℕ, x ≤ (n₁ : ℝ) := exists_nat_ge x
    rcases h1 with ⟨n₁, hn₁⟩
    have h2 : ∃ n₂ : ℕ, 1 / x < (n₂ : ℝ) := exists_nat_gt (1 / x)
    rcases h2 with ⟨n₂, hn₂⟩
    use max n₁ n₂
    constructor
    · have h_pos : (0 : ℝ) < ((max n₁ n₂ : ℕ) : ℝ) + 2 := by
        have : (0 : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      rw [div_lt_iff₀ h_pos]
      have : 1 / x < (n₂ : ℝ) := hn₂
      have h_n2_le : (n₂ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := Nat.cast_le.mpr (le_max_right n₁ n₂)
      have : 1 / x < ((max n₁ n₂ : ℕ) : ℝ) := lt_of_lt_of_le this h_n2_le
      have : 1 / x < ((max n₁ n₂ : ℕ) : ℝ) + 2 := lt_add_of_lt_of_pos this (by norm_num)
      exact (div_lt_iff₀' hx).mp this
    · have : x ≤ n₁ := hn₁
      have h_n1_le : (n₁ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := Nat.cast_le.mpr (le_max_left n₁ n₂)
      have : x ≤ ((max n₁ n₂ : ℕ) : ℝ) := le_trans this h_n1_le
      linarith
  · rintro ⟨n, hn₁, hn₂⟩
    have : (0 : ℝ) < 1 / (n + 2 : ℝ) := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      positivity
    exact lt_trans this hn₁

theorem G11TransformedTruncation_tendsto :
  Filter.Tendsto
    (fun n : ℕ => G11TransformedTruncation (n + 2 : ℝ))
    Filter.atTop
    (nhds (∫ t in Set.Ioi (0 : ℝ), G11TransformedIntegrand t)) := by
  have h_eq : (fun n : ℕ => G11TransformedTruncation (n + 2 : ℝ))
      = (fun n : ℕ => ∫ t in G11SymmetricTruncationSet n, G11TransformedIntegrand t) := by
    funext n
    rfl
  rw [h_eq]
  have h_mono : Monotone G11SymmetricTruncationSet := by
    intro i j hij x hx
    unfold G11SymmetricTruncationSet at *
    rw [Set.mem_Ioc] at *
    constructor
    · have h_pos_i : (0 : ℝ) < (i : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        linarith
      have h_pos_j : (0 : ℝ) < (j : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      have h_le : (i : ℝ) + 2 ≤ (j : ℝ) + 2 := by
        have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
        linarith
      have h_inv_le : 1 / ((j : ℝ) + 2) ≤ 1 / ((i : ℝ) + 2) := by
        apply one_div_le_one_div_of_le h_pos_i h_le
      exact lt_of_le_of_lt h_inv_le hx.1
    · have h_le : (i : ℝ) + 2 ≤ (j : ℝ) + 2 := by
        have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
        linarith
      exact le_trans hx.2 h_le
  have hsm : ∀ i, MeasurableSet (G11SymmetricTruncationSet i) := by
    intro i
    unfold G11SymmetricTruncationSet
    exact measurableSet_Ioc
  have hs : Filter.Tendsto
      (fun i => ∫ x in G11SymmetricTruncationSet i, G11TransformedIntegrand x)
      Filter.atTop
      (nhds (∫ x in ⋃ i, G11SymmetricTruncationSet i, G11TransformedIntegrand x)) := by
    apply MeasureTheory.tendsto_setIntegral_of_monotone hsm h_mono
    rw [← Ioi_zero_eq_iUnion_symmetric_truncations]
    exact integrableOn_G11TransformedIntegrand_Ioi
  rw [← Ioi_zero_eq_iUnion_symmetric_truncations] at hs
  exact hs

theorem measurable_G11OriginalIntegrand :
  Measurable G11OriginalIntegrand := by
  unfold G11OriginalIntegrand
  measurability

theorem norm_G11OriginalIntegrand_le_one
    (x : ℝ) :
    ‖G11OriginalIntegrand x‖ ≤ 1 := by
  unfold G11OriginalIntegrand
  have h1 : 0 ≤ Int.fract (1 / x) := Int.fract_nonneg _
  have h2 : Int.fract (1 / x) < 1 := Int.fract_lt_one _
  have h3 : 0 ≤ (Int.fract (1 / x)) ^ 2 := sq_nonneg _
  have h4 : (Int.fract (1 / x)) ^ 2 ≤ 1 := by
    nlinarith [h1, h2]
  rw [Real.norm_eq_abs, abs_of_nonneg h3]
  exact h4

theorem integrableOn_G11OriginalIntegrand_Ioc_zero_one :
  MeasureTheory.IntegrableOn G11OriginalIntegrand (Set.Ioc (0 : ℝ) (1 : ℝ)) := by
  apply MeasureTheory.Integrable.mono'
    (g := fun _ : ℝ => (1 : ℝ))
  · have h_meas : MeasureTheory.volume (Set.Ioc (0 : ℝ) 1) ≠ ⊤ := measure_Ioc_lt_top.ne
    exact MeasureTheory.integrableOn_const h_meas
  · exact measurable_G11OriginalIntegrand.aestronglyMeasurable.restrict
  · apply Filter.Eventually.of_forall
    intro x
    exact norm_G11OriginalIntegrand_le_one x

theorem G11OriginalIntegrand_eq_inv_sq_on_Ioi_one
    {x : ℝ} (hx : x ∈ Set.Ioi (1 : ℝ)) :
    G11OriginalIntegrand x = 1 / x^2 := by
  unfold G11OriginalIntegrand
  have hx_gt_one : 1 < x := hx
  have hx_pos : 0 < x := by linarith
  have h_inv_pos : 0 < 1 / x := one_div_pos.mpr hx_pos
  have h_inv_lt_one : 1 / x < 1 := by
    rw [div_lt_iff₀ hx_pos]
    simp only [one_mul]
    linarith
  have h_le : 0 ≤ 1 / x := le_of_lt h_inv_pos
  have hfract : Int.fract (1 / x) = 1 / x := Int.fract_eq_self.mpr ⟨h_le, h_inv_lt_one⟩
  rw [hfract]
  ring

theorem integrableOn_G11OriginalIntegrand_Ioi_one :
  MeasureTheory.IntegrableOn G11OriginalIntegrand (Set.Ioi (1 : ℝ)) := by
  apply MeasureTheory.IntegrableOn.congr_fun integrableOn_inv_sq_Ioi_one
  intro x hx
  exact (G11OriginalIntegrand_eq_inv_sq_on_Ioi_one hx).symm
  exact measurableSet_Ioi

theorem integrableOn_G11OriginalIntegrand_Ioi :
  MeasureTheory.IntegrableOn G11OriginalIntegrand (Set.Ioi (0 : ℝ)) := by
  rw [Ioi_zero_eq_Ioc_zero_one_union_Ioi_one]
  exact MeasureTheory.IntegrableOn.union
    integrableOn_G11OriginalIntegrand_Ioc_zero_one
    integrableOn_G11OriginalIntegrand_Ioi_one

theorem G11OriginalTruncation_tendsto :
  Filter.Tendsto
    (fun n : ℕ => G11OriginalTruncation (n + 2 : ℝ))
    Filter.atTop
    (nhds (∫ x in Set.Ioi (0 : ℝ), G11OriginalIntegrand x)) := by
  have h_eq : (fun n : ℕ => G11OriginalTruncation (n + 2 : ℝ))
      = (fun n : ℕ => ∫ x in G11SymmetricTruncationSet n, G11OriginalIntegrand x) := by
    funext n
    rfl
  rw [h_eq]
  have h_mono : Monotone G11SymmetricTruncationSet := by
    intro i j hij x hx
    unfold G11SymmetricTruncationSet at *
    rw [Set.mem_Ioc] at *
    constructor
    · have h_pos_i : (0 : ℝ) < (i : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        linarith
      have h_pos_j : (0 : ℝ) < (j : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      have h_le : (i : ℝ) + 2 ≤ (j : ℝ) + 2 := by
        have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
        linarith
      have h_inv_le : 1 / ((j : ℝ) + 2) ≤ 1 / ((i : ℝ) + 2) := by
        apply one_div_le_one_div_of_le h_pos_i h_le
      exact lt_of_le_of_lt h_inv_le hx.1
    · have h_le : (i : ℝ) + 2 ≤ (j : ℝ) + 2 := by
        have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
        linarith
      exact le_trans hx.2 h_le
  have hsm : ∀ i, MeasurableSet (G11SymmetricTruncationSet i) := by
    intro i
    unfold G11SymmetricTruncationSet
    exact measurableSet_Ioc
  have hs : Filter.Tendsto
      (fun i => ∫ x in G11SymmetricTruncationSet i, G11OriginalIntegrand x)
      Filter.atTop
      (nhds (∫ x in ⋃ i, G11SymmetricTruncationSet i, G11OriginalIntegrand x)) := by
    apply MeasureTheory.tendsto_setIntegral_of_monotone hsm h_mono
    rw [← Ioi_zero_eq_iUnion_symmetric_truncations]
    exact integrableOn_G11OriginalIntegrand_Ioi
  rw [← Ioi_zero_eq_iUnion_symmetric_truncations] at hs
  exact hs

theorem integral_Ioi_inv_substitution_theorem :
  (∫ x in Set.Ioi (0 : ℝ), G11OriginalIntegrand x)
    =
  (∫ t in Set.Ioi (0 : ℝ), G11TransformedIntegrand t) := by
  have h_eq_seq :
    (fun n : ℕ => G11OriginalTruncation (n + 2 : ℝ))
    =
    (fun n : ℕ => G11TransformedTruncation (n + 2 : ℝ)) := by
    funext n
    have hn : (1 : ℝ) < n + 2 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact finite_inverse_substitution_truncation hn
  have h2 : Filter.Tendsto
    (fun n : ℕ => G11OriginalTruncation (n + 2 : ℝ))
    Filter.atTop
    (nhds (∫ t in Set.Ioi (0 : ℝ), G11TransformedIntegrand t)) := by
    rw [h_eq_seq]
    exact G11TransformedTruncation_tendsto
  exact tendsto_nhds_unique G11OriginalTruncation_tendsto h2

theorem G11_change_of_variables_theorem :
  G11Integral = G11TransformedIntegral := by
  unfold G11Integral G11TransformedIntegral
  exact integral_Ioi_inv_substitution_theorem

theorem unit_set_integral_eq_intervalIntegral_theorem
    (n : ℕ) :
    G11UnitSetIntegral n =
    ∫ t in ((n : ℝ))..((n + 1 : ℝ)),
      G11TransformedIntegrand t := by
  unfold G11UnitSetIntegral
  exact (intervalIntegral.integral_of_le (by linarith : (n : ℝ) ≤ (n + 1 : ℝ))).symm

theorem G11SetIntegralSeries_eq_interval_series :
  G11SetIntegralSeries =
    ∑' n : ℕ,
      ∫ t in ((n : ℝ))..((n + 1 : ℝ)),
        G11TransformedIntegrand t := by
  unfold G11SetIntegralSeries
  apply tsum_congr
  intro n
  exact unit_set_integral_eq_intervalIntegral_theorem n

theorem integral_Ioi_eq_tsum_unit_intervals_theorem :
  (∫ t in Set.Ioi (0 : ℝ), G11TransformedIntegrand t)
    =
  ∑' n : ℕ,
    ∫ t in ((n : ℝ))..((n + 1 : ℝ)),
      G11TransformedIntegrand t := by
  rw [integral_Ioi_eq_tsum_unit_set_integrals_theorem]
  exact G11SetIntegralSeries_eq_interval_series

theorem G11_integral_to_series_theorem :
  G11TransformedIntegral = G11IntervalSeries := by
  unfold G11TransformedIntegral G11IntervalSeries G11UnitIntegral
  exact integral_Ioi_eq_tsum_unit_intervals_theorem

noncomputable def G11UnitIntegralFormula (n : ℕ) : ℝ :=
  1 + (n : ℝ) / (n + 1 : ℝ)
    - 2 * (n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))

theorem fract_eq_sub_nat_on_Ioo (n : ℕ) :
    ∀ t ∈ Set.Ioo ((n : ℝ)) ((n + 1 : ℝ)),
      Int.fract t = t - n := by
  intro t ht
  have h_floor : ⌊t⌋ = (n : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · exact le_of_lt ht.1
    · push_cast
      exact ht.2
  unfold Int.fract
  rw [h_floor]
  push_cast
  rfl

theorem G11_unit_integral_zero :
  G11UnitIntegral 0 = 1 := by
  unfold G11UnitIntegral
  simp only [Nat.cast_zero, zero_add]
  have h_ae : G11TransformedIntegrand =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)] (fun _ : ℝ => 1) :=
    ae_G11TransformedIntegrand_eq_one_on_Ioc_zero_one
  have h_int : (∫ t in (0:ℝ)..(1:ℝ), G11TransformedIntegrand t) = ∫ t in (0:ℝ)..(1:ℝ), (1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    have h_ae2 := (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp h_ae
    filter_upwards [h_ae2]
    intro x hx ht
    have h_le : (0:ℝ) ≤ 1 := by norm_num
    rw [Set.uIoc_of_le h_le] at ht
    exact hx ht
  rw [h_int]
  simp

theorem G11_unit_integral_fract_to_poly_theorem (n : ℕ) (_hn : 0 < n) :
  G11UnitIntegral n =
  ∫ t in ((n : ℝ))..((n + 1 : ℝ)),
    ((t - n) ^ 2 / t ^ 2) := by
  unfold G11UnitIntegral G11TransformedIntegrand
  apply intervalIntegral.integral_congr_ae
  have h_ae : ∀ᵐ (t : ℝ) ∂MeasureTheory.volume, t ≠ (n + 1 : ℝ) :=
    MeasureTheory.Measure.ae_ne MeasureTheory.volume (n + 1 : ℝ)
  filter_upwards [h_ae]
  intro t ht ht_in
  have h_le : (n : ℝ) ≤ (n + 1 : ℝ) := by linarith
  rw [Set.uIoc_of_le h_le] at ht_in
  have ht_Ioo : t ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ) := ⟨ht_in.1, lt_of_le_of_ne ht_in.2 ht⟩
  have h_fract := fract_eq_sub_nat_on_Ioo n t ht_Ioo
  rw [h_fract]

noncomputable def G11UnitAntiderivative (n : ℕ) (t : ℝ) : ℝ :=
  t - 2 * (n : ℝ) * Real.log t - (n : ℝ)^2 / t

theorem G11_derivative_algebra
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    1 - 2 * (n : ℝ) / t + (n : ℝ)^2 / t^2
    =
    ((t - n) ^ 2) / t ^ 2 := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  field_simp
  ring

theorem hasDerivAt_G11UnitAntiderivative_raw
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => G11UnitAntiderivative n u)
      (1 - 2 * (n : ℝ) / t + (n : ℝ)^2 / t^2) t := by
  unfold G11UnitAntiderivative
  have ht_ne : t ≠ 0 := ne_of_gt ht

  have h1 : HasDerivAt (fun u => u) 1 t := hasDerivAt_id t
  have hlog : HasDerivAt (fun u => Real.log u) t⁻¹ t := Real.hasDerivAt_log ht_ne
  have h2 : HasDerivAt (fun u => 2 * (n : ℝ) * Real.log u) (2 * (n : ℝ) * t⁻¹) t :=
    HasDerivAt.const_mul (2 * (n : ℝ)) hlog
  
  have hinv : HasDerivAt (fun u => u⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht_ne
  have h3 : HasDerivAt (fun u => (n : ℝ)^2 / u) (- ((n : ℝ)^2) / t^2) t := by
    -- n^2 / u is n^2 * u⁻¹
    have h_mul := HasDerivAt.const_mul ((n : ℝ)^2) hinv
    -- the derivative is n^2 * (-(t^2)⁻¹) = - n^2 / t^2
    have h_eq : (n : ℝ)^2 * -(t ^ 2)⁻¹ = - ((n : ℝ)^2) / t^2 := by ring
    have h_fun_eq : (fun u => (n : ℝ)^2 * u⁻¹) = (fun u => (n : ℝ)^2 / u) := by
      ext u
      exact div_eq_mul_inv ((n : ℝ)^2) u |>.symm
    rw [← h_fun_eq]
    rw [← h_eq]
    exact h_mul

  have h_sub1 := HasDerivAt.sub h1 h2
  have h_sub2 := HasDerivAt.sub h_sub1 h3

  -- The derivative we got is:
  -- 1 - 2 * n * t⁻¹ - (- n^2 / t^2)
  -- We want: 1 - 2 * n / t + n^2 / t^2
  have h_eq2 : 1 - 2 * (n : ℝ) * t⁻¹ - (- ((n : ℝ)^2) / t^2) = 1 - 2 * (n : ℝ) / t + (n : ℝ)^2 / t^2 := by
    ring
  rw [← h_eq2]
  exact h_sub2

theorem hasDerivAt_G11UnitAntiderivative
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => G11UnitAntiderivative n u)
      (((t - n) ^ 2) / t ^ 2) t := by
  have h1 := hasDerivAt_G11UnitAntiderivative_raw n ht
  have h2 := G11_derivative_algebra n ht
  rwa [← h2]

theorem unit_interval_pos
    (n : ℕ) (hn : 0 < n)
    {t : ℝ}
    (ht : t ∈ Set.Icc ((n : ℝ)) ((n + 1 : ℝ))) :
    0 < t := by
  have h1 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (n : ℝ) ≤ t := ht.1
  linarith

theorem integral_poly_over_t_sq_eq_antiderivative_diff
    (n : ℕ) (hn : 0 < n) :
    (∫ t in ((n : ℝ))..((n + 1 : ℝ)),
       ((t - n) ^ 2 / t ^ 2))
    =
    G11UnitAntiderivative n (n + 1)
      - G11UnitAntiderivative n n := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    apply hasDerivAt_G11UnitAntiderivative
    have h1 : (n : ℝ) ≤ (n + 1 : ℝ) := by linarith
    have ht2 : t ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
      rwa [Set.uIcc_of_le h1] at ht
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    linarith [ht2.1]
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply ContinuousOn.pow
      apply ContinuousOn.sub
      · exact continuousOn_id
      · exact continuousOn_const
    · apply ContinuousOn.pow
      exact continuousOn_id
    · intro x hx
      have h1 : (n : ℝ) ≤ (n + 1 : ℝ) := by linarith
      have ht2 : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := by
        rwa [Set.uIcc_of_le h1] at hx
      have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      have hxpos : 0 < x := by linarith [ht2.1]
      positivity



theorem antiderivative_endpoint_simplification
    (n : ℕ) (hn : 0 < n) :
    G11UnitAntiderivative n (n + 1)
      - G11UnitAntiderivative n n
    =
    1 + (n : ℝ) / (n + 1 : ℝ)
      - 2 * (n : ℝ) *
          Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
  unfold G11UnitAntiderivative
  have hx : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hy : (n : ℝ) ≠ 0 := by positivity
  have h3 : Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) = Real.log (n + 1) - Real.log n := by
    rw [Real.log_div hx hy]
    push_cast
    rfl
  rw [h3]
  field_simp
  ring

theorem unit_integral_rational_log_formula (n : ℕ) (hn : 0 < n) :
  (∫ t in ((n : ℝ))..((n + 1 : ℝ)),
     ((t - n) ^ 2 / t ^ 2))
  =
  1 + (n : ℝ) / (n + 1 : ℝ)
    - 2 * (n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
  rw [integral_poly_over_t_sq_eq_antiderivative_diff n hn, antiderivative_endpoint_simplification n hn]


theorem G11_unit_integral_formula_theorem (n : ℕ) (hn : 0 < n) :
  G11UnitIntegral n = G11UnitIntegralFormula n := by
  rw [G11_unit_integral_fract_to_poly_theorem n hn]
  exact unit_integral_rational_log_formula n hn



noncomputable def G11UnitFormulaPartialSum (N : ℕ) : ℝ :=
  (1 : ℝ) + ∑ n ∈ Finset.Icc 1 N, G11UnitIntegralFormula n

noncomputable def G11FiniteClosedForm (N : ℕ) : ℝ :=
  2 * (N : ℝ) + 2
    - (∑ k ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / k)
    - 2 * (N + 1 : ℝ) * Real.log (N + 1)
    + 2 * Real.log ((Nat.factorial (N + 1) : ℝ))

theorem nat_div_succ_identity (n : ℕ) :
    (n : ℝ) / (n + 1 : ℝ) = 1 - 1 / (n + 1 : ℝ) := by
  have h_ne : (n + 1 : ℝ) ≠ 0 := by positivity
  calc
    (n : ℝ) / (n + 1 : ℝ) = ((n + 1 : ℝ) - 1) / (n + 1 : ℝ) := by ring_nf
    _ = (n + 1 : ℝ) / (n + 1 : ℝ) - 1 / (n + 1 : ℝ) := sub_div _ _ _
    _ = 1 - 1 / (n + 1 : ℝ) := by rw [div_self h_ne]

theorem sum_unit_rational_part (N : ℕ) :
    1 + ∑ n ∈ Finset.Icc 1 N, (1 + (n : ℝ) / (n + 1 : ℝ)) =
    2 * (N : ℝ) + 2 - ∑ k ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / k := by
  induction N with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, zero_add, zero_add]
    have h_empty : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty (by decide)
    rw [h_empty, Finset.sum_empty, add_zero]
    have h_one : Finset.Icc 1 1 = {1} := rfl
    rw [h_one, Finset.sum_singleton]
    norm_num
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [← add_assoc, ih]
    rw [Finset.sum_Icc_succ_top (b := N + 1) (by omega)]
    rw [nat_div_succ_identity (N + 1)]
    push_cast
    ring

theorem sum_unit_log_part (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) =
    (N + 1 : ℝ) * Real.log (N + 1) - Real.log ((Nat.factorial (N + 1) : ℝ)) := by
  induction N with
  | zero =>
    have h_empty : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty (by decide)
    rw [h_empty, Finset.sum_empty]
    simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [ih]
    push_cast
    have h_log_div : Real.log ((N + 1 + 1 : ℝ) / (N + 1 : ℝ)) = Real.log (N + 1 + 1 : ℝ) - Real.log (N + 1 : ℝ) := by
      exact Real.log_div (by positivity) (by positivity)
    have h_log_fact : Real.log (Nat.factorial (N + 1 + 1) : ℝ) = Real.log (N + 1 + 1 : ℝ) + Real.log (Nat.factorial (N + 1) : ℝ) := by
      have h1 : Nat.factorial (N + 1 + 1) = (N + 1 + 1) * Nat.factorial (N + 1) := rfl
      rw [h1, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      push_cast
      rfl
    rw [h_log_div, h_log_fact]
    ring

theorem G11_partial_sum_closed_form (N : ℕ) :
    G11UnitFormulaPartialSum N = G11FiniteClosedForm N := by
  unfold G11UnitFormulaPartialSum G11FiniteClosedForm G11UnitIntegralFormula
  have h_sum : ∑ n ∈ Finset.Icc 1 N, (1 + (n : ℝ) / (n + 1 : ℝ) - 2 * (n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) =
      ∑ n ∈ Finset.Icc 1 N, (1 + (n : ℝ) / (n + 1 : ℝ)) - 2 * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) := by
    rw [Finset.sum_sub_distrib]
    have h_mul : ∑ n ∈ Finset.Icc 1 N, 2 * ((n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) =
        2 * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      rw [Finset.mul_sum]
    have h_mul_assoc : ∀ n ∈ Finset.Icc 1 N, 2 * (n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) = 2 * ((n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      intro n _
      ring
    rw [Finset.sum_congr rfl h_mul_assoc]
    rw [h_mul]
  rw [h_sum]
  have h_rat := sum_unit_rational_part N
  have h_log := sum_unit_log_part N
  linarith

noncomputable def HarmonicReal (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k

noncomputable def LogStirlingRemainder (m : ℕ) : ℝ :=
  Real.log ((Nat.factorial m : ℝ))
    - ((m : ℝ) * Real.log m - (m : ℝ)
       + (1 / 2 : ℝ) * Real.log m
       + (1 / 2 : ℝ) * Real.log (2 * Real.pi))

theorem HarmonicReal_eq_mathlib_harmonic (n : ℕ) :
  HarmonicReal n = (harmonic n : ℝ) := by
  unfold HarmonicReal harmonic
  push_cast
  have h_eq : (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k) = ∑ k ∈ Finset.Ico 1 (n + 1), (1 : ℝ) / k := by
    rw [← Finset.Ico_succ_right_eq_Icc]
    rfl
  rw [h_eq]
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro x _hx
  push_cast
  rw [one_div, add_comm]

theorem harmonic_sub_log_tendsto_eulerGamma :
  Filter.Tendsto
    (fun m : ℕ => HarmonicReal m - Real.log m)
    Filter.atTop
    (nhds EulerGamma) := by
  have h_eq : (fun m : ℕ => HarmonicReal m - Real.log m) = (fun m : ℕ => (harmonic m : ℝ) - Real.log m) := by
    ext m
    rw [HarmonicReal_eq_mathlib_harmonic]
  rw [h_eq]
  unfold EulerGamma
  exact Real.tendsto_harmonic_sub_log

theorem log_stirling_remainder_eq (m : ℕ) (hm : 0 < m) :
  LogStirlingRemainder m = Real.log (Stirling.stirlingSeq m) - (1 / 2) * Real.log Real.pi := by
  unfold LogStirlingRemainder
  have h_form := Stirling.log_stirlingSeq_formula m
  have h_exp : Real.log (Real.exp 1) = 1 := Real.log_exp 1
  have hm_real : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_real
  have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hexp_ne : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  have h_log_2n : Real.log (2 * m) = Real.log 2 + Real.log m := Real.log_mul h2_ne hm_ne
  have h_log_div : Real.log (m / Real.exp 1) = Real.log m - Real.log (Real.exp 1) := Real.log_div hm_ne hexp_ne
  have h_log_2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi := Real.log_mul h2_ne hpi_ne
  rw [h_form]
  rw [h_exp] at h_log_div
  rw [h_log_2n, h_log_div, h_log_2pi]
  ring

theorem log_stirling_remainder_tendsto_zero :
  Filter.Tendsto
    (fun m : ℕ => LogStirlingRemainder m)
    Filter.atTop
    (nhds 0) := by
  have h_eq : (fun m : ℕ => LogStirlingRemainder (m + 1)) = (fun m : ℕ => Real.log (Stirling.stirlingSeq (m + 1)) - (1 / 2) * Real.log Real.pi) := by
    ext m
    exact log_stirling_remainder_eq (m + 1) (Nat.succ_pos m)
  have h_lim1 : Filter.Tendsto (fun m : ℕ => Stirling.stirlingSeq (m + 1)) Filter.atTop (nhds (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp (Filter.tendsto_add_atTop_nat 1)
  have h_lim2 : Filter.Tendsto (fun m : ℕ => Real.log (Stirling.stirlingSeq (m + 1))) Filter.atTop (nhds (Real.log (Real.sqrt Real.pi))) :=
    Filter.Tendsto.log h_lim1 (by positivity)
  have h_log_sqrt : Real.log (Real.sqrt Real.pi) = (1 / 2) * Real.log Real.pi := by
    rw [Real.log_sqrt (by positivity)]
    ring
  rw [h_log_sqrt] at h_lim2
  have h_lim3 : Filter.Tendsto (fun m : ℕ => Real.log (Stirling.stirlingSeq (m + 1)) - (1 / 2) * Real.log Real.pi) Filter.atTop (nhds 0) := by
    have h_sub := Filter.Tendsto.sub h_lim2 (tendsto_const_nhds (x := (1 / 2) * Real.log Real.pi))
    rw [sub_self] at h_sub
    exact h_sub
  rw [← h_eq] at h_lim3
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp h_lim3

noncomputable def G11FiniteClosedFormM (m : ℕ) : ℝ :=
  2 * ((m : ℝ) - 1) + 2
    - HarmonicReal m
    - 2 * (m : ℝ) * Real.log m
    + 2 * Real.log ((Nat.factorial m : ℝ))

theorem G11FiniteClosedForm_eq_m_shift (N : ℕ) :
  G11FiniteClosedForm N = G11FiniteClosedFormM (N + 1) := by
  unfold G11FiniteClosedForm G11FiniteClosedFormM HarmonicReal
  push_cast
  ring

theorem G11FiniteClosedFormM_decomposition (m : ℕ) :
  G11FiniteClosedFormM m =
    Real.log (2 * Real.pi)
    - (HarmonicReal m - Real.log m)
    + 2 * LogStirlingRemainder m := by
  unfold G11FiniteClosedFormM LogStirlingRemainder HarmonicReal
  ring

theorem G11FiniteClosedFormM_tendsto :
    Filter.Tendsto G11FiniteClosedFormM Filter.atTop (nhds (Real.log (2 * Real.pi) - EulerGamma)) := by
  have h_eq : G11FiniteClosedFormM = fun m => Real.log (2 * Real.pi) - (HarmonicReal m - Real.log m) + 2 * LogStirlingRemainder m := by
    ext m
    exact G11FiniteClosedFormM_decomposition m
  rw [h_eq]
  have h_log2pi : Filter.Tendsto (fun _ : ℕ => Real.log (2 * Real.pi)) Filter.atTop (nhds (Real.log (2 * Real.pi))) :=
    tendsto_const_nhds
  have h_harm : Filter.Tendsto (fun m : ℕ => HarmonicReal m - Real.log m) Filter.atTop (nhds EulerGamma) :=
    harmonic_sub_log_tendsto_eulerGamma
  have h_sub := Filter.Tendsto.sub h_log2pi h_harm
  have h_stirling : Filter.Tendsto (fun m : ℕ => LogStirlingRemainder m) Filter.atTop (nhds 0) :=
    log_stirling_remainder_tendsto_zero
  have h_2_stirling : Filter.Tendsto (fun m : ℕ => 2 * LogStirlingRemainder m) Filter.atTop (nhds (2 * 0)) :=
    Filter.Tendsto.const_mul 2 h_stirling
  have h_2_stirling_0 : Filter.Tendsto (fun m : ℕ => 2 * LogStirlingRemainder m) Filter.atTop (nhds 0) := by
    simpa using h_2_stirling
  have h_add := Filter.Tendsto.add h_sub h_2_stirling_0
  simpa using h_add

theorem G11_closed_form_tendsto_log_gamma :
  Filter.Tendsto G11FiniteClosedForm Filter.atTop
    (nhds (Real.log (2 * Real.pi) - EulerGamma)) := by
  have h_eq : G11FiniteClosedForm = fun N => G11FiniteClosedFormM (N + 1) := by
    ext N
    exact G11FiniteClosedForm_eq_m_shift N
  rw [h_eq]
  have h_tendsto_succ : Filter.Tendsto (fun N : ℕ => N + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_add_atTop_nat 1
  exact Filter.Tendsto.comp G11FiniteClosedFormM_tendsto h_tendsto_succ

noncomputable def G11UnitFormulaSeq (n : ℕ) : ℝ :=
  if hn : 0 < n then G11UnitIntegralFormula n else 0

theorem G11UnitFormulaSeq_partial_sum_eq (N : ℕ) :
    1 + ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n = G11UnitFormulaPartialSum N := by
  unfold G11UnitFormulaPartialSum G11UnitFormulaSeq
  have h_range : Finset.range (N + 1) = {0} ∪ Finset.Icc 1 N := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have h_disjoint : Disjoint {0} (Finset.Icc 1 N) := by
    simp only [Finset.disjoint_singleton_left, Finset.mem_Icc, not_and, not_le]
    intro h
    omega
  rw [h_range, Finset.sum_union h_disjoint]
  have h_zero : ∑ n ∈ ({0} : Finset ℕ), (if hn : 0 < n then G11UnitIntegralFormula n else (0 : ℝ)) = 0 := by
    simp
  rw [h_zero, zero_add]
  have h_eq : ∑ n ∈ Finset.Icc 1 N, (if hn : 0 < n then G11UnitIntegralFormula n else (0 : ℝ)) = ∑ n ∈ Finset.Icc 1 N, G11UnitIntegralFormula n := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_Icc] at hx
    have hx0 : 0 < x := hx.1
    simp [hx0]
  rw [h_eq]

theorem G11UnitFormulaSeq_partial_sums_tendsto :
    Filter.Tendsto
      (fun N : ℕ => 1 + ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n)
      Filter.atTop
      (nhds (Real.log (2 * Real.pi) - EulerGamma)) := by
  have h_eq : (fun N : ℕ => 1 + ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n) = G11UnitFormulaPartialSum := by
    ext N
    exact G11UnitFormulaSeq_partial_sum_eq N
  rw [h_eq]
  have h_part_eq : G11UnitFormulaPartialSum = G11FiniteClosedForm := by
    ext N
    exact G11_partial_sum_closed_form N
  rw [h_part_eq]
  exact G11_closed_form_tendsto_log_gamma

theorem hasSum_G11UnitFormulaSeq_from_tendsto :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n)
      Filter.atTop
      (nhds ((Real.log (2 * Real.pi) - EulerGamma) - 1)) := by
  have h_sub : Filter.Tendsto (fun N : ℕ => (1 + ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n) - 1) Filter.atTop (nhds ((Real.log (2 * Real.pi) - EulerGamma) - 1)) :=
    Filter.Tendsto.sub G11UnitFormulaSeq_partial_sums_tendsto tendsto_const_nhds
  have h_eq : (fun N : ℕ => (1 + ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n) - 1) = fun N => ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n := by
    ext N
    ring
  rw [h_eq] at h_sub
  exact h_sub

theorem G11UnitIntegral_nonneg (n : ℕ) : 0 ≤ G11UnitIntegral n := by
  unfold G11UnitIntegral
  apply intervalIntegral.integral_nonneg_of_forall
  · exact_mod_cast Nat.le_succ n
  · intro t
    apply div_nonneg
    · exact sq_nonneg _
    · exact sq_nonneg _

theorem G11UnitFormulaSeq_nonneg (n : ℕ) : 0 ≤ G11UnitFormulaSeq n := by
  unfold G11UnitFormulaSeq
  split_ifs with hn
  · have hformula := G11_unit_integral_formula_theorem n hn
    rw [← hformula]
    exact G11UnitIntegral_nonneg n
  · rfl

theorem hasSum_G11UnitFormulaSeq :
    HasSum G11UnitFormulaSeq ((Real.log (2 * Real.pi) - EulerGamma) - 1) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg G11UnitFormulaSeq_nonneg ((Real.log (2 * Real.pi) - EulerGamma) - 1)).mpr
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp hasSum_G11UnitFormulaSeq_from_tendsto

theorem tsum_unit_formula_eq_limit_closed_form :
  (1 : ℝ) + (∑' n : ℕ, if hn : 0 < n then G11UnitIntegralFormula n else (0 : ℝ))
    =
    Real.log (2 * Real.pi) - EulerGamma := by
  have h_eq_seq : (∑' n : ℕ, if hn : 0 < n then G11UnitIntegralFormula n else (0 : ℝ)) = ∑' n : ℕ, G11UnitFormulaSeq n := by
    rfl
  rw [h_eq_seq]
  have h_sum := hasSum_G11UnitFormulaSeq.tsum_eq
  linarith



theorem G11_unit_formula_series_eval_theorem :
  (1 : ℝ) + (∑' n : ℕ, if hn : 0 < n then G11UnitIntegralFormula n else (0 : ℝ))
    =
    Real.log (2 * Real.pi) - EulerGamma := by
  exact tsum_unit_formula_eq_limit_closed_form

theorem G11_series_from_unit_formula_proof :
  G11IntervalSeries =
    (1 : ℝ) + ∑' n : ℕ,
      if hn : 0 < n then G11UnitIntegralFormula n else (0 : ℝ) := by
  unfold G11IntervalSeries
  have h_eq : (fun n : ℕ => G11UnitIntegral n) = fun n =>
      (if n = 0 then (1 : ℝ) else 0) + G11UnitFormulaSeq n := by
    ext n
    by_cases h : n = 0
    · subst h
      rw [if_pos rfl, G11_unit_integral_zero]
      unfold G11UnitFormulaSeq
      simp
    · rw [if_neg h]
      have hn : 0 < n := Nat.pos_of_ne_zero h
      have h1 := G11_unit_integral_formula_theorem n hn
      unfold G11UnitFormulaSeq
      rw [dif_pos hn, zero_add]
      exact h1
  rw [h_eq]
  have h_sum1 : HasSum (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 1 :=
    hasSum_ite_eq 0 (1 : ℝ)
  have h_sum2 : HasSum G11UnitFormulaSeq (∑' n : ℕ, G11UnitFormulaSeq n) :=
    hasSum_G11UnitFormulaSeq.summable.hasSum
  have h_sum_add := HasSum.add h_sum1 h_sum2
  have h_tsum_add := h_sum_add.tsum_eq
  rw [h_tsum_add]
  have h_eq2 : (∑' n : ℕ, G11UnitFormulaSeq n) = ∑' n : ℕ, if hn : 0 < n then G11UnitIntegralFormula n else (0 : ℝ) := rfl
  rw [h_eq2]

theorem G11_series_eval_theorem :
  G11IntervalSeries = Real.log (2 * Real.pi) - EulerGamma := by
  rw [G11_series_from_unit_formula_proof, G11_unit_formula_series_eval_theorem]

theorem G11_integral_eval_theorem :
  G11Integral = Real.log (2 * Real.pi) - EulerGamma := by
  rw [
    G11_change_of_variables_theorem,
    G11_integral_to_series_theorem,
    G11_series_eval_theorem
  ]

end RH.Criteria.NymanBeurling.VasyuninGram
