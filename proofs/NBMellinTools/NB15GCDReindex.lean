/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15PreFEAssembly

/-!
# NB15 exploration: exact gcd reindexing of the certified Gram form

This module reindexes the complete one-based NB8 Gram double sum by

`h = g*a`, `k = g*q`, `g = gcd(h,k)`, `Coprime a q`.

It proves the exact `g⁻¹` homogeneity of the Gram integral, replaces the
primitive Gram entry by the unconditional NB11 Vasyunin formula, and splits
the result into the primitive interior (`a,q >= 2`) and its endpoint
complement.  No Estermann special value or asymptotic estimate is used.
-/

open MeasureTheory Set
open scoped BigOperators

namespace NBMellinTools.NB15

open NBMellinTools
open NBMellinTools.NB8
open NBMellinTools.NB9
open NBMellinTools.NB10
open NBMellinTools.NB11
open NBMellinTools.NB12
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## One-based certified Gram form -/

/-- The certified logarithmic-taper Gram form in one-based notation. -/
noncomputable def oneBasedGramForm (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    h15NaturalLogTaperCoeff N h * h15NaturalLogTaperCoeff N k *
      baezDuarteGramEntry h k

private theorem sum_Icc_one_eq_sum_fin
    {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ i : Fin N, f (i.val + 1) := by
  classical
  apply Finset.sum_bij (fun n hn => ⟨n - 1, by
    simp only [Finset.mem_Icc] at hn
    omega⟩)
  · intro n hn
    simp
  · intro a ha b hb hab
    simp only [Fin.mk.injEq] at hab
    simp only [Finset.mem_Icc] at ha hb
    omega
  · intro i hi
    refine ⟨i.val + 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · apply Fin.ext
      simp
  · intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [Nat.sub_add_cancel hn1]

/-- The one-based form is exactly the NB9 Gram term for the NB8 coefficient
vector. -/
theorem oneBasedGramForm_eq_bdGramTerm (n : ℕ) :
    oneBasedGramForm (logTaperLength n) =
      bdGramTerm (logTaperLength n) (logTaperCoeffs n) := by
  classical
  unfold oneBasedGramForm bdGramTerm
  simp_rw [sum_Icc_one_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [h15NaturalLogTaperCoeff_eq_logTaperCoeffs n j,
    h15NaturalLogTaperCoeff_eq_logTaperCoeffs n k,
    ← bdGram_eq_classicalGramEntry]

/-! ## Exact Gram homogeneity -/

private noncomputable def positiveGramIntegrand
    (h k : ℕ) (x : ℝ) : ℝ :=
  Int.fract (1 / ((h : ℝ) * x)) * Int.fract (1 / ((k : ℝ) * x))

private theorem positiveGramIntegrand_scale
    (g a q : ℕ) (hg : 0 < g) (ha : 0 < a) (hq : 0 < q) (x : ℝ) :
    positiveGramIntegrand (g * a) (g * q) x =
      positiveGramIntegrand a q ((g : ℝ) * x) := by
  by_cases hx : x = 0
  · subst x
    simp [positiveGramIntegrand]
  unfold positiveGramIntegrand
  congr 2 <;>
    field_simp [Nat.cast_ne_zero.mpr hg.ne', Nat.cast_ne_zero.mpr ha.ne',
      Nat.cast_ne_zero.mpr hq.ne', hx] <;>
    push_cast <;> ring

/-- Exact homogeneity of the positive-denominator Gram kernel. -/
theorem baezDuarteGramEntry_scale
    (g a q : ℕ) (hg : 0 < g) (ha : 0 < a) (hq : 0 < q) :
    baezDuarteGramEntry (g * a) (g * q) =
      (g : ℝ)⁻¹ * baezDuarteGramEntry a q := by
  unfold baezDuarteGramEntry
  change (∫ x in Ioi (0 : ℝ), positiveGramIntegrand (g * a) (g * q) x) =
    (g : ℝ)⁻¹ * ∫ x in Ioi (0 : ℝ), positiveGramIntegrand a q x
  calc
    _ = ∫ x in Ioi (0 : ℝ),
        positiveGramIntegrand a q ((g : ℝ) * x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact positiveGramIntegrand_scale g a q hg ha hq x
    _ = (g : ℝ)⁻¹ •
        ∫ x in Ioi ((g : ℝ) * 0), positiveGramIntegrand a q x :=
      MeasureTheory.integral_comp_mul_left_Ioi (positiveGramIntegrand a q) 0
        (by exact_mod_cast hg : (0 : ℝ) < (g : ℝ))
    _ = _ := by simp [smul_eq_mul]

/-! ## Gcd slices and coprime reindexing -/

noncomputable def oneBasedGramGcdSlice (N g : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    if Nat.gcd h k = g then
      h15NaturalLogTaperCoeff N h * h15NaturalLogTaperCoeff N k *
        baezDuarteGramEntry h k
    else 0

noncomputable def oneBasedGramCoprimeScaledSlice (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ q ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a q then
      h15NaturalLogTaperCoeff N (g * a) *
        h15NaturalLogTaperCoeff N (g * q) *
        baezDuarteGramEntry (g * a) (g * q)
    else 0

noncomputable def oneBasedGramCoprimeRatioSlice (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ q ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a q then
      h15NaturalLogTaperCoeff N (g * a) *
        h15NaturalLogTaperCoeff N (g * q) *
        (g : ℝ)⁻¹ * baezDuarteGramEntry a q
    else 0

/-- The full positive square is partitioned by its positive gcd. -/
theorem oneBasedGramForm_eq_sum_gcdSlices (N : ℕ) :
    oneBasedGramForm N =
      ∑ g ∈ Finset.Icc 1 N, oneBasedGramGcdSlice N g := by
  classical
  symm
  unfold oneBasedGramForm oneBasedGramGcdSlice
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rcases Finset.mem_Icc.mp hh with ⟨h1, hN⟩
  have hhpos : 0 < h := lt_of_lt_of_le Nat.zero_lt_one h1
  have hgcd_mem : Nat.gcd h k ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left k hhpos,
      (Nat.gcd_le_left k hhpos).trans hN⟩
  simp only [Finset.sum_ite_eq, if_pos hgcd_mem]

/-- Reindex one positive gcd slice by its unique coprime quotient pair. -/
theorem oneBasedGramGcdSlice_eq_coprimeScaled
    (N g : ℕ) (hg : 0 < g) :
    oneBasedGramGcdSlice N g = oneBasedGramCoprimeScaledSlice N g := by
  classical
  let S := Finset.Icc 1 N
  let T := Finset.Icc 1 (N / g)
  let F : ℕ × ℕ → ℝ := fun p =>
    h15NaturalLogTaperCoeff N p.1 * h15NaturalLogTaperCoeff N p.2 *
      baezDuarteGramEntry p.1 p.2
  let scaledF : ℕ × ℕ → ℝ := fun p =>
    h15NaturalLogTaperCoeff N (g * p.1) *
      h15NaturalLogTaperCoeff N (g * p.2) *
      baezDuarteGramEntry (g * p.1) (g * p.2)
  calc
    oneBasedGramGcdSlice N g =
        ∑ p ∈ (S ×ˢ S).filter (fun p => Nat.gcd p.1 p.2 = g), F p := by
      unfold oneBasedGramGcdSlice
      dsimp [S, F]
      rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ p ∈ (T ×ˢ T).filter (fun p => Nat.Coprime p.1 p.2),
          scaledF p := by
      symm
      apply Finset.sum_bij (fun p _ => (g * p.1, g * p.2))
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpbox, hcop⟩
        rcases Finset.mem_product.mp hpbox with ⟨hpa, hpq⟩
        rcases Finset.mem_Icc.mp hpa with ⟨ha1, haN⟩
        rcases Finset.mem_Icc.mp hpq with ⟨hq1, hqN⟩
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_product.mpr
          constructor
          · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
                (Nat.mul_ne_zero hg.ne' (Nat.ne_of_gt
                  (lt_of_lt_of_le Nat.zero_lt_one ha1))),
              by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hg).mp haN⟩
          · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
                (Nat.mul_ne_zero hg.ne' (Nat.ne_of_gt
                  (lt_of_lt_of_le Nat.zero_lt_one hq1))),
              by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hg).mp hqN⟩
        · rw [Nat.gcd_mul_left, hcop.gcd_eq_one, Nat.mul_one]
      · intro p _ q _ hpq
        apply Prod.ext
        · exact Nat.mul_left_cancel hg (congrArg Prod.fst hpq)
        · exact Nat.mul_left_cancel hg (congrArg Prod.snd hpq)
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpbox, hpgcd⟩
        rcases Finset.mem_product.mp hpbox with ⟨hph, hpk⟩
        rcases Finset.mem_Icc.mp hph with ⟨hh1, hhN⟩
        rcases Finset.mem_Icc.mp hpk with ⟨hk1, hkN⟩
        have hhpos : 0 < p.1 := lt_of_lt_of_le Nat.zero_lt_one hh1
        have hkpos : 0 < p.2 := lt_of_lt_of_le Nat.zero_lt_one hk1
        have hdvdh : g ∣ p.1 := by
          rw [← hpgcd]
          exact Nat.gcd_dvd_left _ _
        have hdvdk : g ∣ p.2 := by
          rw [← hpgcd]
          exact Nat.gcd_dvd_right _ _
        have hg_le_h : g ≤ p.1 := by
          rw [← hpgcd]
          exact Nat.gcd_le_left _ hhpos
        have hg_le_k : g ≤ p.2 := by
          rw [← hpgcd]
          exact Nat.gcd_le_right _ hkpos
        have hreconh : g * (p.1 / g) = p.1 := by
          rw [Nat.mul_comm]
          exact Nat.div_mul_cancel hdvdh
        have hreconk : g * (p.2 / g) = p.2 := by
          rw [Nat.mul_comm]
          exact Nat.div_mul_cancel hdvdk
        refine ⟨(p.1 / g, p.2 / g), ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_product.mpr
            constructor
            · exact Finset.mem_Icc.mpr
                ⟨Nat.div_pos hg_le_h hg, Nat.div_le_div_right hhN⟩
            · exact Finset.mem_Icc.mpr
                ⟨Nat.div_pos hg_le_k hg, Nat.div_le_div_right hkN⟩
          · apply Nat.coprime_iff_gcd_eq_one.mpr
            apply Nat.mul_left_cancel hg
            rw [← Nat.gcd_mul_left, hreconh, hreconk, hpgcd, Nat.mul_one]
        · apply Prod.ext
          · exact hreconh
          · exact hreconk
      · intro p _
        rfl
    _ = oneBasedGramCoprimeScaledSlice N g := by
      unfold oneBasedGramCoprimeScaledSlice
      dsimp [T, scaledF]
      rw [Finset.sum_filter, Finset.sum_product]

/-- Insert Gram homogeneity after the gcd reindexing. -/
theorem oneBasedGramCoprimeScaledSlice_eq_ratioSlice
    (N g : ℕ) (hg : 0 < g) :
    oneBasedGramCoprimeScaledSlice N g =
      oneBasedGramCoprimeRatioSlice N g := by
  classical
  unfold oneBasedGramCoprimeScaledSlice oneBasedGramCoprimeRatioSlice
  apply Finset.sum_congr rfl
  intro a ha
  have ha_pos : 0 < a :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1
  apply Finset.sum_congr rfl
  intro q hq
  have hq_pos : 0 < q :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1
  split_ifs with hcop
  · rw [baezDuarteGramEntry_scale g a q hg ha_pos hq_pos]
    ring
  · rfl

/-- Exact gcd-ratio formula for the certified one-based Gram form. -/
theorem oneBasedGramForm_eq_sum_ratioSlices (N : ℕ) :
    oneBasedGramForm N =
      ∑ g ∈ Finset.Icc 1 N, oneBasedGramCoprimeRatioSlice N g := by
  rw [oneBasedGramForm_eq_sum_gcdSlices]
  apply Finset.sum_congr rfl
  intro g hg
  have hgpos : 0 < g :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hg).1
  exact (oneBasedGramGcdSlice_eq_coprimeScaled N g hgpos).trans
    (oneBasedGramCoprimeScaledSlice_eq_ratioSlice N g hgpos)

/-! ## Primitive Vasyunin realization and endpoint split -/

/-- Unconditional one-based Vasyunin evaluation, derived from NB11. -/
theorem baezDuarteGramEntry_eq_vasyuninBEntryFormula
    (a q : ℕ) (ha : 0 < a) (hq : 0 < q) :
    baezDuarteGramEntry a q = vasyuninBEntryFormula a q := by
  have ha1 : 1 ≤ a := ha
  have hq1 : 1 ≤ q := hq
  calc
    baezDuarteGramEntry a q = bdGram (a - 1) (q - 1) := by
      simpa [Nat.sub_add_cancel ha1, Nat.sub_add_cancel hq1] using
        (bdGram_eq_classicalGramEntry (a - 1) (q - 1)).symm
    _ = vasyuninGramFormula (a - 1) (q - 1) :=
      bdGram_eq_vasyuninGramFormula (a - 1) (q - 1)
    _ = vasyuninBEntryFormula ((a - 1) + 1) ((q - 1) + 1) :=
      (classicalFormula_eq_activeFormula (a - 1) (q - 1)).symm
    _ = vasyuninBEntryFormula a q := by
      rw [Nat.sub_add_cancel ha1, Nat.sub_add_cancel hq1]

noncomputable def oneBasedVasyuninCoprimeRatioSlice (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ q ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a q then
      h15NaturalLogTaperCoeff N (g * a) *
        h15NaturalLogTaperCoeff N (g * q) *
        (g : ℝ)⁻¹ * vasyuninBEntryFormula a q
    else 0

theorem oneBasedGramCoprimeRatioSlice_eq_vasyunin
    (N g : ℕ) :
    oneBasedGramCoprimeRatioSlice N g =
      oneBasedVasyuninCoprimeRatioSlice N g := by
  classical
  unfold oneBasedGramCoprimeRatioSlice oneBasedVasyuninCoprimeRatioSlice
  apply Finset.sum_congr rfl
  intro a ha
  have ha_pos : 0 < a :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1
  apply Finset.sum_congr rfl
  intro q hq
  have hq_pos : 0 < q :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1
  split_ifs with hcop
  · rw [baezDuarteGramEntry_eq_vasyuninBEntryFormula a q ha_pos hq_pos]
  · rfl

noncomputable def oneBasedVasyuninInteriorSlice (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ q ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a q ∧ 2 ≤ a ∧ 2 ≤ q then
      h15NaturalLogTaperCoeff N (g * a) *
        h15NaturalLogTaperCoeff N (g * q) *
        (g : ℝ)⁻¹ * vasyuninBEntryFormula a q
    else 0

noncomputable def oneBasedVasyuninEndpointSlice (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ q ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a q ∧ ¬ (2 ≤ a ∧ 2 ≤ q) then
      h15NaturalLogTaperCoeff N (g * a) *
        h15NaturalLogTaperCoeff N (g * q) *
        (g : ℝ)⁻¹ * vasyuninBEntryFormula a q
    else 0

theorem oneBasedVasyuninCoprimeRatioSlice_eq_interior_add_endpoint
    (N g : ℕ) :
    oneBasedVasyuninCoprimeRatioSlice N g =
      oneBasedVasyuninInteriorSlice N g +
        oneBasedVasyuninEndpointSlice N g := by
  classical
  unfold oneBasedVasyuninCoprimeRatioSlice oneBasedVasyuninInteriorSlice
    oneBasedVasyuninEndpointSlice
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hcop : Nat.Coprime a q
  · by_cases hint : 2 ≤ a ∧ 2 ≤ q <;> simp [hint]
  · simp [hcop]

/-- Complete gcd-reindexed primitive Vasyunin Gram form. -/
noncomputable def oneBasedVasyuninInterior (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N, oneBasedVasyuninInteriorSlice N g

noncomputable def oneBasedVasyuninEndpoint (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N, oneBasedVasyuninEndpointSlice N g

/-- Exact certified energy after gcd reindexing and endpoint retention. -/
theorem logTaperL2Error_eq_gcdVasyuninInterior_add_endpoint
    (n : ℕ) :
    logTaperL2Error n =
      preFECorrection n +
        oneBasedVasyuninInterior (logTaperLength n) +
        oneBasedVasyuninEndpoint (logTaperLength n) := by
  rw [logTaperL2Error_eq_quadraticForm,
    bdQuadraticForm_eq_correction_add_gram]
  unfold preFECorrection
  rw [← oneBasedGramForm_eq_bdGramTerm]
  rw [oneBasedGramForm_eq_sum_ratioSlices]
  simp_rw [oneBasedGramCoprimeRatioSlice_eq_vasyunin,
    oneBasedVasyuninCoprimeRatioSlice_eq_interior_add_endpoint]
  unfold oneBasedVasyuninInterior oneBasedVasyuninEndpoint
  rw [Finset.sum_add_distrib]
  ring

end NBMellinTools.NB15
