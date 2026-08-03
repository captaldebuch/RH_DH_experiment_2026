import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaper
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninBridge

/-!
# GCD-ratio decomposition of the BCF logarithmic-taper energy

This file is the finite algebraic part of WP2 in the integrated-cancellation
programme.  It rewrites the exact BCF Gram quadratic form by the common gcd
`g` and coprime pair `(a, b)`.  The logarithmic Möbius weights are kept
unchanged throughout; no limiting estimate or contour argument occurs here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperGcd

open scoped BigOperators
open Set
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The BCF quadratic Gram form, indexed by the natural one-based basis
indices rather than `Fin N`. -/
noncomputable def gramQuadraticForm (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    dirichletCoeff N h * dirichletCoeff N k * baezDuarteGramEntry h k

/-- The linear BCF Gram correction, in one-based notation. -/
noncomputable def gramLinearCorrection (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    dirichletCoeff N k * RH.Certificates.innerProductChiRho (k - 1)

/-- The portion of the BCF quadratic form with common gcd exactly `g`. -/
noncomputable def gramGcdSlice (N g : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    if Nat.gcd h k = g then
      dirichletCoeff N h * dirichletCoeff N k * baezDuarteGramEntry h k
    else 0

/-- The `g`-scaled, coprime-pair parametrisation of one BCF gcd slice. -/
noncomputable def gramCoprimeScaledSlice (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ b ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a b then
      dirichletCoeff N (g * a) * dirichletCoeff N (g * b) *
        baezDuarteGramEntry (g * a) (g * b)
    else 0

/-- The actual reciprocal-ratio kernel after the common gcd is factored out.
The factor `g⁻¹` is the Jacobian from the exact scaling of the Gram integral. -/
noncomputable def gramCoprimeRatioSlice (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ b ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a b then
      dirichletCoeff N (g * a) * dirichletCoeff N (g * b) *
        (g : ℝ)⁻¹ * baezDuarteGramEntry a b
    else 0

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

private theorem gram_integrand_scale
    (g a b : ℕ) (hg : 0 < g) (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    genIntegrand (g * a) (g * b) x = genIntegrand a b ((g : ℝ) * x) := by
  by_cases hx : x = 0
  · subst x
    simp [genIntegrand]
  unfold genIntegrand
  congr 2 <;> field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hg),
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha),
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb), hx] <;> push_cast <;> ring

/-- Exact homogeneity of the Báez--Duarte Gram kernel. -/
theorem baezDuarteGramEntry_scale
    (g a b : ℕ) (hg : 0 < g) (ha : 0 < a) (hb : 0 < b) :
    baezDuarteGramEntry (g * a) (g * b) =
      (g : ℝ)⁻¹ * baezDuarteGramEntry a b := by
  rw [baezDuarteGramEntry_eq_genIntegrand, baezDuarteGramEntry_eq_genIntegrand]
  calc
    _ = ∫ x in Ioi (0 : ℝ), genIntegrand a b ((g : ℝ) * x) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact gram_integrand_scale g a b hg ha hb x
    _ = (g : ℝ)⁻¹ • ∫ x in Ioi ((g : ℝ) * 0), genIntegrand a b x :=
      MeasureTheory.integral_comp_mul_left_Ioi (genIntegrand a b) 0
        (by exact_mod_cast hg : (0 : ℝ) < (g : ℝ))
    _ = _ := by simp [smul_eq_mul]

/-- The finite BCF energy in one-based Gram notation. -/
theorem energy_eq_gramQuadraticForm_add_linearCorrection (N : ℕ) :
    energy N = gramQuadraticForm N + 2 * gramLinearCorrection N + 1 := by
  rw [energy_eq_finite_gram]
  change
    (∑ h : Fin N, ∑ k : Fin N,
        (-dirichletCoeff N (h.val + 1)) * (-dirichletCoeff N (k.val + 1)) *
          baezDuarteGramEntry (h.val + 1) (k.val + 1)) -
        2 * ∑ k : Fin N,
          (-dirichletCoeff N (k.val + 1)) *
            RH.Certificates.innerProductChiRho k.val + 1 = _
  unfold gramQuadraticForm gramLinearCorrection
  simp_rw [sum_Icc_one_eq_sum_fin]
  simp only [Nat.add_sub_cancel]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

/-- Partition the BCF quadratic Gram form into its positive gcd slices. -/
theorem gramQuadraticForm_eq_sum_gcdSlices (N : ℕ) :
    gramQuadraticForm N = ∑ g ∈ Finset.Icc 1 N, gramGcdSlice N g := by
  classical
  symm
  unfold gramQuadraticForm gramGcdSlice
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

/-- Reindex a positive BCF gcd slice by coprime pairs. -/
theorem gramGcdSlice_eq_coprimeScaled (N g : ℕ) (hg : 0 < g) :
    gramGcdSlice N g = gramCoprimeScaledSlice N g := by
  classical
  let S := Finset.Icc 1 N
  let T := Finset.Icc 1 (N / g)
  let F : ℕ × ℕ → ℝ := fun p =>
    dirichletCoeff N p.1 * dirichletCoeff N p.2 *
      baezDuarteGramEntry p.1 p.2
  let scaledF : ℕ × ℕ → ℝ := fun p =>
    dirichletCoeff N (g * p.1) * dirichletCoeff N (g * p.2) *
      baezDuarteGramEntry (g * p.1) (g * p.2)
  calc
    gramGcdSlice N g =
        ∑ p ∈ (S ×ˢ S).filter (fun p => Nat.gcd p.1 p.2 = g), F p := by
      unfold gramGcdSlice
      dsimp [S, F]
      rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ p ∈ (T ×ˢ T).filter (fun p => Nat.Coprime p.1 p.2), scaledF p := by
      symm
      apply Finset.sum_bij (fun p _ => (g * p.1, g * p.2))
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpbox, hcop⟩
        rcases Finset.mem_product.mp hpbox with ⟨hpa, hpb⟩
        rcases Finset.mem_Icc.mp hpa with ⟨ha1, haN⟩
        rcases Finset.mem_Icc.mp hpb with ⟨hb1, hbN⟩
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_product.mpr
          constructor
          · apply Finset.mem_Icc.mpr
            constructor
            · exact Nat.one_le_iff_ne_zero.mpr
                (Nat.mul_ne_zero (Nat.ne_of_gt hg)
                  (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one ha1)))
            · have ha_mul := (Nat.le_div_iff_mul_le hg).mp haN
              simpa [Nat.mul_comm] using ha_mul
          · apply Finset.mem_Icc.mpr
            constructor
            · exact Nat.one_le_iff_ne_zero.mpr
                (Nat.mul_ne_zero (Nat.ne_of_gt hg)
                  (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hb1)))
            · have hb_mul := (Nat.le_div_iff_mul_le hg).mp hbN
              simpa [Nat.mul_comm] using hb_mul
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
    _ = gramCoprimeScaledSlice N g := by
      unfold gramCoprimeScaledSlice
      dsimp [T, scaledF]
      rw [Finset.sum_filter, Finset.sum_product]

/-- Insert the Gram scaling law into a coprime BCF gcd slice. -/
theorem gramCoprimeScaledSlice_eq_ratioSlice (N g : ℕ) (hg : 0 < g) :
    gramCoprimeScaledSlice N g = gramCoprimeRatioSlice N g := by
  classical
  unfold gramCoprimeScaledSlice gramCoprimeRatioSlice
  apply Finset.sum_congr rfl
  intro a ha
  have ha_pos : 0 < a := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1
  apply Finset.sum_congr rfl
  intro b hb
  have hb_pos : 0 < b := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb).1
  split_ifs with hcop
  · rw [baezDuarteGramEntry_scale g a b hg ha_pos hb_pos]
    ring
  · rfl

/-- WP2: the exact GCD-ratio decomposition of the finite BCF energy. -/
theorem energy_eq_gcdRatioFormula (N : ℕ) :
    energy N =
      (∑ g ∈ Finset.Icc 1 N, gramCoprimeRatioSlice N g) +
        2 * gramLinearCorrection N + 1 := by
  rw [energy_eq_gramQuadraticForm_add_linearCorrection,
    gramQuadraticForm_eq_sum_gcdSlices]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  exact (gramGcdSlice_eq_coprimeScaled N g
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hg).1)).trans
    (gramCoprimeScaledSlice_eq_ratioSlice N g
      (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hg).1))

end RH.Criteria.NymanBeurling.BCFLogTaperGcd
