/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import RiemannHypothesis.HardySpace.BlaschkeZeros

/-!
# The Hardy space `H²` of the unit disc and the Blaschke condition

We define membership in the Hardy space of the unit disc by

  `f` is analytic on the disc and `sup_{r<1} (1/2π)∫₀^{2π} ‖f (r e^{iθ})‖² dθ < ∞`,

expressed with `Real.circleAverage`.

The main theorem of this file is the classical **Blaschke condition**: the zeros of a nonzero
Hardy space function, listed with multiplicity, satisfy `∑ (1 - ‖z_n‖) < ∞`.  The proof runs
through Jensen's formula (`MeromorphicOn.circleAverage_log_norm`) together with the elementary
bound `log t ≤ (t² + 1)/2`, valid for every `t ≥ 0` (including `t = 0`, where Lean's `log 0 = 0`).
-/

noncomputable section

open Filter Topology Metric Set Complex Blaschke MeromorphicOn

namespace Hardy


def MemHardyDisc (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f disc ∧
    ∃ M : ℝ, ∀ r : ℝ, 0 ≤ r → r < 1 → Real.circleAverage (fun z => ‖f z‖ ^ 2) 0 r ≤ M

/-- The index type enumerating the zeros of `f` in the disc, with multiplicity. -/
abbrev zeroIndex (f : ℂ → ℂ) : Type := Σ z : disc, Fin (analyticOrderNatAt f (z : ℂ))

/-- The family of zeros of `f`, each repeated according to its multiplicity. -/
def zeroFamily (f : ℂ → ℂ) : zeroIndex f → ℂ := fun p => (p.1 : ℂ)

/-- The number of members of the zero family equal to a given point is the order of vanishing
of `f` there. -/
lemma card_fiber_zeroFamily (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ disc) :
    Nat.card {i // zeroFamily f i = z} = analyticOrderNatAt f z := by
  have e : {i : zeroIndex f // zeroFamily f i = z} ≃ Fin (analyticOrderNatAt f z) := by
    refine (Equiv.ofBijective (fun k : Fin (analyticOrderNatAt f z) =>
      (⟨⟨⟨z, hz⟩, k⟩, rfl⟩ : {i : zeroIndex f // zeroFamily f i = z})) ?_).symm
    constructor
    · intro k k' h
      have h1 : (⟨⟨z, hz⟩, k⟩ : Σ w : disc, Fin (analyticOrderNatAt f (w : ℂ)))
          = ⟨⟨z, hz⟩, k'⟩ := congrArg Subtype.val h
      injection h1
    · rintro ⟨⟨⟨w, hw⟩, k⟩, hk⟩
      simp only [zeroFamily] at hk
      subst hk
      exact ⟨k, rfl⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]


lemma log_le_half_sq_add_one {t : ℝ} (ht : 0 ≤ t) : Real.log t ≤ (t ^ 2 + 1) / 2 := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h]; simp
  · have h1 := Real.log_le_sub_one_of_pos h
    nlinarith [sq_nonneg (t - 1)]

lemma sphere_subset_disc {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : sphere (0 : ℂ) |r| ⊆ disc := by
  intro x hx
  rw [mem_sphere_iff_norm, sub_zero] at hx
  rw [mem_disc_iff, hx, abs_of_nonneg hr0]
  exact hr1

lemma circleAverage_log_norm_le (f : ℂ → ℂ) (hf : MemHardyDisc f) {M : ℝ}
    (hM : ∀ r : ℝ, 0 ≤ r → r < 1 → Real.circleAverage (fun z => ‖f z‖ ^ 2) 0 r ≤ M)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun z => Real.log ‖f z‖) 0 r ≤ (M + 1) / 2 := by
  have habs : |r| = r := abs_of_nonneg hr0
  have hsub : sphere (0 : ℂ) r ⊆ disc := by
    have := sphere_subset_disc hr0 hr1
    rwa [habs] at this
  have hint1 : CircleIntegrable (fun z => Real.log ‖f z‖) 0 r :=
    circleIntegrable_log_norm_meromorphicOn
      ((hf.1.mono (by rw [habs]; exact hsub)).meromorphicOn)
  have hintsq : CircleIntegrable (fun z => ‖f z‖ ^ 2) 0 r :=
    ContinuousOn.circleIntegrable hr0
      (fun x hx => (((hf.1 x (hsub hx)).continuousAt.norm).pow 2).continuousWithinAt)
  have hint2 : CircleIntegrable (fun z => (‖f z‖ ^ 2 + 1) / 2) 0 r :=
    ContinuousOn.circleIntegrable hr0
      (fun x hx => ((((hf.1 x (hsub hx)).continuousAt.norm).pow 2).add
        continuousAt_const).div_const 2 |>.continuousWithinAt)
  have hmono := Real.circleAverage_mono hint1 hint2
    (fun x _ => log_le_half_sq_add_one (by positivity))
  have hconst : CircleIntegrable (fun _ : ℂ => (1 : ℝ)) 0 r :=
    ContinuousOn.circleIntegrable hr0 continuousOn_const
  have hcomp : Real.circleAverage (fun z => (‖f z‖ ^ 2 + 1) / 2) 0 r
      = (Real.circleAverage (fun z => ‖f z‖ ^ 2) 0 r + 1) / 2 := by
    have hfe : (fun z => (‖f z‖ ^ 2 + 1) / 2)
        = (2 : ℝ)⁻¹ • ((fun z => ‖f z‖ ^ 2) + (fun _ => (1 : ℝ))) := by
      funext z
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    rw [hfe, Real.circleAverage_smul, Real.circleAverage_add hintsq hconst,
      Real.circleAverage_const]
    simp only [smul_eq_mul]
    ring
  rw [hcomp] at hmono
  have := hM r hr0 hr1
  linarith



lemma exists_bound_lt_one (F : Finset ℂ) (h : ∀ z ∈ F, ‖z‖ < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ z ∈ F, ‖z‖ < ρ := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1/2, by norm_num, by norm_num, by simp⟩
  | insert a F ha ih =>
    obtain ⟨ρ, hρ0, hρ1, hρ⟩ := ih (fun z hz => h z (Finset.mem_insert_of_mem hz))
    have ha1 : ‖a‖ < 1 := h a (Finset.mem_insert_self a F)
    refine ⟨max ρ ((‖a‖ + 1) / 2), lt_of_lt_of_le hρ0 (le_max_left _ _),
      max_lt hρ1 (by linarith), ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · exact lt_of_lt_of_le (hρ z hz') (le_max_left _ _)

lemma divisor_eq_order (f : ℂ → ℂ) {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) {z : ℂ} (hz : z ∈ U)
    (hord : analyticOrderAt f z ≠ ⊤) :
    (divisor f U) z = (analyticOrderNatAt f z : ℤ) := by
  rw [divisor_apply hf.meromorphicOn hz, (hf z hz).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt hord]
  simp



theorem sum_order_mul_one_sub_norm_le (f : ℂ → ℂ) (hf : MemHardyDisc f)
    (hford : ∀ z ∈ disc, analyticOrderAt f z ≠ ⊤) :
    ∃ C : ℝ, ∀ F : Finset ℂ, (∀ z ∈ F, ‖z‖ < 1) →
      ∑ z ∈ F, (analyticOrderNatAt f z : ℝ) * (1 - ‖z‖) ≤ C := by
  classical
  obtain ⟨M, hM⟩ := hf.2
  set n₀ : ℕ := analyticOrderNatAt f 0 with hn₀
  set c₀ : ℝ := Real.log ‖meromorphicTrailingCoeffAt f 0‖ with hc₀
  refine ⟨(M + 1) / 2 + 2 - c₀ + n₀, ?_⟩
  intro F hF
  obtain ⟨ρ, hρ0, hρ1, hρF⟩ := exists_bound_lt_one F hF
  set N : ℕ := ∑ z ∈ F, analyticOrderNatAt f z with hN
  set eps : ℝ := 1 / ((N : ℝ) + n₀ + 1) with heps
  have hden : (0:ℝ) < (N : ℝ) + n₀ + 1 := by positivity
  have heps0 : 0 < eps := by rw [heps]; positivity
  set r : ℝ := max ρ (Real.exp (-eps)) with hrdef
  have hr0 : 0 < r := lt_of_lt_of_le hρ0 (le_max_left _ _)
  have hr1 : r < 1 := max_lt hρ1 (by rw [Real.exp_lt_one_iff]; linarith)
  have hlogr : -eps ≤ Real.log r := by
    have h1 : Real.exp (-eps) ≤ r := le_max_right _ _
    calc -eps = Real.log (Real.exp (-eps)) := (Real.log_exp _).symm
      _ ≤ Real.log r := Real.log_le_log (Real.exp_pos _) h1
  have hlogr0 : Real.log r ≤ 0 := (Real.log_nonpos_iff hr0.le).mpr hr1.le
  have habs : |r| = r := abs_of_nonneg hr0.le
  have hball : closedBall (0:ℂ) |r| ⊆ disc := by
    rw [habs]
    intro x hx
    rw [mem_disc_iff]
    exact lt_of_le_of_lt (by simpa using mem_closedBall_zero_iff.mp hx) hr1
  have hfan : AnalyticOnNhd ℂ f (closedBall (0:ℂ) |r|) := hf.1.mono hball
  have hmero : MeromorphicOn f (closedBall (0:ℂ) |r|) := hfan.meromorphicOn
  set D := divisor f (closedBall (0:ℂ) |r|) with hD
  have hDzero : ∀ u ∉ closedBall (0:ℂ) |r|, D u = 0 := by
    intro u hu
    by_contra h
    exact hu (D.supportWithinDomain h)
  have hDval : ∀ u ∈ closedBall (0:ℂ) |r|, (D u : ℝ) = (analyticOrderNatAt f u : ℝ) := by
    intro u hu
    rw [hD, divisor_eq_order f hfan hu (hford u (hball hu))]
    simp
  have hDnn : ∀ u, (0:ℝ) ≤ (D u : ℝ) := by
    intro u
    by_cases hu : u ∈ closedBall (0:ℂ) |r|
    · rw [hDval u hu]; positivity
    · rw [hDzero u hu]; simp
  have hjensen := hmero.circleAverage_log_norm (ne_of_gt hr0)
  have hgnn : ∀ u : ℂ, 0 ≤ (D u : ℝ) * Real.log (r * ‖(0:ℂ) - u‖⁻¹) := by
    intro u
    by_cases hu : u ∈ closedBall (0:ℂ) |r|
    · rcases eq_or_ne u 0 with rfl | hu0
      · simp
      · have h1 : ‖u‖ ≤ r := by simpa [habs] using mem_closedBall_zero_iff.mp hu
        have h2 : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
        have h3 : (1:ℝ) ≤ r * ‖(0:ℂ) - u‖⁻¹ := by
          rw [zero_sub, norm_neg, le_mul_inv_iff₀ h2]
          linarith
        exact mul_nonneg (hDnn u) (Real.log_nonneg h3)
    · rw [hDzero u hu]; simp
  have hDfin : (Function.support (D : ℂ → ℤ)).Finite :=
    D.finiteSupport (isCompact_closedBall _ _)
  have hlow : ∑ z ∈ F.erase 0, (D z : ℝ) * Real.log (r * ‖(0:ℂ) - z‖⁻¹)
      ≤ ∑ᶠ (u : ℂ), (D u : ℝ) * Real.log (r * ‖(0:ℂ) - u‖⁻¹) := by
    have hfinsum : ∑ᶠ (u : ℂ), (D u : ℝ) * Real.log (r * ‖(0:ℂ) - u‖⁻¹)
        = ∑ u ∈ hDfin.toFinset ∪ F.erase 0, (D u : ℝ) * Real.log (r * ‖(0:ℂ) - u‖⁻¹) := by
      apply finsum_eq_sum_of_support_subset
      intro u hu
      simp only [Function.mem_support] at hu
      have hDu : D u ≠ 0 := by
        intro h
        exact hu (by rw [h]; simp)
      exact Finset.mem_coe.mpr (Finset.mem_union_left _ (hDfin.mem_toFinset.mpr hDu))
    rw [hfinsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      (fun i _ _ => hgnn i)
  have hA : Real.circleAverage (fun z => Real.log ‖f z‖) 0 r ≤ (M + 1) / 2 :=
    circleAverage_log_norm_le f hf hM hr0.le hr1
  have hD0 : (D 0 : ℝ) = (n₀ : ℝ) := hDval 0 (by simp)
  have hsum_le : ∑ z ∈ F.erase 0, (D z : ℝ) * Real.log (r * ‖(0:ℂ) - z‖⁻¹)
      ≤ (M + 1) / 2 - n₀ * Real.log r - c₀ := by
    rw [hD0] at hjensen
    linarith
  -- pointwise comparison
  have hstep : ∀ z ∈ F.erase 0, (analyticOrderNatAt f z : ℝ) * (1 - ‖z‖)
      ≤ (D z : ℝ) * Real.log (r * ‖(0:ℂ) - z‖⁻¹) + (analyticOrderNatAt f z : ℝ) * eps := by
    intro z hz
    have hz0 : z ≠ 0 := Finset.ne_of_mem_erase hz
    have hzF : z ∈ F := Finset.mem_of_mem_erase hz
    have hzn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
    have hzr : ‖z‖ ≤ r := le_of_lt (lt_of_lt_of_le (hρF z hzF) (le_max_left _ _))
    have hmem : z ∈ closedBall (0:ℂ) |r| := by
      rw [habs]
      simpa using hzr
    have hDz : (D z : ℝ) = (analyticOrderNatAt f z : ℝ) := hDval z hmem
    have hlogz : Real.log (r * ‖(0:ℂ) - z‖⁻¹) = Real.log r - Real.log ‖z‖ := by
      rw [zero_sub, norm_neg, Real.log_mul (ne_of_gt hr0) (by positivity), Real.log_inv]
      ring
    have hlz : Real.log ‖z‖ ≤ ‖z‖ - 1 := Real.log_le_sub_one_of_pos hzn
    rw [hDz, hlogz]
    have hnn : (0:ℝ) ≤ (analyticOrderNatAt f z : ℝ) := by positivity
    nlinarith [hnn, hlogr, hlz]
  have hNerase : ∑ z ∈ F.erase 0, (analyticOrderNatAt f z : ℝ) ≤ (N : ℝ) := by
    rw [hN]
    push_cast
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun i _ _ => by positivity)
  have hepsN : eps * (N : ℝ) ≤ 1 := by
    rw [heps]
    rw [div_mul_eq_mul_div, one_mul, div_le_one hden]
    have : (0:ℝ) ≤ (n₀ : ℝ) := by positivity
    linarith
  have hepsn₀ : (n₀ : ℝ) * eps ≤ 1 := by
    rw [heps, mul_one_div, div_le_one hden]
    have : (0:ℝ) ≤ (N : ℝ) := by positivity
    linarith
  have hkey : ∑ z ∈ F.erase 0, (analyticOrderNatAt f z : ℝ) * (1 - ‖z‖)
      ≤ (M + 1) / 2 + 2 - c₀ := by
    have h1 := Finset.sum_le_sum hstep
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h1
    have h2 : (∑ z ∈ F.erase 0, (analyticOrderNatAt f z : ℝ)) * eps ≤ 1 := by
      calc (∑ z ∈ F.erase 0, (analyticOrderNatAt f z : ℝ)) * eps ≤ (N : ℝ) * eps :=
            mul_le_mul_of_nonneg_right hNerase heps0.le
        _ = eps * (N : ℝ) := by ring
        _ ≤ 1 := hepsN
    have h3 : -((n₀ : ℝ) * Real.log r) ≤ 1 := by nlinarith [hlogr, hepsn₀]
    linarith
  by_cases h0F : (0:ℂ) ∈ F
  · rw [← Finset.sum_erase_add F _ h0F]
    simp only [norm_zero, sub_zero, mul_one, ← hn₀]
    linarith
  · rw [Finset.erase_eq_of_notMem h0F] at hkey
    have : (0:ℝ) ≤ (n₀ : ℝ) := by positivity
    linarith



lemma norm_zeroFamily_lt_one (f : ℂ → ℂ) (i : zeroIndex f) : ‖zeroFamily f i‖ < 1 :=
  mem_disc_iff.mp i.1.2

theorem isBlaschkeFamily_zeroFamily (f : ℂ → ℂ) (hf : MemHardyDisc f)
    (h0 : ∃ z ∈ disc, f z ≠ 0) : IsBlaschkeFamily (zeroFamily f) := by
  classical
  obtain ⟨z₁, hz₁U, hz₁⟩ := h0
  have hU : IsPreconnected (disc : Set ℂ) := (convex_ball (0 : ℂ) 1).isPreconnected
  have hford₁ : analyticOrderAt f z₁ = 0 := (hf.1 z₁ hz₁U).analyticOrderAt_eq_zero.mpr hz₁
  have hford : ∀ z ∈ disc, analyticOrderAt f z ≠ ⊤ := fun z hz =>
    hf.1.analyticOrderAt_ne_top_of_isPreconnected hU hz₁U hz
      (by rw [hford₁]; exact ENat.zero_ne_top)
  obtain ⟨C, hC⟩ := sum_order_mul_one_sub_norm_le f hf hford
  have hsum2 : Summable (fun z : disc => (analyticOrderNatAt f (z : ℂ) : ℝ) * (1 - ‖(z : ℂ)‖)) := by
    refine summable_of_sum_le (c := C) (fun z => ?_) (fun J => ?_)
    · have hz : ‖(z : ℂ)‖ < 1 := mem_disc_iff.mp z.2
      have : (0:ℝ) ≤ (analyticOrderNatAt f (z : ℂ) : ℝ) * (1 - ‖(z : ℂ)‖) := by
        have h1 : (0:ℝ) ≤ (analyticOrderNatAt f (z : ℂ) : ℝ) := by positivity
        nlinarith
      simpa using this
    · have hinj : ∀ x ∈ J, ∀ y ∈ J, ((x : ℂ)) = (y : ℂ) → x = y :=
        fun x _ y _ h => Subtype.ext h
      rw [← Finset.sum_image (f := fun z : ℂ => (analyticOrderNatAt f z : ℝ) * (1 - ‖z‖)) hinj]
      refine hC _ ?_
      intro z hz
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
      exact mem_disc_iff.mp p.2
  refine ⟨norm_zeroFamily_lt_one f, ?_⟩
  have hnn : ∀ i : zeroIndex f, 0 ≤ 1 - ‖zeroFamily f i‖ := by
    intro i
    have := norm_zeroFamily_lt_one f i
    linarith
  rw [summable_sigma_of_nonneg hnn]
  refine ⟨fun z => Summable.of_finite, ?_⟩
  have heq : ∀ z : disc,
      (∑' k : Fin (analyticOrderNatAt f (z : ℂ)), (1 - ‖zeroFamily f (⟨z, k⟩ : zeroIndex f)‖))
        = (analyticOrderNatAt f (z : ℂ) : ℝ) * (1 - ‖(z : ℂ)‖) := by
    intro z
    rw [tsum_fintype]
    simp only [zeroFamily, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [heq]
  exact hsum2


end Hardy
