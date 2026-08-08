/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import RiemannHypothesis.HardySpace.BlaschkeProduct

/-!
# Zeros of Blaschke products

The zeros of the Blaschke product attached to a Blaschke family `a : ι → ℂ` are exactly the
points `a i`, and the order of vanishing at a point `z` is the number of indices `i` with
`a i = z`.
-/

noncomputable section

open Filter Topology Metric Set Complex

namespace Blaschke

variable {ι : Type*} {a : ι → ℂ} {z : ℂ} {ρ : ℝ}

/-- The set of indices with a prescribed value is finite. -/
lemma finite_fiber (ha : IsBlaschkeFamily a) (z : ℂ) : {i | a i = z}.Finite := by
  by_cases hz : ‖z‖ < 1
  · have h := ha.summable.tendsto_cofinite_zero
    have hev : ∀ᶠ i in Filter.cofinite, |1 - ‖a i‖| < 1 - ‖z‖ := by
      have := h.eventually (Metric.ball_mem_nhds (0 : ℝ) (by linarith : (0:ℝ) < 1 - ‖z‖))
      simpa [Real.dist_eq, abs_sub_comm] using this
    have hfin := Filter.eventually_cofinite.mp hev
    refine hfin.subset ?_
    intro i hi
    simp only [mem_setOf_eq] at hi ⊢
    rw [hi]
    have : (0:ℝ) ≤ 1 - ‖z‖ := by linarith
    rw [abs_of_nonneg this]
    exact lt_irrefl _
  · have : {i | a i = z} = ∅ := by
      ext i
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro hi
      exact hz (hi ▸ ha.norm_lt_one i)
    rw [this]
    exact finite_empty

/-- The order of vanishing of a single Blaschke factor. -/
lemma analyticOrderAt_blaschkeFactor {b : ℂ} (hb : ‖b‖ < 1) (hz : ‖z‖ < 1) :
    analyticOrderAt (blaschkeFactor b) z = if b = z then 1 else 0 := by
  by_cases h : b = z
  · subst h
    have hbmem : b ∈ disc := mem_disc_iff.mpr hb
    have hdisc : disc ∈ 𝓝 b := isOpen_ball.mem_nhds hbmem
    have heq : blaschkeFactor b =ᶠ[𝓝 b]
        (fun w : ℂ => w - b) * fun w : ℂ => (blaschkeUnit b w)⁻¹ := by
      filter_upwards [hdisc] with w hw
      have hw' : ‖w‖ < 1 := mem_disc_iff.mp hw
      have hunit : blaschkeUnit b w ≠ 0 := blaschkeUnit_ne_zero hb hw'
      have hx := sub_eq_blaschkeFactor_mul_unit hb hw'
      simp only [Pi.mul_apply]
      rw [← div_eq_mul_inv, eq_div_iff hunit]
      exact hx.symm
    have h1 : AnalyticAt ℂ (fun w : ℂ => w - b) b := by fun_prop
    have h2 : AnalyticAt ℂ (fun w : ℂ => (blaschkeUnit b w)⁻¹) b :=
      (blaschkeUnit_analyticOnNhd hb b (mem_disc_iff.mpr hb)).inv (blaschkeUnit_ne_zero hb hb)
    rw [analyticOrderAt_congr heq, analyticOrderAt_mul h1 h2]
    have e1 : analyticOrderAt (fun w : ℂ => w - b) b = 1 := by
      have hmono : (fun w : ℂ => w - b) = ((· - b) ^ 1 : ℂ → ℂ) := by funext w; simp
      rw [hmono, analyticOrderAt_centeredMonomial]
      simp
    have e2 : analyticOrderAt (fun w : ℂ => (blaschkeUnit b w)⁻¹) b = 0 :=
      h2.analyticOrderAt_eq_zero.mpr (by simp [blaschkeUnit_ne_zero hb hb])
    rw [e1, e2, add_zero, if_pos rfl]
  · rw [if_neg h]
    refine (blaschkeFactor_analyticAt hb hz).analyticOrderAt_eq_zero.mpr ?_
    rw [Ne, blaschkeFactor_eq_zero_iff hb hz]
    exact fun hh => h hh.symm

/-- The order of vanishing of a finite product of Blaschke factors. -/
lemma analyticOrderAt_finset_prod (ha : IsBlaschkeFamily a) (hz : ‖z‖ < 1) (S : Finset ι) :
    analyticOrderAt (fun w => ∏ i ∈ S, blaschkeFactor (a i) w) z
      = ∑ i ∈ S, (if a i = z then (1 : ℕ∞) else 0) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [analyticOrderAt_eq_zero]
  | insert j S hj ih =>
    have hfac : (fun w => ∏ i ∈ insert j S, blaschkeFactor (a i) w)
        = (fun w => blaschkeFactor (a j) w) * fun w => ∏ i ∈ S, blaschkeFactor (a i) w := by
      funext w
      simp only [Pi.mul_apply]
      rw [Finset.prod_insert hj]
    have h1 : AnalyticAt ℂ (fun w => blaschkeFactor (a j) w) z :=
      blaschkeFactor_analyticAt (ha.norm_lt_one j) hz
    have h2 : AnalyticAt ℂ (fun w => ∏ i ∈ S, blaschkeFactor (a i) w) z := by
      have : ∀ i ∈ S, AnalyticAt ℂ (fun w => blaschkeFactor (a i) w) z :=
        fun i _ => blaschkeFactor_analyticAt (ha.norm_lt_one i) hz
      exact Finset.analyticAt_fun_prod S this
    rw [hfac, analyticOrderAt_mul h1 h2, ih, Finset.sum_insert hj,
      analyticOrderAt_blaschkeFactor (ha.norm_lt_one j) hz]

/-- The order of vanishing of a Blaschke product at a point of the disc is the number of
members of the family equal to that point. -/
lemma analyticOrderAt_blaschkeProduct (ha : IsBlaschkeFamily a) (hz : ‖z‖ < 1) :
    analyticOrderAt (blaschkeProduct a) z = (Nat.card {i // a i = z} : ℕ∞) := by
  classical
  set ρ : ℝ := (‖z‖ + 1) / 2 with hρdef
  have hρ0 : 0 ≤ ρ := by have := norm_nonneg z; simp only [hρdef]; linarith
  have hρ1 : ρ < 1 := by simp only [hρdef]; linarith
  have hzρ : ‖z‖ < ρ := by simp only [hρdef]; linarith
  obtain ⟨S, hS, hsmall⟩ := exists_finset_tail_small ha hρ0 hρ1 (Real.log_pos one_lt_two)
  set T : ℂ → ℂ := blaschkeProduct (fun i : {i // i ∉ S} => a i) with hT_def
  have hTfam : IsBlaschkeFamily (fun i : {i // i ∉ S} => a i) := ha.subtype _
  -- the tail does not vanish on the closed subdisc
  have hTz : T z ≠ 0 := by
    have hmem : z ∈ closedBall (0 : ℂ) ρ := by simp [hzρ.le]
    have hb := norm_blaschkeProduct_sub_one_le hTfam hρ0 hρ1 hmem
    have hlt : Real.exp (∑' i : {i // i ∉ S}, (1 - ‖a i‖) * ((1 + ρ) / (1 - ρ))) - 1 < 1 := by
      have := Real.exp_lt_exp.mpr hsmall
      rw [Real.exp_log (by norm_num)] at this
      linarith
    intro hTz0
    rw [show blaschkeProduct (fun i : {i // i ∉ S} => a (i : ι)) z = 0 from hTz0] at hb
    simp only [zero_sub, norm_neg, norm_one] at hb
    linarith
  -- split the product
  have hsplit : blaschkeProduct a =ᶠ[𝓝 z]
      (fun w => ∏ i ∈ S, blaschkeFactor (a i) w) * T := by
    have hdisc : disc ∈ 𝓝 z := isOpen_ball.mem_nhds (mem_disc_iff.mpr hz)
    filter_upwards [hdisc] with w hw
    simp only [Pi.mul_apply]
    exact blaschkeProduct_split ha S (mem_disc_iff.mp hw)
  have hP : AnalyticAt ℂ (fun w => ∏ i ∈ S, blaschkeFactor (a i) w) z :=
    Finset.analyticAt_fun_prod S (fun i _ => blaschkeFactor_analyticAt (ha.norm_lt_one i) hz)
  have hTan : AnalyticAt ℂ T z := blaschkeProduct_analyticOnNhd hTfam z (mem_disc_iff.mpr hz)
  rw [analyticOrderAt_congr hsplit, analyticOrderAt_mul hP hTan,
    hTan.analyticOrderAt_eq_zero.mpr hTz, add_zero, analyticOrderAt_finset_prod ha hz]
  -- count
  have hsubS : {i | a i = z} = ↑(S.filter (fun i => a i = z)) := by
    ext i
    simp only [mem_setOf_eq, Finset.coe_filter]
    refine ⟨fun hi => ⟨?_, hi⟩, fun h => h.2⟩
    by_contra hiS
    have hlt := hS i hiS
    rw [hi] at hlt
    linarith
  have hcard : Nat.card {i // a i = z} = (S.filter (fun i => a i = z)).card := by
    have hnc : Nat.card {i // a i = z} = Set.ncard {i | a i = z} := Nat.card_coe_set_eq _
    rw [hnc, hsubS, Set.ncard_coe_finset]
  rw [hcard, ← Finset.sum_filter]
  simp

/-- The zeros of a Blaschke product are exactly the points of the family. -/
lemma blaschkeProduct_eq_zero_iff (ha : IsBlaschkeFamily a) (hz : ‖z‖ < 1) :
    blaschkeProduct a z = 0 ↔ ∃ i, a i = z := by
  have han : AnalyticAt ℂ (blaschkeProduct a) z :=
    blaschkeProduct_analyticOnNhd ha z (mem_disc_iff.mpr hz)
  constructor
  · intro h0
    have hne : analyticOrderAt (blaschkeProduct a) z ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨han, h0⟩
    rw [analyticOrderAt_blaschkeProduct ha hz] at hne
    have : Nat.card {i // a i = z} ≠ 0 := by
      intro h
      rw [h] at hne
      simp at hne
    have hfin : Finite {i // a i = z} := (finite_fiber ha z).to_subtype
    have hnonempty : Nonempty {i // a i = z} := (Nat.card_ne_zero.mp this).1
    obtain ⟨i, hi⟩ := hnonempty
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    have hne : Nat.card {i // a i = z} ≠ 0 := by
      have hfin : Finite {i // a i = z} := (finite_fiber ha z).to_subtype
      have : Nonempty {i // a i = z} := ⟨⟨i, hi⟩⟩
      exact Nat.card_ne_zero.mpr ⟨this, hfin⟩
    have hord : analyticOrderAt (blaschkeProduct a) z ≠ 0 := by
      rw [analyticOrderAt_blaschkeProduct ha hz]
      simpa using hne
    exact (analyticOrderAt_ne_zero.mp hord).2

end Blaschke
