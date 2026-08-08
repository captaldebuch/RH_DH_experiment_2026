/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import RiemannHypothesis.HardySpace.BlaschkeFactor

/-!
# Blaschke products

Given a family `a : ι → ℂ` of points of the unit disc satisfying the *Blaschke condition*
`∑ i, (1 - ‖a i‖) < ∞`, the associated Blaschke product is

  `B(z) = ∏' i, b_{a i}(z)`.

We prove that `B` is analytic on the disc, that `‖B‖ ≤ 1` there, and record the splitting of `B`
into a finite product times a tail which is uniformly close to `1` on a compact subdisc.
-/

noncomputable section

open Filter Topology Metric Set Complex

namespace Blaschke

variable {ι : Type*} {a : ι → ℂ} {z : ℂ} {ρ : ℝ}

/-- A family of points of the unit disc satisfying the Blaschke condition. -/
structure IsBlaschkeFamily (a : ι → ℂ) : Prop where
  norm_lt_one : ∀ i, ‖a i‖ < 1
  summable : Summable fun i => 1 - ‖a i‖

/-- The Blaschke product associated with a family of points of the disc. -/
def blaschkeProduct (a : ι → ℂ) (z : ℂ) : ℂ := ∏' i, blaschkeFactor (a i) z

lemma IsBlaschkeFamily.subtype (ha : IsBlaschkeFamily a) (p : ι → Prop) :
    IsBlaschkeFamily (fun i : {i // p i} => a i) where
  norm_lt_one i := ha.norm_lt_one i
  summable := ha.summable.subtype _

/-- The summable majorant controlling the Blaschke product on the subdisc of radius `ρ`. -/
lemma summable_majorant (ha : IsBlaschkeFamily a) (ρ : ℝ) :
    Summable fun i => (1 - ‖a i‖) * ((1 + ρ) / (1 - ρ)) :=
  ha.summable.mul_right _

lemma majorant_nonneg (ha : IsBlaschkeFamily a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (i : ι) :
    0 ≤ (1 - ‖a i‖) * ((1 + ρ) / (1 - ρ)) := by
  have h1 : 0 ≤ 1 - ‖a i‖ := by linarith [ha.norm_lt_one i]
  have h2 : 0 ≤ (1 + ρ) / (1 - ρ) := by
    apply div_nonneg <;> linarith
  exact mul_nonneg h1 h2

lemma le_majorant (ha : IsBlaschkeFamily a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (i : ι) :
    1 - ‖a i‖ ≤ (1 - ‖a i‖) * ((1 + ρ) / (1 - ρ)) := by
  have h1 : 0 ≤ 1 - ‖a i‖ := by linarith [ha.norm_lt_one i]
  have h2 : (1 : ℝ) ≤ (1 + ρ) / (1 - ρ) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  nlinarith

lemma norm_blaschkeFactor_sub_one_le (ha : IsBlaschkeFamily a) (hρ : ρ < 1) (i : ι)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) ρ) :
    ‖blaschkeFactor (a i) z - 1‖ ≤ (1 - ‖a i‖) * ((1 + ρ) / (1 - ρ)) := by
  have hz' : ‖z‖ ≤ ρ := by simpa using hz
  rw [← norm_neg, neg_sub]
  exact norm_one_sub_blaschkeFactor_le (ha.norm_lt_one i) hρ hz'

lemma closedBall_subset_disc (hρ1 : ρ < 1) : closedBall (0 : ℂ) ρ ⊆ disc := by
  intro w hw
  have : ‖w‖ ≤ ρ := by simpa using hw
  exact mem_disc_iff.mpr (lt_of_le_of_lt this hρ1)

/-- The Blaschke product converges uniformly on every closed subdisc. -/
lemma hasProdUniformlyOn_closedBall (ha : IsBlaschkeFamily a) (hρ1 : ρ < 1) :
    HasProdUniformlyOn (fun i z => blaschkeFactor (a i) z) (blaschkeProduct a)
      (closedBall (0 : ℂ) ρ) := by
  have hsub : closedBall (0 : ℂ) ρ ⊆ disc := closedBall_subset_disc hρ1
  have hbase :
      HasProdUniformlyOn (fun i z => 1 + (blaschkeFactor (a i) z - 1))
        (fun z => ∏' i, (1 + (blaschkeFactor (a i) z - 1))) (closedBall (0 : ℂ) ρ) :=
    Summable.hasProdUniformlyOn_one_add (isCompact_closedBall _ _) (summable_majorant ha ρ)
      (Filter.Eventually.of_forall fun i z hz => norm_blaschkeFactor_sub_one_le ha hρ1 i hz)
      (fun i => ((blaschkeFactor_continuousOn (ha.norm_lt_one i)).mono hsub).sub continuousOn_const)
  have h1 : HasProdUniformlyOn (fun i z => blaschkeFactor (a i) z)
      (fun z => ∏' i, (1 + (blaschkeFactor (a i) z - 1))) (closedBall (0 : ℂ) ρ) := by
    refine hbase.congr (Filter.Eventually.of_forall fun s z _ => ?_)
    simp
  refine h1.congr_right fun w _ => ?_
  simp [blaschkeProduct]

lemma multipliable_blaschkeFactor (ha : IsBlaschkeFamily a) (hz : ‖z‖ < 1) :
    Multipliable fun i => blaschkeFactor (a i) z :=
  ((hasProdUniformlyOn_closedBall ha hz).multipliableUniformlyOn).multipliable
    (by simp)

/-- Partial products converge to the Blaschke product. -/
lemma hasProd_blaschkeFactor (ha : IsBlaschkeFamily a) (hz : ‖z‖ < 1) :
    HasProd (fun i => blaschkeFactor (a i) z) (blaschkeProduct a z) :=
  (multipliable_blaschkeFactor ha hz).hasProd

/-- Blaschke products are analytic on the unit disc. -/
lemma blaschkeProduct_analyticOnNhd (ha : IsBlaschkeFamily a) :
    AnalyticOnNhd ℂ (blaschkeProduct a) disc := by
  intro z₀ hz₀
  have hz₀' : ‖z₀‖ < 1 := mem_disc_iff.mp hz₀
  set ρ : ℝ := (‖z₀‖ + 1) / 2 with hρdef
  have hρ0 : 0 ≤ ρ := by
    have := norm_nonneg z₀
    simp only [hρdef]; linarith
  have hρ1 : ρ < 1 := by simp only [hρdef]; linarith
  have hz₀ρ : ‖z₀‖ < ρ := by simp only [hρdef]; linarith
  have hU := hasProdUniformlyOn_iff_tendstoUniformlyOn.mp
    (hasProdUniformlyOn_closedBall ha hρ1)
  have h2 : TendstoLocallyUniformlyOn (fun (s : Finset ι) z => ∏ i ∈ s, blaschkeFactor (a i) z)
      (blaschkeProduct a) atTop (ball (0 : ℂ) ρ) :=
    (hU.mono ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hdiff : ∀ᶠ (s : Finset ι) in atTop,
      DifferentiableOn ℂ (fun z => ∏ i ∈ s, blaschkeFactor (a i) z) (ball (0 : ℂ) ρ) := by
    filter_upwards with s
    intro w hw
    have hw' : ‖w‖ < ρ := by simpa using hw
    have : ∀ i ∈ s, DifferentiableWithinAt ℂ (blaschkeFactor (a i)) (ball (0 : ℂ) ρ) w := by
      intro i _
      exact ((blaschkeFactor_analyticAt (ha.norm_lt_one i)
        (lt_trans hw' hρ1)).differentiableAt).differentiableWithinAt
    have hprod := DifferentiableWithinAt.finset_prod this
    have hfun : (∏ i ∈ s, blaschkeFactor (a i)) = fun w => ∏ i ∈ s, blaschkeFactor (a i) w :=
      funext fun w => by simp
    rwa [hfun] at hprod
  have hd := h2.differentiableOn hdiff isOpen_ball
  exact (hd.analyticOnNhd isOpen_ball) z₀ (by simpa using hz₀ρ)

/-- Blaschke products are bounded by one on the unit disc. -/
lemma norm_blaschkeProduct_le_one (ha : IsBlaschkeFamily a) (hz : ‖z‖ < 1) :
    ‖blaschkeProduct a z‖ ≤ 1 := by
  have h := (hasProd_blaschkeFactor ha hz).norm
  refine le_of_tendsto h (Filter.Eventually.of_forall fun s => ?_)
  exact Finset.prod_le_one (fun i _ => norm_nonneg _)
    (fun i _ => (norm_blaschkeFactor_lt_one (ha.norm_lt_one i) hz).le)

/-- Quantitative bound: on a closed subdisc, the Blaschke product is close to `1` whenever the
Blaschke sum is small. -/
lemma norm_blaschkeProduct_sub_one_le (ha : IsBlaschkeFamily a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hz : z ∈ closedBall (0 : ℂ) ρ) :
    ‖blaschkeProduct a z - 1‖
      ≤ Real.exp (∑' i, (1 - ‖a i‖) * ((1 + ρ) / (1 - ρ))) - 1 := by
  have hz' : ‖z‖ ≤ ρ := by simpa using hz
  have hzlt : ‖z‖ < 1 := lt_of_le_of_lt hz' hρ1
  have h := ((hasProd_blaschkeFactor ha hzlt).sub_const (1 : ℂ)).norm
  refine le_of_tendsto h (Filter.Eventually.of_forall fun s => ?_)
  have key := Finset.norm_prod_one_add_sub_one_le s (fun i => blaschkeFactor (a i) z - 1)
  have heq : ∏ i ∈ s, (1 + (blaschkeFactor (a i) z - 1)) = ∏ i ∈ s, blaschkeFactor (a i) z := by
    refine Finset.prod_congr rfl fun i _ => by ring
  rw [heq] at key
  refine key.trans ?_
  have hsum : ∑ i ∈ s, ‖blaschkeFactor (a i) z - 1‖
      ≤ ∑' i, (1 - ‖a i‖) * ((1 + ρ) / (1 - ρ)) := by
    refine le_trans (Finset.sum_le_sum fun i _ => norm_blaschkeFactor_sub_one_le ha hρ1 i hz) ?_
    exact (summable_majorant ha ρ).sum_le_tsum s
      (fun i _ => majorant_nonneg ha hρ0 hρ1 i)
  have := Real.exp_le_exp.mpr hsum
  linarith

/-- Splitting off a finite set of factors. -/
lemma blaschkeProduct_split (ha : IsBlaschkeFamily a) (S : Finset ι) (hz : ‖z‖ < 1) :
    blaschkeProduct a z
      = (∏ i ∈ S, blaschkeFactor (a i) z) * blaschkeProduct (fun i : {i // i ∉ S} => a i) z := by
  have htail : HasProd (fun i : {i // i ∉ S} => blaschkeFactor (a i) z)
      (blaschkeProduct (fun i : {i // i ∉ S} => a i) z) :=
    hasProd_blaschkeFactor (ha.subtype _) hz
  have h1 : HasProd ((fun i => blaschkeFactor (a i) z) ∘ ((↑) : (↑S : Set ι) → ι))
      (∏ i ∈ S, blaschkeFactor (a i) z) := S.hasProd _
  have h2 : HasProd ((fun i => blaschkeFactor (a i) z) ∘
      ((↑) : ((↑S : Set ι)ᶜ : Set ι) → ι))
      (blaschkeProduct (fun i : {i // i ∉ S} => a i) z) := htail
  exact (h1.mul_compl h2).tprod_eq

/-- Given `ρ < 1`, all but finitely many points of a Blaschke family lie outside the disc of
radius `ρ`, and the remaining tail sum is arbitrarily small. -/
lemma exists_finset_tail_small (ha : IsBlaschkeFamily a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ι, (∀ i, i ∉ S → ρ < ‖a i‖) ∧
      (∑' i : {i // i ∉ S}, (1 - ‖a i‖) * ((1 + ρ) / (1 - ρ))) < ε := by
  set u : ι → ℝ := fun i => (1 - ‖a i‖) * ((1 + ρ) / (1 - ρ)) with hu_def
  have hu : Summable u := summable_majorant ha ρ
  have hunonneg : ∀ i, 0 ≤ u i := fun i => majorant_nonneg ha hρ0 hρ1 i
  set δ : ℝ := min ε (1 - ρ) with hδ_def
  have hδ : 0 < δ := lt_min hε (by linarith)
  have htend := tendsto_tsum_compl_atTop_zero u
  have hev : ∀ᶠ s : Finset ι in atTop, (∑' i : {i // i ∉ s}, u i) < δ := by
    have := htend.eventually (eventually_lt_nhds hδ)
    simpa using this
  obtain ⟨S, hS⟩ := hev.exists
  refine ⟨S, ?_, lt_of_lt_of_le hS (min_le_left _ _)⟩
  intro i hi
  have hle : u i ≤ ∑' j : {j // j ∉ S}, u j := by
    have := (hu.subtype {j | j ∉ S}).le_tsum ⟨i, hi⟩ (fun j _ => hunonneg j)
    simpa using this
  have h1 : 1 - ‖a i‖ ≤ u i := le_majorant ha hρ0 hρ1 i
  have h2 : u i < 1 - ρ := lt_of_le_of_lt hle (lt_of_lt_of_le hS (min_le_right _ _))
  linarith

end Blaschke
