/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import RiemannHypothesis.HardySpace.HardyDisc

/-!
# Inner-outer factorization on the unit disc

The main theorem of this file states that every nonzero function `f` of the Hardy space `H²`
of the unit disc factors as

  `f = B · G`

where `B` is the Blaschke product built from the zeros of `f` (so `B` is analytic, bounded by
one, and has exactly the zeros of `f`, with multiplicity) and `G` is analytic and zero-free on
the disc.
-/

noncomputable section

open Filter Topology Metric Set Complex Blaschke MeromorphicOn

namespace Hardy

/-- **Inner-outer factorization on the disc.**  A nonzero Hardy space function is the product of
the Blaschke product of its zeros and a zero-free analytic function. -/
theorem hardyDisc_inner_outer (f : ℂ → ℂ) (hf : MemHardyDisc f) (h0 : ∃ z ∈ disc, f z ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G disc ∧ (∀ z ∈ disc, G z ≠ 0) ∧
      ∀ z ∈ disc, f z = blaschkeProduct (zeroFamily f) z * G z := by
  classical
  obtain ⟨z₁, hz₁U, hz₁⟩ := h0
  have hfan : AnalyticOnNhd ℂ f disc := hf.1
  have hU : IsPreconnected (disc : Set ℂ) := (convex_ball (0 : ℂ) 1).isPreconnected
  have hfam : IsBlaschkeFamily (zeroFamily f) :=
    isBlaschkeFamily_zeroFamily f hf ⟨z₁, hz₁U, hz₁⟩
  set B : ℂ → ℂ := blaschkeProduct (zeroFamily f) with hB_def
  have hBan : AnalyticOnNhd ℂ B disc := blaschkeProduct_analyticOnNhd hfam
  -- Orders of `f` are finite
  have hford₁ : analyticOrderAt f z₁ = 0 := (hfan z₁ hz₁U).analyticOrderAt_eq_zero.mpr hz₁
  have hford : ∀ z ∈ disc, analyticOrderAt f z ≠ ⊤ := fun z hz =>
    hfan.analyticOrderAt_ne_top_of_isPreconnected hU hz₁U hz
      (by rw [hford₁]; exact ENat.zero_ne_top)
  -- The Blaschke product has the same orders as `f`
  have horder : ∀ z ∈ disc, analyticOrderAt B z = analyticOrderAt f z := by
    intro z hz
    rw [hB_def, analyticOrderAt_blaschkeProduct hfam (mem_disc_iff.mp hz),
      card_fiber_zeroFamily f hz]
    exact Nat.cast_analyticOrderNatAt (hford z hz)
  have hmf : ∀ z ∈ disc, meromorphicOrderAt f z ≠ ⊤ := by
    intro z hz
    rw [(hfan z hz).meromorphicOrderAt_eq]
    simpa using hford z hz
  have hmB : ∀ z ∈ disc, meromorphicOrderAt B z ≠ ⊤ := by
    intro z hz
    rw [(hBan z hz).meromorphicOrderAt_eq]
    simpa [horder z hz] using hford z hz
  have hmBinv : ∀ z ∈ disc, meromorphicOrderAt B⁻¹ z ≠ ⊤ := by
    intro z hz
    rw [meromorphicOrderAt_inv]
    simpa using hmB z hz
  -- The divisors agree
  have hdivfB : divisor f disc = divisor B disc := by
    ext z
    by_cases hz : z ∈ disc
    · rw [divisor_apply hfan.meromorphicOn hz, divisor_apply hBan.meromorphicOn hz,
        (hfan z hz).meromorphicOrderAt_eq, (hBan z hz).meromorphicOrderAt_eq, horder z hz]
    · simp [hz]
  -- The quotient
  set F : ℂ → ℂ := f * B⁻¹ with hF_def
  have hmBinv' : ∀ z ∈ disc, meromorphicOrderAt B⁻¹ z ≠ ⊤ := hmBinv
  have hFmero : MeromorphicOn F disc := hfan.meromorphicOn.mul hBan.meromorphicOn.inv
  have hdivF : divisor F disc = 0 := by
    rw [hF_def, divisor_mul hfan.meromorphicOn hBan.meromorphicOn.inv hmf hmBinv',
      divisor_inv, hdivfB]
    simp
  set G : ℂ → ℂ := toMeromorphicNFOn F disc with hG_def
  have hGnf : MeromorphicNFOn G disc := meromorphicNFOn_toMeromorphicNFOn F disc
  have hdivG : divisor G disc = 0 := by
    rw [hG_def, MeromorphicOn.divisor_of_toMeromorphicNFOn hFmero, hdivF]
  have hGan : AnalyticOnNhd ℂ G disc :=
    hGnf.divisor_nonneg_iff_analyticOnNhd.mp (by rw [hdivG])
  have hmF : ∀ z ∈ disc, meromorphicOrderAt F z ≠ ⊤ := by
    intro z hz
    rw [hF_def, meromorphicOrderAt_mul (hfan z hz).meromorphicAt
      (hBan z hz).meromorphicAt.inv]
    exact WithTop.add_ne_top.mpr ⟨hmf z hz, hmBinv z hz⟩
  have hmG : ∀ u : (disc : Set ℂ), meromorphicOrderAt G u ≠ ⊤ := by
    rintro ⟨u, hu⟩
    rw [hG_def, meromorphicOrderAt_toMeromorphicNFOn hFmero hu]
    exact hmF u hu
  have hGne : ∀ z ∈ disc, G z ≠ 0 := by
    intro z hz hGz
    have hmem : z ∈ disc ∩ G ⁻¹' {0} := ⟨hz, hGz⟩
    rw [hGnf.zero_set_eq_divisor_support hmG] at hmem
    simp [hdivG] at hmem
  refine ⟨G, hGan, hGne, ?_⟩
  -- identity theorem
  have hBz₁ : B z₁ ≠ 0 := by
    have : analyticOrderAt B z₁ = 0 := by rw [horder z₁ hz₁U, hford₁]
    exact (hBan z₁ hz₁U).analyticOrderAt_eq_zero.mp this
  have hfreq : ∃ᶠ z in 𝓝[≠] z₁, f z = B z * G z := by
    have h1 : ∀ᶠ z in 𝓝[≠] z₁, G z = F z :=
      MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE hFmero hz₁U
    have h2 : ∀ᶠ z in 𝓝[≠] z₁, B z ≠ 0 := by
      have hcont : ContinuousAt B z₁ := (hBan z₁ hz₁U).continuousAt
      exact (hcont.eventually_ne hBz₁).filter_mono nhdsWithin_le_nhds
    have : ∀ᶠ z in 𝓝[≠] z₁, f z = B z * G z := by
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hF_def]
      simp only [Pi.mul_apply, Pi.inv_apply]
      field_simp
    exact this.frequently
  have := (hfan.eqOn_of_preconnected_of_frequently_eq (hBan.mul hGan) hU hz₁U hfreq)
  intro z hz
  simpa using this hz

end Hardy
