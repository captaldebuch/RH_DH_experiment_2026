/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import RiemannHypothesis.HardySpace.InnerOuterDisc

/-!
# Inner-outer factorization on the half-plane `{re z > 1/2}`

This file transports the disc factorization `Hardy.hardyDisc_inner_outer` to the half-plane
`{z : ℂ | 1/2 < z.re}` through the Cayley map

  `cayley w = 1/2 + (1 + w) / (1 - w)`,  `cayleyInv z = (z - 3/2) / (z + 1/2)`,

which is a biholomorphism from the open unit disc onto the half-plane.

## Contents

* `Hardy.halfPlane`, `Hardy.cayley`, `Hardy.cayleyInv` and their basic properties;
* `Hardy.MemHardyHalfPlane`, the Hardy space `H²` of the half-plane, *defined by transport*
  from the Hardy space of the disc with the usual conformal weight `(1 - w)⁻¹`;
* `Hardy.IsInnerFunction` and `Hardy.IsOuterFunction`, the two notions in the form requested;
* `Hardy.inner_outer_factorization`, the existence half of the requested theorem, in a
  strengthened form which also records that `‖B‖ ≤ 1` on the half-plane and that `B` and `f`
  have the same zeros;
* `Hardy.inner_outer_factorization_not_unique`, a **disproof** of the uniqueness half of the
  requested theorem.

## Caveats and gaps (please read)

1. **The requested boundary condition is vacuous.**  `IsInnerFunction θ` as specified constrains
   `θ` only on the *open* half-plane (analyticity) and at the points `1/2 + i t`, which lie on
   its *boundary* and are therefore not constrained by the analyticity requirement.  A function
   may be modified arbitrarily off the open half-plane, so `∀ t, ‖θ (1/2 + t * I)‖ = 1` carries
   no information about the behaviour of `θ` inside.  Our inner factor is genuinely a Blaschke
   product transported from the disc, and we record the extra genuine information `‖B‖ ≤ 1`
   and `B z = 0 ↔ f z = 0`.

2. **The requested `IsOuterFunction` is equivalent to "analytic and zero-free".**  For a
   zero-free analytic `g`, `log ‖g‖` is automatically harmonic
   (`AnalyticAt.harmonicAt_log_norm`), so the third clause of the definition is implied by the
   first two; see `Hardy.isOuterFunction_of_ne_zero`.  In the classical theory "outer" is a
   strictly stronger notion, defined through a Poisson integral of the boundary values; that
   theory (boundary values of `H²` functions, singular inner functions, the Poisson
   representation of `log|g|`) is **not** available in Mathlib and is **not** formalized here.
   What is proved here is therefore the factorization
   `f = (Blaschke product) × (zero-free analytic function)`, which is the first — and only
   the first — step of the classical inner-outer factorization.

3. **Uniqueness is false as stated**, precisely because of 1 and 2; see
   `Hardy.inner_outer_factorization_not_unique`.  The correct uniqueness statement is that the
   *zero divisor*, hence the Blaschke factor, is determined by `f`; the remaining factor is
   determined only up to a zero-free analytic unit.

4. **The half-plane Hardy space is defined by transport.**  The equivalence of
   `MemHardyHalfPlane` with the classical definition through uniformly bounded integrals over
   the vertical lines `re z = σ` is classical but is not formalized here.
-/

noncomputable section

open Filter Topology Metric Set Complex Blaschke

namespace Hardy

/-! ## The half-plane and the Cayley transform -/

/-- The open half-plane `{z : ℂ | 1/2 < z.re}`. -/
def halfPlane : Set ℂ := {z : ℂ | 1 / 2 < z.re}

lemma mem_halfPlane_iff {z : ℂ} : z ∈ halfPlane ↔ 1 / 2 < z.re := Iff.rfl

lemma isOpen_halfPlane : IsOpen halfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

/-- The Cayley map from the unit disc onto the half-plane `{re z > 1/2}`. -/
def cayley (w : ℂ) : ℂ := 1 / 2 + (1 + w) / (1 - w)

/-- The inverse Cayley map, from the half-plane `{re z > 1/2}` onto the unit disc. -/
def cayleyInv (z : ℂ) : ℂ := (z - 3 / 2) / (z + 1 / 2)

lemma one_sub_ne_zero_of_mem_disc {w : ℂ} (hw : w ∈ disc) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := by linear_combination -h
  rw [this] at hw
  simpa using mem_disc_iff.mp hw

lemma add_half_ne_zero_of_mem_halfPlane {z : ℂ} (hz : z ∈ halfPlane) : z + 1 / 2 ≠ 0 := by
  intro h
  have hre : z.re + 1 / 2 = 0 := by
    have := congrArg Complex.re h
    simpa using this
  have := mem_halfPlane_iff.mp hz
  linarith

lemma cayley_mem_halfPlane {w : ℂ} (hw : w ∈ disc) : cayley w ∈ halfPlane := by
  have h1 : 1 - w ≠ 0 := one_sub_ne_zero_of_mem_disc hw
  have hnw : ‖w‖ < 1 := mem_disc_iff.mp hw
  have hden : (0:ℝ) < Complex.normSq (1 - w) := Complex.normSq_pos.mpr h1
  have hnum : 0 < 1 - Complex.normSq w := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hu : ((1 + w) / (1 - w)).re = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
    rw [Complex.div_re, ← add_div, div_eq_div_iff (ne_of_gt hden) (ne_of_gt hden)]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hpos : 0 < (1 - Complex.normSq w) / Complex.normSq (1 - w) := by positivity
  rw [mem_halfPlane_iff, cayley, Complex.add_re, hu]
  norm_num
  linarith

lemma cayleyInv_mem_disc {z : ℂ} (hz : z ∈ halfPlane) : cayleyInv z ∈ disc := by
  have h1 : z + 1 / 2 ≠ 0 := add_half_ne_zero_of_mem_halfPlane hz
  have hre := mem_halfPlane_iff.mp hz
  have hpos : (0:ℝ) < ‖z + 1 / 2‖ := norm_pos_iff.mpr h1
  rw [mem_disc_iff, cayleyInv, norm_div, div_lt_one hpos]
  have hs : ‖z - 3 / 2‖ ^ 2 < ‖z + 1 / 2‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im]
    norm_num
    nlinarith
  nlinarith [norm_nonneg (z - 3 / 2)]

lemma cayley_cayleyInv {z : ℂ} (hz : z ∈ halfPlane) : cayley (cayleyInv z) = z := by
  have h1 : z + 1 / 2 ≠ 0 := add_half_ne_zero_of_mem_halfPlane hz
  have hnum : 1 + cayleyInv z = (2 * z - 1) / (z + 1 / 2) := by
    rw [cayleyInv, eq_div_iff h1, add_mul, one_mul, div_mul_cancel₀ _ h1]
    ring
  have hden : 1 - cayleyInv z = 2 / (z + 1 / 2) := by
    rw [cayleyInv, eq_div_iff h1, sub_mul, one_mul, div_mul_cancel₀ _ h1]
    ring
  rw [cayley, hnum, hden, div_div_div_cancel_right₀]
  · ring
  · exact h1

lemma cayley_add_half {w : ℂ} (hw : w ∈ disc) : cayley w + 1 / 2 = 2 / (1 - w) := by
  have h1 : 1 - w ≠ 0 := one_sub_ne_zero_of_mem_disc hw
  rw [cayley, eq_div_iff h1, add_mul, add_mul, div_mul_cancel₀ _ h1]
  ring

lemma cayleyInv_cayley {w : ℂ} (hw : w ∈ disc) : cayleyInv (cayley w) = w := by
  have h1 : 1 - w ≠ 0 := one_sub_ne_zero_of_mem_disc hw
  have hnum : cayley w - 3 / 2 = 2 * w / (1 - w) := by
    rw [cayley, eq_div_iff h1, sub_mul, add_mul, div_mul_cancel₀ _ h1]
    ring
  rw [cayleyInv, hnum, cayley_add_half hw, div_div_div_cancel_right₀]
  · ring
  · exact h1

lemma cayleyInv_analyticAt {z : ℂ} (hz : z ∈ halfPlane) : AnalyticAt ℂ cayleyInv z := by
  have h1 : z + 1 / 2 ≠ 0 := add_half_ne_zero_of_mem_halfPlane hz
  exact ((analyticAt_id.sub analyticAt_const).div (analyticAt_id.add analyticAt_const) h1)

lemma cayley_analyticAt {w : ℂ} (hw : w ∈ disc) : AnalyticAt ℂ cayley w := by
  have h1 : 1 - w ≠ 0 := one_sub_ne_zero_of_mem_disc hw
  exact analyticAt_const.add
    ((analyticAt_const.add analyticAt_id).div (analyticAt_const.sub analyticAt_id) h1)

/-! ## The Hardy space of the half-plane -/

/-- Membership in the Hardy space `H²` of the half-plane `{re z > 1/2}`, defined by transport
along the Cayley map with the usual conformal weight `(1 - w)⁻¹`. -/
structure MemHardyHalfPlane (f : ℂ → ℂ) : Prop where
  analytic : AnalyticOnNhd ℂ f halfPlane
  transport : MemHardyDisc fun w => f (cayley w) / (1 - w)

/-! ## Inner and outer functions -/

/-- Inner function: analytic on the half-plane, of modulus `1` on the line `re z = 1/2`.

Warning: as noted in the module docstring, the boundary condition is vacuous, since the value of
`θ` at points of the boundary line is unrelated to its values on the open half-plane. -/
def IsInnerFunction (θ : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ θ halfPlane ∧ ∀ t : ℝ, ‖θ (1 / 2 + t * I)‖ = 1

/-- Outer function: analytic on the half-plane, zero-free there, with harmonic `log ‖g‖`.

Warning: as noted in the module docstring, the third clause follows from the first two, so this
predicate is equivalent to "analytic and zero-free" and is strictly weaker than the classical
notion of an outer function. -/
def IsOuterFunction (g : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ g halfPlane ∧ (∀ z ∈ halfPlane, g z ≠ 0) ∧
    ∀ z ∈ halfPlane, InnerProductSpace.HarmonicAt (fun x => Real.log ‖g x‖) z

/-- Every zero-free analytic function on the half-plane is "outer" in the requested sense. -/
lemma isOuterFunction_of_ne_zero {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g halfPlane)
    (hg0 : ∀ z ∈ halfPlane, g z ≠ 0) : IsOuterFunction g :=
  ⟨hg, hg0, fun z hz => (hg z hz).harmonicAt_log_norm (hg0 z hz)⟩

/-- The outer factor of a factorization is nowhere zero; this is part of the definition. -/
lemma outer_function_ne_zero {g : ℂ → ℂ} (hg : IsOuterFunction g) :
    ∀ z ∈ halfPlane, g z ≠ 0 := hg.2.1

/-! ## The factorization -/

/-- **Inner-outer factorization on the half-plane `{re z > 1/2}`.**

Every nonzero `f` in the Hardy space of the half-plane factors as `f = B · G` with `B` inner and
`G` outer in the requested sense.  Two genuine extra properties are recorded: `B` is bounded by
one on the half-plane (it is a transported Blaschke product), and `B` has exactly the zeros
of `f`. -/
theorem inner_outer_factorization (f : ℂ → ℂ) (hf : MemHardyHalfPlane f)
    (h0 : ∃ z ∈ halfPlane, f z ≠ 0) :
    ∃ B G : ℂ → ℂ, IsInnerFunction B ∧ IsOuterFunction G ∧
      (∀ z ∈ halfPlane, ‖B z‖ ≤ 1) ∧
      (∀ z ∈ halfPlane, (B z = 0 ↔ f z = 0)) ∧
      (∀ z ∈ halfPlane, f z = B z * G z) := by
  classical
  obtain ⟨z₀, hz₀, hfz₀⟩ := h0
  set F : ℂ → ℂ := fun w => f (cayley w) / (1 - w) with hF
  have hFmem : MemHardyDisc F := hf.transport
  have hFne : ∃ w ∈ disc, F w ≠ 0 := by
    refine ⟨cayleyInv z₀, cayleyInv_mem_disc hz₀, ?_⟩
    have h1 : 1 - cayleyInv z₀ ≠ 0 :=
      one_sub_ne_zero_of_mem_disc (cayleyInv_mem_disc hz₀)
    rw [hF]
    simp only
    rw [cayley_cayleyInv hz₀]
    exact div_ne_zero hfz₀ h1
  obtain ⟨Gd, hGdan, hGdne, hFfac⟩ := hardyDisc_inner_outer F hFmem hFne
  set Bd : ℂ → ℂ := blaschkeProduct (zeroFamily F) with hBd
  have hfam : IsBlaschkeFamily (zeroFamily F) := isBlaschkeFamily_zeroFamily F hFmem hFne
  have hBdan : AnalyticOnNhd ℂ Bd disc := blaschkeProduct_analyticOnNhd hfam
  -- the half-plane factors
  set B : ℂ → ℂ := fun z => if z ∈ halfPlane then Bd (cayleyInv z) else 1 with hB
  set G : ℂ → ℂ :=
    fun z => if z ∈ halfPlane then (1 - cayleyInv z) * Gd (cayleyInv z) else 1 with hG
  have hBval : ∀ z ∈ halfPlane, B z = Bd (cayleyInv z) := by
    intro z hz; rw [hB]; simp [hz]
  have hBout : ∀ z ∉ halfPlane, B z = 1 := by
    intro z hz; rw [hB]; simp [hz]
  have hGval : ∀ z ∈ halfPlane, G z = (1 - cayleyInv z) * Gd (cayleyInv z) := by
    intro z hz; rw [hG]; simp [hz]
  have hBan : AnalyticOnNhd ℂ B halfPlane := by
    intro z hz
    have hcomp : AnalyticAt ℂ (fun x => Bd (cayleyInv x)) z :=
      (hBdan _ (cayleyInv_mem_disc hz)).comp (cayleyInv_analyticAt hz)
    refine hcomp.congr ?_
    filter_upwards [isOpen_halfPlane.mem_nhds hz] with x hx
    exact (hBval x hx).symm
  have hGan : AnalyticOnNhd ℂ G halfPlane := by
    intro z hz
    have hcomp : AnalyticAt ℂ (fun x => (1 - cayleyInv x) * Gd (cayleyInv x)) z :=
      ((analyticAt_const.sub (cayleyInv_analyticAt hz)).mul
        ((hGdan _ (cayleyInv_mem_disc hz)).comp (cayleyInv_analyticAt hz)))
    refine hcomp.congr ?_
    filter_upwards [isOpen_halfPlane.mem_nhds hz] with x hx
    exact (hGval x hx).symm
  have hGne : ∀ z ∈ halfPlane, G z ≠ 0 := by
    intro z hz
    rw [hGval z hz]
    exact mul_ne_zero (one_sub_ne_zero_of_mem_disc (cayleyInv_mem_disc hz))
      (hGdne _ (cayleyInv_mem_disc hz))
  have hfac : ∀ z ∈ halfPlane, f z = B z * G z := by
    intro z hz
    have hw : cayleyInv z ∈ disc := cayleyInv_mem_disc hz
    have h1 : 1 - cayleyInv z ≠ 0 := one_sub_ne_zero_of_mem_disc hw
    have hFw : f z / (1 - cayleyInv z) = Bd (cayleyInv z) * Gd (cayleyInv z) := by
      have h := hFfac _ hw
      rw [hF] at h
      simp only [cayley_cayleyInv hz] at h
      exact h
    rw [div_eq_iff h1] at hFw
    rw [hBval z hz, hGval z hz, hFw]
    ring
  refine ⟨B, G, ⟨hBan, ?_⟩, isOuterFunction_of_ne_zero hGan hGne, ?_, ?_, hfac⟩
  · intro t
    have hnot : (1 / 2 + (t : ℂ) * I) ∉ halfPlane := by
      rw [mem_halfPlane_iff]
      simp
    rw [hBout _ hnot, norm_one]
  · intro z hz
    rw [hBval z hz, hBd]
    exact norm_blaschkeProduct_le_one hfam (mem_disc_iff.mp (cayleyInv_mem_disc hz))
  · intro z hz
    rw [hfac z hz]
    simp [hGne z hz]

/-! ## The correct uniqueness statement -/

/-- **Uniqueness up to a zero-free unit.**  If `f = B₁ · G₁ = B₂ · G₂` with `G₁`, `G₂` outer,
then the two inner factors differ by a zero-free analytic factor on the half-plane; in
particular they have the same zeros.  This is the statement that survives; literal uniqueness
of `B` and `G` is false, see `Hardy.inner_outer_factorization_not_unique`. -/
theorem inner_outer_unique_up_to_unit (f B₁ G₁ B₂ G₂ : ℂ → ℂ)
    (hG₁ : IsOuterFunction G₁) (hG₂ : IsOuterFunction G₂)
    (h₁ : ∀ z ∈ halfPlane, f z = B₁ z * G₁ z)
    (h₂ : ∀ z ∈ halfPlane, f z = B₂ z * G₂ z) :
    ∃ u : ℂ → ℂ, AnalyticOnNhd ℂ u halfPlane ∧ (∀ z ∈ halfPlane, u z ≠ 0) ∧
      (∀ z ∈ halfPlane, B₁ z = u z * B₂ z) ∧
      (∀ z ∈ halfPlane, (B₁ z = 0 ↔ B₂ z = 0)) := by
  refine ⟨fun z => G₂ z / G₁ z, fun z hz => (hG₂.1 z hz).div (hG₁.1 z hz) (hG₁.2.1 z hz),
    fun z hz => div_ne_zero (hG₂.2.1 z hz) (hG₁.2.1 z hz), ?_, ?_⟩
  · intro z hz
    have hne : G₁ z ≠ 0 := hG₁.2.1 z hz
    have h := (h₁ z hz).symm.trans (h₂ z hz)
    field_simp
    linear_combination h
  · intro z hz
    have hne₁ : G₁ z ≠ 0 := hG₁.2.1 z hz
    have hne₂ : G₂ z ≠ 0 := hG₂.2.1 z hz
    have h := (h₁ z hz).symm.trans (h₂ z hz)
    constructor
    · intro hb
      rw [hb, zero_mul] at h
      exact (mul_eq_zero.mp h.symm).resolve_right hne₂
    · intro hb
      rw [hb, zero_mul] at h
      exact (mul_eq_zero.mp h).resolve_right hne₁

/-! ## Failure of uniqueness -/

/-- The concrete Hardy function `z ↦ (z + 1/2)⁻¹` used to disprove uniqueness. -/
def sampleFun : ℂ → ℂ := fun z => (z + 1 / 2)⁻¹

lemma sampleFun_transport {w : ℂ} (hw : w ∈ disc) :
    sampleFun (cayley w) / (1 - w) = 1 / 2 := by
  have h1 : 1 - w ≠ 0 := one_sub_ne_zero_of_mem_disc hw
  simp only [sampleFun]
  rw [cayley_add_half hw, inv_div]
  field_simp

lemma sampleFun_memHardy : MemHardyHalfPlane sampleFun := by
  constructor
  · intro z hz
    exact (analyticAt_id.add analyticAt_const).inv (add_half_ne_zero_of_mem_halfPlane hz)
  · constructor
    · intro w hw
      have hcong : (fun w : ℂ => sampleFun (cayley w) / (1 - w)) =ᶠ[𝓝 w] fun _ => (1 : ℂ) / 2 := by
        filter_upwards [isOpen_ball.mem_nhds hw] with x hx
        exact sampleFun_transport hx
      exact analyticAt_const.congr hcong.symm
    · refine ⟨1 / 4, fun r hr0 hr1 => ?_⟩
      have hcong : Set.EqOn (fun x => ‖sampleFun (cayley x) / (1 - x)‖ ^ 2)
          (fun _ => (1 : ℝ) / 4) (sphere (0 : ℂ) |r|) := by
        intro x hx
        have hxd : x ∈ disc := sphere_subset_disc hr0 hr1 hx
        simp only
        rw [sampleFun_transport hxd]
        norm_num
      rw [Real.circleAverage_congr_sphere hcong, Real.circleAverage_const]

/-- **Uniqueness fails.**  The factorization requested in the problem statement is not unique:
already the zero-free function `z ↦ (z + 1/2)⁻¹` admits two factorizations with different inner
factors, namely `1 · f` and `e^{1/2 - z} · (e^{z - 1/2} f)`. -/
theorem inner_outer_factorization_not_unique :
    ¬ ∀ (f : ℂ → ℂ), MemHardyHalfPlane f → (∃ z ∈ halfPlane, f z ≠ 0) →
        ∀ B₁ G₁ B₂ G₂ : ℂ → ℂ,
          IsInnerFunction B₁ → IsOuterFunction G₁ →
            (∀ z ∈ halfPlane, f z = B₁ z * G₁ z) →
          IsInnerFunction B₂ → IsOuterFunction G₂ →
            (∀ z ∈ halfPlane, f z = B₂ z * G₂ z) →
          ∀ z ∈ halfPlane, B₁ z = B₂ z := by
  intro h
  classical
  have hfan : AnalyticOnNhd ℂ sampleFun halfPlane := sampleFun_memHardy.analytic
  have hfne : ∀ z ∈ halfPlane, sampleFun z ≠ 0 := fun z hz =>
    inv_ne_zero (add_half_ne_zero_of_mem_halfPlane hz)
  have hone : (1 : ℂ) ∈ halfPlane := by rw [mem_halfPlane_iff]; norm_num
  -- first factorization: trivial inner factor
  have hB₁ : IsInnerFunction (fun _ => (1 : ℂ)) :=
    ⟨fun z _ => analyticAt_const, fun t => by simp⟩
  have hG₁ : IsOuterFunction sampleFun := isOuterFunction_of_ne_zero hfan hfne
  have hfac₁ : ∀ z ∈ halfPlane, sampleFun z = (fun _ => (1 : ℂ)) z * sampleFun z := by
    intro z _; simp
  -- second factorization: multiply by the unimodular-on-the-boundary unit `exp (1/2 - z)`
  set B₂ : ℂ → ℂ := fun z => if z ∈ halfPlane then Complex.exp (1 / 2 - z) else 1 with hB₂def
  set G₂ : ℂ → ℂ :=
    fun z => if z ∈ halfPlane then sampleFun z * Complex.exp (z - 1 / 2) else 1 with hG₂def
  have hB₂val : ∀ z ∈ halfPlane, B₂ z = Complex.exp (1 / 2 - z) := by
    intro z hz; rw [hB₂def]; simp [hz]
  have hB₂out : ∀ z ∉ halfPlane, B₂ z = 1 := by
    intro z hz; rw [hB₂def]; simp [hz]
  have hG₂val : ∀ z ∈ halfPlane, G₂ z = sampleFun z * Complex.exp (z - 1 / 2) := by
    intro z hz; rw [hG₂def]; simp [hz]
  have hB₂ : IsInnerFunction B₂ := by
    constructor
    · intro z hz
      have hcomp : AnalyticAt ℂ (fun x => Complex.exp (1 / 2 - x)) z :=
        by fun_prop
      refine hcomp.congr ?_
      filter_upwards [isOpen_halfPlane.mem_nhds hz] with x hx
      exact (hB₂val x hx).symm
    · intro t
      have hnot : (1 / 2 + (t : ℂ) * I) ∉ halfPlane := by
        rw [mem_halfPlane_iff]; simp
      rw [hB₂out _ hnot, norm_one]
  have hG₂ : IsOuterFunction G₂ := by
    refine isOuterFunction_of_ne_zero ?_ ?_
    · intro z hz
      have hcomp : AnalyticAt ℂ (fun x => sampleFun x * Complex.exp (x - 1 / 2)) z :=
        (hfan z hz).mul (by fun_prop)
      refine hcomp.congr ?_
      filter_upwards [isOpen_halfPlane.mem_nhds hz] with x hx
      exact (hG₂val x hx).symm
    · intro z hz
      rw [hG₂val z hz]
      exact mul_ne_zero (hfne z hz) (Complex.exp_ne_zero _)
  have hfac₂ : ∀ z ∈ halfPlane, sampleFun z = B₂ z * G₂ z := by
    intro z hz
    rw [hB₂val z hz, hG₂val z hz]
    rw [show Complex.exp (1 / 2 - z) * (sampleFun z * Complex.exp (z - 1 / 2))
        = sampleFun z * (Complex.exp (1 / 2 - z) * Complex.exp (z - 1 / 2)) by ring,
      ← Complex.exp_add]
    norm_num
  have hcontr := h sampleFun sampleFun_memHardy ⟨1, hone, hfne 1 hone⟩
    (fun _ => (1 : ℂ)) sampleFun B₂ G₂ hB₁ hG₁ hfac₁ hB₂ hG₂ hfac₂ 1 hone
  rw [hB₂val 1 hone] at hcontr
  simp only at hcontr
  have hnorm : ‖Complex.exp (1 / 2 - (1 : ℂ))‖ = Real.exp (-(1 / 2)) := by
    rw [Complex.norm_exp]
    norm_num
  have h1 : (1 : ℝ) = Real.exp (-(1 / 2)) := by
    have hc := congrArg (fun x : ℂ => ‖x‖) hcontr
    simp only [norm_one] at hc
    rw [hnorm] at hc
    exact hc
  have : Real.exp (-(1 / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  linarith

/-!
## The originally requested statements, verbatim

For the record, this is the theorem exactly as it was requested.  It is **false** as stated
(see `Hardy.inner_outer_factorization_not_unique` for a proof that the uniqueness clause fails),
so it is kept here only as a comment.

```
/-- Inner function: analytic with modulus 1 on the boundary (Re s = 1/2) -/
def IsInnerFunction (θ : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ θ {z : ℂ | 1/2 < z.re} ∧
  ∀ t : ℝ, Complex.abs (θ (1/2 + t * I)) = 1

/-- Outer function: analytic, nonzero, log-harmonic -/
def IsOuterFunction (g : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ g {z : ℂ | 1/2 < z.re} ∧
  (∀ z : ℂ, 1/2 < z.re → g z ≠ 0) ∧
  (∃ (h : ℂ → ℝ), Harmonic ℝ h {z : ℂ | 1/2 < z.re} ∧
    ∀ z : ℂ, 1/2 < z.re → h z = Real.log (Complex.abs (g z)))

theorem inner_outer_factorization (f : H2Space) (hf : f ≠ 0) :
    ∃ (B G : ℂ → ℂ),
      IsInnerFunction B ∧
      IsOuterFunction G ∧
      (∀ z : ℂ, 1/2 < z.re → (f z : ℂ) = B z * G z) ∧
      (∀ B' G',
        IsInnerFunction B' → IsOuterFunction G' →
        (∀ z : ℂ, 1/2 < z.re → (f z : ℂ) = B' z * G' z) →
        (∀ z : ℂ, 1/2 < z.re → B z = B' z) ∧
        (∀ z : ℂ, 1/2 < z.re → G z = G' z))
```

Deviations made in the formalization above:

* `AnalyticOn` was replaced by the stronger `AnalyticOnNhd` (the two agree on open sets, and the
  half-plane is open);
* `Complex.abs x` was replaced by the current Mathlib spelling `‖x‖`;
* the clause "`log ‖g‖` is the restriction of a harmonic function" was replaced by the
  equivalent, and more directly usable, "`log ‖g‖` is harmonic at every point of the
  half-plane"; and
* the uniqueness clause was replaced by `Hardy.inner_outer_unique_up_to_unit` and refuted by
  `Hardy.inner_outer_factorization_not_unique`.
-/

end Hardy
