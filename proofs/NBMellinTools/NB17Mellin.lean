import Mathlib

/-!
# Mellin transform infrastructure: the multiplicative Haar measure and Mellin–Plancherel

This file develops the basic analytic infrastructure needed to treat the Mellin transform as a
unitary map, i.e. the *Mellin–Plancherel isometry*.

## Main definitions

* `MellinPlancherel.mulHaar` : the multiplicative Haar measure `dx / x` on `(0, ∞)`, viewed as a
  measure on `ℝ` supported on `Set.Ioi 0`.
* `MellinPlancherel.expEquivL2` : the exponential substitution `x = e^u`, as a linear isometry
  equivalence `L²((0,∞), dx/x) ≃ₗᵢ[ℂ] L²(ℝ, du)`.
* `MellinPlancherel.mellinEquivL2` : the Mellin transform on `L²((0,∞), dx/x)`, as a linear
  isometry equivalence onto `L²(ℝ, dt)`; it is the composition of `expEquivL2` with the
  `L²`-Fourier transform.

## Main statements

* `MellinPlancherel.measurePreserving_exp` / `measurePreserving_log` : `exp` and `log` intertwine
  Lebesgue measure on `ℝ` and the multiplicative Haar measure on `(0, ∞)`.
* `MellinPlancherel.norm_mellinEquivL2` and `MellinPlancherel.inner_mellinEquivL2` :
  the Mellin–Plancherel isometry (unitarity of the Mellin transform).
* `MellinPlancherel.mellin_eq_fourierIntegral` : the pointwise dictionary between the Mellin
  transform along the vertical line `Re s = σ` and the Fourier transform of the taper
  `u ↦ e^{σ u} f(e^u)`.
* `MellinPlancherel.mellin_sq_integral_eq` : the concrete Mellin–Plancherel identity
  `∫_ℝ ‖M f (2πit)‖² dt = ∫_{x>0} ‖f x‖² dx/x` for `f x = g (log x)` with `g` a Schwartz function.
-/

open MeasureTheory Set Filter Real Complex
open scoped ENNReal NNReal Topology FourierTransform RealInnerProductSpace

noncomputable section

namespace MellinPlancherel

/-! ## The multiplicative Haar measure `dx / x` on `(0, ∞)` -/

/-- The multiplicative Haar measure `dx / x` on the multiplicative group `(0, ∞)`, viewed as a
measure on `ℝ` which is supported on `Set.Ioi 0`. -/
def mulHaar : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun x => ENNReal.ofReal x⁻¹)

lemma mulHaar_apply {s : Set ℝ} (hs : MeasurableSet s) :
    mulHaar s = ∫⁻ x in s ∩ Set.Ioi 0, ENNReal.ofReal x⁻¹ := by
  rw [mulHaar, withDensity_apply _ hs, Measure.restrict_restrict hs]

/-- The exponential map pushes Lebesgue measure on `ℝ` forward to the multiplicative Haar measure
on `(0, ∞)`. -/
theorem measurePreserving_exp : MeasurePreserving Real.exp volume mulHaar := by
  refine ⟨Real.measurable_exp, ?_⟩
  ext s hs
  rw [Measure.map_apply Real.measurable_exp hs]
  have key := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
      (f := Real.exp) (f' := Real.exp) (s := univ) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn
      (fun x => ENNReal.ofReal x⁻¹ * s.indicator 1 x)
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at key
  have hR : ∀ x : ℝ, ENNReal.ofReal |Real.exp x| * (ENNReal.ofReal (Real.exp x)⁻¹ *
      s.indicator 1 (Real.exp x)) = (Real.exp ⁻¹' s).indicator 1 x := by
    intro x
    rw [abs_of_pos (Real.exp_pos x), ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos x).le,
      mul_inv_cancel₀ (Real.exp_pos x).ne', ENNReal.ofReal_one, one_mul]
    by_cases h : Real.exp x ∈ s <;> simp [h, Set.mem_preimage]
  simp_rw [hR] at key
  rw [lintegral_indicator (hs.preimage Real.measurable_exp)] at key
  simp only [Pi.one_apply, lintegral_const, one_mul, Measure.restrict_apply_univ] at key
  rw [← key, mulHaar, withDensity_apply _ hs, Measure.restrict_restrict hs]
  have hind : ∀ x : ℝ, ENNReal.ofReal x⁻¹ * s.indicator 1 x
      = s.indicator (fun a => ENNReal.ofReal a⁻¹) x := by
    intro x; by_cases h : x ∈ s <;> simp [h]
  simp_rw [hind]
  rw [lintegral_indicator hs, Measure.restrict_restrict hs]

/-- The logarithm pushes the multiplicative Haar measure on `(0, ∞)` forward to Lebesgue measure
on `ℝ`. -/
theorem measurePreserving_log : MeasurePreserving Real.log mulHaar volume := by
  refine ⟨Real.measurable_log, ?_⟩
  rw [← measurePreserving_exp.map_eq,
    Measure.map_map Real.measurable_log Real.measurable_exp]
  simp [Function.comp_def, Real.log_exp]

lemma mulHaar_Iic_zero : mulHaar (Set.Iic 0) = 0 := by
  rw [mulHaar_apply measurableSet_Iic]
  have : Set.Iic (0:ℝ) ∩ Set.Ioi 0 = ∅ := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩; linarith
  simp [this]

/-- Almost every point for `mulHaar` lies in `(0, ∞)`. -/
lemma ae_mem_Ioi_mulHaar : ∀ᵐ x ∂mulHaar, x ∈ Set.Ioi (0 : ℝ) := by
  rw [ae_iff]
  have : {x : ℝ | ¬ x ∈ Set.Ioi (0:ℝ)} = Set.Iic 0 := by
    ext x; simp
  rw [this, mulHaar_Iic_zero]

/-- `exp ∘ log` is the identity almost everywhere for `mulHaar`. -/
lemma exp_log_ae : (fun x : ℝ => Real.exp (Real.log x)) =ᵐ[mulHaar] id := by
  filter_upwards [ae_mem_Ioi_mulHaar] with x hx
  simpa using Real.exp_log hx

/-! ## Integral change of variables -/

/-- `Real.exp` is a measurable embedding. -/
theorem measurableEmbedding_exp : MeasurableEmbedding Real.exp :=
  Real.continuous_exp.measurableEmbedding Real.exp_injective

/-- Change of variables `x = e^u` for Bochner integrals. -/
theorem integral_comp_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ u : ℝ, g (Real.exp u) = ∫ x, g x ∂mulHaar :=
  measurePreserving_exp.integral_comp measurableEmbedding_exp g

/-- Change of variables `x = e^u` for lower Lebesgue integrals. -/
theorem lintegral_comp_exp (g : ℝ → ℝ≥0∞) :
    ∫⁻ u : ℝ, g (Real.exp u) = ∫⁻ x, g x ∂mulHaar :=
  measurePreserving_exp.lintegral_comp_emb measurableEmbedding_exp g

/-- Concretely, integration against `mulHaar` is integration of `g x / x` over `(0, ∞)`. -/
theorem lintegral_mulHaar {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂mulHaar = ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal x⁻¹ * g x := by
  rw [mulHaar, lintegral_withDensity_eq_lintegral_mul _
    (f := fun x : ℝ => ENNReal.ofReal x⁻¹) (by fun_prop) hg]
  rfl

/-! ## The exponential substitution as an isometry of `L²` spaces -/

/-- Composition with `exp`, as a linear isometry `L²((0,∞), dx/x) →ₗᵢ L²(ℝ, du)`. -/
def expL2 : Lp ℂ 2 mulHaar →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ ℂ Real.exp measurePreserving_exp

/-- Composition with `log`, as a linear isometry `L²(ℝ, du) →ₗᵢ L²((0,∞), dx/x)`. -/
def logL2 : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 mulHaar :=
  Lp.compMeasurePreservingₗᵢ ℂ Real.log measurePreserving_log

lemma expL2_logL2 (g : Lp ℂ 2 (volume : Measure ℝ)) : expL2 (logL2 g) = g := by
  rw [Lp.ext_iff]
  have h1 : (expL2 (logL2 g) : ℝ → ℂ) =ᵐ[volume] (logL2 g : ℝ → ℂ) ∘ Real.exp :=
    Lp.coeFn_compMeasurePreserving _ measurePreserving_exp
  have h2 : (logL2 g : ℝ → ℂ) =ᵐ[mulHaar] (g : ℝ → ℂ) ∘ Real.log :=
    Lp.coeFn_compMeasurePreserving _ measurePreserving_log
  have h3 : ((logL2 g : ℝ → ℂ)) ∘ Real.exp =ᵐ[volume] ((g : ℝ → ℂ) ∘ Real.log) ∘ Real.exp :=
    measurePreserving_exp.quasiMeasurePreserving.ae_eq_comp h2
  refine h1.trans (h3.trans ?_)
  filter_upwards with u
  simp [Function.comp_def, Real.log_exp]

/-- The exponential substitution `x = e^u`, as a linear isometry equivalence
`L²((0,∞), dx/x) ≃ₗᵢ[ℂ] L²(ℝ, du)`. -/
def expEquivL2 : Lp ℂ 2 mulHaar ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective expL2 (fun g => ⟨logL2 g, expL2_logL2 g⟩)

@[simp] lemma expEquivL2_apply (f : Lp ℂ 2 mulHaar) : expEquivL2 f = expL2 f := rfl

lemma coeFn_expEquivL2 (f : Lp ℂ 2 mulHaar) :
    (expEquivL2 f : ℝ → ℂ) =ᵐ[volume] (f : ℝ → ℂ) ∘ Real.exp :=
  Lp.coeFn_compMeasurePreserving _ measurePreserving_exp

/-! ## The Mellin–Plancherel isometry -/

/-- The Mellin transform as a unitary map `L²((0,∞), dx/x) ≃ₗᵢ[ℂ] L²(ℝ, dt)`: substitute
`x = e^u` and take the Fourier transform. -/
def mellinEquivL2 : Lp ℂ 2 mulHaar ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  expEquivL2.trans (Lp.fourierTransformₗᵢ ℝ ℂ)

/-- **Mellin–Plancherel**: the Mellin transform preserves the `L²` norm. -/
@[simp] theorem norm_mellinEquivL2 (f : Lp ℂ 2 mulHaar) : ‖mellinEquivL2 f‖ = ‖f‖ :=
  mellinEquivL2.norm_map f

/-- **Mellin–Plancherel**: the Mellin transform preserves inner products. -/
@[simp] theorem inner_mellinEquivL2 (f g : Lp ℂ 2 mulHaar) :
    inner ℂ (mellinEquivL2 f) (mellinEquivL2 g) = inner ℂ f g :=
  mellinEquivL2.inner_map_map f g

/-! ## The pointwise Mellin–Fourier dictionary -/

/-- Change of variables `x = e^u` for the multiplicative Haar integral, in `smul` form. -/
theorem integral_Ioi_inv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ x in Set.Ioi (0:ℝ), x⁻¹ • g x = ∫ u : ℝ, g (Real.exp u) := by
  have key := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (f := Real.exp) (f' := Real.exp) (s := univ) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn (fun x => x⁻¹ • g x)
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at key
  rw [key]
  congr 1
  ext u
  rw [abs_of_pos (Real.exp_pos u), smul_smul, mul_inv_cancel₀ (Real.exp_pos u).ne', one_smul]

/-- `(e^u)^s = e^{s u}` for a complex exponent. -/
theorem cpow_ofReal_exp (u : ℝ) (s : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ s = Complex.exp (s * u) := by
  rw [Complex.cpow_def_of_ne_zero (by simp), Complex.ofReal_exp,
    Complex.log_exp (by simp; positivity) (by simp; positivity)]
  ring_nf

/-- The Mellin transform written on the additive line via `x = e^u`. -/
theorem mellin_eq_integral_exp (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ u : ℝ, Complex.exp (s * u) * f (Real.exp u) := by
  rw [mellin]
  have h : ∀ x ∈ Set.Ioi (0:ℝ), (x:ℂ) ^ (s - 1) • f x = x⁻¹ • ((x:ℂ) ^ s * f x) := by
    intro x hx
    have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one, smul_eq_mul, Complex.real_smul]
    push_cast
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi h, integral_Ioi_inv_smul]
  simp_rw [cpow_ofReal_exp]

/-- **Mellin–Fourier dictionary.** The Fourier transform of the taper `u ↦ e^{σ u} f(e^u)` is the
Mellin transform of `f` along the vertical line `Re s = σ`. -/
theorem fourier_taper_eq_mellin (f : ℝ → ℂ) (σ t : ℝ) :
    𝓕 (fun u : ℝ => Real.exp (σ * u) * f (Real.exp u)) t
      = mellin f (σ - 2 * π * Complex.I * t) := by
  rw [Real.fourier_eq, mellin_eq_integral_exp]
  congr 1
  ext v
  rw [Circle.smul_def, Real.fourierChar_apply]
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The case `σ = 0` of `fourier_taper_eq_mellin`: the Mellin transform on the vertical line
through the origin is the Fourier transform of `u ↦ f(e^u)`. -/
theorem fourier_comp_exp_eq_mellin (f : ℝ → ℂ) (t : ℝ) :
    𝓕 (fun u : ℝ => f (Real.exp u)) t = mellin f (-(2 * π * Complex.I * t)) := by
  have := fourier_taper_eq_mellin f 0 t
  simpa using this

/-! ## The concrete Mellin–Plancherel identity for tapered Schwartz data -/

section Schwartz

variable (g : SchwartzMap ℝ ℂ)

/-- `x ↦ g (log x)` is square integrable for the multiplicative Haar measure. -/
theorem memLp_comp_log : MemLp (fun x : ℝ => g (Real.log x)) 2 mulHaar :=
  (g.memLp 2).comp_measurePreserving measurePreserving_log

/-- The image of `x ↦ g (log x)` under the Mellin–Plancherel unitary is the Fourier transform
of `g`. -/
theorem mellinEquivL2_comp_log :
    mellinEquivL2 ((memLp_comp_log g).toLp _) = (𝓕 g).toLp 2 := by
  have hexp : expEquivL2 ((memLp_comp_log g).toLp _) = g.toLp 2 := by
    rw [Lp.ext_iff]
    refine (coeFn_expEquivL2 _).trans ?_
    have h2 : ((memLp_comp_log g).toLp _ : ℝ → ℂ) =ᵐ[mulHaar] fun x => g (Real.log x) :=
      (memLp_comp_log g).coeFn_toLp
    have h3 := measurePreserving_exp.quasiMeasurePreserving.ae_eq_comp h2
    refine h3.trans ?_
    filter_upwards [(g.memLp 2).coeFn_toLp] with u hu
    simp only [Function.comp_apply, Real.log_exp]
    exact hu.symm
  rw [mellinEquivL2, LinearIsometryEquiv.trans_apply, hexp]
  exact SchwartzMap.toLp_fourier_eq g

/-- **Mellin–Plancherel, concrete form.** For `f x = g (log x)` with `g` a Schwartz function,
the `L²`-norm of `f` for the multiplicative Haar measure `dx/x` equals the `L²`-norm of the
Mellin transform of `f` along the vertical line through the origin. -/
theorem mellin_norm_sq_integral :
    ∫ t : ℝ, ‖mellin (fun x : ℝ => g (Real.log x)) (-(2 * π * Complex.I * t))‖ ^ 2
      = ∫ x in Set.Ioi (0:ℝ), ‖g (Real.log x)‖ ^ 2 / x := by
  have hL : ∀ t : ℝ, mellin (fun x : ℝ => g (Real.log x)) (-(2 * π * Complex.I * t))
      = 𝓕 (g : ℝ → ℂ) t := by
    intro t
    rw [← fourier_comp_exp_eq_mellin]
    simp only [Real.log_exp]
  simp_rw [hL]
  have hR : ∀ x : ℝ, ‖g (Real.log x)‖ ^ 2 / x = x⁻¹ • ‖g (Real.log x)‖ ^ 2 := by
    intro x; rw [smul_eq_mul]; ring
  simp_rw [hR]
  rw [integral_Ioi_inv_smul (fun x : ℝ => ‖g (Real.log x)‖ ^ 2)]
  simp only [Real.log_exp]
  rw [← SchwartzMap.fourier_coe]
  exact SchwartzMap.integral_norm_sq_fourier g

end Schwartz

/-! ## Identifying the `L²`-Fourier transform with the Fourier integral on `L¹ ∩ L²` -/

/-- The multiplication formula `∫ (𝓕 f) • g = ∫ f • (𝓕 g)` for integrable functions on `ℝ`. -/
theorem integral_fourier_smul_eq_of_integrable {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    ∫ t : ℝ, (𝓕 f t) • g t = ∫ x : ℝ, f x • (𝓕 g x) := by
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ)) (f := f) (g := g)
    Real.continuous_fourierChar (by fun_prop) hf hg
  simpa using this

/-- If an `L²` function on `ℝ` also has an integrable representative, then its `L²`-Fourier
transform is almost everywhere given by the Fourier integral. -/
theorem coeFn_fourier_Lp (F : Lp ℂ 2 (volume : Measure ℝ)) {f : ℝ → ℂ}
    (hf : Integrable f) (hFf : (F : ℝ → ℂ) =ᵐ[volume] f) :
    ((𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  have hlocL : LocallyIntegrable ((𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hf
  refine ae_eq_of_integral_contDiff_smul_eq hlocL hcont.locallyIntegrable ?_
  intro g hg hgc
  set Φ : SchwartzMap ℝ ℂ :=
    (hgc.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg) with hΦ
  have hΦval : ∀ x, Φ x = (g x : ℂ) := fun _ => rfl
  have h1 : ∫ x : ℝ, Φ x • (𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) x
      = ∫ x : ℝ, (𝓕 Φ) x • (F : ℝ → ℂ) x := by
    rw [← MeasureTheory.Lp.toTemperedDistribution_apply,
      ← MeasureTheory.Lp.toTemperedDistribution_apply,
      ← MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
    rfl
  have h2 : ∫ x : ℝ, (𝓕 Φ) x • (F : ℝ → ℂ) x = ∫ x : ℝ, (𝓕 Φ) x • f x := by
    refine integral_congr_ae ?_
    filter_upwards [hFf] with x hx
    rw [hx]
  have h3 : ∫ x : ℝ, (𝓕 (Φ : ℝ → ℂ)) x • f x = ∫ t : ℝ, (𝓕 f t) • Φ t := by
    rw [integral_fourier_smul_eq_of_integrable hf Φ.integrable]
    simp [smul_eq_mul, mul_comm]
  have hcoe : ∀ x, (𝓕 Φ) x = (𝓕 (Φ : ℝ → ℂ)) x := fun x => by rw [SchwartzMap.fourier_coe]
  calc ∫ x : ℝ, g x • ((𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
      = ∫ x : ℝ, Φ x • ((𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x := by
        simp [hΦval, Complex.real_smul]
    _ = ∫ x : ℝ, (𝓕 Φ) x • (F : ℝ → ℂ) x := h1
    _ = ∫ x : ℝ, (𝓕 Φ) x • f x := h2
    _ = ∫ t : ℝ, (𝓕 f t) • Φ t := by simp_rw [hcoe]; exact h3
    _ = ∫ x : ℝ, g x • 𝓕 f x := by simp [hΦval, Complex.real_smul, smul_eq_mul, mul_comm]

/-! ## Concrete form of the Mellin–Plancherel unitary -/

/-- For `f` in `L¹(dx/x) ∩ L²(dx/x)`, the Mellin–Plancherel unitary is given almost everywhere by
the absolutely convergent Mellin integral on the vertical line through the origin. -/
theorem coeFn_mellinEquivL2 {f : ℝ → ℂ} (h1 : Integrable f mulHaar) (h2 : MemLp f 2 mulHaar) :
    (mellinEquivL2 (h2.toLp f) : ℝ → ℂ)
      =ᵐ[volume] fun t : ℝ => mellin f (-(2 * π * Complex.I * t)) := by
  have hG : Integrable (fun u : ℝ => f (Real.exp u)) volume :=
    measurePreserving_exp.integrable_comp_of_integrable h1
  have hae : (expEquivL2 (h2.toLp f) : ℝ → ℂ) =ᵐ[volume] fun u : ℝ => f (Real.exp u) := by
    refine (coeFn_expEquivL2 _).trans ?_
    exact measurePreserving_exp.quasiMeasurePreserving.ae_eq_comp h2.coeFn_toLp
  have hfour := coeFn_fourier_Lp (expEquivL2 (h2.toLp f)) hG hae
  filter_upwards [hfour] with t ht
  rw [show mellinEquivL2 (h2.toLp f)
      = (𝓕 (expEquivL2 (h2.toLp f)) : Lp ℂ 2 (volume : Measure ℝ)) from rfl, ht,
    fourier_comp_exp_eq_mellin]

/-- The squared `L²` norm of an `L²` element is the integral of the squared pointwise norm. -/
theorem norm_sq_Lp {α : Type*} [MeasurableSpace α] {μ : Measure α} (F : Lp ℂ 2 μ) :
    ‖F‖ ^ 2 = ∫ x, ‖(F : α → ℂ) x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ _ _ _ _ F, MeasureTheory.L2.inner_def]
  have h : ∀ a : α, (inner ℂ ((F : α → ℂ) a) ((F : α → ℂ) a)) = ((‖(F : α → ℂ) a‖ ^ 2 : ℝ) : ℂ) := by
    intro a; rw [inner_self_eq_norm_sq_to_K]; norm_num
  simp_rw [h]
  rw [show (∫ a, ((‖(F : α → ℂ) a‖ ^ 2 : ℝ) : ℂ) ∂μ) = ((∫ a, ‖(F : α → ℂ) a‖ ^ 2 ∂μ : ℝ) : ℂ)
    from integral_ofReal]
  simp

/-- **Mellin–Plancherel theorem.** For `f` in `L¹(dx/x) ∩ L²(dx/x)`, the `L²` norm of `f` for the
multiplicative Haar measure equals the `L²` norm of its Mellin transform along the vertical line
through the origin. -/
theorem mellin_plancherel {f : ℝ → ℂ} (h1 : Integrable f mulHaar) (h2 : MemLp f 2 mulHaar) :
    ∫ t : ℝ, ‖mellin f (-(2 * π * Complex.I * t))‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂mulHaar := by
  have hnorm : ‖mellinEquivL2 (h2.toLp f)‖ ^ 2 = ‖h2.toLp f‖ ^ 2 := by
    rw [norm_mellinEquivL2]
  rw [norm_sq_Lp, norm_sq_Lp] at hnorm
  have hL : ∫ t : ℝ, ‖mellin f (-(2 * π * Complex.I * t))‖ ^ 2
      = ∫ t : ℝ, ‖(mellinEquivL2 (h2.toLp f) : ℝ → ℂ) t‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_mellinEquivL2 h1 h2] with t ht
    rw [ht]
  have hR : ∫ x, ‖(h2.toLp f : ℝ → ℂ) x‖ ^ 2 ∂mulHaar = ∫ x, ‖f x‖ ^ 2 ∂mulHaar := by
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  rw [hL, hnorm, hR]

/-- **Mellin–Plancherel theorem**, written with the explicit multiplicative Haar integral
`∫_{x>0} ‖f x‖² dx/x`. -/
theorem mellin_plancherel_Ioi {f : ℝ → ℂ} (h1 : Integrable f mulHaar) (h2 : MemLp f 2 mulHaar) :
    ∫ t : ℝ, ‖mellin f (-(2 * π * Complex.I * t))‖ ^ 2
      = ∫ x in Set.Ioi (0:ℝ), ‖f x‖ ^ 2 / x := by
  rw [mellin_plancherel h1 h2, ← integral_comp_exp (fun x : ℝ => ‖f x‖ ^ 2),
    ← integral_Ioi_inv_smul (fun x : ℝ => ‖f x‖ ^ 2)]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x _
  simp only [smul_eq_mul]
  ring

end MellinPlancherel
