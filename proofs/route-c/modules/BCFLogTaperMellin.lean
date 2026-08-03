import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaper
import RiemannHypothesis.Criteria.NymanBeurling.NBChiMellin
import NBMellinTools.BaezDuarteTail
import NBMellinTools.FourierCompatibility
import Mathlib.Analysis.MellinInversion

/-!
# Mellin transform of the BCF logarithmic-taper residual

This file proves the finite, pointwise part of the Mellin bridge for the
Bettin--Conrey--Farey logarithmic taper.  If

`V_N(s) = Σ_{n ≤ N} μ(n) (1 - log n / log N) n^{-s}`,

then the Nyman--Beurling residual has the exact Mellin transform

`M(χ - A_N)(s) = (1 - ζ(s) V_N(s)) / s`

throughout `0 < Re(s) < 1`.  This is an unconditional finite calculation:
the integrability needed to exchange the finite sum and the Mellin integral is
proved below.

The subsequent equality of the *integrals of squares* on the positive half
line and on the critical line is deliberately kept in a separate module.  It
requires the currently absent `L¹ ∩ L²` function-level compatibility theorem
between Mathlib's Fourier integral and its `Lp` Fourier transform.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperMellin

open scoped BigOperators FourierTransform
open MeasureTheory Set Complex
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Certificates

/-- The BCF residual on the positive half-line. -/
noncomputable def residual (N : ℕ) (x : ℝ) : ℝ :=
  chi01 x - approximant N x

/-- Coefficient of the exact reciprocal tail of the finite BCF residual. -/
noncomputable def tailCoefficient (N : ℕ) : ℝ :=
  ∑ k : Fin N, coefficientFamily.coeff N k / (k.val + 1 : ℝ)

private theorem measurable_chi01 : Measurable chi01 := by
  unfold chi01
  exact Measurable.ite measurableSet_Ioc measurable_const measurable_const

private theorem measurable_bdApprox (N : ℕ) (coeffs : Fin N → ℝ) :
    Measurable (bdApprox N coeffs) := by
  unfold bdApprox
  exact Finset.measurable_sum _ (fun k _ =>
    measurable_const.mul (by
      unfold rhoBD
      measurability))

private theorem measurable_approximant (N : ℕ) : Measurable (approximant N) := by
  unfold approximant
  exact measurable_bdApprox N (coefficientFamily.coeff N)

private theorem measurable_residual (N : ℕ) : Measurable (residual N) := by
  unfold residual
  exact measurable_chi01.sub (measurable_approximant N)

private theorem residual_eq_tail_on_Ioi (N : ℕ) {x : ℝ} (hx : 1 < x) :
    residual N x = -tailCoefficient N / x := by
  change chi01 x - bdApprox N (coefficientFamily.coeff N) x = _
  simpa only [tailCoefficient] using
    NBMellinTools.chi_sub_bdApprox_eq_tail_of_one_lt N
      (coefficientFamily.coeff N) hx

private theorem norm_rhoBD_le_one (k : ℕ) (x : ℝ) : ‖rhoBD k x‖ ≤ 1 := by
  unfold rhoBD
  rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

private theorem norm_approximant_le (N : ℕ) (x : ℝ) :
    ‖approximant N x‖ ≤ ∑ k : Fin N, ‖coefficientFamily.coeff N k‖ := by
  unfold approximant bdApprox
  calc
    ‖∑ k, coefficientFamily.coeff N k * rhoBD k.val x‖ ≤
        ∑ k, ‖coefficientFamily.coeff N k * rhoBD k.val x‖ := norm_sum_le _ _
    _ = ∑ k, ‖coefficientFamily.coeff N k‖ * ‖rhoBD k.val x‖ := by
      simp only [norm_mul]
    _ ≤ ∑ k, ‖coefficientFamily.coeff N k‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_of_le_one_right (norm_nonneg _)
        (norm_rhoBD_le_one k.val x)

private theorem norm_residual_le (N : ℕ) (x : ℝ) :
    ‖(residual N x : ℂ)‖ ≤ 1 + ∑ k : Fin N, ‖coefficientFamily.coeff N k‖ := by
  unfold residual
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    |chi01 x - approximant N x| ≤ |chi01 x| + |approximant N x| := abs_sub _ _
    _ = ‖chi01 x‖ + ‖approximant N x‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 + ∑ k : Fin N, ‖coefficientFamily.coeff N k‖ := by
      gcongr
      · unfold chi01
        split_ifs <;> norm_num
      · exact norm_approximant_le N x

/-- The Mellin kernel, named to keep the finite integrability arguments legible. -/
private noncomputable def mellinKernel (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1)

private noncomputable def rhoMellinIntegrand (k : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  mellinKernel s x * ((rhoBD k x : ℝ) : ℂ)

private theorem measurable_rhoBD (k : ℕ) : Measurable (rhoBD k) := by
  unfold rhoBD
  measurability

private theorem rhoBD_eq_inv_on_Ioi (k : ℕ) {x : ℝ} (hx : 1 < x) :
    rhoBD k x = 1 / (((k : ℝ) + 1) * x) := by
  unfold rhoBD
  rw [Int.fract_eq_self.mpr]
  constructor
  · positivity
  · have hden : (1 : ℝ) < ((k : ℝ) + 1) * x := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have ha : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
      calc
        (1 : ℝ) < 1 * x := by nlinarith
        _ ≤ ((k : ℝ) + 1) * x :=
          mul_le_mul_of_nonneg_right ha
            (le_of_lt (lt_trans zero_lt_one hx))
    have hfrac : (1 : ℝ) / (((k : ℝ) + 1) * x) < 1 := by
      apply (div_lt_iff₀ (by positivity :
        (0 : ℝ) < ((k : ℝ) + 1) * x)).2
      simpa only [one_mul] using hden
    exact hfrac

private theorem rho_mellin_integrableOn_Ioc01
    {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    IntegrableOn (rhoMellinIntegrand k s) (Ioc (0 : ℝ) 1) := by
  have hk := intervalIntegral.intervalIntegrable_cpow'
    (r := s - 1) (a := (0 : ℝ)) (b := 1) (by
      rw [Complex.sub_re, Complex.one_re]
      linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hk
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => ((rhoBD k x : ℝ) : ℂ))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (measurable_rhoBD k).complex_ofReal.aestronglyMeasurable.restrict
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖((rhoBD k x : ℝ) : ℂ)‖ ≤ (1 : ℝ) := by
    filter_upwards with x
    unfold rhoBD
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have hnon : 0 ≤ Int.fract (1 / (((k : ℝ) + 1) * x)) := Int.fract_nonneg _
    rw [abs_of_nonneg hnon]
    exact (Int.fract_lt_one _).le
  have hmul := hk.mul_bdd hmeas hbound
  simpa [rhoMellinIntegrand, mellinKernel, smul_eq_mul] using hmul

private theorem rho_mellin_integrableOn_Ioi
    {s : ℂ} (hs : s.re < 1) (k : ℕ) :
    IntegrableOn (rhoMellinIntegrand k s) (Ioi (1 : ℝ)) := by
  have hcpow : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s - 2)) (Ioi (1 : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt
    · change s.re - 2 < -1
      linarith
    · exact one_pos
  have ha : (0 : ℂ) ≠ (((k : ℝ) + 1 : ℝ) : ℂ) := by
    intro h
    have h' : ((k : ℝ) + 1) = 0 := by exact_mod_cast h
    have hpos : 0 < ((k : ℝ) + 1) := by positivity
    linarith
  have hmodel : IntegrableOn
      (fun x : ℝ => (((k : ℝ) + 1 : ℝ) : ℂ)⁻¹ * (x : ℂ) ^ (s - 2))
      (Ioi (1 : ℝ)) := by
    exact hcpow.const_mul _
  apply hmodel.congr_fun _ measurableSet_Ioi
  intro x hx
  have hx0 : (x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hx))
  dsimp [rhoMellinIntegrand, mellinKernel]
  rw [rhoBD_eq_inv_on_Ioi k hx]
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  rw [show s - 2 = (s - 1) - 1 by ring,
    Complex.cpow_sub (s - 1) 1 hx0, Complex.cpow_one]
  field_simp
  simp

private theorem rho_mellin_integrableOn_Ioi_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (k : ℕ) :
    IntegrableOn (rhoMellinIntegrand k s) (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (rho_mellin_integrableOn_Ioc01 hs0 k).union
    (rho_mellin_integrableOn_Ioi hs1 k)

private theorem bdApprox_mellin_integrableOn
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    IntegrableOn
      (fun x : ℝ => mellinKernel s x * ((bdApprox N coeffs x : ℝ) : ℂ))
      (Ioi (0 : ℝ)) := by
  have hsum : IntegrableOn
      (fun x : ℝ => ∑ k : Fin N,
        mellinKernel s x * (coeffs k : ℂ) * (rhoBD k.val x : ℂ))
      (Ioi (0 : ℝ)) := by
    apply MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin N))
    intro k hk
    have h := rho_mellin_integrableOn_Ioi_zero hs0 hs1 k.val
    simpa [mellinKernel, rhoMellinIntegrand, smul_eq_mul, mul_assoc,
      mul_left_comm, mul_comm] using h.const_mul (coeffs k : ℂ)
  apply hsum.congr_fun _ measurableSet_Ioi
  intro x hx
  unfold bdApprox
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem chi_mellin_integrableOn
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun x : ℝ => mellinKernel s x * ((chi01 x : ℝ) : ℂ))
      (Ioi (0 : ℝ)) := by
  have hk := intervalIntegral.intervalIntegrable_cpow'
    (r := s - 1) (a := (0 : ℝ)) (b := 1) (by
      rw [Complex.sub_re, Complex.one_re]
      linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hk
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  have hlocal : IntegrableOn
      (fun x : ℝ => mellinKernel s x * ((chi01 x : ℝ) : ℂ))
      (Ioc (0 : ℝ) 1) := by
    apply hk.congr_fun _ measurableSet_Ioc
    intro x hx
    have hchi : chi01 x = 1 := by
      simp [chi01, hx.1, hx.2]
    simp [mellinKernel, hchi]
  have htail : IntegrableOn
      (fun x : ℝ => mellinKernel s x * ((chi01 x : ℝ) : ℂ))
      (Ioi (1 : ℝ)) := by
    apply integrableOn_zero.congr_fun _ measurableSet_Ioi
    intro x hx
    have hx' : 1 < x := hx
    have hchi : chi01 x = 0 := by
      simp [chi01, not_le_of_gt hx']
    simp [hchi]
  exact hlocal.union htail

private theorem mellin_sub_chi_bdApprox
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    mellin (fun x : ℝ => ((chi01 x - bdApprox N coeffs x : ℝ) : ℂ)) s =
      mellin (fun x : ℝ => (chi01 x : ℂ)) s -
        mellin (fun x : ℝ => (bdApprox N coeffs x : ℂ)) s := by
  have hchi := chi_mellin_integrableOn (s := s) hs0
  have hbd := bdApprox_mellin_integrableOn hs0 hs1 N coeffs
  unfold mellin
  simp only [smul_eq_mul]
  have hsub := MeasureTheory.integral_sub hchi hbd
  change (∫ x in Ioi (0 : ℝ), mellinKernel s x *
      (((chi01 x - bdApprox N coeffs x : ℝ) : ℂ))) =
    (∫ x in Ioi (0 : ℝ), mellinKernel s x * ((chi01 x : ℝ) : ℂ)) -
      ∫ x in Ioi (0 : ℝ), mellinKernel s x *
        ((bdApprox N coeffs x : ℝ) : ℂ)
  have hfun :
      (fun x : ℝ => mellinKernel s x *
        (((chi01 x - bdApprox N coeffs x : ℝ) : ℂ))) =
      (fun x : ℝ => mellinKernel s x * ((chi01 x : ℝ) : ℂ) -
        mellinKernel s x * ((bdApprox N coeffs x : ℝ) : ℂ)) := by
    funext x
    rw [Complex.ofReal_sub]
    ring
  rw [hfun]
  exact hsub

/-- Reindex the one-based interval used by `dirichletPolynomial` by `Fin N`. -/
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

/-- Mellin transform of a finite Báez--Duarte approximation. -/
theorem mellin_bdApprox_eq_sum
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsne : s ≠ 0)
    (N : ℕ) (coeffs : Fin N → ℝ) :
    mellin (fun x : ℝ => (bdApprox N coeffs x : ℂ)) s =
      ∑ i : Fin N,
        (coeffs i : ℂ) *
          (-(riemannZeta s) / (s * ((i.val + 1 : ℕ) : ℂ) ^ s)) := by
  unfold mellin bdApprox
  rw [show (fun x : ℝ => (x : ℂ) ^ (s - 1) •
      (↑(∑ k, coeffs k * rhoBD k.val x) : ℂ)) =
      (fun x : ℝ => ∑ k : Fin N,
        (x : ℂ) ^ (s - 1) * (coeffs k : ℂ) *
          (rhoBD k.val x : ℂ)) by
        funext x
        push_cast
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [show (fun x : ℝ => (x : ℂ) ^ (s - 1) *
        (coeffs k : ℂ) * (rhoBD k.val x : ℂ)) =
        (fun x : ℝ => (coeffs k : ℂ) *
          ((x : ℂ) ^ (s - 1) * (rhoBD k.val x : ℂ))) by
          funext x
          ring]
    rw [MeasureTheory.integral_const_mul]
    rw [show (∫ x in Ioi (0 : ℝ),
        (x : ℂ) ^ (s - 1) * (rhoBD k.val x : ℂ)) =
        mellin (fun x : ℝ => (rhoBD k.val x : ℂ)) s by rfl]
    rw [mellin_generator_eval_proved k.val s hs0 hs1 hsne]
  · intro k hk
    have h := rho_mellin_integrableOn_Ioi_zero hs0 hs1 k.val
    simpa [rhoMellinIntegrand, mellinKernel, smul_eq_mul,
      mul_assoc, mul_left_comm, mul_comm] using h.const_mul (coeffs k : ℂ)

/-- Mellin transform of the BCF approximant. -/
theorem mellin_approximant_eq
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsne : s ≠ 0) (N : ℕ) :
    mellin (fun x : ℝ => (approximant N x : ℂ)) s =
      riemannZeta s * dirichletPolynomial N s / s := by
  rw [show (fun x : ℝ => (approximant N x : ℂ)) =
      (fun x : ℝ => (bdApprox N (coefficientFamily.coeff N) x : ℂ)) by rfl,
    mellin_bdApprox_eq_sum hs0 hs1 hsne]
  unfold dirichletPolynomial coefficientFamily
  rw [sum_Icc_one_eq_sum_fin]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : 0 < i.val + 1 := by omega
  have hinpos : ((i.val + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hin)
  have hnpow : (((i.val + 1 : ℕ) : ℂ) ^ (-s)) =
      ((((i.val + 1 : ℕ) : ℂ) ^ s)⁻¹) := by
    rw [Complex.cpow_neg]
  rw [hnpow]
  field_simp
  push_cast
  ring

/-- The exact BCF Mellin numerator identity on the critical strip. -/
theorem mellin_residual_eq
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsne : s ≠ 0) (N : ℕ) :
    mellin (fun x : ℝ => (residual N x : ℂ)) s =
      (1 - riemannZeta s * dirichletPolynomial N s) / s := by
  unfold residual approximant
  rw [mellin_sub_chi_bdApprox hs0 hs1 N (coefficientFamily.coeff N),
    mellin_chi01_eq hs0,
    show mellin (fun x : ℝ =>
      (bdApprox N (coefficientFamily.coeff N) x : ℂ)) s =
        mellin (fun x : ℝ => (approximant N x : ℂ)) s by rfl,
    mellin_approximant_eq hs0 hs1 hsne N]
  field_simp

/-- The logarithmic pullback which turns Mellin transform on the critical line
into the ordinary Fourier transform. -/
noncomputable def mellinLogPullback (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  Real.exp (-u / 2) • f (Real.exp (-u))

/-! ## The logarithmic coordinate isometry

The map `u ↦ exp (-u)` takes Lebesgue measure to `x⁻¹ dx` on the
positive half-line.  The half-density in `mellinLogPullback` supplies the
remaining factor, so that this is an exact `L²` coordinate change.  This
part does not use Fourier analysis. -/

private theorem rexp_neg_deriv :
    ∀ u ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-u)) univ u :=
  fun u _ ↦ mul_neg_one (Real.exp (-u)) ▸
    ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt

private theorem rexp_neg_image :
    (Real.exp ∘ Neg.neg) '' (univ : Set ℝ) = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
    Set.image_univ, Real.range_exp]

private theorem rexp_neg_injOn : (univ : Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

/-- Squared norm is preserved by the Mellin logarithmic coordinate change. -/
theorem integral_sq_norm_mellinLogPullback (f : ℝ → ℂ) :
    (∫ u : ℝ, ‖mellinLogPullback f u‖ ^ 2) =
      ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 := by
  calc
    (∫ u : ℝ, ‖mellinLogPullback f u‖ ^ 2) =
        ∫ u : ℝ, Real.exp (-u) * ‖f (Real.exp (-u))‖ ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      unfold mellinLogPullback
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
      have hexp : Real.exp (-u / 2) ^ 2 = Real.exp (-u) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [hexp]
    _ = ∫ x in (Real.exp ∘ Neg.neg) '' (univ : Set ℝ), ‖f x‖ ^ 2 := by
      rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul
        MeasurableSet.univ rexp_neg_deriv rexp_neg_injOn]
      simp only [Measure.restrict_univ]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      simp only [Function.comp_apply, abs_neg,
        abs_of_pos (Real.exp_pos _), smul_eq_mul]
    _ = ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 := by rw [rexp_neg_image]

/-- The logarithmic Mellin coordinate change transports `L²` membership from
the positive half-line to the ordinary Fourier line.  Measurability is kept
explicit here; this avoids concealing the only non-algebraic part of the
coordinate transport in the later Plancherel argument. -/
theorem mellinLogPullback_memLp_two_of_measurable
    (f : ℝ → ℂ) (hfmeas : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (mellinLogPullback f) 2 volume := by
  have hpullback_meas : Measurable (mellinLogPullback f) := by
    unfold mellinLogPullback
    apply Measurable.smul
    · exact (Real.continuous_exp.comp
        (continuous_neg.div_const 2)).measurable
    · exact hfmeas.comp
        (Real.continuous_exp.comp continuous_neg).measurable
  apply (memLp_two_iff_integrable_sq_norm
    hpullback_meas.aestronglyMeasurable).2
  have hsource : Integrable (fun x : ℝ => ‖f x‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hf.integrable_norm_pow (by norm_num)
  have himage : IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2)
      ((Real.exp ∘ Neg.neg) '' (univ : Set ℝ)) := by
    simpa only [rexp_neg_image] using hsource
  have hcoordinateOn :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexp_neg_deriv rexp_neg_injOn
      (fun x : ℝ => ‖f x‖ ^ 2)).mp himage
  have hcoordinate : Integrable
      (fun u : ℝ => Real.exp (-u) * ‖f (Real.exp (-u))‖ ^ 2) := by
    rw [integrableOn_univ] at hcoordinateOn
    simpa only [Function.comp_apply, abs_neg,
      abs_of_pos (Real.exp_pos _), smul_eq_mul] using hcoordinateOn
  apply hcoordinate.congr
  filter_upwards with u
  unfold mellinLogPullback
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  have hexp : Real.exp (-u / 2) ^ 2 = Real.exp (-u) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]

/-- The standard point `1/2 + it` on the critical line. -/
noncomputable def criticalLinePoint (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)

theorem criticalLinePoint_re (t : ℝ) : (criticalLinePoint t).re = 1 / 2 := by
  simp [criticalLinePoint]

theorem criticalLinePoint_ne_zero (t : ℝ) : criticalLinePoint t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [criticalLinePoint] at this

/-- The exact residual transform on the critical line. -/
theorem mellin_residual_criticalLine (N : ℕ) (t : ℝ) :
    mellin (fun x : ℝ => (residual N x : ℂ)) (criticalLinePoint t) =
      (1 - riemannZeta (criticalLinePoint t) *
          dirichletPolynomial N (criticalLinePoint t)) / criticalLinePoint t := by
  apply mellin_residual_eq
  · rw [criticalLinePoint_re]
    norm_num
  · rw [criticalLinePoint_re]
    norm_num
  · exact criticalLinePoint_ne_zero t

/-- Logarithmic pullback of the BCF residual.  This is the function to which
ordinary Fourier Plancherel applies. -/
noncomputable def criticalLogPullback (N : ℕ) (u : ℝ) : ℂ :=
  Real.exp (-u / 2) • (residual N (Real.exp (-u)) : ℂ)

theorem criticalLogPullback_eq_mellinLogPullback (N : ℕ) :
    criticalLogPullback N =
      mellinLogPullback (fun x : ℝ => (residual N x : ℂ)) := rfl

private theorem criticalLogPullback_measurable (N : ℕ) :
    Measurable (criticalLogPullback N) := by
  unfold criticalLogPullback
  apply Measurable.smul
  · exact (Real.continuous_exp.comp
      (continuous_neg.div_const 2)).measurable
  · exact ((measurable_residual N).comp
      (Real.continuous_exp.comp continuous_neg).measurable).complex_ofReal

private theorem criticalLogPullback_integrableOn_Iio (N : ℕ) :
    IntegrableOn (criticalLogPullback N) (Iio (0 : ℝ)) := by
  have hbase : IntegrableOn (fun u : ℝ => Real.exp ((1 / 2 : ℝ) * u))
      (Iic (0 : ℝ)) :=
    integrableOn_exp_mul_Iic (by norm_num) 0
  have hbase' : IntegrableOn (fun u : ℝ => Real.exp ((1 / 2 : ℝ) * u))
      (Iio (0 : ℝ)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).mp hbase
  have hmodel : IntegrableOn
      (fun u : ℝ => |tailCoefficient N| * Real.exp ((1 / 2 : ℝ) * u))
      (Iio (0 : ℝ)) := by
    exact hbase'.const_mul _
  apply Integrable.mono' hmodel
    (criticalLogPullback_measurable N).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
  have hu' : u < 0 := hu
  have hx : 1 < Real.exp (-u) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  unfold criticalLogPullback
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    residual_eq_tail_on_Ioi N hx, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_neg, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-u / 2) * (|tailCoefficient N| / Real.exp (-u)) =
        |tailCoefficient N| *
          (Real.exp (-u / 2) / Real.exp (-u)) := by ring
    _ = |tailCoefficient N| * Real.exp ((1 / 2 : ℝ) * u) := by
      rw [← Real.exp_sub]
      congr 2
      ring
    _ ≤ |tailCoefficient N| * Real.exp ((1 / 2 : ℝ) * u) := le_rfl

private theorem criticalLogPullback_integrableOn_Ici (N : ℕ) :
    IntegrableOn (criticalLogPullback N) (Ici (0 : ℝ)) := by
  have hbase : IntegrableOn (fun u : ℝ => Real.exp ((-1 / 2 : ℝ) * u))
      (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  have hbase' : IntegrableOn (fun u : ℝ => Real.exp ((-1 / 2 : ℝ) * u))
      (Ici (0 : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hbase
  have hmodel : IntegrableOn
      (fun u : ℝ =>
        (1 + ∑ k : Fin N, ‖coefficientFamily.coeff N k‖) *
          Real.exp ((-1 / 2 : ℝ) * u))
      (Ici (0 : ℝ)) := by
    exact hbase'.const_mul _
  apply Integrable.mono' hmodel
    (criticalLogPullback_measurable N).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  unfold criticalLogPullback
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-u / 2) * ‖(residual N (Real.exp (-u)) : ℂ)‖ ≤
        Real.exp (-u / 2) *
          (1 + ∑ k : Fin N, ‖coefficientFamily.coeff N k‖) :=
      mul_le_mul_of_nonneg_left (norm_residual_le N _) (Real.exp_pos _).le
    _ = (1 + ∑ k : Fin N, ‖coefficientFamily.coeff N k‖) *
          Real.exp ((-1 / 2 : ℝ) * u) := by
      have hexp : Real.exp (-u / 2) = Real.exp ((-1 / 2 : ℝ) * u) := by
        congr 1
        ring
      rw [hexp]
      ring

/-- The BCF logarithmic pullback is integrable on the Fourier line.  The proof
uses boundedness near zero and the exact reciprocal tail beyond one. -/
theorem criticalLogPullback_integrable (N : ℕ) : Integrable (criticalLogPullback N) := by
  simpa only [Iio_union_Ici, IntegrableOn, Measure.restrict_univ] using
    (criticalLogPullback_integrableOn_Iio N).union
      (criticalLogPullback_integrableOn_Ici N)

theorem criticalLinePoint_im (t : ℝ) : (criticalLinePoint t).im = t := by
  simp [criticalLinePoint]

/-- On the critical line the Mellin transform is the Fourier transform of the
logarithmic pullback.  This is independent of the BCF residual. -/
theorem mellin_criticalLine_eq_fourier_mellinLogPullback
    (f : ℝ → ℂ) (t : ℝ) :
    mellin f (criticalLinePoint t) =
      𝓕 (mellinLogPullback f) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier, criticalLinePoint_re, criticalLinePoint_im]
  apply congrArg (fun g : ℝ → ℂ => 𝓕 g (t / (2 * Real.pi)))
  funext u
  unfold mellinLogPullback
  congr 1
  ring_nf

/-- The Mellin--Plancherel identity on the positive half-line for a measurable
representative whose logarithmic pullback is both `L¹` and `L²`.

The explicit measurability and `L¹` hypotheses are needed because `mellin` is
a pointwise integral, whereas a bare `L²` class has no canonical pointwise
representative. -/
theorem mellin_plancherel_positive_half_line_of_measurable
    (f : ℝ → ℂ) (hfmeas : Measurable f)
    (hf2 : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))))
    (hlog : Integrable (mellinLogPullback f)) :
    (∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2) =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖mellin f (criticalLinePoint t)‖ ^ 2 := by
  have hpullback : MemLp (mellinLogPullback f) 2 volume :=
    mellinLogPullback_memLp_two_of_measurable f hfmeas hf2
  calc
    (∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2) =
        ∫ u : ℝ, ‖mellinLogPullback f u‖ ^ 2 :=
      (integral_sq_norm_mellinLogPullback f).symm
    _ = ∫ ξ : ℝ, ‖𝓕 (mellinLogPullback f) ξ‖ ^ 2 :=
      (NBMellinTools.integral_sq_norm_fourier_eq_integral_sq_norm
        (mellinLogPullback f) hlog hpullback).symm
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖𝓕 (mellinLogPullback f) (t / (2 * Real.pi))‖ ^ 2 :=
      (NBMellinTools.criticalLineFrequencyEnergy_eq_fourierNormSq
        (mellinLogPullback f)).symm
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖mellin f (criticalLinePoint t)‖ ^ 2 := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      rw [mellin_criticalLine_eq_fourier_mellinLogPullback]

/-- On the critical line the Mellin transform is exactly the ordinary Fourier
transform of the logarithmic pullback, with Mathlib's `2π` frequency scaling. -/
theorem mellin_residual_eq_fourier_criticalLogPullback (N : ℕ) (t : ℝ) :
    mellin (fun x : ℝ => (residual N x : ℂ)) (criticalLinePoint t) =
      𝓕 (criticalLogPullback N) (t / (2 * Real.pi)) := by
  simpa only [criticalLogPullback_eq_mellinLogPullback] using
    mellin_criticalLine_eq_fourier_mellinLogPullback
      (fun x : ℝ => (residual N x : ℂ)) t

/-- The critical-line energy written directly from the BCF Dirichlet polynomial. -/
noncomputable def criticalLineEnergy (N : ℕ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ,
    ‖(1 - riemannZeta (criticalLinePoint t) *
      dirichletPolynomial N (criticalLinePoint t)) / criticalLinePoint t‖ ^ 2

/-- The same critical-line energy, expressed through the actual Mellin transform. -/
noncomputable def mellinCriticalLineEnergy (N : ℕ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ,
    ‖mellin (fun x : ℝ => (residual N x : ℂ)) (criticalLinePoint t)‖ ^ 2

/-- Critical-line energy in the Fourier-coordinate form supplied by the
logarithmic change of variables. -/
noncomputable def fourierCriticalLineEnergy (N : ℕ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ,
    ‖𝓕 (criticalLogPullback N) (t / (2 * Real.pi))‖ ^ 2

/-- The `2π` frequency normalization in Mathlib's Fourier transform exactly
cancels the Jacobian in the critical-line coordinate. -/
theorem fourierCriticalLineEnergy_eq_fourierNormSq (N : ℕ) :
    fourierCriticalLineEnergy N =
      ∫ t : ℝ, ‖𝓕 (criticalLogPullback N) t‖ ^ 2 := by
  exact NBMellinTools.criticalLineFrequencyEnergy_eq_fourierNormSq
    (criticalLogPullback N)

theorem mellinCriticalLineEnergy_eq_fourierCriticalLineEnergy (N : ℕ) :
    mellinCriticalLineEnergy N = fourierCriticalLineEnergy N := by
  unfold mellinCriticalLineEnergy fourierCriticalLineEnergy
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [mellin_residual_eq_fourier_criticalLogPullback]

/-- The proposed critical-line energy is exactly the Mellin energy of the finite
BCF residual.  No Plancherel hypothesis enters this statement. -/
theorem mellinCriticalLineEnergy_eq_criticalLineEnergy (N : ℕ) :
    mellinCriticalLineEnergy N = criticalLineEnergy N := by
  unfold mellinCriticalLineEnergy criticalLineEnergy
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [mellin_residual_criticalLine]

/-- The BCF approximant belongs to `L²(0,∞)`. -/
theorem approximant_memLp_two (N : ℕ) :
    MemLp (approximant N) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  unfold approximant bdApprox coefficientFamily
  apply MeasureTheory.memLp_finsetSum (Finset.univ : Finset (Fin N))
  intro i hi
  simpa only [Pi.smul_apply, smul_eq_mul] using
    (rhoBD_memLp_two i.val).const_smul (-dirichletCoeff N (i.val + 1))

/-- The real BCF residual lies in the Hilbert space used by the finite energy. -/
theorem residual_memLp_two (N : ℕ) :
    MemLp (residual N) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  unfold residual
  exact chi01_memLp_two.sub (approximant_memLp_two N)

/-- Its complexification is also square-integrable. -/
theorem complex_residual_memLp_two (N : ℕ) :
    MemLp (fun x : ℝ => (residual N x : ℂ)) 2
      (volume.restrict (Ioi (0 : ℝ))) :=
  (residual_memLp_two N).ofReal

/-- The BCF logarithmic pullback is square-integrable on the Fourier line. -/
theorem criticalLogPullback_memLp_two (N : ℕ) :
    MemLp (criticalLogPullback N) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (criticalLogPullback_measurable N).aestronglyMeasurable).2
  have hsource : Integrable
      (fun x : ℝ => ‖(residual N x : ℂ)‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (complex_residual_memLp_two N).integrable_norm_pow (by norm_num)
  have himage : IntegrableOn
      (fun x : ℝ => ‖(residual N x : ℂ)‖ ^ 2)
      ((Real.exp ∘ Neg.neg) '' (univ : Set ℝ)) := by
    simpa only [rexp_neg_image] using hsource
  have hcoordinateOn := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexp_neg_deriv rexp_neg_injOn
      (fun x : ℝ => ‖(residual N x : ℂ)‖ ^ 2)).mp himage
  have hcoordinate : Integrable
      (fun u : ℝ => Real.exp (-u) * ‖(residual N (Real.exp (-u)) : ℂ)‖ ^ 2) := by
    rw [integrableOn_univ] at hcoordinateOn
    simpa only [Function.comp_apply, abs_neg,
      abs_of_pos (Real.exp_pos _), smul_eq_mul] using hcoordinateOn
  apply hcoordinate.congr
  filter_upwards with u
  unfold criticalLogPullback
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  have hexp : Real.exp (-u / 2) ^ 2 = Real.exp (-u) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]

/-- The finite BCF Gram energy is literally the positive-half-line squared norm
of the residual. -/
theorem energy_eq_residualL2NormSq (N : ℕ) :
    energy N = ∫ x in Ioi (0 : ℝ), ‖(residual N x : ℂ)‖ ^ 2 := by
  unfold energy BaezDuarteL2Error residual approximant
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The finite BCF Gram energy is also exactly the ordinary `L²` energy of
its logarithmic Fourier-coordinate pullback. -/
theorem energy_eq_criticalLogPullbackL2NormSq (N : ℕ) :
    energy N = ∫ u : ℝ, ‖criticalLogPullback N u‖ ^ 2 := by
  calc
    energy N = ∫ x in Ioi (0 : ℝ), ‖(residual N x : ℂ)‖ ^ 2 :=
      energy_eq_residualL2NormSq N
    _ = ∫ u : ℝ, ‖criticalLogPullback N u‖ ^ 2 := by
      simpa only [criticalLogPullback_eq_mellinLogPullback] using
        (integral_sq_norm_mellinLogPullback
          (fun x : ℝ => (residual N x : ℂ))).symm

/-- The finite BCF energy equals the proposed critical-line energy without
any additional analytic hypothesis.  The only analytic ingredient is the
proved `L¹ ∩ L²` compatibility of Mathlib's pointwise and `Lp` Fourier
transforms. -/
theorem energy_eq_criticalLineEnergy_unconditional (N : ℕ) :
    energy N = criticalLineEnergy N := by
  calc
    energy N = ∫ u : ℝ, ‖criticalLogPullback N u‖ ^ 2 :=
      energy_eq_criticalLogPullbackL2NormSq N
    _ = ∫ t : ℝ, ‖𝓕 (criticalLogPullback N) t‖ ^ 2 :=
      (NBMellinTools.integral_sq_norm_fourier_eq_integral_sq_norm
        (criticalLogPullback N) (criticalLogPullback_integrable N)
        (criticalLogPullback_memLp_two N)).symm
    _ = fourierCriticalLineEnergy N :=
      (fourierCriticalLineEnergy_eq_fourierNormSq N).symm
    _ = mellinCriticalLineEnergy N :=
      (mellinCriticalLineEnergy_eq_fourierCriticalLineEnergy N).symm
    _ = criticalLineEnergy N := mellinCriticalLineEnergy_eq_criticalLineEnergy N

/-- A compatibility interface retained for callers that package their own
positive-half-line Mellin--Plancherel hypotheses.  For the BCF residual, the
concrete theorem `energy_eq_criticalLineEnergy_unconditional` now proves the
bridge directly. -/
structure MellinPlancherelOnPositiveHalfLine where
  plancherel :
    ∀ f : ℝ → ℂ,
      MemLp f 2 (volume.restrict (Ioi (0 : ℝ))) →
      Integrable (mellinLogPullback f) →
        (∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2) =
          (1 / (2 * Real.pi)) * ∫ t : ℝ,
            ‖mellin f (criticalLinePoint t)‖ ^ 2

/--
The genuine finite-energy-to-critical-line bridge, conditional only on the
standard half-line Mellin--Plancherel theorem above.  All BCF-specific inputs
(finite `L²` membership, Mellin algebra, signs, and normalization) are proved
in this file.
-/
theorem energy_eq_criticalLineEnergy
    (HP : MellinPlancherelOnPositiveHalfLine) (N : ℕ) :
    energy N = criticalLineEnergy N := by
  rw [energy_eq_residualL2NormSq,
    HP.plancherel (fun x : ℝ => (residual N x : ℂ))
      (complex_residual_memLp_two N) (by
        simpa only [criticalLogPullback_eq_mellinLogPullback] using
          criticalLogPullback_integrable N)]
  exact mellinCriticalLineEnergy_eq_criticalLineEnergy N

end RH.Criteria.NymanBeurling.BCFLogTaperMellin
