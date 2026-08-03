import Mathlib.Probability.Distributions.Beta
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelTwoPole
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHorizontal
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzPLGrowth

/-!
# Route C: exponential horizontal control for complex Abel damping

For real Abel damping, inverse-polynomial Gamma recurrence is enough to make
the horizontal sides of the two-pole rectangle vanish.  A complex damping
parameter contributes `exp (|arg u| * |T|)`, so the genuine complex contour
requires Gamma's intrinsic `exp (-pi * |T| / 2)` decay uniformly in the real
part of the contour strip.

The first step is a Beta-integral comparison.  It transfers the exact
half-integer Gamma bound to every real part in the compact strip, without
using Stirling asymptotics.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelHorizontal

open Complex Filter MeasureTheory Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVerticalBounds
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHorizontal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelComplexDamping
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzGrowth
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzPLGrowth
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelLeftLine
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelTwoPole
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexEstermannMellin

/-- Taking norms inside the Beta integral discards only the imaginary parts
of its two parameters. -/
theorem norm_betaIntegral_le_realPart_betaIntegral
    {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ‖Complex.betaIntegral u v‖ ≤
      (Complex.betaIntegral (u.re : ℂ) (v.re : ℂ)).re := by
  unfold Complex.betaIntegral
  calc
    ‖∫ x : ℝ in 0..1,
        (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖ ≤
        ∫ x : ℝ in 0..1,
          ‖(x : ℂ) ^ (u - 1) *
            (1 - (x : ℂ)) ^ (v - 1)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ∫ x : ℝ in 0..1,
          ((x : ℂ) ^ ((u.re : ℂ) - 1) *
            (1 - (x : ℂ)) ^ ((v.re : ℂ) - 1)).re := by
      apply intervalIntegral.integral_congr_ae
      have hzero : ∀ᵐ x : ℝ, x ≠ 0 := by
        simp [ae_iff, measure_singleton]
      have hone : ∀ᵐ x : ℝ, x ≠ 1 := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hzero, hone] with x hx0ne hx1ne
      intro hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hx0 : 0 < x := hx.1
      have hx1lt : x < 1 := lt_of_le_of_ne hx.2 hx1ne
      have hx1 : 0 < 1 - x := sub_pos.mpr hx1lt
      have hcast : 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by
        push_cast
        ring
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
        hcast, Complex.norm_cpow_eq_rpow_re_of_pos hx1]
      simp only [sub_re, one_re]
      rw [show ((u.re : ℂ) - 1) = ((u.re - 1 : ℝ) : ℂ) by norm_cast,
        show ((v.re : ℂ) - 1) = ((v.re - 1 : ℝ) : ℂ) by norm_cast]
      rw [← Complex.ofReal_cpow (le_of_lt hx0),
        ← Complex.ofReal_cpow (le_of_lt hx1)]
      norm_cast
    _ = (∫ x : ℝ in 0..1,
          (x : ℂ) ^ ((u.re : ℂ) - 1) *
            (1 - (x : ℂ)) ^ ((v.re : ℂ) - 1)).re := by
      exact intervalIntegral.intervalIntegral_re
        (Complex.betaIntegral_convergent
          (u := (u.re : ℂ)) (v := (v.re : ℂ))
          (by simpa using hu) (by simpa using hv))

/-- Beta comparison in Gamma-quotient form. -/
theorem norm_betaIntegral_le_realGamma_quotient
    {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ‖Complex.betaIntegral u v‖ ≤
      Real.Gamma u.re * Real.Gamma v.re / Real.Gamma (u.re + v.re) := by
  calc
    ‖Complex.betaIntegral u v‖ ≤
        (Complex.betaIntegral (u.re : ℂ) (v.re : ℂ)).re :=
      norm_betaIntegral_le_realPart_betaIntegral hu hv
    _ = Real.Gamma u.re * Real.Gamma v.re /
        Real.Gamma (u.re + v.re) := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div]
      · simp_rw [← Complex.ofReal_add, Complex.Gamma_ofReal]
        norm_cast
      · simpa using hu
      · simpa using hv

/-! ## Transfer from the `9/2` half-line to the contour strip -/

/-- Three Gamma recurrences transfer the exact `3/2` estimate to `9/2`.
The deliberately coarse cubic factor is sufficient for every contour
application below. -/
theorem norm_Gamma_nine_halves_add_I_mul_le (t : ℝ) :
    ‖Complex.Gamma (((9 / 2 : ℝ) : ℂ) + I * t)‖ ≤
      (9 / 2 + |t|) ^ 3 * gammaThreeHalvesMajorant t := by
  let z : ℂ := ((3 / 2 : ℝ) : ℂ) + I * t
  have hz : ∀ j : ℕ, j < 3 → z + (j : ℂ) ≠ 0 := by
    intro j hj hzero
    have hre := congrArg Complex.re hzero
    have hjleNat : j ≤ 2 := by omega
    have hjle : (j : ℝ) ≤ 2 := by exact_mod_cast hjleNat
    norm_num [z] at hre
    linarith
  have hrec := Gamma_add_nat_eq_gammaShiftProduct_mul 3 z hz
  have harg : z + (3 : ℂ) = ((9 / 2 : ℝ) : ℂ) + I * t := by
    dsimp [z]
    push_cast
    ring
  have hrec' :
      Complex.Gamma (((9 / 2 : ℝ) : ℂ) + I * t) =
        gammaShiftProduct 3 z * Complex.Gamma z := by
    rw [← harg]
    exact hrec
  rw [hrec', norm_mul]
  have hfactor :
      ‖gammaShiftProduct 3 z‖ ≤ (9 / 2 + |t|) ^ 3 := by
    unfold gammaShiftProduct
    rw [norm_prod]
    calc
      ∏ j ∈ Finset.range 3, ‖z + (j : ℂ)‖ ≤
          ∏ _j ∈ Finset.range 3, (9 / 2 + |t|) := by
        apply Finset.prod_le_prod
        · exact fun _ _ => norm_nonneg _
        · intro j hj
          have hjlt : j < 3 := Finset.mem_range.mp hj
          have hjleNat : j ≤ 2 := by omega
          have hjle : (j : ℝ) ≤ 2 := by exact_mod_cast hjleNat
          have hjnonneg : 0 ≤ (3 / 2 + j : ℝ) := by positivity
          calc
            ‖z + (j : ℂ)‖ ≤
                |(z + (j : ℂ)).re| + |(z + (j : ℂ)).im| :=
              Complex.norm_le_abs_re_add_abs_im _
            _ = (3 / 2 + j : ℝ) + |t| := by
              simp [z, abs_of_nonneg hjnonneg]
            _ ≤ 9 / 2 + |t| := by linarith
      _ = (9 / 2 + |t|) ^ 3 := by simp
  exact mul_le_mul hfactor
    (norm_Gamma_three_halves_add_I_mul_le_majorant t)
    (norm_nonneg _) (by positivity)

/-- Beta comparison transfers the `9/2` half-line estimate to every positive
real part between `3/2` and `7/2`. -/
theorem norm_Gamma_positive_strip_le
    (r t : ℝ) (hr : r ∈ Set.Icc (3 / 2 : ℝ) (7 / 2 : ℝ)) :
    ‖Complex.Gamma (estermannVerticalPoint r t)‖ ≤
      ‖Complex.Gamma (((9 / 2 : ℝ) : ℂ) + I * t)‖ *
        Real.Gamma r / Real.Gamma (9 / 2 : ℝ) := by
  let u : ℂ := estermannVerticalPoint r t
  let v : ℝ := 9 / 2 - r
  have hu : 0 < u.re := by
    simp [u, estermannVerticalPoint]
    linarith [hr.1]
  have hv : 0 < v := by dsimp [v]; linarith [hr.2]
  have hsum : u + (v : ℂ) = ((9 / 2 : ℝ) : ℂ) + I * t := by
    dsimp [u, v, estermannVerticalPoint]
    push_cast
    ring
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := u) (t := (v : ℂ)) hu (by simpa using hv)
  have hvGamma : 0 < Real.Gamma v := Real.Gamma_pos_of_pos hv
  have hnormv : ‖Complex.Gamma (v : ℂ)‖ = Real.Gamma v := by
    simp [Complex.Gamma_ofReal, abs_of_pos hvGamma]
  have hbetaNorm := norm_betaIntegral_le_realGamma_quotient
    (u := u) (v := (v : ℂ)) hu (by simpa using hv)
  have hru : u.re = r := by simp [u, estermannVerticalPoint]
  have hvre : (v : ℂ).re = v := by simp
  rw [hru, hvre, show r + v = 9 / 2 by dsimp [v]; ring] at hbetaNorm
  have hmul :
      ‖Complex.Gamma u‖ * Real.Gamma v ≤
        ‖Complex.Gamma (((9 / 2 : ℝ) : ℂ) + I * t)‖ *
          (Real.Gamma r * Real.Gamma v / Real.Gamma (9 / 2 : ℝ)) := by
    calc
      ‖Complex.Gamma u‖ * Real.Gamma v =
          ‖Complex.Gamma u * Complex.Gamma (v : ℂ)‖ := by
        rw [norm_mul, hnormv]
      _ = ‖Complex.Gamma (((9 / 2 : ℝ) : ℂ) + I * t)‖ *
          ‖Complex.betaIntegral u (v : ℂ)‖ := by
        rw [hbeta, hsum, norm_mul]
      _ ≤ ‖Complex.Gamma (((9 / 2 : ℝ) : ℂ) + I * t)‖ *
          (Real.Gamma r * Real.Gamma v / Real.Gamma (9 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbetaNorm (norm_nonneg _)
  have hrearr :
      ‖Complex.Gamma (((9 / 2 : ℝ) : ℂ) + I * t)‖ *
          (Real.Gamma r * Real.Gamma v / Real.Gamma (9 / 2 : ℝ)) =
        (‖Complex.Gamma (((9 / 2 : ℝ) : ℂ) + I * t)‖ *
          Real.Gamma r / Real.Gamma (9 / 2 : ℝ)) * Real.Gamma v := by
    ring
  rw [hrearr] at hmul
  change ‖Complex.Gamma u‖ ≤ _
  nlinarith

/-- Uniform exponential Gamma decay on the full two-pole contour strip.
Only a compact maximum of the real Gamma function enters the constant. -/
theorem exists_gamma_complex_horizontal_strip_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ c ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ), ∀ t : ℝ,
        1 ≤ |t| →
        ‖Complex.Gamma (estermannVerticalPoint c t)‖ ≤
          C * (9 / 2 + |t|) ^ 3 * (1 + |t|) *
            Real.exp (-(Real.pi / 2) * |t|) := by
  let K : Set ℝ := Set.Icc (3 / 2 : ℝ) (7 / 2 : ℝ)
  have hKne : K.Nonempty := nonempty_Icc.mpr (by norm_num)
  have hKpos : K ⊆ Set.Ioi 0 := by
    intro r hr
    exact Set.mem_Ioi.mpr (by linarith [hr.1])
  have hcont : ContinuousOn Real.Gamma K :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono hKpos
  obtain ⟨r₀, hr₀, hrmax⟩ := isCompact_Icc.exists_isMaxOn hKne hcont
  let C : ℝ := Real.Gamma r₀ / Real.Gamma (9 / 2 : ℝ) *
    Real.sqrt (2 * Real.pi)
  have hr₀pos : 0 < r₀ := by linarith [hr₀.1]
  have hGammaR₀ : 0 < Real.Gamma r₀ := Real.Gamma_pos_of_pos hr₀pos
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro c hc t ht
  have ht0 : t ≠ 0 := by
    intro h
    norm_num [h] at ht
  have hcshift : c + 2 ∈ K := by
    constructor <;> dsimp [K] <;> linarith [hc.1, hc.2]
  have hrec := norm_Gamma_mul_abs_pow_le_real_Gamma_shift
    2 c t ht0 (by norm_num; linarith [hc.1])
  have hshift := norm_Gamma_positive_strip_le (c + 2) t hcshift
  have htSq : 1 ≤ |t| ^ 2 := by nlinarith [abs_nonneg t]
  have hdrop :
      ‖Complex.Gamma (estermannVerticalPoint c t)‖ ≤
        ‖Complex.Gamma (estermannVerticalPoint (c + 2) t)‖ := by
    have hmul :
        ‖Complex.Gamma (estermannVerticalPoint c t)‖ ≤
          ‖Complex.Gamma (estermannVerticalPoint c t)‖ * |t| ^ 2 := by
      nlinarith [norm_nonneg (Complex.Gamma (estermannVerticalPoint c t))]
    exact hmul.trans (by
      -- Reuse the exact recurrence argument rather than the weaker real-line
      -- majorant contained in `hrec`.
      let z : ℂ := estermannVerticalPoint c t
      have hz : ∀ j : ℕ, j < 2 → z + (j : ℂ) ≠ 0 := by
        intro j hj hzero
        have him := congrArg Complex.im hzero
        simp [z, estermannVerticalPoint] at him
        exact ht0 him
      have hexact := Gamma_add_nat_eq_gammaShiftProduct_mul 2 z hz
      have hprod := abs_pow_le_norm_gammaShiftProduct 2 c t
      have hmulprod := mul_le_mul_of_nonneg_left hprod
        (norm_nonneg (Complex.Gamma z))
      calc
        ‖Complex.Gamma z‖ * |t| ^ 2 ≤
            ‖Complex.Gamma z‖ * ‖gammaShiftProduct 2 z‖ := hmulprod
        _ = ‖Complex.Gamma (z + (2 : ℕ))‖ := by
          rw [← norm_mul, mul_comm, ← hexact]
        _ = ‖Complex.Gamma (estermannVerticalPoint (c + 2) t)‖ := by
          congr 2
          dsimp [z, estermannVerticalPoint]
          push_cast
          ring)
  have hrbound : Real.Gamma (c + 2) ≤ Real.Gamma r₀ := hrmax hcshift
  have hGamma9 := norm_Gamma_nine_halves_add_I_mul_le t
  calc
    ‖Complex.Gamma (estermannVerticalPoint c t)‖ ≤
        ‖Complex.Gamma (estermannVerticalPoint (c + 2) t)‖ := hdrop
    _ ≤ ‖Complex.Gamma (((9 / 2 : ℝ) : ℂ) + I * t)‖ *
        Real.Gamma (c + 2) / Real.Gamma (9 / 2 : ℝ) := hshift
    _ ≤ ‖Complex.Gamma (((9 / 2 : ℝ) : ℂ) + I * t)‖ *
        Real.Gamma r₀ / Real.Gamma (9 / 2 : ℝ) := by
      gcongr
    _ ≤ ((9 / 2 + |t|) ^ 3 * gammaThreeHalvesMajorant t) *
        Real.Gamma r₀ / Real.Gamma (9 / 2 : ℝ) := by
      gcongr
    _ = C * (9 / 2 + |t|) ^ 3 * (1 + |t|) *
        Real.exp (-(Real.pi / 2) * |t|) := by
      unfold gammaThreeHalvesMajorant C
      ring

/-! ## The complete complex horizontal row -/

/-- Uniform radial cost of the complex Abel power on the canonical strip. -/
noncomputable def complexAbelRadialStripBound (u : ℂ) : ℝ :=
  max (Real.rpow ‖u‖ (-2)) ‖u‖

theorem complexAbelRadialStripBound_nonneg (u : ℂ) :
    0 ≤ complexAbelRadialStripBound u :=
  le_max_of_le_left (Real.rpow_nonneg (norm_nonneg _) _)

/-- On a closed sector in the right half-plane, the complex Abel power has
only the angular cost `exp (theta * |t|)`. -/
theorem norm_complexAbelCpow_horizontal_le
    {u : ℂ} (hu : u ≠ 0) {theta : ℝ}
    (harg : |Complex.arg u| ≤ theta)
    (c t : ℝ) (hc : c ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ)) :
    ‖u ^ (estermannVerticalPoint c t - 1)‖ ≤
      complexAbelRadialStripBound u * Real.exp (theta * |t|) := by
  have hnormu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  rw [Complex.norm_cpow_of_ne_zero hu]
  have hre : (estermannVerticalPoint c t - 1).re = c - 1 := by
    simp [estermannVerticalPoint]
  have him : (estermannVerticalPoint c t - 1).im = t := by
    simp [estermannVerticalPoint]
  rw [hre, him, div_eq_mul_inv, ← Real.exp_neg]
  have hradial :
      Real.rpow ‖u‖ (c - 1) ≤ complexAbelRadialStripBound u := by
    by_cases hone : 1 ≤ ‖u‖
    · apply le_max_of_le_right
      calc
        Real.rpow ‖u‖ (c - 1) ≤ Real.rpow ‖u‖ 1 :=
          Real.rpow_le_rpow_of_exponent_le hone (by linarith [hc.2])
        _ = ‖u‖ := Real.rpow_one _
    · have hle : ‖u‖ ≤ 1 := le_of_not_ge hone
      apply le_max_of_le_left
      exact Real.rpow_le_rpow_of_exponent_ge hnormu hle
        (by linarith [hc.1])
  have hang : Real.exp (-(Complex.arg u * t)) ≤
      Real.exp (theta * |t|) := by
    apply Real.exp_le_exp.mpr
    calc
      -(Complex.arg u * t) ≤ |-(Complex.arg u * t)| := le_abs_self _
      _ = |Complex.arg u| * |t| := by rw [abs_neg, abs_mul]
      _ ≤ theta * |t| :=
        mul_le_mul_of_nonneg_right harg (abs_nonneg _)
  exact mul_le_mul hradial hang (Real.exp_pos _).le
    (complexAbelRadialStripBound_nonneg u)

/-- A canonical choice of the compact-strip Gamma constant. -/
noncomputable def complexAbelGammaStripConstant : ℝ :=
  Classical.choose exists_gamma_complex_horizontal_strip_bound

theorem complexAbelGammaStripConstant_nonneg :
    0 ≤ complexAbelGammaStripConstant :=
  (Classical.choose_spec exists_gamma_complex_horizontal_strip_bound).1

theorem complexAbelGammaStripConstant_bound
    (c : ℝ) (hc : c ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ))
    (t : ℝ) (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (estermannVerticalPoint c t)‖ ≤
      complexAbelGammaStripConstant * (9 / 2 + |t|) ^ 3 *
        (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) :=
  (Classical.choose_spec exists_gamma_complex_horizontal_strip_bound).2
    c hc t ht

/-- Pointwise decay of the full Estermann row on either horizontal side.
The exponent `2 * tDegree + 4` records the Hurwitz polynomial, three Gamma
recurrences, and the remaining linear Gamma factor. -/
theorem norm_complexAbel_horizontal_le
    (H : HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ))
    {u : ℂ} (hu : u ≠ 0) {theta : ℝ}
    (harg : |Complex.arg u| ≤ theta)
    (a q : ℕ) [NeZero q]
    (c t : ℝ) (hc : c ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ))
    (ht : 1 ≤ |t|) (hheight : H.minHeight ≤ |t|) :
    ‖estermannWeightedIntegrand a q
        (bettinConreyComplexAbelReflectionWeight u)
        (estermannVerticalPoint c t)‖ ≤
      (complexAbelGammaStripConstant * complexAbelRadialStripBound u *
        eventualEstermannStripConstant H q * (11 / 2) ^ 3 *
        2 ^ (2 * H.tDegree + 1)) *
        |t| ^ (2 * H.tDegree + 4) *
          Real.exp (-(Real.pi / 2 - theta) * |t|) := by
  have hreflect :
      1 - estermannVerticalPoint c t =
        estermannVerticalPoint (1 - c) (-t) := by
    unfold estermannVerticalPoint
    push_cast
    ring
  have hcref : 1 - c ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2]
  have hgamma := complexAbelGammaStripConstant_bound
    (1 - c) hcref (-t) (by simpa using ht)
  have hpow := norm_complexAbelCpow_horizontal_le hu harg c t hc
  have hD := eventualHurwitz_estermann_norm_le_uniform
    H a q (1 - c) (-t) hcref (by simpa using hheight)
  simp only [abs_neg] at hgamma hD
  have htpos : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have hbase : 1 + |t| ≤ 2 * |t| := by linarith
  have hbase9 : 9 / 2 + |t| ≤ (11 / 2) * |t| := by
    nlinarith
  have hgammaMajorantNonneg :
      0 ≤ complexAbelGammaStripConstant * (9 / 2 + |t|) ^ 3 *
        (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg complexAbelGammaStripConstant_nonneg
          (pow_nonneg (by positivity) _)) (by positivity))
      (Real.exp_pos _).le
  have hpowerMajorantNonneg :
      0 ≤ complexAbelRadialStripBound u * Real.exp (theta * |t|) :=
    mul_nonneg (complexAbelRadialStripBound_nonneg u) (Real.exp_pos _).le
  unfold estermannWeightedIntegrand
    bettinConreyComplexAbelReflectionWeight
  rw [norm_mul, norm_neg, norm_mul, hreflect]
  calc
    ‖Complex.Gamma (estermannVerticalPoint (1 - c) (-t))‖ *
          ‖u ^ (estermannVerticalPoint c t - 1)‖ *
        ‖estermannHurwitzContinuation a q
          (estermannVerticalPoint (1 - c) (-t))‖ ≤
      (complexAbelGammaStripConstant * (9 / 2 + |t|) ^ 3 *
          (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) *
        (complexAbelRadialStripBound u * Real.exp (theta * |t|)) *
        (eventualEstermannStripConstant H q *
          (1 + |t|) ^ (2 * H.tDegree)) := by
      have hfirst := mul_le_mul hgamma hpow
        (norm_nonneg _) hgammaMajorantNonneg
      exact mul_le_mul hfirst hD (norm_nonneg _)
        (mul_nonneg hgammaMajorantNonneg hpowerMajorantNonneg)
    _ ≤ (complexAbelGammaStripConstant * complexAbelRadialStripBound u *
          eventualEstermannStripConstant H q * (11 / 2) ^ 3 *
          2 ^ (2 * H.tDegree + 1)) *
        |t| ^ (2 * H.tDegree + 4) *
          Real.exp (-(Real.pi / 2 - theta) * |t|) := by
      have hpow9 : (9 / 2 + |t|) ^ 3 ≤
          ((11 / 2) * |t|) ^ 3 := pow_le_pow_left₀ (by positivity) hbase9 3
      have hpowBase : (1 + |t|) ^ (2 * H.tDegree + 1) ≤
          (2 * |t|) ^ (2 * H.tDegree + 1) :=
        pow_le_pow_left₀ (by positivity) hbase _
      have hexp :
          Real.exp (-(Real.pi / 2) * |t|) *
              Real.exp (theta * |t|) =
            Real.exp (-(Real.pi / 2 - theta) * |t|) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hexp]
      have hnonneg :
          0 ≤ complexAbelGammaStripConstant *
            complexAbelRadialStripBound u *
              eventualEstermannStripConstant H q := by
        exact mul_nonneg
          (mul_nonneg complexAbelGammaStripConstant_nonneg
            (complexAbelRadialStripBound_nonneg u))
          (eventualEstermannStripConstant_nonneg H q)
      calc
        (complexAbelGammaStripConstant * (9 / 2 + |t|) ^ 3 *
              (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) *
            (complexAbelRadialStripBound u * Real.exp (theta * |t|)) *
            (eventualEstermannStripConstant H q *
              (1 + |t|) ^ (2 * H.tDegree)) =
          (complexAbelGammaStripConstant * complexAbelRadialStripBound u *
              eventualEstermannStripConstant H q) *
            (9 / 2 + |t|) ^ 3 *
            (1 + |t|) ^ (2 * H.tDegree + 1) *
            (Real.exp (-(Real.pi / 2) * |t|) *
              Real.exp (theta * |t|)) := by
                rw [pow_succ']
                ring
        _ ≤ (complexAbelGammaStripConstant * complexAbelRadialStripBound u *
              eventualEstermannStripConstant H q) *
            (((11 / 2) * |t|) ^ 3) *
            ((2 * |t|) ^ (2 * H.tDegree + 1)) *
            (Real.exp (-(Real.pi / 2) * |t|) *
              Real.exp (theta * |t|)) := by
                gcongr
        _ = (complexAbelGammaStripConstant * complexAbelRadialStripBound u *
              eventualEstermannStripConstant H q * (11 / 2) ^ 3 *
              2 ^ (2 * H.tDegree + 1)) *
            |t| ^ (2 * H.tDegree + 4) *
            (Real.exp (-(Real.pi / 2) * |t|) *
              Real.exp (theta * |t|)) := by
                rw [mul_pow, mul_pow, show 2 * H.tDegree + 4 =
                  3 + (2 * H.tDegree + 1) by omega, pow_add]
                ring

/-- The full complex-damped horizontal pair vanishes in every closed sector
strictly inside the right half-plane. -/
theorem complexAbel_horizontal_pair_vanishes_of_eventualHurwitzGrowth
    (H : HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ))
    {u : ℂ} (hu : u ≠ 0) {theta : ℝ}
    (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi / 2)
    (a q : ℕ) [NeZero q] :
    Tendsto
      (symmetricHorizontalEdges
        (estermannWeightedIntegrand a q
          (bettinConreyComplexAbelReflectionWeight u))
        (-1 / 2 : ℝ) (3 / 2 : ℝ)) atTop (𝓝 0) := by
  let degree : ℕ := 2 * H.tDegree + 4
  let rate : ℝ := Real.pi / 2 - theta
  let C : ℝ :=
    complexAbelGammaStripConstant * complexAbelRadialStripBound u *
      eventualEstermannStripConstant H q * (11 / 2) ^ 3 *
        2 ^ (2 * H.tDegree + 1)
  apply horizontal_pair_vanishes_of_eventual_majorant
    (estermannWeightedIntegrand a q
      (bettinConreyComplexAbelReflectionWeight u))
    (-1 / 2 : ℝ) (3 / 2 : ℝ)
    (abelHorizontalPolynomialExponentialMajorant C degree rate)
    (by norm_num)
  · filter_upwards [eventually_ge_atTop (max 1 H.minHeight)] with T hT
    have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
    have hTheight : H.minHeight ≤ T := (le_max_right _ _).trans hT
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT1
    have hTabs : |T| = T := abs_of_pos hTpos
    refine ⟨hTpos.le, ?_⟩
    intro c hc
    constructor
    · have h := norm_complexAbel_horizontal_le H hu harg a q c T hc
        (by simpa [hTabs] using hT1)
        (by simpa [hTabs] using hTheight)
      simpa [C, degree, rate, hTabs,
        abelHorizontalPolynomialExponentialMajorant,
        estermannVerticalPoint] using h
    · have h := norm_complexAbel_horizontal_le H hu harg a q c (-T) hc
        (by simpa [abs_neg, hTabs] using hT1)
        (by simpa [abs_neg, hTabs] using hTheight)
      simpa [C, degree, rate, abs_neg, hTabs,
        abelHorizontalPolynomialExponentialMajorant,
        estermannVerticalPoint, sub_eq_add_neg] using h
  · exact tendsto_abelHorizontalPolynomialExponentialMajorant
      C degree (sub_pos.mpr htheta)

/-- Unconditional specialization using the theta-kernel Hurwitz strip
estimate already proved in Route C. -/
theorem complexAbel_horizontal_pair_vanishes
    {u : ℂ} (hu : u ≠ 0) {theta : ℝ}
    (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi / 2)
    (a q : ℕ) [NeZero q] :
    Tendsto
      (symmetricHorizontalEdges
        (estermannWeightedIntegrand a q
          (bettinConreyComplexAbelReflectionWeight u))
        (-1 / 2 : ℝ) (3 / 2 : ℝ)) atTop (𝓝 0) :=
  complexAbel_horizontal_pair_vanishes_of_eventualHurwitzGrowth
    eventualHurwitzGrowth hu harg htheta a q

/-! ## The infinite complex two-pole contour -/

/-- All four sides of the complex Abel rectangle now converge
unconditionally in a strict right-half-plane sector. -/
noncomputable def complexAbelEvaluationContourShift
    {u : ℂ} (huRe : 0 < u.re) {theta : ℝ}
    (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi / 2)
    (a q : ℕ) [NeZero q] :
    EstermannEvaluationContourShift a q
      (bettinConreyComplexAbelReflectionWeight u)
      (-1 / 2 : ℝ) (3 / 2 : ℝ) := by
  have hu : u ≠ 0 := by
    intro h
    simp [h] at huRe
  exact {
    weight_differentiableAt_zero :=
      differentiableAt_complexAbelReflectionWeight_zero hu
    weight_unitResidueAt_one :=
      hasUnitResidueAtOne_complexAbelReflectionWeight hu
    left_of_zero := by norm_num
    right_of_one := by norm_num
    boundary_eq_two_residues := fun T hT =>
      bettinConreyComplexAbel_twoPoleRectangle hu a q T hT
    left_vertical_converges :=
      tendsto_truncatedVerticalIntegral_of_integrable _ _
        (integrable_complexAbel_leftVertical huRe a q)
    right_vertical_converges :=
      tendsto_truncatedVerticalIntegral_of_integrable _ _
        (EstermannNegativeHalfPolynomialGrowth.complex_right_integrable
          (estermannNegativeHalfPolynomialGrowth a q) hu harg htheta)
    horizontal_pair_vanishes :=
      complexAbel_horizontal_pair_vanishes hu harg htheta a q }

/-- Exact infinite contour identity for complex damping.  This is the
sectorial extension needed on the reciprocal rational Abel ray. -/
theorem complexAbel_rightVertical_eq_damped_add_residues
    {u : ℂ} (huRe : 0 < u.re) {theta : ℝ}
    (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi / 2)
    (a q : ℕ) [NeZero q] :
    estermannPrimalVerticalIntegral a q (3 / 2 : ℝ)
        (bettinConreyComplexAbelReflectionWeight u) =
      -(2 * Real.pi : ℝ) * complexDampedEstermannLambertSeries a q u +
        2 * Real.pi *
          (estermannWeightedResidueCoefficient a q
              (bettinConreyComplexAbelReflectionWeight u) +
            estermannHurwitzContinuation a q 0) := by
  rw [EstermannEvaluationContourShift.primalVerticalIntegral_eq
      (complexAbelEvaluationContourShift huRe harg htheta a q),
    complexAbel_leftVerticalIntegral_eq_damped huRe a q]

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelHorizontal
