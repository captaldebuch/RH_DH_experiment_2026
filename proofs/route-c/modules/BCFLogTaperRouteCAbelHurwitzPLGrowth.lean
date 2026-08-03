import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzStrip

/-!
# Route C: a-priori Hurwitz growth from the theta Mellin kernels

This file supplies the last a-priori growth input in the pole-removed
Phragmen--Lindelof argument.  The first ingredient is a reusable elementary
fact: a Mellin transform is uniformly bounded when its real parameter stays
in a compact interval and the two endpoint norm majorants are integrable.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzPLGrowth

open Complex Filter Set Topology MeasureTheory Asymptotics
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzStrip
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVerticalBounds
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannGlobalExchange
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHorizontal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelContourLimit
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReflectionWeight

/-- An integrable endpoint majorant for a Mellin transform on the compact
real strip `[a,b]`. -/
noncomputable def mellinCompactStripMajorant
    (f : ℝ → ℂ) (a b : ℝ) (x : ℝ) : ℝ :=
  (x ^ (a - 1) + x ^ (b - 1)) * ‖f x‖

theorem integrableOn_mellinCompactStripMajorant
    (f : ℝ → ℂ) (a b : ℝ)
    (ha : IntegrableOn (fun x : ℝ => x ^ (a - 1) * ‖f x‖) (Ioi 0))
    (hb : IntegrableOn (fun x : ℝ => x ^ (b - 1) * ‖f x‖) (Ioi 0)) :
    IntegrableOn (mellinCompactStripMajorant f a b) (Ioi 0) := by
  convert ha.add hb using 1
  ext x
  simp only [Pi.add_apply, mellinCompactStripMajorant]
  ring

/-- The norm of a Mellin transform is uniformly controlled by the two real
endpoint integrals.  No imaginary parameter occurs in the majorant. -/
theorem norm_mellin_le_compactStripMajorant
    (f : ℝ → ℂ) (a b : ℝ) (s : ℂ)
    (ha : IntegrableOn (fun x : ℝ => x ^ (a - 1) * ‖f x‖) (Ioi 0))
    (hb : IntegrableOn (fun x : ℝ => x ^ (b - 1) * ‖f x‖) (Ioi 0))
    (has : a ≤ s.re) (hsb : s.re ≤ b) :
    ‖mellin f s‖ ≤
      ∫ x : ℝ in Ioi 0, mellinCompactStripMajorant f a b x := by
  unfold mellin
  apply norm_integral_le_of_norm_le
    (integrableOn_mellinCompactStripMajorant f a b ha hb)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx]
  simp only [sub_re, one_re]
  unfold mellinCompactStripMajorant
  rw [add_mul]
  by_cases hx1 : x ≤ 1
  · have hpow : x ^ (s.re - 1) ≤ x ^ (a - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)
    exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
      (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _)))
  · have hx1' : 1 ≤ x := le_of_not_ge hx1
    have hpow : x ^ (s.re - 1) ≤ x ^ (b - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
    exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
      (le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _)))

/-- A strong functional-equation pair has an integrable Mellin endpoint
majorant at every real parameter. -/
theorem StrongFEPair.integrableOn_mellinNormEndpoint
    (P : StrongFEPair ℂ) (a : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * ‖P.f x‖) (Ioi 0) := by
  have h := (mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi
    P.hf_int.aestronglyMeasurable (s := (a : ℂ))).mp
    (P.hasMellin (a : ℂ)).1
  simpa using h

/-- Consequently the completed Mellin transform of a strong
functional-equation pair is uniformly bounded on every compact vertical
strip. -/
theorem StrongFEPair.norm_Λ_le_compactStripMajorant
    (P : StrongFEPair ℂ) (a b : ℝ) (s : ℂ)
    (has : a ≤ s.re) (hsb : s.re ≤ b) :
    ‖P.Λ s‖ ≤
      ∫ x : ℝ in Ioi 0, mellinCompactStripMajorant P.f a b x := by
  exact norm_mellin_le_compactStripMajorant P.f a b s
    (StrongFEPair.integrableOn_mellinNormEndpoint P a)
    (StrongFEPair.integrableOn_mellinNormEndpoint P b) has hsb

/-! ## Reciprocal Gamma on the compact Hurwitz strip -/

/-- The elementary exponential bound for complex sine, with the important
feature that it depends only on the imaginary part. -/
theorem norm_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, norm_ofNat, norm_I, mul_one]
  have hpos : (0 : ℝ) < 2 := by norm_num
  apply (div_le_iff₀ hpos).2
  calc
    ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ ≤
        ‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖ := norm_sub_le _ _
    _ ≤ Real.exp |z.im| + Real.exp |z.im| := by
      apply add_le_add <;> rw [Complex.norm_exp, Real.exp_le_exp] <;>
        simp only [mul_re, neg_re, I_re, I_im, mul_zero, zero_mul,
          sub_zero, neg_im, neg_neg] <;> linarith [neg_abs_le z.im, le_abs_self z.im]
    _ = Real.exp |z.im| * 2 := by ring

/-- Gamma is uniformly bounded on every vertical line whose real part lies
in the positive compact interval `[3/4,9/4]`. -/
theorem exists_gamma_positive_compactStrip_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ c ∈ Set.Icc (3 / 4 : ℝ) (9 / 4 : ℝ), ∀ t : ℝ,
        ‖Complex.Gamma (estermannVerticalPoint c t)‖ ≤ C := by
  let K : Set ℝ := Set.Icc (3 / 4 : ℝ) (9 / 4 : ℝ)
  have hKne : K.Nonempty := nonempty_Icc.mpr (by norm_num)
  have hKpos : K ⊆ Set.Ioi 0 := by
    intro y hy
    exact Set.mem_Ioi.mpr (by linarith [hy.1])
  have hcont : ContinuousOn Real.Gamma K :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono hKpos
  obtain ⟨y, hyK, hymax⟩ := isCompact_Icc.exists_isMaxOn hKne hcont
  refine ⟨max 0 (Real.Gamma y), le_max_left _ _, ?_⟩
  intro c hc t
  have hcpos : 0 < c := by linarith [hc.1]
  exact (norm_Gamma_vertical_le_real_Gamma c t hcpos).trans
    ((hymax hc).trans (le_max_right _ _))

/-- On the strip needed by both parity components of Hurwitz zeta, reciprocal
Gamma has a single-exponential vertical bound.  We only need the estimate at
height at least one; this avoids every removable integer special case in the
reflection identity. -/
theorem exists_invGamma_compactStrip_exp_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ c ∈ Set.Icc (-1 / 4 : ℝ) (5 / 4 : ℝ), ∀ t : ℝ,
        1 ≤ |t| →
        ‖(Complex.Gamma (estermannVerticalPoint c t))⁻¹‖ ≤
          C * Real.exp (Real.pi * |t|) := by
  obtain ⟨C, hC, hGamma⟩ := exists_gamma_positive_compactStrip_bound
  refine ⟨C, hC, ?_⟩
  intro c hc t ht
  let z : ℂ := estermannVerticalPoint c t
  have ht0 : t ≠ 0 := by
    intro h
    norm_num [h] at ht
  have hzIm : z.im = t := by simp [z, estermannVerticalPoint]
  have hOneSub : 1 - z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [hzIm] at him
    exact ht0 him
  have hzGamma : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have him := congrArg Complex.im h
    simp [hzIm] at him
    exact ht0 him
  have hsin : Complex.sin (Real.pi * z) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have him := congrArg Complex.im hk
    have hpit : Real.pi * t = 0 := by
      simpa [z, estermannVerticalPoint] using him
    exact ht0 ((mul_eq_zero.mp hpit).resolve_left Real.pi_ne_zero)
  have hreflect := Complex.Gamma_mul_Gamma_one_sub z
  have hinvEq :
      (Complex.Gamma z)⁻¹ =
        Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi := by
    have hreflect' :
        Complex.Gamma z * Complex.Gamma (1 - z) *
            Complex.sin (Real.pi * z) = Real.pi :=
      (eq_div_iff hsin).mp hreflect
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).2
    calc
      (Complex.Gamma z)⁻¹ * Real.pi =
          (Complex.Gamma z)⁻¹ *
            (Complex.Gamma z * Complex.Gamma (1 - z) *
              Complex.sin (Real.pi * z)) :=
        congrArg (fun w : ℂ => (Complex.Gamma z)⁻¹ * w) hreflect'.symm
      _ = Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) := by
        field_simp [hzGamma]
  have hshiftArg :
      (1 - z) + 1 = estermannVerticalPoint (2 - c) (-t) := by
    apply Complex.ext <;> simp [z, estermannVerticalPoint] <;> ring
  have hshiftMem : 2 - c ∈ Set.Icc (3 / 4 : ℝ) (9 / 4 : ℝ) := by
    constructor <;> linarith [hc.1, hc.2]
  have hrec := Complex.Gamma_add_one (1 - z) hOneSub
  have hden : 1 ≤ ‖1 - z‖ := by
    have him := Complex.abs_im_le_norm (1 - z)
    have : (1 - z).im = -t := by simp [z, estermannVerticalPoint]
    rw [this, abs_neg] at him
    exact ht.trans him
  have hGammaOneSub : ‖Complex.Gamma (1 - z)‖ ≤ C := by
    have hmul :
        ‖Complex.Gamma (1 - z)‖ ≤
          ‖1 - z‖ * ‖Complex.Gamma (1 - z)‖ :=
      le_mul_of_one_le_left (norm_nonneg _) hden
    calc
      ‖Complex.Gamma (1 - z)‖ ≤
          ‖1 - z‖ * ‖Complex.Gamma (1 - z)‖ := hmul
      _ = ‖Complex.Gamma ((1 - z) + 1)‖ := by
        rw [hrec, norm_mul]
      _ = ‖Complex.Gamma (estermannVerticalPoint (2 - c) (-t))‖ := by rw [hshiftArg]
      _ ≤ C := hGamma (2 - c) hshiftMem (-t)
  have hsinBound :
      ‖Complex.sin (Real.pi * z)‖ ≤ Real.exp (Real.pi * |t|) := by
    calc
      ‖Complex.sin (Real.pi * z)‖ ≤
          Real.exp |(Real.pi * z).im| := norm_sin_le_exp_abs_im _
      _ = Real.exp (Real.pi * |t|) := by
        congr 1
        simp [z, estermannVerticalPoint, abs_mul, abs_of_pos Real.pi_pos]
  rw [hinvEq, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    ‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (Real.pi * z)‖ / Real.pi ≤
        ‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (Real.pi * z)‖ := by
      exact div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (by linarith [Real.pi_gt_three])
    _ ≤ C * Real.exp (Real.pi * |t|) :=
      mul_le_mul hGammaOneSub hsinBound (norm_nonneg _) hC

/-- Both Deligne Gamma factors occurring in the even/odd decomposition of
Hurwitz zeta have the same eventual single-exponential bound on the
canonical strip. -/
theorem exists_invGammaR_hurwitzStrip_exp_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ), ∀ t : ℝ,
        2 ≤ |t| →
        ‖(Complex.Gammaℝ (estermannVerticalPoint σ t))⁻¹‖ ≤
            C * Real.exp (Real.pi * |t| / 2) ∧
          ‖(Complex.Gammaℝ (estermannVerticalPoint σ t + 1))⁻¹‖ ≤
            C * Real.exp (Real.pi * |t| / 2) := by
  obtain ⟨C, hC, hInv⟩ := exists_invGamma_compactStrip_exp_bound
  let C' : ℝ := C * Real.pi ^ 2
  have hC' : 0 ≤ C' := mul_nonneg hC (sq_nonneg _)
  refine ⟨C', hC', ?_⟩
  intro σ hσ t ht
  let s : ℂ := estermannVerticalPoint σ t
  have htHalf : 1 ≤ |t / 2| := by
    rw [abs_div]
    norm_num
    linarith
  have hpiOne : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpiPos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpow (u : ℂ) (hu : u.re / 2 ≤ 2) :
      ‖((Real.pi : ℂ) ^ (-u / 2))⁻¹‖ ≤ Real.pi ^ 2 := by
    have hneg : -(-u / 2) = u / 2 := by ring
    rw [← Complex.cpow_neg, hneg,
      Complex.norm_cpow_eq_rpow_re_of_pos hpiPos]
    have hre : (u / 2).re = u.re / 2 := by simp
    rw [hre]
    calc
      Real.pi ^ (u.re / 2) ≤ Real.pi ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hpiOne hu
      _ = Real.pi ^ 2 := by simpa using Real.rpow_natCast Real.pi 2
  have hsHalf : s / 2 = estermannVerticalPoint (σ / 2) (t / 2) := by
    apply Complex.ext <;> simp [s, estermannVerticalPoint] <;> ring
  have hsOneHalf : (s + 1) / 2 =
      estermannVerticalPoint ((σ + 1) / 2) (t / 2) := by
    apply Complex.ext <;> simp [s, estermannVerticalPoint] <;> ring
  have hσHalf : σ / 2 ∈ Set.Icc (-1 / 4 : ℝ) (5 / 4 : ℝ) := by
    constructor <;> linarith [hσ.1, hσ.2]
  have hσOneHalf : (σ + 1) / 2 ∈ Set.Icc (-1 / 4 : ℝ) (5 / 4 : ℝ) := by
    constructor <;> linarith [hσ.1, hσ.2]
  have hInvS := hInv (σ / 2) hσHalf (t / 2) htHalf
  have hInvSOne := hInv ((σ + 1) / 2) hσOneHalf (t / 2) htHalf
  have hexpHalf :
      Real.exp (Real.pi * |t / 2|) =
        Real.exp (Real.pi * |t| / 2) := by
    congr 1
    rw [abs_div]
    norm_num
    ring
  rw [hexpHalf] at hInvS hInvSOne
  constructor
  · rw [Complex.Gammaℝ_def, mul_inv, norm_mul]
    calc
      ‖((Real.pi : ℂ) ^ (-s / 2))⁻¹‖ *
          ‖(Complex.Gamma (s / 2))⁻¹‖ ≤
        Real.pi ^ 2 * (C * Real.exp (Real.pi * |t| / 2)) := by
          apply mul_le_mul (hpow s (by dsimp [s]; simp [estermannVerticalPoint]; linarith [hσ.2]))
            (by simpa [hsHalf] using hInvS) (norm_nonneg _) (sq_nonneg _)
      _ = C' * Real.exp (Real.pi * |t| / 2) := by
        dsimp [C']
        ring
  · rw [Complex.Gammaℝ_def, mul_inv, norm_mul]
    calc
      ‖((Real.pi : ℂ) ^ (-(s + 1) / 2))⁻¹‖ *
          ‖(Complex.Gamma ((s + 1) / 2))⁻¹‖ ≤
        Real.pi ^ 2 * (C * Real.exp (Real.pi * |t| / 2)) := by
          apply mul_le_mul
            (hpow (s + 1) (by dsimp [s]; simp [estermannVerticalPoint]; linarith [hσ.2]))
            (by simpa [hsOneHalf] using hInvSOne) (norm_nonneg _) (sq_nonneg _)
      _ = C' * Real.exp (Real.pi * |t| / 2) := by
        dsimp [C']
        ring

/-! ## Completed Hurwitz factors -/

/-- The pole-corrected completed even Hurwitz factor is uniformly bounded
on the canonical strip.  This is exactly the theta-kernel Mellin estimate,
not a maximum-modulus assumption. -/
theorem exists_completedHurwitzZetaEven₀_strip_bound
    (x : UnitAddCircle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      s.re ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ) →
      ‖HurwitzZeta.completedHurwitzZetaEven₀ x s‖ ≤ C := by
  let P : StrongFEPair ℂ := (HurwitzZeta.hurwitzEvenFEPair x).toStrongFEPair
  let M : ℝ := ∫ y : ℝ in Ioi 0, mellinCompactStripMajorant P.f (-1) 1 y
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  intro s hs
  have hΛ := StrongFEPair.norm_Λ_le_compactStripMajorant
    P (-1) 1 (s / 2) (by simp; linarith [hs.1]) (by simp; linarith [hs.2])
  have hdef :
      HurwitzZeta.completedHurwitzZetaEven₀ x s = P.Λ (s / 2) / 2 := by
    rfl
  rw [hdef, norm_div, norm_ofNat]
  calc
    ‖P.Λ (s / 2)‖ / 2 ≤ ‖P.Λ (s / 2)‖ :=
      div_le_self (norm_nonneg _) (by norm_num)
    _ ≤ M := by simpa [M] using hΛ
    _ ≤ max 0 M := le_max_right _ _

/-- The completed odd Hurwitz factor is uniformly bounded on the same
strip. -/
theorem exists_completedHurwitzZetaOdd_strip_bound
    (x : UnitAddCircle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      s.re ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ) →
      ‖HurwitzZeta.completedHurwitzZetaOdd x s‖ ≤ C := by
  let P : StrongFEPair ℂ := HurwitzZeta.hurwitzOddFEPair x
  let M : ℝ := ∫ y : ℝ in Ioi 0, mellinCompactStripMajorant P.f 0 2 y
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  intro s hs
  have hΛ := StrongFEPair.norm_Λ_le_compactStripMajorant
    P 0 2 ((s + 1) / 2) (by simp; linarith [hs.1]) (by simp; linarith [hs.2])
  have hdef :
      HurwitzZeta.completedHurwitzZetaOdd x s = P.Λ ((s + 1) / 2) / 2 := by
    rfl
  rw [hdef, norm_div, norm_ofNat]
  calc
    ‖P.Λ ((s + 1) / 2)‖ / 2 ≤ ‖P.Λ ((s + 1) / 2)‖ :=
      div_le_self (norm_nonneg _) (by norm_num)
    _ ≤ M := by simpa [M] using hΛ
    _ ≤ max 0 M := le_max_right _ _

/-! ## The pole-removed Hurwitz factor -/

/-- The complete pole-removed Hurwitz factor has at most a polynomial times
single-exponential vertical loss.  This estimate is substantially stronger
than the double-exponential hypothesis requested by the strip
Phragmen--Lindelof theorem. -/
theorem exists_hurwitzPoleRemovedFactor_exp_bound
    (x : UnitAddCircle) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ), ∀ t : ℝ,
        2 ≤ |t| →
        ‖hurwitzPoleRemovedFactor x (estermannVerticalPoint σ t)‖ ≤
          C * (1 + |t|) * Real.exp (Real.pi * |t| / 2) := by
  obtain ⟨CE, hCE, hEven₀⟩ := exists_completedHurwitzZetaEven₀_strip_bound x
  obtain ⟨CO, hCO, hOdd⟩ := exists_completedHurwitzZetaOdd_strip_bound x
  obtain ⟨CG, hCG, hGammaR⟩ := exists_invGammaR_hurwitzStrip_exp_bound
  let C : ℝ := 2 * CG * (CE + CO + 2)
  have hsum : 0 ≤ CE + CO + 2 := by linarith
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num) hCG) hsum
  refine ⟨C, hC, ?_⟩
  intro σ hσ t ht
  let s : ℂ := estermannVerticalPoint σ t
  have ht0 : t ≠ 0 := by
    intro h
    norm_num [h] at ht
  have hs0 : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [s, estermannVerticalPoint] at him
    exact ht0 him
  have hs1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [s, estermannVerticalPoint] at him
    exact ht0 him
  have hsNorm : 1 ≤ ‖s‖ := by
    have him := Complex.abs_im_le_norm s
    have hsim : s.im = t := by simp [s, estermannVerticalPoint]
    rw [hsim] at him
    linarith
  have hOneSubNorm : 1 ≤ ‖1 - s‖ := by
    have him := Complex.abs_im_le_norm (1 - s)
    have hsim : (1 - s).im = -t := by simp [s, estermannVerticalPoint]
    rw [hsim, abs_neg] at him
    linarith
  have hInvS : ‖s⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hsNorm
  have hInvS' : ‖s‖⁻¹ ≤ 1 := by simpa [norm_inv] using hInvS
  have hInvOneSub : ‖(1 - s)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hOneSubNorm
  have hEvenCompleted :
      ‖HurwitzZeta.completedHurwitzZetaEven x s‖ ≤ CE + 2 := by
    rw [HurwitzZeta.completedHurwitzZetaEven_eq]
    calc
      ‖HurwitzZeta.completedHurwitzZetaEven₀ x s -
          (if x = 0 then 1 else 0) / s - 1 / (1 - s)‖ ≤
        ‖HurwitzZeta.completedHurwitzZetaEven₀ x s‖ +
          ‖(if x = 0 then 1 else 0) / s‖ + ‖1 / (1 - s)‖ := by
            calc
              ‖HurwitzZeta.completedHurwitzZetaEven₀ x s -
                  (if x = 0 then 1 else 0) / s - 1 / (1 - s)‖ ≤
                ‖HurwitzZeta.completedHurwitzZetaEven₀ x s -
                    (if x = 0 then 1 else 0) / s‖ + ‖1 / (1 - s)‖ :=
                  norm_sub_le _ _
              _ ≤ (‖HurwitzZeta.completedHurwitzZetaEven₀ x s‖ +
                    ‖(if x = 0 then 1 else 0) / s‖) + ‖1 / (1 - s)‖ := by
                  gcongr
                  exact norm_sub_le _ _
      _ ≤ CE + 1 + 1 := by
        apply add_le_add
        · apply add_le_add (hEven₀ s (by simpa [s, estermannVerticalPoint] using hσ))
          by_cases hx : x = 0 <;> simp [hx, one_div, hInvS']
        · simpa [one_div] using hInvOneSub
      _ = CE + 2 := by ring
  have hGamma := hGammaR σ hσ t ht
  have hEven :
      ‖HurwitzZeta.hurwitzZetaEven x s‖ ≤
        (CE + 2) * (CG * Real.exp (Real.pi * |t| / 2)) := by
    rw [HurwitzZeta.hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs0),
      div_eq_mul_inv, norm_mul]
    exact mul_le_mul hEvenCompleted hGamma.1 (norm_nonneg _) (by positivity)
  have hOddZeta :
      ‖HurwitzZeta.hurwitzZetaOdd x s‖ ≤
        CO * (CG * Real.exp (Real.pi * |t| / 2)) := by
    unfold HurwitzZeta.hurwitzZetaOdd
    rw [div_eq_mul_inv, norm_mul]
    exact mul_le_mul
      (hOdd s (by simpa [s, estermannVerticalPoint] using hσ))
      hGamma.2 (norm_nonneg _) (by positivity)
  have hZeta :
      ‖HurwitzZeta.hurwitzZeta x s‖ ≤
        CG * (CE + CO + 2) * Real.exp (Real.pi * |t| / 2) := by
    unfold HurwitzZeta.hurwitzZeta
    calc
      ‖HurwitzZeta.hurwitzZetaEven x s +
          HurwitzZeta.hurwitzZetaOdd x s‖ ≤
        ‖HurwitzZeta.hurwitzZetaEven x s‖ +
          ‖HurwitzZeta.hurwitzZetaOdd x s‖ := norm_add_le _ _
      _ ≤ (CE + 2) * (CG * Real.exp (Real.pi * |t| / 2)) +
          CO * (CG * Real.exp (Real.pi * |t| / 2)) := add_le_add hEven hOddZeta
      _ = CG * (CE + CO + 2) * Real.exp (Real.pi * |t| / 2) := by ring
  rw [hurwitzPoleRemovedFactor_eq_mul_hurwitzZeta x hs1, norm_mul]
  have hsub := norm_verticalPoint_sub_one_le σ t hσ
  calc
    ‖s - 1‖ * ‖HurwitzZeta.hurwitzZeta x s‖ ≤
        (2 * (1 + |t|)) *
          (CG * (CE + CO + 2) * Real.exp (Real.pi * |t| / 2)) :=
      mul_le_mul hsub hZeta (norm_nonneg _) (by positivity)
    _ = C * (1 + |t|) * Real.exp (Real.pi * |t| / 2) := by
      dsimp [C]
      ring

/-! ## Discharging the Phragmen--Lindelof input -/

/-- Polynomial-times-single-exponential growth is dominated by the precise
double exponential accepted by the vertical-strip Phragmen--Lindelof
theorem.  We choose exponent `3/2`, which is strictly below the critical
strip exponent `π/2`. -/
theorem normalizedHurwitzPoleRemovedFactor_isBigO_doubleExp
    (x : UnitAddCircle) :
    normalizedHurwitzPoleRemovedFactor x =O[
      Filter.comap (abs ∘ Complex.im) atTop ⊓
        Filter.principal
          (Complex.re ⁻¹' Set.Ioo (-1 / 2 : ℝ) (3 / 2 : ℝ))]
      fun z => Real.exp
        (1 * Real.exp ((3 / 2 : ℝ) * |z.im|)) := by
  obtain ⟨C, hC, hFactor⟩ := exists_hurwitzPoleRemovedFactor_exp_bound x
  let l : Filter ℂ :=
    Filter.comap (abs ∘ Complex.im) atTop ⊓
      Filter.principal
        (Complex.re ⁻¹' Set.Ioo (-1 / 2 : ℝ) (3 / 2 : ℝ))
  apply IsBigO.of_bound C
  have hheightComap :
      ∀ᶠ z : ℂ in Filter.comap (abs ∘ Complex.im) atTop,
        2 ≤ |z.im| := by
    rw [Filter.eventually_comap]
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
    intro z hz
    change |z.im| = y at hz
    rw [hz]
    exact hy
  have hheight : ∀ᶠ z : ℂ in l, 2 ≤ |z.im| :=
    hheightComap.filter_mono inf_le_left
  have hstrip : ∀ᶠ z : ℂ in l,
      z.re ∈ Set.Ioo (-1 / 2 : ℝ) (3 / 2 : ℝ) := by
    have hp : ∀ᶠ z : ℂ in
        Filter.principal (Complex.re ⁻¹' Set.Ioo (-1 / 2 : ℝ) (3 / 2 : ℝ)),
        z.re ∈ Set.Ioo (-1 / 2 : ℝ) (3 / 2 : ℝ) :=
      eventually_mem_principal _
    exact hp.filter_mono inf_le_right
  filter_upwards [hheight, hstrip] with z hz hzs
  have hzIcc : z.re ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ) :=
    ⟨hzs.1.le, hzs.2.le⟩
  have hzEq : z = estermannVerticalPoint z.re z.im := by
    apply Complex.ext <;> simp [estermannVerticalPoint]
  have hraw := hFactor z.re hzIcc z.im hz
  have hden : 1 ≤ ‖z + 2‖ := by
    rw [hzEq]
    exact one_le_norm_verticalPoint_add_two z.re z.im (by linarith [hzs.1])
  have hnormNormalized :
      ‖normalizedHurwitzPoleRemovedFactor x z‖ ≤
        C * (1 + |z.im|) * Real.exp (Real.pi * |z.im| / 2) := by
    unfold normalizedHurwitzPoleRemovedFactor
    rw [norm_div, norm_pow]
    have hdenSq : 1 ≤ ‖z + 2‖ ^ 2 := one_le_pow₀ hden
    calc
      ‖hurwitzPoleRemovedFactor x z‖ / ‖z + 2‖ ^ 2 ≤
          ‖hurwitzPoleRemovedFactor x z‖ :=
        div_le_self (norm_nonneg _) hdenSq
      _ ≤ C * (1 + |z.im|) * Real.exp (Real.pi * |z.im| / 2) := by
        rw [hzEq]
        simpa [estermannVerticalPoint] using hraw
  have hlinear :
      (1 + Real.pi / 2) * |z.im| ≤
        Real.exp ((3 / 2 : ℝ) * |z.im|) := by
    have hcoef : 1 + Real.pi / 2 ≤ 3 := by
      linarith [Real.pi_lt_four]
    have hfirst :
        (1 + Real.pi / 2) * |z.im| ≤ 3 * |z.im| :=
      mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
    have hexp :
        2 * ((3 / 2 : ℝ) * |z.im|) ≤
          Real.exp ((3 / 2 : ℝ) * |z.im|) := Real.two_mul_le_exp
    calc
      (1 + Real.pi / 2) * |z.im| ≤ 3 * |z.im| := hfirst
      _ = 2 * ((3 / 2 : ℝ) * |z.im|) := by ring
      _ ≤ Real.exp ((3 / 2 : ℝ) * |z.im|) := hexp
  calc
    ‖normalizedHurwitzPoleRemovedFactor x z‖ ≤
        C * (1 + |z.im|) * Real.exp (Real.pi * |z.im| / 2) :=
      hnormNormalized
    _ ≤ C * Real.exp |z.im| * Real.exp (Real.pi * |z.im| / 2) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left
          (by simpa [add_comm] using Real.add_one_le_exp |z.im|) hC
      · positivity
    _ = C * Real.exp ((1 + Real.pi / 2) * |z.im|) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring
    _ ≤ C * Real.exp (Real.exp ((3 / 2 : ℝ) * |z.im|)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hlinear) hC
    _ = C * ‖Real.exp
        (1 * Real.exp ((3 / 2 : ℝ) * |z.im|))‖ := by
      rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The final unconditional inhabitant of the a-priori growth package. -/
noncomputable def hurwitzPoleRemovedPhragmenLindelofGrowth :
    HurwitzPoleRemovedPhragmenLindelofGrowth where
  growth q _ r := by
    refine ⟨3 / 2, ?_, 1, ?_⟩
    · norm_num
      linarith [Real.pi_gt_three]
    · exact normalizedHurwitzPoleRemovedFactor_isBigO_doubleExp
        (ZMod.toAddCircle r)

/-- Hence the canonical Hurwitz strip has unconditional eventual polynomial
growth, with no remaining analytic hypothesis. -/
noncomputable def eventualHurwitzGrowth :
    HurwitzEventuallyVerticalStripGrowth (-1 / 2 : ℝ) (3 / 2 : ℝ) :=
  eventualHurwitzGrowth_of_plGrowth
    hurwitzPoleRemovedPhragmenLindelofGrowth

/-- The complete non-Gaussian Abel contour package, now with no classical
growth field left to instantiate. -/
noncomputable def abelContourLimitData
    {x : ℝ} (hx : 0 < x) (a q : ℕ) [NeZero q] :
    BettinConreyAbelContourLimitData x a q :=
  abelContourLimitData_of_eventualHurwitzGrowth
    eventualHurwitzGrowth hx a q

/-- The genuine infinite two-pole rectangle identity obtained from the
unconditional theta-kernel strip estimate. -/
theorem rightVertical_eq_damped_add_residues
    {x : ℝ} (hx : 0 < x) (a q : ℕ) [NeZero q] :
    estermannPrimalVerticalIntegral a q (3 / 2 : ℝ)
        (bettinConreyNormalizedAbelReflectionWeight x) =
      -(2 * Real.pi : ℝ) * dampedEstermannLambertSeries a q x +
        2 * Real.pi *
          (estermannWeightedResidueCoefficient a q
              (bettinConreyNormalizedAbelReflectionWeight x) +
            estermannHurwitzContinuation a q 0) :=
  rightVertical_eq_damped_add_residues_of_eventualHurwitzGrowth
    eventualHurwitzGrowth hx a q

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzPLGrowth
