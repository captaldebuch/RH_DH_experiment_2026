import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorHorizontalReflection
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelHorizontal

/-!
# Route C: intrinsic decay of the Taylor horizontal edges

This module turns the exact reflected-integrand identity into a uniform
bound on the finite Taylor rectangle.  The reciprocal half-angle cosine and
`Gamma (1-s)` each supply exponential rate `pi/2`; all other factors have
only fixed-strip radial cost or polynomial vertical growth.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorHorizontalDecay

open Complex Filter Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHorizontal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelHorizontal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorHorizontalReflection
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCanonicalStrip
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorMultiResidueRectangle
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues
open RH.Criteria.NymanBeurling.H14ZetaFETransport

/-! ## Reciprocal half-angle cosine -/

theorem norm_cos_add_mul_I_sq (a b : ℝ) :
    ‖Complex.cos ((a : ℂ) + (b : ℂ) * I)‖ ^ 2 =
      Real.cos a ^ 2 + Real.sinh b ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.cos_add_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rw [show
      ((Real.cos a * Real.cosh b : ℝ) : ℂ) -
          ((Real.sin a * Real.sinh b : ℝ) : ℂ) * I =
        ((Real.cos a * Real.cosh b : ℝ) : ℂ) +
          ((-Real.sin a * Real.sinh b : ℝ) : ℂ) * I by
            push_cast
            ring]
  rw [Complex.normSq_add_mul_I]
  nlinarith [Real.sin_sq_add_cos_sq a,
    Real.cosh_sq_sub_sinh_sq b]

theorem abs_sinh_le_norm_cos_add_mul_I (a b : ℝ) :
    |Real.sinh b| ≤
      ‖Complex.cos ((a : ℂ) + (b : ℂ) * I)‖ := by
  have hsq := norm_cos_add_mul_I_sq a b
  have habs : |Real.sinh b| ^ 2 = Real.sinh b ^ 2 := sq_abs _
  nlinarith [norm_nonneg
    (Complex.cos ((a : ℂ) + (b : ℂ) * I)), abs_nonneg (Real.sinh b),
    sq_nonneg (Real.cos a)]

theorem one_div_sinh_le_four_mul_exp_neg
    {x : ℝ} (hx : 1 ≤ x) :
    1 / Real.sinh x ≤ 4 * Real.exp (-x) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have htwo : 2 ≤ Real.exp (2 * x) := by
    calc
      2 ≤ 1 + 2 * x := by linarith
      _ ≤ Real.exp (2 * x) := by
        simpa [add_comm] using Real.add_one_le_exp (2 * x)
  have hinv : Real.exp (-(2 * x)) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos (2 * x))
      (by norm_num : (0 : ℝ) < 2)).2 htwo
  have hid :
      4 * Real.exp (-x) * Real.sinh x =
        2 * (1 - Real.exp (-(2 * x))) := by
    rw [Real.sinh_eq]
    have hcancel : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]
      simp
    have hdouble : Real.exp (-x) * Real.exp (-x) =
        Real.exp (-(2 * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show 4 * Real.exp (-x) *
        ((Real.exp x - Real.exp (-x)) / 2) =
          2 * (Real.exp (-x) * Real.exp x -
            Real.exp (-x) * Real.exp (-x)) by ring,
      hcancel, hdouble]
  apply (div_le_iff₀ (Real.sinh_pos_iff.mpr hx0)).2
  nlinarith [hid]

/-- Uniform reciprocal-cosine decay, independent of the horizontal real
part. -/
theorem one_div_norm_cos_half_horizontal_le
    (sigma t : ℝ) (ht : 1 ≤ |Real.pi * t / 2|) :
    1 / ‖Complex.cos ((Real.pi : ℂ) *
        ((sigma : ℂ) + (t : ℂ) * I) / 2)‖ ≤
      4 * Real.exp (-(Real.pi / 2) * |t|) := by
  let a : ℝ := Real.pi * sigma / 2
  let b : ℝ := Real.pi * t / 2
  have harg :
      (Real.pi : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) / 2 =
        (a : ℂ) + (b : ℂ) * I := by
    dsimp [a, b]
    push_cast
    ring
  rw [harg]
  have hbabs : |b| = Real.pi * |t| / 2 := by
    dsimp [b]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  have hb1 : 1 ≤ |b| := by simpa [b] using ht
  have hbsinh : 0 < |Real.sinh b| := by
    rw [abs_pos, ne_eq, Real.sinh_eq_zero]
    intro h
    have : |b| = 0 := by rw [h, abs_zero]
    linarith
  have hcos : 0 < ‖Complex.cos ((a : ℂ) + (b : ℂ) * I)‖ :=
    lt_of_lt_of_le hbsinh (abs_sinh_le_norm_cos_add_mul_I a b)
  calc
    1 / ‖Complex.cos ((a : ℂ) + (b : ℂ) * I)‖ ≤
        1 / |Real.sinh b| := by
      exact (div_le_div_iff₀ hcos hbsinh).2
        (by simpa using abs_sinh_le_norm_cos_add_mul_I a b)
    _ = 1 / Real.sinh |b| := by rw [Real.abs_sinh]
    _ ≤ 4 * Real.exp (-|b|) :=
      one_div_sinh_le_four_mul_exp_neg hb1
    _ = 4 * Real.exp (-(Real.pi / 2) * |t|) := by
      rw [hbabs]
      congr 2
      ring

/-! ## Gamma on the full finite Taylor strip -/

noncomputable def routeCTaylorGammaReference (M : ℕ) : ℝ :=
  2 * M + 3 / 2

theorem routeCTaylorGammaReference_pos (M : ℕ) :
    0 < routeCTaylorGammaReference M := by
  unfold routeCTaylorGammaReference
  positivity

theorem norm_gammaShiftProduct_threeHalves_le
    (M : ℕ) (t : ℝ) :
    ‖gammaShiftProduct (2 * M)
        (estermannVerticalPoint (3 / 2 : ℝ) t)‖ ≤
      (routeCTaylorGammaReference M + |t|) ^ (2 * M) := by
  unfold gammaShiftProduct
  rw [norm_prod]
  calc
    ∏ j ∈ Finset.range (2 * M),
        ‖estermannVerticalPoint (3 / 2 : ℝ) t + (j : ℂ)‖ ≤
      ∏ _j ∈ Finset.range (2 * M),
        (routeCTaylorGammaReference M + |t|) := by
          apply Finset.prod_le_prod
          · exact fun _ _ => norm_nonneg _
          · intro j hj
            have hjlt : j < 2 * M := Finset.mem_range.mp hj
            have hjle : (j : ℝ) ≤ 2 * M := by
              exact_mod_cast (Nat.le_of_lt hjlt)
            have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
            have hjpos : 0 ≤ 3 / 2 + (j : ℝ) := by positivity
            calc
              ‖estermannVerticalPoint (3 / 2 : ℝ) t + (j : ℂ)‖ ≤
                  |(estermannVerticalPoint (3 / 2 : ℝ) t +
                    (j : ℂ)).re| +
                    |(estermannVerticalPoint (3 / 2 : ℝ) t +
                      (j : ℂ)).im| :=
                Complex.norm_le_abs_re_add_abs_im _
              _ = 3 / 2 + (j : ℝ) + |t| := by
                simp [estermannVerticalPoint, abs_of_nonneg hjpos]
              _ ≤ routeCTaylorGammaReference M + |t| := by
                unfold routeCTaylorGammaReference
                linarith
    _ = (routeCTaylorGammaReference M + |t|) ^ (2 * M) := by
      rw [Finset.prod_const, Finset.card_range]

theorem norm_Gamma_routeCTaylorGammaReference_le
    (M : ℕ) (t : ℝ) :
    ‖Complex.Gamma
        (estermannVerticalPoint (routeCTaylorGammaReference M) t)‖ ≤
      (routeCTaylorGammaReference M + |t|) ^ (2 * M) *
        gammaThreeHalvesMajorant t := by
  let z : ℂ := estermannVerticalPoint (3 / 2 : ℝ) t
  have hz : ∀ j < 2 * M, z + (j : ℂ) ≠ 0 := by
    intro j _hj hzero
    have hre := congrArg Complex.re hzero
    simp [z, estermannVerticalPoint] at hre
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hrec := Gamma_add_nat_eq_gammaShiftProduct_mul (2 * M) z hz
  have hpoint : z + (2 * M : ℕ) =
      estermannVerticalPoint (routeCTaylorGammaReference M) t := by
    dsimp [z, estermannVerticalPoint, routeCTaylorGammaReference]
    push_cast
    ring
  have hprod := norm_gammaShiftProduct_threeHalves_le M t
  have hgamma : ‖Complex.Gamma z‖ ≤ gammaThreeHalvesMajorant t := by
    simpa [z, estermannVerticalPoint, mul_comm] using
      norm_Gamma_three_halves_add_I_mul_le_majorant t
  rw [hpoint] at hrec
  rw [hrec, norm_mul]
  exact mul_le_mul hprod hgamma (norm_nonneg _)
    (pow_nonneg (add_nonneg (routeCTaylorGammaReference_pos M).le
      (abs_nonneg t)) _)

/-- Gamma has intrinsic rate `pi/2` uniformly throughout the complete
positive strip reached after reflecting the order-`M` Taylor rectangle. -/
theorem exists_gamma_routeCTaylor_horizontal_strip_bound
    (M : ℕ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ c ∈ Set.Icc (3 / 2 : ℝ) (2 * M + 1 / 2 : ℝ),
        ∀ t : ℝ,
          ‖Complex.Gamma (estermannVerticalPoint c t)‖ ≤
            C * (routeCTaylorGammaReference M + |t|) ^ (2 * M) *
              (1 + |t|) *
                Real.exp (-(Real.pi / 2) * |t|) := by
  let K : Set ℝ := Set.Icc (3 / 2 : ℝ) (2 * M + 1 / 2 : ℝ)
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hKne : K.Nonempty := nonempty_Icc.mpr (by linarith)
  have hKpos : K ⊆ Set.Ioi 0 := by
    intro c hc
    exact Set.mem_Ioi.mpr (by linarith [hc.1])
  have hcont : ContinuousOn Real.Gamma K :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono hKpos
  obtain ⟨c₀, hc₀, hcmax⟩ := isCompact_Icc.exists_isMaxOn hKne hcont
  let R : ℝ := routeCTaylorGammaReference M
  have hRpos : 0 < R := routeCTaylorGammaReference_pos M
  have hGammaR : 0 < Real.Gamma R := Real.Gamma_pos_of_pos hRpos
  let C : ℝ := Real.Gamma c₀ / Real.Gamma R *
    Real.sqrt (2 * Real.pi)
  have hc₀pos : 0 < c₀ := by linarith [hc₀.1]
  have hGammaC₀ : 0 < Real.Gamma c₀ := Real.Gamma_pos_of_pos hc₀pos
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro c hc t
  let u : ℂ := estermannVerticalPoint c t
  let v : ℝ := R - c
  have hu : 0 < u.re := by
    simp [u, estermannVerticalPoint]
    linarith [hc.1]
  have hv : 0 < v := by
    dsimp [v, R, routeCTaylorGammaReference]
    linarith [hc.2]
  have hsum : u + (v : ℂ) = estermannVerticalPoint R t := by
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
  have hru : u.re = c := by simp [u, estermannVerticalPoint]
  have hvre : (v : ℂ).re = v := by simp
  rw [hru, hvre, show c + v = R by dsimp [v]; ring] at hbetaNorm
  have hmul :
      ‖Complex.Gamma u‖ * Real.Gamma v ≤
        ‖Complex.Gamma (estermannVerticalPoint R t)‖ *
          (Real.Gamma c * Real.Gamma v / Real.Gamma R) := by
    calc
      ‖Complex.Gamma u‖ * Real.Gamma v =
          ‖Complex.Gamma u * Complex.Gamma (v : ℂ)‖ := by
            rw [norm_mul, hnormv]
      _ = ‖Complex.Gamma (estermannVerticalPoint R t)‖ *
          ‖Complex.betaIntegral u (v : ℂ)‖ := by
            rw [hbeta, hsum, norm_mul]
      _ ≤ ‖Complex.Gamma (estermannVerticalPoint R t)‖ *
          (Real.Gamma c * Real.Gamma v / Real.Gamma R) :=
        mul_le_mul_of_nonneg_left hbetaNorm (norm_nonneg _)
  have hcGamma : Real.Gamma c ≤ Real.Gamma c₀ := hcmax hc
  have hquotNonneg : 0 ≤
      ‖Complex.Gamma (estermannVerticalPoint R t)‖ /
        Real.Gamma R := by positivity
  have hcancel :
      ‖Complex.Gamma u‖ ≤
        ‖Complex.Gamma (estermannVerticalPoint R t)‖ *
          Real.Gamma c₀ / Real.Gamma R := by
    have hmul' :
        ‖Complex.Gamma u‖ * Real.Gamma v ≤
          (‖Complex.Gamma (estermannVerticalPoint R t)‖ *
            Real.Gamma c₀ / Real.Gamma R) * Real.Gamma v := by
      calc
        ‖Complex.Gamma u‖ * Real.Gamma v ≤
            ‖Complex.Gamma (estermannVerticalPoint R t)‖ *
              (Real.Gamma c * Real.Gamma v / Real.Gamma R) := hmul
        _ ≤ ‖Complex.Gamma (estermannVerticalPoint R t)‖ *
              (Real.Gamma c₀ * Real.Gamma v / Real.Gamma R) := by
            gcongr
        _ = (‖Complex.Gamma (estermannVerticalPoint R t)‖ *
              Real.Gamma c₀ / Real.Gamma R) * Real.Gamma v := by ring
    nlinarith
  have href := norm_Gamma_routeCTaylorGammaReference_le M t
  unfold gammaThreeHalvesMajorant at href
  calc
    ‖Complex.Gamma (estermannVerticalPoint c t)‖ =
        ‖Complex.Gamma u‖ := rfl
    _ ≤ ‖Complex.Gamma (estermannVerticalPoint R t)‖ *
          Real.Gamma c₀ / Real.Gamma R := hcancel
    _ ≤ ((routeCTaylorGammaReference M + |t|) ^ (2 * M) *
          (Real.sqrt (2 * Real.pi) * (1 + |t|) *
            Real.exp (-(Real.pi / 2) * |t|))) *
          Real.Gamma c₀ / Real.Gamma R := by
        have hscaled := mul_le_mul_of_nonneg_right href
          (div_nonneg hGammaC₀.le hGammaR.le)
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
    _ = C * (routeCTaylorGammaReference M + |t|) ^ (2 * M) *
          (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
        dsimp [C]
        ring

/-! ## The remaining reflected factors -/

noncomputable def routeCTaylorBaseStripBound : ℝ :=
  Real.rpow (2 * Real.pi) (-(3 / 2 : ℝ))

theorem routeCTaylorBaseStripBound_nonneg :
    0 ≤ routeCTaylorBaseStripBound := by
  unfold routeCTaylorBaseStripBound
  exact Real.rpow_nonneg (by positivity) _

theorem norm_two_pi_cpow_horizontal_le
    (sigma t : ℝ) (hsigma : sigma ≤ -(1 / 2 : ℝ)) :
    ‖(2 * (Real.pi : ℂ)) ^
        (((sigma : ℂ) + (t : ℂ) * I) - 1)‖ ≤
      routeCTaylorBaseStripBound := by
  have hbase : (0 : ℝ) < 2 * Real.pi := by positivity
  have hbaseOne : (1 : ℝ) ≤ 2 * Real.pi := by
    linarith [Real.pi_gt_three]
  have hcast : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hbase]
  have hre :
      ((((sigma : ℂ) + (t : ℂ) * I) - 1)).re = sigma - 1 := by
    simp [Complex.mul_re]
  rw [hre]
  unfold routeCTaylorBaseStripBound
  exact Real.rpow_le_rpow_of_exponent_le hbaseOne (by linarith)

theorem norm_riemannZeta_one_sub_horizontal_le
    (sigma t : ℝ) (hsigma : sigma ≤ -(1 / 2 : ℝ)) :
    ‖riemannZeta
        (1 - ((sigma : ℂ) + (t : ℂ) * I))‖ ≤ 9 := by
  apply norm_riemannZeta_le_of_re_ge
  simp [Complex.mul_re]
  linarith

noncomputable def routeCTaylorPowerRadialBound
    (u : ℂ) (M : ℕ) : ℝ :=
  max (Real.rpow ‖u‖ (1 / 2 : ℝ))
    (Real.rpow ‖u‖ (2 * M - 1 / 2 : ℝ))

theorem routeCTaylorPowerRadialBound_nonneg (u : ℂ) (M : ℕ) :
    0 ≤ routeCTaylorPowerRadialBound u M := by
  unfold routeCTaylorPowerRadialBound
  exact le_max_of_le_left (Real.rpow_nonneg (norm_nonneg _) _)

theorem norm_cpow_neg_taylor_horizontal_le
    {u : ℂ} (hu : u ≠ 0) (M : ℕ) {theta : ℝ}
    (harg : |Complex.arg u| ≤ theta)
    (sigma t : ℝ)
    (hsigma : sigma ∈
      Set.Icc (routeCTaylorCanonicalLeft M)
        routeCTaylorCanonicalRight) :
    ‖u ^ (-((sigma : ℂ) + (t : ℂ) * I))‖ ≤
      routeCTaylorPowerRadialBound u M *
        Real.exp (theta * |t|) := by
  have hnormu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  rw [Complex.norm_cpow_of_ne_zero hu]
  have hre : (-((sigma : ℂ) + (t : ℂ) * I)).re = -sigma := by
    simp [Complex.mul_re]
  have him : (-((sigma : ℂ) + (t : ℂ) * I)).im = -t := by
    simp [Complex.mul_im]
  rw [hre, him, div_eq_mul_inv, ← Real.exp_neg]
  have hexp : -(Complex.arg u * -t) = Complex.arg u * t := by ring
  rw [hexp]
  have hlower : (1 / 2 : ℝ) ≤ -sigma := by
    unfold routeCTaylorCanonicalRight at hsigma
    linarith [hsigma.2]
  have hupper : -sigma ≤ (2 * M - 1 / 2 : ℝ) := by
    unfold routeCTaylorCanonicalLeft at hsigma
    linarith [hsigma.1]
  have hradial :
      Real.rpow ‖u‖ (-sigma) ≤ routeCTaylorPowerRadialBound u M := by
    by_cases hone : 1 ≤ ‖u‖
    · apply le_max_of_le_right
      exact Real.rpow_le_rpow_of_exponent_le hone hupper
    · have hle : ‖u‖ ≤ 1 := le_of_not_ge hone
      apply le_max_of_le_left
      exact Real.rpow_le_rpow_of_exponent_ge hnormu hle hlower
  have hang : Real.exp (Complex.arg u * t) ≤
      Real.exp (theta * |t|) := by
    apply Real.exp_le_exp.mpr
    calc
      Complex.arg u * t ≤ |Complex.arg u| * |t| := by
        simpa [abs_mul] using le_abs_self (Complex.arg u * t)
      _ ≤ theta * |t| :=
        mul_le_mul_of_nonneg_right harg (abs_nonneg t)
  exact mul_le_mul hradial hang (Real.exp_pos _).le
    (routeCTaylorPowerRadialBound_nonneg u M)

theorem reflectedGamma_real_mem_taylorStrip
    (M : ℕ) {sigma : ℝ}
    (hsigma : sigma ∈
      Set.Icc (routeCTaylorCanonicalLeft M)
        routeCTaylorCanonicalRight) :
    1 - sigma ∈ Set.Icc (3 / 2 : ℝ) (2 * M + 1 / 2 : ℝ) := by
  unfold routeCTaylorCanonicalLeft routeCTaylorCanonicalRight at hsigma
  constructor <;> linarith [hsigma.1, hsigma.2]

/-! ## Assembly of the complete horizontal row -/

noncomputable def routeCTaylorHorizontalConstant
    (Cgamma : ℝ) (u : ℂ) (M : ℕ) : ℝ :=
  routeCTaylorBaseStripBound * Cgamma * 81 * 4 *
    routeCTaylorPowerRadialBound u M *
      (routeCTaylorGammaReference M + 1) ^ (2 * M) * 2

theorem routeCTaylorHorizontalConstant_nonneg
    {Cgamma : ℝ} (hCgamma : 0 ≤ Cgamma) (u : ℂ) (M : ℕ) :
    0 ≤ routeCTaylorHorizontalConstant Cgamma u M := by
  unfold routeCTaylorHorizontalConstant
  have hR : 0 ≤ routeCTaylorGammaReference M + 1 := by
    linarith [routeCTaylorGammaReference_pos M]
  have h1 : 0 ≤ routeCTaylorBaseStripBound * Cgamma :=
    mul_nonneg routeCTaylorBaseStripBound_nonneg hCgamma
  have h2 : 0 ≤ routeCTaylorBaseStripBound * Cgamma * 81 :=
    mul_nonneg h1 (by norm_num)
  have h3 : 0 ≤ routeCTaylorBaseStripBound * Cgamma * 81 * 4 :=
    mul_nonneg h2 (by norm_num)
  have h4 : 0 ≤ routeCTaylorBaseStripBound * Cgamma * 81 * 4 *
      routeCTaylorPowerRadialBound u M :=
    mul_nonneg h3 (routeCTaylorPowerRadialBound_nonneg u M)
  have h5 : 0 ≤ routeCTaylorBaseStripBound * Cgamma * 81 * 4 *
      routeCTaylorPowerRadialBound u M *
        (routeCTaylorGammaReference M + 1) ^ (2 * M) :=
    mul_nonneg h4 (pow_nonneg hR _)
  exact mul_nonneg h5 (by norm_num)

theorem routeCTaylor_horizontal_polynomial_le
    (M : ℕ) (t : ℝ) (ht : 1 ≤ |t|) :
    (routeCTaylorGammaReference M + |t|) ^ (2 * M) *
        (1 + |t|) ≤
      (routeCTaylorGammaReference M + 1) ^ (2 * M) * 2 *
        |t| ^ (2 * M + 1) := by
  have hR : 0 ≤ routeCTaylorGammaReference M :=
    (routeCTaylorGammaReference_pos M).le
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hbase : routeCTaylorGammaReference M + |t| ≤
      (routeCTaylorGammaReference M + 1) * |t| := by
    nlinarith
  have hone : 1 + |t| ≤ 2 * |t| := by linarith
  have hpow :
      (routeCTaylorGammaReference M + |t|) ^ (2 * M) ≤
        ((routeCTaylorGammaReference M + 1) * |t|) ^ (2 * M) :=
    pow_le_pow_left₀ (add_nonneg hR ht0) hbase _
  calc
    (routeCTaylorGammaReference M + |t|) ^ (2 * M) *
        (1 + |t|) ≤
      ((routeCTaylorGammaReference M + 1) * |t|) ^ (2 * M) *
        (2 * |t|) :=
      mul_le_mul hpow hone (by positivity) (by positivity)
    _ = (routeCTaylorGammaReference M + 1) ^ (2 * M) * 2 *
        |t| ^ (2 * M + 1) := by
      rw [mul_pow, pow_succ]
      ring

theorem norm_bettinConreyGZero_horizontal_le
    (u : ℂ) (hu : u ≠ 0) (M : ℕ)
    {theta : ℝ} (harg : |Complex.arg u| ≤ theta)
    (Cgamma : ℝ) (hCgamma : 0 ≤ Cgamma)
    (hgamma : ∀ c ∈ Set.Icc (3 / 2 : ℝ) (2 * M + 1 / 2 : ℝ),
      ∀ t : ℝ,
        ‖Complex.Gamma (estermannVerticalPoint c t)‖ ≤
          Cgamma * (routeCTaylorGammaReference M + |t|) ^ (2 * M) *
            (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|))
    (sigma t : ℝ)
    (hsigma : sigma ∈ Set.Icc (routeCTaylorCanonicalLeft M)
      routeCTaylorCanonicalRight)
    (ht : 1 ≤ |t|) :
    ‖bettinConreyGZeroMeromorphicIntegrand u
        ((sigma : ℂ) + (t : ℂ) * I)‖ ≤
      routeCTaylorHorizontalConstant Cgamma u M *
        |t| ^ (2 * M + 1) *
          Real.exp (-(Real.pi - theta) * |t|) := by
  let s : ℂ := (sigma : ℂ) + (t : ℂ) * I
  have him : s.im ≠ 0 := by
    have ht0 : t ≠ 0 := by
      exact abs_pos.mp (lt_of_lt_of_le zero_lt_one ht)
    simpa [s] using ht0
  rw [bettinConreyGZeroMeromorphicIntegrand_eq_reflected u s him]
  have hsigmaRight : sigma ≤ -(1 / 2 : ℝ) := by
    unfold routeCTaylorCanonicalRight at hsigma
    linarith [hsigma.2]
  have hbase := norm_two_pi_cpow_horizontal_le sigma t hsigmaRight
  have hgammaPoint := hgamma (1 - sigma)
    (reflectedGamma_real_mem_taylorStrip M hsigma) (-t)
  have hgamma' :
      ‖Complex.Gamma (1 - s)‖ ≤
        Cgamma * (routeCTaylorGammaReference M + |t|) ^ (2 * M) *
          (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
    convert hgammaPoint using 1 <;>
      simp [s, estermannVerticalPoint, abs_neg] <;> ring
  have hzeta := norm_riemannZeta_one_sub_horizontal_le
    sigma t hsigmaRight
  have hzetaSq : ‖riemannZeta (1 - s)‖ ^ 2 ≤ 81 := by
    have hzeta' : ‖riemannZeta (1 - s)‖ ≤ 9 := by
      simpa [s] using hzeta
    nlinarith [norm_nonneg (riemannZeta (1 - s))]
  have hpiHalf : (1 : ℝ) ≤ Real.pi / 2 := by
    linarith [Real.pi_gt_three]
  have hcosHeight : 1 ≤ |Real.pi * t / 2| := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
    calc
      1 ≤ |t| := ht
      _ ≤ Real.pi / 2 * |t| := by
        exact le_mul_of_one_le_left (abs_nonneg t) hpiHalf
      _ = Real.pi * |t| / 2 := by ring
  have hcos := one_div_norm_cos_half_horizontal_le
    sigma t hcosHeight
  have hpower := norm_cpow_neg_taylor_horizontal_le
    hu M harg sigma t hsigma
  have hraw :
      ‖bettinConreyGZeroReflectedIntegrand u s‖ ≤
        (routeCTaylorBaseStripBound * Cgamma * 81 * 4 *
          routeCTaylorPowerRadialBound u M) *
        ((routeCTaylorGammaReference M + |t|) ^ (2 * M) *
          (1 + |t|)) *
        (Real.exp (-(Real.pi / 2) * |t|) *
          Real.exp (-(Real.pi / 2) * |t|) *
          Real.exp (theta * |t|)) := by
    unfold bettinConreyGZeroReflectedIntegrand
    rw [norm_mul, norm_div, norm_mul, norm_mul, norm_pow]
    rw [div_eq_mul_inv, ← one_div]
    have hgammaNonneg : 0 ≤
        Cgamma * (routeCTaylorGammaReference M + |t|) ^ (2 * M) *
          (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
      have hR : 0 ≤ routeCTaylorGammaReference M + |t| :=
        add_nonneg (routeCTaylorGammaReference_pos M).le (abs_nonneg t)
      positivity
    have hpowerNonneg : 0 ≤
        routeCTaylorPowerRadialBound u M *
          Real.exp (theta * |t|) := by
      exact mul_nonneg (routeCTaylorPowerRadialBound_nonneg u M)
        (Real.exp_pos _).le
    have hbase' :
        ‖(2 * (Real.pi : ℂ)) ^ (s - 1)‖ ≤
          routeCTaylorBaseStripBound := by
      simpa [s] using hbase
    have hcos' :
        1 / ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ≤
          4 * Real.exp (-(Real.pi / 2) * |t|) := by
      simpa [s] using hcos
    have hpower' :
        ‖u ^ (-s)‖ ≤ routeCTaylorPowerRadialBound u M *
          Real.exp (theta * |t|) := by
      simpa [s] using hpower
    have hAB := mul_le_mul hbase' hgamma'
      (norm_nonneg (Complex.Gamma (1 - s)))
      routeCTaylorBaseStripBound_nonneg
    have hABC := mul_le_mul hAB hzetaSq
      (sq_nonneg ‖riemannZeta (1 - s)‖)
      (mul_nonneg routeCTaylorBaseStripBound_nonneg hgammaNonneg)
    have hABCD := mul_le_mul hABC hcos'
      (by positivity : 0 ≤ 1 / ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖)
      (mul_nonneg
        (mul_nonneg routeCTaylorBaseStripBound_nonneg hgammaNonneg)
        (by norm_num : (0 : ℝ) ≤ 81))
    have hABCDE := mul_le_mul hABCD hpower'
      (norm_nonneg (u ^ (-s)))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg routeCTaylorBaseStripBound_nonneg hgammaNonneg)
          (by norm_num : (0 : ℝ) ≤ 81))
        (by positivity : 0 ≤ 4 * Real.exp (-(Real.pi / 2) * |t|)))
    calc
      ‖(2 * (Real.pi : ℂ)) ^ (s - 1)‖ *
            ‖Complex.Gamma (1 - s)‖ *
            ‖riemannZeta (1 - s)‖ ^ 2 *
            (1 / ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖) *
            ‖u ^ (-s)‖ ≤
          routeCTaylorBaseStripBound *
            (Cgamma * (routeCTaylorGammaReference M + |t|) ^ (2 * M) *
              (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) *
            81 * (4 * Real.exp (-(Real.pi / 2) * |t|)) *
            (routeCTaylorPowerRadialBound u M *
              Real.exp (theta * |t|)) := hABCDE
      _ = _ := by ring
  have hpoly := routeCTaylor_horizontal_polynomial_le M t ht
  have hconstant : 0 ≤
      routeCTaylorBaseStripBound * Cgamma * 81 * 4 *
        routeCTaylorPowerRadialBound u M := by
    have h1 : 0 ≤ routeCTaylorBaseStripBound * Cgamma :=
      mul_nonneg routeCTaylorBaseStripBound_nonneg hCgamma
    have h2 : 0 ≤ routeCTaylorBaseStripBound * Cgamma * 81 :=
      mul_nonneg h1 (by norm_num)
    have h3 : 0 ≤ routeCTaylorBaseStripBound * Cgamma * 81 * 4 :=
      mul_nonneg h2 (by norm_num)
    exact mul_nonneg h3 (routeCTaylorPowerRadialBound_nonneg u M)
  have hexp :
      Real.exp (-(Real.pi / 2) * |t|) *
          Real.exp (-(Real.pi / 2) * |t|) *
          Real.exp (theta * |t|) =
        Real.exp (-(Real.pi - theta) * |t|) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    ‖bettinConreyGZeroReflectedIntegrand u s‖ ≤
        (routeCTaylorBaseStripBound * Cgamma * 81 * 4 *
          routeCTaylorPowerRadialBound u M) *
        ((routeCTaylorGammaReference M + |t|) ^ (2 * M) *
          (1 + |t|)) *
        (Real.exp (-(Real.pi / 2) * |t|) *
          Real.exp (-(Real.pi / 2) * |t|) *
          Real.exp (theta * |t|)) := hraw
    _ ≤ (routeCTaylorBaseStripBound * Cgamma * 81 * 4 *
          routeCTaylorPowerRadialBound u M) *
        ((routeCTaylorGammaReference M + 1) ^ (2 * M) * 2 *
          |t| ^ (2 * M + 1)) *
        (Real.exp (-(Real.pi / 2) * |t|) *
          Real.exp (-(Real.pi / 2) * |t|) *
          Real.exp (theta * |t|)) := by
      gcongr
    _ = routeCTaylorHorizontalConstant Cgamma u M *
        |t| ^ (2 * M + 1) *
          Real.exp (-(Real.pi - theta) * |t|) := by
      rw [hexp]
      unfold routeCTaylorHorizontalConstant
      ring

/-- The two oriented horizontal sides of the genuine finite Taylor
rectangle vanish unconditionally in every closed angular sector strictly
inside the principal slit plane. -/
theorem bettinConreyGZero_horizontal_pair_vanishes
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (hM : 1 ≤ M)
    {theta : ℝ} (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi) :
    Tendsto
      (symmetricHorizontalEdges
        (bettinConreyGZeroMeromorphicIntegrand u)
        (routeCTaylorCanonicalLeft M)
        routeCTaylorCanonicalRight)
      atTop (nhds 0) := by
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    exists_gamma_routeCTaylor_horizontal_strip_bound M hM
  let majorant : ℝ → ℝ :=
    abelHorizontalPolynomialExponentialMajorant
      (routeCTaylorHorizontalConstant Cgamma u M)
      (2 * M + 1) (Real.pi - theta)
  apply horizontal_pair_vanishes_of_eventual_majorant
    (bettinConreyGZeroMeromorphicIntegrand u)
    (routeCTaylorCanonicalLeft M) routeCTaylorCanonicalRight
    majorant
  · unfold routeCTaylorCanonicalLeft routeCTaylorCanonicalRight
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    refine ⟨by linarith, ?_⟩
    intro sigma hsigma
    have hTabs : |T| = T := abs_of_nonneg (by linarith)
    have hupper := norm_bettinConreyGZero_horizontal_le
      u hu M harg Cgamma hCgamma hgamma sigma T hsigma (by
        rw [hTabs]
        exact hT)
    have hlower := norm_bettinConreyGZero_horizontal_le
      u hu M harg Cgamma hCgamma hgamma sigma (-T) hsigma (by
        simpa [abs_neg, hTabs] using hT)
    constructor
    · simpa [majorant, abelHorizontalPolynomialExponentialMajorant,
        hTabs] using hupper
    · simpa [majorant, abelHorizontalPolynomialExponentialMajorant,
        abs_neg, hTabs, sub_eq_add_neg] using hlower
  · dsimp [majorant]
    exact tendsto_abelHorizontalPolynomialExponentialMajorant
      (routeCTaylorHorizontalConstant Cgamma u M)
      (2 * M + 1) (sub_pos.mpr htheta)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorHorizontalDecay
