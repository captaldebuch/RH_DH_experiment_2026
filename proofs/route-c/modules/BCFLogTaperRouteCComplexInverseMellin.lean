import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Convex
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelComplexDamping

/-!
# Route C: complex inverse Mellin for the Abel exponential

For `w` in the horizontal strip `|Im w| < pi/2`, the scalar integral

`integral Gamma(3/2+it) * exp(-(3/2+it)w) dt`

is the logarithmic-coordinate form of the complex inverse-Mellin theorem.
This module first proves its absolute convergence with the exact angular
gap `pi/2-|Im w|` and records its equality on the real axis.  These are the
two inputs for the subsequent holomorphic identity-theorem step.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexInverseMellin

open Complex Filter MeasureTheory Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine

/-- The scalar Gamma inverse-Mellin integrand in logarithmic coordinates. -/
noncomputable def complexGammaMellinIntegrand (w : ℂ) (t : ℝ) : ℂ :=
  let s := estermannVerticalPoint (3 / 2 : ℝ) t
  Complex.exp (-s * w) * Complex.Gamma s

/-- Its full vertical integral. -/
noncomputable def complexGammaMellinIntegral (w : ℂ) : ℂ :=
  ∫ t : ℝ, complexGammaMellinIntegrand w t

/-- Explicit absolute majorant, retaining the exact distance from the
boundary of the logarithmic strip. -/
noncomputable def complexGammaMellinMajorant (w : ℂ) (t : ℝ) : ℝ :=
  (Real.exp (-(3 / 2 : ℝ) * w.re) * Real.sqrt (2 * Real.pi)) *
    abelPolynomialExponentialMajorant 1
      (Real.pi / 2 - |w.im|) t

/-- The exponential factor costs precisely the angular growth
`exp(|Im w|*|t|)` on the vertical line. -/
theorem norm_exp_neg_vertical_mul_le (w : ℂ) (t : ℝ) :
    ‖Complex.exp
        (-estermannVerticalPoint (3 / 2 : ℝ) t * w)‖ ≤
      Real.exp (-(3 / 2 : ℝ) * w.re + |w.im| * |t|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hmul : t * w.im ≤ |t| * |w.im| := by
    calc
      t * w.im ≤ |t * w.im| := le_abs_self _
      _ = |t| * |w.im| := abs_mul _ _
  have hre :
      (-estermannVerticalPoint (3 / 2 : ℝ) t * w).re =
        -(3 / 2 : ℝ) * w.re + t * w.im := by
    unfold estermannVerticalPoint
    norm_num
  rw [hre]
  linarith

/-- Pointwise domination by the strip majorant. -/
theorem norm_complexGammaMellinIntegrand_le (w : ℂ) (t : ℝ) :
    ‖complexGammaMellinIntegrand w t‖ ≤
      complexGammaMellinMajorant w t := by
  have hexp := norm_exp_neg_vertical_mul_le w t
  have hgamma := norm_Gamma_three_halves_add_I_mul_le_majorant t
  have hexpNonneg :
      0 ≤ Real.exp (-(3 / 2 : ℝ) * w.re + |w.im| * |t|) := by
    positivity
  have hprod := mul_le_mul hexp hgamma (norm_nonneg _) hexpNonneg
  unfold complexGammaMellinIntegrand
  dsimp only
  rw [norm_mul]
  calc
    ‖Complex.exp
          (-estermannVerticalPoint (3 / 2 : ℝ) t * w)‖ *
        ‖Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t)‖ ≤
      Real.exp (-(3 / 2 : ℝ) * w.re + |w.im| * |t|) *
        gammaThreeHalvesMajorant t := by
      simpa [estermannVerticalPoint, mul_comm (t : ℂ) Complex.I] using hprod
    _ = complexGammaMellinMajorant w t := by
      unfold complexGammaMellinMajorant gammaThreeHalvesMajorant
        abelPolynomialExponentialMajorant
      have hhead :
          Real.exp (-(3 / 2 : ℝ) * w.re + |w.im| * |t|) =
            Real.exp (-(3 / 2 : ℝ) * w.re) *
              Real.exp (|w.im| * |t|) := by
        rw [Real.exp_add]
      have htail :
          Real.exp (-(Real.pi / 2 - |w.im|) * |t|) =
            Real.exp (-(Real.pi / 2) * |t|) *
              Real.exp (|w.im| * |t|) := by
        rw [show -(Real.pi / 2 - |w.im|) * |t| =
            -(Real.pi / 2) * |t| + |w.im| * |t| by ring]
        rw [Real.exp_add]
      rw [hhead, htail]
      norm_num
      ring

/-- Derivative of the scalar integrand with respect to the logarithmic
parameter. -/
noncomputable def complexGammaMellinDerivIntegrand
    (w : ℂ) (t : ℝ) : ℂ :=
  let s := estermannVerticalPoint (3 / 2 : ℝ) t
  (-s) * Complex.exp (-s * w) * Complex.Gamma s

/-- A locally uniform majorant for the derivative on a closed substrip and
to the right of a fixed real lower bound. -/
noncomputable def complexGammaMellinDerivMajorant
    (lower theta : ℝ) (t : ℝ) : ℝ :=
  (2 * Real.exp (-(3 / 2 : ℝ) * lower) *
      Real.sqrt (2 * Real.pi)) *
    abelPolynomialExponentialMajorant 2
      (Real.pi / 2 - theta) t

theorem norm_verticalPoint_le (t : ℝ) :
    ‖estermannVerticalPoint (3 / 2 : ℝ) t‖ ≤
      2 * (1 + |t|) := by
  calc
    ‖estermannVerticalPoint (3 / 2 : ℝ) t‖ ≤
        |(estermannVerticalPoint (3 / 2 : ℝ) t).re| +
          |(estermannVerticalPoint (3 / 2 : ℝ) t).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = (3 / 2 : ℝ) + |t| := by
      norm_num [estermannVerticalPoint, abs_of_nonneg]
    _ ≤ 2 * (1 + |t|) := by
      linarith [abs_nonneg t]

/-- The derivative has a polynomial-times-exponential bound uniform on
every smaller strip. -/
theorem norm_complexGammaMellinDerivIntegrand_le
    {w : ℂ} {lower theta : ℝ}
    (hre : lower ≤ w.re) (him : |w.im| ≤ theta) (t : ℝ) :
    ‖complexGammaMellinDerivIntegrand w t‖ ≤
      complexGammaMellinDerivMajorant lower theta t := by
  have hexp :
      ‖Complex.exp
          (-estermannVerticalPoint (3 / 2 : ℝ) t * w)‖ ≤
        Real.exp (-(3 / 2 : ℝ) * lower + theta * |t|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have htw : t * w.im ≤ |t| * |w.im| := by
      calc
        t * w.im ≤ |t * w.im| := le_abs_self _
        _ = |t| * |w.im| := abs_mul _ _
    have htheta : |t| * |w.im| ≤ |t| * theta :=
      mul_le_mul_of_nonneg_left him (abs_nonneg t)
    have hreal :
        (-estermannVerticalPoint (3 / 2 : ℝ) t * w).re =
          -(3 / 2 : ℝ) * w.re + t * w.im := by
      unfold estermannVerticalPoint
      norm_num
    rw [hreal]
    nlinarith
  have hs := norm_verticalPoint_le t
  have hgamma := norm_Gamma_three_halves_add_I_mul_le_majorant t
  have hexpNonneg :
      0 ≤ Real.exp (-(3 / 2 : ℝ) * lower + theta * |t|) := by
    positivity
  have hsNonneg : 0 ≤ 2 * (1 + |t|) := by positivity
  have hfirst := mul_le_mul hs hexp (norm_nonneg _) hsNonneg
  have hsecond := mul_le_mul hfirst hgamma
    (norm_nonneg _) (mul_nonneg hsNonneg hexpNonneg)
  unfold complexGammaMellinDerivIntegrand
  dsimp only
  rw [norm_mul, norm_mul, norm_neg]
  calc
    ‖estermannVerticalPoint (3 / 2 : ℝ) t‖ *
          ‖Complex.exp
            (-estermannVerticalPoint (3 / 2 : ℝ) t * w)‖ *
        ‖Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t)‖ ≤
      (2 * (1 + |t|)) *
          Real.exp (-(3 / 2 : ℝ) * lower + theta * |t|) *
        gammaThreeHalvesMajorant t := by
      simpa [estermannVerticalPoint, mul_comm (t : ℂ) Complex.I] using hsecond
    _ = complexGammaMellinDerivMajorant lower theta t := by
      unfold complexGammaMellinDerivMajorant gammaThreeHalvesMajorant
        abelPolynomialExponentialMajorant
      have hhead :
          Real.exp (-(3 / 2 : ℝ) * lower + theta * |t|) =
            Real.exp (-(3 / 2 : ℝ) * lower) *
              Real.exp (theta * |t|) := by
        rw [Real.exp_add]
      have htail :
          Real.exp (-(Real.pi / 2 - theta) * |t|) =
            Real.exp (-(Real.pi / 2) * |t|) *
              Real.exp (theta * |t|) := by
        rw [show -(Real.pi / 2 - theta) * |t| =
            -(Real.pi / 2) * |t| + theta * |t| by ring]
        rw [Real.exp_add]
      rw [hhead, htail]
      ring

theorem integrable_complexGammaMellinDerivMajorant
    (lower : ℝ) {theta : ℝ} (htheta : theta < Real.pi / 2) :
    Integrable (complexGammaMellinDerivMajorant lower theta) := by
  unfold complexGammaMellinDerivMajorant
  exact (integrable_abelPolynomialExponentialMajorant 2
    (sub_pos.mpr htheta)).const_mul _

/-- Pointwise complex derivative of the scalar integrand. -/
theorem hasDerivAt_complexGammaMellinIntegrand
    (w : ℂ) (t : ℝ) :
    HasDerivAt (fun z : ℂ => complexGammaMellinIntegrand z t)
      (complexGammaMellinDerivIntegrand w t) w := by
  let s := estermannVerticalPoint (3 / 2 : ℝ) t
  have hinner : HasDerivAt (fun z : ℂ => -s * z) (-s) w := by
    simpa using (hasDerivAt_id w).const_mul (-s)
  have hexp := (Complex.hasDerivAt_exp (-s * w)).comp w hinner
  have htotal := hexp.mul_const (Complex.Gamma s)
  unfold complexGammaMellinIntegrand complexGammaMellinDerivIntegrand
  dsimp only [s]
  convert htotal using 1
  all_goals ring

theorem continuous_complexGammaMellinIntegrand (w : ℂ) :
    Continuous (complexGammaMellinIntegrand w) := by
  rw [continuous_iff_continuousAt]
  intro t
  unfold complexGammaMellinIntegrand
  dsimp only
  have hs : ContinuousAt
      (fun v : ℝ => estermannVerticalPoint (3 / 2 : ℝ) v) t := by
    unfold estermannVerticalPoint
    fun_prop
  apply ContinuousAt.mul
  · exact Complex.continuous_exp.continuousAt.comp
      (hs.neg.mul continuousAt_const)
  · apply (Complex.continuousAt_Gamma _ ?_).comp hs
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num [estermannVerticalPoint] at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

theorem continuous_complexGammaMellinDerivIntegrand (w : ℂ) :
    Continuous (complexGammaMellinDerivIntegrand w) := by
  rw [continuous_iff_continuousAt]
  intro t
  unfold complexGammaMellinDerivIntegrand
  dsimp only
  have hs : ContinuousAt
      (fun v : ℝ => estermannVerticalPoint (3 / 2 : ℝ) v) t := by
    unfold estermannVerticalPoint
    fun_prop
  apply ContinuousAt.mul
  · apply ContinuousAt.mul
    · exact hs.neg
    · exact Complex.continuous_exp.continuousAt.comp
        (hs.neg.mul continuousAt_const)
  · apply (Complex.continuousAt_Gamma _ ?_).comp hs
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num [estermannVerticalPoint] at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- Absolute convergence throughout the open logarithmic strip. -/
theorem integrable_complexGammaMellinIntegrand
    {w : ℂ} (hw : |w.im| < Real.pi / 2) :
    Integrable (complexGammaMellinIntegrand w) := by
  have hmajor : Integrable (complexGammaMellinMajorant w) := by
    unfold complexGammaMellinMajorant
    exact (integrable_abelPolynomialExponentialMajorant 1
      (sub_pos.mpr hw)).const_mul _
  apply Integrable.mono' hmajor
  · exact (continuous_complexGammaMellinIntegrand w).aestronglyMeasurable
  · filter_upwards [] with t
    exact norm_complexGammaMellinIntegrand_le w t

/-- Holomorphy of the scalar integral in the entire open logarithmic strip.
The proof uses a locally uniform derivative majorant, not a formal exchange
of derivative and integral. -/
theorem differentiableAt_complexGammaMellinIntegral
    {w : ℂ} (hw : |w.im| < Real.pi / 2) :
    DifferentiableAt ℂ complexGammaMellinIntegral w := by
  let lower : ℝ := w.re - 1
  let theta : ℝ := (|w.im| + Real.pi / 2) / 2
  let S : Set ℂ := {z | lower < z.re ∧ |z.im| < theta}
  have hthetaAbove : |w.im| < theta := by
    dsimp [theta]
    linarith
  have hthetaBelow : theta < Real.pi / 2 := by
    dsimp [theta]
    linarith
  have hSopen : IsOpen S := by
    dsimp [S]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (_root_.continuous_abs.comp Complex.continuous_im)
        continuous_const)
  have hwS : w ∈ S := by
    exact ⟨by dsimp [lower]; linarith, hthetaAbove⟩
  have hSnhds : S ∈ 𝓝 w := hSopen.mem_nhds hwS
  have hFmeas : ∀ᶠ z in 𝓝 w,
      AEStronglyMeasurable (complexGammaMellinIntegrand z) volume :=
    Filter.Eventually.of_forall fun z =>
      (continuous_complexGammaMellinIntegrand z).aestronglyMeasurable
  have hFint : Integrable (complexGammaMellinIntegrand w) :=
    integrable_complexGammaMellinIntegrand hw
  have hF'meas : AEStronglyMeasurable
      (complexGammaMellinDerivIntegrand w) volume :=
    (continuous_complexGammaMellinDerivIntegrand w).aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ ∂volume, ∀ z ∈ S,
      ‖complexGammaMellinDerivIntegrand z t‖ ≤
        complexGammaMellinDerivMajorant lower theta t := by
    filter_upwards [] with t z hz
    exact norm_complexGammaMellinDerivIntegrand_le hz.1.le hz.2.le t
  have hboundInt : Integrable
      (complexGammaMellinDerivMajorant lower theta) :=
    integrable_complexGammaMellinDerivMajorant lower hthetaBelow
  have hdiff : ∀ᵐ t : ℝ ∂volume, ∀ z ∈ S,
      HasDerivAt (fun y : ℂ => complexGammaMellinIntegrand y t)
        (complexGammaMellinDerivIntegrand z t) z := by
    filter_upwards [] with t z _
    exact hasDerivAt_complexGammaMellinIntegrand z t
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := complexGammaMellinIntegrand)
    (F' := complexGammaMellinDerivIntegrand)
    (x₀ := w) (s := S)
    (bound := complexGammaMellinDerivMajorant lower theta)
    hSnhds hFmeas hFint hF'meas hbound hboundInt hdiff
  exact hmain.2.differentiableAt

/-- On the real logarithmic axis, complex exponentiation agrees with the
positive-real power used by the existing Mellin inversion theorem. -/
theorem exp_neg_vertical_mul_ofReal
    (x t : ℝ) :
    Complex.exp
        (-estermannVerticalPoint (3 / 2 : ℝ) t * (x : ℂ)) =
      ((Real.exp x : ℝ) : ℂ) ^
        (-estermannVerticalPoint (3 / 2 : ℝ) t) := by
  rw [Complex.cpow_def_of_ne_zero]
  · rw [Complex.ofReal_exp]
    congr 1
    rw [Complex.log_exp
      (by simp; linarith [Real.pi_pos])
      (by simp; linarith [Real.pi_pos])]
    ring
  · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)

/-- The desired formula already holds on the real axis by the proved
positive-real inverse-Mellin theorem. -/
theorem complexGammaMellinIntegral_ofReal (x : ℝ) :
    complexGammaMellinIntegral (x : ℂ) =
      (2 * Real.pi : ℝ) * Complex.exp (-Complex.exp x) := by
  have hx : 0 < Real.exp x := Real.exp_pos x
  have hreal := integral_Gamma_vertical_three_halves hx
  unfold complexGammaMellinIntegral complexGammaMellinIntegrand
  dsimp only
  rw [show (fun t : ℝ =>
      Complex.exp
          (-estermannVerticalPoint (3 / 2 : ℝ) t * (x : ℂ)) *
        Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t)) =
      fun t : ℝ =>
        (((Real.exp x : ℝ) : ℂ) ^
            (-estermannVerticalPoint (3 / 2 : ℝ) t)) *
          Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) by
    funext t
    rw [exp_neg_vertical_mul_ofReal]]
  simpa [estermannVerticalPoint, Complex.ofReal_exp] using hreal

/-! ## Holomorphic continuation from the real axis -/

/-- The natural logarithmic strip for complex Abel damping. -/
def complexGammaMellinStrip : Set ℂ :=
  {w | |w.im| < Real.pi / 2}

theorem isOpen_complexGammaMellinStrip :
    IsOpen complexGammaMellinStrip := by
  unfold complexGammaMellinStrip
  exact isOpen_lt (_root_.continuous_abs.comp Complex.continuous_im)
    continuous_const

theorem convex_complexGammaMellinStrip :
    Convex ℝ complexGammaMellinStrip := by
  have hset : complexGammaMellinStrip =
      {w : ℂ | -(Real.pi / 2) < w.im} ∩
        {w : ℂ | w.im < Real.pi / 2} := by
    ext w
    simp only [complexGammaMellinStrip, mem_setOf_eq, mem_inter_iff,
      abs_lt]
  rw [hset]
  exact (convex_halfSpace_im_gt _).inter
    (convex_halfSpace_im_lt _)

/-- The expected continuation of the real-axis inverse-Mellin value. -/
noncomputable def complexGammaMellinExpected (w : ℂ) : ℂ :=
  (2 * Real.pi : ℝ) * Complex.exp (-Complex.exp w)

theorem differentiableOn_complexGammaMellinIntegral :
    DifferentiableOn ℂ complexGammaMellinIntegral
      complexGammaMellinStrip := by
  intro w hw
  exact (differentiableAt_complexGammaMellinIntegral hw).differentiableWithinAt

theorem differentiable_complexGammaMellinExpected :
    Differentiable ℂ complexGammaMellinExpected := by
  unfold complexGammaMellinExpected
  fun_prop

/-- The real axis supplies an accumulation set for the analytic identity
theorem. -/
theorem zero_mem_closure_complexGammaMellin_realAgreement :
    (0 : ℂ) ∈ closure
      ({w | complexGammaMellinIntegral w =
          complexGammaMellinExpected w} \ {(0 : ℂ)}) := by
  let seq : ℕ → ℂ := fun n =>
    ((((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ)
  have hseqR : Tendsto
      (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0))
  have hseq : Tendsto seq atTop (nhds (0 : ℂ)) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hseqR
  apply mem_closure_of_tendsto hseq
  filter_upwards [] with n
  constructor
  · change complexGammaMellinIntegral
        (((1 : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) =
      complexGammaMellinExpected
        (((1 : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)
    rw [complexGammaMellinIntegral_ofReal]
    rfl
  · simp only [mem_singleton_iff]
    exact Complex.ofReal_ne_zero.mpr (by positivity)

/-- Complex inverse Mellin in logarithmic coordinates, obtained by the
identity theorem from the already proved real inverse-Mellin formula. -/
theorem complexGammaMellinIntegral_eq_expected
    {w : ℂ} (hw : w ∈ complexGammaMellinStrip) :
    complexGammaMellinIntegral w = complexGammaMellinExpected w := by
  have hf : AnalyticOnNhd ℂ complexGammaMellinIntegral
      complexGammaMellinStrip :=
    differentiableOn_complexGammaMellinIntegral.analyticOnNhd
      isOpen_complexGammaMellinStrip
  have hg : AnalyticOnNhd ℂ complexGammaMellinExpected
      complexGammaMellinStrip :=
    differentiable_complexGammaMellinExpected.differentiableOn.analyticOnNhd
      isOpen_complexGammaMellinStrip
  have hzero : (0 : ℂ) ∈ complexGammaMellinStrip := by
    change |(0 : ℂ).im| < Real.pi / 2
    norm_num
    linarith [Real.pi_pos]
  have heq := hf.eqOn_of_preconnected_of_mem_closure hg
    convex_complexGammaMellinStrip.isPreconnected hzero
    zero_mem_closure_complexGammaMellin_realAgreement
  exact heq hw

/-- Genuine scalar complex inverse-Mellin formula on the positive real
half-plane. -/
theorem integral_Gamma_vertical_three_halves_complex
    {u : ℂ} (hu : 0 < u.re) :
    (∫ t : ℝ,
      u ^ (-estermannVerticalPoint (3 / 2 : ℝ) t) *
        Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t)) =
      (2 * Real.pi : ℝ) * Complex.exp (-u) := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    norm_num at hu
  have harg : |Complex.arg u| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hu)
  have hlogStrip : Complex.log u ∈ complexGammaMellinStrip := by
    change |(Complex.log u).im| < Real.pi / 2
    simpa [Complex.log_im] using harg
  have hmain := complexGammaMellinIntegral_eq_expected hlogStrip
  unfold complexGammaMellinIntegral complexGammaMellinExpected
    complexGammaMellinIntegrand at hmain
  dsimp only at hmain
  rw [show (fun t : ℝ =>
      u ^ (-estermannVerticalPoint (3 / 2 : ℝ) t) *
        Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t)) =
      fun t : ℝ =>
        Complex.exp
            (-estermannVerticalPoint (3 / 2 : ℝ) t * Complex.log u) *
          Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) by
    funext t
    rw [Complex.cpow_def_of_ne_zero hu0]
    congr 2
    ring]
  simpa [Complex.exp_log hu0] using hmain

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexInverseMellin
