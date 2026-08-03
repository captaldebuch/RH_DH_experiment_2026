import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroLocalMajorant
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCComplexEstermannMellin
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelHorizontal
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannSimpleLaurent

/-!
# Route C: convergence layer for the Lambert--Mellin identification

The last classical input in the central rational constructor identifies the
upper-half-plane divisor Lambert period with the contour-defined `psi_0`.
Before any Mellin inversion, both Lambert rows must be genuine absolutely
convergent series.  This file proves that prerequisite directly from the
elementary divisor bound and geometric decay of the upper-half-plane
`q`-parameter.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertMellinIdentification

open Complex Filter LSeries MeasureTheory
open scoped LSeries.notation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSimpleLaurent
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelComplexDamping
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzGrowth
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelHorizontal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexEstermannMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPeriod
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroLocalMajorant
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroVerticalMajorant
open RH.Criteria.NymanBeurling.H14ZetaFETransport

/-- The defining divisor Lambert row is absolutely summable at every point
of the upper half-plane. -/
theorem summable_bettinConreyCentralLambertSeries
    (z : ℂ) (hz : 0 < z.im) :
    Summable (fun n : ℕ ↦
      (((n + 1).divisors.card : ℕ) : ℂ) *
        Complex.exp
          ((2 * Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * z)) := by
  let q : ℂ := Complex.exp ((2 * Real.pi : ℂ) * I * z)
  have hq : ‖q‖ < 1 := by
    simpa [q] using
      (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩)
  have hmajorant₀ : Summable (fun n : ℕ ↦
      ‖(((n : ℂ) ^ 1) * q ^ n : ℂ)‖) :=
    summable_norm_pow_mul_geometric_of_norm_lt_one 1 hq
  have hmajorant : Summable (fun n : ℕ ↦
      ‖((((n + 1 : ℕ) : ℂ) ^ 1) * q ^ (n + 1) : ℂ)‖) := by
    exact (summable_nat_add_iff 1).2 hmajorant₀
  apply Summable.of_norm_bounded hmajorant
  intro n
  have hexp :
      Complex.exp
          ((2 * Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * z) =
        q ^ (n + 1) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  simp only [norm_mul, Complex.norm_natCast, norm_pow, pow_one]
  gcongr
  exact_mod_cast Nat.card_divisors_le_self (n + 1)

/-- The `tsum` in the definition is therefore the sum of its displayed
terms, rather than a default value assigned to a nonsummable family. -/
theorem hasSum_bettinConreyCentralLambertSeries
    (z : ℂ) (hz : 0 < z.im) :
    HasSum (fun n : ℕ ↦
      (((n + 1).divisors.card : ℕ) : ℂ) *
        Complex.exp
          ((2 * Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * z))
      (bettinConreyCentralLambertSeries z) := by
  unfold bettinConreyCentralLambertSeries
  exact (summable_bettinConreyCentralLambertSeries z hz).hasSum

/-- Inversion preserves the upper half-plane, so the reciprocal Lambert row
is absolutely summable as well. -/
theorem summable_bettinConreyCentralLambertSeries_neg_inv
    (z : ℂ) (hz : 0 < z.im) :
    Summable (fun n : ℕ ↦
      (((n + 1).divisors.card : ℕ) : ℂ) *
        Complex.exp
          ((2 * Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * (-z⁻¹))) := by
  have hinv : 0 < (-z⁻¹).im := by
    simpa [inv_neg] using
      (UpperHalfPlane.im_inv_neg_coe_pos ⟨z, hz⟩)
  exact summable_bettinConreyCentralLambertSeries (-z⁻¹) hinv

/-- The positive-real Abel parameter corresponding to an upper-half-plane
Lambert variable. -/
noncomputable def bettinConreyLambertAbelParameter (z : ℂ) : ℂ :=
  -(2 * Real.pi : ℂ) * I * z

theorem bettinConreyLambertAbelParameter_re_pos
    (z : ℂ) (hz : 0 < z.im) :
    0 < (bettinConreyLambertAbelParameter z).re := by
  unfold bettinConreyLambertAbelParameter
  norm_num
  positivity

/-! ## Principal-log geometry in the upper half-plane -/

theorem log_neg_I_mul_upperHalfPlane
    (z : ℂ) (hz : 0 < z.im) :
    Complex.log (-I * z) =
      Complex.log z - (Real.pi : ℂ) / 2 * I := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im hz.ne'
  have hargNonneg : 0 ≤ Complex.arg z :=
    Complex.arg_nonneg_iff.mpr hz.le
  have hargLt : Complex.arg z < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')
  have hsector : Complex.arg (-I) + Complex.arg z ∈
      Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_neg_I]
    constructor <;> linarith [Real.pi_pos]
  have hmul := (Complex.log_mul_eq_add_log_iff
    (neg_ne_zero.mpr I_ne_zero) hz0).2 hsector
  rw [hmul, Complex.log_neg_I]
  ring

theorem log_I_mul_inv_upperHalfPlane
    (z : ℂ) (hz : 0 < z.im) :
    Complex.log (I * z⁻¹) =
      (Real.pi : ℂ) / 2 * I - Complex.log z := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im hz.ne'
  have hargNonneg : 0 ≤ Complex.arg z :=
    Complex.arg_nonneg_iff.mpr hz.le
  have hargNeZero : Complex.arg z ≠ 0 := by
    intro hzero
    exact hz.ne' (Complex.arg_eq_zero_iff.mp hzero).2
  have hargPos : 0 < Complex.arg z :=
    lt_of_le_of_ne hargNonneg (Ne.symm hargNeZero)
  have hargLt : Complex.arg z < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')
  have hargNePi : Complex.arg z ≠ Real.pi := ne_of_lt hargLt
  have hargInv : Complex.arg z⁻¹ = -Complex.arg z := by
    rw [Complex.arg_inv, if_neg hargNePi]
  have hsector : Complex.arg I + Complex.arg z⁻¹ ∈
      Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_I, hargInv]
    constructor <;> linarith [Real.pi_pos]
  have hmul := (Complex.log_mul_eq_add_log_iff I_ne_zero
    (inv_ne_zero hz0)).2 hsector
  rw [hmul, Complex.log_I, Complex.log_inv z hargNePi]
  ring

theorem neg_I_mul_cpow_neg_upperHalfPlane
    (z s : ℂ) (hz : 0 < z.im) :
    (-I * z) ^ (-s) =
      Complex.exp ((Real.pi : ℂ) * I * s / 2) * z ^ (-s) := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im hz.ne'
  have hprod0 : -I * z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0
  rw [Complex.cpow_def_of_ne_zero hprod0,
    Complex.cpow_def_of_ne_zero hz0,
    log_neg_I_mul_upperHalfPlane z hz, ← Complex.exp_add]
  congr 1
  ring

theorem I_mul_inv_cpow_neg_upperHalfPlane
    (z s : ℂ) (hz : 0 < z.im) :
    (I * z⁻¹) ^ (-s) =
      Complex.exp (-(Real.pi : ℂ) * I * s / 2) * z ^ s := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im hz.ne'
  have hprod0 : I * z⁻¹ ≠ 0 := mul_ne_zero I_ne_zero (inv_ne_zero hz0)
  rw [Complex.cpow_def_of_ne_zero hprod0,
    Complex.cpow_def_of_ne_zero hz0,
    log_I_mul_inv_upperHalfPlane z hz, ← Complex.exp_add]
  congr 1
  ring

theorem two_pi_cpow_shift_mul_neg (s : ℂ) :
    (2 * Real.pi : ℂ) ^ (s - 1) *
        (2 * Real.pi : ℂ) ^ (-s) =
      (2 * Real.pi : ℂ)⁻¹ := by
  have hbase : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  rw [← Complex.cpow_add _ _ hbase,
    show s - 1 + -s = (-1 : ℂ) by ring,
    Complex.cpow_neg_one]

theorem abelParameter_cpow_normalized
    (z s : ℂ) (hz : 0 < z.im) :
    (2 * Real.pi : ℂ) ^ (s - 1) *
        (bettinConreyLambertAbelParameter z) ^ (-s) =
      (2 * Real.pi : ℂ)⁻¹ *
        Complex.exp ((Real.pi : ℂ) * I * s / 2) * z ^ (-s) := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im hz.ne'
  have hprod0 : -I * z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0
  have hparameter : bettinConreyLambertAbelParameter z =
      (-I * z) * (2 * Real.pi : ℂ) := by
    unfold bettinConreyLambertAbelParameter
    ring
  have hmul : ((-I * z) * (2 * Real.pi : ℂ)) ^ (-s) =
      (-I * z) ^ (-s) * (2 * Real.pi : ℂ) ^ (-s) := by
    simpa only [ofReal_mul, ofReal_ofNat] using
      (mul_posReal_cpow hprod0
        (by positivity : 0 < 2 * Real.pi) (-s))
  rw [hparameter, hmul,
    neg_I_mul_cpow_neg_upperHalfPlane z s hz]
  have hcancel := two_pi_cpow_shift_mul_neg s
  linear_combination
    (Complex.exp ((Real.pi : ℂ) * I * s / 2) * z ^ (-s)) * hcancel

theorem reciprocalAbelParameter_cpow_normalized
    (z s : ℂ) (hz : 0 < z.im) :
    (2 * Real.pi : ℂ) ^ (s - 1) *
        (bettinConreyLambertAbelParameter (-z⁻¹)) ^ (-s) =
      (2 * Real.pi : ℂ)⁻¹ *
        Complex.exp (-(Real.pi : ℂ) * I * s / 2) * z ^ s := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im hz.ne'
  have hprod0 : I * z⁻¹ ≠ 0 := mul_ne_zero I_ne_zero (inv_ne_zero hz0)
  have hparameter : bettinConreyLambertAbelParameter (-z⁻¹) =
      (I * z⁻¹) * (2 * Real.pi : ℂ) := by
    unfold bettinConreyLambertAbelParameter
    ring
  have hmul : ((I * z⁻¹) * (2 * Real.pi : ℂ)) ^ (-s) =
      (I * z⁻¹) ^ (-s) * (2 * Real.pi : ℂ) ^ (-s) := by
    simpa only [ofReal_mul, ofReal_ofNat] using
      (mul_posReal_cpow hprod0
        (by positivity : 0 < 2 * Real.pi) (-s))
  rw [hparameter, hmul,
    I_mul_inv_cpow_neg_upperHalfPlane z s hz]
  have hcancel := two_pi_cpow_shift_mul_neg s
  linear_combination
    (Complex.exp (-(Real.pi : ℂ) * I * s / 2) * z ^ s) * hcancel

/-- Exact principal-branch simplification of the two-row power kernel. -/
theorem coupledAbelPowerKernel_normalized
    (z s : ℂ) (hz : 0 < z.im) :
    (2 * Real.pi : ℂ) ^ (s - 1) *
        ((bettinConreyLambertAbelParameter z) ^ (-s) -
          z⁻¹ *
            (bettinConreyLambertAbelParameter (-z⁻¹)) ^ (-s)) =
      (2 * Real.pi : ℂ)⁻¹ *
        (Complex.exp ((Real.pi : ℂ) * I * s / 2) * z ^ (-s) -
          z⁻¹ * Complex.exp (-(Real.pi : ℂ) * I * s / 2) *
            z ^ s) := by
  rw [mul_sub, abelParameter_cpow_normalized z s hz]
  have hrec := reciprocalAbelParameter_cpow_normalized z s hz
  linear_combination -z⁻¹ * hrec

/-- The conductor-one Estermann series is the square of zeta on its
half-plane of absolute convergence. -/
theorem estermannDirichletSeries_zero_one_eq_zeta_sq
    (s : ℂ) (hs : 1 < s.re) :
    estermannDirichletSeries 0 1 s = riemannZeta s ^ 2 := by
  have hcoeff : estermannCoeff 0 1 = estermannDivisorCoeff := by
    funext n
    unfold estermannCoeff estermannAdditivePhase
    norm_num
  unfold estermannDirichletSeries
  rw [hcoeff]
  unfold estermannDivisorCoeff
  rw [LSeries_convolution'
    (LSeriesSummable_one_iff.mpr hs)
    (LSeriesSummable_one_iff.mpr hs),
    LSeries_one_eq_riemannZeta hs]
  ring

/-- The finite Hurwitz continuation at conductor one is globally the square
of Riemann zeta, not merely on the Dirichlet-series half-plane. -/
theorem estermannHurwitzContinuation_zero_one_eq_zeta_sq (s : ℂ) :
    estermannHurwitzContinuation 0 1 s = riemannZeta s ^ 2 := by
  rw [estermannHurwitzContinuation_eq_finiteSum]
  unfold estermannHurwitzFiniteSum estermannResiduePhase
  have hdefault : (default : ZMod 1) = 0 := Subsingleton.elim _ _
  simp
  have hhz :
      HurwitzZeta.hurwitzZeta
          (ZMod.toAddCircle (default : ZMod 1)) s =
        riemannZeta s := by
    simpa [hdefault] using
      congrFun HurwitzZeta.hurwitzZeta_zero s
  calc
    _ = riemannZeta s * riemannZeta s :=
      congrArg₂ (fun x y : ℂ => x * y) hhz hhz
    _ = riemannZeta s ^ 2 := by ring

/-- Explicit conductor-one residue crossed by the complex Abel contour. -/
theorem complexAbelWeightedResidue_zero_one_eq
    {u : ℂ} (hu : u ≠ 0) :
    estermannWeightedResidueCoefficient 0 1
        (bettinConreyComplexAbelReflectionWeight u) =
      u⁻¹ *
        ((Real.eulerMascheroniConstant : ℂ) - Complex.log u) := by
  rw [complexAbelWeightedResidueCoefficient_eq 0 1 (by simp) hu,
    estermannSimplePoleCoefficient_eq 0 1 (by simp)]
  norm_num
  ring

theorem estermannHurwitzContinuation_zero_one_at_zero :
    estermannHurwitzContinuation 0 1 0 = 1 / 4 := by
  rw [estermannHurwitzContinuation_zero_one_eq_zeta_sq, riemannZeta_zero]
  ring

/-- At conductor one, the complex-damped Estermann row is exactly the
central divisor Lambert row. -/
theorem complexDampedEstermannLambertSeries_zero_one_eq
    (z : ℂ) (hz : 0 < z.im) :
    complexDampedEstermannLambertSeries 0 1
        (bettinConreyLambertAbelParameter z) =
      bettinConreyCentralLambertSeries z := by
  let g : ℕ → ℂ := fun n ↦
    (((n + 1).divisors.card : ℕ) : ℂ) *
      Complex.exp
        ((2 * Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * z)
  have hg : HasSum g (bettinConreyCentralLambertSeries z) := by
    simpa [g] using hasSum_bettinConreyCentralLambertSeries z hz
  have hrow : ∀ n : ℕ,
      LSeries.term (estermannCoeff 0 1) 0 (n + 1) *
          Complex.exp
            (-(bettinConreyLambertAbelParameter z *
              ((n + 1 : ℕ) : ℂ))) =
        g n := by
    intro n
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
    simp only [Complex.cpow_zero, div_one, estermannCoeff,
      estermannDivisorCoeff_apply]
    have hphase : estermannAdditivePhase 0 1 (n + 1) = 1 := by
      simp [estermannAdditivePhase]
    rw [hphase, mul_one]
    unfold g bettinConreyLambertAbelParameter
    congr 1
    ring
  have hfull : HasSum
      (fun n : ℕ ↦
        LSeries.term (estermannCoeff 0 1) 0 n *
          Complex.exp
            (-(bettinConreyLambertAbelParameter z * (n : ℂ))))
      (bettinConreyCentralLambertSeries z) := by
    let f : ℕ → ℂ := fun n ↦
      LSeries.term (estermannCoeff 0 1) 0 n *
        Complex.exp
          (-(bettinConreyLambertAbelParameter z * (n : ℂ)))
    have hshift : HasSum (fun n : ℕ ↦ f (n + 1))
        (bettinConreyCentralLambertSeries z) := by
      simpa only [f, hrow] using hg
    have hf0 : f 0 = 0 := by
      simp [f]
    have hprepend := hshift.zero_add
    rw [hf0, zero_add] at hprepend
    exact hprepend
  unfold complexDampedEstermannLambertSeries
  exact hfull.tsum_eq

/-- The existing global complex inverse-Mellin theorem therefore supplies
the initial-line Mellin representation of the literal divisor Lambert row. -/
theorem centralLambertSeries_eq_complexMellin
    (z : ℂ) (hz : 0 < z.im) :
    (∫ t : ℝ,
      bettinConreyLambertAbelParameter z ^
          (-RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi.estermannVerticalPoint
            (3 / 2 : ℝ) t) *
        Complex.Gamma
          (RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi.estermannVerticalPoint
            (3 / 2 : ℝ) t) *
        estermannDirichletSeries 0 1
          (RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi.estermannVerticalPoint
            (3 / 2 : ℝ) t)) =
      (2 * Real.pi : ℝ) * bettinConreyCentralLambertSeries z := by
  rw [← complexDampedEstermannLambertSeries_zero_one_eq z hz]
  exact complexAbelEstermannMellinIdentity 0 1
    (bettinConreyLambertAbelParameter_re_pos z hz)

/-- Zeta-square form of the initial-line Mellin representation. -/
theorem centralLambertSeries_eq_zetaSquareMellin
    (z : ℂ) (hz : 0 < z.im) :
    (∫ t : ℝ,
      bettinConreyLambertAbelParameter z ^
          (-RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi.estermannVerticalPoint
            (3 / 2 : ℝ) t) *
        Complex.Gamma
          (RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi.estermannVerticalPoint
            (3 / 2 : ℝ) t) *
        riemannZeta
          (RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi.estermannVerticalPoint
            (3 / 2 : ℝ) t) ^ 2) =
      (2 * Real.pi : ℝ) * bettinConreyCentralLambertSeries z := by
  rw [← centralLambertSeries_eq_complexMellin z hz]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [estermannDirichletSeries_zero_one_eq_zeta_sq]
  norm_num [RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi.estermannVerticalPoint]

/-! ## Coupled two-row contour decomposition -/

/-- The elementary residue package attached to one upper-half-plane
Lambert row. -/
noncomputable def bettinConreyLambertResidue (z : ℂ) : ℂ :=
  (bettinConreyLambertAbelParameter z)⁻¹ *
      ((Real.eulerMascheroniConstant : ℂ) -
        Complex.log (bettinConreyLambertAbelParameter z)) +
    1 / 4

/-- The transformed right vertical line for one Lambert row. -/
noncomputable def bettinConreyLambertRightIntegral (z : ℂ) : ℂ :=
  estermannPrimalVerticalIntegral 0 1 (3 / 2 : ℝ)
    (bettinConreyComplexAbelReflectionWeight
      (bettinConreyLambertAbelParameter z))

/-- The existing complex two-pole rectangle, specialized at conductor one,
expresses one transformed right line as its Lambert row plus the exact
residue package. -/
theorem bettinConreyLambertRightIntegral_eq
    (z : ℂ) (hz : 0 < z.im) :
    bettinConreyLambertRightIntegral z =
      -(2 * Real.pi : ℝ) * bettinConreyCentralLambertSeries z +
        2 * Real.pi * bettinConreyLambertResidue z := by
  let u := bettinConreyLambertAbelParameter z
  have huRe : 0 < u.re := bettinConreyLambertAbelParameter_re_pos z hz
  have hu0 : u ≠ 0 := ne_of_apply_ne Complex.re huRe.ne'
  let theta := psiZeroLocalAngle u
  have harg : |Complex.arg u| ≤ theta :=
    (abs_arg_lt_psiZeroLocalAngle u huRe).le
  have htheta : theta < Real.pi / 2 :=
    psiZeroLocalAngle_lt_pi_div_two u huRe
  have hcontour := complexAbel_rightVertical_eq_damped_add_residues
    huRe harg htheta 0 1
  rw [complexDampedEstermannLambertSeries_zero_one_eq z hz,
    complexAbelWeightedResidue_zero_one_eq hu0,
    estermannHurwitzContinuation_zero_one_at_zero] at hcontour
  simpa [bettinConreyLambertRightIntegral,
    bettinConreyLambertResidue, u] using hcontour

/-- The literal conductor-one right-line integrand.  Naming it makes the
remaining functional-equation calculation a pointwise theorem rather than
an opaque equality between completed integrals. -/
noncomputable def bettinConreyLambertRightIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  estermannWeightedIntegrand 0 1
    (bettinConreyComplexAbelReflectionWeight
      (bettinConreyLambertAbelParameter z))
    (estermannVerticalPoint (3 / 2 : ℝ) t)

theorem integrable_bettinConreyLambertRightIntegrand
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (bettinConreyLambertRightIntegrand z) := by
  let u := bettinConreyLambertAbelParameter z
  have huRe : 0 < u.re := bettinConreyLambertAbelParameter_re_pos z hz
  have hu0 : u ≠ 0 := ne_of_apply_ne Complex.re huRe.ne'
  let theta := psiZeroLocalAngle u
  have harg : |Complex.arg u| ≤ theta :=
    (abs_arg_lt_psiZeroLocalAngle u huRe).le
  have htheta : theta < Real.pi / 2 :=
    psiZeroLocalAngle_lt_pi_div_two u huRe
  simpa [bettinConreyLambertRightIntegrand, u] using
    (EstermannNegativeHalfPolynomialGrowth.complex_right_integrable
      (estermannNegativeHalfPolynomialGrowth 0 1) hu0 harg htheta)

theorem bettinConreyLambertRightIntegral_eq_integral
    (z : ℂ) :
    bettinConreyLambertRightIntegral z =
      ∫ t : ℝ, bettinConreyLambertRightIntegrand z t := by
  rfl

/-- The same transformed row after the exact change of variables
`t ↦ -t`; it now lies on the Bettin--Conrey central line and displays the
square of zeta explicitly. -/
noncomputable def bettinConreyCentralSquaredZetaIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  let s := bettinConreyCentralVerticalPoint t;
  -(Complex.Gamma s *
      (bettinConreyLambertAbelParameter z) ^ (-s) *
      riemannZeta s ^ 2)

theorem bettinConreyLambertRightIntegrand_neg_eq_central
    (z : ℂ) (t : ℝ) :
    bettinConreyLambertRightIntegrand z (-t) =
      bettinConreyCentralSquaredZetaIntegrand z t := by
  unfold bettinConreyLambertRightIntegrand
    bettinConreyCentralSquaredZetaIntegrand
    bettinConreyComplexAbelReflectionWeight
    estermannWeightedIntegrand
  rw [estermannHurwitzContinuation_zero_one_eq_zeta_sq]
  have hreflect :
      1 - estermannVerticalPoint (3 / 2 : ℝ) (-t) =
        bettinConreyCentralVerticalPoint t := by
    unfold estermannVerticalPoint bettinConreyCentralVerticalPoint
    push_cast
    ring
  have hpower :
      estermannVerticalPoint (3 / 2 : ℝ) (-t) - 1 =
        -bettinConreyCentralVerticalPoint t := by
    unfold estermannVerticalPoint bettinConreyCentralVerticalPoint
    push_cast
    ring
  dsimp only
  rw [hreflect, hpower]
  ring

/-- The transformed right integral is therefore an honest integral on the
central line; this is the precise entry point for the zeta functional
equation in Bettin--Conrey's proof. -/
theorem bettinConreyLambertRightIntegral_eq_centralSquaredZeta
    (z : ℂ) :
    bettinConreyLambertRightIntegral z =
      ∫ t : ℝ, bettinConreyCentralSquaredZetaIntegrand z t := by
  rw [bettinConreyLambertRightIntegral_eq_integral,
    ← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with t
  exact bettinConreyLambertRightIntegrand_neg_eq_central z t

theorem integrable_bettinConreyCentralSquaredZetaIntegrand
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (bettinConreyCentralSquaredZetaIntegrand z) := by
  exact (integrable_bettinConreyLambertRightIntegrand z hz).comp_neg.congr
    (Eventually.of_forall fun t =>
      bettinConreyLambertRightIntegrand_neg_eq_central z t)

/-- Inversion preserves the upper half-plane. -/
theorem neg_inv_im_pos (z : ℂ) (hz : 0 < z.im) :
    0 < (-z⁻¹).im := by
  simpa [inv_neg] using
    (UpperHalfPlane.im_inv_neg_coe_pos ⟨z, hz⟩)

/-- The two transformed rows remain coupled before the final functional
equation is applied. -/
noncomputable def bettinConreyCoupledRightIntegral (z : ℂ) : ℂ :=
  bettinConreyLambertRightIntegral z -
    z⁻¹ * bettinConreyLambertRightIntegral (-z⁻¹)

/-- Pointwise integrand of the coupled right line. -/
noncomputable def bettinConreyCoupledRightIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  bettinConreyLambertRightIntegrand z t -
    z⁻¹ * bettinConreyLambertRightIntegrand (-z⁻¹) t

/-- Central-line version of the complete coupled integrand. -/
noncomputable def bettinConreyCoupledCentralSquaredZetaIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  bettinConreyCentralSquaredZetaIntegrand z t -
    z⁻¹ * bettinConreyCentralSquaredZetaIntegrand (-z⁻¹) t

/-- The coupled central row with one zeta factor reflected.  This is the
literal spectral kernel immediately before the Gamma reflection and
principal-branch power simplifications in Bettin--Conrey's proof. -/
noncomputable def bettinConreyCoupledCentralFunctionalIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  let s := bettinConreyCentralVerticalPoint t;
  -(Complex.Gamma s * zetaFEFactor s *
      riemannZeta s * riemannZeta (1 - s) *
      ((bettinConreyLambertAbelParameter z) ^ (-s) -
        z⁻¹ *
          (bettinConreyLambertAbelParameter (-z⁻¹)) ^ (-s)))

/-- Gamma reflection on the exact central line.  Keeping the harmless cosine
factor on the left avoids introducing a reciprocal before its nonvanishing
has been checked. -/
theorem Gamma_mul_zetaFEFactor_mul_cos_central
    (t : ℝ) :
    let s := bettinConreyCentralVerticalPoint t
    Complex.Gamma s * zetaFEFactor s *
        Complex.cos ((Real.pi : ℂ) * s / 2) =
      (Real.pi : ℂ) * (2 * Real.pi : ℂ) ^ (s - 1) := by
  let s := bettinConreyCentralVerticalPoint t
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    rw [show s = bettinConreyCentralVerticalPoint t by rfl,
      sin_bettinConreyCentralVerticalPoint]
    exact neg_ne_zero.mpr
      (ofReal_ne_zero.mpr (Real.cosh_pos _).ne')
  have hcomp :
      Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) =
        Complex.sin ((Real.pi : ℂ) * s / 2) := by
    rw [show (Real.pi : ℂ) * (1 - s) / 2 =
        (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * s / 2 by ring,
      Complex.cos_sub]
    have hcos : Complex.cos ((Real.pi : ℂ) / 2) = 0 := by
      rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by
        push_cast; ring, ← Complex.ofReal_cos]
      norm_num
    have hsinHalf : Complex.sin ((Real.pi : ℂ) / 2) = 1 := by
      rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by
        push_cast; ring, ← Complex.ofReal_sin]
      norm_num
    rw [hcos, hsinHalf]
    ring
  have hdouble :
      Complex.sin ((Real.pi : ℂ) * s) =
        2 * Complex.sin ((Real.pi : ℂ) * s / 2) *
          Complex.cos ((Real.pi : ℂ) * s / 2) := by
    calc
      Complex.sin ((Real.pi : ℂ) * s) =
          Complex.sin (2 * ((Real.pi : ℂ) * s / 2)) := by
        congr 1
        ring
      _ = 2 * Complex.sin ((Real.pi : ℂ) * s / 2) *
          Complex.cos ((Real.pi : ℂ) * s / 2) := by
        exact Complex.sin_two_mul _
  have hprod :
      Complex.sin ((Real.pi : ℂ) * s / 2) *
          Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    intro hzero
    apply hsin
    rw [hdouble]
    calc
      2 * Complex.sin ((Real.pi : ℂ) * s / 2) *
          Complex.cos ((Real.pi : ℂ) * s / 2) =
        2 * (Complex.sin ((Real.pi : ℂ) * s / 2) *
          Complex.cos ((Real.pi : ℂ) * s / 2)) := by ring
      _ = 0 := by rw [hzero, mul_zero]
  have hsinHalf : Complex.sin ((Real.pi : ℂ) * s / 2) ≠ 0 :=
    (mul_ne_zero_iff.mp hprod).1
  have hcosHalf : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 :=
    (mul_ne_zero_iff.mp hprod).2
  change Complex.Gamma s * zetaFEFactor s *
      Complex.cos ((Real.pi : ℂ) * s / 2) =
    (Real.pi : ℂ) * (2 * Real.pi : ℂ) ^ (s - 1)
  unfold zetaFEFactor
  rw [hcomp]
  calc
    Complex.Gamma s *
          (2 * (2 * (Real.pi : ℂ)) ^ (s - 1) *
              Complex.Gamma (1 - s) *
            Complex.sin ((Real.pi : ℂ) * s / 2)) *
        Complex.cos ((Real.pi : ℂ) * s / 2) =
      2 * (2 * (Real.pi : ℂ)) ^ (s - 1) *
        (Complex.Gamma s * Complex.Gamma (1 - s)) *
        (Complex.sin ((Real.pi : ℂ) * s / 2) *
          Complex.cos ((Real.pi : ℂ) * s / 2)) := by ring
    _ = 2 * (2 * (Real.pi : ℂ)) ^ (s - 1) *
        ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) *
        (Complex.sin ((Real.pi : ℂ) * s / 2) *
          Complex.cos ((Real.pi : ℂ) * s / 2)) := by
      rw [Complex.Gamma_mul_Gamma_one_sub]
    _ = (Real.pi : ℂ) * (2 * Real.pi : ℂ) ^ (s - 1) := by
      rw [hdouble]
      field_simp [hsin, hsinHalf, hcosHalf]

theorem cos_pi_mul_central_div_two_ne_zero (t : ℝ) :
    Complex.cos ((Real.pi : ℂ) *
      bettinConreyCentralVerticalPoint t / 2) ≠ 0 := by
  have hsin : Complex.sin ((Real.pi : ℂ) *
      bettinConreyCentralVerticalPoint t) ≠ 0 := by
    rw [sin_bettinConreyCentralVerticalPoint]
    exact neg_ne_zero.mpr
      (ofReal_ne_zero.mpr (Real.cosh_pos _).ne')
  intro hcos
  apply hsin
  calc
    Complex.sin ((Real.pi : ℂ) *
        bettinConreyCentralVerticalPoint t) =
      Complex.sin (2 * ((Real.pi : ℂ) *
        bettinConreyCentralVerticalPoint t / 2)) := by
        congr 1
        ring
    _ = 2 * Complex.sin ((Real.pi : ℂ) *
          bettinConreyCentralVerticalPoint t / 2) *
        Complex.cos ((Real.pi : ℂ) *
          bettinConreyCentralVerticalPoint t / 2) :=
      Complex.sin_two_mul _
    _ = 0 := by rw [hcos, mul_zero]

/-- Division form of the reflection identity, now justified by the explicit
nonvanishing of the central cosine. -/
theorem Gamma_mul_zetaFEFactor_central (t : ℝ) :
    let s := bettinConreyCentralVerticalPoint t
    Complex.Gamma s * zetaFEFactor s =
      (Real.pi : ℂ) * (2 * Real.pi : ℂ) ^ (s - 1) /
        Complex.cos ((Real.pi : ℂ) * s / 2) := by
  let s := bettinConreyCentralVerticalPoint t
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    exact cos_pi_mul_central_div_two_ne_zero t
  apply (eq_div_iff hcos).2
  exact Gamma_mul_zetaFEFactor_mul_cos_central t

/-- Fully reflected central integrand.  What remains after this theorem is
only the principal-branch identity for the displayed two-row power kernel. -/
noncomputable def bettinConreyCoupledCentralReflectedIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  let s := bettinConreyCentralVerticalPoint t;
  -((Real.pi : ℂ) * (2 * Real.pi : ℂ) ^ (s - 1) /
      Complex.cos ((Real.pi : ℂ) * s / 2) *
    riemannZeta s * riemannZeta (1 - s) *
    ((bettinConreyLambertAbelParameter z) ^ (-s) -
      z⁻¹ *
        (bettinConreyLambertAbelParameter (-z⁻¹)) ^ (-s)))

/-- After the principal-branch calculation, all `2π` powers cancel and the
two transformed rows become the two explicit exponential phases used in the
source proof. -/
noncomputable def bettinConreyCoupledCentralPhaseIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  let s := bettinConreyCentralVerticalPoint t;
  -((1 / 2 : ℂ) /
      Complex.cos ((Real.pi : ℂ) * s / 2) *
    riemannZeta s * riemannZeta (1 - s) *
    (Complex.exp ((Real.pi : ℂ) * I * s / 2) * z ^ (-s) -
      z⁻¹ * Complex.exp (-(Real.pi : ℂ) * I * s / 2) * z ^ s))

theorem bettinConreyCoupledCentralFunctionalIntegrand_eq_reflected
    (z : ℂ) (t : ℝ) :
    bettinConreyCoupledCentralFunctionalIntegrand z t =
      bettinConreyCoupledCentralReflectedIntegrand z t := by
  unfold bettinConreyCoupledCentralFunctionalIntegrand
    bettinConreyCoupledCentralReflectedIntegrand
  dsimp only
  rw [Gamma_mul_zetaFEFactor_central]

theorem bettinConreyCoupledCentralReflectedIntegrand_eq_phase
    (z : ℂ) (t : ℝ) (hz : 0 < z.im) :
    bettinConreyCoupledCentralReflectedIntegrand z t =
      bettinConreyCoupledCentralPhaseIntegrand z t := by
  unfold bettinConreyCoupledCentralReflectedIntegrand
    bettinConreyCoupledCentralPhaseIntegrand
  dsimp only
  let s := bettinConreyCentralVerticalPoint t
  change -((Real.pi : ℂ) * (2 * Real.pi : ℂ) ^ (s - 1) /
        Complex.cos ((Real.pi : ℂ) * s / 2) *
      riemannZeta s * riemannZeta (1 - s) *
      ((bettinConreyLambertAbelParameter z) ^ (-s) -
        z⁻¹ *
          (bettinConreyLambertAbelParameter (-z⁻¹)) ^ (-s))) =
    -((1 / 2 : ℂ) /
        Complex.cos ((Real.pi : ℂ) * s / 2) *
      riemannZeta s * riemannZeta (1 - s) *
      (Complex.exp ((Real.pi : ℂ) * I * s / 2) * z ^ (-s) -
        z⁻¹ * Complex.exp (-(Real.pi : ℂ) * I * s / 2) * z ^ s))
  have hkernel := coupledAbelPowerKernel_normalized z s hz
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_pos.ne'
  have hscalar : (Real.pi : ℂ) * (2 * Real.pi : ℂ)⁻¹ = 1 / 2 := by
    field_simp [hpi]
  calc
    _ = -((Real.pi : ℂ) /
          Complex.cos ((Real.pi : ℂ) * s / 2) *
        riemannZeta s * riemannZeta (1 - s) *
        ((2 * Real.pi : ℂ) ^ (s - 1) *
          ((bettinConreyLambertAbelParameter z) ^ (-s) -
            z⁻¹ *
              (bettinConreyLambertAbelParameter (-z⁻¹)) ^ (-s)))) := by
      ring
    _ = -((Real.pi : ℂ) /
          Complex.cos ((Real.pi : ℂ) * s / 2) *
        riemannZeta s * riemannZeta (1 - s) *
        ((2 * Real.pi : ℂ)⁻¹ *
          (Complex.exp ((Real.pi : ℂ) * I * s / 2) * z ^ (-s) -
            z⁻¹ * Complex.exp (-(Real.pi : ℂ) * I * s / 2) *
              z ^ s))) := by rw [hkernel]
    _ = _ := by rw [← hscalar]; ring

theorem bettinConreyCoupledCentralSquaredZetaIntegrand_eq
    (z : ℂ) (t : ℝ) :
    bettinConreyCoupledCentralSquaredZetaIntegrand z t =
      let s := bettinConreyCentralVerticalPoint t;
      -(Complex.Gamma s * riemannZeta s ^ 2 *
        ((bettinConreyLambertAbelParameter z) ^ (-s) -
          z⁻¹ *
            (bettinConreyLambertAbelParameter (-z⁻¹)) ^ (-s))) := by
  unfold bettinConreyCoupledCentralSquaredZetaIntegrand
    bettinConreyCentralSquaredZetaIntegrand
  dsimp only
  ring

/-- Away from the null point `t = 0`, one application of the zeta
functional equation converts the square-zeta row into the exact symmetric
product occurring in `g₀`. -/
theorem bettinConreyCoupledCentralSquaredZetaIntegrand_eq_functional
    (z : ℂ) {t : ℝ} (ht : t ≠ 0) :
    bettinConreyCoupledCentralSquaredZetaIntegrand z t =
      bettinConreyCoupledCentralFunctionalIntegrand z t := by
  let s := bettinConreyCentralVerticalPoint t
  have him : s.im ≠ 0 := by
    simpa [s, bettinConreyCentralVerticalPoint] using ht
  have hfe := riemannZeta_eq_zetaFEFactor_mul (w := s) him
  rw [bettinConreyCoupledCentralSquaredZetaIntegrand_eq]
  unfold bettinConreyCoupledCentralFunctionalIntegrand
  dsimp only
  have hsq : riemannZeta s ^ 2 =
      zetaFEFactor s * riemannZeta s * riemannZeta (1 - s) := by
    rw [pow_two, hfe]
    ring
  rw [hsq]
  ring

theorem integrable_bettinConreyCoupledRightIntegrand
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (bettinConreyCoupledRightIntegrand z) := by
  exact (integrable_bettinConreyLambertRightIntegrand z hz).sub
    ((integrable_bettinConreyLambertRightIntegrand (-z⁻¹)
      (neg_inv_im_pos z hz)).const_mul z⁻¹)

theorem integral_bettinConreyCoupledRightIntegrand
    (z : ℂ) (hz : 0 < z.im) :
    (∫ t : ℝ, bettinConreyCoupledRightIntegrand z t) =
      bettinConreyCoupledRightIntegral z := by
  have hfirst := integrable_bettinConreyLambertRightIntegrand z hz
  have hsecond := integrable_bettinConreyLambertRightIntegrand
    (-z⁻¹) (neg_inv_im_pos z hz)
  unfold bettinConreyCoupledRightIntegrand
    bettinConreyCoupledRightIntegral
  rw [integral_sub hfirst (hsecond.const_mul z⁻¹), integral_const_mul]
  rfl

/-- Exact central-line realization of the coupled right integral.  The only
remaining analytic operation is now the pointwise zeta functional equation
and its branch-sensitive power algebra. -/
theorem bettinConreyCoupledRightIntegral_eq_centralSquaredZeta
    (z : ℂ) (hz : 0 < z.im) :
    bettinConreyCoupledRightIntegral z =
      ∫ t : ℝ,
        bettinConreyCoupledCentralSquaredZetaIntegrand z t := by
  have hfirst := integrable_bettinConreyLambertRightIntegrand z hz
  have hsecond := integrable_bettinConreyLambertRightIntegrand
    (-z⁻¹) (neg_inv_im_pos z hz)
  have hfirstCentral :=
    integrable_bettinConreyCentralSquaredZetaIntegrand z hz
  have hsecondCentral :=
    integrable_bettinConreyCentralSquaredZetaIntegrand
      (-z⁻¹) (neg_inv_im_pos z hz)
  rw [bettinConreyCoupledRightIntegral,
    bettinConreyLambertRightIntegral_eq_centralSquaredZeta z,
    bettinConreyLambertRightIntegral_eq_centralSquaredZeta (-z⁻¹)]
  unfold bettinConreyCoupledCentralSquaredZetaIntegrand
  rw [integral_sub hfirstCentral
      (hsecondCentral.const_mul z⁻¹),
    integral_const_mul]

/-- Integral-level functional-equation transport.  The exceptional point
`t = 0` is null, so no ad hoc value is inserted there. -/
theorem bettinConreyCoupledRightIntegral_eq_functionalIntegral
    (z : ℂ) (hz : 0 < z.im) :
    bettinConreyCoupledRightIntegral z =
      ∫ t : ℝ, bettinConreyCoupledCentralFunctionalIntegrand z t := by
  rw [bettinConreyCoupledRightIntegral_eq_centralSquaredZeta z hz]
  apply integral_congr_ae
  have hzero : ∀ᵐ t : ℝ, t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hzero] with t ht
  exact bettinConreyCoupledCentralSquaredZetaIntegrand_eq_functional z ht

/-- The complete coupled contour has now reached the fully reflected kernel.
This is the final branch-free integral identity in the classical chain. -/
theorem bettinConreyCoupledRightIntegral_eq_reflectedIntegral
    (z : ℂ) (hz : 0 < z.im) :
    bettinConreyCoupledRightIntegral z =
      ∫ t : ℝ, bettinConreyCoupledCentralReflectedIntegrand z t := by
  rw [bettinConreyCoupledRightIntegral_eq_functionalIntegral z hz]
  apply integral_congr_ae
  filter_upwards [] with t
  exact bettinConreyCoupledCentralFunctionalIntegrand_eq_reflected z t

/-- Final explicit two-phase form of the coupled contour integral. -/
theorem bettinConreyCoupledRightIntegral_eq_phaseIntegral
    (z : ℂ) (hz : 0 < z.im) :
    bettinConreyCoupledRightIntegral z =
      ∫ t : ℝ, bettinConreyCoupledCentralPhaseIntegrand z t := by
  rw [bettinConreyCoupledRightIntegral_eq_reflectedIntegral z hz]
  apply integral_congr_ae
  filter_upwards [] with t
  exact bettinConreyCoupledCentralReflectedIntegrand_eq_phase z t hz

private theorem solve_lambert_right_equation
    (series residue right c : ℂ) (hc : c ≠ 0)
    (h : right = -c * series + c * residue) :
    series = residue - right / c := by
  field_simp [hc]
  linear_combination h

/-- Exact coupled contour formula for the complete central Lambert period.
No row is estimated separately, and both residue packages remain attached. -/
theorem bettinConreyCentralLambertPeriod_eq_coupledRight
    (z : ℂ) (hz : 0 < z.im) :
    bettinConreyCentralLambertPeriod z =
      bettinConreyLambertResidue z -
        z⁻¹ * bettinConreyLambertResidue (-z⁻¹) -
        (bettinConreyLambertRightIntegral z -
          z⁻¹ * bettinConreyLambertRightIntegral (-z⁻¹)) /
            (2 * Real.pi : ℝ) := by
  have hzinv := neg_inv_im_pos z hz
  have hfirst := bettinConreyLambertRightIntegral_eq z hz
  have hsecond := bettinConreyLambertRightIntegral_eq (-z⁻¹) hzinv
  have hpi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  unfold bettinConreyCentralLambertPeriod centralPeriodOf
  rw [show bettinConreyCentralLambertSeries z =
      bettinConreyLambertResidue z -
        bettinConreyLambertRightIntegral z / (2 * Real.pi : ℝ) by
    apply solve_lambert_right_equation _ _ _ _ hpi
    simpa only [ofReal_mul, ofReal_ofNat] using hfirst,
    show bettinConreyCentralLambertSeries (-z⁻¹) =
      bettinConreyLambertResidue (-z⁻¹) -
        bettinConreyLambertRightIntegral (-z⁻¹) /
          (2 * Real.pi : ℝ) by
      apply solve_lambert_right_equation _ _ _ _ hpi
      simpa only [ofReal_mul, ofReal_ofNat] using hsecond]
  ring

/-! ## Exact final classical target -/

/-- The value that the coupled right line must have in order to recover the
published central Bettin--Conrey period.  This definition deliberately keeps
the two residue packages and the elementary Eisenstein mode attached; no
branch-sensitive logarithm law is hidden in its statement. -/
noncomputable def bettinConreyCoupledRightTarget (z : ℂ) : ℂ :=
  (2 * Real.pi : ℝ) *
    (bettinConreyLambertResidue z -
      z⁻¹ * bettinConreyLambertResidue (-z⁻¹) -
      (1 - z⁻¹ - bettinConreyPsiZero z) / 4)

/-- A proof of the one coupled right-line evaluation constructs the complete
Lambert/`psi₀` identification.  All inverse-Mellin, exchange, contour,
residue, and integrability work has already been discharged above. -/
noncomputable def
    bettinConreyLambertPsiZeroIdentification_of_coupledRight
    (hcoupled : ∀ z : ℂ, 0 < z.im →
      bettinConreyCoupledRightIntegral z =
        bettinConreyCoupledRightTarget z) :
    BettinConreyLambertPsiZeroIdentification where
  eq_on_upperHalfPlane z hz := by
    rw [bettinConreyCentralLambertPeriod_eq_coupledRight z hz]
    change bettinConreyLambertResidue z -
        z⁻¹ * bettinConreyLambertResidue (-z⁻¹) -
        bettinConreyCoupledRightIntegral z / (2 * Real.pi : ℝ) = _
    rw [hcoupled z hz]
    unfold bettinConreyCoupledRightTarget
    have hpi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    field_simp [hpi]
    ring

/-- Consequently, Route C's remaining classical input can be stated directly
as the evaluation of the explicit two-phase integral. -/
noncomputable def
    bettinConreyLambertPsiZeroIdentification_of_phaseIntegral
    (hphase : ∀ z : ℂ, 0 < z.im →
      (∫ t : ℝ, bettinConreyCoupledCentralPhaseIntegrand z t) =
        bettinConreyCoupledRightTarget z) :
    BettinConreyLambertPsiZeroIdentification :=
  bettinConreyLambertPsiZeroIdentification_of_coupledRight fun z hz => by
    rw [bettinConreyCoupledRightIntegral_eq_phaseIntegral z hz]
    exact hphase z hz

/-- Conversely, the source identification forces exactly the coupled
right-line target.  Hence this is an equivalent classical target, not a
stronger auxiliary assumption. -/
theorem bettinConreyCoupledRightIntegral_eq_target_of_identification
    (H : BettinConreyLambertPsiZeroIdentification)
    (z : ℂ) (hz : 0 < z.im) :
    bettinConreyCoupledRightIntegral z =
      bettinConreyCoupledRightTarget z := by
  have hperiod := bettinConreyCentralLambertPeriod_eq_coupledRight z hz
  have hsource := H.eq_on_upperHalfPlane z hz
  unfold bettinConreyCoupledRightTarget
  change bettinConreyCentralLambertPeriod z =
      bettinConreyLambertResidue z -
        z⁻¹ * bettinConreyLambertResidue (-z⁻¹) -
        bettinConreyCoupledRightIntegral z / (2 * Real.pi : ℝ) at hperiod
  have hpi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  rw [← hsource, hperiod]
  push_cast
  field_simp [hpi]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertMellinIdentification
