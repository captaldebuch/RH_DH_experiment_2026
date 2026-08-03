import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCLambertMellinIdentification
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelLeftLine

/-!
# Route C: evaluation of the explicit two-phase Lambert kernel

The coupled Lambert contour has already been reduced to an explicit
two-phase integral on `Re(s) = -1/2`.  Bettin--Conrey equations (18)--(19)
combine those phases only after rewriting `g₀` in its equivalent
square-zeta Mellin form.  This module proves that normalization first.

No rational boundary limit or RH-strength estimate is used here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPhaseEvaluation

open Complex Filter MeasureTheory Set
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertMellinIdentification
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexEstermannMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPeriod
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroLocalMajorant
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroVerticalMajorant
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelLeftLine
open RH.Criteria.NymanBeurling.H14ZetaFETransport

/-- The square-zeta representation of the `g₀` vertical integrand. -/
noncomputable def bettinConreyGZeroSquareVerticalIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  let s := bettinConreyCentralVerticalPoint t;
  riemannZeta s ^ 2 * Complex.Gamma s /
      Complex.sin ((Real.pi : ℂ) * s / 2) *
    ((2 * Real.pi : ℂ) * z) ^ (-s)

theorem sin_pi_mul_central_div_two_ne_zero (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) *
      bettinConreyCentralVerticalPoint t / 2) ≠ 0 := by
  have hsin : Complex.sin ((Real.pi : ℂ) *
      bettinConreyCentralVerticalPoint t) ≠ 0 := by
    rw [sin_bettinConreyCentralVerticalPoint]
    exact neg_ne_zero.mpr
      (ofReal_ne_zero.mpr (Real.cosh_pos _).ne')
  intro hhalf
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
    _ = 0 := by rw [hhalf]; ring

/-- The functional-equation factor at `1-s`, in the exact normalization
used by Bettin--Conrey equation (19). -/
theorem zetaFEFactor_one_sub_central (t : ℝ) :
    let s := bettinConreyCentralVerticalPoint t;
    zetaFEFactor (1 - s) =
      2 * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        Complex.cos ((Real.pi : ℂ) * s / 2) := by
  let s := bettinConreyCentralVerticalPoint t
  change zetaFEFactor (1 - s) =
    2 * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
      Complex.cos ((Real.pi : ℂ) * s / 2)
  unfold zetaFEFactor
  congr 2 <;> ring

/-- Positive-real multiplication produces no principal-branch correction. -/
theorem two_pi_cpow_mul_upperHalfPlane
    (z s : ℂ) (hz : 0 < z.im) :
    (2 * Real.pi : ℂ) ^ (-s) * z ^ (-s) =
      ((2 * Real.pi : ℂ) * z) ^ (-s) := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im hz.ne'
  have h := mul_posReal_cpow hz0
    (by positivity : 0 < 2 * Real.pi) (-s)
  calc
    (2 * Real.pi : ℂ) ^ (-s) * z ^ (-s) =
        z ^ (-s) * (2 * Real.pi : ℂ) ^ (-s) := by ring
    _ = (z * (2 * Real.pi : ℂ)) ^ (-s) := by
      simpa only [ofReal_mul, ofReal_ofNat] using h.symm
    _ = ((2 * Real.pi : ℂ) * z) ^ (-s) := by
      rw [mul_comm]

/-- Pointwise equality of Bettin--Conrey's two displayed formulas for the
`g₀` kernel.  The functional equation is needed only away from `t = 0`; that
single point is removed at the integral level below. -/
theorem bettinConreyGZeroVerticalIntegrand_eq_square
    (z : ℂ) (hz : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    bettinConreyGZeroVerticalIntegrand z t =
      bettinConreyGZeroSquareVerticalIntegrand z t := by
  let s := bettinConreyCentralVerticalPoint t
  have him : (1 - s).im ≠ 0 := by
    simpa [s, bettinConreyCentralVerticalPoint] using neg_ne_zero.mpr ht
  have hfe := riemannZeta_eq_zetaFEFactor_mul (w := 1 - s) him
  have hfactor : zetaFEFactor (1 - s) =
      2 * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        Complex.cos ((Real.pi : ℂ) * s / 2) := by
    simpa [s] using zetaFEFactor_one_sub_central t
  have hsinHalf : Complex.sin ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    simpa [s] using sin_pi_mul_central_div_two_ne_zero t
  have hcosHalf : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    simpa [s] using cos_pi_mul_central_div_two_ne_zero t
  have hdouble : Complex.sin ((Real.pi : ℂ) * s) =
      2 * Complex.sin ((Real.pi : ℂ) * s / 2) *
        Complex.cos ((Real.pi : ℂ) * s / 2) := by
    calc
      Complex.sin ((Real.pi : ℂ) * s) =
          Complex.sin (2 * ((Real.pi : ℂ) * s / 2)) := by
        congr 1
        ring
      _ = 2 * Complex.sin ((Real.pi : ℂ) * s / 2) *
          Complex.cos ((Real.pi : ℂ) * s / 2) :=
        Complex.sin_two_mul _
  have hpower := two_pi_cpow_mul_upperHalfPlane z s hz
  unfold bettinConreyGZeroVerticalIntegrand
    bettinConreyGZeroSquareVerticalIntegrand
  dsimp only
  change riemannZeta s * riemannZeta (1 - s) /
      Complex.sin ((Real.pi : ℂ) * s) * z ^ (-s) =
    riemannZeta s ^ 2 * Complex.Gamma s /
        Complex.sin ((Real.pi : ℂ) * s / 2) *
      ((2 * Real.pi : ℂ) * z) ^ (-s)
  rw [hfe, show 1 - (1 - s) = s by ring, hfactor, hdouble, ← hpower]
  field_simp [hsinHalf, hcosHalf]

/-- Integral form of the alternate square-zeta representation of `g₀`. -/
theorem bettinConreyGZero_eq_squareIntegral
    (z : ℂ) (hz : 0 < z.im) :
    bettinConreyGZero z =
      (1 / (Real.pi : ℂ)) *
        ∫ t : ℝ, bettinConreyGZeroSquareVerticalIntegrand z t := by
  unfold bettinConreyGZero
  congr 1
  apply integral_congr_ae
  have hzero : ∀ᵐ t : ℝ, t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hzero] with t ht
  exact bettinConreyGZeroVerticalIntegrand_eq_square z hz ht

/-! ## Equation (18): the primary shifted Lambert row -/

/-- The primary square-zeta phase appearing in Bettin--Conrey equation
(18), after parametrizing the central line by `s = -1/2 + it`. -/
noncomputable def bettinConreyPrimarySquareZetaIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  let s := bettinConreyCentralVerticalPoint t;
  Complex.Gamma s * riemannZeta s ^ 2 *
    Complex.exp ((Real.pi : ℂ) * I * s / 2) *
    ((2 * Real.pi : ℂ) * z) ^ (-s)

theorem abelParameter_cpow_eq_primaryPower
    (z s : ℂ) (hz : 0 < z.im) :
    (bettinConreyLambertAbelParameter z) ^ (-s) =
      Complex.exp ((Real.pi : ℂ) * I * s / 2) *
        ((2 * Real.pi : ℂ) * z) ^ (-s) := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im hz.ne'
  have hprod0 : -I * z ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0
  have hparameter : bettinConreyLambertAbelParameter z =
      (-I * z) * (2 * Real.pi : ℂ) := by
    unfold bettinConreyLambertAbelParameter
    ring
  have hmul : ((-I * z) * (2 * Real.pi : ℂ)) ^ (-s) =
      (-I * z) ^ (-s) * (2 * Real.pi : ℂ) ^ (-s) := by
    simpa only [ofReal_mul, ofReal_ofNat] using
      (mul_posReal_cpow hprod0
        (by positivity : 0 < 2 * Real.pi) (-s))
  have hphase := neg_I_mul_cpow_neg_upperHalfPlane z s hz
  have hpower := two_pi_cpow_mul_upperHalfPlane z s hz
  rw [hparameter, hmul, hphase, ← hpower]
  ring

theorem bettinConreyCentralSquaredZetaIntegrand_eq_neg_primary
    (z : ℂ) (t : ℝ) (hz : 0 < z.im) :
    bettinConreyCentralSquaredZetaIntegrand z t =
      -bettinConreyPrimarySquareZetaIntegrand z t := by
  unfold bettinConreyCentralSquaredZetaIntegrand
    bettinConreyPrimarySquareZetaIntegrand
  dsimp only
  rw [abelParameter_cpow_eq_primaryPower z
    (bettinConreyCentralVerticalPoint t) hz]
  ring

theorem integrable_bettinConreyPrimarySquareZetaIntegrand
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (bettinConreyPrimarySquareZetaIntegrand z) := by
  have hcentral := integrable_bettinConreyCentralSquaredZetaIntegrand z hz
  exact hcentral.neg.congr (Eventually.of_forall fun t => by
    change -bettinConreyCentralSquaredZetaIntegrand z t =
      bettinConreyPrimarySquareZetaIntegrand z t
    rw [bettinConreyCentralSquaredZetaIntegrand_eq_neg_primary z t hz]
    ring)

theorem bettinConreyLambertRightIntegral_eq_neg_primaryIntegral
    (z : ℂ) (hz : 0 < z.im) :
    bettinConreyLambertRightIntegral z =
      -∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t := by
  rw [bettinConreyLambertRightIntegral_eq_centralSquaredZeta]
  rw [show (∫ t : ℝ, bettinConreyCentralSquaredZetaIntegrand z t) =
      ∫ t : ℝ, -bettinConreyPrimarySquareZetaIntegrand z t by
    apply integral_congr_ae
    filter_upwards [] with t
    exact bettinConreyCentralSquaredZetaIntegrand_eq_neg_primary z t hz]
  rw [integral_neg]

/-- Exact real-line form of Bettin--Conrey equation (18). -/
theorem centralLambertSeries_eq_residue_add_primaryIntegral
    (z : ℂ) (hz : 0 < z.im) :
    bettinConreyCentralLambertSeries z =
      bettinConreyLambertResidue z +
        (1 / (2 * Real.pi : ℂ)) *
          ∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t := by
  have hcontour := bettinConreyLambertRightIntegral_eq z hz
  rw [bettinConreyLambertRightIntegral_eq_neg_primaryIntegral z hz]
    at hcontour
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  push_cast at hcontour
  have hintegral :
      (∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t) =
        (2 * Real.pi : ℂ) * bettinConreyCentralLambertSeries z -
          (2 * Real.pi : ℂ) * bettinConreyLambertResidue z := by
    calc
      (∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t) =
          -(-(∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t)) := by ring
      _ = -(-(2 * Real.pi : ℂ) * bettinConreyCentralLambertSeries z +
          (2 * Real.pi : ℂ) * bettinConreyLambertResidue z) := by rw [hcontour]
      _ = _ := by ring
  have hdiff :
      bettinConreyCentralLambertSeries z - bettinConreyLambertResidue z =
        (∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t) /
          (2 * Real.pi : ℂ) := by
    apply (eq_div_iff hpi).2
    calc
      (bettinConreyCentralLambertSeries z -
          bettinConreyLambertResidue z) * (2 * Real.pi : ℂ) =
          (2 * Real.pi : ℂ) * bettinConreyCentralLambertSeries z -
            (2 * Real.pi : ℂ) * bettinConreyLambertResidue z := by ring
      _ = _ := hintegral.symm
  calc
    bettinConreyCentralLambertSeries z =
        bettinConreyLambertResidue z +
          (bettinConreyCentralLambertSeries z -
            bettinConreyLambertResidue z) := by ring
    _ = bettinConreyLambertResidue z +
        (∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t) /
          (2 * Real.pi : ℂ) := by rw [hdiff]
    _ = _ := by ring

/-! ## Equation (19): the reciprocal shifted Lambert row -/

/-- Initial-line integrand for the reciprocal Lambert row, including the
outer factor `z⁻¹`. -/
noncomputable def bettinConreyReciprocalInitialIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  let w := estermannVerticalPoint (3 / 2 : ℝ) t
  z⁻¹ *
    (bettinConreyLambertAbelParameter (-z⁻¹)) ^ (-w) *
    Complex.Gamma w * riemannZeta w ^ 2

/-- The reciprocal Lambert row on its initial line, before applying the two
zeta functional equations. -/
theorem reciprocalCentralLambertSeries_eq_initialIntegral
    (z : ℂ) (hz : 0 < z.im) :
    (∫ t : ℝ, bettinConreyReciprocalInitialIntegrand z t) =
      (2 * Real.pi : ℝ) *
        (z⁻¹ * bettinConreyCentralLambertSeries (-z⁻¹)) := by
  have h := centralLambertSeries_eq_zetaSquareMellin
    (-z⁻¹) (neg_inv_im_pos z hz)
  unfold bettinConreyReciprocalInitialIntegrand
  dsimp only
  simp_rw [show ∀ t : ℝ,
      z⁻¹ *
          bettinConreyLambertAbelParameter (-z⁻¹) ^
              (-estermannVerticalPoint (3 / 2 : ℝ) t) *
            Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) *
          riemannZeta (estermannVerticalPoint (3 / 2 : ℝ) t) ^ 2 =
        z⁻¹ *
          (bettinConreyLambertAbelParameter (-z⁻¹) ^
              (-estermannVerticalPoint (3 / 2 : ℝ) t) *
            Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) *
          riemannZeta (estermannVerticalPoint (3 / 2 : ℝ) t) ^ 2) by
      intro t; ring]
  rw [integral_const_mul, h]
  ring

/-- The cotangent phase produced by the double functional equation in
Bettin--Conrey equation (19). -/
noncomputable def bettinConreyReciprocalSquareZetaIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  let s := bettinConreyCentralVerticalPoint t
  Complex.Gamma s * riemannZeta s ^ 2 *
    Complex.exp ((Real.pi : ℂ) * I * s / 2) *
    Complex.cos ((Real.pi : ℂ) * s / 2) /
      Complex.sin ((Real.pi : ℂ) * s / 2) *
    ((2 * Real.pi : ℂ) * z) ^ (-s)

/-- Reparametrizing the initial reciprocal line by `w = 1-s`. -/
theorem reciprocalInitialIntegrand_neg_eq_central
    (z : ℂ) (t : ℝ) :
    bettinConreyReciprocalInitialIntegrand z (-t) =
      let s := bettinConreyCentralVerticalPoint t
      z⁻¹ *
        (bettinConreyLambertAbelParameter (-z⁻¹)) ^ (s - 1) *
        Complex.Gamma (1 - s) * riemannZeta (1 - s) ^ 2 := by
  unfold bettinConreyReciprocalInitialIntegrand
  dsimp only
  have hw : estermannVerticalPoint (3 / 2 : ℝ) (-t) =
      1 - bettinConreyCentralVerticalPoint t := by
    unfold estermannVerticalPoint bettinConreyCentralVerticalPoint
    push_cast
    ring
  rw [hw]
  congr 3 <;> ring

theorem reciprocalAbelParameter_cpow_one_sub_normalized
    (z s : ℂ) (hz : 0 < z.im) :
    (2 * Real.pi : ℂ) ^ (-s) *
        (bettinConreyLambertAbelParameter (-z⁻¹)) ^ (s - 1) =
      (2 * Real.pi : ℂ)⁻¹ *
        Complex.exp (-(Real.pi : ℂ) * I * (1 - s) / 2) *
          z ^ (1 - s) := by
  have h := reciprocalAbelParameter_cpow_normalized z (1 - s) hz
  convert h using 1 <;> ring

theorem inv_mul_cpow_one_sub
    (z s : ℂ) (hz : z ≠ 0) :
    z⁻¹ * z ^ (1 - s) = z ^ (-s) := by
  calc
    z⁻¹ * z ^ (1 - s) = z ^ (1 - s) * z⁻¹ := by ring
    _ = z ^ (1 - s) * z ^ (-1 : ℂ) := by
      rw [Complex.cpow_neg_one]
    _ = z ^ ((1 - s) + (-1 : ℂ)) := by
      rw [Complex.cpow_add _ _ hz]
    _ = z ^ (-s) := by congr 1 <;> ring

theorem exp_neg_pi_I_one_sub_div_two (s : ℂ) :
    Complex.exp (-(Real.pi : ℂ) * I * (1 - s) / 2) =
      -I * Complex.exp ((Real.pi : ℂ) * I * s / 2) := by
  have hquarter :
      Complex.exp (-(Real.pi : ℂ) * I / 2) = -I := by
    rw [show -(Real.pi : ℂ) * I / 2 =
        (-(Real.pi : ℂ) / 2) * I by ring,
      Complex.exp_mul_I,
      show -(Real.pi : ℂ) / 2 = -((Real.pi : ℂ) / 2) by ring,
      Complex.cos_neg, Complex.sin_neg,
      Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  rw [show -(Real.pi : ℂ) * I * (1 - s) / 2 =
      (-(Real.pi : ℂ) * I / 2) +
        (Real.pi : ℂ) * I * s / 2 by ring,
    Complex.exp_add, hquarter]

theorem gamma_cotangent_scalar_central (t : ℝ) :
    let s := bettinConreyCentralVerticalPoint t
    4 * (2 * Real.pi : ℂ)⁻¹ *
        Complex.Gamma (1 - s) * Complex.Gamma s ^ 2 *
          Complex.cos ((Real.pi : ℂ) * s / 2) ^ 2 =
      Complex.Gamma s *
        Complex.cos ((Real.pi : ℂ) * s / 2) /
          Complex.sin ((Real.pi : ℂ) * s / 2) := by
  let s := bettinConreyCentralVerticalPoint t
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    rw [show s = bettinConreyCentralVerticalPoint t by rfl,
      sin_bettinConreyCentralVerticalPoint]
    exact neg_ne_zero.mpr
      (ofReal_ne_zero.mpr (Real.cosh_pos _).ne')
  have hsinHalf : Complex.sin ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    simpa [s] using sin_pi_mul_central_div_two_ne_zero t
  have hcosHalf : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    simpa [s] using cos_pi_mul_central_div_two_ne_zero t
  have hdouble : Complex.sin ((Real.pi : ℂ) * s) =
      2 * Complex.sin ((Real.pi : ℂ) * s / 2) *
        Complex.cos ((Real.pi : ℂ) * s / 2) := by
    calc
      Complex.sin ((Real.pi : ℂ) * s) =
          Complex.sin (2 * ((Real.pi : ℂ) * s / 2)) := by
        congr 1
        ring
      _ = _ := Complex.sin_two_mul _
  change 4 * (2 * Real.pi : ℂ)⁻¹ *
      Complex.Gamma (1 - s) * Complex.Gamma s ^ 2 *
        Complex.cos ((Real.pi : ℂ) * s / 2) ^ 2 =
    Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2) /
      Complex.sin ((Real.pi : ℂ) * s / 2)
  calc
    4 * (2 * Real.pi : ℂ)⁻¹ *
        Complex.Gamma (1 - s) * Complex.Gamma s ^ 2 *
          Complex.cos ((Real.pi : ℂ) * s / 2) ^ 2 =
      4 * (2 * Real.pi : ℂ)⁻¹ *
        (Complex.Gamma (1 - s) * Complex.Gamma s) *
        Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2) ^ 2 := by ring
    _ = 4 * (2 * Real.pi : ℂ)⁻¹ *
        ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) *
        Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2) ^ 2 := by
      rw [show Complex.Gamma (1 - s) * Complex.Gamma s =
          (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s) by
        rw [mul_comm, Complex.Gamma_mul_Gamma_one_sub]]
    _ = _ := by
      rw [hdouble]
      field_simp [hsin, hsinHalf, hcosHalf,
        (show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_pos.ne')]
      ring

/-- Pointwise double-functional-equation calculation underlying equation
(19).  The point `t = 0` is excluded only because the functional equation is
invoked there through its non-pole interface. -/
theorem reciprocalInitialIntegrand_neg_eq_reciprocalSquare
    (z : ℂ) (hz : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    bettinConreyReciprocalInitialIntegrand z (-t) =
      -I * bettinConreyReciprocalSquareZetaIntegrand z t := by
  let s := bettinConreyCentralVerticalPoint t
  have him : (1 - s).im ≠ 0 := by
    simpa [s, bettinConreyCentralVerticalPoint] using neg_ne_zero.mpr ht
  have hfe := riemannZeta_eq_zetaFEFactor_mul (w := 1 - s) him
  have hfactor : zetaFEFactor (1 - s) =
      2 * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        Complex.cos ((Real.pi : ℂ) * s / 2) := by
    simpa [s] using zetaFEFactor_one_sub_central t
  have hrec := reciprocalAbelParameter_cpow_one_sub_normalized z s hz
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im hz.ne'
  have hzpower := inv_mul_cpow_one_sub z s hz0
  have hphase := exp_neg_pi_I_one_sub_div_two s
  have hgamma :
      4 * (2 * Real.pi : ℂ)⁻¹ *
          Complex.Gamma (1 - s) * Complex.Gamma s ^ 2 *
            Complex.cos ((Real.pi : ℂ) * s / 2) ^ 2 =
        Complex.Gamma s *
          Complex.cos ((Real.pi : ℂ) * s / 2) /
            Complex.sin ((Real.pi : ℂ) * s / 2) := by
    simpa [s] using gamma_cotangent_scalar_central t
  have htwopower := two_pi_cpow_mul_upperHalfPlane z s hz
  rw [reciprocalInitialIntegrand_neg_eq_central]
  unfold bettinConreyReciprocalSquareZetaIntegrand
  dsimp only
  change z⁻¹ *
        bettinConreyLambertAbelParameter (-z⁻¹) ^ (s - 1) *
        Complex.Gamma (1 - s) * riemannZeta (1 - s) ^ 2 =
    -I * (Complex.Gamma s * riemannZeta s ^ 2 *
      Complex.exp ((Real.pi : ℂ) * I * s / 2) *
      Complex.cos ((Real.pi : ℂ) * s / 2) /
        Complex.sin ((Real.pi : ℂ) * s / 2) *
      ((2 * Real.pi : ℂ) * z) ^ (-s))
  rw [hfe, show 1 - (1 - s) = s by ring, hfactor]
  calc
    z⁻¹ * bettinConreyLambertAbelParameter (-z⁻¹) ^ (s - 1) *
          Complex.Gamma (1 - s) *
          (2 * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
            Complex.cos ((Real.pi : ℂ) * s / 2) * riemannZeta s) ^ 2 =
        z⁻¹ *
          ((2 * Real.pi : ℂ) ^ (-s) *
            bettinConreyLambertAbelParameter (-z⁻¹) ^ (s - 1)) *
          (2 * Real.pi : ℂ) ^ (-s) *
          (4 * Complex.Gamma (1 - s) * Complex.Gamma s ^ 2 *
            Complex.cos ((Real.pi : ℂ) * s / 2) ^ 2) *
          riemannZeta s ^ 2 := by ring
    _ =
        (z⁻¹ * z ^ (1 - s)) *
          Complex.exp (-(Real.pi : ℂ) * I * (1 - s) / 2) *
          (2 * Real.pi : ℂ) ^ (-s) *
          (4 * (2 * Real.pi : ℂ)⁻¹ *
            Complex.Gamma (1 - s) * Complex.Gamma s ^ 2 *
              Complex.cos ((Real.pi : ℂ) * s / 2) ^ 2) *
          riemannZeta s ^ 2 := by rw [hrec]; ring
    _ = z ^ (-s) *
          (-I * Complex.exp ((Real.pi : ℂ) * I * s / 2)) *
          (2 * Real.pi : ℂ) ^ (-s) *
          (Complex.Gamma s *
            Complex.cos ((Real.pi : ℂ) * s / 2) /
              Complex.sin ((Real.pi : ℂ) * s / 2)) *
          riemannZeta s ^ 2 := by rw [hzpower, hphase, hgamma]
    _ = -I *
        (Complex.Gamma s * riemannZeta s ^ 2 *
          Complex.exp ((Real.pi : ℂ) * I * s / 2) *
          Complex.cos ((Real.pi : ℂ) * s / 2) /
            Complex.sin ((Real.pi : ℂ) * s / 2) *
          ((2 * Real.pi : ℂ) ^ (-s) * z ^ (-s))) := by ring
    _ = _ := by rw [htwopower]

/-- Integral form of Bettin--Conrey equation (19), including the `-i`
coming from the unnormalized contour coefficient after `ds = i dt`. -/
theorem reciprocalInitialIntegral_eq_neg_I_reciprocalIntegral
    (z : ℂ) (hz : 0 < z.im) :
    (∫ t : ℝ, bettinConreyReciprocalInitialIntegrand z t) =
      -I * ∫ t : ℝ, bettinConreyReciprocalSquareZetaIntegrand z t := by
  rw [← integral_neg_eq_self]
  calc
    (∫ t : ℝ, bettinConreyReciprocalInitialIntegrand z (-t)) =
        ∫ t : ℝ, -I * bettinConreyReciprocalSquareZetaIntegrand z t := by
      apply integral_congr_ae
      have hzero : ∀ᵐ t : ℝ, t ≠ 0 := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hzero] with t ht
      exact reciprocalInitialIntegrand_neg_eq_reciprocalSquare z hz ht
    _ = _ := by rw [integral_const_mul]

/-- Exact real-line form of Bettin--Conrey equation (19). -/
theorem reciprocalCentralLambertSeries_eq_reciprocalIntegral
    (z : ℂ) (hz : 0 < z.im) :
    z⁻¹ * bettinConreyCentralLambertSeries (-z⁻¹) =
      (-I / (2 * Real.pi : ℂ)) *
        ∫ t : ℝ, bettinConreyReciprocalSquareZetaIntegrand z t := by
  have hinitial := reciprocalCentralLambertSeries_eq_initialIntegral z hz
  rw [reciprocalInitialIntegral_eq_neg_I_reciprocalIntegral z hz] at hinitial
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  push_cast at hinitial
  rw [show (-I / (2 * Real.pi : ℂ)) *
      (∫ t : ℝ, bettinConreyReciprocalSquareZetaIntegrand z t) =
      (-I * (∫ t : ℝ,
        bettinConreyReciprocalSquareZetaIntegrand z t)) /
          (2 * Real.pi : ℂ) by field_simp [hpi]]
  apply (eq_div_iff hpi).2
  calc
    (z⁻¹ * bettinConreyCentralLambertSeries (-z⁻¹)) *
        (2 * Real.pi : ℂ) =
        (2 * Real.pi : ℂ) *
          (z⁻¹ * bettinConreyCentralLambertSeries (-z⁻¹)) := by ring
    _ = -I * ∫ t : ℝ,
        bettinConreyReciprocalSquareZetaIntegrand z t := hinitial.symm

/-- The reciprocal cotangent phase is integrable; this follows from the
initial absolutely convergent Mellin row and equation (19), rather than from
a new majorant. -/
theorem integrable_bettinConreyReciprocalSquareZetaIntegrand
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (bettinConreyReciprocalSquareZetaIntegrand z) := by
  have hinitial : Integrable (bettinConreyReciprocalInitialIntegrand z) := by
    have hbase := integrable_initialComplexAbelEstermann
      (bettinConreyLambertAbelParameter_re_pos (-z⁻¹)
        (neg_inv_im_pos z hz)) 0 1
    have hzeta : Integrable (fun t : ℝ =>
        (bettinConreyLambertAbelParameter (-z⁻¹)) ^
            (-estermannVerticalPoint (3 / 2 : ℝ) t) *
          Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) *
          riemannZeta (estermannVerticalPoint (3 / 2 : ℝ) t) ^ 2) := by
      apply hbase.congr
      filter_upwards [] with t
      rw [estermannDirichletSeries_zero_one_eq_zeta_sq]
      norm_num [estermannVerticalPoint]
    exact hzeta.const_mul z⁻¹ |>.congr
      (Eventually.of_forall fun t => by
        unfold bettinConreyReciprocalInitialIntegrand
        dsimp only
        ring)
  have hzero : ∀ᵐ t : ℝ, t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hneg' : Integrable (fun t : ℝ =>
      -I * bettinConreyReciprocalSquareZetaIntegrand z t) :=
    hinitial.comp_neg.congr (by
      filter_upwards [hzero] with t ht
      exact reciprocalInitialIntegrand_neg_eq_reciprocalSquare z hz ht)
  exact (hneg'.const_mul I).congr (Eventually.of_forall fun t => by
    calc
      I * (-I * bettinConreyReciprocalSquareZetaIntegrand z t) =
          -(I * I) * bettinConreyReciprocalSquareZetaIntegrand z t := by ring
      _ = _ := by rw [I_mul_I]; ring)

theorem central_exponential_cotangent_identity (t : ℝ) :
    let s := bettinConreyCentralVerticalPoint t
    Complex.exp ((Real.pi : ℂ) * I * s / 2) +
        I * (Complex.exp ((Real.pi : ℂ) * I * s / 2) *
          Complex.cos ((Real.pi : ℂ) * s / 2) /
            Complex.sin ((Real.pi : ℂ) * s / 2)) =
      I / Complex.sin ((Real.pi : ℂ) * s / 2) := by
  let s := bettinConreyCentralVerticalPoint t
  let x := (Real.pi : ℂ) * s / 2
  have hsin : Complex.sin x ≠ 0 := by
    simpa [x, s] using sin_pi_mul_central_div_two_ne_zero t
  have hexp : Complex.exp ((Real.pi : ℂ) * I * s / 2) =
      Complex.cos x + Complex.sin x * I := by
    rw [show (Real.pi : ℂ) * I * s / 2 = x * I by
      simp only [x]
      ring,
      Complex.exp_mul_I]
  change Complex.exp ((Real.pi : ℂ) * I * s / 2) +
      I * (Complex.exp ((Real.pi : ℂ) * I * s / 2) *
        Complex.cos x / Complex.sin x) = I / Complex.sin x
  rw [hexp]
  field_simp [hsin]
  calc
    (Complex.cos x + Complex.sin x * I) *
        (Complex.sin x + Complex.cos x * I) =
      (Complex.cos x ^ 2 + Complex.sin x ^ 2) * I +
        (Complex.cos x * Complex.sin x) * (1 + I * I) := by ring
    _ = (Complex.cos x ^ 2 + Complex.sin x ^ 2) * I := by
      rw [I_mul_I]
      ring
    _ = I := by rw [Complex.cos_sq_add_sin_sq, one_mul]

/-- The two phases in equations (18)--(19) combine pointwise to `i` times
the square-zeta representation of `g₀`. -/
theorem primary_add_I_reciprocal_eq_I_gZeroSquare
    (z : ℂ) (t : ℝ) :
    bettinConreyPrimarySquareZetaIntegrand z t +
        I * bettinConreyReciprocalSquareZetaIntegrand z t =
      I * bettinConreyGZeroSquareVerticalIntegrand z t := by
  let s := bettinConreyCentralVerticalPoint t
  have hphase := central_exponential_cotangent_identity t
  unfold bettinConreyPrimarySquareZetaIntegrand
    bettinConreyReciprocalSquareZetaIntegrand
    bettinConreyGZeroSquareVerticalIntegrand
  dsimp only
  change Complex.Gamma s * riemannZeta s ^ 2 *
        Complex.exp ((Real.pi : ℂ) * I * s / 2) *
          ((2 * Real.pi : ℂ) * z) ^ (-s) +
      I * (Complex.Gamma s * riemannZeta s ^ 2 *
        Complex.exp ((Real.pi : ℂ) * I * s / 2) *
        Complex.cos ((Real.pi : ℂ) * s / 2) /
          Complex.sin ((Real.pi : ℂ) * s / 2) *
        ((2 * Real.pi : ℂ) * z) ^ (-s)) =
      I * (riemannZeta s ^ 2 * Complex.Gamma s /
        Complex.sin ((Real.pi : ℂ) * s / 2) *
        ((2 * Real.pi : ℂ) * z) ^ (-s))
  calc
    _ = Complex.Gamma s * riemannZeta s ^ 2 *
        (Complex.exp ((Real.pi : ℂ) * I * s / 2) +
          I * (Complex.exp ((Real.pi : ℂ) * I * s / 2) *
            Complex.cos ((Real.pi : ℂ) * s / 2) /
              Complex.sin ((Real.pi : ℂ) * s / 2))) *
        ((2 * Real.pi : ℂ) * z) ^ (-s) := by ring
    _ = _ := by rw [hphase]; ring

theorem integrable_bettinConreyGZeroSquareVerticalIntegrand
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (bettinConreyGZeroSquareVerticalIntegrand z) := by
  have hp := integrable_bettinConreyPrimarySquareZetaIntegrand z hz
  have hr := integrable_bettinConreyReciprocalSquareZetaIntegrand z hz
  have hsum := hp.add (hr.const_mul I)
  have hI : I ≠ 0 := I_ne_zero
  have hscaled : Integrable (fun t : ℝ =>
      I * bettinConreyGZeroSquareVerticalIntegrand z t) :=
    hsum.congr (Eventually.of_forall fun t =>
      primary_add_I_reciprocal_eq_I_gZeroSquare z t)
  exact (hscaled.const_mul (-I)).congr
    (Eventually.of_forall fun t => by
      change -I * (I * bettinConreyGZeroSquareVerticalIntegrand z t) = _
      calc
        -I * (I * bettinConreyGZeroSquareVerticalIntegrand z t) =
            -(I * I) * bettinConreyGZeroSquareVerticalIntegrand z t := by ring
        _ = _ := by rw [I_mul_I]; ring)

/-- Integral combination corresponding to the trigonometric identity at the
end of the proof of Bettin--Conrey Theorem 1. -/
theorem primaryIntegral_add_I_reciprocalIntegral_eq_I_gZeroSquareIntegral
    (z : ℂ) (hz : 0 < z.im) :
    (∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t) +
        I * (∫ t : ℝ, bettinConreyReciprocalSquareZetaIntegrand z t) =
      I * ∫ t : ℝ, bettinConreyGZeroSquareVerticalIntegrand z t := by
  have hp := integrable_bettinConreyPrimarySquareZetaIntegrand z hz
  have hr := integrable_bettinConreyReciprocalSquareZetaIntegrand z hz
  calc
    (∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t) +
        I * (∫ t : ℝ, bettinConreyReciprocalSquareZetaIntegrand z t) =
      (∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t) +
        ∫ t : ℝ, I * bettinConreyReciprocalSquareZetaIntegrand z t := by
          rw [integral_const_mul]
    _ = ∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t +
        I * bettinConreyReciprocalSquareZetaIntegrand z t := by
          rw [integral_add hp (hr.const_mul I)]
    _ = ∫ t : ℝ, I * bettinConreyGZeroSquareVerticalIntegrand z t := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact primary_add_I_reciprocal_eq_I_gZeroSquare z t
    _ = _ := by rw [integral_const_mul]

/-- The complete central Lambert period is already the elementary residue
plus the exact `g₀` contribution. -/
theorem centralLambertPeriod_eq_residue_add_gZero
    (z : ℂ) (hz : 0 < z.im) :
    bettinConreyCentralLambertPeriod z =
      bettinConreyLambertResidue z + I / 2 * bettinConreyGZero z := by
  have hprimary := centralLambertSeries_eq_residue_add_primaryIntegral z hz
  have hreciprocal :=
    reciprocalCentralLambertSeries_eq_reciprocalIntegral z hz
  have hcombine :=
    primaryIntegral_add_I_reciprocalIntegral_eq_I_gZeroSquareIntegral z hz
  have hgzero := bettinConreyGZero_eq_squareIntegral z hz
  unfold bettinConreyCentralLambertPeriod centralPeriodOf
  rw [hprimary, hreciprocal]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_pos.ne'
  have hgdiv : bettinConreyGZero z =
      (∫ t : ℝ, bettinConreyGZeroSquareVerticalIntegrand z t) /
        (Real.pi : ℂ) := by
    rw [hgzero]
    field_simp [hpi]
  have hgscaled :
      (∫ t : ℝ, bettinConreyGZeroSquareVerticalIntegrand z t) =
        (Real.pi : ℂ) * bettinConreyGZero z := by
    have h := (eq_div_iff hpi).mp hgdiv
    calc
      _ = bettinConreyGZero z * (Real.pi : ℂ) := h.symm
      _ = _ := by ring
  have hsum :
      (∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t) +
          I * (∫ t : ℝ,
            bettinConreyReciprocalSquareZetaIntegrand z t) =
        I * ((Real.pi : ℂ) * bettinConreyGZero z) := by
    calc
      _ = I * ∫ t : ℝ,
          bettinConreyGZeroSquareVerticalIntegrand z t := hcombine
      _ = I * ((Real.pi : ℂ) * bettinConreyGZero z) := by
        rw [hgscaled]
  calc
    bettinConreyLambertResidue z +
          1 / (2 * Real.pi : ℂ) *
            (∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t) -
        (-I / (2 * Real.pi : ℂ)) *
          (∫ t : ℝ, bettinConreyReciprocalSquareZetaIntegrand z t) =
      bettinConreyLambertResidue z +
        1 / (2 * Real.pi : ℂ) *
          ((∫ t : ℝ, bettinConreyPrimarySquareZetaIntegrand z t) +
            I * (∫ t : ℝ,
              bettinConreyReciprocalSquareZetaIntegrand z t)) := by ring
    _ = bettinConreyLambertResidue z +
        1 / (2 * Real.pi : ℂ) *
          (I * ((Real.pi : ℂ) * bettinConreyGZero z)) := by rw [hsum]
    _ = _ := by field_simp [hpi]

/-! ## Residue normalization and the unconditional identification -/

theorem log_lambertAbelParameter_upperHalfPlane
    (z : ℂ) (hz : 0 < z.im) :
    Complex.log (bettinConreyLambertAbelParameter z) =
      Complex.log ((2 * Real.pi : ℂ) * z) -
        (Real.pi : ℂ) / 2 * I := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im hz.ne'
  have hneg0 : -I * z ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0
  have hparameter : bettinConreyLambertAbelParameter z =
      (-I * z) * (2 * Real.pi : ℂ) := by
    unfold bettinConreyLambertAbelParameter
    ring
  have hleft :
      Complex.log (bettinConreyLambertAbelParameter z) =
        ((Real.log (2 * Real.pi) : ℝ) : ℂ) + Complex.log (-I * z) := by
    rw [hparameter]
    convert Complex.log_mul_ofReal
      (2 * Real.pi) (by positivity) (-I * z) hneg0 using 1 <;>
      push_cast <;> ring
  have hright :
      Complex.log ((2 * Real.pi : ℂ) * z) =
        ((Real.log (2 * Real.pi) : ℝ) : ℂ) + Complex.log z := by
    rw [mul_comm]
    convert Complex.log_mul_ofReal
      (2 * Real.pi) (by positivity) z hz0 using 1 <;>
      push_cast <;> ring
  rw [hleft, hright, log_neg_I_mul_upperHalfPlane z hz]
  ring

/-- The residue crossed in equation (18) is exactly the elementary mode in
the source definition of `psi₀`. -/
theorem bettinConreyLambertResidue_eq_elementary
    (z : ℂ) (hz : 0 < z.im) :
    bettinConreyLambertResidue z =
      (1 - z⁻¹) / 4 +
        (Complex.log ((2 * Real.pi : ℂ) * z) -
          (Real.eulerMascheroniConstant : ℂ)) /
          (2 * (Real.pi : ℂ) * I * z) := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im hz.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_pos.ne'
  have hparameter : bettinConreyLambertAbelParameter z =
      -(2 * Real.pi : ℂ) * I * z := rfl
  unfold bettinConreyLambertResidue
  rw [log_lambertAbelParameter_upperHalfPlane z hz, hparameter]
  field_simp [hz0, hpi, I_ne_zero]
  ring

/-- All classical analytic inputs in the Lambert/`psi₀` bridge are now
discharged.  This is the unconditional inhabitant consumed by the Route C
central Abel constructor. -/
noncomputable def bettinConreyLambertPsiZeroIdentification_proved :
    BettinConreyLambertPsiZeroIdentification where
  eq_on_upperHalfPlane z hz := by
    rw [centralLambertPeriod_eq_residue_add_gZero z hz,
      bettinConreyLambertResidue_eq_elementary z hz]
    unfold bettinConreyPsiZero
    have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im hz.ne'
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_pos.ne'
    field_simp [hz0, hpi, I_ne_zero]
    rw [I_sq]
    ring

/-- The finite Abel endpoint, right-half-plane continuity, and the preceding
Lambert identification assemble into the complete unconditional Phase 3
constructor. -/
noncomputable def bettinConreyCentralAbelConstructorData_proved :
    RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelCentralConstructor.BettinConreyCentralAbelConstructorData :=
  bettinConreyCentralAbelConstructorData_of_identification_proved
    bettinConreyLambertPsiZeroIdentification_proved

/-- Unconditional central rational Bettin--Conrey theorem supplied by the
completed Phase 3 chain. -/
noncomputable def bettinConreyPsiZeroCentralRationalTheorem_proved :
    RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralOnlyAssembly.BettinConreyPsiZeroCentralRationalTheorem :=
  bettinConreyPsiZeroCentralRationalTheorem_of_identification
    bettinConreyLambertPsiZeroIdentification_proved

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPhaseEvaluation
