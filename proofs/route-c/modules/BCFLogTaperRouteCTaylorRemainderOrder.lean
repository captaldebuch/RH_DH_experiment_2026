import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorInfiniteRectangle

/-!
# Route C: radial order of the finite Taylor remainder

The preceding contour module bounds the exact left-line remainder by an
integral whose dependence on the complex parameter is already explicit.
Here that radial factor is pulled outside the integral.  For every fixed
order and every closed angular sector strictly inside the principal slit
plane, this gives a genuine uniform estimate

`‖R_M(u)‖ ≤ C(M,theta) * ‖u‖^(2M-1/2)`.

The module also records this estimate as Mathlib `IsBigO` data and proves
that the remainder tends to zero at the vertex of the punctured sector.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorRemainderOrder

open Complex Filter MeasureTheory Set Topology Asymptotics
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFEFactor
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorInfiniteRectangle
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorLineMajorant

/-- The radial order supplied by the order-`M` left contour. -/
noncomputable def routeCTaylorRemainderExponent (M : ℕ) : ℝ :=
  2 * M - 1 / 2

theorem routeCTaylorRemainderExponent_pos
    (M : ℕ) (hM : 1 ≤ M) :
    0 < routeCTaylorRemainderExponent M := by
  unfold routeCTaylorRemainderExponent
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  linarith

/-- The parameter-free vertical profile left after removing the radial
power from the shifted-line majorant. -/
noncomputable def routeCTaylorRemainderProfile
    (n : ℕ) (theta t : ℝ) : ℝ :=
  (1 + routeCTaylorFEPolynomial n t) *
    Real.exp (-(Real.pi - theta) * |t|)

theorem routeCTaylorRemainderProfile_nonneg
    (n : ℕ) (theta t : ℝ) :
    0 ≤ routeCTaylorRemainderProfile n theta t := by
  unfold routeCTaylorRemainderProfile
  have hpoly := routeCTaylorFEPolynomial_nonneg n t
  positivity

/-- Exact separation of the complex radial parameter from the vertical
majorant. -/
theorem routeCTaylorLineMajorant_eq_radial_mul_profile
    (u : ℂ) (n : ℕ) (theta t : ℝ) :
    routeCTaylorLineMajorant u n theta t =
      (162 * ‖u‖ ^ ((n : ℝ) - 1 / 2)) *
        routeCTaylorRemainderProfile n theta t := by
  unfold routeCTaylorLineMajorant routeCTaylorRemainderProfile
  ring

/-- The same separation after integration over the complete vertical
parameter line. -/
theorem integral_routeCTaylorLineMajorant_eq_radial_mul
    (u : ℂ) (n : ℕ) (theta : ℝ) :
    (∫ t : ℝ, routeCTaylorLineMajorant u n theta t) =
      (162 * ‖u‖ ^ ((n : ℝ) - 1 / 2)) *
        ∫ t : ℝ, routeCTaylorRemainderProfile n theta t := by
  simp_rw [routeCTaylorLineMajorant_eq_radial_mul_profile]
  exact integral_const_mul _ _

/-- A finite constant depending only on the contour order and the angular
sector.  The Bochner integral is total; below it is also proved nonnegative.
-/
noncomputable def routeCTaylorRemainderConstant
    (M : ℕ) (theta : ℝ) : ℝ :=
  ‖(1 / (Real.pi : ℂ))‖ * 162 *
    ∫ t : ℝ, routeCTaylorRemainderProfile (2 * M) theta t

theorem routeCTaylorRemainderConstant_nonneg
    (M : ℕ) (theta : ℝ) :
    0 ≤ routeCTaylorRemainderConstant M theta := by
  have hintegral : 0 ≤
      ∫ t : ℝ, routeCTaylorRemainderProfile (2 * M) theta t :=
    integral_nonneg fun t =>
      routeCTaylorRemainderProfile_nonneg (2 * M) theta t
  unfold routeCTaylorRemainderConstant
  positivity

/-- Uniform radial estimate for the exact contour remainder. -/
theorem norm_bettinConreyGZeroFiniteTaylorRemainder_le_rpow
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (hM : 1 ≤ M)
    (theta : ℝ) (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi) :
    ‖bettinConreyGZeroFiniteTaylorRemainder u M‖ ≤
      routeCTaylorRemainderConstant M theta *
        ‖u‖ ^ routeCTaylorRemainderExponent M := by
  calc
    ‖bettinConreyGZeroFiniteTaylorRemainder u M‖ ≤
        ‖(1 / (Real.pi : ℂ))‖ *
          ∫ t : ℝ, routeCTaylorLineMajorant u (2 * M) theta t :=
      norm_bettinConreyGZeroFiniteTaylorRemainder_le
        u hu M hM theta harg htheta
    _ = routeCTaylorRemainderConstant M theta *
        ‖u‖ ^ routeCTaylorRemainderExponent M := by
      rw [integral_routeCTaylorLineMajorant_eq_radial_mul]
      unfold routeCTaylorRemainderConstant routeCTaylorRemainderExponent
      push_cast
      ring

/-- The punctured closed sector on which the principal-power estimate is
uniform. -/
def routeCTaylorClosedPuncturedSector (theta : ℝ) : Set ℂ :=
  {u | u ≠ 0 ∧ |Complex.arg u| ≤ theta}

/-- The exact remainder is uniformly big-O of the radial contour order on
every fixed proper sector. -/
theorem bettinConreyGZeroFiniteTaylorRemainder_isBigO
    (M : ℕ) (hM : 1 ≤ M) (theta : ℝ)
    (htheta : theta < Real.pi) :
    (fun u : ℂ => bettinConreyGZeroFiniteTaylorRemainder u M) =O[
      nhdsWithin 0 (routeCTaylorClosedPuncturedSector theta)]
      (fun u : ℂ => ‖u‖ ^ routeCTaylorRemainderExponent M) := by
  apply IsBigO.of_bound (routeCTaylorRemainderConstant M theta)
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hbound := norm_bettinConreyGZeroFiniteTaylorRemainder_le_rpow
    u hu.1 M hM theta hu.2 htheta
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg u) _)] using hbound

/-- Below the contour order, the remainder is little-o of every prescribed
radial degree.  This is the degree-by-degree form used when finite Taylor
coefficients are extracted. -/
theorem bettinConreyGZeroFiniteTaylorRemainder_isLittleO
    (M : ℕ) (hM : 1 ≤ M) (theta : ℝ)
    (htheta : theta < Real.pi) (degree : ℝ)
    (hdegree : degree < routeCTaylorRemainderExponent M) :
    (fun u : ℂ => bettinConreyGZeroFiniteTaylorRemainder u M) =o[
      nhdsWithin 0 (routeCTaylorClosedPuncturedSector theta)]
      (fun u : ℂ => ‖u‖ ^ degree) := by
  let l : Filter ℂ :=
    nhdsWithin 0 (routeCTaylorClosedPuncturedSector theta)
  have hid : Tendsto (fun u : ℂ => u) l (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hnorm : Tendsto (fun u : ℂ => ‖u‖) l (nhds 0) := by
    simpa using hid.norm
  have hdiff : 0 < routeCTaylorRemainderExponent M - degree :=
    sub_pos.mpr hdegree
  have hrpowAt : Tendsto
      (fun x : ℝ => x ^
        (routeCTaylorRemainderExponent M - degree))
      (nhds 0) (nhds 0) := by
    simpa [Real.zero_rpow hdiff.ne'] using
      (Real.continuousAt_rpow_const 0
        (routeCTaylorRemainderExponent M - degree)
        (Or.inr hdiff.le)).tendsto
  have hratio : Tendsto
      (fun u : ℂ =>
        ‖u‖ ^ routeCTaylorRemainderExponent M /
          ‖u‖ ^ degree)
      l (nhds 0) := by
    apply (hrpowAt.comp hnorm).congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    change ‖u‖ ^ (routeCTaylorRemainderExponent M - degree) = _
    rw [Real.rpow_sub (norm_pos_iff.mpr hu.1)]
  have hzero : ∀ᶠ u : ℂ in l,
      ‖u‖ ^ degree = 0 →
        ‖u‖ ^ routeCTaylorRemainderExponent M = 0 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    intro hpow
    have hpos : 0 < ‖u‖ ^ degree :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr hu.1) degree
    exact (hpos.ne' hpow).elim
  have hradial :
      (fun u : ℂ => ‖u‖ ^ routeCTaylorRemainderExponent M) =o[l]
        (fun u : ℂ => ‖u‖ ^ degree) :=
    (isLittleO_iff_tendsto' hzero).2 hratio
  exact (bettinConreyGZeroFiniteTaylorRemainder_isBigO
    M hM theta htheta).trans_isLittleO hradial

/-- Positivity of the radial exponent turns the quantitative estimate into
vanishing of the exact contour remainder at the sector vertex. -/
theorem tendsto_bettinConreyGZeroFiniteTaylorRemainder_zero
    (M : ℕ) (hM : 1 ≤ M) (theta : ℝ)
    (htheta : theta < Real.pi) :
    Tendsto
      (fun u : ℂ => bettinConreyGZeroFiniteTaylorRemainder u M)
      (nhdsWithin 0 (routeCTaylorClosedPuncturedSector theta))
      (nhds 0) := by
  have hexponent := routeCTaylorRemainderExponent_pos M hM
  have hid : Tendsto (fun u : ℂ => u)
      (nhdsWithin 0 (routeCTaylorClosedPuncturedSector theta))
      (nhds 0) := tendsto_id.mono_left inf_le_left
  have hnorm : Tendsto (fun u : ℂ => ‖u‖)
      (nhdsWithin 0 (routeCTaylorClosedPuncturedSector theta))
      (nhds 0) := by
    simpa using hid.norm
  have hrpowAt : Tendsto
      (fun x : ℝ => x ^ routeCTaylorRemainderExponent M)
      (nhds 0) (nhds 0) := by
    simpa [Real.zero_rpow hexponent.ne'] using
      (Real.continuousAt_rpow_const 0
        (routeCTaylorRemainderExponent M)
        (Or.inr hexponent.le)).tendsto
  have hrpowZero : Tendsto
      (fun u : ℂ => ‖u‖ ^ routeCTaylorRemainderExponent M)
      (nhdsWithin 0 (routeCTaylorClosedPuncturedSector theta))
      (nhds 0) := hrpowAt.comp hnorm
  have hprofile : Tendsto
      (fun u : ℂ => routeCTaylorRemainderConstant M theta *
        ‖u‖ ^ routeCTaylorRemainderExponent M)
      (nhdsWithin 0 (routeCTaylorClosedPuncturedSector theta))
      (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hrpowZero)
  apply squeeze_zero_norm'
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact norm_bettinConreyGZeroFiniteTaylorRemainder_le_rpow
      u hu.1 M hM theta hu.2 htheta
  · exact hprofile

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorRemainderOrder
