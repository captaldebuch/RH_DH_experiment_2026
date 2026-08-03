import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelHorizontal

/-!
# Route C: the reciprocal rational row on the exact complex Abel contour

The reciprocal Lambert row carries the fixed phase `exp(-2*pi*i*k*n/h)`.
This module identifies that phase with a canonical negative Estermann
numerator modulo `h`, proves absolute summability of the complex-damped row,
and specializes the infinite two-pole contour identity to the exact
reciprocal Abel ray.

No residue or endpoint term is estimated separately.  The output retains the
Lambert row and both Laurent contributions in the same exact identity, which
is the form required before the coupled `delta -> 0+` boundary limit.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCReciprocalContour

open Complex Filter MeasureTheory Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelComplexDamping
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelBoundary
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzGrowth
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReciprocalRay
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelHorizontal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexEstermannMellin

/-- Canonical representative of the negative rational twist `-k (mod h)`. -/
noncomputable def bettinConreyNegativeTwist (h k : ℕ) : ℕ :=
  (-(k : ZMod h)).val

@[simp] theorem bettinConreyNegativeTwist_cast
    (h k : ℕ) [NeZero h] :
    (bettinConreyNegativeTwist h k : ZMod h) = -(k : ZMod h) := by
  unfold bettinConreyNegativeTwist
  exact ZMod.natCast_zmod_val _

/-- The canonical negative Estermann phase is exactly the fixed reciprocal
phase occurring in Bettin--Conrey's second Lambert row. -/
theorem estermannAdditivePhase_negativeTwist
    (h k n : ℕ) [NeZero h] :
    estermannAdditivePhase (bettinConreyNegativeTwist h k) h n =
      Complex.exp
        (-(2 * Real.pi : ℂ) * Complex.I * (n : ℂ) *
          (((k : ℝ) / (h : ℝ) : ℝ) : ℂ)) := by
  rw [estermannAdditivePhase_eq_stdAddChar]
  have hcast :
      (((bettinConreyNegativeTwist h k) * n : ℕ) : ZMod h) =
        -(((k * n : ℕ) : ZMod h)) := by
    push_cast
    rw [bettinConreyNegativeTwist_cast]
    ring
  rw [hcast, AddChar.map_neg_eq_inv]
  rw [← estermannAdditivePhase_eq_stdAddChar k h n]
  unfold estermannAdditivePhase
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  field_simp

/-- Absolute summability of the complete complex-damped Estermann Lambert
row.  This is extracted from the already proved global rowwise `L¹` bound,
so it introduces no new estimate. -/
theorem summable_complexDampedEstermannLambertSeries
    (a q : ℕ) {u : ℂ} (hu : 0 < u.re) :
    Summable (fun n : ℕ =>
      LSeries.term (estermannCoeff a q) 0 n *
        Complex.exp (-(u * (n : ℂ)))) := by
  have hnorm :=
    summable_integral_norm_complexAbelMellinEstermannTerm a q hu
  have hint : Summable (fun n : ℕ =>
      ∫ t : ℝ, complexAbelMellinEstermannTerm a q u n t) := by
    rw [← summable_norm_iff]
    exact hnorm.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_integral_le_integral_norm _)
  have hscaled : Summable (fun n : ℕ =>
      ((2 * Real.pi : ℝ) : ℂ) *
        (LSeries.term (estermannCoeff a q) 0 n *
          Complex.exp (-(u * (n : ℂ))))) := by
    exact hint.congr fun n =>
      integral_complexAbelMellinEstermannTerm a q hu n
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  simpa only [inv_mul_cancel_left₀ h2pi] using
    hscaled.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)

/-- The exact reciprocal Lambert row is the complex-damped Estermann series
with the canonical negative numerator. -/
theorem complexDampedEstermannLambertSeries_negativeTwist
    (h k : ℕ) {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hdelta : 0 < delta) :
    complexDampedEstermannLambertSeries
        (bettinConreyNegativeTwist h k) h
        (bettinConreyReciprocalComplexDamping h k delta) =
      bettinConreyReciprocalComplexDampedSeries h k delta := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  have hu : 0 <
      (bettinConreyReciprocalComplexDamping h k delta).re := by
    rw [bettinConreyReciprocalComplexDamping_re]
    exact bettinConreyReciprocalRealDamping_pos h k hh hk hdelta
  have hs := summable_complexDampedEstermannLambertSeries
    (bettinConreyNegativeTwist h k) h hu
  unfold complexDampedEstermannLambertSeries
    bettinConreyReciprocalComplexDampedSeries
  rw [hs.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_mul, zero_add]
  apply tsum_congr
  intro n
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),
    Complex.cpow_zero, div_one]
  unfold estermannCoeff
  rw [estermannDivisorCoeff_apply,
    estermannAdditivePhase_negativeTwist]
  push_cast
  simp only [Nat.succ_eq_add_one, Nat.add_comm n 1]
  ring_nf

/-- Exact infinite two-pole contour identity on the reciprocal rational Abel
ray.  The complex Lambert row and the two Laurent contributions remain
coupled, ready for the final Abel finite-part cancellation. -/
theorem reciprocalComplexAbel_rightVertical_eq_series_add_residues
    (h k : ℕ) [NeZero h] {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    let u := bettinConreyReciprocalComplexDamping h k delta
    let a := bettinConreyNegativeTwist h k
    estermannPrimalVerticalIntegral a h (3 / 2 : ℝ)
        (bettinConreyComplexAbelReflectionWeight u) =
      -(2 * Real.pi : ℝ) *
          bettinConreyReciprocalComplexDampedSeries h k delta +
        2 * Real.pi *
          (estermannWeightedResidueCoefficient a h
              (bettinConreyComplexAbelReflectionWeight u) +
            estermannHurwitzContinuation a h 0) := by
  dsimp only
  let u := bettinConreyReciprocalComplexDamping h k delta
  have hu : 0 < u.re := by
    dsimp only [u]
    rw [bettinConreyReciprocalComplexDamping_re]
    exact bettinConreyReciprocalRealDamping_pos h k hh hk hdelta
  have harg : |Complex.arg u| ≤ Real.pi / 4 := by
    dsimp only [u]
    exact reciprocalComplexDamping_abs_arg_le_pi_div_four
      h k hh hk hdelta hdeltaOne
  have htheta : Real.pi / 4 < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  rw [complexAbel_rightVertical_eq_damped_add_residues
      hu harg htheta (bettinConreyNegativeTwist h k) h]
  rw [complexDampedEstermannLambertSeries_negativeTwist
      h k hh hk hdelta]

/-! ## The complete coupled finite part -/

/-- The two Laurent contributions crossed by the reciprocal complex Abel
contour.  They are kept as one package because their singular behavior must
cancel against the first Lambert row only after the rational period has been
reassembled. -/
noncomputable def bettinConreyReciprocalResiduePackage
    (h k : ℕ) [NeZero h] (delta : ℝ) : ℂ :=
  let u := bettinConreyReciprocalComplexDamping h k delta
  let a := bettinConreyNegativeTwist h k
  estermannWeightedResidueCoefficient a h
      (bettinConreyComplexAbelReflectionWeight u) +
    estermannHurwitzContinuation a h 0

/-- The reflected vertical contribution after solving the reciprocal contour
identity for its Lambert row and restoring the factor from the central
period. -/
noncomputable def bettinConreyReciprocalVerticalContribution
    (h k : ℕ) [NeZero h] (delta : ℝ) : ℂ :=
  let u := bettinConreyReciprocalComplexDamping h k delta
  let a := bettinConreyNegativeTwist h k
  (bettinConreyRationalDampedPoint h k delta)⁻¹ *
    ((2 * Real.pi : ℂ)⁻¹ *
      estermannPrimalVerticalIntegral a h (3 / 2 : ℝ)
        (bettinConreyComplexAbelReflectionWeight u))

/-- The genuine coupled finite part: the first real-damped Lambert row minus
the reciprocal Laurent package.  Neither summand is assigned a boundary
value separately. -/
noncomputable def bettinConreyCoupledContourFinitePart
    (h k : ℕ) [NeZero h] (delta : ℝ) : ℂ :=
  dampedEstermannLambertSeries h k
      (bettinConreyRationalDamping h k delta) -
    (bettinConreyRationalDampedPoint h k delta)⁻¹ *
      bettinConreyReciprocalResiduePackage h k delta

/-- Exact finite-`delta` reconstruction of the complete rational period.
This is the central bookkeeping identity: first row, both residues, and the
reflected vertical error are assembled before any limit is taken. -/
theorem rationalDampedPeriod_eq_coupledFinitePart_add_vertical
    (h k : ℕ) [NeZero h] {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    bettinConreyRationalDampedPeriod h k delta =
      bettinConreyCoupledContourFinitePart h k delta +
        bettinConreyReciprocalVerticalContribution h k delta := by
  rw [rationalDampedPeriod_eq_real_add_reciprocalComplex
      h k hh hk hdelta]
  unfold bettinConreyCoupledContourFinitePart
    bettinConreyReciprocalVerticalContribution
    bettinConreyReciprocalResiduePackage
  dsimp only
  rw [reciprocalComplexAbel_rightVertical_eq_series_add_residues
      h k hh hk hdelta hdeltaOne]
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  field_simp [h2pi]
  push_cast
  ring

/-- The reflected vertical contribution vanishes on the genuine reciprocal
ray.  Thus all remaining boundary content is concentrated in the coupled
first-row/residue finite part. -/
theorem tendsto_bettinConreyReciprocalVerticalContribution_zero
    (h k : ℕ) [NeZero h] (hh : 0 < h) (hk : 0 < k) :
    Tendsto (bettinConreyReciprocalVerticalContribution h k)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  let a := bettinConreyNegativeTwist h k
  have hvertical : Tendsto (fun delta : ℝ =>
      estermannPrimalVerticalIntegral a h (3 / 2 : ℝ)
        (bettinConreyComplexAbelReflectionWeight
          (bettinConreyReciprocalComplexDamping h k delta)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_reciprocalComplexAbelRightLine_zero
      (estermannNegativeHalfPolynomialGrowth a h) h k hh hk
  have hpoint := tendsto_bettinConreyRationalDampedPoint_zero h k
  have hboundary :
      ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero hhR hkR)
  have hinv := hpoint.inv₀ hboundary
  have hscaled := hinv.mul_const ((2 * Real.pi : ℂ)⁻¹)
  have hproduct := hscaled.mul hvertical
  convert hproduct using 1
  · funext delta
    unfold bettinConreyReciprocalVerticalContribution
    dsimp only
    ring
  · simp

/-- Consequently the full rational period and the coupled contour finite
part have the same Abel boundary limit. -/
theorem tendsto_rationalDampedPeriod_sub_coupledFinitePart_zero
    (h k : ℕ) [NeZero h] (hh : 0 < h) (hk : 0 < k) :
    Tendsto (fun delta : ℝ =>
        bettinConreyRationalDampedPeriod h k delta -
          bettinConreyCoupledContourFinitePart h k delta)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  apply (tendsto_bettinConreyReciprocalVerticalContribution_zero
    h k hh hk).congr'
  filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds] with delta hdelta hdeltaOne
  rw [rationalDampedPeriod_eq_coupledFinitePart_add_vertical
      h k hh hk hdelta hdeltaOne.le]
  ring

/-- Exact stop test for the rational Abel boundary: after the unconditional
contour work above, the original coupled period has its prescribed boundary
value if and only if the first-row/two-residue finite part has that value.
This is the next analytic target, with the vanishing vertical line removed. -/
theorem tendsto_rationalDampedPeriod_iff_coupledFinitePart
    (h k : ℕ) [NeZero h] (hh : 0 < h) (hk : 0 < k) :
    Tendsto (bettinConreyRationalDampedPeriod h k)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (bettinConreyCentralAbelBoundaryValue h k)) ↔
      Tendsto (bettinConreyCoupledContourFinitePart h k)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (bettinConreyCentralAbelBoundaryValue h k)) := by
  let b := bettinConreyCentralAbelBoundaryValue h k
  have hvertical :=
    tendsto_bettinConreyReciprocalVerticalContribution_zero h k hh hk
  have hdiff :=
    tendsto_rationalDampedPeriod_sub_coupledFinitePart_zero h k hh hk
  constructor
  · intro hperiod
    have hsub := hperiod.sub hdiff
    convert hsub using 1
    · funext delta
      ring
    · dsimp only [b]
      simp
  · intro hfinite
    have hadd := hfinite.add hvertical
    have hadd' : Tendsto (fun delta : ℝ =>
        bettinConreyCoupledContourFinitePart h k delta +
          bettinConreyReciprocalVerticalContribution h k delta)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (bettinConreyCentralAbelBoundaryValue h k)) := by
      simpa using hadd
    apply hadd'.congr'
    filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
          nhdsWithin_le_nhds] with delta hdelta hdeltaOne
    exact (rationalDampedPeriod_eq_coupledFinitePart_add_vertical
      h k hh hk hdelta hdeltaOne.le).symm

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCReciprocalContour
