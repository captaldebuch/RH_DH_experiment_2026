import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelBoundary
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelFinitePart

/-!
# Route C: exact reciprocal Abel ray

The first Lambert row on Bettin--Conrey's rational path has a fixed additive
phase and positive real damping.  The reciprocal row is subtler: inversion
makes its additive phase drift by a quadratic amount.  This module records
that geometry exactly and packages the row as a complex-damped fixed rational
phase.

The resulting damping parameter has positive real part and satisfies
`Im(u) / Re(u) = -delta`.  Thus it approaches zero inside a shrinking sector.
This is the precise domain on which the remaining complex Abel finite-part
theorem must be proved.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReciprocalRay

open Complex Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelBoundary
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPeriod

/-- The second Lambert argument on the rational Abel path. -/
noncomputable def bettinConreyReciprocalDampedPoint
    (h k : ℕ) (delta : ℝ) : ℂ :=
  -(bettinConreyRationalDampedPoint h k delta)⁻¹

/-- Its real part is the fixed rational phase `-k/h` plus a quadratic
displacement. -/
theorem bettinConreyReciprocalDampedPoint_re
    (h k : ℕ) (delta : ℝ) (hh : 0 < h) (hk : 0 < k) :
    (bettinConreyReciprocalDampedPoint h k delta).re =
      -((k : ℝ) / (h : ℝ)) / (1 + delta ^ 2) := by
  unfold bettinConreyReciprocalDampedPoint
    bettinConreyRationalDampedPoint
  rw [Complex.neg_re, Complex.inv_re, Complex.normSq_apply]
  norm_num
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hden : 1 + delta ^ 2 ≠ 0 := by positivity
  field_simp [hhR, hkR, hden]

/-- Its imaginary part remains positive and gives the reciprocal-row
damping. -/
theorem bettinConreyReciprocalDampedPoint_im
    (h k : ℕ) (delta : ℝ) (hh : 0 < h) (hk : 0 < k) :
    (bettinConreyReciprocalDampedPoint h k delta).im =
      ((k : ℝ) / (h : ℝ)) * delta / (1 + delta ^ 2) := by
  unfold bettinConreyReciprocalDampedPoint
    bettinConreyRationalDampedPoint
  rw [Complex.neg_im, Complex.inv_im, Complex.normSq_apply]
  norm_num
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hden : 1 + delta ^ 2 ≠ 0 := by positivity
  field_simp [hhR, hkR, hden]

/-- Cartesian form of the reciprocal boundary point. -/
theorem bettinConreyReciprocalDampedPoint_eq
    (h k : ℕ) (delta : ℝ) (hh : 0 < h) (hk : 0 < k) :
    bettinConreyReciprocalDampedPoint h k delta =
      ⟨-((k : ℝ) / (h : ℝ)) / (1 + delta ^ 2),
        ((k : ℝ) / (h : ℝ)) * delta / (1 + delta ^ 2)⟩ := by
  apply Complex.ext
  · exact bettinConreyReciprocalDampedPoint_re h k delta hh hk
  · exact bettinConreyReciprocalDampedPoint_im h k delta hh hk

/-- Positive real damping of the reciprocal Lambert row. -/
noncomputable def bettinConreyReciprocalRealDamping
    (h k : ℕ) (delta : ℝ) : ℝ :=
  2 * Real.pi * ((k : ℝ) / (h : ℝ)) *
    delta / (1 + delta ^ 2)

/-- Quadratic drift of the reciprocal additive phase. -/
noncomputable def bettinConreyReciprocalPhaseDrift
    (h k : ℕ) (delta : ℝ) : ℝ :=
  2 * Real.pi * ((k : ℝ) / (h : ℝ)) *
    delta ^ 2 / (1 + delta ^ 2)

/-- The single complex damping parameter which retains both the real decay
and the additive phase drift. -/
noncomputable def bettinConreyReciprocalComplexDamping
    (h k : ℕ) (delta : ℝ) : ℂ :=
  (bettinConreyReciprocalRealDamping h k delta : ℂ) -
    Complex.I * (bettinConreyReciprocalPhaseDrift h k delta : ℂ)

theorem bettinConreyReciprocalRealDamping_pos
    (h k : ℕ) {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hdelta : 0 < delta) :
    0 < bettinConreyReciprocalRealDamping h k delta := by
  unfold bettinConreyReciprocalRealDamping
  positivity

theorem bettinConreyReciprocalComplexDamping_re
    (h k : ℕ) (delta : ℝ) :
    (bettinConreyReciprocalComplexDamping h k delta).re =
      bettinConreyReciprocalRealDamping h k delta := by
  unfold bettinConreyReciprocalComplexDamping
  norm_num

theorem bettinConreyReciprocalComplexDamping_im
    (h k : ℕ) (delta : ℝ) :
    (bettinConreyReciprocalComplexDamping h k delta).im =
      -bettinConreyReciprocalPhaseDrift h k delta := by
  unfold bettinConreyReciprocalComplexDamping
  norm_num

/-- Cartesian form of the complex damping. -/
theorem bettinConreyReciprocalComplexDamping_eq
    (h k : ℕ) (delta : ℝ) :
    bettinConreyReciprocalComplexDamping h k delta =
      ⟨bettinConreyReciprocalRealDamping h k delta,
        -bettinConreyReciprocalPhaseDrift h k delta⟩ := by
  apply Complex.ext
  · exact bettinConreyReciprocalComplexDamping_re h k delta
  · exact bettinConreyReciprocalComplexDamping_im h k delta

/-- The reciprocal damping approaches the positive axis with exact angular
slope `-delta`. -/
theorem reciprocalComplexDamping_im_div_re
    (h k : ℕ) {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hdelta : 0 < delta) :
    (bettinConreyReciprocalComplexDamping h k delta).im /
        (bettinConreyReciprocalComplexDamping h k delta).re =
      -delta := by
  rw [bettinConreyReciprocalComplexDamping_re,
    bettinConreyReciprocalComplexDamping_im]
  unfold bettinConreyReciprocalRealDamping
    bettinConreyReciprocalPhaseDrift
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdelta0 : delta ≠ 0 := hdelta.ne'
  have hden : 1 + delta ^ 2 ≠ 0 := by positivity
  field_simp [hhR, hkR, hdelta0, hden, Real.pi_ne_zero]

/-- The complex damping itself tends to zero along the rational boundary. -/
theorem tendsto_bettinConreyReciprocalComplexDamping_zero
    (h k : ℕ) :
    Tendsto (bettinConreyReciprocalComplexDamping h k)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hcont : ContinuousAt
      (bettinConreyReciprocalComplexDamping h k) 0 := by
    have hreal : ContinuousAt
        (bettinConreyReciprocalRealDamping h k) 0 := by
      unfold bettinConreyReciprocalRealDamping
      fun_prop (disch := norm_num)
    have hdrift : ContinuousAt
        (bettinConreyReciprocalPhaseDrift h k) 0 := by
      unfold bettinConreyReciprocalPhaseDrift
      fun_prop (disch := norm_num)
    unfold bettinConreyReciprocalComplexDamping
    exact (Complex.continuous_ofReal.continuousAt.comp hreal).sub
      (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp hdrift))
  simpa [bettinConreyReciprocalComplexDamping,
    bettinConreyReciprocalRealDamping,
    bettinConreyReciprocalPhaseDrift] using
      hcont.tendsto.mono_left inf_le_left

/-- Multiplication by `2*pi*i` separates the reciprocal point into its fixed
rational phase and the exact complex damping. -/
theorem two_pi_I_mul_reciprocalDampedPoint
    (h k : ℕ) (delta : ℝ) (hh : 0 < h) (hk : 0 < k) :
    (2 * Real.pi : ℂ) * Complex.I *
        bettinConreyReciprocalDampedPoint h k delta =
      -(2 * Real.pi : ℂ) * Complex.I *
          (((k : ℝ) / (h : ℝ) : ℝ) : ℂ) -
        bettinConreyReciprocalComplexDamping h k delta := by
  rw [bettinConreyReciprocalDampedPoint_eq h k delta hh hk]
  rw [bettinConreyReciprocalComplexDamping_eq]
  unfold
    bettinConreyReciprocalRealDamping
    bettinConreyReciprocalPhaseDrift
  apply Complex.ext
  · norm_num
    have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    have hden : 1 + delta ^ 2 ≠ 0 := by positivity
    field_simp [hhR, hden, Real.pi_ne_zero]
  · norm_num
    have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    have hden : 1 + delta ^ 2 ≠ 0 := by positivity
    field_simp [hhR, hden, Real.pi_ne_zero]
    ring

/-- The reciprocal row written with a fixed negative rational phase and its
exact complex damping. -/
noncomputable def bettinConreyReciprocalComplexDampedSeries
    (h k : ℕ) (delta : ℝ) : ℂ :=
  ∑' n : ℕ,
    (((n + 1).divisors.card : ℕ) : ℂ) *
      Complex.exp
        (-(2 * Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) *
          (((k : ℝ) / (h : ℝ) : ℝ) : ℂ)) *
      Complex.exp
        (-bettinConreyReciprocalComplexDamping h k delta *
          ((n + 1 : ℕ) : ℂ))

/-- Exact termwise reciprocal-ray factorization. -/
theorem centralLambertTerm_reciprocalDampedPoint
    (h k n : ℕ) (delta : ℝ) (hh : 0 < h) (hk : 0 < k) :
    (((n + 1).divisors.card : ℕ) : ℂ) *
        Complex.exp
          ((2 * Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) *
            bettinConreyReciprocalDampedPoint h k delta) =
      (((n + 1).divisors.card : ℕ) : ℂ) *
        Complex.exp
          (-(2 * Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) *
            (((k : ℝ) / (h : ℝ) : ℝ) : ℂ)) *
        Complex.exp
          (-bettinConreyReciprocalComplexDamping h k delta *
            ((n + 1 : ℕ) : ℂ)) := by
  have hsplit := two_pi_I_mul_reciprocalDampedPoint
    h k delta hh hk
  have hexponent :
      (2 * Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) *
          bettinConreyReciprocalDampedPoint h k delta =
        (-(2 * Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) *
          (((k : ℝ) / (h : ℝ) : ℝ) : ℂ)) +
          (-bettinConreyReciprocalComplexDamping h k delta *
            ((n + 1 : ℕ) : ℂ)) := by
    linear_combination (((n + 1 : ℕ) : ℂ)) * hsplit
  calc
    (((n + 1).divisors.card : ℕ) : ℂ) *
          Complex.exp
            ((2 * Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) *
              bettinConreyReciprocalDampedPoint h k delta) =
        (((n + 1).divisors.card : ℕ) : ℂ) *
          Complex.exp
            ((-(2 * Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) *
              (((k : ℝ) / (h : ℝ) : ℝ) : ℂ)) +
              (-bettinConreyReciprocalComplexDamping h k delta *
                ((n + 1 : ℕ) : ℂ))) := by rw [hexponent]
    _ = _ := by rw [Complex.exp_add]; ring

/-- Hence the actual second Lambert row is exactly the fixed-phase
complex-damped series, before taking any limit. -/
theorem centralLambertSeries_reciprocalDampedPoint
    (h k : ℕ) (delta : ℝ) (hh : 0 < h) (hk : 0 < k) :
    bettinConreyCentralLambertSeries
        (bettinConreyReciprocalDampedPoint h k delta) =
      bettinConreyReciprocalComplexDampedSeries h k delta := by
  unfold bettinConreyCentralLambertSeries
    bettinConreyReciprocalComplexDampedSeries
  apply tsum_congr
  intro n
  exact centralLambertTerm_reciprocalDampedPoint
    h k n delta hh hk

/-- Exact decomposition of the complete coupled rational period into its
real-damped fixed first twist and its sectorially complex-damped reciprocal
twist. No boundary limit or separate estimate is taken here. -/
theorem rationalDampedPeriod_eq_real_add_reciprocalComplex
    (h k : ℕ) {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hdelta : 0 < delta) :
    bettinConreyRationalDampedPeriod h k delta =
      dampedEstermannLambertSeries h k
          (bettinConreyRationalDamping h k delta) -
        (bettinConreyRationalDampedPoint h k delta)⁻¹ *
          bettinConreyReciprocalComplexDampedSeries h k delta := by
  unfold bettinConreyRationalDampedPeriod
    bettinConreyCentralLambertPeriod centralPeriodOf
  rw [centralLambertSeries_rationalDampedPoint h k hh hk hdelta]
  change dampedEstermannLambertSeries h k
        (bettinConreyRationalDamping h k delta) -
      (bettinConreyRationalDampedPoint h k delta)⁻¹ *
        bettinConreyCentralLambertSeries
          (bettinConreyReciprocalDampedPoint h k delta) = _
  rw [centralLambertSeries_reciprocalDampedPoint h k delta hh hk]

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReciprocalRay
