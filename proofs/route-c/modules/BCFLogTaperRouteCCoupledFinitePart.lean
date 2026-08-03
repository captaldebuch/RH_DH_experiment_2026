import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannSimpleLaurent

/-!
# Route C: isolate the coupled Laurent finite part

The reciprocal contour reduces the rational Abel boundary to a first
real-damped Lambert row coupled to a two-pole residue package.  This module
expands that package, separates the already proved fixed-twist finite part,
and identifies the one remaining Laurent mismatch.

All decompositions are exact.  In particular, no divergent residue is given
an individual boundary value.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCCoupledFinitePart

open Complex Filter Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSimpleLaurent
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelBoundary
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelComplexDamping
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReflectionWeight
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReciprocalRay
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCReciprocalContour

/-- Negating a reduced rational numerator and taking its canonical residue
preserves coprimality with the modulus. -/
theorem bettinConreyNegativeTwist_coprime
    (h k : ℕ) [NeZero h] (hcop : Nat.Coprime k h) :
    Nat.Coprime (bettinConreyNegativeTwist h k) h := by
  rw [← ZMod.isUnit_iff_coprime]
  rw [bettinConreyNegativeTwist_cast]
  exact ((ZMod.isUnit_iff_coprime k h).2 hcop).neg

/-- The reciprocal two-pole package with every dependence on the complex
damping displayed explicitly. -/
theorem bettinConreyReciprocalResiduePackage_eq
    (h k : ℕ) [NeZero h] {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k)
    (hdelta : 0 < delta) :
    let u := bettinConreyReciprocalComplexDamping h k delta
    let a := bettinConreyNegativeTwist h k
    bettinConreyReciprocalResiduePackage h k delta =
      (-u⁻¹ *
          (((Real.eulerMascheroniConstant : ℝ) : ℂ) + Complex.log u)) *
          (h : ℂ)⁻¹ +
        u⁻¹ * estermannSimplePoleCoefficient a h +
        estermannHurwitzContinuation a h 0 := by
  dsimp only
  have huRe : 0 <
      (bettinConreyReciprocalComplexDamping h k delta).re := by
    rw [bettinConreyReciprocalComplexDamping_re]
    exact bettinConreyReciprocalRealDamping_pos h k hh hk hdelta
  have hu : bettinConreyReciprocalComplexDamping h k delta ≠ 0 := by
    intro hzero
    have := congrArg Complex.re hzero
    simp only [Complex.zero_re] at this
    linarith
  unfold bettinConreyReciprocalResiduePackage
  dsimp only
  rw [complexAbelWeightedResidueCoefficient_eq
    (bettinConreyNegativeTwist h k) h
    (bettinConreyNegativeTwist_coprime h k hcop.symm) hu]

/-- The fixed-twist residue attached to the first Lambert row. -/
noncomputable def bettinConreyFirstResiduePackage
    (h k : ℕ) [NeZero k] (delta : ℝ) : ℂ :=
  estermannWeightedResidueCoefficient h k
    (bettinConreyNormalizedAbelReflectionWeight
      (bettinConreyRationalDamping h k delta))

/-- The first Lambert row after its own Laurent residue is subtracted. -/
noncomputable def bettinConreyFirstFixedFinitePart
    (h k : ℕ) [NeZero k] (delta : ℝ) : ℂ :=
  dampedEstermannLambertSeries h k
      (bettinConreyRationalDamping h k delta) -
    bettinConreyFirstResiduePackage h k delta

/-- The residual Laurent coupling between the first row and the reciprocal
two-pole package.  This expression must be kept signed. -/
noncomputable def bettinConreyCoupledLaurentMismatch
    (h k : ℕ) [NeZero h] [NeZero k] (delta : ℝ) : ℂ :=
  bettinConreyFirstResiduePackage h k delta -
    (bettinConreyRationalDampedPoint h k delta)⁻¹ *
      bettinConreyReciprocalResiduePackage h k delta

/-- Exact decomposition of the coupled contour finite part into the already
settled fixed-twist finite part and one Laurent mismatch. -/
theorem coupledContourFinitePart_eq_firstFinitePart_add_laurentMismatch
    (h k : ℕ) [NeZero h] [NeZero k] (delta : ℝ) :
    bettinConreyCoupledContourFinitePart h k delta =
      bettinConreyFirstFixedFinitePart h k delta +
        bettinConreyCoupledLaurentMismatch h k delta := by
  unfold bettinConreyCoupledContourFinitePart
    bettinConreyFirstFixedFinitePart
    bettinConreyCoupledLaurentMismatch
    bettinConreyFirstResiduePackage
  ring

/-- The first Lambert row's complete residue after inserting the classical
simple Laurent coefficient. -/
theorem bettinConreyFirstResiduePackage_eq
    (h k : ℕ) [NeZero k] {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k)
    (hdelta : 0 < delta) :
    let x := bettinConreyRationalDamping h k delta
    bettinConreyFirstResiduePackage h k delta =
      (x : ℂ)⁻¹ *
        (((Real.eulerMascheroniConstant : ℝ) : ℂ) -
          Complex.log (x : ℂ) - 2 * Complex.log (k : ℂ)) *
        (k : ℂ)⁻¹ := by
  dsimp only
  have hx := bettinConreyRationalDamping_pos h k hh hk hdelta
  unfold bettinConreyFirstResiduePackage
  rw [normalizedAbelWeightedResidueCoefficient_eq h k hcop hx,
    estermannSimplePoleCoefficient_eq h k hcop]
  rw [← Complex.ofReal_log hx.le]
  ring

/-- The reciprocal residue package after the same Laurent substitution. -/
theorem bettinConreyReciprocalResiduePackage_laurent_eq
    (h k : ℕ) [NeZero h] {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k)
    (hdelta : 0 < delta) :
    let u := bettinConreyReciprocalComplexDamping h k delta
    let a := bettinConreyNegativeTwist h k
    bettinConreyReciprocalResiduePackage h k delta =
      u⁻¹ *
          (((Real.eulerMascheroniConstant : ℝ) : ℂ) -
            Complex.log u - 2 * Complex.log (h : ℂ)) *
          (h : ℂ)⁻¹ +
        estermannHurwitzContinuation a h 0 := by
  dsimp only
  rw [bettinConreyReciprocalResiduePackage_eq
    h k hh hk hcop hdelta,
    estermannSimplePoleCoefficient_eq
      (bettinConreyNegativeTwist h k) h
      (bettinConreyNegativeTwist_coprime h k hcop.symm)]
  ring

/-- The reciprocal complex damping is a positive real scale times the
inverse of the boundary direction `1+i*delta`. -/
theorem bettinConreyReciprocalComplexDamping_factorization
    (h k : ℕ) {delta : ℝ} (hh : 0 < h) (hk : 0 < k) :
    bettinConreyReciprocalComplexDamping h k delta =
      ((bettinConreyRationalDamping h k delta *
        ((k : ℝ) / (h : ℝ)) ^ 2 : ℝ) : ℂ) *
        (1 + Complex.I * (delta : ℂ))⁻¹ := by
  unfold bettinConreyReciprocalComplexDamping
    bettinConreyReciprocalRealDamping
    bettinConreyReciprocalPhaseDrift
    bettinConreyRationalDamping
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hden : (1 + delta ^ 2 : ℝ) ≠ 0 := by positivity
  have hw : (1 + Complex.I * (delta : ℂ)) ≠ 0 := by
    intro hw
    have := congrArg Complex.re hw
    norm_num at this
  have hwinv :
      (1 + Complex.I * (delta : ℂ))⁻¹ =
        (1 - Complex.I * (delta : ℂ)) / ((1 + delta ^ 2 : ℝ) : ℂ) := by
    rw [Complex.inv_def]
    congr 1
    · apply Complex.ext <;> norm_num
    · norm_num [Complex.normSq_apply]
      ring
  rw [hwinv]
  push_cast
  field_simp [hhR, hkR, hden]

/-- Exact logarithmic cancellation between the two Laurent packages. -/
theorem bettinConreyReciprocal_log_cancellation
    (h k : ℕ) {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hdelta : 0 < delta) :
    let x := bettinConreyRationalDamping h k delta
    let u := bettinConreyReciprocalComplexDamping h k delta
    Complex.log u - Complex.log (x : ℂ) +
        2 * Complex.log (h : ℂ) - 2 * Complex.log (k : ℂ) =
      -Complex.log (1 + Complex.I * (delta : ℂ)) := by
  dsimp only
  have hx := bettinConreyRationalDamping_pos h k hh hk hdelta
  have hr : 0 < (k : ℝ) / (h : ℝ) := div_pos (by exact_mod_cast hk) (by exact_mod_cast hh)
  have hw : (1 + Complex.I * (delta : ℂ)) ≠ 0 := by
    intro hw
    have := congrArg Complex.re hw
    norm_num at this
  have harg : (1 + Complex.I * (delta : ℂ)).arg ≠ Real.pi := by
    apply Complex.slitPlane_arg_ne_pi
    rw [Complex.mem_slitPlane_iff]
    left
    norm_num
  rw [bettinConreyReciprocalComplexDamping_factorization h k hh hk,
    Complex.log_ofReal_mul (mul_pos hx (sq_pos_of_pos hr)) (inv_ne_zero hw),
    Complex.log_inv _ harg, ← Complex.ofReal_log hx.le]
  rw [Real.log_mul hx.ne' (pow_ne_zero 2 hr.ne'), Real.log_pow,
    Real.log_div (by exact_mod_cast hk.ne') (by exact_mod_cast hh.ne')]
  push_cast
  ring

/-- The two reciprocal boundary scales multiply to the universal Abel scale
`2*pi*delta`. -/
theorem bettinConreyDampedPoint_mul_reciprocalDamping
    (h k : ℕ) {delta : ℝ} (hh : 0 < h) (hk : 0 < k) :
    bettinConreyRationalDampedPoint h k delta *
        bettinConreyReciprocalComplexDamping h k delta =
      (2 * Real.pi : ℂ) * (delta : ℂ) := by
  rw [bettinConreyReciprocalComplexDamping_factorization h k hh hk]
  unfold bettinConreyRationalDampedPoint bettinConreyRationalDamping
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hw : (1 + Complex.I * (delta : ℂ)) ≠ 0 := by
    intro hw
    have := congrArg Complex.re hw
    norm_num at this
  push_cast
  field_simp [hhC, hkC, hw]

/-- After the simple Laurent coefficient is evaluated, both divergent rows
have the same scalar.  Their difference is exactly the logarithmic boundary
derivative plus the reciprocal Estermann value at zero. -/
theorem bettinConreyCoupledLaurentMismatch_eq
    (h k : ℕ) [NeZero h] [NeZero k] {delta : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k)
    (hdelta : 0 < delta) :
    bettinConreyCoupledLaurentMismatch h k delta =
      -Complex.log (1 + Complex.I * (delta : ℂ)) *
          ((2 * Real.pi : ℂ) * (h : ℂ) * (delta : ℂ))⁻¹ -
        (bettinConreyRationalDampedPoint h k delta)⁻¹ *
          estermannHurwitzContinuation
            (bettinConreyNegativeTwist h k) h 0 := by
  let x := bettinConreyRationalDamping h k delta
  let u := bettinConreyReciprocalComplexDamping h k delta
  let z := bettinConreyRationalDampedPoint h k delta
  let D := estermannHurwitzContinuation
    (bettinConreyNegativeTwist h k) h 0
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hxprod : (x : ℂ) * (k : ℂ) =
      (2 * Real.pi : ℂ) * (h : ℂ) * (delta : ℂ) := by
    dsimp only [x]
    unfold bettinConreyRationalDamping
    push_cast
    field_simp [hkC]
  have hzprod : z * u * (h : ℂ) =
      (2 * Real.pi : ℂ) * (h : ℂ) * (delta : ℂ) := by
    dsimp only [z, u]
    rw [bettinConreyDampedPoint_mul_reciprocalDamping h k hh hk]
    ring
  have hscalar1 : (x : ℂ)⁻¹ * (k : ℂ)⁻¹ =
      ((2 * Real.pi : ℂ) * (h : ℂ) * (delta : ℂ))⁻¹ := by
    rw [← mul_inv]
    rw [hxprod]
  have hscalar2 : z⁻¹ * u⁻¹ * (h : ℂ)⁻¹ =
      ((2 * Real.pi : ℂ) * (h : ℂ) * (delta : ℂ))⁻¹ := by
    rw [← mul_inv, ← mul_inv]
    rw [hzprod]
  have hlog := bettinConreyReciprocal_log_cancellation
    h k hh hk hdelta
  have hlog' : Complex.log u - Complex.log (x : ℂ) +
      2 * Complex.log (h : ℂ) - 2 * Complex.log (k : ℂ) =
        -Complex.log (1 + Complex.I * (delta : ℂ)) := by
    simpa only [x, u] using hlog
  unfold bettinConreyCoupledLaurentMismatch
  rw [bettinConreyFirstResiduePackage_eq h k hh hk hcop hdelta,
    bettinConreyReciprocalResiduePackage_laurent_eq
      h k hh hk hcop hdelta]
  change
    (x : ℂ)⁻¹ *
          (((Real.eulerMascheroniConstant : ℝ) : ℂ) -
            Complex.log (x : ℂ) - 2 * Complex.log (k : ℂ)) *
          (k : ℂ)⁻¹ -
        z⁻¹ *
          (u⁻¹ *
              (((Real.eulerMascheroniConstant : ℝ) : ℂ) -
                Complex.log u - 2 * Complex.log (h : ℂ)) *
              (h : ℂ)⁻¹ + D) = _
  calc
    _ = ((x : ℂ)⁻¹ * (k : ℂ)⁻¹) *
          (((Real.eulerMascheroniConstant : ℝ) : ℂ) -
            Complex.log (x : ℂ) - 2 * Complex.log (k : ℂ)) -
        (z⁻¹ * u⁻¹ * (h : ℂ)⁻¹) *
          (((Real.eulerMascheroniConstant : ℝ) : ℂ) -
            Complex.log u - 2 * Complex.log (h : ℂ)) - z⁻¹ * D := by
          ring
    _ = ((2 * Real.pi : ℂ) * (h : ℂ) * (delta : ℂ))⁻¹ *
          (((Real.eulerMascheroniConstant : ℝ) : ℂ) -
            Complex.log (x : ℂ) - 2 * Complex.log (k : ℂ)) -
        ((2 * Real.pi : ℂ) * (h : ℂ) * (delta : ℂ))⁻¹ *
          (((Real.eulerMascheroniConstant : ℝ) : ℂ) -
            Complex.log u - 2 * Complex.log (h : ℂ)) - z⁻¹ * D := by
          rw [hscalar1, hscalar2]
    _ = ((2 * Real.pi : ℂ) * (h : ℂ) * (delta : ℂ))⁻¹ *
          (Complex.log u - Complex.log (x : ℂ) +
            2 * Complex.log (h : ℂ) - 2 * Complex.log (k : ℂ)) -
        z⁻¹ * D := by ring
    _ = ((2 * Real.pi : ℂ) * (h : ℂ) * (delta : ℂ))⁻¹ *
          (-Complex.log (1 + Complex.I * (delta : ℂ))) - z⁻¹ * D := by
          rw [hlog']
    _ = _ := by
      dsimp only [z, D]
      ring

/-- The elementary logarithmic quotient on the reciprocal boundary has the
expected derivative `i` at zero. -/
theorem tendsto_log_one_add_I_mul_div_zero_right :
    Tendsto (fun delta : ℝ =>
        Complex.log (1 + Complex.I * (delta : ℂ)) / (delta : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Complex.I) := by
  have hinner : HasDerivAt (fun z : ℂ => 1 + Complex.I * z)
      Complex.I 0 := by
    convert (hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).add
      ((hasDerivAt_id (x := (0 : ℂ))).const_mul Complex.I) using 1
    ring
  have hone : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    norm_num
  have hlog : HasDerivAt
      (fun z : ℂ => Complex.log (1 + Complex.I * z)) Complex.I 0 := by
    have hone' : (fun z : ℂ => 1 + Complex.I * z) 0 ∈
        Complex.slitPlane := by simpa using hone
    have hcomp := HasDerivAt.comp (x := (0 : ℂ))
      (h := fun z : ℂ => 1 + Complex.I * z) (h₂ := Complex.log)
      (Complex.hasDerivAt_log hone') hinner
    simpa [Function.comp_def] using hcomp
  have hofReal : Tendsto (fun delta : ℝ => (delta : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with delta hdelta
      simpa using hdelta.ne'
  have hslope := hlog.tendsto_slope.comp hofReal
  apply hslope.congr'
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  simp only [Function.comp_apply]
  rw [slope_def_field]
  simp

/-- The first-order logarithmic residue has an explicit unconditional
boundary value. -/
theorem tendsto_bettinConreyLogarithmicResidue
    (h : ℕ) (_hh : 0 < h) :
    Tendsto (fun delta : ℝ =>
        -Complex.log (1 + Complex.I * (delta : ℂ)) *
          ((2 * Real.pi : ℂ) * (h : ℂ) * (delta : ℂ))⁻¹)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-Complex.I * ((2 * Real.pi : ℂ) * (h : ℂ))⁻¹)) := by
  have hscaled := tendsto_log_one_add_I_mul_div_zero_right.neg.mul_const
    (((2 * Real.pi : ℂ) * (h : ℂ))⁻¹)
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  have hdeltaC : (delta : ℂ) ≠ 0 := by exact_mod_cast hdelta.ne'
  field_simp [hdeltaC]

/-- The exact boundary of the entire signed Laurent mismatch. -/
theorem tendsto_bettinConreyCoupledLaurentMismatch
    (h k : ℕ) [NeZero h] [NeZero k]
    (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    Tendsto (bettinConreyCoupledLaurentMismatch h k)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (-Complex.I * ((2 * Real.pi : ℂ) * (h : ℂ))⁻¹ -
          ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ))⁻¹ *
            estermannHurwitzContinuation
              (bettinConreyNegativeTwist h k) h 0)) := by
  have hlog := tendsto_bettinConreyLogarithmicResidue h hh
  have hpoint := tendsto_bettinConreyRationalDampedPoint_zero h k
  have hx0 : ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (div_ne_zero (by exact_mod_cast hh.ne') (by exact_mod_cast hk.ne'))
  have hinv : Tendsto
      (fun delta : ℝ => (bettinConreyRationalDampedPoint h k delta)⁻¹)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (((((h : ℝ) / (k : ℝ) : ℝ) : ℂ))⁻¹)) :=
    (continuousAt_inv₀ hx0).tendsto.comp hpoint
  have hsecond := hinv.mul_const
    (estermannHurwitzContinuation (bettinConreyNegativeTwist h k) h 0)
  have hdiff := hlog.sub hsecond
  apply hdiff.congr'
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  exact (bettinConreyCoupledLaurentMismatch_eq
    h k hh hk hcop hdelta).symm

/-- The rational damping map preserves the positive punctured neighborhood
of zero. -/
theorem tendsto_bettinConreyRationalDamping_zero_right
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    Tendsto (bettinConreyRationalDamping h k)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hcont : ContinuousAt (bettinConreyRationalDamping h k) 0 := by
      unfold bettinConreyRationalDamping
      fun_prop
    simpa [bettinConreyRationalDamping] using
      hcont.tendsto.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with delta hdelta
    exact bettinConreyRationalDamping_pos h k hh hk hdelta

/-- The first row's fixed-twist finite part is completely unconditional and
converges to the continued Estermann value at zero. -/
theorem tendsto_bettinConreyFirstFixedFinitePart
    (h k : ℕ) [NeZero k] (hh : 0 < h) (hk : 0 < k) :
    Tendsto (bettinConreyFirstFixedFinitePart h k)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (estermannHurwitzContinuation h k 0)) := by
  simpa [Function.comp_def, bettinConreyFirstFixedFinitePart,
    bettinConreyFirstResiduePackage] using
      (tendsto_dampedEstermann_sub_residue_zero h k).comp
        (tendsto_bettinConreyRationalDamping_zero_right h k hh hk)

/-- The rational Abel boundary is now equivalent to a limit of the single
Laurent mismatch.  This theorem is the quantitative stop test after all
contour and fixed-twist analysis has been removed. -/
theorem tendsto_coupledContourFinitePart_iff_laurentMismatch
    (h k : ℕ) [NeZero h] [NeZero k] (hh : 0 < h) (hk : 0 < k) :
    Tendsto (bettinConreyCoupledContourFinitePart h k)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (bettinConreyCentralAbelBoundaryValue h k)) ↔
      Tendsto (bettinConreyCoupledLaurentMismatch h k)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (bettinConreyCentralAbelBoundaryValue h k -
          estermannHurwitzContinuation h k 0)) := by
  have hfirst := tendsto_bettinConreyFirstFixedFinitePart h k hh hk
  constructor
  · intro hcoupled
    have hsub := hcoupled.sub hfirst
    apply hsub.congr'
    exact Eventually.of_forall fun delta => by
      change bettinConreyCoupledContourFinitePart h k delta -
        bettinConreyFirstFixedFinitePart h k delta =
          bettinConreyCoupledLaurentMismatch h k delta
      rw [coupledContourFinitePart_eq_firstFinitePart_add_laurentMismatch]
      ring
  · intro hmismatch
    have hadd := hfirst.add hmismatch
    have hadd' : Tendsto (fun delta : ℝ =>
        bettinConreyFirstFixedFinitePart h k delta +
          bettinConreyCoupledLaurentMismatch h k delta)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (bettinConreyCentralAbelBoundaryValue h k)) := by
      convert hadd using 1
      ring
    apply hadd'.congr'
    exact Eventually.of_forall fun delta =>
      (coupledContourFinitePart_eq_firstFinitePart_add_laurentMismatch
        h k delta).symm

/-- The complete coupled contour finite part has an explicit unconditional
boundary in terms of two genuine Estermann values at zero. -/
theorem tendsto_bettinConreyCoupledContourFinitePart_explicit
    (h k : ℕ) [NeZero h] [NeZero k]
    (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    Tendsto (bettinConreyCoupledContourFinitePart h k)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (estermannHurwitzContinuation h k 0 -
          Complex.I * ((2 * Real.pi : ℂ) * (h : ℂ))⁻¹ -
          ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ))⁻¹ *
            estermannHurwitzContinuation
              (bettinConreyNegativeTwist h k) h 0)) := by
  have hfirst := tendsto_bettinConreyFirstFixedFinitePart h k hh hk
  have hmismatch := tendsto_bettinConreyCoupledLaurentMismatch
    h k hh hk hcop
  have hadd := hfirst.add hmismatch
  have hadd' : Tendsto (fun delta : ℝ =>
      bettinConreyFirstFixedFinitePart h k delta +
        bettinConreyCoupledLaurentMismatch h k delta)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (estermannHurwitzContinuation h k 0 -
          Complex.I * ((2 * Real.pi : ℂ) * (h : ℂ))⁻¹ -
          ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ))⁻¹ *
            estermannHurwitzContinuation
              (bettinConreyNegativeTwist h k) h 0)) := by
    convert hadd using 1
    ring
  apply hadd'.congr'
  exact Eventually.of_forall fun delta =>
    (coupledContourFinitePart_eq_firstFinitePart_add_laurentMismatch
      h k delta).symm

/-- Reattaching the vanishing reciprocal vertical line gives the same
explicit boundary for the original coupled Lambert period. -/
theorem tendsto_bettinConreyRationalDampedPeriod_explicit
    (h k : ℕ) [NeZero h] [NeZero k]
    (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    Tendsto (bettinConreyRationalDampedPeriod h k)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (estermannHurwitzContinuation h k 0 -
          Complex.I * ((2 * Real.pi : ℂ) * (h : ℂ))⁻¹ -
          ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ))⁻¹ *
            estermannHurwitzContinuation
              (bettinConreyNegativeTwist h k) h 0)) := by
  have hfinite := tendsto_bettinConreyCoupledContourFinitePart_explicit
    h k hh hk hcop
  have hvertical :=
    tendsto_bettinConreyReciprocalVerticalContribution_zero h k hh hk
  have hadd := hfinite.add hvertical
  have hadd' : Tendsto (fun delta : ℝ =>
      bettinConreyCoupledContourFinitePart h k delta +
        bettinConreyReciprocalVerticalContribution h k delta)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (estermannHurwitzContinuation h k 0 -
          Complex.I * ((2 * Real.pi : ℂ) * (h : ℂ))⁻¹ -
          ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ))⁻¹ *
            estermannHurwitzContinuation
              (bettinConreyNegativeTwist h k) h 0)) := by
    simpa using hadd
  apply hadd'.congr'
  filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds] with delta hdelta hdeltaOne
  exact (rationalDampedPeriod_eq_coupledFinitePart_add_vertical
    h k hh hk hdelta hdeltaOne.le).symm

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCCoupledFinitePart
