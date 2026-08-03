import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmSeriesValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Finite integral assembly for Ehm's `R₁` series

This module formalizes the finite, unconditional part of Ehm (2024),
Proposition 5.1.  The paper first represents `R₁(x)` as a tail integral of
the centered fractional part and then rescales and sums those tails.  The
infinite sum/integral exchange is deliberately left separate.

The exact finite identity proved here identifies the normalization and the
`1/k` weight before any limiting argument.  It therefore rules out a hidden
factor in the remaining all-real series-value bridge.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmIntegralSeriesAssembly

open Filter MeasureTheory Set
open scoped BigOperators Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmR1Decay
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesValue

/-- The centered periodic function in Ehm's Proposition 5.1. -/
noncomputable def ehmCenteredFractionalPart (x : ℝ) : ℝ :=
  Int.fract x - 1 / 2

/-- The tail-integral model for `R₁`; Ehm's equation (32) asserts that this
equals the elementary function `ehmR1` on the positive half-line. -/
noncomputable def ehmR1TailIntegral (x : ℝ) : ℝ :=
  -(∫ t in Ioi x, ehmCenteredFractionalPart t / t ^ 2)

/-- Finite truncation of Ehm's periodic `φ₁`. -/
noncomputable def ehmPhi1Partial (K : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K,
    ehmCenteredFractionalPart ((k : ℝ) * x) / (k : ℝ)

/-- Reciprocal-square decay is integrable on every tail bounded away from
zero. -/
theorem integrableOn_inv_sq_Ioi {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Ioi r) := by
  have hpow := integrableOn_Ioi_rpow_of_lt
    (a := (-2 : ℝ)) (by norm_num) hr
  apply hpow.congr_fun _ measurableSet_Ioi
  intro x hx
  have hxpos : 0 < x := hr.trans hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  change x ^ (-2 : ℝ) = 1 / x ^ 2
  norm_num [Real.rpow_neg_natCast, zpow_neg, hx0]
  rfl

/-- Every dilated centered fractional-part row is integrable against the
reciprocal-square tail weight. -/
theorem integrableOn_ehmCenteredFractionalPart_mul_div_sq
    {r c : ℝ} (hr : 0 < r) :
    IntegrableOn
      (fun x : ℝ => ehmCenteredFractionalPart (c * x) / x ^ 2)
      (Ioi r) := by
  have hmaj := integrableOn_inv_sq_Ioi hr
  have hmeas : Measurable (fun x : ℝ =>
      ehmCenteredFractionalPart (c * x) / x ^ 2) := by
    unfold ehmCenteredFractionalPart
    fun_prop
  apply Integrable.mono' hmaj hmeas.aestronglyMeasurable.restrict
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  have hxpos : 0 < x := hr.trans hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hcentered : |ehmCenteredFractionalPart (c * x)| ≤ 1 := by
    rw [abs_le]
    unfold ehmCenteredFractionalPart
    constructor <;>
      linarith [Int.fract_nonneg (c * x), (Int.fract_lt_one (c * x)).le]
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hxpos]
  exact div_le_div_of_nonneg_right hcentered (sq_nonneg x)

/-- A positive dilation of the centered fractional-part tail produces
exactly the harmonic `1/k` coefficient used in `φ₁`. -/
theorem ehmR1TailIntegral_nat_mul
    (r : ℝ) (k : ℕ) (hk : 0 < k) :
    ehmR1TailIntegral ((k : ℝ) * r) =
      -(∫ x in Ioi r,
        (ehmCenteredFractionalPart ((k : ℝ) * x) / (k : ℝ)) / x ^ 2) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkR
  let g : ℝ → ℝ := fun t => ehmCenteredFractionalPart t / t ^ 2
  have hcomp := integral_comp_mul_right_Ioi g r hkR
  simp only [smul_eq_mul] at hcomp
  unfold ehmR1TailIntegral
  rw [show (k : ℝ) * r = r * (k : ℝ) by ring]
  have htail :
      (∫ t in Ioi (r * (k : ℝ)), g t) =
        (k : ℝ) * ∫ x in Ioi r, g (x * (k : ℝ)) := by
    calc
      (∫ t in Ioi (r * (k : ℝ)), g t) =
          (k : ℝ) * ((k : ℝ)⁻¹ *
            ∫ t in Ioi (r * (k : ℝ)), g t) := by
              field_simp [hk0]
      _ = (k : ℝ) * ∫ x in Ioi r, g (x * (k : ℝ)) := by rw [hcomp]
  rw [htail, ← integral_const_mul]
  congr 2
  funext x
  dsimp [g]
  field_simp [hk0]

/-- Finite version of Ehm's equation (33).  The rescaled `R₁` tails assemble
exactly into the finite periodic sum `φ₁,K`, with no limiting or Fubini
hypothesis. -/
theorem sum_ehmR1TailIntegral_eq_integral_ehmPhi1Partial
    (K : ℕ) {r : ℝ} (hr : 0 < r) :
    (∑ k ∈ Finset.Icc 1 K,
      ehmR1TailIntegral ((k : ℝ) * r)) =
      -(∫ x in Ioi r, ehmPhi1Partial K x / x ^ 2) := by
  classical
  calc
    (∑ k ∈ Finset.Icc 1 K,
        ehmR1TailIntegral ((k : ℝ) * r)) =
      ∑ k ∈ Finset.Icc 1 K,
        -(∫ x in Ioi r,
          (ehmCenteredFractionalPart ((k : ℝ) * x) / (k : ℝ)) /
            x ^ 2) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact ehmR1TailIntegral_nat_mul r k
                (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1)
    _ = -(∑ k ∈ Finset.Icc 1 K,
        ∫ x in Ioi r,
          (ehmCenteredFractionalPart ((k : ℝ) * x) / (k : ℝ)) /
            x ^ 2) := by rw [Finset.sum_neg_distrib]
    _ = -(∫ x in Ioi r,
        ∑ k ∈ Finset.Icc 1 K,
          (ehmCenteredFractionalPart ((k : ℝ) * x) / (k : ℝ)) /
            x ^ 2) := by
              congr 1
              rw [integral_finsetSum]
              intro k hk
              have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one
                (Finset.mem_Icc.mp hk).1
              have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
              have hbase :=
                integrableOn_ehmCenteredFractionalPart_mul_div_sq
                  (c := (k : ℝ)) hr
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                hbase.const_mul (k : ℝ)⁻¹
    _ = -(∫ x in Ioi r, ehmPhi1Partial K x / x ^ 2) := by
      congr 2
      funext x
      unfold ehmPhi1Partial
      rw [Finset.sum_div]

/-! ## The two remaining clauses of Ehm Proposition 5.1 -/

/-- The usual `range K` partial sum agrees with the positive-index partial
series used throughout the Ehm modules. -/
theorem sum_range_shift_ehmR1_eq_partialSeries (K : ℕ) (r : ℝ) :
    (∑ q ∈ Finset.range K,
      ehmR1 (((q + 1 : ℕ) : ℝ) * r)) =
      ehmR1PartialSeries ehmR1 K r := by
  induction K with
  | zero => simp [ehmR1PartialSeries]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      unfold ehmR1PartialSeries
      rw [Finset.sum_Icc_succ_top (by omega)]

/-- Ehm's equation (32), isolated from the subsequent global
sum/integral exchange.  This is a local piecewise-calculus theorem about the
explicit elementary function `ehmR1`. -/
structure EhmR1TailIntegralIdentity where
  value : ∀ x : ℝ, 0 < x → ehmR1 x = ehmR1TailIntegral x

/-! ## Ehm's equation (32) by cell calculus -/

/-- On the cell `[n,n+1]`, this smooth function is the continuous primitive
whose derivative is the centered fractional-part density.  Its endpoint
values agree with the two adjacent floor branches of `ehmR1`. -/
noncomputable def ehmR1CellPrimitive (n : ℕ) (x : ℝ) : ℝ :=
  Real.log x + Real.eulerMascheroniConstant - ehmHarmonic n - 1 +
    ((n : ℝ) + 1 / 2) / x

/-- The finite harmonic term gains exactly one reciprocal at an integer
successor. -/
theorem ehmHarmonic_nat_succ (n : ℕ) :
    ehmHarmonic ((n + 1 : ℕ) : ℝ) =
      ehmHarmonic (n : ℝ) + 1 / ((n : ℝ) + 1) := by
  unfold ehmHarmonic
  rw [Nat.floor_natCast, Nat.floor_natCast]
  rw [Finset.sum_Icc_succ_top (by omega)]
  push_cast
  rfl

/-- Inside the half-open cell `[n,n+1)`, the elementary floor formula for
`ehmR1` is the smooth cell primitive. -/
theorem ehmR1_eq_cellPrimitive_of_mem_Ico (n : ℕ) {x : ℝ}
    (hxpos : 0 < x) (hx : x ∈ Ico (n : ℝ) ((n : ℝ) + 1)) :
    ehmR1 x = ehmR1CellPrimitive n x := by
  have hfloorN : ⌊x⌋₊ = n := Nat.floor_eq_on_Ico n x hx
  have hxZ : x ∈ Ico ((n : ℤ) : ℝ) (((n : ℤ) : ℝ) + 1) := by
    simpa using hx
  have hfloorZ : ⌊x⌋ = (n : ℤ) := Int.floor_eq_on_Ico (n : ℤ) x hxZ
  have hharmonic : ehmHarmonic x = ehmHarmonic (n : ℝ) := by
    unfold ehmHarmonic
    rw [hfloorN, Nat.floor_natCast]
  unfold ehmR1 ehmR1CellPrimitive
  rw [hharmonic]
  unfold Int.fract
  rw [hfloorZ]
  push_cast
  field_simp [ne_of_gt hxpos]
  ring

/-- The cell primitive has the correct value at the right integer endpoint;
the harmonic jump cancels the fractional-part jump exactly. -/
theorem ehmR1CellPrimitive_succ (n : ℕ) :
    ehmR1CellPrimitive n ((n : ℝ) + 1) = ehmR1 ((n + 1 : ℕ) : ℝ) := by
  rw [ehmR1_nat_formula (n + 1) (by omega), ehmHarmonic_nat_succ]
  unfold ehmR1CellPrimitive
  push_cast
  have hne : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hne]
  ring

/-- Derivative of the smooth primitive on the positive half-line. -/
theorem hasDerivAt_ehmR1CellPrimitive (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (ehmR1CellPrimitive n)
      (1 / x - ((n : ℝ) + 1 / 2) / x ^ 2) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlog := Real.hasDerivAt_log hx0
  have hc : HasDerivAt (fun _ : ℝ =>
      Real.eulerMascheroniConstant - ehmHarmonic n - 1) 0 x :=
    hasDerivAt_const x _
  have hquot : HasDerivAt (fun y : ℝ => ((n : ℝ) + 1 / 2) / y)
      (-((n : ℝ) + 1 / 2) / x ^ 2) x := by
    convert (hasDerivAt_const x ((n : ℝ) + 1 / 2)).div
      (hasDerivAt_id x) hx0 using 1
    simp only [id_eq]
    ring
  convert hlog.add (hc.add hquot) using 1
  · funext y
    simp only [ehmR1CellPrimitive, Pi.add_apply]
    ring
  · simp only [one_div]
    ring

/-- On an open integer cell, the centered fractional-part density is the
derivative displayed by the cell primitive. -/
theorem ehmCenteredFractionalPart_div_sq_eq_cellDerivative
    (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (n : ℝ) ((n : ℝ) + 1)) :
    ehmCenteredFractionalPart x / x ^ 2 =
      1 / x - ((n : ℝ) + 1 / 2) / x ^ 2 := by
  have hxZ : x ∈ Ico ((n : ℤ) : ℝ) (((n : ℤ) : ℝ) + 1) := by
    exact ⟨hx.1.le, hx.2⟩
  have hfloorZ : ⌊x⌋ = (n : ℤ) := Int.floor_eq_on_Ico (n : ℤ) x hxZ
  unfold ehmCenteredFractionalPart Int.fract
  rw [hfloorZ]
  push_cast
  have hxpos : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg n) hx.1
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  field_simp [hx0]
  ring

/-- The centered density is interval-integrable between any two positive
ordered endpoints. -/
theorem intervalIntegrable_ehmCenteredFractionalPart_div_sq
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => ehmCenteredFractionalPart t / t ^ 2)
      volume a b := by
  have htail := integrableOn_ehmCenteredFractionalPart_mul_div_sq
    (r := a / 2) (c := 1) (by positivity)
  have htail' : IntegrableOn
      (fun t : ℝ => ehmCenteredFractionalPart t / t ^ 2)
      (Ioi (a / 2)) := by simpa using htail
  apply (htail'.mono_set ?_).intervalIntegrable
  intro y hy
  rw [uIcc_of_le hab] at hy
  have hay : a / 2 < y := (by linarith : a / 2 < a).trans_le hy.1
  simpa using hay

/-- Fundamental-theorem-of-calculus evaluation from an arbitrary positive
point to the right endpoint of its integer cell. -/
theorem integral_ehmCenteredFractionalPart_div_sq_to_cellEnd
    (n : ℕ) {x : ℝ} (hxpos : 0 < x)
    (hxcell : x ∈ Ico (n : ℝ) ((n : ℝ) + 1)) :
    (∫ t in x..((n : ℝ) + 1),
      ehmCenteredFractionalPart t / t ^ 2) =
      ehmR1 ((n + 1 : ℕ) : ℝ) - ehmR1 x := by
  have hxe : x ≤ (n : ℝ) + 1 := hxcell.2.le
  have hcont : ContinuousOn (ehmR1CellPrimitive n)
      (Icc x ((n : ℝ) + 1)) := by
    intro y hy
    exact (hasDerivAt_ehmR1CellPrimitive n
      (hxpos.trans_le hy.1)).continuousAt.continuousWithinAt
  have hderiv : ∀ y ∈ Ioo x ((n : ℝ) + 1),
      HasDerivAt (ehmR1CellPrimitive n)
        (ehmCenteredFractionalPart y / y ^ 2) y := by
    intro y hy
    have hycell : y ∈ Ioo (n : ℝ) ((n : ℝ) + 1) :=
      ⟨hxcell.1.trans_lt hy.1, hy.2⟩
    rw [ehmCenteredFractionalPart_div_sq_eq_cellDerivative n hycell]
    exact hasDerivAt_ehmR1CellPrimitive n (hxpos.trans hy.1)
  calc
    (∫ t in x..((n : ℝ) + 1),
        ehmCenteredFractionalPart t / t ^ 2) =
        ehmR1CellPrimitive n ((n : ℝ) + 1) -
          ehmR1CellPrimitive n x := by
            exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxe
              hcont hderiv
              (intervalIntegrable_ehmCenteredFractionalPart_div_sq hxpos hxe)
    _ = ehmR1 ((n + 1 : ℕ) : ℝ) - ehmR1 x := by
      rw [ehmR1CellPrimitive_succ,
        ← ehmR1_eq_cellPrimitive_of_mem_Ico n hxpos hxcell]

/-- Successive cell evaluations telescope exactly to every later natural
endpoint. -/
theorem integral_ehmCenteredFractionalPart_div_sq_to_natOffset
    (n q : ℕ) {x : ℝ} (hxpos : 0 < x)
    (hxcell : x ∈ Ico (n : ℝ) ((n : ℝ) + 1)) :
    (∫ t in x..((n + q + 1 : ℕ) : ℝ),
      ehmCenteredFractionalPart t / t ^ 2) =
      ehmR1 ((n + q + 1 : ℕ) : ℝ) - ehmR1 x := by
  induction q with
  | zero =>
      simpa using
        integral_ehmCenteredFractionalPart_div_sq_to_cellEnd n hxpos hxcell
  | succ q ih =>
      let M : ℕ := n + q + 1
      have hMpos : 0 < M := by omega
      have hMx : x ≤ (M : ℝ) := by
        have : (n : ℝ) + 1 ≤ (M : ℝ) := by
          exact_mod_cast (show n + 1 ≤ M by dsimp [M]; omega)
        exact hxcell.2.le.trans this
      have hMcell : (M : ℝ) ∈ Ico (M : ℝ) ((M : ℝ) + 1) := by
        constructor <;> simp
      have hcell := integral_ehmCenteredFractionalPart_div_sq_to_cellEnd
        M (by exact_mod_cast hMpos) hMcell
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_ehmCenteredFractionalPart_div_sq hxpos hMx)
        (intervalIntegrable_ehmCenteredFractionalPart_div_sq
          (by exact_mod_cast hMpos) (by linarith : (M : ℝ) ≤ (M : ℝ) + 1))
      change (∫ t in x..((M + 1 : ℕ) : ℝ),
        ehmCenteredFractionalPart t / t ^ 2) =
        ehmR1 ((M + 1 : ℕ) : ℝ) - ehmR1 x
      change (∫ t in x..(M : ℝ),
        ehmCenteredFractionalPart t / t ^ 2) =
        ehmR1 (M : ℝ) - ehmR1 x at ih
      rw [show ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 by push_cast; ring]
      norm_num [Nat.cast_add, Nat.cast_one] at hcell
      rw [← hadd, ih, hcell]
      ring

/-- The boundary values at the natural endpoints used in the telescope tend
to zero by the already proved quadratic decay of `ehmR1`. -/
theorem tendsto_ehmR1_natOffset_zero (n : ℕ) :
    Tendsto (fun q : ℕ => ehmR1 ((n + q + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
  have hcast : Tendsto (fun q : ℕ => ((n + q + 1 : ℕ) : ℝ))
      atTop atTop := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (tendsto_atTop_add_const_right atTop ((n : ℝ) + 1)
        tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun q : ℕ =>
      (((n + q + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hmajor : Tendsto (fun q : ℕ =>
      8 / (((n + q + 1 : ℕ) : ℝ)) ^ 2) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, inv_pow] using
      (tendsto_const_nhds.mul (hinv.pow 2) :
        Tendsto (fun q : ℕ =>
          (8 : ℝ) * ((((n + q + 1 : ℕ) : ℝ))⁻¹) ^ 2)
          atTop (nhds (8 * 0 ^ 2)))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero'
    (g := fun q : ℕ => 8 / (((n + q + 1 : ℕ) : ℝ)) ^ 2)
    (Eventually.of_forall fun q => abs_nonneg _) ?_ hmajor
  exact Eventually.of_forall fun q =>
    ehmConcreteR1QuadraticDecay.bound _ (by positivity)

/-- Ehm (2024), equation (32): the explicit elementary remainder is exactly
the tail integral of the centered fractional part. -/
theorem ehmEquation32 (x : ℝ) (hx : 0 < x) :
    ehmR1 x = ehmR1TailIntegral x := by
  let n : ℕ := ⌊x⌋₊
  have hxcell : x ∈ Ico (n : ℝ) ((n : ℝ) + 1) := by
    constructor
    · exact Nat.floor_le hx.le
    · simpa [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
  let endpoint : ℕ → ℝ := fun q => ((n + q + 1 : ℕ) : ℝ)
  have hendpoint : Tendsto endpoint atTop atTop := by
    dsimp [endpoint]
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (tendsto_atTop_add_const_right atTop ((n : ℝ) + 1)
        tendsto_natCast_atTop_atTop)
  have htailIntegrable : IntegrableOn
      (fun t : ℝ => ehmCenteredFractionalPart t / t ^ 2) (Ioi x) := by
    simpa using
      (integrableOn_ehmCenteredFractionalPart_mul_div_sq
        (r := x) (c := 1) hx)
  have himproper := MeasureTheory.intervalIntegral_tendsto_integral_Ioi x
    htailIntegrable hendpoint
  have hfinite : ∀ q : ℕ,
      (∫ t in x..endpoint q, ehmCenteredFractionalPart t / t ^ 2) =
        ehmR1 (endpoint q) - ehmR1 x := by
    intro q
    simpa [endpoint] using
      integral_ehmCenteredFractionalPart_div_sq_to_natOffset n q hx hxcell
  have himproper' : Tendsto
      (fun q : ℕ => ehmR1 (endpoint q) - ehmR1 x) atTop
      (nhds (∫ t in Ioi x, ehmCenteredFractionalPart t / t ^ 2)) :=
    himproper.congr' (Eventually.of_forall fun q => hfinite q)
  have hboundary : Tendsto
      (fun q : ℕ => ehmR1 (endpoint q) - ehmR1 x) atTop
      (nhds (-ehmR1 x)) := by
    simpa [endpoint] using (tendsto_ehmR1_natOffset_zero n).sub_const (ehmR1 x)
  have htail : (∫ t in Ioi x, ehmCenteredFractionalPart t / t ^ 2) =
      -ehmR1 x := tendsto_nhds_unique himproper' hboundary
  unfold ehmR1TailIntegral
  linarith

/-- The proved inhabitant of the local tail-integral clause in Ehm's
Proposition 5.1. -/
noncomputable def ehmR1TailIntegralIdentityProved :
    EhmR1TailIntegralIdentity where
  value := ehmEquation32

/-- The global clause of Proposition 5.1 after the finite assembly theorem:
the finite `φ₁` tail integrals converge to the concrete autocorrelation
kernel.  This field contains both the justified limit exchange and the
identification with Ehm's integral representation (31). -/
structure EhmPhi1IntegralLimitIdentity where
  tendsto_value : ∀ r : ℝ, 0 < r →
    Tendsto (fun K : ℕ =>
      -(∫ x in Ioi r, ehmPhi1Partial K x / x ^ 2))
      atTop (nhds (ehmS1Autocorrelation r))

/-- With equation (32) proved, the exact finite weighted integrals converge
unconditionally to the absolutely convergent `R₁` series.  No infinite
sum/integral interchange is used in this statement. -/
theorem integral_ehmPhi1Partial_tendsto_tsum
    (r : ℝ) (hr : 0 < r) :
    Tendsto (fun K : ℕ =>
      -(∫ x in Ioi r, ehmPhi1Partial K x / x ^ 2))
      atTop
      (nhds (∑' q : ℕ,
        ehmR1 (((q + 1 : ℕ) : ℝ) * r))) := by
  have hsummable := ehmConcreteR1QuadraticDecay.summable_series r hr
  have hseries := hsummable.hasSum.tendsto_sum_nat
  apply hseries.congr'
  filter_upwards with K
  calc
    (∑ q ∈ Finset.range K,
        ehmR1 (((q + 1 : ℕ) : ℝ) * r)) =
        ehmR1PartialSeries ehmR1 K r :=
      sum_range_shift_ehmR1_eq_partialSeries K r
    _ = -(∫ x in Ioi r, ehmPhi1Partial K x / x ^ 2) := by
      unfold ehmR1PartialSeries
      rw [← sum_ehmR1TailIntegral_eq_integral_ehmPhi1Partial K hr]
      apply Finset.sum_congr rfl
      intro k hk
      rw [ehmEquation32]
      exact mul_pos (by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp hk).1)) hr

/-- The all-real autocorrelation--series value theorem supplies exactly the
remaining target of the finite-integral limit. -/
noncomputable def ehmPhi1IntegralLimitIdentity_of_seriesValue
    (HV : EhmAutocorrelationR1SeriesValueIdentity) :
    EhmPhi1IntegralLimitIdentity where
  tendsto_value r hr := by
    rw [HV.value r hr]
    exact integral_ehmPhi1Partial_tendsto_tsum r hr

/-- Conversely, the weighted `φ₁` limit contains no more and no less value
information than the autocorrelation--`R₁` series identity. -/
noncomputable def ehmAutocorrelationR1SeriesValueIdentity_of_phi1Limit
    (HL : EhmPhi1IntegralLimitIdentity) :
    EhmAutocorrelationR1SeriesValueIdentity where
  value r hr := by
    exact tendsto_nhds_unique (HL.tendsto_value r hr)
      (integral_ehmPhi1Partial_tendsto_tsum r hr)

/-- The remaining global clause of Ehm Proposition 5.1 is equivalent to the
concrete all-real autocorrelation--series value identity. -/
theorem exists_ehmPhi1IntegralLimitIdentity_iff_exists_seriesValue :
    Nonempty EhmPhi1IntegralLimitIdentity ↔
      Nonempty EhmAutocorrelationR1SeriesValueIdentity := by
  constructor
  · rintro ⟨HL⟩
    exact ⟨ehmAutocorrelationR1SeriesValueIdentity_of_phi1Limit HL⟩
  · rintro ⟨HV⟩
    exact ⟨ehmPhi1IntegralLimitIdentity_of_seriesValue HV⟩

/-- Equation (32) transfers the exact finite tail assembly to the concrete
partial `R₁` series. -/
theorem ehmR1PartialSeries_eq_integral_ehmPhi1Partial
    (HT : EhmR1TailIntegralIdentity) (K : ℕ) {r : ℝ} (hr : 0 < r) :
    ehmR1PartialSeries ehmR1 K r =
      -(∫ x in Ioi r, ehmPhi1Partial K x / x ^ 2) := by
  unfold ehmR1PartialSeries
  rw [← sum_ehmR1TailIntegral_eq_integral_ehmPhi1Partial K hr]
  apply Finset.sum_congr rfl
  intro k hk
  rw [HT.value]
  exact mul_pos (by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp hk).1)) hr

/-- The two clauses of Proposition 5.1 instantiate the all-positive-real
series bridge used by the regularized Fourier theory.  No H15 cancellation
estimate enters this construction. -/
noncomputable def ehmAutocorrelationR1SeriesBridge_of_integralIdentities
    (HT : EhmR1TailIntegralIdentity)
    (HL : EhmPhi1IntegralLimitIdentity) :
    EhmAutocorrelationR1SeriesBridge where
  hasSum_series r hr := by
    have hsummable := ehmConcreteR1QuadraticDecay.summable_series r hr
    apply (hsummable.hasSum_iff_tendsto_nat).mpr
    have hlimit := HL.tendsto_value r hr
    apply hlimit.congr'
    filter_upwards with K
    rw [← ehmR1PartialSeries_eq_integral_ehmPhi1Partial HT K hr]
    exact (sum_range_shift_ehmR1_eq_partialSeries K r).symm

end RH.Criteria.NymanBeurling.BCFLogTaperEhmIntegralSeriesAssembly
