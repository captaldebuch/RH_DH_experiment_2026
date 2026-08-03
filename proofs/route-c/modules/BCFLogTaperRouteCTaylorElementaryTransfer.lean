import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCoefficientCollection

/-!
# Route C: elementary logarithmic Taylor transfer

The three-term relation leaves an elementary expression containing source
logarithms at `z` and `z/(1+z)`.  On the positive real axis those logarithms
combine exactly into

`-((1+z)/z) * log(1+z) + 1 + z/2`.

This module proves that identity without hiding a branch choice and gives
the removable-at-zero function its complete Taylor series on the unit disc.
The first two coefficients cancel and every coefficient in degree `m >= 2`
is `(-1)^m/(m*(m+1))`, precisely the elementary row used in the general
coefficient calculation.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorElementaryTransfer

open Complex
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorGeneralCoefficient
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorThreeTermTransfer

/-- The elementary transfer with its removable value at the origin filled
in explicitly. -/
noncomputable def routeCTaylorElementaryModel (z : ℂ) : ℂ :=
  if z = 0 then 0
  else -((1 + z) / z) * Complex.log (1 + z) + 1 + z / 2

/-- The complete elementary coefficient sequence, including its two zero
initial coefficients. -/
noncomputable def routeCTaylorElementarySeriesCoefficient (m : ℕ) : ℂ :=
  if 2 ≤ m then routeCTaylorElementaryScalarCoefficient m else 0

@[simp] theorem routeCTaylorElementarySeriesCoefficient_zero :
    routeCTaylorElementarySeriesCoefficient 0 = 0 := by
  simp [routeCTaylorElementarySeriesCoefficient]

@[simp] theorem routeCTaylorElementarySeriesCoefficient_one :
    routeCTaylorElementarySeriesCoefficient 1 = 0 := by
  simp [routeCTaylorElementarySeriesCoefficient]

theorem routeCTaylorElementarySeriesCoefficient_of_two_le
    (m : ℕ) (hm : 2 ≤ m) :
    routeCTaylorElementarySeriesCoefficient m =
      routeCTaylorElementaryScalarCoefficient m := by
  simp [routeCTaylorElementarySeriesCoefficient, hm]

/-- Before invoking positivity, the source expression is already an exact
difference of two complex logarithms. -/
theorem routeCTaylorRawElementaryTransfer_eq_log_difference
    (z : ℂ) (hz : z ≠ 0) (hz1 : 1 + z ≠ 0) :
    routeCTaylorRawElementaryTransfer z =
      (1 + z) / z *
        (Complex.log
            ((2 * Real.pi : ℂ) * routeCTaylorMobiusArgument z) -
          Complex.log ((2 * Real.pi : ℂ) * z)) +
        1 + z / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hmob : routeCTaylorMobiusArgument z ≠ 0 := by
    unfold routeCTaylorMobiusArgument
    exact div_ne_zero hz hz1
  unfold routeCTaylorRawElementaryTransfer
    bettinConreyPsiZeroElementaryPart routeCTaylorMobiusArgument
  field_simp [hz, hz1, hmob, hpi, Complex.I_ne_zero]
  ring

/-- On the positive ray, the principal logarithms obey the ordinary real
logarithm law, so the raw source transfer is the removable elementary model.
-/
theorem routeCTaylorRawElementaryTransfer_ofReal_eq_model
    (x : ℝ) (hx : 0 < x) :
    routeCTaylorRawElementaryTransfer (x : ℂ) =
      routeCTaylorElementaryModel (x : ℂ) := by
  have hz : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hx1 : 0 < 1 + x := by linarith
  have hz1 : 1 + (x : ℂ) ≠ 0 := by
    simpa using Complex.ofReal_ne_zero.mpr hx1.ne'
  rw [routeCTaylorRawElementaryTransfer_eq_log_difference
    (x : ℂ) hz hz1]
  let y : ℝ := x / (1 + x)
  have hy : 0 < y := div_pos hx hx1
  have hmob : routeCTaylorMobiusArgument (x : ℂ) = (y : ℂ) := by
    unfold routeCTaylorMobiusArgument
    dsimp [y]
    push_cast
    ring
  rw [hmob]
  have htwopi : 0 < 2 * Real.pi :=
    mul_pos (by norm_num) Real.pi_pos
  have hxy : 0 < 2 * Real.pi * x := mul_pos htwopi hx
  have hyy : 0 < 2 * Real.pi * y := mul_pos htwopi hy
  have hlogx :
      Complex.log ((2 * Real.pi : ℂ) * (x : ℂ)) =
        (Real.log (2 * Real.pi * x) : ℂ) := by
    rw [show (2 * Real.pi : ℂ) * (x : ℂ) =
      ((2 * Real.pi * x : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log hxy.le).symm
  have hlogy :
      Complex.log ((2 * Real.pi : ℂ) * (y : ℂ)) =
        (Real.log (2 * Real.pi * y) : ℂ) := by
    rw [show (2 * Real.pi : ℂ) * (y : ℂ) =
      ((2 * Real.pi * y : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log hyy.le).symm
  rw [hlogx, hlogy]
  have hreal :
      Real.log (2 * Real.pi * y) - Real.log (2 * Real.pi * x) =
        -Real.log (1 + x) := by
    dsimp [y]
    rw [Real.log_mul htwopi.ne' (div_ne_zero hx.ne' hx1.ne'),
      Real.log_mul htwopi.ne' hx.ne',
      Real.log_div hx.ne' hx1.ne']
    ring
  rw [show (Real.log (2 * Real.pi * y) : ℂ) -
      (Real.log (2 * Real.pi * x) : ℂ) =
      -(Real.log (1 + x) : ℂ) by exact_mod_cast hreal]
  rw [Complex.ofReal_log hx1.le]
  push_cast
  unfold routeCTaylorElementaryModel
  rw [if_neg hz]
  ring

/-! ## Complete elementary power series -/

/-- Dividing the shifted logarithm series by `z` gives the regular power
series for `log(1+z)/z`. -/
theorem hasSum_routeCTaylorLogOneAdd_div
    (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    HasSum
      (fun m : ℕ => (-1 : ℂ) ^ m * z ^ m / (m + 1 : ℕ))
      (Complex.log (1 + z) / z) := by
  have hlog := Complex.hasSum_taylorSeries_log hz
  have hshift := (hasSum_nat_add_iff' 1).2 hlog
  have hzero : ∑ i ∈ Finset.range 1,
      (-1 : ℂ) ^ (i + 1) * z ^ i / (i : ℂ) = 0 := by
    simp
  rw [hzero, sub_zero] at hshift
  have hscaled := hshift.mul_left z⁻¹
  convert hscaled using 1
  · funext m
    rw [pow_succ]
    push_cast
    field_simp [hz0]
    rw [pow_succ z m, pow_succ (-1 : ℂ) m]
    ring
  · field_simp [hz0]

/-- **Complete elementary Taylor theorem.**  The removable elementary model
is represented on the entire open unit disc by the exact coefficients used
in the contour calculation. -/
theorem hasSum_routeCTaylorElementarySeries
    (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum
      (fun m : ℕ => routeCTaylorElementarySeriesCoefficient m * z ^ m)
      (routeCTaylorElementaryModel z) := by
  by_cases hz0 : z = 0
  · subst z
    have hzero : HasSum (fun _ : ℕ => (0 : ℂ)) 0 := hasSum_zero
    have hseq :
        (fun m : ℕ =>
          routeCTaylorElementarySeriesCoefficient m * (0 : ℂ) ^ m) =
        (fun _ : ℕ => (0 : ℂ)) := by
      funext m
      by_cases hm : 2 ≤ m
      · simp [routeCTaylorElementarySeriesCoefficient, hm,
          zero_pow (by omega : m ≠ 0)]
      · simp [routeCTaylorElementarySeriesCoefficient, hm]
    rw [hseq]
    unfold routeCTaylorElementaryModel
    rw [if_pos rfl]
    exact hzero
  have hlog := Complex.hasSum_taylorSeries_log hz
  have hP : HasSum
      (fun m : ℕ => (-1 : ℂ) ^ m * z ^ m / (m : ℂ))
      (-Complex.log (1 + z)) := by
    convert hlog.neg using 1
    funext m
    ring
  have hB := hasSum_routeCTaylorLogOneAdd_div z hz0 hz
  have hdiff := hP.sub hB
  have hconstant : HasSum
      (fun m : ℕ => if m = 0 then (1 : ℂ) else 0) 1 :=
    hasSum_ite_eq 0 1
  have hlinear : HasSum
      (fun m : ℕ => if m = 1 then z / 2 else 0) (z / 2) :=
    hasSum_ite_eq 1 (z / 2)
  have htotal := (hdiff.add hconstant).add hlinear
  convert htotal using 1
  · funext m
    unfold routeCTaylorElementarySeriesCoefficient
      routeCTaylorElementaryScalarCoefficient
    by_cases hm0 : m = 0
    · subst m
      norm_num
    by_cases hm1 : m = 1
    · subst m
      norm_num
      ring
    have hm : 2 ≤ m := by omega
    simp only [hm, if_true, hm0, hm1, if_false]
    push_cast
    have hmC : (m : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < m))
    have hm1C : ((m + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero m
    field_simp [hmC, hm1C]
    ring
  · unfold routeCTaylorElementaryModel
    rw [if_neg hz0]
    field_simp [hz0]
    ring

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorElementaryTransfer
