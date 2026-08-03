import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Route C: Taylor coefficient identification

Bettin--Conrey's central Taylor theorem is printed as an ordinary scalar
series beginning in degree two.  Phase 4, however, consumes Mathlib's native
`FormalMultilinearSeries` formulation.  This file proves that the two
statements are exactly equivalent once the already separated absolute
coefficient estimate is available.

The result is not a new analytic hypothesis: it checks the zero coefficients
in degrees zero and one, the shift by two, the factor `(-1)^n`, and the radius
of convergence.  Thus a proof of the paper's literal scalar `HasSum` theorem
identifies the unique native Taylor coefficients used downstream.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCoefficientIdentification

open Complex ENNReal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic

/-- Root-exponential control of the centered row implies that the native
formal series has radius at least one.  The nondecaying `1/n` part is handled
by evaluation strictly inside the unit disc. -/
theorem bettinConreyPsiZeroTaylorFormalSeries_radius_ge_one
    (D : BettinConreyCentralCoefficientRootDecay) :
    (1 : ℝ≥0∞) ≤ bettinConreyPsiZeroTaylorFormalSeries.radius := by
  refine le_of_forall_nnreal_lt fun r hr => ?_
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have hrreal : (r : ℝ) < 1 := by
    simpa using hr
  have hraw := D.raw_taylor_summable (r : ℂ) (by
    simpa [Complex.norm_real, Real.norm_of_nonneg r.coe_nonneg] using hrreal)
  have hnorm := hraw.norm
  apply (summable_nat_add_iff 2).1
  simpa [bettinConreyPsiZeroTaylorFormalSeries,
    bettinConreyPsiZeroTaylorScalarCoefficient_add_two,
    FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
    norm_neg, NNReal.norm_eq, mul_assoc, mul_left_comm, mul_comm] using hnorm

/-- The literal shifted scalar theorem supplies the full native scalar
series after inserting its two zero initial coefficients. -/
theorem bettinConreyPsiZeroTaylor_full_hasSum
    (T : BettinConreyPsiZeroTaylorHasSum)
    (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum
      (fun n : ℕ =>
        bettinConreyPsiZeroTaylorScalarCoefficient n * z ^ n)
      (bettinConreyPsiZeroTaylorFunction z) := by
  have hzero :
      ∑ i ∈ Finset.range 2,
        bettinConreyPsiZeroTaylorScalarCoefficient i * z ^ i = 0 := by
    norm_num [Finset.sum_range_succ,
      bettinConreyPsiZeroTaylorScalarCoefficient]
  have hfun :
      (fun n : ℕ =>
        bettinConreyPsiZeroTaylorScalarCoefficient (n + 2) * z ^ (n + 2)) =
      (fun n : ℕ =>
        bettinConreyCentralTaylorCoefficient (n + 2) * (-z) ^ (n + 2)) := by
    funext n
    rw [bettinConreyPsiZeroTaylorScalarCoefficient_add_two, neg_pow]
    ring
  apply (hasSum_nat_add_iff' 2).1
  rw [hzero, sub_zero, hfun]
  exact T.hasSum z hz

/-- **Taylor coefficient-identification theorem.**  A proof of the paper's
literal scalar Taylor theorem, together with its independent absolute
coefficient estimate, constructs the exact Mathlib power series on `|z|<1`.
No derivative or coefficient formula is assumed a second time. -/
noncomputable def bettinConreyPsiZeroTaylorSeriesOnDisc_of_hasSum
    (T : BettinConreyPsiZeroTaylorHasSum)
    (D : BettinConreyCentralCoefficientRootDecay) :
    BettinConreyPsiZeroTaylorSeriesOnDisc where
  hasSeries := {
    r_le := bettinConreyPsiZeroTaylorFormalSeries_radius_ge_one D
    r_pos := by norm_num
    hasSum := by
      intro z hz
      have hznorm : ‖z‖ < 1 := by
        rw [Metric.mem_eball, edist_dist, dist_zero_right] at hz
        simpa only [ENNReal.ofReal_lt_one] using hz
      rw [zero_add]
      have hfull := bettinConreyPsiZeroTaylor_full_hasSum T z hznorm
      exact HasSum.congr_fun hfull (fun n =>
        bettinConreyPsiZeroTaylorFormalSeries_apply n z) }

/-- Economical version matching the source split used by Phase 4: the exact
Taylor value and the eventual coefficient asymptotic suffice. -/
noncomputable def bettinConreyPsiZeroTaylorSeriesOnDisc_of_valueIdentity
    (V : BettinConreyPsiZeroTaylorValueIdentity)
    (A : BettinConreyCentralCoefficientAsymptoticEnvelope) :
    BettinConreyPsiZeroTaylorSeriesOnDisc :=
  let D := A.toRootDecay
  bettinConreyPsiZeroTaylorSeriesOnDisc_of_hasSum (V.toHasSum D) D

/-- Coefficientwise uniqueness.  Any independently constructed analytic
power series for the normalized central period at zero has the
Bettin--Conrey scalar coefficient in every degree. -/
theorem bettinConreyPsiZeroTaylorCoefficient_identification
    (T : BettinConreyPsiZeroTaylorHasSum)
    (D : BettinConreyCentralCoefficientRootDecay)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt bettinConreyPsiZeroTaylorFunction p 0)
    (n : ℕ) :
    p.coeff n = bettinConreyPsiZeroTaylorScalarCoefficient n := by
  let H := bettinConreyPsiZeroTaylorSeriesOnDisc_of_hasSum T D
  have hcanonical := H.hasSeries.hasFPowerSeriesAt
  have heq : p = bettinConreyPsiZeroTaylorFormalSeries :=
    hp.eq_formalMultilinearSeries hcanonical
  have hn := congr_arg (FormalMultilinearSeries.coeff · n) heq
  simpa [bettinConreyPsiZeroTaylorFormalSeries] using hn

/-- In the degrees occurring in the paper, the identified coefficient is
exactly `a_n * (-1)^n`; the first two degrees were proved to vanish above. -/
theorem bettinConreyPsiZeroTaylorCoefficient_identification_of_two_le
    (T : BettinConreyPsiZeroTaylorHasSum)
    (D : BettinConreyCentralCoefficientRootDecay)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt bettinConreyPsiZeroTaylorFunction p 0)
    (n : ℕ) (hn : 2 ≤ n) :
    p.coeff n =
      bettinConreyCentralTaylorCoefficient n * (-1 : ℂ) ^ n := by
  rw [bettinConreyPsiZeroTaylorCoefficient_identification T D p hp n]
  simp [bettinConreyPsiZeroTaylorScalarCoefficient, hn]

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCoefficientIdentification
