import Mathlib.Analysis.Analytic.OfScalars
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPeriod

/-!
# Route C: native analytic form of the central Taylor theorem

The remaining Taylor step is best stated as a genuine complex power series,
not as an isolated equality of `tsum`s.  This module packages the exact
scalar coefficients from Bettin--Conrey Theorem 2 as a Mathlib
`FormalMultilinearSeries`, proves the first two coefficients vanish, and
derives the previously used `HasSum` and value-identity interfaces from a
power-series theorem on the open unit disc.

Thus the source proof has one quantitative analytic target:
`bettinConreyPsiZeroTaylorSeriesOnDisc`.  Its proof must still identify the
derivatives of the Mellin-contour period with the Bernoulli--zeta formula;
that calculation is not asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic

open Complex
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero

/-- The complete source-normalized analytic function whose Taylor series
starts in degree two. -/
noncomputable def bettinConreyPsiZeroTaylorFunction (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * I / 2 * (1 + z) *
      bettinConreyPsiZero (1 + z) + 1 + z / 2

/-- Scalar coefficient sequence of the Taylor theorem, including its two
vanishing initial coefficients. -/
noncomputable def bettinConreyPsiZeroTaylorScalarCoefficient
    (n : ℕ) : ℂ :=
  if 2 ≤ n then
    bettinConreyCentralTaylorCoefficient n * (-1 : ℂ) ^ n
  else 0

/-- The preceding scalar sequence as Mathlib's native one-variable formal
multilinear series. -/
noncomputable def bettinConreyPsiZeroTaylorFormalSeries :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    bettinConreyPsiZeroTaylorScalarCoefficient

@[simp] theorem bettinConreyPsiZeroTaylorScalarCoefficient_zero :
    bettinConreyPsiZeroTaylorScalarCoefficient 0 = 0 := by
  simp [bettinConreyPsiZeroTaylorScalarCoefficient]

@[simp] theorem bettinConreyPsiZeroTaylorScalarCoefficient_one :
    bettinConreyPsiZeroTaylorScalarCoefficient 1 = 0 := by
  simp [bettinConreyPsiZeroTaylorScalarCoefficient]

@[simp] theorem bettinConreyPsiZeroTaylorScalarCoefficient_add_two
    (n : ℕ) :
    bettinConreyPsiZeroTaylorScalarCoefficient (n + 2) =
      bettinConreyCentralTaylorCoefficient (n + 2) *
        (-1 : ℂ) ^ (n + 2) := by
  simp [bettinConreyPsiZeroTaylorScalarCoefficient]

/-- The literal native-analytic target extracted from Bettin--Conrey's
Taylor theorem.  No inhabitant is declared: constructing it is precisely the
contour differentiation and coefficient-identification proof. -/
structure BettinConreyPsiZeroTaylorSeriesOnDisc where
  hasSeries : HasFPowerSeriesOnBall
    bettinConreyPsiZeroTaylorFunction
    bettinConreyPsiZeroTaylorFormalSeries 0 1

/-- Evaluation of the formal scalar series is the expected ordinary power
series. -/
theorem bettinConreyPsiZeroTaylorFormalSeries_apply
    (n : ℕ) (z : ℂ) :
    bettinConreyPsiZeroTaylorFormalSeries n (fun _ => z) =
      bettinConreyPsiZeroTaylorScalarCoefficient n * z ^ n := by
  simp [bettinConreyPsiZeroTaylorFormalSeries]
  ring

/-- A native power-series proof on the unit disc yields the exact shifted
`HasSum` statement consumed by the Route-C package. -/
theorem BettinConreyPsiZeroTaylorSeriesOnDisc.hasSum
    (H : BettinConreyPsiZeroTaylorSeriesOnDisc)
    (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum
      (fun n : ℕ =>
        bettinConreyCentralTaylorCoefficient (n + 2) *
          (-z) ^ (n + 2))
      (bettinConreyPsiZeroTaylorFunction z) := by
  have hzball : z ∈ Metric.eball (0 : ℂ) (1 : ENNReal) := by
    rw [Metric.mem_eball, edist_dist]
    simp only [dist_zero_right, ENNReal.ofReal_lt_one]
    exact hz
  have hfull := H.hasSeries.hasSum hzball
  have hfull' : HasSum
      (fun n : ℕ =>
        bettinConreyPsiZeroTaylorScalarCoefficient n * z ^ n)
      (bettinConreyPsiZeroTaylorFunction z) := by
    simp_rw [bettinConreyPsiZeroTaylorFormalSeries_apply] at hfull
    simpa [mul_comm] using hfull
  have hshift := (hasSum_nat_add_iff' 2).2 hfull'
  have hzero :
      ∑ i ∈ Finset.range 2,
        bettinConreyPsiZeroTaylorScalarCoefficient i * z ^ i = 0 := by
    norm_num [Finset.sum_range_succ,
      bettinConreyPsiZeroTaylorScalarCoefficient]
  rw [hzero, sub_zero] at hshift
  have hfun :
      (fun n : ℕ =>
        bettinConreyPsiZeroTaylorScalarCoefficient (n + 2) *
          z ^ (n + 2)) =
      fun n : ℕ =>
        bettinConreyCentralTaylorCoefficient (n + 2) *
          (-z) ^ (n + 2) := by
    funext n
    rw [bettinConreyPsiZeroTaylorScalarCoefficient_add_two, neg_pow]
    ring
  rw [← hfun]
  exact hshift

/-- Native analyticity supplies the exact Taylor `HasSum` interface used by
the final package constructor. -/
noncomputable def BettinConreyPsiZeroTaylorSeriesOnDisc.toTaylorHasSum
    (H : BettinConreyPsiZeroTaylorSeriesOnDisc) :
    BettinConreyPsiZeroTaylorHasSum where
  hasSum := by
    intro z hz
    simpa [bettinConreyPsiZeroTaylorFunction] using H.hasSum z hz

/-- It also supplies the economical value-only interface; coefficient decay
can then be supplied independently by the saddle-point work package. -/
noncomputable def BettinConreyPsiZeroTaylorSeriesOnDisc.toValueIdentity
    (H : BettinConreyPsiZeroTaylorSeriesOnDisc) :
    BettinConreyPsiZeroTaylorValueIdentity where
  tsum_eq := by
    intro z hz
    exact (H.hasSum z hz).tsum_eq

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic
