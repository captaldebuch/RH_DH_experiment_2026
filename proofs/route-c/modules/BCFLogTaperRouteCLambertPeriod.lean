import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero

/-!
# Route C: the algebraic Lambert-period relation

At the central parameter Bettin--Conrey start in the upper half-plane with

`S₀(z) = ∑_{n≥1} d(n) exp(2*pi*i*n*z)`

and form the weight-one period

`S₀(z) - z⁻¹ S₀(-z⁻¹)`.

This file separates the elementary part of their Theorem 1 from its analytic
continuation.  The Lambert series is exactly one-periodic, term by term, and
the three-term equation of its period is then a field identity.  Neither
fact uses a contour shift, a rational boundary limit, or RH.

The still substantive source theorem is now isolated as the equality between
this upper-half-plane period and the contour-defined `bettinConreyPsiZero`.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPeriod

open Complex
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero

/-- The central divisor Lambert series, indexed by `n + 1` so that the
coefficient is the positive divisor count `d(n+1)`. -/
noncomputable def bettinConreyCentralLambertSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ,
    (((n + 1).divisors.card : ℕ) : ℂ) *
      Complex.exp
        ((2 * Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * z)

/-- The divisor Lambert series is one-periodic.  This identity is valid as a
total `tsum` identity; convergence is needed only for its analytic use in the
upper half-plane. -/
theorem bettinConreyCentralLambertSeries_periodic :
    Function.Periodic bettinConreyCentralLambertSeries 1 := by
  intro z
  unfold bettinConreyCentralLambertSeries
  apply tsum_congr
  intro n
  congr 1
  have hexp :
      Complex.exp
          ((2 * Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * (z + 1)) =
        Complex.exp
          ((2 * Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * z) := by
    calc
      Complex.exp
          ((2 * Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * (z + 1)) =
          Complex.exp
              ((2 * Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * z) *
            Complex.exp (((n + 1 : ℕ) : ℂ) * (2 * Real.pi * I)) := by
              rw [← Complex.exp_add]
              congr 1
              ring
      _ = Complex.exp
          ((2 * Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * z) := by
            rw [Complex.exp_nat_mul_two_pi_mul_I]
            simp
  exact hexp

/-- The weight-one period attached to an arbitrary function. -/
noncomputable def centralPeriodOf (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F z - z⁻¹ * F (-z⁻¹)

/-- A one-periodic function gives a weight-one three-term period.  This is
the exact algebra behind Bettin--Conrey Theorem 1. -/
theorem centralPeriodOf_threeTerm
    (F : ℂ → ℂ) (hF : Function.Periodic F 1)
    (z : ℂ) (hz : z ≠ 0) (hz1 : z + 1 ≠ 0) :
    centralPeriodOf F z - centralPeriodOf F (z + 1) =
      (z + 1)⁻¹ * centralPeriodOf F (z / (z + 1)) := by
  have hperiod₁ : F (z / (z + 1)) = F (-(z + 1)⁻¹) := by
    have hp := hF (-(z + 1)⁻¹)
    rw [show -(z + 1)⁻¹ + 1 = z / (z + 1) by
      field_simp
      ring] at hp
    exact hp
  have hperiod₂ : F (-(z / (z + 1))⁻¹) = F (-z⁻¹) := by
    have hp := hF.sub_eq (-z⁻¹)
    rw [show -z⁻¹ - 1 = -(z / (z + 1))⁻¹ by
      field_simp
      ring] at hp
    exact hp
  unfold centralPeriodOf
  rw [hF z, hperiod₁, hperiod₂]
  have hratio : z / (z + 1) ≠ 0 := div_ne_zero hz hz1
  field_simp [hz, hz1, hratio]
  ring

/-- The actual central divisor period in the upper half-plane. -/
noncomputable def bettinConreyCentralLambertPeriod (z : ℂ) : ℂ :=
  centralPeriodOf bettinConreyCentralLambertSeries z

/-- Bettin--Conrey's central Eisenstein normalization.  Since
`riemannZeta 0 = -1/2`, the factor `2 / zeta(0)` multiplying the Lambert
series is exactly `-4`. -/
noncomputable def bettinConreyCentralEisensteinSeries (z : ℂ) : ℂ :=
  1 - 4 * bettinConreyCentralLambertSeries z

/-- The central Eisenstein normalization inherits exact one-periodicity from
the divisor Lambert series. -/
theorem bettinConreyCentralEisensteinSeries_periodic :
    Function.Periodic bettinConreyCentralEisensteinSeries 1 := by
  intro z
  unfold bettinConreyCentralEisensteinSeries
  rw [bettinConreyCentralLambertSeries_periodic z]

/-- The Eisenstein period contains both the elementary constant mode and the
normalized Lambert period.  This is the normalization in equation (3) of
Bettin--Conrey, specialized to `a = 0`. -/
theorem centralPeriodOf_bettinConreyCentralEisensteinSeries (z : ℂ) :
    centralPeriodOf bettinConreyCentralEisensteinSeries z =
      1 - z⁻¹ - 4 * bettinConreyCentralLambertPeriod z := by
  unfold centralPeriodOf bettinConreyCentralEisensteinSeries
    bettinConreyCentralLambertPeriod
  unfold centralPeriodOf
  ring

/-- Unconditional three-term relation for the central divisor period. -/
theorem bettinConreyCentralLambertPeriod_threeTerm
    (z : ℂ) (hz : z ≠ 0) (hz1 : z + 1 ≠ 0) :
    bettinConreyCentralLambertPeriod z -
        bettinConreyCentralLambertPeriod (z + 1) =
      (z + 1)⁻¹ *
        bettinConreyCentralLambertPeriod (z / (z + 1)) :=
  centralPeriodOf_threeTerm _
    bettinConreyCentralLambertSeries_periodic z hz hz1

/-- The exact analytic-continuation theorem needed to identify the algebraic
Lambert period with the literal Mellin-contour period `psi₀`.  The elementary
mode and the factor `-4` are retained: equation (3) gives

`psi₀(z) = 1 - z⁻¹ - 4 * centralLambertPeriod(z)`.

It is kept as a proposition-valued interface; no inhabitant is asserted. -/
structure BettinConreyLambertPsiZeroIdentification where
  eq_on_upperHalfPlane : ∀ z : ℂ, 0 < z.im →
    bettinConreyCentralLambertPeriod z =
      (1 - z⁻¹ - bettinConreyPsiZero z) / 4

/-- The corrected Lambert identification is equivalent to the source
Eisenstein-period normalization. -/
theorem centralPeriodOf_eisenstein_eq_psiZero
    (H : BettinConreyLambertPsiZeroIdentification)
    (z : ℂ) (hz : 0 < z.im) :
    centralPeriodOf bettinConreyCentralEisensteinSeries z =
      bettinConreyPsiZero z := by
  rw [centralPeriodOf_bettinConreyCentralEisensteinSeries,
    H.eq_on_upperHalfPlane z hz]
  ring

/-- The corrected upper-half-plane identification transfers the algebraic
period relation to the literal source function `psi_0`. -/
theorem bettinConreyPsiZero_threeTerm_on_upperHalfPlane
    (H : BettinConreyLambertPsiZeroIdentification)
    (z : ℂ) (hzIm : 0 < z.im) :
    bettinConreyPsiZero z - bettinConreyPsiZero (z + 1) =
      (z + 1)⁻¹ * bettinConreyPsiZero (z / (z + 1)) := by
  have hz : z ≠ 0 := by
    intro hz
    subst z
    simp at hzIm
  have hz1 : z + 1 ≠ 0 := by
    intro hz1
    have him := congrArg Complex.im hz1
    norm_num at him
    linarith
  have hz1Im : 0 < (z + 1).im := by
    simpa using hzIm
  have hratioIm : 0 < (z / (z + 1)).im := by
    rw [Complex.div_im]
    have hnorm : 0 < Complex.normSq (z + 1) :=
      Complex.normSq_pos.mpr hz1
    have hnum :
        z.im * (z + 1).re - z.re * (z + 1).im = z.im := by
      norm_num
      ring
    rw [← sub_div, hnum]
    positivity
  rw [← centralPeriodOf_eisenstein_eq_psiZero H z hzIm,
    ← centralPeriodOf_eisenstein_eq_psiZero H (z + 1) hz1Im,
    ← centralPeriodOf_eisenstein_eq_psiZero H (z / (z + 1)) hratioIm]
  exact centralPeriodOf_threeTerm _
    bettinConreyCentralEisensteinSeries_periodic z hz hz1

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPeriod
