/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15SignedRightLine

/-!
# NB12x: Bettin--Chandee exponent audit for the H15 right edge

This file performs the exact balanced-block exponent substitution into
Theorem 1 of Bettin--Chandee, *Trilinear forms with Kloosterman fractions*
(2015).  It does not postulate that theorem as a Lean axiom.

For one orientation and fixed gcd slice, the `Re(s)=3/2` functional equation
leaves separated arithmetic coefficients of sizes

* `c_N(g a) / a` in the inverse-residue variable `a`;
* `c_N(g q) * q` in the modulus variable `q`;
* `d(r) / r^(3/2+it)` in the frequency variable `r`;

together with the global factors `delta_N^(3/2) / g`.  The first theorem
below proves the finite H15 `a,q` factorization exactly.

On balanced blocks `a,q ~ X` and `r ~ R`, the coefficient `L²` norms have
model size `X / R`.  Substitution into the two terms of Bettin--Chandee
Theorem 1 gives, before arbitrary epsilon losses,

`N^(9/20) R^(-13/20)` and `N^(3/8) R^(-1/2)`

on the top gcd block `X ~ N`.  Thus the published theorem gives decay only
once `R` is beyond `N^(3/4+eta)`.  It does not control the fixed or low
frequency sector needed by the current signed `L¹` package.
-/

open scoped BigOperators Topology
open Complex

namespace NBMellinTools.NB12

open NBMellinTools.NB8

/-! ## Exact H15 separated coefficient -/

theorem h15LaurentRow_denominator_eq_q_of_orientation_zero
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i)
    (horientation : h15LaurentOrientation i = 0) :
    (h15LaurentRow i).denominator = h15LaurentQ i := by
  have hcop : Nat.Coprime (h15LaurentA i) (h15LaurentQ i) :=
    hvalid.2.2.2.2
  simp [h15LaurentRow_denominator, h15LaurentReducedDenominator,
    horientation, hcop.gcd_eq_one]

/-- After the functional equation contributes the square of the modulus, the
orientation-zero H15 coefficient separates exactly into an `a` coefficient,
a `q` coefficient and the global `pi/g` factor. -/
theorem h15LaurentRowWeight_mul_denominator_sq_factorization
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i)
    (horientation : h15LaurentOrientation i = 0) :
    h15LaurentRowWeight i *
        ((h15LaurentRow i).denominator : ℂ) ^ 2 =
      (((Real.pi / (h15LaurentG i : ℝ)) *
        (h15NaturalLogTaperCoeff N
            (h15LaurentG i * h15LaurentA i) /
          (h15LaurentA i : ℝ)) *
        (h15NaturalLogTaperCoeff N
            (h15LaurentG i * h15LaurentQ i) *
          (h15LaurentQ i : ℝ)) : ℝ) : ℂ) := by
  rw [h15LaurentRow_denominator_eq_q_of_orientation_zero i hvalid horientation]
  simp only [h15LaurentRowWeight, if_pos hvalid]
  push_cast
  have hg : ((h15LaurentG i : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by simp [h15LaurentG] : h15LaurentG i ≠ 0)
  have ha : ((h15LaurentA i : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by simp [h15LaurentA] : h15LaurentA i ≠ 0)
  have hq : ((h15LaurentQ i : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by simp [h15LaurentQ] : h15LaurentQ i ≠ 0)
  field_simp [hg, ha, hq]

/-! ## Exact balanced exponent ledger -/

/-- Exponent of `N` in the first Bettin--Chandee term after inserting the
three-halves damping and the balanced H15 coefficient norms. -/
noncomputable def h15BettinChandeeFirstNExponent : ℝ :=
  -(3 / 2) + 1 + 7 / 10 + 1 / 4

/-- Exponent of the frequency scale in the first term. -/
noncomputable def h15BettinChandeeFirstFrequencyExponent : ℝ :=
  -1 + 7 / 20

/-- Exponent of `N` in the second Bettin--Chandee term. -/
noncomputable def h15BettinChandeeSecondNExponent : ℝ :=
  -(3 / 2) + 1 + 3 / 4 + 1 / 8

/-- Exponent of the frequency scale in the second term. -/
noncomputable def h15BettinChandeeSecondFrequencyExponent : ℝ :=
  -1 + 3 / 8 + 1 / 8

theorem h15BettinChandeeFirstNExponent_eq :
    h15BettinChandeeFirstNExponent = 9 / 20 := by
  norm_num [h15BettinChandeeFirstNExponent]

theorem h15BettinChandeeFirstFrequencyExponent_eq :
    h15BettinChandeeFirstFrequencyExponent = -(13 / 20) := by
  norm_num [h15BettinChandeeFirstFrequencyExponent]

theorem h15BettinChandeeSecondNExponent_eq :
    h15BettinChandeeSecondNExponent = 3 / 8 := by
  norm_num [h15BettinChandeeSecondNExponent]

theorem h15BettinChandeeSecondFrequencyExponent_eq :
    h15BettinChandeeSecondFrequencyExponent = -(1 / 2) := by
  norm_num [h15BettinChandeeSecondFrequencyExponent]

/-- Total first-term exponent when the frequency block has scale
`R = N^kappa`. -/
noncomputable def h15BettinChandeeFirstScaledExponent (kappa : ℝ) : ℝ :=
  9 / 20 - (13 / 20) * kappa

/-- Total second-term exponent under the same substitution. -/
noncomputable def h15BettinChandeeSecondScaledExponent (kappa : ℝ) : ℝ :=
  3 / 8 - kappa / 2

/-- Since the theorem supplies the sum of its two terms, the worse exponent
is the maximum. -/
noncomputable def h15BettinChandeeWorstScaledExponent (kappa : ℝ) : ℝ :=
  max (h15BettinChandeeFirstScaledExponent kappa)
    (h15BettinChandeeSecondScaledExponent kappa)

theorem h15BettinChandeeFirstScaledExponent_neg_iff (kappa : ℝ) :
    h15BettinChandeeFirstScaledExponent kappa < 0 ↔
      9 / 13 < kappa := by
  unfold h15BettinChandeeFirstScaledExponent
  constructor <;> intro h <;> linarith

theorem h15BettinChandeeSecondScaledExponent_neg_iff (kappa : ℝ) :
    h15BettinChandeeSecondScaledExponent kappa < 0 ↔
      3 / 4 < kappa := by
  unfold h15BettinChandeeSecondScaledExponent
  constructor <;> intro h <;> linarith

/-- The exact no-epsilon threshold of the published balanced exponent pair.
Arbitrary epsilon losses require a strict margin beyond `3/4`. -/
theorem h15BettinChandeeWorstScaledExponent_neg_iff (kappa : ℝ) :
    h15BettinChandeeWorstScaledExponent kappa < 0 ↔
      3 / 4 < kappa := by
  rw [h15BettinChandeeWorstScaledExponent, max_lt_iff,
    h15BettinChandeeFirstScaledExponent_neg_iff,
    h15BettinChandeeSecondScaledExponent_neg_iff]
  constructor
  · exact fun h => h.2
  · intro h
    constructor
    · linarith
    · exact h

/-- Fixed-frequency blocks fail the exponent stop test: the available upper
bound grows like `N^(9/20)` before epsilon losses. -/
theorem h15BettinChandeeWorstScaledExponent_zero :
    h15BettinChandeeWorstScaledExponent 0 = 9 / 20 := by
  norm_num [h15BettinChandeeWorstScaledExponent,
    h15BettinChandeeFirstScaledExponent,
    h15BettinChandeeSecondScaledExponent, max_eq_left]

/-- At the boundary `R=N^(3/4)`, the second contribution has exponent zero;
strictly larger frequency is necessary for power decay. -/
theorem h15BettinChandeeSecondScaledExponent_three_quarters :
    h15BettinChandeeSecondScaledExponent (3 / 4) = 0 := by
  norm_num [h15BettinChandeeSecondScaledExponent]

end NBMellinTools.NB12
