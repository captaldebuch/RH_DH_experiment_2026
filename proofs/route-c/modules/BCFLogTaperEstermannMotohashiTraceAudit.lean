import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiCompensation

/-!
# BT1-C4: Motohashi trace-seminorm audit

Motohashi's Chapter 6 supplies a qualitative Sobolev mechanism for the
spectral resolution.  Equation (6.3.25) trades a power of the Casimir/K-type
operator against decay in the spectral parameters, while Section 6.5
explicitly leaves convergence aside in the general big-cell calculation
(6.5.13)--(6.5.21).  In particular, the source does not state a finite
largest Schwartz-seminorm order or a power of modulus decay for an arbitrary
seed.

This module therefore records the source-faithful quantitative conclusion in
parametric form.  If a later rigorous trace theorem consumes a radial
polynomial-weight order `k >= 1`, the exact H15 double inverse-modulus
normalization leaves the residual exponent

`2 * (k - 1)`.

A trace estimate whose conductor gain merely equals that exponent has a
constant majorant.  One additional power gives a reciprocal majorant and
hence convergence to zero.  No claim is made here that Motohashi's formal
identity supplies that additional power.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiTraceAudit

open Filter Real Topology
open scoped Topology

/-! ## Exact residual-power ledger -/

/-- Residual modulus exponent after the two H15 inverse-modulus factors have
been retained inside a seminorm of polynomial radial order `k`. -/
def h15MotohashiResidualExponent (k : ℕ) : ℕ :=
  2 * (k - 1)

@[simp]
theorem h15MotohashiResidualExponent_zero :
    h15MotohashiResidualExponent 0 = 0 := by
  simp [h15MotohashiResidualExponent]

@[simp]
theorem h15MotohashiResidualExponent_one :
    h15MotohashiResidualExponent 1 = 0 := by
  simp [h15MotohashiResidualExponent]

@[simp]
theorem h15MotohashiResidualExponent_succ (k : ℕ) :
    h15MotohashiResidualExponent (k + 1) = 2 * k := by
  simp [h15MotohashiResidualExponent]

/-- Normalized power profile obtained by dividing the residual seminorm cost
by a hypothetical trace/conductor gain.  The shift `N + 1` makes the profile
defined and positive at every natural cutoff. -/
noncomputable def h15MotohashiTracePowerProfile
    (seminormOrder gainPower N : ℕ) : ℝ :=
  (((N + 1 : ℕ) : ℝ) ^
      h15MotohashiResidualExponent seminormOrder) /
    (((N + 1 : ℕ) : ℝ) ^ gainPower)

/-- Matching the residual exponent is critical: the power majorant is
identically one, not a decaying bound. -/
theorem h15MotohashiTracePowerProfile_critical
    (seminormOrder N : ℕ) :
    h15MotohashiTracePowerProfile seminormOrder
        (h15MotohashiResidualExponent seminormOrder) N = 1 := by
  unfold h15MotohashiTracePowerProfile
  have hN : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  exact div_self (pow_ne_zero _ hN)

/-- One power beyond the residual exponent leaves exactly a reciprocal
factor. -/
theorem h15MotohashiTracePowerProfile_one_power_surplus
    (seminormOrder N : ℕ) :
    h15MotohashiTracePowerProfile seminormOrder
        (h15MotohashiResidualExponent seminormOrder + 1) N =
      (((N + 1 : ℕ) : ℝ))⁻¹ := by
  unfold h15MotohashiTracePowerProfile
  have hN : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

/-- With no conductor gain, the profile is exactly the residual polynomial
cost.  Motohashi (6.5.20)--(6.5.21) is an identity and by itself contributes
no additional modulus power. -/
theorem h15MotohashiTracePowerProfile_zero_gain
    (seminormOrder N : ℕ) :
    h15MotohashiTracePowerProfile seminormOrder 0 N =
      (((N + 1 : ℕ) : ℝ) ^
        h15MotohashiResidualExponent seminormOrder) := by
  simp [h15MotohashiTracePowerProfile]

theorem one_le_h15MotohashiTracePowerProfile_zero_gain
    (seminormOrder N : ℕ) :
    1 ≤ h15MotohashiTracePowerProfile seminormOrder 0 N := by
  rw [h15MotohashiTracePowerProfile_zero_gain]
  apply one_le_pow₀
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)

/-- The critical power profile tends to one.  Thus a trace estimate which
only balances the seminorm loss cannot prove decay by this majorant. -/
theorem h15MotohashiTracePowerProfile_critical_tendsto_one
    (seminormOrder : ℕ) :
    Tendsto
      (h15MotohashiTracePowerProfile seminormOrder
        (h15MotohashiResidualExponent seminormOrder))
      atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  exact Filter.Eventually.of_forall fun N =>
    (h15MotohashiTracePowerProfile_critical seminormOrder N).symm

/-- One surplus conductor power makes the profile tend to zero. -/
theorem h15MotohashiTracePowerProfile_one_power_surplus_tendsto_zero
    (seminormOrder : ℕ) :
    Tendsto
      (h15MotohashiTracePowerProfile seminormOrder
        (h15MotohashiResidualExponent seminormOrder + 1))
      atTop (nhds 0) := by
  have hinv : Tendsto
      (fun N : ℕ => (((N + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
    simpa using (tendsto_add_atTop_iff_nat (α := ℝ) 1).2
      tendsto_inv_atTop_nhds_zero_nat
  apply hinv.congr'
  exact Filter.Eventually.of_forall fun N =>
    (h15MotohashiTracePowerProfile_one_power_surplus
      seminormOrder N).symm

/-- A zero-gain power majorant cannot itself tend to zero, for every value is
at least one.  This does not rule out cancellation in the signed output; it
rules out proving that cancellation from the source's bare continuity
majorant. -/
theorem h15MotohashiTracePowerProfile_zero_gain_not_tendsto_zero
    (seminormOrder : ℕ) :
    ¬ Tendsto (h15MotohashiTracePowerProfile seminormOrder 0)
        atTop (nhds 0) := by
  intro h
  have hbad : (1 : ℝ) ≤ 0 := by
    apply ge_of_tendsto h
    exact Filter.Eventually.of_forall fun N =>
      one_le_h15MotohashiTracePowerProfile_zero_gain seminormOrder N
  norm_num at hbad

/-! ## Proof-carrying finite-order trace threshold -/

/-- Quantitative data that a future rigorous Motohashi trace theorem must
provide.  `seminormOrder` is deliberately explicit: the primary source does
not specify a largest order for the arbitrary big-cell seed. -/
structure H15MotohashiPolynomialTraceBudget where
  seminormOrder : ℕ
  seminormOrder_pos : 0 < seminormOrder
  gainPower : ℕ
  seedCost : ℕ → ℝ
  signedOutput : ℕ → ℝ
  Cseed : ℝ
  Ctrace : ℝ
  Cseed_nonneg : 0 ≤ Cseed
  Ctrace_nonneg : 0 ≤ Ctrace
  seedCost_nonneg : ∀ N, 0 ≤ seedCost N
  seedCost_bound : ∀ N,
    seedCost N ≤ Cseed *
      (((N + 1 : ℕ) : ℝ) ^
        h15MotohashiResidualExponent seminormOrder)
  signed_trace_bound : ∀ N,
    |signedOutput N| ≤ Ctrace * seedCost N /
      (((N + 1 : ℕ) : ℝ) ^ gainPower)

/-- Every quantitative trace budget is bounded by its exact residual/gain
profile. -/
theorem H15MotohashiPolynomialTraceBudget.output_abs_le_profile
    (H : H15MotohashiPolynomialTraceBudget) (N : ℕ) :
    |H.signedOutput N| ≤
      H.Ctrace * H.Cseed *
        h15MotohashiTracePowerProfile
          H.seminormOrder H.gainPower N := by
  have hden : 0 ≤ (((N + 1 : ℕ) : ℝ) ^ H.gainPower) := by positivity
  calc
    |H.signedOutput N| ≤
        H.Ctrace * H.seedCost N /
          (((N + 1 : ℕ) : ℝ) ^ H.gainPower) :=
      H.signed_trace_bound N
    _ ≤ H.Ctrace *
          (H.Cseed * (((N + 1 : ℕ) : ℝ) ^
            h15MotohashiResidualExponent H.seminormOrder)) /
          (((N + 1 : ℕ) : ℝ) ^ H.gainPower) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (H.seedCost_bound N) H.Ctrace_nonneg)
        hden
    _ = H.Ctrace * H.Cseed *
        h15MotohashiTracePowerProfile
          H.seminormOrder H.gainPower N := by
      unfold h15MotohashiTracePowerProfile
      ring

/-- **Strict-gain stop test.**  If the trace theorem supplies one power more
than its consumed H15 seminorm order costs, the signed output tends to zero.
This theorem is a transfer result, not an inhabitant of the missing trace
budget. -/
theorem H15MotohashiPolynomialTraceBudget.tendsto_zero_of_one_power_surplus
    (H : H15MotohashiPolynomialTraceBudget)
    (hgain : H.gainPower =
      h15MotohashiResidualExponent H.seminormOrder + 1) :
    Tendsto H.signedOutput atTop (nhds 0) := by
  have hprofile : Tendsto
      (h15MotohashiTracePowerProfile H.seminormOrder H.gainPower)
      atTop (nhds 0) := by
    rw [hgain]
    exact
      h15MotohashiTracePowerProfile_one_power_surplus_tendsto_zero
        H.seminormOrder
  apply squeeze_zero_norm
  · intro N
    simpa [Real.norm_eq_abs] using H.output_abs_le_profile N
  · have hconst : Tendsto (fun _ : ℕ => H.Ctrace * H.Cseed)
        atTop (nhds (H.Ctrace * H.Cseed)) := tendsto_const_nhds
    simpa using hconst.mul hprofile

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiTraceAudit
