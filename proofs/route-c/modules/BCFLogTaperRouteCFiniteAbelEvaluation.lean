import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCCoupledFinitePart
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelCentralConstructor

/-!
# Route C: unconditional finite rational Abel evaluation

The coupled contour calculation supplies an explicit boundary involving two
Estermann values at zero.  This module evaluates those values by the already
proved rational Hurwitz endpoint and finite Fourier transform, then matches
the result exactly with the central finite cotangent boundary.

Consequently `BettinConreyCentralRationalFiniteAbelEvaluation` is now a
theorem rather than an open interface.  This is local classical analysis; it
does not assert the outer H15 low-mode estimate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCFiniteAbelEvaluation

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFiniteFourier
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelCentralConstructor
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralOnlyAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCoupledFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPeriod
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodRealization
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCReciprocalContour
open RH.Criteria.NymanBeurling.BCFLogTaperRationalSineEndpoint

/-- Direct central normalization of the analytic Estermann value at zero:
`D(0,a/q) = 1/4 + (i/2)c₀(a/q)`. -/
theorem estermannHurwitzContinuation_zero_eq_centralFiniteSum
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    estermannHurwitzContinuation a q 0 =
      (1 / 4 : ℂ) + Complex.I / 2 *
        bettinConreyCentralFiniteSum a q := by
  let HZ : HurwitzZetaZeroFormula :=
    (hurwitzZetaZeroNonzeroFormula_of_rationalSineZetaOne
      rationalSineZetaOneFormula).toZeroFormula
  rw [estermannHurwitzContinuation_zero_eq_bernoulliFinite HZ]
  unfold estermannBernoulliFiniteValue
  simp_rw [sum_estermannResiduePhase_mul_bernoulli]
  have hzero := dft_periodicBernoulliOneValue (q := q) (0 : ZMod q)
  rw [ZMod.dft_apply_zero, residueCotangent_zero] at hzero
  rw [bettinConreyCentralFiniteSum_eq_residueSum a q hcop]
  unfold bettinConreyCentralResidueSum
  calc
    (∑ j : ZMod q,
        (-(1 : ℂ) / 2 + Complex.I / 2 *
            residueCotangent ((a : ZMod q) * j)) *
          periodicBernoulliOneValue j) =
        -(1 : ℂ) / 2 *
            (∑ j : ZMod q, periodicBernoulliOneValue j) +
          Complex.I / 2 *
            (∑ j : ZMod q,
              residueCotangent ((a : ZMod q) * j) *
                periodicBernoulliOneValue j) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (1 / 4 : ℂ) + Complex.I / 2 *
          (∑ j : ZMod q,
            residueCotangent ((a : ZMod q) * j) *
              periodicBernoulliOneValue j) := by
          rw [hzero]
          ring

/-- Negating the reduced additive numerator negates the literal central
cotangent sum. -/
theorem bettinConreyCentralFiniteSum_negativeTwist
    (h k : ℕ) [NeZero h] (hcop : Nat.Coprime h k) :
    bettinConreyCentralFiniteSum (bettinConreyNegativeTwist h k) h =
      -bettinConreyCentralFiniteSum k h := by
  rw [bettinConreyCentralFiniteSum_eq_residueSum
      (bettinConreyNegativeTwist h k) h
      (bettinConreyNegativeTwist_coprime h k hcop.symm),
    bettinConreyCentralFiniteSum_eq_residueSum k h hcop.symm]
  unfold bettinConreyCentralResidueSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [bettinConreyNegativeTwist_cast]
  have hneg : (-(k : ZMod h)) * j = -((k : ZMod h) * j) := by ring
  rw [hneg, residueCotangent_neg]
  ring

/-- The explicit contour boundary is exactly the finite cotangent boundary
used by the central Abel constructor. -/
theorem bettinConreyExplicitBoundary_eq_finiteAbelBoundary
    (h k : ℕ) [NeZero h] [NeZero k]
    (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    estermannHurwitzContinuation h k 0 -
        Complex.I * ((2 * Real.pi : ℂ) * (h : ℂ))⁻¹ -
        ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ))⁻¹ *
          estermannHurwitzContinuation
            (bettinConreyNegativeTwist h k) h 0 =
      bettinConreyCentralFiniteAbelBoundaryValue h k := by
  rw [estermannHurwitzContinuation_zero_eq_centralFiniteSum
      h k hcop,
    estermannHurwitzContinuation_zero_eq_centralFiniteSum
      (bettinConreyNegativeTwist h k) h
      (bettinConreyNegativeTwist_coprime h k hcop.symm),
    bettinConreyCentralFiniteSum_negativeTwist h k hcop]
  unfold bettinConreyCentralFiniteAbelBoundaryValue
  dsimp only
  rw [← bettinConreyCentralFinitePartSideC_eq_ofReal h k hh hk]
  unfold bettinConreyCentralFinitePartSideC
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp [hhC, hkC, hpiC]
  ring

/-- The formerly open finite Abel evaluation is fully inhabited by the
two-pole contour, Laurent coefficient, and finite Fourier endpoint. -/
theorem bettinConreyCentralRationalFiniteAbelEvaluation_proved :
    BettinConreyCentralRationalFiniteAbelEvaluation := by
  intro h k hh hk hcop
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hlimit := tendsto_bettinConreyRationalDampedPeriod_explicit
    h k hh hk hcop
  rw [bettinConreyExplicitBoundary_eq_finiteAbelBoundary
    h k hh hk hcop] at hlimit
  exact hlimit

/-! ## Reduced Phase 3 constructor -/

/-- Once the upper-half-plane Lambert identification and right-half-plane
continuity of the literal period function are available, the finite boundary
proved above supplies the complete Phase 3 constructor data.  In particular,
the rational cotangent boundary is no longer an independent hypothesis. -/
noncomputable def bettinConreyCentralAbelConstructorData_of_identification
    (H : BettinConreyLambertPsiZeroIdentification)
    (hpsi : ∀ z : ℂ, 0 < z.re → ContinuousAt bettinConreyPsiZero z) :
    BettinConreyCentralAbelConstructorData where
  finiteBoundary :=
    bettinConreyCentralRationalFiniteAbelEvaluation_proved
  identification := H
  psiContinuous := hpsi

/-- The entire central rational Bettin--Conrey theorem now follows from only
the two global analytic facts about the literal period function. -/
noncomputable def bettinConreyPsiZeroCentralRationalTheorem_of_identification
    (H : BettinConreyLambertPsiZeroIdentification)
    (hpsi : ∀ z : ℂ, 0 < z.re → ContinuousAt bettinConreyPsiZero z) :
    BettinConreyPsiZeroCentralRationalTheorem :=
  BettinConreyCentralAbelConstructorData.toCentralRationalTheorem
    (bettinConreyCentralAbelConstructorData_of_identification H hpsi)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCFiniteAbelEvaluation
