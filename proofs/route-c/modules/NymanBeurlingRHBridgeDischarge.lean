import RiemannHypothesis.Criteria.NymanBeurling.NBChiMellin

/-!
# Nyman--Beurling forward bridge: discharged Mellin identities

The χ and generator Mellin evaluations are now theorems in
`NBChiMellin` and `H15RhoBDBaseDischarge`.  This file wires those results into
the existing RH-bridge debt package.  The remaining fields are deliberately
kept explicit: continuity of the Mellin evaluation under the L² approximation
and the zero-detection/transport step are the genuine Nyman--Beurling
analytic argument.  In particular, this file does not use the historical
iff axiom and does not claim to prove Plancherel or the zero-detection step.
-/

namespace RH.Criteria.NymanBeurling.RHBridge

open scoped BigOperators

open RH.Criteria.NymanBeurling.BaezDuarte

/-- The continuity half of the remaining Mellin transport debt, named
separately so it can be supplied by a future half-line Plancherel theorem. -/
structure MellinContinuityUnderL2Approx where
  statement :
    ∀ s₀ : ℂ, 1 / 2 < s₀.re → s₀.re < 1 → s₀ ≠ 0 →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (N : ℕ) (coeffs : Fin N → ℝ),
          ‖mellin
              (fun x : ℝ =>
                ((chi01 x - bdApprox N coeffs x : ℝ) : ℂ)) s₀‖ ≤
            C * Real.sqrt (BaezDuarteL2Error N coeffs)

/-- The zero-detection half of the remaining Mellin transport debt, named
separately from the continuity estimate. -/
structure ZeroTransportToChiHypothesis where
  statement :
    ∀ s₀ : ℂ, 1 / 2 < s₀.re → s₀.re < 1 → s₀ ≠ 0 →
      NymanBeurlingCriterion →
      (∀ k : ℕ,
        mellin (fun x : ℝ => (rhoBD k x : ℂ)) s₀ = 0) →
      mellin (fun x : ℝ => (chi01 x : ℂ)) s₀ = 0

/-- The residual analytic input after the χ and generator Mellin formulas have
been discharged.  `eval_functional_continuous` is the fixed-point continuity
estimate needed to pass from finite L² approximation to Mellin values;
`vanishing_transport` is the zero-detection step that turns vanishing of all
generator transforms into vanishing of the χ transform.  Both are stated as
content-bearing hypotheses, not axioms. -/
structure NymanBeurlingMellinTransportDebts where
  eval_functional_continuous :
    ∀ s₀ : ℂ, 1 / 2 < s₀.re → s₀.re < 1 → s₀ ≠ 0 →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (N : ℕ) (coeffs : Fin N → ℝ),
          ‖mellin
              (fun x : ℝ =>
                ((chi01 x - bdApprox N coeffs x : ℝ) : ℂ)) s₀‖ ≤
            C * Real.sqrt (BaezDuarteL2Error N coeffs)
  vanishing_transport :
    ∀ s₀ : ℂ, 1 / 2 < s₀.re → s₀.re < 1 → s₀ ≠ 0 →
      NymanBeurlingCriterion →
      (∀ k : ℕ,
        mellin (fun x : ℝ => (rhoBD k x : ℂ)) s₀ = 0) →
      mellin (fun x : ℝ => (chi01 x : ℂ)) s₀ = 0

/-- Assemble the full Mellin debt package from the two remaining transport
fields.  The two Mellin identities are supplied by proved theorems, so this
constructor introduces no `sorryAx` or historical Nyman--Beurling axiom. -/
def mellinNymanBridgeDebts_of_transport
    (D : NymanBeurlingMellinTransportDebts) : MellinNymanBridgeDebts where
  mellin_chi_eval := BaezDuarte.mellin_chi_eval_proved
  mellin_generator_eval := by
    intro k s hsright hslt hsne
    exact BaezDuarte.mellin_generator_eval_proved k s (by linarith) hslt hsne
  eval_functional_continuous := D.eval_functional_continuous
  vanishing_transport := D.vanishing_transport

/-- Package the two separately named residual debts into the original bridge
shape used by `RHBridge.lean`. -/
def NymanBeurlingMellinTransportDebts.of_split
    (C : MellinContinuityUnderL2Approx)
    (Z : ZeroTransportToChiHypothesis) :
    NymanBeurlingMellinTransportDebts where
  eval_functional_continuous := C.statement
  vanishing_transport := Z.statement

/-- The forward RH bridge conditional on exactly the residual Mellin transport
debts.  This is the project-facing endpoint for the currently available
Mellin work: the finite criterion conversion and the χ/generator formulas are
fully theorem-level, while the Plancherel/continuity and zero-detection
analysis remains isolated in `NymanBeurlingMellinTransportDebts`. -/
theorem NBForward_of_mellin_transport_debts
    (D : NymanBeurlingMellinTransportDebts) : NBForward := by
  apply NBForward_of_bridgeDebts
  apply NymanBeurlingRHBridgeDebts_of_forward_debt
  exact no_zeros_right_half_of_mellinNymanBridgeDebts
    (mellinNymanBridgeDebts_of_transport D)

/-- Split-debt presentation of the same conditional forward bridge. -/
theorem NBForward_of_split_mellin_transport_debts
    (C : MellinContinuityUnderL2Approx)
    (Z : ZeroTransportToChiHypothesis) : NBForward :=
  NBForward_of_mellin_transport_debts
    (NymanBeurlingMellinTransportDebts.of_split C Z)

end RH.Criteria.NymanBeurling.RHBridge
