import RiemannHypothesis.Criteria.NymanBeurling.BaezDuarte

/-!
# Phase NB0 — structural Nyman--Beurling/RH bridge debts

This file separates the forward Nyman--Beurling implication into the two
mathematical debts that remain after the finite Báez--Duarte reduction.  The
first debt is the analytic implication from the approximation criterion to
zero-freeness in the right half of the critical strip.  The second is the
elementary symmetry step from that zero-free half-strip to RH; it is proved
here using the existing functional-equation symmetry axiom.

The Mellin structure below freezes the next analytic attack surface without
asserting any of its fields.  Its statements use the actual functions in
`BaezDuarte.lean`, including the zero-based `rhoBD` index used by `bdApprox`.
-/

namespace RH.Criteria.NymanBeurling.RHBridge

open scoped BigOperators

open RH.Criteria.NymanBeurling.BaezDuarte

/-- The forward Nyman--Beurling implication needed for the RH pipeline. -/
def NBForward : Prop :=
  NymanBeurlingCriterion → RH.Basic.RiemannHypothesis

/-! ## NB0-b: the two-debt bridge -/

/-- The two analytic implications underlying the forward Nyman--Beurling
bridge.  The second field is discharged below from `zero_symmetry`. -/
structure NymanBeurlingRHBridgeDebts where
  nyman_implies_no_zeros_right_half :
    NymanBeurlingCriterion →
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0
  no_zeros_right_half_implies_RH :
    (∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0) →
      RH.Basic.RiemannHypothesis

/-- Mechanical composition of the two bridge debts into `NBForward`. -/
theorem NBForward_of_bridgeDebts (D : NymanBeurlingRHBridgeDebts) : NBForward := by
  intro hcriterion
  exact D.no_zeros_right_half_implies_RH
    (D.nyman_implies_no_zeros_right_half hcriterion)

/-! ## NB0-c: the symmetry half is unconditional relative to `zero_symmetry` -/

/-- If there are no nontrivial zeros in the open right half of the critical
strip, the existing functional-equation symmetry forces every nontrivial zero
onto the critical line. -/
theorem no_zeros_right_half_implies_RH :
    (∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0) →
      RH.Basic.RiemannHypothesis := by
  intro hright s hs
  rcases hs with ⟨hsstrip, hszero⟩
  rcases hsstrip with ⟨hspos, hslt⟩
  unfold RH.Basic.onCriticalLine
  by_contra hneq
  rcases lt_or_gt_of_ne hneq with hsleft | hsright
  · have hsym : RH.Basic.isNontrivialZero (1 - s) :=
      RH.Basic.zero_symmetry s ⟨⟨hspos, hslt⟩, hszero⟩
    have hsymstrip : 1 / 2 < (1 - s).re ∧ (1 - s).re < 1 := by
      constructor
      · norm_num [Complex.sub_re]
        linarith
      · norm_num [Complex.sub_re]
        linarith
    exact (hright (1 - s) hsymstrip.1 hsymstrip.2) hsym.2
  · exact (hright s hsright hslt) hszero

/-- Constructor for the two-debt package when only the analytic forward debt
has been supplied. -/
def NymanBeurlingRHBridgeDebts_of_forward_debt
    (hforward :
      NymanBeurlingCriterion →
        ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0) :
    NymanBeurlingRHBridgeDebts where
  nyman_implies_no_zeros_right_half := hforward
  no_zeros_right_half_implies_RH := no_zeros_right_half_implies_RH

/-! ## NB0-d: Mellin sub-debts -/

/-- The Mellin-transform identities and the closure-to-vanishing estimate
needed by the forward Nyman--Beurling argument.

The generator index is the actual zero-based index of `rhoBD` in `bdApprox`:
the corresponding dilation is `k + 1`.  The last field is deliberately the
transport statement itself; proving it requires the Mellin/Plancherel
analysis, so it remains an explicit content-bearing debt rather than an
axiom or a `sorry` theorem.
-/
structure MellinNymanBridgeDebts where
  mellin_chi_eval :
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → s ≠ 0 →
      mellin (fun x : ℝ => (chi01 x : ℂ)) s = 1 / s
  mellin_generator_eval :
    ∀ (k : ℕ) (s : ℂ), 1 / 2 < s.re → s.re < 1 → s ≠ 0 →
      mellin (fun x : ℝ => (rhoBD k x : ℂ)) s =
        -(riemannZeta s) / (s * ((k + 1 : ℕ) : ℂ) ^ s)
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

/-- The Mellin sub-debts mechanically imply the first RH bridge debt.  The
only analytic content used here is the explicitly stored closure transport;
the generator formula turns a hypothetical zeta zero into vanishing of every
generator transform, while the chi transform is `1/s` and hence nonzero. -/
theorem no_zeros_right_half_of_mellinNymanBridgeDebts
    (D : MellinNymanBridgeDebts) :
    NymanBeurlingCriterion →
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  intro hcriterion s hsright hslt
  intro hszero
  have hsne : s ≠ 0 := by
    intro hs0
    subst hs0
    norm_num at hsright
  have hgens :
      ∀ k : ℕ, mellin (fun x : ℝ => (rhoBD k x : ℂ)) s = 0 := by
    intro k
    rw [D.mellin_generator_eval k s hsright hslt hsne]
    simp [hszero]
  have hchi := D.vanishing_transport s hsright hslt hsne hcriterion hgens
  rw [D.mellin_chi_eval s hsright hslt hsne] at hchi
  exact (one_div_ne_zero hsne) hchi

end RH.Criteria.NymanBeurling.RHBridge
