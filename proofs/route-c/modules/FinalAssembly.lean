import RiemannHypothesis.Criteria.NymanBeurling.QuadraticInteraction
import RiemannHypothesis.Criteria.NymanBeurling.H15CenteredAggregateEstimate
import RiemannHypothesis.Criteria.NymanBeurling.RHBridge

/-!
# Final conditional assembly

This module records the exact endgame wiring without asserting either of the
remaining analytic inputs.  A classical Mertens decay package supplies the
linear estimates, while the corrected centered H15 aggregate supplies the
quadratic estimates.  The Vasyunin local bridge is constructed from the
proved H13 period-reduction chain.  A forward Nyman--Beurling implication then
yields RH.  The aggregate estimate and the forward implication remain
explicit hypotheses, so this theorem does not hide an analytic debt.
-/

namespace RH.Criteria.NymanBeurling.FinalAssembly

open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.MobiusSummatory
open RH.Criteria.NymanBeurling.RHBridge
open RH.Criteria.NymanBeurling.QuadraticInteraction
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The local Vasyunin bridge is now an explicit inhabitant of the corrected
H13 debt structure.  The only nonstandard dependency in this constructor is
the already-documented inverse-substitution bridge used by the diagonal and
tail-integral proofs; no cotangent-recognition `sorryAx` is introduced here. -/
noncomputable def vasyuninBridgeLocalDebts_of_proved_chain :
    VasyuninBridgeLocalDebts :=
  { vasyuninBEntry_symm := vasyuninBEntry_symm_proof
    vasyuninBEntry_diagonal := vasyuninBEntry_diagonal_proof
    interval_sum_add_tail_eq_cotangent_formula := by
      intro h k hne hh hk
      exact interval_sum_add_tail_eq_cotangent_formula_unconditional h k hne hh hk }

/--
The final conditional RH wiring.  The first hypothesis is the single H14
decay input, the second is the centered H15 Bernoulli-correlation estimate,
and the third is the forward Nyman--Beurling implication.  The local
Vasyunin bridge is supplied by `vasyuninBridgeLocalDebts_of_proved_chain`;
no converse Nyman--Beurling implication is used.
-/
theorem riemannHypothesis_of_pair_and_NBforward
    (H_decay : ClassicalMertensDecay)
    (H_pair : QuadraticInteractionBernoulliCorrelationEstimate H_decay)
    (h_forward : NBForward) :
    RH.Basic.RiemannHypothesis := by
  let H_linear : LinearMobiusDirichletEstimates :=
    linear_mobius_dirichlet_estimates_of_classical_api
      (ClassicalMertensAPI.ofDecayOnly H_decay)
  let H_quadratic : QuadraticInteractionEstimates :=
    quadraticInteractionEstimates_of_decay_and_bernoulliCorrelation H_decay H_pair
  have h_baez : BaezDuarteCriterion :=
    baezDuarteCriterion_of_linear_dirichlet_and_quadratic_interaction_estimates
      vasyuninBridgeLocalDebts_of_proved_chain H_linear H_quadratic
  exact h_forward (nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr h_baez)

/--
The official final conditional RH wiring.  Unlike the retired cellwise
interfaces, `H_aggregate` is the exact coupled H15 residual with its specific
cutoff-Möbius weights and its necessary centered cancellations.
-/
theorem riemannHypothesis_of_centeredAggregate_and_NBforward
    (H_decay : ClassicalMertensDecay)
    (H_aggregate : H15CenteredAggregateEstimate)
    (h_forward : NBForward) :
    RH.Basic.RiemannHypothesis := by
  let H_quadratic : QuadraticInteractionEstimates :=
    quadraticInteractionEstimates_of_decay_and_h15CenteredAggregate
      H_decay H_aggregate
  let H_linear : LinearMobiusDirichletEstimates :=
    linear_mobius_dirichlet_estimates_of_classical_api
      (ClassicalMertensAPI.ofDecayOnly H_decay)
  have h_baez : BaezDuarteCriterion :=
    baezDuarteCriterion_of_linear_dirichlet_and_quadratic_interaction_estimates
      vasyuninBridgeLocalDebts_of_proved_chain H_linear H_quadratic
  exact h_forward (nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr h_baez)

end RH.Criteria.NymanBeurling.FinalAssembly
