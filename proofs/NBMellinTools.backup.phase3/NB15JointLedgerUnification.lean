/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB8LogTaperTarget
import NBMellinTools.NB12BBLSH15PostFECompleteHarmonicNormalForm

/-!
# NB15 exploration: exact parameterized PostFE energy specialization

This module is deliberately not imported by the public `NBMellinTools`
umbrella.  It replaces the former one-variable placeholder components by
literal aliases of the verified NB12 expressions.

For fixed PostFE parameters the exact identity is

`actual varying-row energy = norm imbalance + 2 * (constant + static + harmonic)`.

The NB12 energy is local to a frequency support and to the parameters
`n`, `g`, `U`, `Q`, and `t`.  The active package does not currently prove
that a sequence of these local energies is the NB8 certified log-taper error.
That missing global assembly is therefore represented below by the explicit
predicate `IsNymanBeurlingEnergySpecialization`; it is not asserted.
-/

open Filter Topology

namespace NBMellinTools.NB15

/-- The full set of parameters on which the verified NB12 PostFE energy
depends.  Positivity of `Q` is retained because the exact NB12 normal form
uses the common-superperiod construction. -/
structure PostFEParameters where
  frequencySupport : Finset ℕ
  n : ℕ
  g : ℕ
  U : ℕ
  Q : ℕ
  t : ℝ
  cutoff_pos : 0 < Q

/-- Exact NB12 affine norm-imbalance component. -/
noncomputable def affineNormImbalanceDefect
    (P : PostFEParameters) : ℝ :=
  NB12.h15PostFEAffineNormImbalanceDefect
    P.frequencySupport P.n P.g P.U P.Q P.t

/-- Exact signed NB12 constant-mode component.

This is the constant diagonal balance, not its absolute `L¹` budget. -/
noncomputable def endpointConstantMode
    (P : PostFEParameters) : ℝ :=
  NB12.h15PostFEWeightedConstantDiagonalBalance
    P.frequencySupport P.n P.g P.U P.Q P.t

/-- Exact signed NB12 static non-diagonal collision component. -/
noncomputable def staticNonDiagonalCollisionGap
    (P : PostFEParameters) : ℝ :=
  NB12.h15PostFECompleteStaticNondiagonalGap
    P.frequencySupport P.n P.g P.U P.Q P.t

/-- Exact signed NB12 combined harmonic component. -/
noncomputable def completeCombinedHarmonicLedger
    (P : PostFEParameters) : ℝ :=
  NB12.h15PostFECompleteCombinedHarmonicLedger
    P.frequencySupport P.n P.g P.U P.Q P.t

/-- The correction-preserving four-component normal form.

The factor `2` and the grouping of the three signed ledgers are essential;
replacing this expression by a sum of four nonnegative majorants would lose
the cancellation proved by the NB12 algebra. -/
noncomputable def jointResidualEnergy (P : PostFEParameters) : ℝ :=
  affineNormImbalanceDefect P +
    2 *
      (endpointConstantMode P +
        staticNonDiagonalCollisionGap P +
        completeCombinedHarmonicLedger P)

/-- Unconditional exact identification of the corrected four-component
normal form with the verified NB12 varying-row energy. -/
theorem jointResidualEnergy_eq_actualVaryingRowEnergy
    (P : PostFEParameters) :
    jointResidualEnergy P =
      NB12.h15PostFEActualVaryingRowEnergy
        P.frequencySupport P.n P.g P.U P.Q P.t := by
  unfold jointResidualEnergy affineNormImbalanceDefect endpointConstantMode
    staticNonDiagonalCollisionGap completeCombinedHarmonicLedger
  exact
    (NB12.h15PostFEActualVaryingRowEnergy_eq_normImbalance_add_constant_static_harmonic
      P.frequencySupport P.n P.g P.U P.Q P.t P.cutoff_pos).symm

/-- The exact global bridge that a PostFE parameter family must satisfy in
order to represent the certified NB8 log-taper energy.

This predicate is intentionally not inhabited here: constructing such a
family from the complete H15 transformation is a remaining algebraic/global
assembly problem. -/
def IsNymanBeurlingEnergySpecialization
    (parameters : ℕ → PostFEParameters) : Prop :=
  ∀ stage : ℕ,
    NB12.h15PostFEActualVaryingRowEnergy
        (parameters stage).frequencySupport
        (parameters stage).n
        (parameters stage).g
        (parameters stage).U
        (parameters stage).Q
        (parameters stage).t =
      NB8.logTaperL2Error stage

/-- Under the exact specialization certificate, the four-component residual
is pointwise equal to the certified Nyman--Beurling log-taper energy. -/
theorem jointResidualEnergy_eq_logTaperL2Error
    {parameters : ℕ → PostFEParameters}
    (H : IsNymanBeurlingEnergySpecialization parameters)
    (stage : ℕ) :
    jointResidualEnergy (parameters stage) =
      NB8.logTaperL2Error stage := by
  rw [jointResidualEnergy_eq_actualVaryingRowEnergy]
  exact H stage

/-- The specialization certificate transports residual decay to the exact
NB8 log-taper decay statement. -/
theorem logTaperL2Decay_of_jointResidualEnergy
    {parameters : ℕ → PostFEParameters}
    (H : IsNymanBeurlingEnergySpecialization parameters)
    (hdecay :
      Tendsto (fun stage => jointResidualEnergy (parameters stage))
        atTop (nhds 0)) :
    NB8.LogTaperL2Decay := by
  unfold NB8.LogTaperL2Decay
  apply hdecay.congr'
  exact Eventually.of_forall fun stage =>
    jointResidualEnergy_eq_logTaperL2Error H stage

/-- Honest conditional endpoint: an exact global specialization together
with decay of its correction-preserving residual implies RH through the
already certified NB8 route. -/
theorem riemannHypothesis_of_jointResidualEnergy
    {parameters : ℕ → PostFEParameters}
    (H : IsNymanBeurlingEnergySpecialization parameters)
    (hdecay :
      Tendsto (fun stage => jointResidualEnergy (parameters stage))
        atTop (nhds 0)) :
    RiemannHypothesis :=
  NB8.riemannHypothesis_of_logTaperL2Decay
    (logTaperL2Decay_of_jointResidualEnergy H hdecay)

end NBMellinTools.NB15
