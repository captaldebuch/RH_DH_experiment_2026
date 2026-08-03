import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmFourierBridge
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCoefficientConvergence

/-!
# Reduction of concrete Ehm `L²` convergence to finite Fourier algebra

The analytic tail estimate is proved in
`BCFLogTaperEhmCoefficientConvergence`.  This module shows that the concrete
finite centered-sawtooth functions converge as soon as their Fourier
coefficients are identified with the corresponding divisor-truncated
vectors.  Thus the remaining Week-1 obligation is finite harmonic analysis,
not an asymptotic estimate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmL2Convergence

open Filter MeasureTheory AddCircle
open scoped Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPeriodicL2
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoefficientConvergence

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The exact finite Fourier-algebra statement still needed to identify the
concrete centered-sawtooth partial sums with the coefficient synthesis. -/
structure EhmFiniteSawtoothFourierIdentification : Prop where
  coefficient : ∀ K : ℕ, ∀ m : ℤ,
    fourierCoeff (ehmPhi1PartialL2 K) m =
      ehmPhi1PartialComplexFourierCoefficient K m

theorem ehmPhi1PartialL2_eq_coefficientPartial
    (H : EhmFiniteSawtoothFourierIdentification) (K : ℕ) :
    ehmPhi1PartialL2 K = ehmPhi1CoefficientPartialL2 K := by
  apply (@fourierBasis 1 inferInstance).repr.injective
  ext m
  rw [fourierBasis_repr, fourierBasis_repr,
    H.coefficient K m,
    ehmPhi1CoefficientPartialL2_fourierCoefficient]

/-- Concrete `L²` convergence follows from the finite dilation/coefficient
identity and the already-proved divisor-square tail estimate. -/
theorem ehmPhi1L2Convergence
    (H : EhmFiniteSawtoothFourierIdentification) :
    Tendsto ehmPhi1PartialL2 atTop (nhds periodicEhmKernelL2) := by
  apply ehmPhi1CoefficientPartialL2_tendsto.congr'
  exact Eventually.of_forall fun K =>
    (ehmPhi1PartialL2_eq_coefficientPartial H K).symm

/-- Packaged form consumed by the Fourier bridge. -/
noncomputable def ehmPhi1L2ConvergenceData
    (H : EhmFiniteSawtoothFourierIdentification) :
    EhmPhi1L2Convergence where
  tendsto_periodic := ehmPhi1L2Convergence H

end RH.Criteria.NymanBeurling.BCFLogTaperEhmL2Convergence
