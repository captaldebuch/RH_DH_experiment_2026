import Mathlib
import RiemannHypothesis.HardySpace.BlaschkeFactor

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RiemannHypothesis.HardySpace

/-- Infinite Blaschke product B(z) = ∏ (conj a_n / |a_n|) * (a_n - z)/(1 - conj a_n * z). -/
def BlaschkeProduct (seq : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n, blaschkeFactor (seq n) z

end RiemannHypothesis.HardySpace
