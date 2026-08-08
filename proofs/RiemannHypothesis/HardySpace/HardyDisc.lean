import Mathlib

open Complex Real MeasureTheory Set Filter Topology InnerProductSpace

noncomputable section

namespace RiemannHypothesis.HardySpace

/-- Hardy space H²(𝔻) of analytic functions on the unit disc with square-integrable boundary values. -/
def HardyDisc : Type :=
  { f : ℂ → ℂ // AnalyticOn ℂ f (Metric.ball 0 1) ∧ ∃ C, ∀ r ∈ Ioo (0:ℝ) 1, ∫ θ in Ioc (0:ℝ) (2*π), ‖f (r * exp (I * θ))‖^2 ≤ C }

/-- Inner function definition on H²(𝔻). -/
def IsInnerDisc (f : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f (Metric.ball 0 1) ∧ ∀ᵐ θ, ‖f (exp (I * θ))‖ = 1

/-- Outer function definition on H²(𝔻). -/
def IsOuterDisc (g : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ g (Metric.ball 0 1) ∧ ∀ z ∈ Metric.ball (0:ℂ) 1, g z ≠ 0

end RiemannHypothesis.HardySpace
