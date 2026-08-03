import RiemannHypothesis.Criteria.NymanBeurling.H14ZeroFree

/-!
# H14 Borel--Jensen interface audit

Mathlib already contains the generic Borel--Carathéodory theorem and Jensen's
formula.  This file packages the part that can be specialized to ζ without a
new analytic axiom: once a closed disc avoids the pole at `1`, a center value
is nonzero, and an outer-circle bound is supplied, Mathlib gives the Jensen
zero-count estimate directly.

The remaining H14 obstruction is not Jensen's identity itself.  It is the
quantitative zeta-specific construction of a logarithm/factorization on the
height-dependent disc and the resulting log-derivative bound.  Those inputs
remain represented by `ZetaBorelJensenFactorizationAtHeight` in `H14ZeroFree`.
-/

namespace RH.Criteria.NymanBeurling.MobiusSummatory

open Complex Metric Set Filter MeromorphicAt MeasureTheory MeromorphicOn Real Topology

/-- Data needed to apply Mathlib's Jensen zero-count estimate to ζ on one
closed disc.  The pole-avoidance field supplies the analytic hypothesis; the
outer-circle bound is deliberately an explicit input rather than a claimed
consequence of the current vertical-growth package. -/
structure ZetaJensenDiscInput where
  center : ℂ
  innerRadius : ℝ
  outerRadius : ℝ
  bound : ℝ
  innerRadius_pos : 0 < |innerRadius|
  inner_lt_outer : |innerRadius| < |outerRadius|
  bound_ge_one : 1 ≤ bound
  disc_avoids_pole : closedBall center |outerRadius| ⊆ {1}ᶜ
  center_nonzero : riemannZeta center ≠ 0
  outer_bound : ∀ z ∈ sphere center |outerRadius|, ‖riemannZeta z‖ ≤ bound

/-- Jensen's inequality for the ζ zeros in the inner disc.  This is a real
result using Mathlib's `AnalyticOnNhd.sum_divisor_le`; no zeta zero-counting
or factorization axiom is introduced. -/
theorem zeta_jensen_disc_zero_count
    (H : ZetaJensenDiscInput) :
    (↑(∑ᶠ u, MeromorphicOn.divisor
      riemannZeta (closedBall H.center |H.innerRadius|) u) : ℝ) ≤
      Real.log (H.bound / ‖riemannZeta H.center‖) /
        Real.log (H.outerRadius / H.innerRadius) := by
  exact AnalyticOnNhd.sum_divisor_le
    H.innerRadius_pos H.inner_lt_outer H.bound_ge_one
    (analyticOn_riemannZeta.mono H.disc_avoids_pole)
    H.center_nonzero H.outer_bound

/-- The exact residual needed by Mathlib's canonical finite-zero factorization
on a zeta disc.  The two finiteness fields are isolated explicitly because
establishing them uniformly for the height-dependent H14 discs is part of the
remaining zeta-specific work. -/
structure ZetaDiscFactorizationInput where
  center : ℂ
  radius : ℝ
  disc_avoids_pole : closedBall center |radius| ⊆ {1}ᶜ
  orders_finite :
    ∀ u : (closedBall center |radius|),
      meromorphicOrderAt riemannZeta (u : ℂ) ≠ ⊤
  divisor_support_finite :
    (MeromorphicOn.divisor riemannZeta (closedBall center |radius|)).support.Finite

/-- Mathlib's canonical decomposition supplies an analytic nonvanishing factor
and the finite divisor product, with equality on the codiscrete set where the
meromorphic normal form is defined. -/
theorem zeta_extract_zeros_poles_on_disc
    (H : ZetaDiscFactorizationInput) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (closedBall H.center |H.radius|) ∧
        (∀ u : (closedBall H.center |H.radius|), g (u : ℂ) ≠ 0) ∧
        riemannZeta =ᶠ[codiscreteWithin (closedBall H.center |H.radius|)]
          (∏ᶠ u : ℂ,
            (fun z => z - u) ^
              (MeromorphicOn.divisor riemannZeta
                (closedBall H.center |H.radius|) u)) • g := by
  have hmeromorphic :
      MeromorphicOn riemannZeta (closedBall H.center |H.radius|) :=
    (analyticOn_riemannZeta.mono H.disc_avoids_pole).meromorphicOn
  exact hmeromorphic.extract_zeros_poles
    H.orders_finite H.divisor_support_finite

/-- A direct reusable wrapper for the generic Borel--Carathéodory estimate.
The theorem is stated with an arbitrary analytic function because the missing
H14 step is the zeta-specific choice of a holomorphic logarithm, not the
real-part-to-norm inequality itself. -/
theorem borelCaratheodory_norm_bound
    {f : ℂ → ℂ} {R M : ℝ} {z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : MapsTo f (ball 0 R) {w | w.re ≤ M})
    (hR : 0 < R) (hz : z ∈ ball 0 R) :
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) +
      ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by
  exact Complex.borelCaratheodory hM hf hf₁ hR hz

end RH.Criteria.NymanBeurling.MobiusSummatory
