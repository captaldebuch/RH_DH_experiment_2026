import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal

/-!
# Route C: central windows and the quantitative uniformity gate

The fixed-cutoff period-function theorem gives a punctured neighborhood of
the central parameter on which the analytic period-plus-dual aggregate is
close to the exact central target.  This module selects one such radius for
every cutoff and shrinks it by `1/(N+1)`.  Consequently the radii themselves
tend to zero and the approximation error is uniformly below `1/(N+1)` inside
the selected window.

This is still a qualitative diagonal construction: the selected radii can
shrink arbitrarily quickly.  `RouteCPolynomialWindowCertificate` isolates the
genuinely stronger input needed for an explicit polynomial central path.  No
inhabitant of that certificate is asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCUniformCentralWindow

open Complex Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal

/-- The null tolerance used to select the `N`-th central window. -/
noncomputable def routeCCentralWindowSlack (N : ℕ) : ℝ :=
  1 / ((N : ℝ) + 1)

theorem routeCCentralWindowSlack_pos (N : ℕ) :
    0 < routeCCentralWindowSlack N := by
  unfold routeCCentralWindowSlack
  positivity

theorem routeCCentralWindowSlack_tendsto_zero :
    Tendsto routeCCentralWindowSlack atTop (nhds 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- A punctured central window at every cutoff, with an explicit null error
majorant.  The radius is not assumed to have any quantitative lower bound. -/
structure RouteCCentralWindowData
    (H : AuliBettinConreyRationalReciprocityPackage) where
  radius : ℕ → ℝ
  radius_pos : ∀ N, 0 < radius N
  radius_tendsto_zero : Tendsto radius atTop (nhds 0)
  approximation_bound : ∀ (N : ℕ) (z : ℂ), z ≠ 0 → ‖z‖ < radius N →
    ‖routeCInteriorRenormalizedPeriodDualAggregate H z N -
        routeCCentralFinitePartTarget N‖ < routeCCentralWindowSlack N

/-- Fixed-cutoff convergence produces a full punctured window at every
cutoff.  Shrinking the local radius by `1/(N+1)` makes the chosen radii a null
sequence without claiming any lower bound on them. -/
theorem exists_routeCCentralWindowData
    (H : AuliBettinConreyRationalReciprocityPackage) :
    Nonempty (RouteCCentralWindowData H) := by
  have hlocal : ∀ N : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ,
      z ≠ 0 → dist z 0 < δ →
        dist (routeCInteriorRenormalizedPeriodDualAggregate H z N)
          (routeCCentralFinitePartTarget N) < routeCCentralWindowSlack N := by
    intro N
    have hlimit : Tendsto
        (fun z : ℂ => routeCInteriorRenormalizedPeriodDualAggregate H z N)
        (nhdsWithin 0 {0}ᶜ) (nhds (routeCCentralFinitePartTarget N)) := by
      simpa [routeCCentralFinitePartTarget] using
        tendsto_routeCInteriorRenormalizedPeriodDualAggregate_zero H N
    obtain ⟨δ, hδ, hbound⟩ :=
      (Metric.tendsto_nhdsWithin_nhds.mp hlimit)
        (routeCCentralWindowSlack N) (routeCCentralWindowSlack_pos N)
    refine ⟨δ, hδ, ?_⟩
    intro z hz hdist
    exact hbound (by simpa using hz) hdist
  choose raw hraw_pos hraw_bound using hlocal
  let radius : ℕ → ℝ := fun N => min (raw N) (routeCCentralWindowSlack N)
  have hradius_pos : ∀ N, 0 < radius N := by
    intro N
    exact lt_min (hraw_pos N) (routeCCentralWindowSlack_pos N)
  have hradius_zero : Tendsto radius atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hevent := Metric.tendsto_nhds.mp
      routeCCentralWindowSlack_tendsto_zero ε hε
    filter_upwards [hevent] with N hN
    have hslack_lt : routeCCentralWindowSlack N < ε := by
      have habs : |routeCCentralWindowSlack N| < ε := by
        simpa [Real.dist_eq] using hN
      rwa [abs_of_pos (routeCCentralWindowSlack_pos N)] at habs
    have hradius_lt : radius N < ε :=
      (min_le_right (raw N) (routeCCentralWindowSlack N)).trans_lt hslack_lt
    simpa [Real.dist_eq, abs_of_pos (hradius_pos N)] using hradius_lt
  refine ⟨⟨radius, hradius_pos, hradius_zero, ?_⟩⟩
  intro N z hz hznorm
  have hdist : dist z 0 < raw N := by
    simpa [dist_zero_right] using
      hznorm.trans_le (min_le_left (raw N) (routeCCentralWindowSlack N))
  simpa [dist_eq_norm] using hraw_bound N z hz hdist

/-- A path through a selected central window. -/
structure RouteCCentralWindowPath
    {H : AuliBettinConreyRationalReciprocityPackage}
    (W : RouteCCentralWindowData H) where
  parameter : ℕ → ℂ
  parameter_ne_zero : ∀ N, parameter N ≠ 0
  eventually_inside : ∀ᶠ N in atTop, ‖parameter N‖ < W.radius N

theorem RouteCCentralWindowPath.parameter_tendsto_zero
    {H : AuliBettinConreyRationalReciprocityPackage}
    {W : RouteCCentralWindowData H} (P : RouteCCentralWindowPath W) :
    Tendsto P.parameter atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hevent := Metric.tendsto_nhds.mp W.radius_tendsto_zero ε hε
  filter_upwards [P.eventually_inside, hevent] with N hinside hradius
  have hradius_lt : W.radius N < ε := by
    have habs : |W.radius N| < ε := by
      simpa [Real.dist_eq] using hradius
    rwa [abs_of_pos (W.radius_pos N)] at habs
  simpa [dist_zero_right] using hinside.trans hradius_lt

/-- Every path inside the selected windows approximates the exact central
target by a null sequence. -/
theorem RouteCCentralWindowPath.approximation_tendsto_zero
    {H : AuliBettinConreyRationalReciprocityPackage}
    {W : RouteCCentralWindowData H} (P : RouteCCentralWindowPath W) :
    Tendsto (fun N : ℕ =>
      routeCInteriorRenormalizedPeriodDualAggregate H (P.parameter N) N -
        routeCCentralFinitePartTarget N) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hevent := Metric.tendsto_nhds.mp
    routeCCentralWindowSlack_tendsto_zero ε hε
  filter_upwards [P.eventually_inside, hevent] with N hinside hslack
  have hslack_lt : routeCCentralWindowSlack N < ε := by
    have habs : |routeCCentralWindowSlack N| < ε := by
      simpa [Real.dist_eq] using hslack
    rwa [abs_of_pos (routeCCentralWindowSlack_pos N)] at habs
  simpa [dist_zero_right] using
    (W.approximation_bound N (P.parameter N) (P.parameter_ne_zero N) hinside).trans
      hslack_lt

noncomputable def RouteCCentralWindowPath.analyticValue
    {H : AuliBettinConreyRationalReciprocityPackage}
    {W : RouteCCentralWindowData H} (P : RouteCCentralWindowPath W)
    (N : ℕ) : ℂ :=
  routeCInteriorRenormalizedPeriodDualAggregate H (P.parameter N) N

/-- Window control transfers decay in both directions.  Thus even a usable
uniform window does not replace the final signed central estimate. -/
theorem RouteCCentralWindowPath.analytic_tendsto_zero_iff_target
    {H : AuliBettinConreyRationalReciprocityPackage}
    {W : RouteCCentralWindowData H} (P : RouteCCentralWindowPath W) :
    Tendsto P.analyticValue atTop (nhds 0) ↔
      Tendsto routeCCentralFinitePartTarget atTop (nhds 0) := by
  have happ : Tendsto (fun N : ℕ =>
      P.analyticValue N - routeCCentralFinitePartTarget N)
      atTop (nhds 0) := by
    simpa [RouteCCentralWindowPath.analyticValue] using
      P.approximation_tendsto_zero
  constructor
  · intro hanalytic
    have h := hanalytic.sub happ
    convert h using 1
    · funext N
      abel
    · abel
  · intro htarget
    have h := happ.add htarget
    convert h using 1
    · funext N
      abel
    · abel

/-- The genuinely quantitative uniformity requested by Route C: the selected
central windows contain a polynomial-size punctured disk.  The qualitative
fixed-cutoff theorem does not construct this certificate. -/
structure RouteCPolynomialWindowCertificate
    {H : AuliBettinConreyRationalReciprocityPackage}
    (W : RouteCCentralWindowData H) where
  exponent : ℕ
  exponent_pos : 0 < exponent
  radius_lower : ∀ N : ℕ,
    1 / (((N : ℝ) + 2) ^ exponent) ≤ W.radius N

/-- An explicit polynomial path lying halfway inside a certified polynomial
window. -/
noncomputable def RouteCPolynomialWindowCertificate.parameter
    {H : AuliBettinConreyRationalReciprocityPackage}
    {W : RouteCCentralWindowData H} (Q : RouteCPolynomialWindowCertificate W)
    (N : ℕ) : ℂ :=
  (((1 / 2 : ℝ) * (1 / (((N : ℝ) + 2) ^ Q.exponent)) : ℝ) : ℂ)

theorem RouteCPolynomialWindowCertificate.parameter_ne_zero
    {H : AuliBettinConreyRationalReciprocityPackage}
    {W : RouteCCentralWindowData H} (Q : RouteCPolynomialWindowCertificate W)
    (N : ℕ) : Q.parameter N ≠ 0 := by
  unfold RouteCPolynomialWindowCertificate.parameter
  rw [Complex.ofReal_ne_zero]
  exact mul_ne_zero (by norm_num : (1 / 2 : ℝ) ≠ 0)
    (one_div_ne_zero (ne_of_gt (pow_pos (by positivity) Q.exponent)))

theorem RouteCPolynomialWindowCertificate.parameter_inside
    {H : AuliBettinConreyRationalReciprocityPackage}
    {W : RouteCCentralWindowData H} (Q : RouteCPolynomialWindowCertificate W)
    (N : ℕ) : ‖Q.parameter N‖ < W.radius N := by
  have hbase : 0 < 1 / (((N : ℝ) + 2) ^ Q.exponent) := by positivity
  have hparameter : 0 < (1 / 2 : ℝ) *
      (1 / (((N : ℝ) + 2) ^ Q.exponent)) :=
    mul_pos (by norm_num) hbase
  calc
    ‖Q.parameter N‖ = (1 / 2 : ℝ) *
        (1 / (((N : ℝ) + 2) ^ Q.exponent)) := by
          rw [show Q.parameter N = (((1 / 2 : ℝ) *
            (1 / (((N : ℝ) + 2) ^ Q.exponent)) : ℝ) : ℂ) by rfl,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos hparameter]
    _ < 1 / (((N : ℝ) + 2) ^ Q.exponent) := by linarith
    _ ≤ W.radius N := Q.radius_lower N

noncomputable def RouteCPolynomialWindowCertificate.toPath
    {H : AuliBettinConreyRationalReciprocityPackage}
    {W : RouteCCentralWindowData H} (Q : RouteCPolynomialWindowCertificate W) :
    RouteCCentralWindowPath W where
  parameter := Q.parameter
  parameter_ne_zero := Q.parameter_ne_zero
  eventually_inside := Eventually.of_forall Q.parameter_inside

/-- The polynomial-window hypothesis gives an explicit analytic path, but
decay along it is still exactly equivalent to decay of the central target. -/
theorem RouteCPolynomialWindowCertificate.analytic_tendsto_zero_iff_target
    {H : AuliBettinConreyRationalReciprocityPackage}
    {W : RouteCCentralWindowData H} (Q : RouteCPolynomialWindowCertificate W) :
    Tendsto Q.toPath.analyticValue atTop (nhds 0) ↔
      Tendsto routeCCentralFinitePartTarget atTop (nhds 0) :=
  Q.toPath.analytic_tendsto_zero_iff_target

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCUniformCentralWindow
