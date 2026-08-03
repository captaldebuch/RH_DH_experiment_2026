import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart

/-!
# Route C: a certified central diagonal

The period finite-part passage is known at every fixed H15 cutoff, but it is
not uniform in that cutoff.  This module records the strongest unconditional
selection consequence: after fixing the cited rational reciprocity package,
there is a strictly cofinal sequence of punctured central parameters along
which the analytic period-plus-dual aggregate differs from the exact central
target by a null sequence.

This is a diagonal theorem, not an interchange of limits.  The selected
parameter may approach zero arbitrarily quickly as the cutoff grows.  Thus
the final signed decay remains exactly as hard as decay of the central H15
target; the last theorem below makes that equivalence explicit.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal

open Complex Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart

/-- A fixed explicit sequence approaching the central parameter through the
punctured complex plane. -/
noncomputable def routeCCentralProbe (m : ℕ) : ℂ :=
  1 / ((m : ℂ) + 1)

theorem routeCCentralProbe_ne_zero (m : ℕ) :
    routeCCentralProbe m ≠ 0 := by
  unfold routeCCentralProbe
  exact one_div_ne_zero (by exact_mod_cast Nat.succ_ne_zero m)

theorem routeCCentralProbe_tendsto_zero :
    Tendsto routeCCentralProbe atTop (nhds 0) := by
  unfold routeCCentralProbe
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem routeCCentralProbe_tendsto_punctured_zero :
    Tendsto routeCCentralProbe atTop (nhdsWithin 0 {0}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨routeCCentralProbe_tendsto_zero,
    Eventually.of_forall fun m => by
      simpa using routeCCentralProbe_ne_zero m⟩

/-- The exact central expression identified by the fixed-cutoff Laurent
passage. -/
noncomputable def routeCCentralFinitePartTarget (N : ℕ) : ℂ :=
  ((routeCInteriorCentralCotangentAggregate N -
    routeCInteriorCentralFinitePartAggregate N : ℝ) : ℂ)

/-- Along the explicit probe, every fixed cutoff converges to the exact
central target. -/
theorem tendsto_routeCInteriorPeriodDual_along_probe
    (H : AuliBettinConreyRationalReciprocityPackage) (N : ℕ) :
    Tendsto (fun m : ℕ =>
        routeCInteriorRenormalizedPeriodDualAggregate H
          (routeCCentralProbe m) N)
      atTop (nhds (routeCCentralFinitePartTarget N)) := by
  exact (tendsto_routeCInteriorRenormalizedPeriodDualAggregate_zero H N).comp
    routeCCentralProbe_tendsto_punctured_zero

/-- A selected cofinal probe index whose analytic aggregate approximates the
central H15 target asymptotically. -/
structure RouteCPeriodDiagonalData
    (H : AuliBettinConreyRationalReciprocityPackage) where
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  approximation : Tendsto (fun N : ℕ =>
      routeCInteriorRenormalizedPeriodDualAggregate H
          (routeCCentralProbe (index N)) N -
        routeCCentralFinitePartTarget N)
    atTop (nhds 0)

/-- A diagonal exists by applying the fixed-cutoff limit with tolerance
`1/(N+1)` and then taking a strictly increasing extraction. -/
theorem exists_routeCPeriodDiagonalData
    (H : AuliBettinConreyRationalReciprocityPackage) :
    Nonempty (RouteCPeriodDiagonalData H) := by
  have hrow : ∀ N : ℕ, Tendsto (fun m : ℕ =>
      routeCInteriorRenormalizedPeriodDualAggregate H
          (routeCCentralProbe m) N -
        routeCCentralFinitePartTarget N) atTop (nhds 0) := by
    intro N
    have h := (tendsto_routeCInteriorPeriodDual_along_probe H N).sub
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => routeCCentralFinitePartTarget N)
        atTop (nhds (routeCCentralFinitePartTarget N)))
    simpa using h
  have hselect : ∀ N : ℕ, ∀ᶠ m in atTop,
      ‖routeCInteriorRenormalizedPeriodDualAggregate H
          (routeCCentralProbe m) N -
        routeCCentralFinitePartTarget N‖ < 1 / ((N : ℝ) + 1) := by
    intro N
    have htol : 0 < 1 / ((N : ℝ) + 1) := by positivity
    simpa [dist_zero_right] using
      (Metric.tendsto_nhds.mp (hrow N) _ htol)
  obtain ⟨index, hindex, hbound⟩ :=
    extraction_forall_of_eventually hselect
  refine ⟨⟨index, hindex, ?_⟩⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hslack : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hevent := Metric.tendsto_nhds.mp hslack ε hε
  filter_upwards [hevent] with N hN
  have hslack_lt : 1 / ((N : ℝ) + 1) < ε := by
    have hN' : |1 / ((N : ℝ) + 1)| < ε := by
      simpa [Real.dist_eq] using hN
    rw [abs_of_pos (by positivity : 0 < 1 / ((N : ℝ) + 1))] at hN'
    exact hN'
  simpa [dist_zero_right] using (hbound N).trans hslack_lt

noncomputable def RouteCPeriodDiagonalData.parameter
    {H : AuliBettinConreyRationalReciprocityPackage}
    (D : RouteCPeriodDiagonalData H) (N : ℕ) : ℂ :=
  routeCCentralProbe (D.index N)

theorem RouteCPeriodDiagonalData.parameter_ne_zero
    {H : AuliBettinConreyRationalReciprocityPackage}
    (D : RouteCPeriodDiagonalData H) (N : ℕ) :
    D.parameter N ≠ 0 :=
  routeCCentralProbe_ne_zero _

theorem RouteCPeriodDiagonalData.parameter_tendsto_zero
    {H : AuliBettinConreyRationalReciprocityPackage}
    (D : RouteCPeriodDiagonalData H) :
    Tendsto D.parameter atTop (nhds 0) := by
  exact routeCCentralProbe_tendsto_zero.comp D.index_strictMono.tendsto_atTop

theorem RouteCPeriodDiagonalData.parameter_tendsto_punctured_zero
    {H : AuliBettinConreyRationalReciprocityPackage}
    (D : RouteCPeriodDiagonalData H) :
    Tendsto D.parameter atTop (nhdsWithin 0 {0}ᶜ) := by
  exact routeCCentralProbe_tendsto_punctured_zero.comp
    D.index_strictMono.tendsto_atTop

noncomputable def RouteCPeriodDiagonalData.analyticValue
    {H : AuliBettinConreyRationalReciprocityPackage}
    (D : RouteCPeriodDiagonalData H) (N : ℕ) : ℂ :=
  routeCInteriorRenormalizedPeriodDualAggregate H (D.parameter N) N

/-- Decay of the selected analytic period-plus-dual expression is equivalent,
not merely sufficient, to decay of the exact central H15 target.  The
diagonal selection therefore removes no part of the RH-strength problem. -/
theorem RouteCPeriodDiagonalData.analytic_tendsto_zero_iff_target
    {H : AuliBettinConreyRationalReciprocityPackage}
    (D : RouteCPeriodDiagonalData H) :
    Tendsto D.analyticValue atTop (nhds 0) ↔
      Tendsto routeCCentralFinitePartTarget atTop (nhds 0) := by
  have happ : Tendsto (fun N : ℕ =>
      D.analyticValue N - routeCCentralFinitePartTarget N)
      atTop (nhds 0) := by
    simpa [RouteCPeriodDiagonalData.analyticValue,
      RouteCPeriodDiagonalData.parameter] using D.approximation
  constructor
  · intro hanalytic
    have h := hanalytic.sub happ
    convert h using 1
    · funext N
      ring
    · ring
  · intro htarget
    have h := happ.add htarget
    convert h using 1
    · funext N
      ring
    · ring

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
