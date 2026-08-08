/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15CorrectionCoupledAbel

/-!
# NB12zn: status of the H15 coupled variation/boundary decay

This file answers, formally, the question *"does the coupled
variation-plus-boundary aggregate of the H15 branch decay?"*.

The object under discussion is the one already built in
`NB12BBLSH15ActiveIncidence.lean`:

`h15NormalizedProgressionCoupledVariationBoundaryAggregate N g r U Q`.

Three things are proved here.

* **Exact identification.**  The coupled variation/boundary aggregate is
  *equal* (not merely comparable) to the signed square-divisor aggregate
  `h15RamanujanSignedSquareDivisorAggregate`, by chaining the two exact
  identities already in the repository.  Consequently it is not a strictly
  smaller sub-object of the H15 branch: any decay statement about it is a
  decay statement about the whole signed aggregate.

* **What the existing (absolute / divisor-budget) machinery gives.**
  Unconditionally, `|coupled aggregate| ≤ Q/U`, hence `≤ 1` at the balanced
  scale `Q = U`.  That is exponent `0`: no power saving, and *a fortiori* no
  subexponential decay.

* **Exact equivalence with the open gate.**  A power saving for the coupled
  variation/boundary aggregate is equivalent to an inhabitant of
  `H15SignedSquareDivisorPowerSaving`, the open lower-middle gate of the H15
  branch.  Likewise the subexponential ("`exp (-c √log N)`") decay of the
  coupled aggregate is equivalent to the same decay for the signed
  square-divisor aggregate.

Finally, the file records the *interface* lemmas relating the coupled decay
to the Abel interior and correction-coupled Abel boundary decays, so that the
exact identity
`coupled + Abel interior + Abel boundary = pointwise coupled aggregate`
can be used in either direction at the level of decay hypotheses.

No new estimate is asserted: every statement below is either an exact
consequence of an identity already proved in this repository, or an explicit
`Prop`-level equivalence.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius

namespace NBMellinTools.NB12

/-! ## Exact identification of the coupled aggregate -/

/-- The coupled variation/boundary aggregate **is** the signed
square-divisor aggregate.  This chains
`h15RamanujanSignedSquareDivisorAggregate_eq_normalizedProgression` with
`h15NormalizedProgressionAggregate_eq_coupledVariationBoundary`. -/
theorem h15NormalizedProgressionCoupledVariationBoundaryAggregate_eq_signedSquareDivisor
    {N g r U Q : ℕ} (hg : 0 < g) (hU : 0 < U) (hQ : 0 < Q) :
    h15NormalizedProgressionCoupledVariationBoundaryAggregate N g r U Q =
      h15RamanujanSignedSquareDivisorAggregate N g r U Q := by
  rw [h15RamanujanSignedSquareDivisorAggregate_eq_normalizedProgression
      hg hU hQ,
    h15NormalizedProgressionAggregate_eq_coupledVariationBoundary hg hU hQ]

/-! ## What the absolute divisor budget gives for the coupled aggregate -/

/-- The coupled aggregate obeys the same absolute divisor budget as the
signed square-divisor aggregate. -/
theorem abs_h15NormalizedProgressionCoupledVariationBoundaryAggregate_le_budget
    {N g r U Q : ℕ} (hg : 0 < g) (hU : 0 < U) (hQ : 0 < Q) :
    |h15NormalizedProgressionCoupledVariationBoundaryAggregate N g r U Q| ≤
      h15RamanujanSquareDivisorAbsoluteBudget N g r U Q := by
  rw [h15NormalizedProgressionCoupledVariationBoundaryAggregate_eq_signedSquareDivisor
    hg hU hQ]
  exact abs_h15RamanujanSignedSquareDivisorAggregate_le_budget N g r U Q

/-- Unconditional bound obtainable from the existing divisor-growth budget:
`Q/U`.  No cancellation between the variation and the boundary term is used,
and none is gained. -/
theorem abs_h15NormalizedProgressionCoupledVariationBoundaryAggregate_le
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hQ : 0 < Q) :
    |h15NormalizedProgressionCoupledVariationBoundaryAggregate N g r U Q| ≤
      (Q : ℝ) / (U : ℝ) :=
  le_trans
    (abs_h15NormalizedProgressionCoupledVariationBoundaryAggregate_le_budget
      (show 0 < g by omega) hU hQ)
    (h15RamanujanSquareDivisorAbsoluteBudget_le hN hg hU hQ)

/-- At the balanced scale `Q = U` the absolute route yields exactly `1`. -/
theorem abs_h15NormalizedProgressionCoupledVariationBoundaryAggregate_balanced_le
    {N g r U : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) :
    |h15NormalizedProgressionCoupledVariationBoundaryAggregate N g r U U| ≤ 1 := by
  calc
    |h15NormalizedProgressionCoupledVariationBoundaryAggregate N g r U U| ≤
        (U : ℝ) / (U : ℝ) :=
      abs_h15NormalizedProgressionCoupledVariationBoundaryAggregate_le
        hN hg hU hU
    _ = 1 := by field_simp

/-- Balanced exponent supplied by the absolute (divisor-budget) treatment of
the coupled variation/boundary aggregate. -/
noncomputable def h15CoupledVariationBoundaryAbsoluteBalancedExponent : ℝ := 0

/-- The absolute route gives no negative exponent: the coupled
variation/boundary splitting, taken with absolute values, does not by itself
produce decay. -/
theorem h15CoupledVariationBoundaryAbsoluteBalancedExponent_not_neg :
    ¬ h15CoupledVariationBoundaryAbsoluteBalancedExponent < 0 := by
  norm_num [h15CoupledVariationBoundaryAbsoluteBalancedExponent]

/-! ## Power saving for the coupled aggregate is the open H15 gate -/

/-- Power-saving gate stated directly for the coupled variation/boundary
aggregate, in the same normalization as
`H15SignedSquareDivisorPowerSaving`. -/
structure H15CoupledVariationBoundaryPowerSaving where
  C : ℝ
  η : ℝ
  C_nonneg : 0 ≤ C
  η_pos : 0 < η
  bound : ∀ {N g r U Q : ℕ},
    2 ≤ N → 1 ≤ g → 0 < U → 0 < Q → Q ≤ U →
    |h15NormalizedProgressionCoupledVariationBoundaryAggregate N g r U Q| ≤
      C / (U : ℝ) ^ η

/-- A coupled variation/boundary power saving transfers to the signed
square-divisor gate. -/
noncomputable def H15CoupledVariationBoundaryPowerSaving.toSquareDivisor
    (H : H15CoupledVariationBoundaryPowerSaving) :
    H15SignedSquareDivisorPowerSaving where
  C := H.C
  η := H.η
  C_nonneg := H.C_nonneg
  η_pos := H.η_pos
  bound := by
    intro N g r U Q hN hg hU hQ hQU
    rw [← h15NormalizedProgressionCoupledVariationBoundaryAggregate_eq_signedSquareDivisor
      (show 0 < g by omega) hU hQ]
    exact H.bound hN hg hU hQ hQU

/-- Conversely, the signed square-divisor gate gives the coupled
variation/boundary power saving. -/
noncomputable def H15SignedSquareDivisorPowerSaving.toCoupledVariationBoundary
    (H : H15SignedSquareDivisorPowerSaving) :
    H15CoupledVariationBoundaryPowerSaving where
  C := H.C
  η := H.η
  C_nonneg := H.C_nonneg
  η_pos := H.η_pos
  bound := by
    intro N g r U Q hN hg hU hQ hQU
    rw [h15NormalizedProgressionCoupledVariationBoundaryAggregate_eq_signedSquareDivisor
      (show 0 < g by omega) hU hQ]
    exact H.bound hN hg hU hQ hQU

/-- **Exact status of the coupled variation/boundary decay problem.**  It is
neither weaker nor stronger than the open lower-middle H15 gate: the two are
equivalent. -/
theorem nonempty_H15CoupledVariationBoundaryPowerSaving_iff :
    Nonempty H15CoupledVariationBoundaryPowerSaving ↔
      Nonempty H15SignedSquareDivisorPowerSaving :=
  ⟨fun ⟨H⟩ => ⟨H.toSquareDivisor⟩,
    fun ⟨H⟩ => ⟨H.toCoupledVariationBoundary⟩⟩

/-! ## Subexponential decay predicates -/

/-- The H15 target decay rate: `C * exp (-c √(log N))`, uniformly in
`N ≥ 2`. -/
def H15SubexponentialDecay (F : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∃ c > 0, ∀ N : ℕ, 2 ≤ N →
    |F N| ≤ C * Real.exp (-c * Real.sqrt (Real.log (N : ℝ)))

theorem H15SubexponentialDecay.congr {F G : ℕ → ℝ}
    (h : ∀ N : ℕ, 2 ≤ N → F N = G N) (hF : H15SubexponentialDecay F) :
    H15SubexponentialDecay G := by
  obtain ⟨C, hC, c, hc, hbound⟩ := hF
  refine ⟨C, hC, c, hc, ?_⟩
  intro N hN
  rw [← h N hN]
  exact hbound N hN

theorem H15SubexponentialDecay.add {F G : ℕ → ℝ}
    (hF : H15SubexponentialDecay F) (hG : H15SubexponentialDecay G) :
    H15SubexponentialDecay (fun N => F N + G N) := by
  obtain ⟨C₁, hC₁, c₁, hc₁, h₁⟩ := hF
  obtain ⟨C₂, hC₂, c₂, hc₂, h₂⟩ := hG
  refine ⟨C₁ + C₂, by linarith, min c₁ c₂, lt_min hc₁ hc₂, ?_⟩
  intro N hN
  set s : ℝ := Real.sqrt (Real.log (N : ℝ)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have e₁ : Real.exp (-c₁ * s) ≤ Real.exp (-(min c₁ c₂) * s) := by
    apply Real.exp_le_exp.2
    have := min_le_left c₁ c₂
    nlinarith
  have e₂ : Real.exp (-c₂ * s) ≤ Real.exp (-(min c₁ c₂) * s) := by
    apply Real.exp_le_exp.2
    have := min_le_right c₁ c₂
    nlinarith
  calc
    |F N + G N| ≤ |F N| + |G N| := abs_add_le _ _
    _ ≤ C₁ * Real.exp (-c₁ * s) + C₂ * Real.exp (-c₂ * s) :=
      add_le_add (h₁ N hN) (h₂ N hN)
    _ ≤ C₁ * Real.exp (-(min c₁ c₂) * s) +
        C₂ * Real.exp (-(min c₁ c₂) * s) := by
      have := mul_le_mul_of_nonneg_left e₁ hC₁.le
      have := mul_le_mul_of_nonneg_left e₂ hC₂.le
      linarith
    _ = (C₁ + C₂) * Real.exp (-(min c₁ c₂) * s) := by ring

theorem H15SubexponentialDecay.neg {F : ℕ → ℝ}
    (hF : H15SubexponentialDecay F) :
    H15SubexponentialDecay (fun N => -F N) := by
  obtain ⟨C, hC, c, hc, hbound⟩ := hF
  refine ⟨C, hC, c, hc, ?_⟩
  intro N hN
  rw [abs_neg]
  exact hbound N hN

theorem H15SubexponentialDecay.sub {F G : ℕ → ℝ}
    (hF : H15SubexponentialDecay F) (hG : H15SubexponentialDecay G) :
    H15SubexponentialDecay (fun N => F N - G N) := by
  have := hF.add hG.neg
  refine this.congr ?_
  intro N _
  ring

/-! ## The named Task-R proposition and its exact status -/

/-- `H15CoupledVariationBoundaryDecay`: subexponential decay of the coupled
variation/boundary aggregate along a schedule `N ↦ (g N, r N, U N, Q N)`. -/
def H15CoupledVariationBoundaryDecay (g r U Q : ℕ → ℕ) : Prop :=
  H15SubexponentialDecay fun N =>
    h15NormalizedProgressionCoupledVariationBoundaryAggregate
      N (g N) (r N) (U N) (Q N)

/-- Subexponential decay of the signed square-divisor aggregate along the
same schedule.  This is the H15 branch's open signed estimate. -/
def H15SignedSquareDivisorAggregateDecay (g r U Q : ℕ → ℕ) : Prop :=
  H15SubexponentialDecay fun N =>
    h15RamanujanSignedSquareDivisorAggregate N (g N) (r N) (U N) (Q N)

/-- **Main result of Task R.**  Along any admissible schedule, the coupled
variation/boundary decay proposition is *equivalent* to the decay of the
signed square-divisor aggregate.  In other words the coupled
variation/boundary term is not an auxiliary piece that could be discharged by
divisor-budget or orthogonality input alone: proving it is exactly proving the
open H15 signed estimate. -/
theorem H15CoupledVariationBoundaryDecay_iff_signedSquareDivisorDecay
    {g r U Q : ℕ → ℕ}
    (hg : ∀ N : ℕ, 2 ≤ N → 0 < g N) (hU : ∀ N : ℕ, 2 ≤ N → 0 < U N)
    (hQ : ∀ N : ℕ, 2 ≤ N → 0 < Q N) :
    H15CoupledVariationBoundaryDecay g r U Q ↔
      H15SignedSquareDivisorAggregateDecay g r U Q := by
  constructor
  · intro h
    refine h.congr ?_
    intro N hN
    exact h15NormalizedProgressionCoupledVariationBoundaryAggregate_eq_signedSquareDivisor
      (hg N hN) (hU N hN) (hQ N hN)
  · intro h
    refine h.congr ?_
    intro N hN
    exact (h15NormalizedProgressionCoupledVariationBoundaryAggregate_eq_signedSquareDivisor
      (hg N hN) (hU N hN) (hQ N hN)).symm

/-! ## The pointwise coupled aggregate and the two named superperiod gates -/

/-- Absolute control of the boundary half of the pointwise coupled aggregate
by the repository's endpoint budget. -/
theorem abs_sum_h15DyadicNormalizedSuperperiodBoundaryDefect_le_budget
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hQ : 0 < Q) :
    |∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
      ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
        h15DyadicNormalizedSuperperiodBoundaryDefect r U
          (h15SquareDivisorProgressionModulus g d) q
          (h15NormalizedProgressionSmoothWeight N g d)| ≤
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
          h15NormalizedSuperperiodBoundaryBudget U
            (h15SquareDivisorProgressionModulus g d) q := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro q hq
  have hqBounds := mem_h15BettinChandeeSupportedNatBlock.mp hq
  have hqPos : 0 < q := hQ.trans_le hqBounds.1
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro d hd
  have hd' := hd
  rw [h15DyadicActivePeriodSquareDivisorIndices, Finset.mem_biUnion] at hd'
  obtain ⟨k, _hk, hdk⟩ := hd'
  have hactive := mem_h15ActivePeriodSquareDivisorIndices.mp hdk
  have hLPos : 0 < h15SquareDivisorProgressionModulus g d := by omega
  exact abs_h15DyadicNormalizedSuperperiodBoundaryDefect_smooth_le
    (d := d) hN hg hU hLPos hqPos

/-- The pointwise coupled aggregate splits, without any loss, into the
variation aggregate controlled by
`H15NormalizedSuperperiodVariationPowerSaving` and the boundary aggregate
controlled by `H15NormalizedProgressionBoundaryAverage`. -/
theorem abs_h15NormalizedProgressionPointwiseCoupledAggregate_le
    (HV : H15NormalizedSuperperiodVariationPowerSaving)
    (HB : H15NormalizedProgressionBoundaryAverage)
    {N g r U Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U) (hQ : 0 < Q)
    (hQU : Q ≤ U) :
    |h15NormalizedProgressionPointwiseCoupledAggregate N g r U Q| ≤
      HV.C / (U : ℝ) ^ HV.η + HB.C / (U : ℝ) ^ HB.η := by
  have hsplit :
      h15NormalizedProgressionPointwiseCoupledAggregate N g r U Q =
        (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
          ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
            h15DyadicNormalizedSuperperiodVariationDefect r U
              (h15SquareDivisorProgressionModulus g d) q
              (h15NormalizedProgressionSmoothWeight N g d)
              (fun j => h15NormalizedProgressionSmoothWeight N g d
                (j * (h15SquareDivisorProgressionModulus g d * q)))) +
          ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
            ∑ d ∈ h15DyadicActivePeriodSquareDivisorIndices g U q,
              h15DyadicNormalizedSuperperiodBoundaryDefect r U
                (h15SquareDivisorProgressionModulus g d) q
                (h15NormalizedProgressionSmoothWeight N g d) := by
    unfold h15NormalizedProgressionPointwiseCoupledAggregate
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_add_distrib
  rw [hsplit]
  refine le_trans (abs_add_le _ _) (add_le_add (HV.bound hN hg hU hQ hQU) ?_)
  exact le_trans
    (abs_sum_h15DyadicNormalizedSuperperiodBoundaryDefect_le_budget
      hN hg hU hQ)
    (HB.bound hN hg hU hQ hQU)

/-- Power-saving gate for the genuine pointwise coupled aggregate. -/
structure H15PointwiseCoupledAggregatePowerSaving where
  C : ℝ
  η : ℝ
  C_nonneg : 0 ≤ C
  η_pos : 0 < η
  bound : ∀ {N g r U Q : ℕ},
    2 ≤ N → 1 ≤ g → 0 < U → 0 < Q → Q ≤ U →
    |h15NormalizedProgressionPointwiseCoupledAggregate N g r U Q| ≤
      C / (U : ℝ) ^ η

/-- The two named superperiod gates of the repository together give a power
saving for the pointwise coupled aggregate. -/
noncomputable def H15PointwiseCoupledAggregatePowerSaving.ofVariationAndBoundaryAverage
    (HV : H15NormalizedSuperperiodVariationPowerSaving)
    (HB : H15NormalizedProgressionBoundaryAverage) :
    H15PointwiseCoupledAggregatePowerSaving where
  C := HV.C + HB.C
  η := min HV.η HB.η
  C_nonneg := add_nonneg HV.C_nonneg HB.C_nonneg
  η_pos := lt_min HV.η_pos HB.η_pos
  bound := by
    intro N g r U Q hN hg hU hQ hQU
    have hU1 : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
    have hmin_pos : (0 : ℝ) < (U : ℝ) ^ min HV.η HB.η :=
      Real.rpow_pos_of_pos (by linarith) _
    have hV : HV.C / (U : ℝ) ^ HV.η ≤ HV.C / (U : ℝ) ^ min HV.η HB.η := by
      apply div_le_div_of_nonneg_left HV.C_nonneg hmin_pos
      exact Real.rpow_le_rpow_of_exponent_le hU1 (min_le_left _ _)
    have hB : HB.C / (U : ℝ) ^ HB.η ≤ HB.C / (U : ℝ) ^ min HV.η HB.η := by
      apply div_le_div_of_nonneg_left HB.C_nonneg hmin_pos
      exact Real.rpow_le_rpow_of_exponent_le hU1 (min_le_right _ _)
    have hmain := abs_h15NormalizedProgressionPointwiseCoupledAggregate_le
      HV HB (r := r) hN hg hU hQ hQU
    have : HV.C / (U : ℝ) ^ min HV.η HB.η +
        HB.C / (U : ℝ) ^ min HV.η HB.η =
        (HV.C + HB.C) / (U : ℝ) ^ min HV.η HB.η := by
      field_simp
    linarith

/-! ## Interface with the Abel interior/boundary decays (Task Q objects) -/

/-- Decay of the Abel interior aggregate along a schedule. -/
def H15AbelInteriorDecay (g r U Q : ℕ → ℕ) : Prop :=
  H15SubexponentialDecay fun N =>
    h15NormalizedProgressionAbelInteriorAggregate N (g N) (r N) (U N) (Q N)

/-- Decay of the correction-coupled Abel boundary aggregate along a
schedule. -/
def H15CorrectionCoupledAbelBoundaryDecay (g r U Q : ℕ → ℕ) : Prop :=
  H15SubexponentialDecay fun N =>
    h15NormalizedProgressionCorrectionCoupledAbelBoundaryAggregate
      N (g N) (r N) (U N) (Q N)

/-- Decay of the genuine pointwise coupled aggregate along a schedule. -/
def H15PointwiseCoupledAggregateDecay (g r U Q : ℕ → ℕ) : Prop :=
  H15SubexponentialDecay fun N =>
    h15NormalizedProgressionPointwiseCoupledAggregate N (g N) (r N) (U N) (Q N)

/-- Forward interface: coupled variation/boundary decay together with the two
Abel decays yields decay of the pointwise coupled aggregate.  This uses the
exact identity
`h15CoupledVariationBoundary_add_abelInterior_add_boundary`. -/
theorem H15PointwiseCoupledAggregateDecay_of_coupled_and_abel
    {g r U Q : ℕ → ℕ}
    (hg : ∀ N : ℕ, 2 ≤ N → 0 < g N) (hU : ∀ N : ℕ, 2 ≤ N → 0 < U N)
    (hQ : ∀ N : ℕ, 2 ≤ N → 0 < Q N)
    (hcv : H15CoupledVariationBoundaryDecay g r U Q)
    (hint : H15AbelInteriorDecay g r U Q)
    (hbd : H15CorrectionCoupledAbelBoundaryDecay g r U Q) :
    H15PointwiseCoupledAggregateDecay g r U Q := by
  have hsum := (hcv.add hint).add hbd
  refine hsum.congr ?_
  intro N hN
  exact h15CoupledVariationBoundary_add_abelInterior_add_boundary
    (hg N hN) (hU N hN) (hQ N hN)

/-- Converse interface: the pointwise coupled decay together with the two
Abel decays returns the coupled variation/boundary decay. -/
theorem H15CoupledVariationBoundaryDecay_of_pointwise_and_abel
    {g r U Q : ℕ → ℕ}
    (hg : ∀ N : ℕ, 2 ≤ N → 0 < g N) (hU : ∀ N : ℕ, 2 ≤ N → 0 < U N)
    (hQ : ∀ N : ℕ, 2 ≤ N → 0 < Q N)
    (hpt : H15PointwiseCoupledAggregateDecay g r U Q)
    (hint : H15AbelInteriorDecay g r U Q)
    (hbd : H15CorrectionCoupledAbelBoundaryDecay g r U Q) :
    H15CoupledVariationBoundaryDecay g r U Q := by
  have hsub := (hpt.sub hint).sub hbd
  refine hsub.congr ?_
  intro N hN
  have hid := h15CoupledVariationBoundary_add_abelInterior_add_boundary
    (N := N) (g := g N) (r := r N) (U := U N) (Q := Q N)
    (hg N hN) (hU N hN) (hQ N hN)
  linarith

end NBMellinTools.NB12
