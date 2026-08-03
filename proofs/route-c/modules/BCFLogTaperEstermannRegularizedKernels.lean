import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannGlobalExchange

/-!
# Route B9.3: H15 physical inverse-Mellin kernels

The two common Mellin profiles from WP2 are converted here into Mathlib
`mellinInv` kernels.  Every integrated Dirichlet term factors exactly as its
completed H15 coefficient times the corresponding physical kernel, including
the zero-frequency convention, and the result is lifted through the complete
finite `(g,q)` aggregate.

The pole ledger at `s = 1` is also explicit: the same-sign crossed term is
`x⁻¹ q/(2π²)` and the opposite-sign term is its negative.  A final structure
states precisely the rectangle shift still needed for unconditional line
independence.  It is not inhabited in this file, and no Bessel or Kuznetsov
identity is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannRegularizedKernels

open Complex Filter LSeries MeasureTheory Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannInverseMellin
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15MellinAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannGlobalExchange
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFourToTwoCollapse

noncomputable def h15SameSignKernelProfile
    (η : ℝ) (q : ℕ) (s : ℂ) : ℂ :=
  h15SameSignMellinFactor (estermannGaussianEvaluationWeight η) q s

noncomputable def h15OppositeSignKernelProfile
    (η : ℝ) (q : ℕ) (s : ℂ) : ℂ :=
  h15OppositeSignMellinFactor (estermannGaussianEvaluationWeight η) q s

noncomputable def h15SameSignMellinKernel
    (η c : ℝ) (q : ℕ) (x : ℝ) : ℂ :=
  mellinInv c (h15SameSignKernelProfile η q) x

noncomputable def h15OppositeSignMellinKernel
    (η c : ℝ) (q : ℕ) (x : ℝ) : ℂ :=
  mellinInv c (h15OppositeSignKernelProfile η q) x

theorem integral_sameSignTerm_eq_mellinKernel
    (N g q : ℕ) [NeZero q] (η c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      h15SameSignMellinFactor (estermannGaussianEvaluationWeight η) q
          (estermannVerticalPoint c t) *
        LSeries.term (h15SameSignCoefficient N g q)
          (estermannVerticalPoint c t) n) =
      h15SameSignCoefficient N g q n *
        ((2 * Real.pi : ℂ) * h15SameSignMellinKernel η c q n) := by
  unfold h15SameSignMellinKernel h15SameSignKernelProfile
  rw [← verticalIntegral_cpow_neg_eq_two_pi_mul_mellinInv]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  have hcast : (((n : ℝ) : ℂ)) = (n : ℂ) := by norm_cast
  rw [hcast]
  ring

theorem integral_oppositeSignTerm_eq_mellinKernel
    (N g q : ℕ) [NeZero q] (η c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      h15OppositeSignMellinFactor (estermannGaussianEvaluationWeight η) q
          (estermannVerticalPoint c t) *
        LSeries.term (h15OppositeSignCoefficient N g q)
          (estermannVerticalPoint c t) n) =
      h15OppositeSignCoefficient N g q n *
        ((2 * Real.pi : ℂ) * h15OppositeSignMellinKernel η c q n) := by
  unfold h15OppositeSignMellinKernel h15OppositeSignKernelProfile
  rw [← verticalIntegral_cpow_neg_eq_two_pi_mul_mellinInv]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  have hcast : (((n : ℝ) : ℂ)) = (n : ℂ) := by norm_cast
  rw [hcast]
  ring

@[simp] theorem estermannDivisorCoeff_zero : estermannDivisorCoeff 0 = 0 := by
  rw [estermannDivisorCoeff_apply]
  simp

@[simp] theorem h15SameSignCompletedCoefficient_zero
    (N g q : ℕ) [NeZero q] :
    h15SameSignCompletedCoefficient N g q 0 = 0 := by
  simp [h15SameSignCompletedCoefficient]

@[simp] theorem h15OppositeSignCompletedCoefficient_zero
    (N g q : ℕ) [NeZero q] :
    h15OppositeSignCompletedCoefficient N g q 0 = 0 := by
  simp [h15OppositeSignCompletedCoefficient]

theorem integral_sameSignTerm_eq_completedKernel
    (N g q : ℕ) [NeZero q] (η c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      h15SameSignMellinFactor (estermannGaussianEvaluationWeight η) q
          (estermannVerticalPoint c t) *
        LSeries.term (h15SameSignCoefficient N g q)
          (estermannVerticalPoint c t) n) =
      h15SameSignCompletedCoefficient N g q n *
        ((2 * Real.pi : ℂ) * h15SameSignMellinKernel η c q n) := by
  rw [← h15SameSignCoefficient_eq_completed]
  exact integral_sameSignTerm_eq_mellinKernel N g q η c hn

theorem integral_oppositeSignTerm_eq_completedKernel
    (N g q : ℕ) [NeZero q] (η c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      h15OppositeSignMellinFactor (estermannGaussianEvaluationWeight η) q
          (estermannVerticalPoint c t) *
        LSeries.term (h15OppositeSignCoefficient N g q)
          (estermannVerticalPoint c t) n) =
      h15OppositeSignCompletedCoefficient N g q n *
        ((2 * Real.pi : ℂ) * h15OppositeSignMellinKernel η c q n) := by
  rw [← h15OppositeSignCoefficient_eq_completed]
  exact integral_oppositeSignTerm_eq_mellinKernel N g q η c hn

noncomputable def h15SameSignCompletedKernelSeries
    (N g q : ℕ) [NeZero q] (η c : ℝ) : ℂ :=
  ∑' n : ℕ, h15SameSignCompletedCoefficient N g q n *
    ((2 * Real.pi : ℂ) * h15SameSignMellinKernel η c q n)

noncomputable def h15OppositeSignCompletedKernelSeries
    (N g q : ℕ) [NeZero q] (η c : ℝ) : ℂ :=
  ∑' n : ℕ, h15OppositeSignCompletedCoefficient N g q n *
    ((2 * Real.pi : ℂ) * h15OppositeSignMellinKernel η c q n)

noncomputable def h15TwoSignCompletedKernelSeries
    (N g q : ℕ) [NeZero q] (η c : ℝ) : ℂ :=
  h15SameSignCompletedKernelSeries N g q η c +
    h15OppositeSignCompletedKernelSeries N g q η c

theorem h15SameSignTermwiseVerticalIntegral_eq_completedKernelSeries
    (N g q : ℕ) [NeZero q] (η c : ℝ) :
    h15SameSignTermwiseVerticalIntegral N g q η c =
      h15SameSignCompletedKernelSeries N g q η c := by
  unfold h15SameSignTermwiseVerticalIntegral
    h15SameSignCompletedKernelSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · exact integral_sameSignTerm_eq_completedKernel N g q η c hn

theorem h15OppositeSignTermwiseVerticalIntegral_eq_completedKernelSeries
    (N g q : ℕ) [NeZero q] (η c : ℝ) :
    h15OppositeSignTermwiseVerticalIntegral N g q η c =
      h15OppositeSignCompletedKernelSeries N g q η c := by
  unfold h15OppositeSignTermwiseVerticalIntegral
    h15OppositeSignCompletedKernelSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · exact integral_oppositeSignTerm_eq_completedKernel N g q η c hn

theorem h15TwoSignTermwiseVerticalIntegral_eq_completedKernelSeries
    (N g q : ℕ) [NeZero q] (η c : ℝ) :
    h15TwoSignTermwiseVerticalIntegral N g q η c =
      h15TwoSignCompletedKernelSeries N g q η c := by
  unfold h15TwoSignTermwiseVerticalIntegral h15TwoSignCompletedKernelSeries
  rw [h15SameSignTermwiseVerticalIntegral_eq_completedKernelSeries,
    h15OppositeSignTermwiseVerticalIntegral_eq_completedKernelSeries]

noncomputable def h15InteriorCompletedKernelAggregate
    (N : ℕ) (η c : ℝ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ q ∈ Finset.Icc 2 (N / g),
      if hq : 0 < q then
        @h15TwoSignCompletedKernelSeries N g q
          ⟨Nat.ne_of_gt hq⟩ η c
      else 0

theorem h15InteriorTermwiseVerticalIntegral_eq_completedKernelAggregate
    (N : ℕ) (η c : ℝ) :
    h15InteriorTermwiseVerticalIntegral N η c =
      h15InteriorCompletedKernelAggregate N η c := by
  classical
  unfold h15InteriorTermwiseVerticalIntegral
    h15InteriorCompletedKernelAggregate
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro q hqmem
  have hq : 0 < q := by
    have := (Finset.mem_Icc.mp hqmem).1
    omega
  rw [dif_pos hq, dif_pos hq]
  exact @h15TwoSignTermwiseVerticalIntegral_eq_completedKernelSeries N g q
    ⟨Nat.ne_of_gt hq⟩ η c

/-- WP2 followed by exact physical-kernel extraction. -/
theorem h15Interior_integral_eq_completedKernelAggregate
    (N : ℕ) (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    (∫ t : ℝ,
      h15InteriorNaturalDualIntegrand N
        (estermannGaussianEvaluationWeight η)
        (estermannVerticalPoint c t)) =
      h15InteriorCompletedKernelAggregate N η c := by
  rw [h15Interior_global_sum_integral_exchange N η c hη hc,
    h15InteriorTermwiseVerticalIntegral_eq_completedKernelAggregate]

/-! ## Pole ledger for the physical profiles -/

def HasResidueAtOne (F : ℂ → ℂ) (R : ℂ) : Prop :=
  Tendsto (fun s : ℂ => (s - 1) * F s) (𝓝[≠] 1) (𝓝 R)

theorem differentiableAt_estermannCollapsedCommonFactor_one
    (q : ℕ) [NeZero q] :
    DifferentiableAt ℂ (estermannCollapsedCommonFactor q) 1 := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  have hDual : DifferentiableAt ℂ (estermannDualGammaFactor q) 1 := by
    unfold estermannDualGammaFactor
    exact (((differentiableAt_id.sub_const 1).const_cpow (Or.inl hq)).mul
      (differentiableAt_id.neg.const_cpow (Or.inl h2pi))).mul
        Complex.differentiableAt_Gamma_one
  unfold estermannCollapsedCommonFactor
  exact (hDual.mul hDual).mul
    (((differentiableAt_id.neg.const_cpow (Or.inl hq)).mul
      (differentiableAt_const (c := (q : ℂ)))).mul
        (differentiableAt_id.const_cpow (Or.inl hq)))

theorem estermannDualGammaFactor_one (q : ℕ) [NeZero q] :
    estermannDualGammaFactor q 1 = (2 * Real.pi : ℂ)⁻¹ := by
  unfold estermannDualGammaFactor
  simp [Complex.Gamma_one, Complex.cpow_neg_one]

theorem estermannCollapsedCommonFactor_one (q : ℕ) [NeZero q] :
    estermannCollapsedCommonFactor q 1 =
      (q : ℂ) / (4 * (Real.pi : ℂ) ^ 2) := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  unfold estermannCollapsedCommonFactor
  simp only [estermannDualGammaFactor_one]
  simp only [Complex.cpow_neg_one, Complex.cpow_one]
  field_simp [hq, Real.pi_ne_zero]
  ring

theorem hasResidueAtOne_h15SameSignKernelProfile
    (η : ℝ) (q : ℕ) [NeZero q] :
    HasResidueAtOne (h15SameSignKernelProfile η q)
      ((q : ℂ) / (2 * (Real.pi : ℂ) ^ 2)) := by
  have hW := hasUnitResidueAtOne_estermannGaussianEvaluationWeight η
  have hC : Tendsto
      (fun s : ℂ => 2 * estermannCollapsedCommonFactor q s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (2 * ((q : ℂ) / (4 * (Real.pi : ℂ) ^ 2)))) := by
    have hcommon : Tendsto (estermannCollapsedCommonFactor q)
        (𝓝[≠] (1 : ℂ)) (𝓝 (estermannCollapsedCommonFactor q 1)) :=
      ((differentiableAt_estermannCollapsedCommonFactor_one q).continuousAt.tendsto).mono_left
        inf_le_left
    simpa [estermannCollapsedCommonFactor_one] using
      tendsto_const_nhds.mul hcommon
  unfold HasResidueAtOne h15SameSignKernelProfile
    h15SameSignMellinFactor
  convert hW.mul hC using 1
  · ext s
    ring
  · field_simp [Real.pi_ne_zero]
    ring

theorem hasResidueAtOne_h15OppositeSignKernelProfile
    (η : ℝ) (q : ℕ) [NeZero q] :
    HasResidueAtOne (h15OppositeSignKernelProfile η q)
      (-((q : ℂ) / (2 * (Real.pi : ℂ) ^ 2))) := by
  have hW := hasUnitResidueAtOne_estermannGaussianEvaluationWeight η
  have hC : Tendsto
      (fun s : ℂ =>
        2 * Complex.cos (Real.pi * s) * estermannCollapsedCommonFactor q s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (2 * Complex.cos (Real.pi * (1 : ℂ)) *
        ((q : ℂ) / (4 * (Real.pi : ℂ) ^ 2)))) := by
    have hcos : Tendsto (fun s : ℂ => Complex.cos (Real.pi * s))
        (𝓝[≠] (1 : ℂ)) (𝓝 (Complex.cos (Real.pi * (1 : ℂ)))) :=
      ((Complex.continuous_cos.comp
        (continuous_const.mul continuous_id)).tendsto (1 : ℂ)).mono_left inf_le_left
    have hcommon : Tendsto (estermannCollapsedCommonFactor q)
        (𝓝[≠] (1 : ℂ)) (𝓝 (estermannCollapsedCommonFactor q 1)) :=
      ((differentiableAt_estermannCollapsedCommonFactor_one q).continuousAt.tendsto).mono_left
        inf_le_left
    simpa [estermannCollapsedCommonFactor_one] using
      (tendsto_const_nhds.mul hcos).mul hcommon
  unfold HasResidueAtOne h15OppositeSignKernelProfile
    h15OppositeSignMellinFactor
  convert hW.mul hC using 1
  · ext s
    ring
  · simp [Complex.cos_pi]
    field_simp [Real.pi_ne_zero]
    ring

noncomputable def h15SameSignPhysicalMellinIntegrand
    (η : ℝ) (q : ℕ) (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ (-s) * h15SameSignKernelProfile η q s

noncomputable def h15OppositeSignPhysicalMellinIntegrand
    (η : ℝ) (q : ℕ) (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ (-s) * h15OppositeSignKernelProfile η q s

noncomputable def h15SameSignCrossedPoleTerm
    (q : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ)⁻¹ * ((q : ℂ) / (2 * (Real.pi : ℂ) ^ 2))

noncomputable def h15OppositeSignCrossedPoleTerm
    (q : ℕ) (x : ℝ) : ℂ :=
  -h15SameSignCrossedPoleTerm q x

theorem hasResidueAtOne_h15SameSignPhysicalMellinIntegrand
    (η : ℝ) (q : ℕ) [NeZero q] (x : ℝ) (hx : 0 < x) :
    HasResidueAtOne (h15SameSignPhysicalMellinIntegrand η q x)
      (h15SameSignCrossedPoleTerm q x) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpow : Tendsto (fun s : ℂ => (x : ℂ) ^ (-s))
      (𝓝[≠] (1 : ℂ)) (𝓝 ((x : ℂ) ^ (-(1 : ℂ)))) :=
    ((continuous_id.neg.const_cpow (Or.inl hx0)).tendsto (1 : ℂ)).mono_left
      inf_le_left
  have hres := hasResidueAtOne_h15SameSignKernelProfile η q
  unfold HasResidueAtOne at hres ⊢
  unfold h15SameSignPhysicalMellinIntegrand h15SameSignCrossedPoleTerm
  convert hpow.mul hres using 1
  · ext s
    ring
  · rw [Complex.cpow_neg_one]

theorem hasResidueAtOne_h15OppositeSignPhysicalMellinIntegrand
    (η : ℝ) (q : ℕ) [NeZero q] (x : ℝ) (hx : 0 < x) :
    HasResidueAtOne (h15OppositeSignPhysicalMellinIntegrand η q x)
      (h15OppositeSignCrossedPoleTerm q x) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpow : Tendsto (fun s : ℂ => (x : ℂ) ^ (-s))
      (𝓝[≠] (1 : ℂ)) (𝓝 ((x : ℂ) ^ (-(1 : ℂ)))) :=
    ((continuous_id.neg.const_cpow (Or.inl hx0)).tendsto (1 : ℂ)).mono_left
      inf_le_left
  have hres := hasResidueAtOne_h15OppositeSignKernelProfile η q
  unfold HasResidueAtOne at hres ⊢
  unfold h15OppositeSignPhysicalMellinIntegrand
    h15OppositeSignCrossedPoleTerm h15SameSignCrossedPoleTerm
  convert hpow.mul hres using 1
  · ext s
    ring
  · rw [Complex.cpow_neg_one]
    ring

/-- The exact contour-shift input still needed to make the raw physical
kernels independent of the chosen vertical line.  Its two fields use the
proved crossed-pole terms and contain no cancellation estimate. -/
structure H15PhysicalKernelLineShiftData
    (η : ℝ) (q : ℕ) (x cL cR : ℝ) : Prop where
  same_shift :
    h15SameSignMellinKernel η cR q x =
      h15SameSignMellinKernel η cL q x +
        h15SameSignCrossedPoleTerm q x
  opposite_shift :
    h15OppositeSignMellinKernel η cR q x =
      h15OppositeSignMellinKernel η cL q x +
        h15OppositeSignCrossedPoleTerm q x

noncomputable def h15SameSignRegularizedKernel
    (η c : ℝ) (q : ℕ) (x : ℝ) : ℂ :=
  h15SameSignMellinKernel η c q x -
    if 1 < c then h15SameSignCrossedPoleTerm q x else 0

noncomputable def h15OppositeSignRegularizedKernel
    (η c : ℝ) (q : ℕ) (x : ℝ) : ℂ :=
  h15OppositeSignMellinKernel η c q x -
    if 1 < c then h15OppositeSignCrossedPoleTerm q x else 0

theorem h15RegularizedKernels_line_independent_of_shift
    (η : ℝ) (q : ℕ) (x cL cR : ℝ)
    (hcL : cL < 1) (hcR : 1 < cR)
    (H : H15PhysicalKernelLineShiftData η q x cL cR) :
    h15SameSignRegularizedKernel η cR q x =
        h15SameSignRegularizedKernel η cL q x ∧
      h15OppositeSignRegularizedKernel η cR q x =
        h15OppositeSignRegularizedKernel η cL q x := by
  constructor
  · unfold h15SameSignRegularizedKernel
    rw [if_pos hcR, if_neg (not_lt.mpr hcL.le), H.same_shift]
    ring
  · unfold h15OppositeSignRegularizedKernel
    rw [if_pos hcR, if_neg (not_lt.mpr hcL.le), H.opposite_shift]
    ring

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannRegularizedKernels
