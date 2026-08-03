import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis
import Mathlib.Analysis.Analytic.Order

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannGaussianSubtraction

open Complex Filter Set Topology MeasureTheory
open scoped Interval Real
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannTwoPoleRectangle
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis

theorem differentiable_hurwitzPoleRemovedFactor (x : UnitAddCircle) :
    Differentiable ℂ (hurwitzPoleRemovedFactor x) := by
  intro s
  by_cases hs : s = 1
  · subst s
    exact differentiableAt_hurwitzPoleRemovedFactor x
  · unfold hurwitzPoleRemovedFactor hurwitzRegularPart
    have hprincipal : DifferentiableAt ℂ
        (fun z : ℂ => 1 / (z - 1) / Complex.Gammaℝ z) s := by
      convert (((differentiableAt_const (c := (1 : ℂ))).div
        (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs)).mul
          Complex.differentiable_Gammaℝ_inv.differentiableAt) using 1 <;>
        simp [div_eq_mul_inv]
    exact Complex.differentiable_Gammaℝ_inv.differentiableAt.add
      ((differentiableAt_id.sub_const 1).mul
        ((HurwitzZeta.differentiableAt_hurwitzZeta x hs).sub
          hprincipal))

theorem differentiable_estermannPoleRemovedNumerator
    (a q : ℕ) [NeZero q] :
    Differentiable ℂ (estermannPoleRemovedNumerator a q) := by
  intro s
  unfold estermannPoleRemovedNumerator
  have hq : DifferentiableAt ℂ (fun z : ℂ => (q : ℂ) ^ (-z)) s := by
    fun_prop
  apply hq.mul
  apply DifferentiableAt.fun_sum
  intro j _
  apply DifferentiableAt.mul
  · apply hq.mul
    apply DifferentiableAt.fun_sum
    intro k _
    exact (differentiable_hurwitzPoleRemovedFactor
      (ZMod.toAddCircle k) s).const_mul _
  · exact differentiable_hurwitzPoleRemovedFactor (ZMod.toAddCircle j) s

theorem exists_differentiable_secondOrderQuotient
    (N : ℂ → ℂ) (hN : Differentiable ℂ N) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ z : ℂ,
      N z = N 0 + z * deriv N 0 + z ^ 2 * F z := by
  have hAnalyticOn : AnalyticOnNhd ℂ N Set.univ :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_univ).2
      hN.differentiableOn
  have hAnalytic : AnalyticAt ℂ N 0 := hAnalyticOn 0 (Set.mem_univ 0)
  rcases hAnalytic.exists_eq_sum_add_pow_mul 2 with ⟨F, hFa, hEq⟩
  have hEq' : ∀ z : ℂ,
      N z = N 0 + z * deriv N 0 + z ^ 2 * F z := by
    intro z
    simpa [Finset.sum_range_succ, iteratedDeriv_zero,
      iteratedDeriv_one, add_assoc] using hEq z
  have hFdiff : Differentiable ℂ F := by
    intro z
    by_cases hz : z = 0
    · subst z
      exact hFa.differentiableAt
    · let Q : ℂ → ℂ := fun w =>
        (N w - N 0 - w * deriv N 0) / w ^ 2
      have hQ : DifferentiableAt ℂ Q z := by
        unfold Q
        exact (((hN z).sub (differentiableAt_const (c := N 0))).sub
          (differentiableAt_id.mul_const (deriv N 0))).div
            (differentiableAt_id.pow 2) (pow_ne_zero 2 hz)
      have hFQ : F =ᶠ[𝓝 z] Q := by
        filter_upwards [eventually_ne_nhds hz] with w hw
        have heq := hEq' w
        unfold Q
        rw [eq_div_iff (pow_ne_zero 2 hw)]
        rw [heq]
        ring
      exact hQ.congr_of_eventuallyEq hFQ
  exact ⟨F, hFdiff, hEq'⟩

theorem exists_differentiable_firstOrderQuotient
    (M : ℂ → ℂ) (hM : Differentiable ℂ M) :
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ ∀ u : ℂ,
      M u = M 0 + u * R u := by
  have hAnalyticOn : AnalyticOnNhd ℂ M Set.univ :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_univ).2
      hM.differentiableOn
  have hAnalytic : AnalyticAt ℂ M 0 := hAnalyticOn 0 (Set.mem_univ 0)
  rcases hAnalytic.exists_eq_sum_add_pow_mul 1 with ⟨R, hRa, hEq⟩
  have hEq' : ∀ u : ℂ, M u = M 0 + u * R u := by
    intro u
    simpa [Finset.sum_range_succ, iteratedDeriv_zero] using hEq u
  have hRdiff : Differentiable ℂ R := by
    intro u
    by_cases hu : u = 0
    · subst u
      exact hRa.differentiableAt
    · let Q : ℂ → ℂ := fun v => (M v - M 0) / v
      have hQ : DifferentiableAt ℂ Q u := by
        unfold Q
        exact ((hM u).sub (differentiableAt_const (c := M 0))).div
          differentiableAt_id hu
      have hRQ : R =ᶠ[𝓝 u] Q := by
        filter_upwards [eventually_ne_nhds hu] with v hv
        have heq := hEq' v
        unfold Q
        rw [eq_div_iff hv, heq]
        ring
      exact hQ.congr_of_eventuallyEq hRQ
  exact ⟨R, hRdiff, hEq'⟩

theorem exists_differentiable_firstOrderQuotientAtOne
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z : ℂ,
      F z = F 1 + (z - 1) * G z := by
  let M : ℂ → ℂ := fun u => F (1 + u)
  have hM : Differentiable ℂ M := by
    intro u
    unfold M
    fun_prop
  rcases exists_differentiable_firstOrderQuotient M hM with
    ⟨R, hR, hEq⟩
  let G : ℂ → ℂ := fun z => R (z - 1)
  have hG : Differentiable ℂ G := by
    intro z
    unfold G
    fun_prop
  refine ⟨G, hG, ?_⟩
  intro z
  have h := hEq (z - 1)
  simpa [M, G] using h

noncomputable def estermannGaussianPoleNumerator
    (η : ℝ) (a q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  estermannGaussianDamping η s *
    estermannPoleRemovedNumerator a q (1 - s)

theorem differentiable_estermannGaussianPoleNumerator
    (η : ℝ) (a q : ℕ) [NeZero q] :
    Differentiable ℂ (estermannGaussianPoleNumerator η a q) := by
  intro s
  unfold estermannGaussianPoleNumerator estermannGaussianDamping
  apply DifferentiableAt.mul
  · fun_prop
  · exact (differentiable_estermannPoleRemovedNumerator a q (1 - s)).comp s (by
      fun_prop)

theorem estermannWeightedIntegrand_eq_gaussianPoleNumerator_div
    (η : ℝ) (a q : ℕ) [NeZero q] {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    estermannWeightedIntegrand a q
        (estermannGaussianEvaluationWeight η) s =
      estermannGaussianPoleNumerator η a q s / (s ^ 2 * (s - 1)) := by
  have hsub : 1 - s ≠ 1 := by
    intro h
    apply hs0
    have hneg : -s = 0 := by simpa using congrArg (fun z : ℂ => z - 1) h
    exact neg_eq_zero.mp hneg
  unfold estermannWeightedIntegrand estermannGaussianEvaluationWeight
  unfold estermannEvaluationWeight estermannGaussianPoleNumerator
  rw [estermannPoleRemovedNumerator_eq a q hsub]
  field_simp [hs0, hs1]
  ring

theorem TwoPoleRectangleSubtraction.residue_limit
    {f : ℂ → ℂ} (H : TwoPoleRectangleSubtraction f) :
    Tendsto
      (fun s : ℂ => s * (f s - H.doubleCoefficient / s ^ 2))
      (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (nhds H.residueAtZero) := by
  let R : ℂ → ℂ := fun s =>
    s * H.regularized s + H.residueAtZero +
      s * H.residueAtOne / (s - 1)
  have hR : ContinuousAt R 0 := by
    unfold R
    exact ((continuousAt_id.mul
      H.regularized_differentiable.continuous.continuousAt).add
        continuousAt_const).add
          ((continuousAt_id.mul continuousAt_const).div
            (continuousAt_id.sub continuousAt_const) (by norm_num))
  have hRt : Tendsto R (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (nhds H.residueAtZero) := by
    convert hR.tendsto.mono_left inf_le_left using 1 <;> simp [R]
  apply hRt.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)).filter_mono inf_le_left]
      with s hs0 hs1
  have hs0' : s ≠ 0 := by simpa using hs0
  rw [H.decomposition s hs0' hs1]
  unfold R
  field_simp [hs0', hs1]
  ring

theorem neg_estermannGaussianPoleNumerator_zero
    (η : ℝ) (a q : ℕ) [NeZero q] :
    -estermannGaussianPoleNumerator η a q 0 =
      estermannWeightedDoublePoleCoefficient a q
        (estermannGaussianEvaluationWeight η) := by
  unfold estermannGaussianPoleNumerator
  simp only [sub_zero]
  rw [estermannPoleRemovedNumerator_one]
  unfold estermannWeightedDoublePoleCoefficient
  unfold estermannGaussianEvaluationWeight estermannEvaluationWeight
  ring

theorem estermannGaussianPoleNumerator_one
    (η : ℝ) (a q : ℕ) [NeZero q] :
    estermannGaussianPoleNumerator η a q 1 =
      estermannHurwitzContinuation a q 0 := by
  unfold estermannGaussianPoleNumerator
  rw [estermannGaussianDamping_one]
  simp only [sub_self]
  have hzero : (0 : ℂ) ≠ 1 := by norm_num
  rw [estermannPoleRemovedNumerator_eq a q hzero]
  norm_num

theorem exists_estermannGaussianTwoPoleSubtraction
    (η : ℝ) (a q : ℕ) [NeZero q] :
    ∃ H : TwoPoleRectangleSubtraction
        (estermannWeightedIntegrand a q
          (estermannGaussianEvaluationWeight η)),
      H.doubleCoefficient =
          estermannWeightedDoublePoleCoefficient a q
            (estermannGaussianEvaluationWeight η) ∧
        H.residueAtZero =
          estermannWeightedResidueCoefficient a q
            (estermannGaussianEvaluationWeight η) ∧
        H.residueAtOne = estermannHurwitzContinuation a q 0 := by
  let N : ℂ → ℂ := estermannGaussianPoleNumerator η a q
  have hN : Differentiable ℂ N :=
    differentiable_estermannGaussianPoleNumerator η a q
  rcases exists_differentiable_secondOrderQuotient N hN with
    ⟨F, hF, hNexp⟩
  rcases exists_differentiable_firstOrderQuotientAtOne F hF with
    ⟨G, hG, hFexp⟩
  have hFone : F 1 = N 1 - N 0 - deriv N 0 := by
    have h := hNexp 1
    norm_num at h
    linear_combination -h
  let H : TwoPoleRectangleSubtraction
      (estermannWeightedIntegrand a q
        (estermannGaussianEvaluationWeight η)) := {
    regularized := G
    regularized_differentiable := hG
    doubleCoefficient := -N 0
    residueAtZero := -(N 0 + deriv N 0)
    residueAtOne := N 1
    decomposition s hs0 hs1 := by
      rw [estermannWeightedIntegrand_eq_gaussianPoleNumerator_div
        η a q hs0 hs1]
      change N s / (s ^ 2 * (s - 1)) = _
      rw [hNexp s, hFexp s, hFone]
      have hsm1 : -1 + s ≠ 0 := by
        rw [add_comm]
        exact sub_ne_zero.mpr hs1
      have hsubform : -1 + s = s - 1 := by ring
      field_simp [hs0, hs1, hsm1, sub_ne_zero.mpr hs1]
      ring
  }
  have hdouble : H.doubleCoefficient =
      estermannWeightedDoublePoleCoefficient a q
        (estermannGaussianEvaluationWeight η) := by
    exact neg_estermannGaussianPoleNumerator_zero η a q
  have hres0 : H.residueAtZero =
      estermannWeightedResidueCoefficient a q
        (estermannGaussianEvaluationWeight η) := by
    have hleft := TwoPoleRectangleSubtraction.residue_limit H
    rw [hdouble] at hleft
    have hright := estermannWeightedIntegrand_residue_limit a q
      (estermannGaussianEvaluationWeight η)
      (differentiableAt_estermannGaussianEvaluationWeight_zero η)
    exact tendsto_nhds_unique hleft hright
  have hres1 : H.residueAtOne =
      estermannHurwitzContinuation a q 0 := by
    exact estermannGaussianPoleNumerator_one η a q
  exact ⟨H, hdouble, hres0, hres1⟩

noncomputable def estermannGaussianTwoPoleSubtraction
    (η : ℝ) (a q : ℕ) [NeZero q] :
    TwoPoleRectangleSubtraction
      (estermannWeightedIntegrand a q
        (estermannGaussianEvaluationWeight η)) :=
  Classical.choose (exists_estermannGaussianTwoPoleSubtraction η a q)

theorem estermannGaussianTwoPoleSubtraction_residueAtZero
    (η : ℝ) (a q : ℕ) [NeZero q] :
    (estermannGaussianTwoPoleSubtraction η a q).residueAtZero =
      estermannWeightedResidueCoefficient a q
        (estermannGaussianEvaluationWeight η) :=
  (Classical.choose_spec
    (exists_estermannGaussianTwoPoleSubtraction η a q)).2.1

theorem estermannGaussianTwoPoleSubtraction_residueAtOne
    (η : ℝ) (a q : ℕ) [NeZero q] :
    (estermannGaussianTwoPoleSubtraction η a q).residueAtOne =
      estermannHurwitzContinuation a q 0 :=
  (Classical.choose_spec
    (exists_estermannGaussianTwoPoleSubtraction η a q)).2.2

noncomputable def estermannGaussianTwoPoleBoundaryIdentity
    (η : ℝ) (a q : ℕ) [NeZero q]
    (σL σR : ℝ) (hL : σL < 0) (hR : 1 < σR) :
    EstermannTwoPoleBoundaryIdentity a q
      (estermannGaussianEvaluationWeight η) σL σR :=
  EstermannTwoPoleBoundaryIdentity.of_subtraction hL hR
    (estermannGaussianTwoPoleSubtraction η a q)
    (estermannGaussianTwoPoleSubtraction_residueAtZero η a q)
    (estermannGaussianTwoPoleSubtraction_residueAtOne η a q)

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannGaussianSubtraction
