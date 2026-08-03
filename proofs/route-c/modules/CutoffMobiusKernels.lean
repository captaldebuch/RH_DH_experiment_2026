import RiemannHypothesis.Criteria.NymanBeurling.CoefficientFamilies
import RiemannHypothesis.Criteria.NymanBeurling.AsymptoticEnergy
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninBridge
import Mathlib.Data.Finset.Interval
import RiemannHypothesis.Criteria.NymanBeurling.BaezDuarte
namespace RH.Criteria.NymanBeurling.CutoffMobiusKernels

open RH.Criteria.NymanBeurling.CoefficientFamilies
open RH.Criteria.NymanBeurling.AsymptoticEnergy
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Certificates

-- ---------------------------------------------------------------------------
-- 1. Cutoff Weight and Coefficient
-- ---------------------------------------------------------------------------

noncomputable def cutoffWeight (N k : ℕ) : ℝ :=
  1 - ((k : ℝ) / ((N + 1 : ℕ) : ℝ))

noncomputable def cutoffMobiusCoeff (N k : ℕ) : ℝ :=
  - ((ArithmeticFunction.moebius k : ℤ) : ℝ) * cutoffWeight N k

theorem cutoffMobiusCoeff_eq_family_coeff (N : ℕ) (i : Fin N) :
    cutoffMobiusCoefficientFamily.coeff N i = cutoffMobiusCoeff N (i.val + 1) := by
  unfold cutoffMobiusCoefficientFamily cutoffMobiusCoeff cutoffWeight
  push_cast
  rfl

-- ---------------------------------------------------------------------------
-- 2. Kernel Definitions
-- ---------------------------------------------------------------------------

noncomputable def chiRhoKernel (k : ℕ) : ℝ :=
  RH.Certificates.innerProductChiRho (k - 1)

noncomputable def baezDuarteKernel (h k : ℕ) : ℝ :=
  VasyuninGram.baezDuarteGramEntry h k

-- ---------------------------------------------------------------------------
-- 3. Energy Decomposition with Kernels
-- ---------------------------------------------------------------------------

theorem sum_fin_eq_sum_Icc_one (N : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin N, f (i.val + 1)) = ∑ k ∈ Finset.Icc 1 N, f k := by
  have h1 : (∑ i : Fin N, f (i.val + 1)) = ∑ k ∈ Finset.range N, f (k + 1) := by
    exact Fin.sum_univ_eq_sum_range (fun i ↦ f (i + 1)) N
  have h2 : ∑ k ∈ Finset.range N, f (k + 1) = ∑ k ∈ Finset.Ico 1 (N + 1), f k := by
    have h_sub : N = N + 1 - 1 := by omega
    nth_rw 1 [h_sub]
    have eq_ico := (Finset.sum_Ico_eq_sum_range (fun i ↦ f i) 1 (N + 1)).symm
    have hc : (fun (k : ℕ) ↦ f (1 + k)) = (fun (k : ℕ) ↦ f (k + 1)) := by
      ext x
      rw [add_comm]
    rw [←hc]
    exact eq_ico
  have h3 : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [h1, h2, h3]

theorem sum_fin_fin_eq_sum_Icc_Icc (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ i : Fin N, ∑ j : Fin N, f (i.val + 1) (j.val + 1)) =
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, f h k := by
  have h1 : (∑ i : Fin N, ∑ j : Fin N, f (i.val + 1) (j.val + 1)) = ∑ i : Fin N, ∑ k ∈ Finset.Icc 1 N, f (i.val + 1) k := by
    apply Finset.sum_congr rfl
    intro i _
    exact sum_fin_eq_sum_Icc_one N (fun j ↦ f (i.val + 1) j)
  have h2 : (∑ i : Fin N, ∑ k ∈ Finset.Icc 1 N, f (i.val + 1) k) = ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, f h k := by
    exact sum_fin_eq_sum_Icc_one N (fun i ↦ ∑ k ∈ Finset.Icc 1 N, f i k)
  rw [h1, h2]

theorem cutoffMobiusLinearTerm_eq_sum (N : ℕ) :
    cutoffMobiusLinearTerm N =
      ∑ k ∈ Finset.Icc 1 N, cutoffMobiusCoeff N k * chiRhoKernel k := by
  unfold cutoffMobiusLinearTerm cutoffMobiusCoeff cutoffWeight chiRhoKernel
  rw [← sum_fin_eq_sum_Icc_one]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rfl

theorem cutoffMobiusQuadraticTerm_eq_double_sum (N : ℕ) :
    cutoffMobiusQuadraticTerm N =
      ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 N,
          cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * baezDuarteKernel h k := by
  unfold cutoffMobiusQuadraticTerm cutoffMobiusCoeff cutoffWeight baezDuarteKernel
  rw [← sum_fin_fin_eq_sum_Icc_Icc]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rfl

-- ---------------------------------------------------------------------------
-- 4. Kernel Energy Target
-- ---------------------------------------------------------------------------

noncomputable def cutoffMobiusEnergyKernel (N : ℕ) : ℝ :=
  1
    - 2 * (∑ k ∈ Finset.Icc 1 N, cutoffMobiusCoeff N k * chiRhoKernel k)
    + (∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 N,
          cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * baezDuarteKernel h k)

theorem cutoffMobiusEnergy_eq_kernel (N : ℕ) :
    coefficientEnergy cutoffMobiusCoefficientFamily N = cutoffMobiusEnergyKernel N := by
  rw [cutoffMobiusEnergy_decomposition]
  rw [cutoffMobiusLinearTerm_eq_sum]
  rw [cutoffMobiusQuadraticTerm_eq_double_sum]
  rfl

structure CutoffMobiusKernelEstimate where
  C : ℝ
  C_pos : 0 < C
  bound :
    ∀ N : ℕ,
      cutoffMobiusEnergyKernel N ≤ C / Real.log (N + 2 : ℝ)

def cutoffMobius_log_energy_of_kernel_estimate
    (H : CutoffMobiusKernelEstimate) :
    CutoffMobiusLogEnergyTarget :=
  { C := H.C
    C_pos := H.C_pos
    bound := fun N => by
      rw [cutoffMobiusEnergy_eq_kernel]
      exact H.bound N }

-- ---------------------------------------------------------------------------
-- 5. Explicit Kernel Formulas
-- ---------------------------------------------------------------------------

noncomputable def explicitChiRhoKernel (k : ℕ) : ℝ :=
  (Real.log (k : ℝ) + 1 - Real.eulerMascheroniConstant) / (k : ℝ)

noncomputable def explicitBaezDuarteKernel (h k : ℕ) : ℝ :=
  RH.Criteria.NymanBeurling.VasyuninGram.vasyuninBEntryFormula h k

theorem chiRhoKernel_eq_explicit
    {k : ℕ} (hk : 1 ≤ k) :
    chiRhoKernel k = explicitChiRhoKernel k := by
  unfold chiRhoKernel explicitChiRhoKernel
  rw [innerProductChiRho_formula (k - 1)]
  have h_cancel : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast Nat.sub_add_cancel hk
  rw [h_cancel]

theorem baezDuarteKernel_eq_explicit
    (H_vasyunin : RH.Criteria.NymanBeurling.VasyuninGram.VasyuninBridgeLocalDebts)
    {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) :
    baezDuarteKernel h k = explicitBaezDuarteKernel h k := by
  unfold baezDuarteKernel explicitBaezDuarteKernel
  rw [RH.Criteria.NymanBeurling.VasyuninGram.vasyuninBEntry_correct_of_local_debts H_vasyunin h k hh hk]
  rfl

noncomputable def explicitCutoffMobiusEnergyKernel (N : ℕ) : ℝ :=
  1
    - 2 * (∑ k ∈ Finset.Icc 1 N,
        cutoffMobiusCoeff N k * explicitChiRhoKernel k)
    + (∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 N,
          cutoffMobiusCoeff N h
            * cutoffMobiusCoeff N k
            * explicitBaezDuarteKernel h k)

theorem cutoffMobiusEnergyKernel_eq_explicit
    (H_vasyunin : RH.Criteria.NymanBeurling.VasyuninGram.VasyuninBridgeLocalDebts)
    (N : ℕ) :
    cutoffMobiusEnergyKernel N =
      explicitCutoffMobiusEnergyKernel N := by
  unfold cutoffMobiusEnergyKernel explicitCutoffMobiusEnergyKernel
  congr 1
  · congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [chiRhoKernel_eq_explicit hk.1]
  · apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.mem_Icc] at hh
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [baezDuarteKernel_eq_explicit H_vasyunin hh.1 hk.1]

structure ExplicitCutoffMobiusKernelEstimate where
  C : ℝ
  C_pos : 0 < C
  bound :
    ∀ N : ℕ,
      explicitCutoffMobiusEnergyKernel N
        ≤ C / Real.log (N + 2 : ℝ)

def cutoffMobius_kernel_estimate_of_explicit
    (H_vasyunin : RH.Criteria.NymanBeurling.VasyuninGram.VasyuninBridgeLocalDebts)
    (H : ExplicitCutoffMobiusKernelEstimate) :
    CutoffMobiusKernelEstimate := by
  refine ⟨H.C, H.C_pos, ?_⟩
  intro N
  rw [cutoffMobiusEnergyKernel_eq_explicit H_vasyunin]
  exact H.bound N


-- ---------------------------------------------------------------------------
-- 6. Explicit Components Decomposition (Phase 11H)
-- ---------------------------------------------------------------------------

noncomputable def explicitLinearLogComponent (N : ℕ) : ℝ :=
  - 2 * (∑ k ∈ Finset.Icc 1 N, cutoffMobiusCoeff N k * explicitChiRhoKernel k)

noncomputable def explicitQuadraticLogGammaComponent (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
      ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 * (1 / (h : ℝ) + 1 / (k : ℝ)))

noncomputable def explicitQuadraticLogRatioComponent (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
      (((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) * Real.log ((h : ℝ) / (k : ℝ)))

noncomputable def explicitQuadraticCotangentComponent (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
      (- (Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
        (RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula h k +
         RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula k h)))

noncomputable def explicitCutoffResidueComponent (_N : ℕ) : ℝ := 0

noncomputable def explicitCutoffMobiusComponentSum (N : ℕ) : ℝ :=
  1
    + explicitLinearLogComponent N
    + explicitQuadraticLogGammaComponent N
    + explicitQuadraticLogRatioComponent N
    + explicitQuadraticCotangentComponent N
    + explicitCutoffResidueComponent N

theorem explicitCutoffMobiusEnergyKernel_eq_components (N : ℕ) :
    explicitCutoffMobiusEnergyKernel N = explicitCutoffMobiusComponentSum N := by
  unfold explicitCutoffMobiusEnergyKernel explicitCutoffMobiusComponentSum
  unfold explicitLinearLogComponent explicitQuadraticLogGammaComponent
  unfold explicitQuadraticLogRatioComponent explicitQuadraticCotangentComponent
  unfold explicitCutoffResidueComponent
  unfold explicitBaezDuarteKernel RH.Criteria.NymanBeurling.VasyuninGram.vasyuninBEntryFormula
  have h_quad : (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
        ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 * (1 / (h : ℝ) + 1 / (k : ℝ)) +
          ((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) * Real.log ((h : ℝ) / (k : ℝ)) -
          Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
            (RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula h k +
              RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula k h))) =
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
        ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 * (1 / (h : ℝ) + 1 / (k : ℝ)))) +
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
        (((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) * Real.log ((h : ℝ) / (k : ℝ)))) +
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
        (- (Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
          (RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula h k +
           RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula k h)))) := by
    have h1 : (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
          ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 * (1 / (h : ℝ) + 1 / (k : ℝ)) +
            ((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) * Real.log ((h : ℝ) / (k : ℝ)) -
            Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
              (RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula h k +
                RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula k h))) =
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 * (1 / (h : ℝ) + 1 / (k : ℝ))) +
         cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * (((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) * Real.log ((h : ℝ) / (k : ℝ))) +
         cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * (- (Real.pi / (2 * (h : ℝ) * (k : ℝ)) * (RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula h k + RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula k h)))) := by
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h1]
    simp_rw [Finset.sum_add_distrib]
  rw [h_quad]
  ring

structure ExplicitCutoffMobiusComponentEstimates where
  C : ℝ
  C_pos : 0 < C
  bound_components :
    ∀ N : ℕ,
      explicitCutoffMobiusComponentSum N
        ≤ C / Real.log (N + 2 : ℝ)

def explicit_kernel_estimate_of_component_estimates
    (H : ExplicitCutoffMobiusComponentEstimates) :
    ExplicitCutoffMobiusKernelEstimate := by
  refine ⟨H.C, H.C_pos, ?_⟩
  intro N
  rw [explicitCutoffMobiusEnergyKernel_eq_components]
  exact H.bound_components N

noncomputable def explicitQuadraticTotalComponent (N : ℕ) : ℝ :=
  explicitQuadraticLogGammaComponent N
    + explicitQuadraticLogRatioComponent N
    + explicitQuadraticCotangentComponent N
    + explicitCutoffResidueComponent N

noncomputable def explicitLinearCenteredRemainder (N : ℕ) : ℝ :=
  explicitLinearLogComponent N + 2

noncomputable def explicitQuadraticCenteredRemainder (N : ℕ) : ℝ :=
  explicitQuadraticTotalComponent N - 1

noncomputable def explicitTotalCenteredRemainder (N : ℕ) : ℝ :=
  explicitLinearCenteredRemainder N
    + explicitQuadraticCenteredRemainder N

theorem explicitCutoffMobiusComponentSum_eq_centered_remainders
    (N : ℕ) :
    explicitCutoffMobiusComponentSum N =
      explicitTotalCenteredRemainder N := by
  unfold explicitCutoffMobiusComponentSum
  unfold explicitTotalCenteredRemainder
  unfold explicitLinearCenteredRemainder
  unfold explicitQuadraticCenteredRemainder
  unfold explicitQuadraticTotalComponent
  ring

structure CenteredCutoffMobiusSplitEstimates where
  C_linear : ℝ
  C_quadratic : ℝ
  C_pos : 0 < C_linear + C_quadratic
  linear_bound :
    ∀ N : ℕ,
      |explicitLinearCenteredRemainder N|
        ≤ C_linear / Real.log (N + 2 : ℝ)
  quadratic_bound :
    ∀ N : ℕ,
      |explicitQuadraticCenteredRemainder N|
        ≤ C_quadratic / Real.log (N + 2 : ℝ)

def explicit_component_estimate_of_centered_split_estimates
    (H : CenteredCutoffMobiusSplitEstimates) :
    ExplicitCutoffMobiusComponentEstimates := by
  refine ⟨H.C_linear + H.C_quadratic, H.C_pos, ?_⟩
  intro N
  rw [explicitCutoffMobiusComponentSum_eq_centered_remainders]
  unfold explicitTotalCenteredRemainder
  have hlin := H.linear_bound N
  have hquad := H.quadratic_bound N
  have h1 : explicitLinearCenteredRemainder N ≤ H.C_linear / Real.log (N + 2 : ℝ) :=
    le_trans (le_abs_self _) hlin
  have h2 : explicitQuadraticCenteredRemainder N ≤ H.C_quadratic / Real.log (N + 2 : ℝ) :=
    le_trans (le_abs_self _) hquad
  have h3 : explicitLinearCenteredRemainder N + explicitQuadraticCenteredRemainder N ≤ H.C_linear / Real.log (N + 2 : ℝ) + H.C_quadratic / Real.log (N + 2 : ℝ) := add_le_add h1 h2
  have h4 : H.C_linear / Real.log (N + 2 : ℝ) + H.C_quadratic / Real.log (N + 2 : ℝ) = (H.C_linear + H.C_quadratic) / Real.log (N + 2 : ℝ) := by ring
  rwa [h4] at h3

structure CenteredCutoffMobiusGlobalEstimate where
  C : ℝ
  C_pos : 0 < C
  centered_bound :
    ∀ N : ℕ,
      explicitTotalCenteredRemainder N
        ≤ C / Real.log (N + 2 : ℝ)

def explicit_component_estimate_of_centered_global_estimate
    (H : CenteredCutoffMobiusGlobalEstimate) :
    ExplicitCutoffMobiusComponentEstimates := by
  refine ⟨H.C, H.C_pos, ?_⟩
  intro N
  rw [explicitCutoffMobiusComponentSum_eq_centered_remainders]
  exact H.centered_bound N

noncomputable def explicitQuadraticLogCotangentInteraction (N : ℕ) : ℝ :=
  explicitQuadraticLogRatioComponent N
    + explicitQuadraticCotangentComponent N

noncomputable def explicitQuadraticInteractionRemainder (N : ℕ) : ℝ :=
  explicitQuadraticLogCotangentInteraction N - 1

noncomputable def explicitLinearMobiusSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (1 - (k : ℝ) / ((N + 1 : ℕ) : ℝ)) *
      ((Real.log (k : ℝ) + 1 - Real.eulerMascheroniConstant) / (k : ℝ))

theorem explicitLinearCenteredRemainder_eq_sum (N : ℕ) :
    explicitLinearCenteredRemainder N =
      2 * (explicitLinearMobiusSum N + 1) := by
  unfold explicitLinearCenteredRemainder explicitLinearLogComponent explicitLinearMobiusSum
  unfold cutoffMobiusCoeff cutoffWeight explicitChiRhoKernel
  have h1 : (∑ k ∈ Finset.Icc 1 N,
      -((ArithmeticFunction.moebius k : ℤ) : ℝ) * (1 - (k : ℝ) / ((N + 1 : ℕ) : ℝ)) *
        ((Real.log (k : ℝ) + 1 - Real.eulerMascheroniConstant) / (k : ℝ))) =
    - ∑ k ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (1 - (k : ℝ) / ((N + 1 : ℕ) : ℝ)) *
        ((Real.log (k : ℝ) + 1 - Real.eulerMascheroniConstant) / (k : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h1]
  ring

structure LinearMobiusCenteredEstimate where
  C : ℝ
  C_pos : 0 < C
  bound :
    ∀ N : ℕ,
      |explicitLinearMobiusSum N + 1|
        ≤ C / Real.log (N + 2 : ℝ)

def linear_centered_remainder_bound_of_mobius_estimate
    (H : LinearMobiusCenteredEstimate) :
    ∃ C > 0, ∀ N, |explicitLinearCenteredRemainder N| ≤ C / Real.log (N + 2 : ℝ) := by
  use 2 * H.C
  constructor
  · linarith [H.C_pos]
  · intro N
    rw [explicitLinearCenteredRemainder_eq_sum]
    have h := H.bound N
    rw [abs_mul, abs_two]
    calc
      2 * |explicitLinearMobiusSum N + 1| ≤ 2 * (H.C / Real.log (N + 2 : ℝ)) := by linarith
      _ = (2 * H.C) / Real.log (N + 2 : ℝ) := by ring

noncomputable def cutoffMobiusOverKSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ)
      * (1 - (k : ℝ) / ((N + 1 : ℕ) : ℝ))
      / (k : ℝ)

noncomputable def cutoffMobiusLogOverKSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ)
      * (1 - (k : ℝ) / ((N + 1 : ℕ) : ℝ))
      * Real.log (k : ℝ)
      / (k : ℝ)

theorem explicitLinearMobiusSum_eq_dirichlet_pieces
    (N : ℕ) :
    explicitLinearMobiusSum N =
      cutoffMobiusLogOverKSum N
        + (1 - Real.eulerMascheroniConstant)
            * cutoffMobiusOverKSum N := by
  unfold explicitLinearMobiusSum cutoffMobiusLogOverKSum cutoffMobiusOverKSum
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

structure LinearMobiusDirichletEstimates where
  C_log : ℝ
  C_overK : ℝ
  C_pos : 0 < C_log + |1 - Real.eulerMascheroniConstant| * C_overK
  log_bound :
    ∀ N : ℕ,
      |cutoffMobiusLogOverKSum N + 1|
        ≤ C_log / Real.log (N + 2 : ℝ)
  overK_bound :
    ∀ N : ℕ,
      |cutoffMobiusOverKSum N|
        ≤ C_overK / Real.log (N + 2 : ℝ)

noncomputable def linear_mobius_centered_estimate_of_dirichlet_estimates
    (H : LinearMobiusDirichletEstimates) :
    LinearMobiusCenteredEstimate := by
  refine ⟨H.C_log + |1 - Real.eulerMascheroniConstant| * H.C_overK, H.C_pos, ?_⟩
  intro N
  rw [explicitLinearMobiusSum_eq_dirichlet_pieces]
  have hlog := H.log_bound N
  have hk := H.overK_bound N
  have h1 : |cutoffMobiusLogOverKSum N + (1 - Real.eulerMascheroniConstant) * cutoffMobiusOverKSum N + 1| =
            |cutoffMobiusLogOverKSum N + 1 + (1 - Real.eulerMascheroniConstant) * cutoffMobiusOverKSum N| := by
    congr 1; ring
  rw [h1]
  have h2 := abs_add_le (cutoffMobiusLogOverKSum N + 1) ((1 - Real.eulerMascheroniConstant) * cutoffMobiusOverKSum N)
  have h3 : |(1 - Real.eulerMascheroniConstant) * cutoffMobiusOverKSum N| = |1 - Real.eulerMascheroniConstant| * |cutoffMobiusOverKSum N| := abs_mul _ _
  rw [h3] at h2
  have h4 : |1 - Real.eulerMascheroniConstant| * |cutoffMobiusOverKSum N| ≤ |1 - Real.eulerMascheroniConstant| * (H.C_overK / Real.log (N + 2 : ℝ)) := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
  have h5 : |cutoffMobiusLogOverKSum N + 1| + |1 - Real.eulerMascheroniConstant| * |cutoffMobiusOverKSum N| ≤ H.C_log / Real.log (N + 2 : ℝ) + |1 - Real.eulerMascheroniConstant| * (H.C_overK / Real.log (N + 2 : ℝ)) := add_le_add hlog h4
  have h6 : H.C_log / Real.log (N + 2 : ℝ) + |1 - Real.eulerMascheroniConstant| * (H.C_overK / Real.log (N + 2 : ℝ)) = (H.C_log + |1 - Real.eulerMascheroniConstant| * H.C_overK) / Real.log (N + 2 : ℝ) := by ring
  linarith

theorem explicitQuadraticCenteredRemainder_eq_interaction_parts
    (N : ℕ) :
    explicitQuadraticCenteredRemainder N =
      explicitQuadraticLogGammaComponent N
        + explicitQuadraticInteractionRemainder N
        + explicitCutoffResidueComponent N := by
  unfold explicitQuadraticCenteredRemainder
  unfold explicitQuadraticTotalComponent
  unfold explicitQuadraticInteractionRemainder
  unfold explicitQuadraticLogCotangentInteraction
  ring

structure QuadraticInteractionEstimates where
  C_loggamma : ℝ
  C_interaction : ℝ
  C_residue : ℝ

  C_pos :
    0 < C_loggamma + C_interaction + C_residue

  loggamma_bound :
    ∀ N : ℕ,
      |explicitQuadraticLogGammaComponent N|
        ≤ C_loggamma / Real.log (N + 2 : ℝ)

  interaction_bound :
    ∀ N : ℕ,
      |explicitQuadraticInteractionRemainder N|
        ≤ C_interaction / Real.log (N + 2 : ℝ)

  residue_bound :
    ∀ N : ℕ,
      |explicitCutoffResidueComponent N|
        ≤ C_residue / Real.log (N + 2 : ℝ)

noncomputable def quadratic_centered_estimate_of_interaction_estimates
    (H : QuadraticInteractionEstimates) :
    ∃ C > 0,
      ∀ N : ℕ,
        |explicitQuadraticCenteredRemainder N|
          ≤ C / Real.log (N + 2 : ℝ) := by
  use H.C_loggamma + H.C_interaction + H.C_residue
  constructor
  · exact H.C_pos
  · intro N
    rw [explicitQuadraticCenteredRemainder_eq_interaction_parts]
    have h1 : |explicitQuadraticLogGammaComponent N + explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N|
              = |explicitQuadraticLogGammaComponent N + (explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N)| := by
      congr 1; ring
    rw [h1]
    have h2 := abs_add_le (explicitQuadraticLogGammaComponent N + explicitQuadraticInteractionRemainder N) (explicitCutoffResidueComponent N)
    have h3 := abs_add_le (explicitQuadraticLogGammaComponent N) (explicitQuadraticInteractionRemainder N)
    have hlG := H.loggamma_bound N
    have hint := H.interaction_bound N
    have hres := H.residue_bound N
    calc
      |explicitQuadraticLogGammaComponent N + (explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N)|
        ≤ |explicitQuadraticLogGammaComponent N| + |explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N| := abs_add_le _ _
      _ ≤ |explicitQuadraticLogGammaComponent N| + (|explicitQuadraticInteractionRemainder N| + |explicitCutoffResidueComponent N|) := add_le_add (le_refl _) (abs_add_le _ _)
      _ = |explicitQuadraticLogGammaComponent N| + |explicitQuadraticInteractionRemainder N| + |explicitCutoffResidueComponent N| := by ring
      _ ≤ (H.C_loggamma / Real.log (N + 2 : ℝ)) + (H.C_interaction / Real.log (N + 2 : ℝ)) + (H.C_residue / Real.log (N + 2 : ℝ)) := add_le_add (add_le_add hlG hint) hres
      _ = (H.C_loggamma + H.C_interaction + H.C_residue) / Real.log (N + 2 : ℝ) := by ring

noncomputable def centered_split_estimates_of_linear_and_quadratic
    (HL : LinearMobiusCenteredEstimate)
    (HQ : QuadraticInteractionEstimates) :
    CenteredCutoffMobiusSplitEstimates := by
  refine ⟨2 * HL.C, HQ.C_loggamma + HQ.C_interaction + HQ.C_residue, ?_, ?_, ?_⟩
  · have h1 := HL.C_pos
    have h2 := HQ.C_pos
    linarith
  · intro N
    rw [explicitLinearCenteredRemainder_eq_sum]
    have h := HL.bound N
    rw [abs_mul, abs_two]
    calc
      2 * |explicitLinearMobiusSum N + 1| ≤ 2 * (HL.C / Real.log (N + 2 : ℝ)) := by linarith
      _ = (2 * HL.C) / Real.log (N + 2 : ℝ) := by ring
  · intro N
    rw [explicitQuadraticCenteredRemainder_eq_interaction_parts]
    have h1 : |explicitQuadraticLogGammaComponent N + explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N|
              = |explicitQuadraticLogGammaComponent N + (explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N)| := by
      congr 1; ring
    rw [h1]
    have h2 := abs_add_le (explicitQuadraticLogGammaComponent N + explicitQuadraticInteractionRemainder N) (explicitCutoffResidueComponent N)
    have h3 := abs_add_le (explicitQuadraticLogGammaComponent N) (explicitQuadraticInteractionRemainder N)
    have hlG := HQ.loggamma_bound N
    have hint := HQ.interaction_bound N
    have hres := HQ.residue_bound N
    calc
      |explicitQuadraticLogGammaComponent N + (explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N)|
        ≤ |explicitQuadraticLogGammaComponent N| + |explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N| := abs_add_le _ _
      _ ≤ |explicitQuadraticLogGammaComponent N| + (|explicitQuadraticInteractionRemainder N| + |explicitCutoffResidueComponent N|) := add_le_add (le_refl _) (abs_add_le _ _)
      _ = |explicitQuadraticLogGammaComponent N| + |explicitQuadraticInteractionRemainder N| + |explicitCutoffResidueComponent N| := by ring
      _ ≤ (HQ.C_loggamma / Real.log (N + 2 : ℝ)) + (HQ.C_interaction / Real.log (N + 2 : ℝ)) + (HQ.C_residue / Real.log (N + 2 : ℝ)) := add_le_add (add_le_add hlG hint) hres
      _ = (HQ.C_loggamma + HQ.C_interaction + HQ.C_residue) / Real.log (N + 2 : ℝ) := by ring

-- ---------------------------------------------------------------------------
-- 7. Final Conditional Synthesis (Phase 11L)
-- ---------------------------------------------------------------------------

theorem baezDuarteCriterion_of_linear_dirichlet_and_quadratic_interaction_estimates
    (H_vasyunin : RH.Criteria.NymanBeurling.VasyuninGram.VasyuninBridgeLocalDebts)
    (HL : LinearMobiusDirichletEstimates)
    (HQ : QuadraticInteractionEstimates) :
    BaezDuarteCriterion := by
  have Hsplit :
      CenteredCutoffMobiusSplitEstimates :=
    centered_split_estimates_of_linear_and_quadratic
      (linear_mobius_centered_estimate_of_dirichlet_estimates HL)
      HQ

  have Hcomponents :
      ExplicitCutoffMobiusComponentEstimates :=
    explicit_component_estimate_of_centered_split_estimates Hsplit

  have Hexplicit :
      ExplicitCutoffMobiusKernelEstimate :=
    explicit_kernel_estimate_of_component_estimates Hcomponents

  have Hkernel :
      CutoffMobiusKernelEstimate :=
    cutoffMobius_kernel_estimate_of_explicit H_vasyunin Hexplicit

  have Hlog :
      CutoffMobiusLogEnergyTarget :=
    cutoffMobius_log_energy_of_kernel_estimate Hkernel

  exact baezDuarteCriterion_of_cutoffMobius_log_energy Hlog

theorem RH_of_linear_dirichlet_and_quadratic_interaction_estimates
    (debt : NymanBeurlingRHBridgeDebts)
    (H_vasyunin : RH.Criteria.NymanBeurling.VasyuninGram.VasyuninBridgeLocalDebts)
    (HL : LinearMobiusDirichletEstimates)
    (HQ : QuadraticInteractionEstimates) :
    RH.Basic.RiemannHypothesis := by
  exact baez_duarte_criterion_implies_RH debt
    (baezDuarteCriterion_of_linear_dirichlet_and_quadratic_interaction_estimates H_vasyunin HL HQ)

end RH.Criteria.NymanBeurling.CutoffMobiusKernels
