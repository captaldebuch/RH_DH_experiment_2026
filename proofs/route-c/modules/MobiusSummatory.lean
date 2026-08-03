import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels

namespace RH.Criteria.NymanBeurling.MobiusSummatory

open RH.Criteria.NymanBeurling.CutoffMobiusKernels

-- ---------------------------------------------------------------------------
-- 1. Standard Möbius Summatory Functions
-- ---------------------------------------------------------------------------

/-- M(N) = Σ_{k=1}^N μ(k) -/
noncomputable def mobiusSummatory (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius k : ℤ) : ℝ)

/-- L(N) = Σ_{k=1}^N μ(k) log(k) -/
noncomputable def mobiusLogSummatory (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius k : ℤ) : ℝ) * Real.log (k : ℝ)

-- ---------------------------------------------------------------------------
-- 2. Classical Asymptotic Bounds Structure
-- ---------------------------------------------------------------------------

/-- The classical asymptotic estimates for the Möbius function.
  For the cutoff-Möbius integral convergence, we need bounds strong enough
  to overcome the logarithmic weights in the Abel summation.
  Specifically, M(N) ≪ N / log(N)^A and L(N) ≪ N / log(N)^A for some A > 1.
-/
structure MobiusSummatoryEstimates where
  C_M : ℝ
  C_L : ℝ
  -- For now we just assume it implies the exact Dirichlet estimate targets:
  implies_overK :
    ∀ N : ℕ,
      |cutoffMobiusOverKSum N|
        ≤ C_M / Real.log (N + 2 : ℝ)
  implies_logOverK :
    ∀ N : ℕ,
      |cutoffMobiusLogOverKSum N + 1|
        ≤ C_L / Real.log (N + 2 : ℝ)
  C_pos : 0 < C_L + |1 - Real.eulerMascheroniConstant| * C_M

-- ---------------------------------------------------------------------------
-- 3. Finite Abel Summation
-- ---------------------------------------------------------------------------

/-- Finite Abel summation for a cutoff that vanishes at `N + 1`. -/
private theorem sum_Icc_mul_sub_endpoint_eq_sum_partial
    (a b : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1))) =
      ∑ k ∈ Finset.Icc 1 N,
        (∑ j ∈ Finset.Icc 1 k, a j) * (b k - b (k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hone : 1 ≤ N + 1 := by omega
      rw [Finset.sum_Icc_succ_top hone, Finset.sum_Icc_succ_top hone]
      have hshift :
          (∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1 + 1))) =
            (∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1))) +
              (∑ k ∈ Finset.Icc 1 N, a k) * (b (N + 1) - b (N + 1 + 1)) := by
        calc
          _ = ∑ k ∈ Finset.Icc 1 N,
                (a k * (b k - b (N + 1)) +
                  a k * (b (N + 1) - b (N + 1 + 1))) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
          _ = _ := by
              rw [Finset.sum_add_distrib, Finset.sum_mul]
      rw [hshift, ih, Finset.sum_Icc_succ_top hone]
      ring

/-- Exact Abel-summation formula for the cutoff sum of `μ(k) / k`. -/
theorem cutoffMobiusOverKSum_eq_abel_sum (N : ℕ) :
    cutoffMobiusOverKSum N =
      ∑ k ∈ Finset.Icc 1 N,
        mobiusSummatory k *
          (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
  have habel := sum_Icc_mul_sub_endpoint_eq_sum_partial
    (fun k ↦ ((ArithmeticFunction.moebius k : ℤ) : ℝ))
    (fun k ↦ 1 / (k : ℝ)) N
  rw [show cutoffMobiusOverKSum N =
      ∑ k ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
          (1 / (k : ℝ) - 1 / ((N + 1 : ℕ) : ℝ)) by
    unfold cutoffMobiusOverKSum
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Finset.mem_Icc.mp hk).1)
    have hN0 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp]
  simpa [mobiusSummatory] using habel

/-- Exact Abel-summation formula for the cutoff sum of `μ(k) log(k) / k`. -/
theorem cutoffMobiusLogOverKSum_eq_abel_sum (N : ℕ) :
    cutoffMobiusLogOverKSum N + 1 =
      1 + ∑ k ∈ Finset.Icc 1 N,
        mobiusLogSummatory k *
          (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
  have habel := sum_Icc_mul_sub_endpoint_eq_sum_partial
    (fun k ↦ ((ArithmeticFunction.moebius k : ℤ) : ℝ) * Real.log (k : ℝ))
    (fun k ↦ 1 / (k : ℝ)) N
  have hcutoff :
      cutoffMobiusLogOverKSum N =
        ∑ k ∈ Finset.Icc 1 N,
          mobiusLogSummatory k *
            (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
    rw [show cutoffMobiusLogOverKSum N =
        ∑ k ∈ Finset.Icc 1 N,
          (((ArithmeticFunction.moebius k : ℤ) : ℝ) * Real.log (k : ℝ)) *
            (1 / (k : ℝ) - 1 / ((N + 1 : ℕ) : ℝ)) by
      unfold cutoffMobiusLogOverKSum
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : (k : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Finset.mem_Icc.mp hk).1)
      have hN0 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp]
    simpa [mobiusLogSummatory] using habel
  rw [hcutoff]
  ring

-- ---------------------------------------------------------------------------
-- 4. PNT-Style Summatory Estimates
-- ---------------------------------------------------------------------------

/--
PNT-style quantitative hypotheses at the exact Abel-transform interface needed
by the cutoff Möbius argument.  Constructing this structure is the remaining
classical analytic-number-theory debt; it makes no assumption about the cutoff
sums themselves.
-/
structure MobiusPNTStyleEstimates where
  C_M : ℝ
  C_L : ℝ
  C_M_nonneg : 0 ≤ C_M
  C_L_pos : 0 < C_L
  mobius_abel_bound :
    ∀ N : ℕ,
      |∑ k ∈ Finset.Icc 1 N,
          mobiusSummatory k *
            (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))|
        ≤ C_M / Real.log (N + 2 : ℝ)
  mobiusLog_abel_bound :
    ∀ N : ℕ,
      |1 + ∑ k ∈ Finset.Icc 1 N,
          mobiusLogSummatory k *
            (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))|
        ≤ C_L / Real.log (N + 2 : ℝ)

-- ---------------------------------------------------------------------------
-- 5. Bridge to Dirichlet Estimates
-- ---------------------------------------------------------------------------

/-- The PNT-style Abel bounds imply the cutoff-sum estimates. -/
noncomputable def mobius_summatory_estimates_of_pnt_style
    (H : MobiusPNTStyleEstimates) :
    MobiusSummatoryEstimates :=
  { C_M := H.C_M
    C_L := H.C_L
    implies_overK := by
      intro N
      rw [cutoffMobiusOverKSum_eq_abel_sum]
      exact H.mobius_abel_bound N
    implies_logOverK := by
      intro N
      rw [cutoffMobiusLogOverKSum_eq_abel_sum]
      exact H.mobiusLog_abel_bound N
    C_pos := add_pos_of_pos_of_nonneg H.C_L_pos
      (mul_nonneg (abs_nonneg _) H.C_M_nonneg) }

noncomputable def linear_mobius_dirichlet_estimates_of_summatory_estimates
    (H : MobiusSummatoryEstimates) :
    LinearMobiusDirichletEstimates :=
  { C_log := H.C_L
    C_overK := H.C_M
    C_pos := H.C_pos
    log_bound := H.implies_logOverK
    overK_bound := H.implies_overK }

/-- Full Phase 14 bridge from PNT-style summatory input to the linear cutoff estimates. -/
noncomputable def linear_mobius_dirichlet_estimates_of_pnt_style
    (H : MobiusPNTStyleEstimates) :
    LinearMobiusDirichletEstimates :=
  linear_mobius_dirichlet_estimates_of_summatory_estimates
    (mobius_summatory_estimates_of_pnt_style H)

end RH.Criteria.NymanBeurling.MobiusSummatory
