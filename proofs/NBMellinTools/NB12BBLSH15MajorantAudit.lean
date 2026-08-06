/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15Rectangle

/-!
# NB12u: exponent audit for an H15 vertical majorant

The adaptive Abel parameter is small enough to kill the additional residue,
but its complex power behaves in opposite ways on the two sides of the
reflected rectangle.  This file proves that sign split exactly.

For `Re(s) >= 0`, the factor `delta_n^s` is bounded above by
`(n+1)^(-Re(s))`.  For `Re(s) <= 0`, the inequality reverses: the same factor
is bounded *below* by the corresponding power.  Consequently an absolute
uniform majorant on the reflected left line cannot come from Gamma decay and
the Abel factor alone; signed arithmetic cancellation must compensate for the
amplification.
-/

open scoped Topology
open Complex Filter MeasureTheory

namespace NBMellinTools.NB12

theorem h15ContourDamping_le_one_div (n : ℕ) :
    h15ContourDamping n ≤ 1 / ((n + 1 : ℕ) : ℝ) :=
  bblsAdaptiveResidueDamping_le n (h15AdditionalResidueAmplitude n)

theorem h15ContourDamping_le_one (n : ℕ) :
    h15ContourDamping n ≤ 1 := by
  calc
    h15ContourDamping n ≤ 1 / ((n + 1 : ℕ) : ℝ) :=
      h15ContourDamping_le_one_div n
    _ ≤ 1 := by
      have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact (div_le_one (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))).2 hn

/-- Exact norm of the moving Abel complex power; the imaginary coordinate
does not affect it. -/
theorem norm_h15ContourDamping_cpow (n : ℕ) (σ t : ℝ) :
    ‖(h15ContourDamping n : ℂ) ^
        ((σ : ℂ) + (t : ℂ) * I)‖ =
      h15ContourDamping n ^ σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (h15ContourDamping_pos n)]
  simp [Complex.mul_re]

/-- On nonnegative reflected lines, adaptive damping supplies an explicit
decaying power of the H15 cutoff. -/
theorem norm_h15ContourDamping_cpow_le_of_nonneg
    (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    ‖(h15ContourDamping n : ℂ) ^
        ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      (1 / ((n + 1 : ℕ) : ℝ)) ^ σ := by
  rw [norm_h15ContourDamping_cpow]
  exact Real.rpow_le_rpow
    (le_of_lt (h15ContourDamping_pos n))
    (h15ContourDamping_le_one_div n) hσ

/-- On nonpositive reflected lines the Abel power is amplified, not damped.
This is the formal stop test for a termwise `N`-uniform left-line majorant. -/
theorem one_div_rpow_le_norm_h15ContourDamping_cpow_of_nonpos
    (n : ℕ) {σ : ℝ} (hσ : σ ≤ 0) (t : ℝ) :
    (1 / ((n + 1 : ℕ) : ℝ)) ^ σ ≤
      ‖(h15ContourDamping n : ℂ) ^
        ((σ : ℂ) + (t : ℂ) * I)‖ := by
  rw [norm_h15ContourDamping_cpow]
  exact Real.rpow_le_rpow_of_nonpos
    (h15ContourDamping_pos n)
    (h15ContourDamping_le_one_div n) hσ

/-- Concrete half-line version used by the reflected contour. -/
theorem one_div_rpow_neg_half_le_norm_h15ContourDamping_cpow
    (n : ℕ) (t : ℝ) :
    (1 / ((n + 1 : ℕ) : ℝ)) ^ (-1 / 2 : ℝ) ≤
      ‖(h15ContourDamping n : ℂ) ^
        ((-1 / 2 : ℝ) + (t : ℂ) * I)‖ := by
  exact one_div_rpow_le_norm_h15ContourDamping_cpow_of_nonpos
    n (by norm_num) t

/-! ## Correct split of the remaining analytic input -/

/-- A modulus-explicit row bound on a positive reflected line.  Its cutoff
exponent is deliberately visible so it can be compared with the damping gain
instead of being hidden inside an unspecified constant. -/
structure H15PositiveLineRowGrowth where
  σ : ℝ
  sigma_pos : 0 < σ
  sigma_lt_two : σ < 2
  modulusExponent : ℕ
  tExponent : ℕ
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound : ∀ (n : ℕ) (i : H15LaurentRowIndex (NB8.logTaperLength n)) (t : ℝ),
    ‖bblsActiveReflectedExpression (h15ContourDamping n)
        (h15LaurentRow i).numerator (h15LaurentRow i).denominator
        ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      constant * ((h15LaurentRow i).denominator : ℝ) ^ modulusExponent *
        (1 / ((n + 1 : ℕ) : ℝ)) ^ σ *
        bblsPolynomialExponentialMajorant tExponent (Real.pi / 2) t

namespace H15PositiveLineRowGrowth

/-- The exact absolute arithmetic mass left after the common Abel and
archimedean factors have been removed from the finite H15 row family. -/
noncomputable def arithmeticMass
    (H : H15PositiveLineRowGrowth) (n : ℕ) : ℝ :=
  ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
    ‖h15LaurentRowWeight i‖ *
      ((h15LaurentRow i).denominator : ℝ) ^ H.modulusExponent

theorem arithmeticMass_nonneg
    (H : H15PositiveLineRowGrowth) (n : ℕ) :
    0 ≤ H.arithmeticMass n := by
  unfold arithmeticMass
  positivity

/-- The common integrable vertical profile supplied by Gamma decay. -/
noncomputable def verticalProfile
    (H : H15PositiveLineRowGrowth) (t : ℝ) : ℝ :=
  bblsPolynomialExponentialMajorant H.tExponent (Real.pi / 2) t

theorem verticalProfile_nonneg
    (H : H15PositiveLineRowGrowth) (t : ℝ) :
    0 ≤ H.verticalProfile t := by
  unfold verticalProfile bblsPolynomialExponentialMajorant
  positivity

theorem integrable_verticalProfile (H : H15PositiveLineRowGrowth) :
    Integrable H.verticalProfile := by
  unfold verticalProfile
  exact integrable_bblsPolynomialExponentialMajorant H.tExponent
    (by positivity : 0 < Real.pi / 2)

/-- Factored majorant for the complete finite aggregate.  The first three
factors are the precise cutoff/modulus budget; the last factor is integrable
in the vertical variable. -/
noncomputable def aggregateMajorant
    (H : H15PositiveLineRowGrowth) (n : ℕ) (t : ℝ) : ℝ :=
  H.constant * (1 / ((n + 1 : ℕ) : ℝ)) ^ H.σ *
    H.arithmeticMass n * H.verticalProfile t

theorem aggregateMajorant_nonneg
    (H : H15PositiveLineRowGrowth) (n : ℕ) (t : ℝ) :
    0 ≤ H.aggregateMajorant n t := by
  unfold aggregateMajorant
  have hbase : 0 ≤ (1 / ((n + 1 : ℕ) : ℝ)) := by positivity
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg H.constant_nonneg (Real.rpow_nonneg hbase H.σ))
      (H.arithmeticMass_nonneg n))
    (H.verticalProfile_nonneg t)

theorem integrable_aggregateMajorant
    (H : H15PositiveLineRowGrowth) (n : ℕ) :
    Integrable (H.aggregateMajorant n) := by
  unfold aggregateMajorant
  exact H.integrable_verticalProfile.const_mul
    (H.constant * (1 / ((n + 1 : ℕ) : ℝ)) ^ H.σ *
      H.arithmeticMass n)

/-- Finite triangle inequality followed by the row-growth package.  This is
the strongest unconditional aggregation step available before estimating
the arithmetic mass. -/
theorem norm_h15ActiveContourAggregate_le_aggregateMajorant
    (H : H15PositiveLineRowGrowth) (n : ℕ) (t : ℝ) :
    ‖h15ActiveContourAggregate n
        ((H.σ : ℂ) + (t : ℂ) * I)‖ ≤
      H.aggregateMajorant n t := by
  classical
  unfold h15ActiveContourAggregate bblsFiniteActiveAggregate
  calc
    ‖∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
        h15LaurentRowWeight i *
          bblsActiveReflectedExpression (h15ContourDamping n)
            (h15LaurentRow i).numerator (h15LaurentRow i).denominator
            ((H.σ : ℂ) + (t : ℂ) * I)‖ ≤
      ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
        ‖h15LaurentRowWeight i *
          bblsActiveReflectedExpression (h15ContourDamping n)
            (h15LaurentRow i).numerator (h15LaurentRow i).denominator
            ((H.σ : ℂ) + (t : ℂ) * I)‖ := norm_sum_le _ _
    _ ≤ ∑ i : H15LaurentRowIndex (NB8.logTaperLength n),
        ‖h15LaurentRowWeight i‖ *
          (H.constant * ((h15LaurentRow i).denominator : ℝ) ^
              H.modulusExponent *
            (1 / ((n + 1 : ℕ) : ℝ)) ^ H.σ *
            H.verticalProfile t) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (H.bound n i t) (norm_nonneg _)
    _ = H.aggregateMajorant n t := by
      unfold aggregateMajorant arithmeticMass verticalProfile
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The sole arithmetic exponent test left by the absolute positive-line
argument.  It asks whether Abel cutoff decay absorbs the total weighted
modulus mass of the growing H15 family. -/
structure CutoffBudget (H : H15PositiveLineRowGrowth) where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound : ∀ n : ℕ,
    H.constant * (1 / ((n + 1 : ℕ) : ℝ)) ^ H.σ *
      H.arithmeticMass n ≤ constant

/-- Once the explicit cutoff budget is supplied, the row estimate produces
a genuine cutoff-uniform integrable envelope on that positive line. -/
theorem activeIntegrableMajorantAt_of_cutoffBudget
    (H : H15PositiveLineRowGrowth) (B : H.CutoffBudget) :
    H15ActiveIntegrableMajorantAt H.σ := by
  refine ⟨0, fun t => B.constant * H.verticalProfile t,
    (H.integrable_verticalProfile.const_mul B.constant), ?_, ?_⟩
  · intro t
    exact mul_nonneg B.constant_nonneg (H.verticalProfile_nonneg t)
  · intro n _hn t
    calc
      ‖h15ActiveContourAggregate n
          ((H.σ : ℂ) + (t : ℂ) * I)‖ ≤
        H.aggregateMajorant n t :=
          H.norm_h15ActiveContourAggregate_le_aggregateMajorant n t
      _ ≤ B.constant * H.verticalProfile t := by
        unfold aggregateMajorant
        exact mul_le_mul_of_nonneg_right (B.bound n)
          (H.verticalProfile_nonneg t)

end H15PositiveLineRowGrowth

/-- The remaining left-line input is necessarily signed.  It is kept
separate from the positive-line absolute-growth package. -/
def H15SignedReflectedLeftLineControl : Prop :=
  ∃ σ : ℝ, σ < 0 ∧
    ∃ value : ℕ → ℂ,
      Tendsto value atTop (nhds 0) ∧
        ∀ n, value n =
          ∫ t : ℝ,
            h15ActiveContourAggregate n ((σ : ℂ) + (t : ℂ) * I)

end NBMellinTools.NB12
