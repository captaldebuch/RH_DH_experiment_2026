import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPeriodReduction

/-!
# Phase 15: finite j-mode spectrum diagnostics

This file formalizes the finite diagnostic used by
`experiments/phase15_pair_spectrum.py`.  It deliberately makes no analytic
claim about the infinite Bernoulli expansion.  Instead it provides callable
finite objects and predicates which can record exactly where a proposed
positivity or concentration argument fails.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction.ModeSpectrum

open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The `(h,k)` contribution to the `j`-th Bernoulli mode. -/
noncomputable def jModePairTerm (N j h k : ℕ) : ℝ :=
  (2 / (j : ℝ)) *
    (cutoffMobiusCoeff N h / (h : ℝ)) * cutoffMobiusCoeff N k *
      bernoulliB1 ((j : ℝ) * (h : ℝ) / (k : ℝ))

/-- The finite `j`-mode `W_j(N)` from the Phase 15 spectrum experiment. -/
noncomputable def jMode (N j : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, jModePairTerm N j h k

/-- The inner `k`-sum at fixed `(N,j,h)`, useful for pointwise diagnostics. -/
noncomputable def jModePointwise (N j h : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, jModePairTerm N j h k

/-- The portion of a mode supported on pairs with gcd exactly `g`. -/
noncomputable def jModeGcdSlice (N j g : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    if Nat.gcd h k = g then jModePairTerm N j h k else 0

theorem jMode_eq_sum_pointwise (N j : ℕ) :
    jMode N j = ∑ h ∈ Finset.Icc 1 N, jModePointwise N j h := by
  rfl

/-- Exact finite gcd partition of a `j`-mode. -/
theorem jMode_eq_sum_gcdSlices (N j : ℕ) :
    jMode N j = ∑ g ∈ Finset.Icc 1 N, jModeGcdSlice N j g := by
  symm
  unfold jModeGcdSlice jMode
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rcases Finset.mem_Icc.mp hh with ⟨h1, hN⟩
  have hhpos : 0 < h := lt_of_lt_of_le Nat.zero_lt_one h1
  have hgcd_mem : Nat.gcd h k ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left k hhpos,
      (Nat.gcd_le_left k hhpos).trans hN⟩
  simp only [Finset.sum_ite_eq, if_pos hgcd_mem]

/-- Pointwise positivity, exposed as a named condition rather than assumed. -/
def PointwiseNonnegative (N j : ℕ) : Prop :=
  ∀ h ∈ Finset.Icc 1 N, 0 ≤ jModePointwise N j h

/-- A concrete witness that pointwise positivity fails. -/
def HasNegativePointwiseTerm (N j : ℕ) : Prop :=
  ∃ h ∈ Finset.Icc 1 N, jModePointwise N j h < 0

/-- Gcd-slice positivity, exposed as a named condition rather than assumed. -/
def GcdSlicesNonnegative (N j : ℕ) : Prop :=
  ∀ g ∈ Finset.Icc 1 N, 0 ≤ jModeGcdSlice N j g

/-- A concrete witness that gcd-local positivity fails. -/
def HasNegativeGcdSlice (N j : ℕ) : Prop :=
  ∃ g ∈ Finset.Icc 1 N, jModeGcdSlice N j g < 0

/-- The whole finite mode has negative sign. -/
def IsNegativeMode (N j : ℕ) : Prop := jMode N j < 0

/-- Absolute spectral mass in modes `1,...,J`. -/
noncomputable def lowModeMass (N J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 J, |jMode N j|

/-- Absolute spectral mass in the finite band `J < j ≤ K`. -/
noncomputable def modeTailMass (N J K : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc J K, |jMode N j|

/-- A finite, quantitative version of the proposed low-mode concentration. -/
def LowModeConcentrated (N J K : ℕ) (factor : ℝ) : Prop :=
  modeTailMass N J K ≤ factor * lowModeMass N J

theorem hasNegativePointwiseTerm_iff_not_nonnegative (N j : ℕ) :
    HasNegativePointwiseTerm N j ↔ ¬ PointwiseNonnegative N j := by
  constructor
  · rintro ⟨h, hh, hneg⟩ H
    exact (not_lt_of_ge (H h hh)) hneg
  · intro H
    by_contra hno
    apply H
    intro h hh
    exact le_of_not_gt fun hneg => hno ⟨h, hh, hneg⟩

theorem hasNegativeGcdSlice_iff_not_nonnegative (N j : ℕ) :
    HasNegativeGcdSlice N j ↔ ¬ GcdSlicesNonnegative N j := by
  constructor
  · rintro ⟨g, hg, hneg⟩ H
    exact (not_lt_of_ge (H g hg)) hneg
  · intro H
    by_contra hno
    apply H
    intro g hg
    exact le_of_not_gt fun hneg => hno ⟨g, hg, hneg⟩

theorem isNegativeMode_iff_not_nonnegative (N j : ℕ) :
    IsNegativeMode N j ↔ ¬ 0 ≤ jMode N j := by
  simp [IsNegativeMode]

theorem jMode_nonnegative_of_pointwise (N j : ℕ)
    (H : PointwiseNonnegative N j) : 0 ≤ jMode N j := by
  rw [jMode_eq_sum_pointwise]
  exact Finset.sum_nonneg fun h hh => H h hh

theorem jMode_nonnegative_of_gcdSlices (N j : ℕ)
    (H : GcdSlicesNonnegative N j) : 0 ≤ jMode N j := by
  rw [jMode_eq_sum_gcdSlices]
  exact Finset.sum_nonneg fun g hg => H g hg

/-- A negative whole mode forces a negative pointwise inner sum. -/
theorem hasNegativePointwiseTerm_of_negativeMode (N j : ℕ)
    (H : IsNegativeMode N j) : HasNegativePointwiseTerm N j := by
  rw [hasNegativePointwiseTerm_iff_not_nonnegative]
  intro hnonneg
  exact (not_lt_of_ge (jMode_nonnegative_of_pointwise N j hnonneg)) H

/-- A negative whole mode also forces a negative gcd slice. -/
theorem hasNegativeGcdSlice_of_negativeMode (N j : ℕ)
    (H : IsNegativeMode N j) : HasNegativeGcdSlice N j := by
  rw [hasNegativeGcdSlice_iff_not_nonnegative]
  intro hnonneg
  exact (not_lt_of_ge (jMode_nonnegative_of_gcdSlices N j hnonneg)) H

theorem lowModeMass_nonneg (N J : ℕ) : 0 ≤ lowModeMass N J := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem modeTailMass_nonneg (N J K : ℕ) : 0 ≤ modeTailMass N J K := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-! ## The `W₁ - 1` centered bracket

The experimental bracket is useful precisely because its smallness may come
from cancellation between `W₁ - 1` and `2(L + 1)`.  The following API keeps
that cancellation explicit and states the extra hypothesis needed to recover
a bound on `W₁ - 1` itself.
-/

/-- The centered first-mode bracket `W₁ - 1 + 2(L + 1)`. -/
def firstModeBracket (W₁ L : ℝ) : ℝ := W₁ - 1 + 2 * (L + 1)

theorem firstModeBracket_eq (W₁ L : ℝ) :
    firstModeBracket W₁ L = W₁ + 2 * L + 1 := by
  simp [firstModeBracket]
  ring

theorem firstMode_sub_one_eq_bracket_sub_correction (W₁ L : ℝ) :
    W₁ - 1 = firstModeBracket W₁ L - 2 * (L + 1) := by
  simp [firstModeBracket]

/-- Triangle-inequality extraction of a `W₁-1` bound from the centered bracket
and the independently centered linear term. -/
theorem firstMode_sub_one_abs_le (W₁ L B E : ℝ)
    (hbracket : |firstModeBracket W₁ L| ≤ B)
    (hlinear : |L + 1| ≤ E) :
    |W₁ - 1| ≤ B + 2 * E := by
  rw [firstMode_sub_one_eq_bracket_sub_correction]
  calc
    |firstModeBracket W₁ L - 2 * (L + 1)|
        ≤ |firstModeBracket W₁ L| + |2 * (L + 1)| := abs_sub _ _
    _ = |firstModeBracket W₁ L| + 2 * |L + 1| := by norm_num [abs_mul]
    _ ≤ B + 2 * E := add_le_add hbracket
      (mul_le_mul_of_nonneg_left hlinear (by norm_num))

/-- The `C/log` specialization used by downstream Phase 15 estimates. -/
theorem firstMode_sub_one_log_bound (W₁ L C_bracket C_linear logScale : ℝ)
    (hbracket : |firstModeBracket W₁ L| ≤ C_bracket / logScale)
    (hlinear : |L + 1| ≤ C_linear / logScale) :
    |W₁ - 1| ≤ (C_bracket + 2 * C_linear) / logScale := by
  calc
    |W₁ - 1| ≤ C_bracket / logScale + 2 * (C_linear / logScale) :=
      firstMode_sub_one_abs_le W₁ L _ _ hbracket hlinear
    _ = (C_bracket + 2 * C_linear) / logScale := by ring

end RH.Criteria.NymanBeurling.QuadraticInteraction.ModeSpectrum
