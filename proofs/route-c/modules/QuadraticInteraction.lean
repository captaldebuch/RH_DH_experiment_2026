import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import RiemannHypothesis.Criteria.NymanBeurling.MobiusSummatoryClassical
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.VasyuninGram
open Filter
open Topology

-- ---------------------------------------------------------------------------
-- 1. Unified Interaction Kernel
-- ---------------------------------------------------------------------------

/-- The central arithmetic interaction kernel independent of the Möbius cutoff weights.
  It combines the log-ratio and the fractional cotangent sum, which are individually large
  but cancel heavily to approximate 1 when summed against the Möbius cutoff.
-/
noncomputable def quadraticInteractionKernel (h k : ℕ) : ℝ :=
  (((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) * Real.log ((h : ℝ) / (k : ℝ)))
    - (Real.pi / (2 * (h : ℝ) * (k : ℝ)) * (cotangentSumVFormula h k + cotangentSumVFormula k h))

theorem quadraticInteractionKernel_symm (h k : ℕ) :
    quadraticInteractionKernel h k = quadraticInteractionKernel k h := by
  by_cases hh : h = 0
  · subst h
    simp [quadraticInteractionKernel]
  by_cases hk : k = 0
  · subst k
    simp [quadraticInteractionKernel]
  unfold quadraticInteractionKernel
  rw [Real.log_div (Nat.cast_ne_zero.mpr hh) (Nat.cast_ne_zero.mpr hk),
    Real.log_div (Nat.cast_ne_zero.mpr hk) (Nat.cast_ne_zero.mpr hh)]
  ring

theorem quadraticInteractionKernel_diag_eq_zero (h : ℕ) :
    quadraticInteractionKernel h h = 0 := by
  simp [quadraticInteractionKernel, cotangentSumVFormula_diag_eq_zero]

-- ---------------------------------------------------------------------------
-- 2. Diagonal / Off-Diagonal Split
-- ---------------------------------------------------------------------------

/-- The terms in the weighted interaction sum with equal indices. -/
noncomputable def quadraticInteractionDiagonal (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N h * quadraticInteractionKernel h h

theorem quadraticInteractionDiagonal_eq_zero (N : ℕ) :
    quadraticInteractionDiagonal N = 0 := by
  simp [quadraticInteractionDiagonal, quadraticInteractionKernel_diag_eq_zero]

/-- The terms in the weighted interaction sum with distinct indices. -/
noncomputable def quadraticInteractionOffDiagonal (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ (Finset.Icc 1 N).erase h,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k

theorem quadraticInteractionKernelSum_eq_diagonal_add_offDiagonal (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k) =
      quadraticInteractionDiagonal N + quadraticInteractionOffDiagonal N := by
  unfold quadraticInteractionDiagonal quadraticInteractionOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  exact (Finset.add_sum_erase (Finset.Icc 1 N)
    (fun k => cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
      quadraticInteractionKernel h k) hh).symm

-- ---------------------------------------------------------------------------
-- 3. GCD Stratification
-- ---------------------------------------------------------------------------

/-- The weighted interaction terms whose two indices have gcd exactly `g`. -/
noncomputable def quadraticInteractionGcdSlice (N g : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    if Nat.gcd h k = g then
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k
    else 0

/-- A gcd stratum indexed by a non-squarefree integer vanishes identically. -/
theorem quadraticInteractionGcdSlice_eq_zero_of_not_squarefree
    (N g : ℕ) (hg : ¬ Squarefree g) :
    quadraticInteractionGcdSlice N g = 0 := by
  classical
  unfold quadraticInteractionGcdSlice
  apply Finset.sum_eq_zero
  intro h _
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hgcd
  · have hgdvdh : g ∣ h := by
      rw [← hgcd]
      exact Nat.gcd_dvd_left h k
    have h_not_squarefree : ¬ Squarefree h := by
      intro hh
      exact hg (hh.squarefree_of_dvd hgdvdh)
    have hmu : ArithmeticFunction.moebius h = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree h_not_squarefree
    simp [cutoffMobiusCoeff, hmu]
  · rfl

theorem quadraticInteractionKernelSum_eq_sum_gcdSlices (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k) =
      ∑ g ∈ Finset.Icc 1 N, quadraticInteractionGcdSlice N g := by
  symm
  unfold quadraticInteractionGcdSlice
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

/-- The `g`-scaled interaction terms indexed by coprime positive pairs. -/
noncomputable def quadraticInteractionCoprimeScaledSlice (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ b ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a b then
      cutoffMobiusCoeff N (g * a) * cutoffMobiusCoeff N (g * b) *
        quadraticInteractionKernel (g * a) (g * b)
    else 0

/-- A positive gcd slice is exactly its reindexing by coprime pairs `h = g * a`, `k = g * b`. -/
theorem quadraticInteractionGcdSlice_eq_coprimeScaled (N g : ℕ) (hg : 0 < g) :
    quadraticInteractionGcdSlice N g = quadraticInteractionCoprimeScaledSlice N g := by
  classical
  let S := Finset.Icc 1 N
  let T := Finset.Icc 1 (N / g)
  let F : ℕ × ℕ → ℝ := fun p =>
    cutoffMobiusCoeff N p.1 * cutoffMobiusCoeff N p.2 *
      quadraticInteractionKernel p.1 p.2
  let scaledF : ℕ × ℕ → ℝ := fun p =>
    cutoffMobiusCoeff N (g * p.1) * cutoffMobiusCoeff N (g * p.2) *
      quadraticInteractionKernel (g * p.1) (g * p.2)
  calc
    quadraticInteractionGcdSlice N g =
        ∑ p ∈ (S ×ˢ S).filter (fun p => Nat.gcd p.1 p.2 = g), F p := by
      unfold quadraticInteractionGcdSlice
      dsimp [S, F]
      rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ p ∈ (T ×ˢ T).filter (fun p => Nat.Coprime p.1 p.2), scaledF p := by
      symm
      apply Finset.sum_bij (fun p _ => (g * p.1, g * p.2))
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpbox, hcop⟩
        rcases Finset.mem_product.mp hpbox with ⟨hpa, hpb⟩
        rcases Finset.mem_Icc.mp hpa with ⟨ha1, haN⟩
        rcases Finset.mem_Icc.mp hpb with ⟨hb1, hbN⟩
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_product.mpr
          constructor
          · apply Finset.mem_Icc.mpr
            constructor
            · exact Nat.one_le_iff_ne_zero.mpr
                (Nat.mul_ne_zero (Nat.ne_of_gt hg)
                  (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one ha1)))
            · have ha_mul := (Nat.le_div_iff_mul_le hg).mp haN
              simpa [Nat.mul_comm] using ha_mul
          · apply Finset.mem_Icc.mpr
            constructor
            · exact Nat.one_le_iff_ne_zero.mpr
                (Nat.mul_ne_zero (Nat.ne_of_gt hg)
                  (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hb1)))
            · have hb_mul := (Nat.le_div_iff_mul_le hg).mp hbN
              simpa [Nat.mul_comm] using hb_mul
        · rw [Nat.gcd_mul_left, hcop.gcd_eq_one, Nat.mul_one]
      · intro p _ q _ hpq
        apply Prod.ext
        · exact Nat.mul_left_cancel hg (congrArg Prod.fst hpq)
        · exact Nat.mul_left_cancel hg (congrArg Prod.snd hpq)
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpbox, hpgcd⟩
        rcases Finset.mem_product.mp hpbox with ⟨hph, hpk⟩
        rcases Finset.mem_Icc.mp hph with ⟨hh1, hhN⟩
        rcases Finset.mem_Icc.mp hpk with ⟨hk1, hkN⟩
        have hhpos : 0 < p.1 := lt_of_lt_of_le Nat.zero_lt_one hh1
        have hkpos : 0 < p.2 := lt_of_lt_of_le Nat.zero_lt_one hk1
        have hdvdh : g ∣ p.1 := by
          rw [← hpgcd]
          exact Nat.gcd_dvd_left _ _
        have hdvdk : g ∣ p.2 := by
          rw [← hpgcd]
          exact Nat.gcd_dvd_right _ _
        have hg_le_h : g ≤ p.1 := by
          rw [← hpgcd]
          exact Nat.gcd_le_left _ hhpos
        have hg_le_k : g ≤ p.2 := by
          rw [← hpgcd]
          exact Nat.gcd_le_right _ hkpos
        have hreconh : g * (p.1 / g) = p.1 := by
          rw [Nat.mul_comm]
          exact Nat.div_mul_cancel hdvdh
        have hreconk : g * (p.2 / g) = p.2 := by
          rw [Nat.mul_comm]
          exact Nat.div_mul_cancel hdvdk
        refine ⟨(p.1 / g, p.2 / g), ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_product.mpr
            constructor
            · exact Finset.mem_Icc.mpr
                ⟨Nat.div_pos hg_le_h hg, Nat.div_le_div_right hhN⟩
            · exact Finset.mem_Icc.mpr
                ⟨Nat.div_pos hg_le_k hg, Nat.div_le_div_right hkN⟩
          · apply Nat.coprime_iff_gcd_eq_one.mpr
            apply Nat.mul_left_cancel hg
            rw [← Nat.gcd_mul_left, hreconh, hreconk, hpgcd, Nat.mul_one]
        · apply Prod.ext
          · exact hreconh
          · exact hreconk
      · intro p _
        rfl
    _ = quadraticInteractionCoprimeScaledSlice N g := by
      unfold quadraticInteractionCoprimeScaledSlice
      dsimp [T, scaledF]
      rw [Finset.sum_filter, Finset.sum_product]

/-!
The common-gcd variable does not carry a second Möbius sign.  Once
`g` is coprime to `a * b`, multiplicativity gives
`μ (g*a) μ (g*b) = μ a μ b μ g²`; if it is not coprime, at least one
factor vanishes.  This exact identity is the arithmetic preconditioning
for the fractional-tail route to H15.
-/

theorem moebius_mul_gcd_factor
    (g a b : ℕ) (hgab : Nat.Coprime g (a * b)) :
    ArithmeticFunction.moebius (g * a) * ArithmeticFunction.moebius (g * b) =
      ArithmeticFunction.moebius a * ArithmeticFunction.moebius b *
        (ArithmeticFunction.moebius g) ^ 2 := by
  have hga : Nat.Coprime g a :=
    hgab.coprime_dvd_right (dvd_mul_right a b)
  have hgb : Nat.Coprime g b :=
    hgab.coprime_dvd_right (dvd_mul_left b a)
  rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hga,
    ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hgb]
  ring

theorem cutoffMobiusCoeff_mul_gcd_factor
    (N g a b : ℕ) (hgab : Nat.Coprime g (a * b)) :
    cutoffMobiusCoeff N (g * a) * cutoffMobiusCoeff N (g * b) =
      (((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
          (((ArithmeticFunction.moebius g : ℤ) : ℝ) ^ 2)) *
        (cutoffWeight N (g * a) * cutoffWeight N (g * b)) := by
  unfold cutoffMobiusCoeff
  have hga : Nat.Coprime g a :=
    hgab.coprime_dvd_right (dvd_mul_right a b)
  have hgb : Nat.Coprime g b :=
    hgab.coprime_dvd_right (dvd_mul_left b a)
  rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hga,
    ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hgb]
  push_cast
  ring

-- ---------------------------------------------------------------------------
-- 4. Off-Diagonal GCD Stratification
-- ---------------------------------------------------------------------------

/-- The off-diagonal weighted interaction terms whose indices have gcd exactly `g`. -/
noncomputable def quadraticInteractionOffDiagonalGcdSlice (N g : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ (Finset.Icc 1 N).erase h,
    if Nat.gcd h k = g then
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k
    else 0

theorem quadraticInteractionOffDiagonal_eq_sum_gcdSlices (N : ℕ) :
    quadraticInteractionOffDiagonal N =
      ∑ g ∈ Finset.Icc 1 N, quadraticInteractionOffDiagonalGcdSlice N g := by
  symm
  unfold quadraticInteractionOffDiagonal quadraticInteractionOffDiagonalGcdSlice
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

-- ---------------------------------------------------------------------------
-- 5. Analytic Sub-Estimate Interfaces
-- ---------------------------------------------------------------------------

/-- The diagonal contribution is negligible at the target logarithmic rate. -/
structure QuadraticInteractionDiagonalEstimate where
  C_diagonal : ℝ
  C_diagonal_nonneg : 0 ≤ C_diagonal
  diagonal_bound :
    ∀ N : ℕ,
      |quadraticInteractionDiagonal N| ≤ C_diagonal / Real.log (N + 2 : ℝ)

/-- The exact-zero diagonal supplies its logarithmic estimate with constant zero. -/
noncomputable def quadraticInteractionDiagonalEstimate_zero :
    QuadraticInteractionDiagonalEstimate := by
  refine ⟨0, le_rfl, ?_⟩
  intro N
  rw [quadraticInteractionDiagonal_eq_zero]
  simp

/--
The limiting main term assigned to each off-diagonal gcd stratum. Its partial
sums account for the target value `1` at the required logarithmic rate.
-/
structure QuadraticInteractionGcdMainTermEstimate where
  mainTerm : ℕ → ℝ
  C_main : ℝ
  C_main_nonneg : 0 ≤ C_main
  main_term_bound :
    ∀ N : ℕ,
      |(∑ g ∈ Finset.Icc 1 N, mainTerm g) - 1| ≤ C_main / Real.log (N + 2 : ℝ)

/--
Each finite-cutoff gcd slice is controlled against its limiting main term by a
nonnegative majorant whose total mass has the target logarithmic decay.
-/
structure QuadraticInteractionGcdSliceErrorEstimate (mainTerm : ℕ → ℝ) where
  errorMajorant : ℕ → ℕ → ℝ
  C_error : ℝ
  C_error_nonneg : 0 ≤ C_error
  errorMajorant_nonneg : ∀ N g : ℕ, 0 ≤ errorMajorant N g
  slice_error_bound :
    ∀ N g : ℕ,
      g ∈ Finset.Icc 1 N →
        |quadraticInteractionOffDiagonalGcdSlice N g - mainTerm g| ≤ errorMajorant N g
  error_mass_bound :
    ∀ N : ℕ,
      (∑ g ∈ Finset.Icc 1 N, errorMajorant N g) ≤ C_error / Real.log (N + 2 : ℝ)

/--
The Phase 15D analytic debts, bundled without yet deriving the global
`QuadraticInteractionEstimates` interface. That synthesis is reserved for Phase 15E.
-/
structure QuadraticInteractionAnalyticSubEstimates where
  diagonal : QuadraticInteractionDiagonalEstimate
  gcdMain : QuadraticInteractionGcdMainTermEstimate
  gcdError : QuadraticInteractionGcdSliceErrorEstimate gcdMain.mainTerm

-- ---------------------------------------------------------------------------
-- 5a. BBLS / Estermann Contour Package Interface
-- ---------------------------------------------------------------------------

/--
Structural interface for the Báez-Duarte--Balazard--Landreau--Saias
autocorrelation/Estermann contour input relevant to the quadratic interaction.

This is intentionally only a dependency package, not an attempted proof of the
contour argument.  The current Lean kernel is

`((k-h)/(2hk))*log(h/k) - (π/(2hk))*(V(h,k)+V(k,h))`.

For coprime positive `h,k`, BBLS Proposition 89 gives

`A(h/k)/h =
  quadraticInteractionKernel h k
    + ((log(2π)-γ)/2) * (1/h + 1/k)`.

Thus the BBLS autocorrelation main term lines up with this file only after
respecting the existing split between the log-gamma component and the
log/cotangent interaction kernel.  The package below records the three analytic
inputs expected from the Mellin/Estermann contour method, plus the extracted
gcd-main-term estimate that H15 can consume.  It deliberately does **not**
include the gcd-slice error estimate, which is the separate Möbius-correlation
problem.
-/
structure BBLS_EstermannContourPackage where
  /--
  BBLS Proposition 86: the Mellin transform formula for the multiplicative
  fractional-part autocorrelation `A`, namely
  `M_A(s) = -ζ(-s)ζ(s+1)/(s(s+1))` on `-1 < Re s < 0`, expressed in whatever
  eventual Mellin-transform API this project adopts.
  -/
  mellin_transform_formula : Prop
  /--
  The residue/double-pole computation at `s = 0` for the contour-shifted
  integrand, producing the explicit main term that matches the BBLS
  Proposition 89 normalization after subtracting this file's log-gamma split.
  -/
  double_pole_residue_formula : Prop
  /--
  The vertical-strip growth bound for the Estermann side, of the kind used in
  BBLS Proposition 66, sufficient to justify the contour shift.
  -/
  vertical_strip_growth_bound : Prop
  mellin_transform_formula_holds : mellin_transform_formula
  double_pole_residue_formula_holds : double_pole_residue_formula
  vertical_strip_growth_bound_holds : vertical_strip_growth_bound
  mainTerm : ℕ → ℝ
  C_main : ℝ
  C_main_nonneg : 0 ≤ C_main
  /--
  The H15-level consequence of the BBLS residue extraction: the proposed gcd
  main terms sum to the target value `1` at the logarithmic rate required by
  `QuadraticInteractionGcdMainTermEstimate`.

  Proving this field from the preceding analytic fields is future Mellin/
  contour infrastructure.  Once supplied, the bridge below is purely structural.
  -/
  main_term_bound :
    ∀ N : ℕ,
      |(∑ g ∈ Finset.Icc 1 N, mainTerm g) - 1| ≤ C_main / Real.log (N + 2 : ℝ)

/-- The BBLS/Estermann contour package discharges the gcd-main-term subestimate. -/
noncomputable def quadraticInteractionGcdMainTermEstimate_of_BBLS
    (H : BBLS_EstermannContourPackage) :
    QuadraticInteractionGcdMainTermEstimate :=
  { mainTerm := H.mainTerm
    C_main := H.C_main
    C_main_nonneg := H.C_main_nonneg
    main_term_bound := H.main_term_bound }

/--
BBLS contour input plus a separately supplied gcd-slice error estimate gives
the full analytic-subestimate package.  The diagonal component is already
unconditional (`quadraticInteractionDiagonalEstimate_zero`); the remaining
separate input is exactly the uniform Möbius-weighted slice-error estimate.
-/
noncomputable def quadraticInteractionAnalyticSubEstimates_of_BBLS_and_gcdError
    (H : BBLS_EstermannContourPackage)
    (E : QuadraticInteractionGcdSliceErrorEstimate H.mainTerm) :
    QuadraticInteractionAnalyticSubEstimates :=
  { diagonal := quadraticInteractionDiagonalEstimate_zero
    gcdMain := quadraticInteractionGcdMainTermEstimate_of_BBLS H
    gcdError := E }

-- ---------------------------------------------------------------------------
-- 5b. Farey-Cell Möbius Correlation Interface
-- ---------------------------------------------------------------------------

/--
The two-linear-forms Möbius correlation sum expected after decomposing a gcd
slice into Farey cells.  The parameters `a/q` describe the Farey approximant,
`r,s` are residue offsets, and `w` is the real kernel/cutoff weight left over
from the quadratic interaction on that cell.

The point of this definition is that the arithmetic obstruction is genuinely a
binary correlation

`μ(a*m+r) * μ(q*m+s)`,

not a one-dimensional arithmetic-progression or Bombieri--Vinogradov-type
estimate.
-/
noncomputable def fareyCellMobiusCorrelationSum
    (a q r s M : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    ((ArithmeticFunction.moebius (a * m + r) : ℤ) : ℝ) *
      ((ArithmeticFunction.moebius (q * m + s) : ℤ) : ℝ) * w m

/-- The `ℓ¹` size of the cell weight over the active parameter interval. -/
noncomputable def fareyCellWeightL1 (M : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, |w m|

/--
The pointwise logarithmic saving predicted for one Farey-cell correlation sum.
The global H15 error still needs a separate summation/decomposition hypothesis:
there are many cells, and their weights must have summable total mass.
-/
noncomputable def fareyCellLogSavingMajorant
    (C : ℝ) (N M : ℕ) (w : ℕ → ℝ) : ℝ :=
  C * fareyCellWeightL1 M w / Real.log (N + 2 : ℝ)

/--
Finite summation over the Farey-cell parameters relevant to the `g`-scaled
off-diagonal slice.  For a slice with `h = g*x`, `k = g*y`, the scaled variables
`x,y` are at most `N/g`; hence the Farey order and all cell lengths are bounded
by `N/g`.
-/
noncomputable def fareyCellParameterSum
    (N g : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g),
    ∑ q ∈ (Finset.Icc 1 (N / g)).filter (fun q => Nat.Coprime a q),
      ∑ r ∈ Finset.range a,
        ∑ s ∈ Finset.range q,
          ∑ M ∈ Finset.Icc 1 (N / g), F a q r s M

/--
The genuine arithmetic input needed by the Farey-cell approach: a uniform
log-saving estimate for Möbius evaluated on two independent affine-linear
forms.

This is deliberately stronger and more specific than
`QuadraticInteractionGcdSliceErrorEstimate`.  It does not mention the H15 kernel
or gcd slices; it only states the binary Möbius-correlation estimate that a
future analytic proof would have to supply.  The surrounding parameter ranges
are those arising from `quadraticInteractionOffDiagonalGcdSlice` after the
scaling `h = g*x`, `k = g*y` and a Farey decomposition of the coprime pair
`x/y`.
-/
structure FareyCellMobiusCorrelationEstimate where
  C_correlation : ℝ
  C_correlation_nonneg : 0 ≤ C_correlation
  correlation_bound :
    ∀ N g a q r s M : ℕ,
      ∀ w : ℕ → ℝ,
        g ∈ Finset.Icc 1 N →
          a ∈ Finset.Icc 1 (N / g) →
            q ∈ Finset.Icc 1 (N / g) →
              Nat.Coprime a q →
                r < a →
                  s < q →
                    M ∈ Finset.Icc 1 (N / g) →
                      |fareyCellMobiusCorrelationSum a q r s M w| ≤
                        fareyCellLogSavingMajorant C_correlation N M w

/--
The combinatorial and weight bookkeeping that connects Farey-cell correlations
back to the concrete H15 gcd-slice error.

This is a separate package because it is not merely a tactic-level rewrite:
formalizing the Farey partition of the off-diagonal coprime pairs, extracting
the exact cell weights from `quadraticInteractionKernel`, and proving their
summed log-saving majorants are all substantial infrastructure.  The fields
below isolate that infrastructure without pretending to prove the hard binary
Möbius-correlation estimate itself.
-/
structure FareyCellGcdSliceErrorDecomposition
    (Hcorr : FareyCellMobiusCorrelationEstimate) (mainTerm : ℕ → ℝ) where
  /--
  The real weight attached to a Farey cell.  It absorbs the cutoff factors, the
  log/cotangent interaction kernel, the fixed gcd `g`, and any squarefree or
  coprimality indicators needed to convert `μ(g*x) μ(g*y)` into the primitive
  two-linear-forms correlation.
  -/
  cellWeight : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ
  errorMajorant : ℕ → ℕ → ℝ
  C_error : ℝ
  C_error_nonneg : 0 ≤ C_error
  errorMajorant_nonneg : ∀ N g : ℕ, 0 ≤ errorMajorant N g
  /--
  Exact Farey-cell decomposition of one finite gcd slice after subtracting its
  BBLS-supplied limiting main term.
  -/
  farey_cell_decomposition :
    ∀ N g : ℕ,
      g ∈ Finset.Icc 1 N →
        quadraticInteractionOffDiagonalGcdSlice N g - mainTerm g =
          fareyCellParameterSum N g (fun a q r s M =>
            fareyCellMobiusCorrelationSum a q r s M
              (cellWeight N g a q r s M))
  /--
  The finite triangle-inequality and cellwise correlation step: applying
  `Hcorr.correlation_bound` over all relevant Farey cells is enough to dominate
  the decomposed slice by the sum of the cell log-saving majorants.
  -/
  farey_cell_correlation_bound :
    ∀ N g : ℕ,
      g ∈ Finset.Icc 1 N →
        |fareyCellParameterSum N g (fun a q r s M =>
          fareyCellMobiusCorrelationSum a q r s M
            (cellWeight N g a q r s M))| ≤
          fareyCellParameterSum N g (fun a q r s M =>
            fareyCellLogSavingMajorant Hcorr.C_correlation N M
              (cellWeight N g a q r s M))
  /--
  The remaining Farey-cell mass bookkeeping: once every cell has its
  log-saving majorant, their total contribution to this gcd slice is controlled
  by `errorMajorant`.
  -/
  farey_cell_majorant_bound :
    ∀ N g : ℕ,
      g ∈ Finset.Icc 1 N →
        fareyCellParameterSum N g (fun a q r s M =>
          fareyCellLogSavingMajorant Hcorr.C_correlation N M
            (cellWeight N g a q r s M)) ≤ errorMajorant N g
  error_mass_bound :
    ∀ N : ℕ,
      (∑ g ∈ Finset.Icc 1 N, errorMajorant N g) ≤
        C_error / Real.log (N + 2 : ℝ)

/--
Farey-cell binary Möbius-correlation input, together with the explicit
decomposition/weight bookkeeping, supplies the abstract H15 gcd-slice error
estimate.
-/
noncomputable def quadraticInteractionGcdSliceErrorEstimate_of_fareyCellCorrelation
    (Hcorr : FareyCellMobiusCorrelationEstimate) (mainTerm : ℕ → ℝ)
    (D : FareyCellGcdSliceErrorDecomposition Hcorr mainTerm) :
    QuadraticInteractionGcdSliceErrorEstimate mainTerm :=
  { errorMajorant := D.errorMajorant
    C_error := D.C_error
    C_error_nonneg := D.C_error_nonneg
    errorMajorant_nonneg := D.errorMajorant_nonneg
    slice_error_bound := by
      intro N g hg
      rw [D.farey_cell_decomposition N g hg]
      exact (D.farey_cell_correlation_bound N g hg).trans
        (D.farey_cell_majorant_bound N g hg)
    error_mass_bound := D.error_mass_bound }

-- ---------------------------------------------------------------------------
-- 6. Formal Reductions
-- ---------------------------------------------------------------------------

theorem explicitQuadraticLogCotangentInteraction_eq_unified_sum (N : ℕ) :
    explicitQuadraticLogCotangentInteraction N =
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k := by
  unfold explicitQuadraticLogCotangentInteraction
  unfold explicitQuadraticLogRatioComponent explicitQuadraticCotangentComponent
  unfold quadraticInteractionKernel
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

-- ---------------------------------------------------------------------------
-- 7. The Isolated Hard Remainder Target
-- ---------------------------------------------------------------------------

/-- The core remaining analytic estimate target:
  The double sum over the interaction kernel must converge to 1
  with an error rate of O(1/log N).
-/
theorem explicitQuadraticInteractionRemainder_eq_kernel_sum (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k) - 1 := by
  unfold explicitQuadraticInteractionRemainder
  rw [explicitQuadraticLogCotangentInteraction_eq_unified_sum N]

theorem explicitQuadraticInteractionRemainder_eq_diagonal_add_offDiagonal (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      quadraticInteractionDiagonal N + quadraticInteractionOffDiagonal N - 1 := by
  rw [explicitQuadraticInteractionRemainder_eq_kernel_sum,
    quadraticInteractionKernelSum_eq_diagonal_add_offDiagonal]

theorem explicitQuadraticInteractionRemainder_eq_diagonal_add_sum_offDiagonalGcdSlices
    (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      quadraticInteractionDiagonal N +
        (∑ g ∈ Finset.Icc 1 N, quadraticInteractionOffDiagonalGcdSlice N g) - 1 := by
  rw [explicitQuadraticInteractionRemainder_eq_diagonal_add_offDiagonal,
    quadraticInteractionOffDiagonal_eq_sum_gcdSlices]

theorem explicitQuadraticInteractionRemainder_eq_sum_gcdSlices (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      (∑ g ∈ Finset.Icc 1 N, quadraticInteractionGcdSlice N g) - 1 := by
  rw [explicitQuadraticInteractionRemainder_eq_kernel_sum,
    quadraticInteractionKernelSum_eq_sum_gcdSlices]

-- ---------------------------------------------------------------------------
-- 8. Analytic Synthesis (Phase 15E)
-- ---------------------------------------------------------------------------

/--
The three Phase 15D hypotheses imply the interaction-remainder field required
by `QuadraticInteractionEstimates`. This is finite-sum and triangle-inequality wiring.
-/
theorem explicitQuadraticInteractionRemainder_bound_of_analytic_subEstimates
    (H : QuadraticInteractionAnalyticSubEstimates) (N : ℕ) :
    |explicitQuadraticInteractionRemainder N| ≤
      (H.diagonal.C_diagonal + H.gcdError.C_error + H.gcdMain.C_main) /
        Real.log (N + 2 : ℝ) := by
  rw [explicitQuadraticInteractionRemainder_eq_diagonal_add_sum_offDiagonalGcdSlices]
  have hdecomp :
      quadraticInteractionDiagonal N +
          (∑ g ∈ Finset.Icc 1 N, quadraticInteractionOffDiagonalGcdSlice N g) - 1 =
        quadraticInteractionDiagonal N +
          (∑ g ∈ Finset.Icc 1 N,
            (quadraticInteractionOffDiagonalGcdSlice N g - H.gcdMain.mainTerm g)) +
          ((∑ g ∈ Finset.Icc 1 N, H.gcdMain.mainTerm g) - 1) := by
    rw [Finset.sum_sub_distrib]
    abel
  rw [hdecomp]
  have hslice :
      |∑ g ∈ Finset.Icc 1 N,
          (quadraticInteractionOffDiagonalGcdSlice N g - H.gcdMain.mainTerm g)| ≤
        ∑ g ∈ Finset.Icc 1 N, H.gcdError.errorMajorant N g := by
    calc
      |∑ g ∈ Finset.Icc 1 N,
          (quadraticInteractionOffDiagonalGcdSlice N g - H.gcdMain.mainTerm g)|
          ≤ ∑ g ∈ Finset.Icc 1 N,
              |quadraticInteractionOffDiagonalGcdSlice N g - H.gcdMain.mainTerm g| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ g ∈ Finset.Icc 1 N, H.gcdError.errorMajorant N g := by
        exact Finset.sum_le_sum fun g hg => H.gcdError.slice_error_bound N g hg
  calc
    |quadraticInteractionDiagonal N +
        (∑ g ∈ Finset.Icc 1 N,
          (quadraticInteractionOffDiagonalGcdSlice N g - H.gcdMain.mainTerm g)) +
        ((∑ g ∈ Finset.Icc 1 N, H.gcdMain.mainTerm g) - 1)|
        ≤ |quadraticInteractionDiagonal N| +
            |∑ g ∈ Finset.Icc 1 N,
              (quadraticInteractionOffDiagonalGcdSlice N g - H.gcdMain.mainTerm g)| +
            |(∑ g ∈ Finset.Icc 1 N, H.gcdMain.mainTerm g) - 1| := by
          exact (abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ H.diagonal.C_diagonal / Real.log (N + 2 : ℝ) +
          (∑ g ∈ Finset.Icc 1 N, H.gcdError.errorMajorant N g) +
          H.gcdMain.C_main / Real.log (N + 2 : ℝ) :=
      add_le_add (add_le_add (H.diagonal.diagonal_bound N) hslice)
        (H.gcdMain.main_term_bound N)
    _ ≤ H.diagonal.C_diagonal / Real.log (N + 2 : ℝ) +
          H.gcdError.C_error / Real.log (N + 2 : ℝ) +
          H.gcdMain.C_main / Real.log (N + 2 : ℝ) :=
      add_le_add (add_le_add le_rfl (H.gcdError.error_mass_bound N)) le_rfl
    _ = (H.diagonal.C_diagonal + H.gcdError.C_error + H.gcdMain.C_main) /
          Real.log (N + 2 : ℝ) := by rw [add_div, add_div]

/-- Package the interaction bridge with independently supplied log-gamma and residue bounds. -/
noncomputable def quadraticInteractionEstimates_of_analytic_subEstimates
    (H : QuadraticInteractionAnalyticSubEstimates)
    (C_loggamma C_residue : ℝ)
    (C_pos :
      0 < C_loggamma +
        (H.diagonal.C_diagonal + H.gcdError.C_error + H.gcdMain.C_main) + C_residue)
    (loggamma_bound :
      ∀ N : ℕ,
        |explicitQuadraticLogGammaComponent N| ≤ C_loggamma / Real.log (N + 2 : ℝ))
    (residue_bound :
      ∀ N : ℕ,
        |explicitCutoffResidueComponent N| ≤ C_residue / Real.log (N + 2 : ℝ)) :
    QuadraticInteractionEstimates := by
  refine ⟨C_loggamma,
    H.diagonal.C_diagonal + H.gcdError.C_error + H.gcdMain.C_main,
    C_residue, C_pos, loggamma_bound, ?_, residue_bound⟩
  exact explicitQuadraticInteractionRemainder_bound_of_analytic_subEstimates H


/-! ## Phase 15H: the kernel–Gram-entry correspondence

With the Vasyunin bridge now fully proved (`vasyuninBEntry_correct_axiom`,
tag `verified-h13-complete`), the quadratic interaction kernel acquires an
UNCONDITIONAL integral representation: it is exactly the Báez-Duarte Gram
entry minus its smooth `(log 2π − γ)`-part. This replaces the finite
cotangent sums (whose per-stratum Diophantine fluctuations the Phase 15B
diagnostics showed to be individually unboundable) by a manifestly
positive-semidefinite integral kernel plus a smooth correction — the
global-cancellation structure the diagnostics called for. -/

section KernelGramCorrespondence

open RH.Criteria.NymanBeurling.VasyuninGram

/-- The quadratic interaction kernel is the Vasyunin explicit-formula entry minus
its smooth part — a pure algebraic identity between the two definitions. -/
theorem quadraticInteractionKernel_eq_vasyuninBEntry_sub (h k : ℕ) :
    quadraticInteractionKernel h k =
      vasyuninBEntry h k -
        (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
          (1 / (h : ℝ) + 1 / (k : ℝ)) := by
  unfold quadraticInteractionKernel vasyuninBEntry vasyuninBEntryFormula
  ring

/-- **The Gram-integral representation of the quadratic interaction kernel**
(Phase 15H): for positive `h, k`,

`K(h,k) = ∫₀^∞ {1/(hx)}·{1/(kx)} dx − (log 2π − γ)/2 · (1/h + 1/k)`.

This is unconditional, via the now-proved Vasyunin bridge. The first term is a
positive-semidefinite kernel in `(h,k)` (it is the Gram matrix of the
Nyman–Beurling family), so the Möbius-weighted quadratic form
`∑ c(h)c(k)·K(h,k)` is a genuine squared `L²`-norm minus a product of linear
sums — the broad cancellation across gcd strata observed numerically in
Phase 15B is structural, not accidental. -/
theorem quadraticInteractionKernel_eq_gramEntry_sub (h k : ℕ)
    (hh : 0 < h) (hk : 0 < k) :
    quadraticInteractionKernel h k =
      baezDuarteGramEntry h k -
        (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
          (1 / (h : ℝ) + 1 / (k : ℝ)) := by
  rw [quadraticInteractionKernel_eq_vasyuninBEntry_sub,
    vasyuninBEntry_correct_axiom h k hh hk]

end KernelGramCorrespondence

/-! ## Phase 15H-H3: Gram-square structure of the finite quadratic form

The pointwise kernel identity above upgrades immediately to a finite quadratic-form
identity.  The genuinely analytic input is already present in `VasyuninBridge`:
`genIntegrand_integrableOn_Ioi` proves integrability of the Gram integrand.
Everything below is finite-sum/integral interchange plus algebra. -/

section KernelGramQuadraticForm

open scoped MeasureTheory
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The Gram-entry integrand is integrable on `(0, ∞)` for positive indices.

This is a local wrapper around the existing `genIntegrand_integrableOn_Ioi`.
No new integrability analysis is needed here. -/
theorem gramIntegrand_integrableOn_Ioi (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => Int.fract (1 / ((h : ℝ) * x)) *
        Int.fract (1 / ((k : ℝ) * x)))
      (Set.Ioi (0 : ℝ)) := by
  change MeasureTheory.IntegrableOn (genIntegrand h k) (Set.Ioi (0 : ℝ))
  exact genIntegrand_integrableOn_Ioi h k hh hk

/-- A finite Gram quadratic form is the integral of the square of the corresponding
finite linear combination of fractional-part basis functions. -/
theorem gram_quadratic_form_eq_integral_sq (N : ℕ) (c : ℕ → ℝ) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c h * c k * baezDuarteGramEntry h k)
      = ∫ x in Set.Ioi (0 : ℝ),
          (∑ h ∈ Finset.Icc 1 N,
            c h * Int.fract (1 / ((h : ℝ) * x))) ^ 2 := by
  classical
  let S := Finset.Icc 1 N
  let G : ℕ → ℕ → ℝ → ℝ := fun h k x => c h * c k * genIntegrand h k x
  have hpair_int : ∀ h ∈ S, ∀ k ∈ S,
      MeasureTheory.Integrable (fun x : ℝ => G h k x)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro h hh k hk
    have hhpos : 0 < h := by
      exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hh).1
    have hkpos : 0 < k := by
      exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
    have hint : MeasureTheory.IntegrableOn (genIntegrand h k) (Set.Ioi (0 : ℝ)) :=
      genIntegrand_integrableOn_Ioi h k hhpos hkpos
    simpa [G] using hint.const_mul (c h * c k)
  have h_lhs :
      (∑ h ∈ S, ∑ k ∈ S, c h * c k * baezDuarteGramEntry h k) =
        ∑ h ∈ S, ∑ k ∈ S, ∫ x in Set.Ioi (0 : ℝ), G h k x := by
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro k _
    rw [baezDuarteGramEntry_eq_genIntegrand]
    calc
      c h * c k * (∫ x in Set.Ioi (0 : ℝ), genIntegrand h k x)
          = (c h * c k) * (∫ x in Set.Ioi (0 : ℝ), genIntegrand h k x) := by
            ring
      _ = ∫ x in Set.Ioi (0 : ℝ), (c h * c k) * genIntegrand h k x := by
            rw [MeasureTheory.integral_const_mul]
      _ = ∫ x in Set.Ioi (0 : ℝ), G h k x := by
            rfl
  have h_integral_sum :
      (∫ x in Set.Ioi (0 : ℝ), ∑ h ∈ S, ∑ k ∈ S, G h k x) =
        ∑ h ∈ S, ∑ k ∈ S, ∫ x in Set.Ioi (0 : ℝ), G h k x := by
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro h hh
      rw [MeasureTheory.integral_finsetSum]
      exact fun k hk => hpair_int h hh k hk
    · intro h hh
      exact MeasureTheory.integrable_finsetSum S (fun k hk => hpair_int h hh k hk)
  rw [h_lhs, ← h_integral_sum]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp [G, genIntegrand]
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- The smooth correction term in the kernel-Gram correspondence collapses to a
product of two finite linear sums. -/
theorem smooth_part_quadratic_sum_eq_linear_product (N : ℕ) (c : ℕ → ℝ) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c h * c k *
          ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
            (1 / (h : ℝ) + 1 / (k : ℝ)))) =
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) *
        (∑ h ∈ Finset.Icc 1 N, c h / (h : ℝ)) *
          (∑ k ∈ Finset.Icc 1 N, c k) := by
  classical
  let S := Finset.Icc 1 N
  let A := (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2
  let L := Real.log (2 * Real.pi) - Real.eulerMascheroniConstant
  change
    (∑ h ∈ S, ∑ k ∈ S, c h * c k * (A * (1 / (h : ℝ) + 1 / (k : ℝ)))) =
      L * (∑ h ∈ S, c h / (h : ℝ)) * (∑ k ∈ S, c k)
  have hswap :
      (∑ h ∈ S, ∑ k ∈ S, c h * c k * (A * (1 / (k : ℝ)))) =
        ∑ h ∈ S, ∑ k ∈ S, c h * c k * (A * (1 / (h : ℝ))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hprod :
      (∑ h ∈ S, ∑ k ∈ S, c h * c k * (A * (1 / (h : ℝ)))) =
        A * ((∑ h ∈ S, c h / (h : ℝ)) * (∑ k ∈ S, c k)) := by
    rw [Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hL : L = 2 * A := by
    dsimp [L, A]
    ring
  rw [hL]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hswap, hprod]
  ring

/-- The finite quadratic form associated to `quadraticInteractionKernel` is a
Gram-square integral minus the smooth linear product. -/
theorem quadratic_form_eq_normSq_sub_linear (N : ℕ) (c : ℕ → ℝ) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c h * c k * quadraticInteractionKernel h k)
      = (∫ x in Set.Ioi (0 : ℝ),
          (∑ h ∈ Finset.Icc 1 N,
            c h * Int.fract (1 / ((h : ℝ) * x))) ^ 2)
        - (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) *
            (∑ h ∈ Finset.Icc 1 N, c h / (h : ℝ)) *
              (∑ k ∈ Finset.Icc 1 N, c k) := by
  classical
  let S := Finset.Icc 1 N
  let A := (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2
  have hrewrite :
      (∑ h ∈ S, ∑ k ∈ S, c h * c k * quadraticInteractionKernel h k) =
        ∑ h ∈ S, ∑ k ∈ S,
          c h * c k *
            (baezDuarteGramEntry h k - A * (1 / (h : ℝ) + 1 / (k : ℝ))) := by
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro k hk
    have hhpos : 0 < h := by
      exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hh).1
    have hkpos : 0 < k := by
      exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
    rw [quadraticInteractionKernel_eq_gramEntry_sub h k hhpos hkpos]
  rw [hrewrite]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [gram_quadratic_form_eq_integral_sq N c,
    smooth_part_quadratic_sum_eq_linear_product N c]

/-- The Gram-square integral appearing in `quadratic_form_eq_normSq_sub_linear`
is nonnegative. -/
theorem gram_norm_integral_nonneg (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∫ x in Set.Ioi (0 : ℝ),
      (∑ h ∈ Finset.Icc 1 N,
        c h * Int.fract (1 / ((h : ℝ) * x))) ^ 2 := by
  exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _

/-- Unconditional lower bound for any finite weighted quadratic form of the
interaction kernel: only the smooth linear product can contribute negatively. -/
theorem quadratic_form_ge_neg_linear (N : ℕ) (c : ℕ → ℝ) :
    -((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) *
        (∑ h ∈ Finset.Icc 1 N, c h / (h : ℝ)) *
          (∑ k ∈ Finset.Icc 1 N, c k))
      ≤ ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          c h * c k * quadraticInteractionKernel h k := by
  rw [quadratic_form_eq_normSq_sub_linear N c]
  have hnonneg := gram_norm_integral_nonneg N c
  linarith

/-- The norm-square identity specialized to the project's cutoff Möbius weights. -/
theorem cutoffMobius_quadratic_form_eq_normSq_sub_linear (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k)
      = (∫ x in Set.Ioi (0 : ℝ),
          (∑ h ∈ Finset.Icc 1 N,
            cutoffMobiusCoeff N h * Int.fract (1 / ((h : ℝ) * x))) ^ 2)
        - (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) *
            (∑ h ∈ Finset.Icc 1 N, cutoffMobiusCoeff N h / (h : ℝ)) *
              (∑ k ∈ Finset.Icc 1 N, cutoffMobiusCoeff N k) :=
  quadratic_form_eq_normSq_sub_linear N (cutoffMobiusCoeff N)

/-- The isolated quadratic-interaction remainder is the cutoff Möbius Gram-square
minus its smooth product correction, and then minus the target main term `1`. -/
theorem explicitQuadraticInteractionRemainder_eq_normSq_sub_linear (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      (∫ x in Set.Ioi (0 : ℝ),
          (∑ h ∈ Finset.Icc 1 N,
            cutoffMobiusCoeff N h * Int.fract (1 / ((h : ℝ) * x))) ^ 2)
        - (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) *
            (∑ h ∈ Finset.Icc 1 N, cutoffMobiusCoeff N h / (h : ℝ)) *
              (∑ k ∈ Finset.Icc 1 N, cutoffMobiusCoeff N k)
        - 1 := by
  rw [explicitQuadraticInteractionRemainder_eq_kernel_sum,
    cutoffMobius_quadratic_form_eq_normSq_sub_linear]

end KernelGramQuadraticForm

/-! ## Phase 15H finish attempt: norm residual interface

The norm-square representation exposes the interaction remainder as a completed
square plus linear corrections.  The H14 Dirichlet estimates control the linear
piece `explicitLinearMobiusSum N + 1`; the remaining genuinely quadratic input
is isolated below as a single norm/loggamma residual package.

This section deliberately does not assume any Nyman--Beurling distance infimum
or RH-equivalent approximation statement.  The only norm quantity appearing is
the specific finite cutoff-Möbius vector already present in the kernel formula.
-/

section KernelNormFinish

open scoped MeasureTheory
open RH.Criteria.NymanBeurling.CutoffMobiusKernels

/-- H15-facing wrapper for the already-proved χ--ρ integral evaluation. -/
theorem chiRhoIntegral_eq_explicitChiRhoKernel (h : ℕ) (hh : 0 < h) :
    (∫ x in Set.Ioc (0 : ℝ) 1, Int.fract (1 / ((h : ℝ) * x))) =
      explicitChiRhoKernel h := by
  change RH.Criteria.NymanBeurling.ChiRhoIntegralEvaluation.chiRhoIntegral h =
    explicitChiRhoKernel h
  rw [RH.Criteria.NymanBeurling.ChiRhoIntegralEvaluation.chiRhoIntegral_formula h hh]
  rfl

/-- The cutoff-Möbius Gram norm appearing in the 15H-H3 identity. -/
noncomputable def cutoffMobiusGramNormIntegral (N : ℕ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    (∑ h ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * Int.fract (1 / ((h : ℝ) * x))) ^ 2

/-- The χ-cross term for the specific cutoff-Möbius vector. -/
noncomputable def cutoffMobiusChiRhoCross (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, cutoffMobiusCoeff N k * explicitChiRhoKernel k

/-- The completed-square energy of the specific cutoff-Möbius approximation. -/
noncomputable def cutoffMobiusDefectEnergy (N : ℕ) : ℝ :=
  1 - 2 * cutoffMobiusChiRhoCross N + cutoffMobiusGramNormIntegral N

/-- The cutoff χ-cross term is the negative of the explicit linear Möbius sum. -/
theorem cutoffMobiusChiRhoCross_eq_neg_explicitLinearMobiusSum (N : ℕ) :
    cutoffMobiusChiRhoCross N = - explicitLinearMobiusSum N := by
  unfold cutoffMobiusChiRhoCross explicitLinearMobiusSum cutoffMobiusCoeff
    cutoffWeight explicitChiRhoKernel
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The explicit log-gamma quadratic component is the smooth product in the
kernel-Gram correspondence. -/
theorem explicitQuadraticLogGammaComponent_eq_smooth_product (N : ℕ) :
    explicitQuadraticLogGammaComponent N =
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) *
        (∑ h ∈ Finset.Icc 1 N, cutoffMobiusCoeff N h / (h : ℝ)) *
          (∑ k ∈ Finset.Icc 1 N, cutoffMobiusCoeff N k) := by
  unfold explicitQuadraticLogGammaComponent
  exact smooth_part_quadratic_sum_eq_linear_product N (cutoffMobiusCoeff N)

/-- The inverse-index factor in the smooth product is exactly the negative
H14 cutoff Dirichlet sum. -/
theorem cutoffMobiusCoeff_div_sum_eq_neg_overK (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, cutoffMobiusCoeff N h / (h : ℝ)) =
      -cutoffMobiusOverKSum N := by
  unfold cutoffMobiusCoeff cutoffWeight cutoffMobiusOverKSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- Classical Mertens decay controls the inverse-index factor of the smooth
product.  The other factor `∑ k, cutoffMobiusCoeff N k` is deliberately not
discarded: the separate absolute value in the H15 target requires genuine
control of their product. -/
theorem cutoffMobiusCoeff_div_sum_bound_of_decay
    (H : MobiusSummatory.ClassicalMertensDecay) :
    ∃ C > 0, ∀ N : ℕ,
      |∑ h ∈ Finset.Icc 1 N, cutoffMobiusCoeff N h / (h : ℝ)| ≤
        C / Real.log (N + 2 : ℝ) := by
  let api := MobiusSummatory.ClassicalMertensAPI.ofDecayOnly H
  refine ⟨12 * api.C_M, mul_pos (by norm_num) api.C_M_pos, ?_⟩
  intro N
  rw [cutoffMobiusCoeff_div_sum_eq_neg_overK, abs_neg]
  exact api.overK_bound N

/-- The interaction remainder written as completed-square energy plus the
H14-controlled linear centered error. -/
theorem explicitQuadraticInteractionRemainder_eq_defect_sub_loggamma_sub_linear
    (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      cutoffMobiusDefectEnergy N - explicitQuadraticLogGammaComponent N
        - 2 * (explicitLinearMobiusSum N + 1) := by
  rw [explicitQuadraticInteractionRemainder_eq_normSq_sub_linear,
    explicitQuadraticLogGammaComponent_eq_smooth_product]
  unfold cutoffMobiusDefectEnergy cutoffMobiusGramNormIntegral
  rw [cutoffMobiusChiRhoCross_eq_neg_explicitLinearMobiusSum]
  ring

/-! ### The BBLS Bernoulli-series form of the cotangent interaction -/

/-- The Möbius-weighted Bernoulli inner sum exposed by BBLS Proposition 48. -/
noncomputable def cutoffMobiusBernoulliInner (N m h : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N k *
      bernoulliB1 ((m : ℝ) * ((h : ℝ) / (k : ℝ)))

/-- The finite `m`-partial sum of the reordered symmetric cotangent interaction. -/
noncomputable def cutoffMobiusBernoulliCorrelationPartial (N M : ℕ) : ℝ :=
  -2 * ∑ m ∈ Finset.Icc 1 M,
    (∑ h ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h / (h : ℝ) * cutoffMobiusBernoulliInner N m h) /
        (m : ℝ)

/-- The individual BBLS Fourier mode in the reordered cotangent interaction.

The index `m = 0` is harmless as a definition, but all correlation partials
below sum this mode only over `m ≥ 1`, matching the analytic series
`∑_{m≥1} B₁(m·h/k)/m`. -/
noncomputable def cutoffMobiusBernoulliMode (N m : ℕ) : ℝ :=
  -2 *
    ((∑ h ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h / (h : ℝ) * cutoffMobiusBernoulliInner N m h) /
        (m : ℝ))

/-- Zero-based indexing for the positive modes: index `j` is analytic mode
`m = j + 1`. -/
noncomputable def cutoffMobiusBernoulliModeFromZero (N j : ℕ) : ℝ :=
  cutoffMobiusBernoulliMode N (j + 1)

/-- The finite correlation partial is exactly the sum of its first `M`
positive Fourier modes. -/
theorem cutoffMobiusBernoulliCorrelationPartial_eq_mode_sum (N M : ℕ) :
    cutoffMobiusBernoulliCorrelationPartial N M =
      ∑ m ∈ Finset.Icc 1 M, cutoffMobiusBernoulliMode N m := by
  unfold cutoffMobiusBernoulliCorrelationPartial cutoffMobiusBernoulliMode
  rw [Finset.mul_sum]

/-- The same positive-mode sum, written with zero-based `range` indexing. -/
theorem cutoffMobiusBernoulliModeFromZero_sum_range_eq_Icc (N M : ℕ) :
    (∑ j ∈ Finset.range M, cutoffMobiusBernoulliModeFromZero N j) =
      ∑ m ∈ Finset.Icc 1 M, cutoffMobiusBernoulliMode N m := by
  rw [Finset.range_eq_Ico]
  rw [show (∑ j ∈ Finset.Ico 0 M, cutoffMobiusBernoulliModeFromZero N j) =
      ∑ j ∈ Finset.Ico 0 M, cutoffMobiusBernoulliMode N (1 + j) by
        apply Finset.sum_congr rfl
        intro j _
        simp [cutoffMobiusBernoulliModeFromZero, Nat.add_comm]]
  rw [Finset.sum_Ico_add]
  simp [Finset.Ico_add_one_right_eq_Icc]

/-- The reordered partial sum is exactly the corresponding finite triple sum. -/
theorem cutoffMobiusBernoulliCorrelationPartial_eq_triple (N M : ℕ) :
    cutoffMobiusBernoulliCorrelationPartial N M =
      -2 * ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (cutoffMobiusCoeff N h * cutoffMobiusCoeff N k / (h : ℝ)) *
          (∑ m ∈ Finset.Icc 1 M,
            bernoulliB1 ((m : ℝ) * ((h : ℝ) / (k : ℝ))) / (m : ℝ)) := by
  classical
  unfold cutoffMobiusBernoulliCorrelationPartial cutoffMobiusBernoulliInner
  congr 1
  simp_rw [Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- The BBLS limit value of the reordered Bernoulli correlation. -/
noncomputable def cutoffMobiusBernoulliCorrelationValue (N : ℕ) : ℝ :=
  -2 * ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    (cutoffMobiusCoeff N h * cutoffMobiusCoeff N k / (h : ℝ)) *
      (Real.pi / (2 * (k : ℝ)) * cotangentSumVFormula h k)

/-- BBLS Proposition 48 evaluates every finite `(h,k)` series in the
reordered correlation, so its finite `m`-partials converge to the displayed
cotangent value. -/
theorem cutoffMobiusBernoulliCorrelationPartial_tendsto (N : ℕ) :
    Tendsto (cutoffMobiusBernoulliCorrelationPartial N) atTop
      (𝓝 (cutoffMobiusBernoulliCorrelationValue N)) := by
  have hpairs : Tendsto (fun M : ℕ =>
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (cutoffMobiusCoeff N h * cutoffMobiusCoeff N k / (h : ℝ)) *
          (∑ m ∈ Finset.Icc 1 M,
            bernoulliB1 ((m : ℝ) * ((h : ℝ) / (k : ℝ))) / (m : ℝ)))
      atTop
      (𝓝 (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (cutoffMobiusCoeff N h * cutoffMobiusCoeff N k / (h : ℝ)) *
          (Real.pi / (2 * (k : ℝ)) * cotangentSumVFormula h k))) := by
    apply tendsto_finset_sum
    intro h hh
    apply tendsto_finset_sum
    intro k hk
    have hhpos : 0 < h :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hh).1
    have hkpos : 0 < k :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
    exact tendsto_const_nhds.mul
      (tendsto_bernoulliB1_sum_div_rat h k hhpos hkpos)
  have hscaled := hpairs.const_mul (-2)
  apply hscaled.congr'
  filter_upwards [] with M
  rw [cutoffMobiusBernoulliCorrelationPartial_eq_triple]

/-- The BBLS cotangent/Bernoulli correlation is the limit of its finite mode
partials, indexed from zero as `m = j + 1`.

This is the exact conditional-Fourier statement supplied by BBLS Proposition
48.  It deliberately uses `Tendsto` of ordinary partial sums rather than an
unconditional `tsum`: the proved rational `φ₁` series in this project is a
partial-sum limit theorem, not an absolute-summability theorem. -/
theorem cutoffMobiusBernoulliCorrelationValue_eq_mode_partial_limit (N : ℕ) :
    Tendsto (fun M : ℕ =>
      ∑ j ∈ Finset.range M, cutoffMobiusBernoulliModeFromZero N j) atTop
      (𝓝 (cutoffMobiusBernoulliCorrelationValue N)) := by
  have h := cutoffMobiusBernoulliCorrelationPartial_tendsto N
  apply h.congr'
  filter_upwards [] with M
  rw [cutoffMobiusBernoulliCorrelationPartial_eq_mode_sum]
  rw [← cutoffMobiusBernoulliModeFromZero_sum_range_eq_Icc]

/-- If the zero-based mode series is summable in Lean's `tsum` sense, then
its `tsum` agrees with the BBLS cotangent/Bernoulli value.  The summability
hypothesis is intentionally explicit: it is stronger than the currently
proved BBLS partial-sum convergence statement. -/
theorem cutoffMobiusBernoulliCorrelationValue_eq_tsum_modes_of_summable
    (N : ℕ)
    (hs : Summable (cutoffMobiusBernoulliModeFromZero N)) :
    cutoffMobiusBernoulliCorrelationValue N =
      ∑' j : ℕ, cutoffMobiusBernoulliModeFromZero N j := by
  exact tendsto_nhds_unique
    (cutoffMobiusBernoulliCorrelationValue_eq_mode_partial_limit N)
    hs.hasSum.tendsto_sum_nat

/-- The BBLS Bernoulli correlation value is exactly the symmetric cotangent
component already used in the explicit quadratic decomposition. -/
theorem cutoffMobiusBernoulliCorrelationValue_eq_cotangentComponent (N : ℕ) :
    cutoffMobiusBernoulliCorrelationValue N =
      explicitQuadraticCotangentComponent N := by
  classical
  let S := Finset.Icc 1 N
  let A := ∑ h ∈ S, ∑ k ∈ S,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
      (-(Real.pi / (2 * (h : ℝ) * (k : ℝ)) * cotangentSumVFormula h k))
  let B := ∑ h ∈ S, ∑ k ∈ S,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
      (-(Real.pi / (2 * (h : ℝ) * (k : ℝ)) * cotangentSumVFormula k h))
  have hvalue : cutoffMobiusBernoulliCorrelationValue N = A + A := by
    unfold cutoffMobiusBernoulliCorrelationValue
    dsimp [A, S]
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hswap : B = A := by
    dsimp [A, B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hexplicit : explicitQuadraticCotangentComponent N = A + B := by
    unfold explicitQuadraticCotangentComponent
    dsimp [A, B, S]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hvalue, hexplicit, hswap]

/-- The reordered Bernoulli partials converge to the existing cotangent
component, with no extra analytic hypothesis. -/
theorem cutoffMobiusBernoulliCorrelationPartial_tendsto_cotangent (N : ℕ) :
    Tendsto (cutoffMobiusBernoulliCorrelationPartial N) atTop
      (𝓝 (explicitQuadraticCotangentComponent N)) := by
  simpa [cutoffMobiusBernoulliCorrelationValue_eq_cotangentComponent] using
    cutoffMobiusBernoulliCorrelationPartial_tendsto N

/-- The cotangent component is the partial-sum limit of the BBLS Fourier
modes.  This is the safe regrouping identity used by the mode-split
diagnostics. -/
theorem cotangent_component_eq_mode_partial_limit (N : ℕ) :
    Tendsto (fun M : ℕ =>
      ∑ j ∈ Finset.range M, cutoffMobiusBernoulliModeFromZero N j) atTop
      (𝓝 (explicitQuadraticCotangentComponent N)) := by
  simpa [cutoffMobiusBernoulliCorrelationValue_eq_cotangentComponent] using
    cutoffMobiusBernoulliCorrelationValue_eq_mode_partial_limit N

/-- Conditional `tsum` form of `cotangent_component_eq_mode_partial_limit`.
The explicit summability hypothesis prevents the theorem from claiming an
absolute/unordered summability result not supplied by the current BBLS
infrastructure. -/
theorem cotangent_component_eq_tsum_modes_of_summable
    (N : ℕ)
    (hs : Summable (cutoffMobiusBernoulliModeFromZero N)) :
    explicitQuadraticCotangentComponent N =
      ∑' j : ℕ, cutoffMobiusBernoulliModeFromZero N j := by
  rw [← cutoffMobiusBernoulliCorrelationValue_eq_cotangentComponent]
  exact cutoffMobiusBernoulliCorrelationValue_eq_tsum_modes_of_summable N hs

/-- The corrected defect is the log-ratio term plus the BBLS Bernoulli
correlation main term and the already-controlled H14 linear centering. -/
theorem cutoffMobiusDefectEnergy_sub_loggamma_eq_bernoulli_value (N : ℕ) :
    cutoffMobiusDefectEnergy N - explicitQuadraticLogGammaComponent N =
      explicitQuadraticLogRatioComponent N +
        cutoffMobiusBernoulliCorrelationValue N - 1 +
          2 * (explicitLinearMobiusSum N + 1) := by
  rw [cutoffMobiusBernoulliCorrelationValue_eq_cotangentComponent]
  have h :=
    explicitQuadraticInteractionRemainder_eq_defect_sub_loggamma_sub_linear N
  unfold explicitQuadraticInteractionRemainder
    explicitQuadraticLogCotangentInteraction at h
  linarith

/-- The centered Bernoulli package preserves the exact cancellation between
the log-ratio term, the BBLS correlation main term `1`, and the doubled H14
linear correction. -/
theorem centeredBernoulliPair_eq_interactionRemainder_add_linear (N : ℕ) :
    explicitQuadraticLogRatioComponent N +
        cutoffMobiusBernoulliCorrelationValue N - 1 +
          2 * (explicitLinearMobiusSum N + 1) =
      explicitQuadraticInteractionRemainder N +
        2 * (explicitLinearMobiusSum N + 1) := by
  rw [cutoffMobiusBernoulliCorrelationValue_eq_cotangentComponent]
  unfold explicitQuadraticInteractionRemainder
    explicitQuadraticLogCotangentInteraction
  ring

/-- The finite centered partial whose limit is the corrected defect. -/
noncomputable def cutoffMobiusBernoulliCenteredPartial (N M : ℕ) : ℝ :=
  explicitQuadraticLogRatioComponent N +
    cutoffMobiusBernoulliCorrelationPartial N M - 1 +
      2 * (explicitLinearMobiusSum N + 1)

/-- The centered Bernoulli correlation partials converge exactly to the
completed-square defect after subtraction of the log-gamma term. -/
theorem cutoffMobiusBernoulliCenteredPartial_tendsto (N : ℕ) :
    Tendsto (cutoffMobiusBernoulliCenteredPartial N) atTop
      (𝓝 (cutoffMobiusDefectEnergy N -
        explicitQuadraticLogGammaComponent N)) := by
  have h := cutoffMobiusBernoulliCorrelationPartial_tendsto N
  have hcentered :=
    (((h.const_add (explicitQuadraticLogRatioComponent N)).sub_const 1).add_const
      (2 * (explicitLinearMobiusSum N + 1)))
  rw [cutoffMobiusDefectEnergy_sub_loggamma_eq_bernoulli_value]
  simpa [cutoffMobiusBernoulliCenteredPartial, add_assoc] using hcentered

/--
The one genuinely quadratic estimate not supplied by classical Mertens decay.

Its second absolute value is the limit of
`cutoffMobiusBernoulliCenteredPartial`; hence the field states the actual
Möbius--Bernoulli correlation estimate exposed by BBLS Proposition 48, rather
than merely renaming the norm residual.  Diagnostics at `N = 20, 50, 100, 300`
gave `package * log(N+2)^2 = 4.01, 3.11, 2.38, 1.56`, motivating the displayed
full spare logarithm.

The parameter `H` records the intended background input.  It is not sufficient
by itself in the present proof: the pointwise inner sums grow in the numerical
gate, and their outer `1/m` series is only conditionally convergent.
-/
structure QuadraticInteractionBernoulliCorrelationEstimate
    (_H : MobiusSummatory.ClassicalMertensDecay) where
  C_correlation : ℝ
  C_correlation_nonneg : 0 ≤ C_correlation
  centered_correlation_bound :
    ∀ N : ℕ,
      |explicitQuadraticLogGammaComponent N| +
          |explicitQuadraticLogRatioComponent N +
              cutoffMobiusBernoulliCorrelationValue N - 1 +
                2 * (explicitLinearMobiusSum N + 1)|
        ≤ C_correlation / Real.log (N + 2 : ℝ) ^ 2

/-- The separately absolute smooth-product sub-debt in the S1 estimate.

The H14 toolkit proves an `O(1 / log N)` bound for its inverse-index factor
(`cutoffMobiusCoeff_div_sum_bound_of_decay`), but its available bound for the
unweighted factor grows like `N * exp (-c * sqrt (log N))`.  Multiplying those
separate majorants does not prove decay.  Numerically,
`|explicitQuadraticLogGammaComponent N| * log(N+2)^2` was
`0.986, 0.539, 0.228, 0.082, 0.047, 0.006, 0.039` at
`N = 100, 300, 1000, 3000, 10^4, 10^5, 10^6`.
-/
structure QuadraticInteractionSmoothProductLogSqEstimate
    (_H : MobiusSummatory.ClassicalMertensDecay) where
  C_smooth : ℝ
  C_smooth_nonneg : 0 ≤ C_smooth
  smooth_product_bound :
    ∀ N : ℕ,
      |explicitQuadraticLogGammaComponent N| ≤
        C_smooth / Real.log (N + 2 : ℝ) ^ 2

/-- The content-bearing centered main-term sub-debt left by the numerical S1
gate.  It keeps `logRatio + Bernoulli - 1` paired before adding the doubled
linear correction; no pointwise bound on `cutoffMobiusBernoulliInner` is used.

At `N = 500, 1000, 2000`, the first pairing cancels its three constituents by
factors about `315, 738, 291`, and the final centered expression multiplied by
`log(N+2)^2` was `0.975, 0.925, 1.010`.
-/
structure QuadraticInteractionCenteredBernoulliPairEstimate
    (_H : MobiusSummatory.ClassicalMertensDecay) where
  C_centered : ℝ
  C_centered_nonneg : 0 ≤ C_centered
  centered_pair_bound :
    ∀ N : ℕ,
      |explicitQuadraticLogRatioComponent N +
          cutoffMobiusBernoulliCorrelationValue N - 1 +
            2 * (explicitLinearMobiusSum N + 1)| ≤
        C_centered / Real.log (N + 2 : ℝ) ^ 2

/-- The two precisely isolated S1 sub-estimates assemble mechanically into the
existing Bernoulli-correlation interface.  This theorem adds no analytic
assumption beyond the two displayed content-bearing fields. -/
noncomputable def quadraticInteractionBernoulliCorrelationEstimate_of_subEstimates
    (H : MobiusSummatory.ClassicalMertensDecay)
    (H_smooth : QuadraticInteractionSmoothProductLogSqEstimate H)
    (H_centered : QuadraticInteractionCenteredBernoulliPairEstimate H) :
    QuadraticInteractionBernoulliCorrelationEstimate H := by
  refine
    { C_correlation := H_smooth.C_smooth + H_centered.C_centered
      C_correlation_nonneg :=
        add_nonneg H_smooth.C_smooth_nonneg H_centered.C_centered_nonneg
      centered_correlation_bound := ?_ }
  intro N
  calc
    |explicitQuadraticLogGammaComponent N| +
          |explicitQuadraticLogRatioComponent N +
              cutoffMobiusBernoulliCorrelationValue N - 1 +
                2 * (explicitLinearMobiusSum N + 1)|
        ≤ H_smooth.C_smooth / Real.log (N + 2 : ℝ) ^ 2 +
            H_centered.C_centered / Real.log (N + 2 : ℝ) ^ 2 :=
      add_le_add (H_smooth.smooth_product_bound N)
        (H_centered.centered_pair_bound N)
    _ = (H_smooth.C_smooth + H_centered.C_centered) /
          Real.log (N + 2 : ℝ) ^ 2 := by ring

/--
The single residual analytic input left by the norm-square finish attempt.

It packages exactly the part not supplied by H14's linear Möbius estimates:
both the smooth log-gamma component and the corrected cutoff-Möbius defect
energy must have total logarithmic mass.  This is intentionally stronger than
separate bounds but keeps the remaining H15 debt as one named, content-bearing
norm statement rather than the earlier gcd-slice sub-estimate interface.
-/
structure QuadraticInteractionNormResidual where
  C_norm : ℝ
  C_norm_nonneg : 0 ≤ C_norm
  norm_loggamma_package_bound :
    ∀ N : ℕ,
      |explicitQuadraticLogGammaComponent N| +
          |cutoffMobiusDefectEnergy N - explicitQuadraticLogGammaComponent N|
        ≤ C_norm / Real.log (N + 2 : ℝ)

/-- The centered BBLS correlation estimate, with its observed spare logarithm,
implies the norm residual required by the existing H15 finish bridge. -/
noncomputable def quadraticInteractionNormResidual_of_bernoulliCorrelation
    (H : MobiusSummatory.ClassicalMertensDecay)
    (Hcorr : QuadraticInteractionBernoulliCorrelationEstimate H) :
    QuadraticInteractionNormResidual := by
  let logTwo := Real.log (2 : ℝ)
  refine
    { C_norm := Hcorr.C_correlation / logTwo
      C_norm_nonneg := div_nonneg Hcorr.C_correlation_nonneg
        (Real.log_pos (by norm_num)).le
      norm_loggamma_package_bound := ?_ }
  intro N
  rw [cutoffMobiusDefectEnergy_sub_loggamma_eq_bernoulli_value]
  have hcorr := Hcorr.centered_correlation_bound N
  have hlogTwo : 0 < logTwo := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
  have hmono : logTwo ≤ Real.log (N + 2 : ℝ) := by
    exact Real.log_le_log (by norm_num) (by norm_cast; omega)
  have hratio :
      Hcorr.C_correlation / Real.log (N + 2 : ℝ) ≤
        Hcorr.C_correlation / logTwo :=
    div_le_div_of_nonneg_left Hcorr.C_correlation_nonneg hlogTwo hmono
  calc
    |explicitQuadraticLogGammaComponent N| +
          |explicitQuadraticLogRatioComponent N +
              cutoffMobiusBernoulliCorrelationValue N - 1 +
                2 * (explicitLinearMobiusSum N + 1)|
        ≤ Hcorr.C_correlation / Real.log (N + 2 : ℝ) ^ 2 := hcorr
    _ = (Hcorr.C_correlation / Real.log (N + 2 : ℝ)) /
          Real.log (N + 2 : ℝ) := by ring
    _ ≤ (Hcorr.C_correlation / logTwo) /
          Real.log (N + 2 : ℝ) :=
      div_le_div_of_nonneg_right hratio hlogN.le

/-- The residual package gives the log-gamma field of
`QuadraticInteractionEstimates`. -/
theorem explicitQuadraticLogGammaComponent_bound_of_normResidual
    (H_res : QuadraticInteractionNormResidual) (N : ℕ) :
    |explicitQuadraticLogGammaComponent N| ≤
      H_res.C_norm / Real.log (N + 2 : ℝ) := by
  have h := H_res.norm_loggamma_package_bound N
  exact (le_add_of_nonneg_right (abs_nonneg _)).trans h

/-- H14 linear estimates plus the norm residual give the interaction-remainder
field of `QuadraticInteractionEstimates`. -/
theorem explicitQuadraticInteractionRemainder_bound_of_linear_and_normResidual
    (H_linear : LinearMobiusDirichletEstimates)
    (H_res : QuadraticInteractionNormResidual) (N : ℕ) :
    |explicitQuadraticInteractionRemainder N| ≤
      (H_res.C_norm +
          2 * (H_linear.C_log +
            |1 - Real.eulerMascheroniConstant| * H_linear.C_overK)) /
        Real.log (N + 2 : ℝ) := by
  rw [explicitQuadraticInteractionRemainder_eq_defect_sub_loggamma_sub_linear]
  let C_linear :=
    H_linear.C_log + |1 - Real.eulerMascheroniConstant| * H_linear.C_overK
  have hcenter :
      |explicitLinearMobiusSum N + 1| ≤ C_linear / Real.log (N + 2 : ℝ) :=
    (linear_mobius_centered_estimate_of_dirichlet_estimates H_linear).bound N
  have hres_all := H_res.norm_loggamma_package_bound N
  have hres :
      |cutoffMobiusDefectEnergy N - explicitQuadraticLogGammaComponent N| ≤
        H_res.C_norm / Real.log (N + 2 : ℝ) :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans hres_all
  calc
    |cutoffMobiusDefectEnergy N - explicitQuadraticLogGammaComponent N -
        2 * (explicitLinearMobiusSum N + 1)|
        ≤ |cutoffMobiusDefectEnergy N - explicitQuadraticLogGammaComponent N| +
            |2 * (explicitLinearMobiusSum N + 1)| := by
          simpa [sub_eq_add_neg] using
            (abs_add_le
            (cutoffMobiusDefectEnergy N - explicitQuadraticLogGammaComponent N)
            (-(2 * (explicitLinearMobiusSum N + 1))))
    _ = |cutoffMobiusDefectEnergy N - explicitQuadraticLogGammaComponent N| +
            2 * |explicitLinearMobiusSum N + 1| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ H_res.C_norm / Real.log (N + 2 : ℝ) +
            2 * (C_linear / Real.log (N + 2 : ℝ)) := by
          exact add_le_add hres
            (mul_le_mul_of_nonneg_left hcenter (by norm_num : (0 : ℝ) ≤ 2))
    _ = (H_res.C_norm + 2 * C_linear) / Real.log (N + 2 : ℝ) := by
          ring

/-- The residue component is definitionally zero. -/
theorem explicitCutoffResidueComponent_zero_bound (N : ℕ) :
    |explicitCutoffResidueComponent N| ≤ 0 / Real.log (N + 2 : ℝ) := by
  simp [explicitCutoffResidueComponent]

/-- H14 linear Möbius estimates plus the single norm residual discharge the
current `QuadraticInteractionEstimates` interface. -/
noncomputable def quadraticInteractionEstimates_of_linearDirichlet_and_normResidual
    (H_linear : LinearMobiusDirichletEstimates)
    (H_res : QuadraticInteractionNormResidual) :
    QuadraticInteractionEstimates := by
  let C_linear :=
    H_linear.C_log + |1 - Real.eulerMascheroniConstant| * H_linear.C_overK
  refine
    { C_loggamma := H_res.C_norm
      C_interaction := H_res.C_norm + 2 * C_linear
      C_residue := 0
      C_pos := ?_
      loggamma_bound := explicitQuadraticLogGammaComponent_bound_of_normResidual H_res
      interaction_bound :=
        explicitQuadraticInteractionRemainder_bound_of_linear_and_normResidual H_linear H_res
      residue_bound := explicitCutoffResidueComponent_zero_bound }
  have hlin : 0 < C_linear := H_linear.C_pos
  have hnorm : 0 ≤ H_res.C_norm := H_res.C_norm_nonneg
  dsimp [C_linear]
  linarith

/-- The requested H14-facing wrapper: a `ClassicalMertensAPI` instance supplies
the linear Dirichlet estimates, and the single norm residual supplies the
remaining quadratic input. -/
noncomputable def quadraticInteractionEstimates_of_mertens_and_normResidual
    (H_mertens : MobiusSummatory.ClassicalMertensAPI)
    (H_res : QuadraticInteractionNormResidual) :
    QuadraticInteractionEstimates :=
  quadraticInteractionEstimates_of_linearDirichlet_and_normResidual
    (MobiusSummatory.linear_mobius_dirichlet_estimates_of_classical_api H_mertens)
    H_res

/-- Final C4 wiring: classical Mertens decay supplies every H14 input, while
the single centered Möbius--Bernoulli correlation estimate supplies the
remaining H15 norm residual. -/
noncomputable def quadraticInteractionEstimates_of_decay_and_bernoulliCorrelation
    (H : MobiusSummatory.ClassicalMertensDecay)
    (Hcorr : QuadraticInteractionBernoulliCorrelationEstimate H) :
    QuadraticInteractionEstimates :=
  quadraticInteractionEstimates_of_mertens_and_normResidual
    (MobiusSummatory.ClassicalMertensAPI.ofDecayOnly H)
    (quadraticInteractionNormResidual_of_bernoulliCorrelation H Hcorr)

end KernelNormFinish

end RH.Criteria.NymanBeurling.QuadraticInteraction
