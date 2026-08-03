import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperSpectral

/-!
# Ehm decomposition of the BCF logarithmic-taper energy

This module records the finite algebra in the `q = 1` decomposition from
Werner Ehm, *On certain Gram matrices and their associated series* (2024),
Section 8.1.  The analytic kernel evaluation is deliberately a package:
the existing project has not yet kernel-verified the required `R₁`/`S₁`
representation.  Once such a package is supplied, all conversion to the
fully coupled BCF energy is proved here by finite algebra.

In particular, this module does **not** assert a decay estimate for the
inversion error or for the resulting coupled expression.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhm

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral

/-- Ehm's finite Mertens-type moment for the BCF coefficients. -/
noncomputable def ehmM (j N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, dirichletCoeff N n * Real.log (n : ℝ) ^ j

/-- Ehm's finite Landau-type moment for the BCF coefficients. -/
noncomputable def ehmL (j N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    dirichletCoeff N n * Real.log (n : ℝ) ^ j / (n : ℝ)

/-- The untapered finite Möbius moment underlying `ehmM`. -/
noncomputable def rawMobiusMoment (j N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ j

/-- The untapered harmonic Möbius moment underlying `ehmL`. -/
noncomputable def rawMobiusHarmonicMoment (j N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ j / (n : ℝ)

/-- The logarithmic taper expresses Ehm's Mertens-type moment as the
difference of two consecutive untapered Möbius moments. -/
theorem ehmM_eq_rawMobiusMoments (j N : ℕ) (hN : 2 ≤ N) :
    ehmM j N = rawMobiusMoment j N - rawMobiusMoment (j + 1) N / Real.log N := by
  classical
  unfold ehmM rawMobiusMoment dirichletCoeff
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [weight_of_two_le hN]
  rw [show j + 1 = Nat.succ j by omega, pow_succ]
  ring

/-- The logarithmic taper expresses Ehm's Landau-type moment as the
difference of two consecutive untapered harmonic Möbius moments. -/
theorem ehmL_eq_rawMobiusHarmonicMoments (j N : ℕ) (hN : 2 ≤ N) :
    ehmL j N = rawMobiusHarmonicMoment j N -
      rawMobiusHarmonicMoment (j + 1) N / Real.log N := by
  classical
  unfold ehmL rawMobiusHarmonicMoment dirichletCoeff
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [weight_of_two_le hN]
  rw [show j + 1 = Nat.succ j by omega, pow_succ]
  ring

/-- The constant appearing in Ehm's `q = 1` quadratic-form decomposition. -/
noncomputable def ehmK : ℝ :=
  (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant + 1) / 2

/-- The non-error part of Ehm's Section 8.1 decomposition of the quadratic
Gram form. -/
noncomputable def ehmQuadraticMain (N : ℕ) : ℝ :=
  ehmM 0 N * (ehmK * ehmL 0 N + (ehmL 1 N + 1) / 2)
    - (ehmM 1 N * ehmL 0 N) / 2
    + (Real.eulerMascheroniConstant - 1) * ehmL 0 N - ehmL 1 N

/-- The finite error term in Ehm's `q = 1` decomposition.  `S1` and `R1`
are parameters because their analytic definitions and the Gram-kernel formula
are independent of the finite algebra developed in this file. -/
noncomputable def ehmInversionError (S1 R1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) *
    ((∑ n ∈ Finset.Icc 1 N,
        dirichletCoeff N n * S1 ((n : ℝ) / (m : ℝ))) - R1 (1 / (m : ℝ)))

/-- The double sum in Ehm's inversion error before the `R₁` correction is
subtracted.  Naming it separately makes the pointwise kernel formula usable
without duplicating a finite double sum. -/
noncomputable def ehmS1QuadraticTerm (S1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) *
    ∑ n ∈ Finset.Icc 1 N, dirichletCoeff N n * S1 ((n : ℝ) / (m : ℝ))

/-- The one-variable term subtracted from `ehmS1QuadraticTerm` in Ehm's
finite inversion error. -/
noncomputable def ehmR1Correction (R1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) * R1 (1 / (m : ℝ))

/-- Ehm's harmonic-sum function `H(x) = Σ_{1 ≤ k ≤ x} 1/k`, implemented
through the natural floor.  Only positive arguments occur in the Ehm kernel,
but this total definition is convenient for Lean. -/
noncomputable def ehmHarmonic (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, 1 / (k : ℝ)

/-- Ehm's elementary `R₁` function (Ehm, Theorem 2.1, equation (8)).  The
infinite analytic content of the kernel lies in `S₁(x) = Σ_{k ≥ 1} R₁(kx)`;
this finite-floor definition itself is completely elementary. -/
noncomputable def ehmR1 (x : ℝ) : ℝ :=
  Real.log x + Real.eulerMascheroniConstant - ehmHarmonic x -
    (Int.fract x - 1 / 2) / x

/-- The reciprocal values of Ehm's explicit `R₁` function.  This is the
elementary input previously carried abstractly by `EhmR1ReciprocalPackage`.
The `m = 1` endpoint has a one-term harmonic sum; for `m ≥ 2` the harmonic
sum is empty and the fractional part is `1/m`. -/
theorem ehmR1_reciprocal_formula (m : ℕ) (hm : 0 < m) :
    ehmR1 (1 / (m : ℝ)) = (m : ℝ) / 2 - Real.log (m : ℝ) +
      Real.eulerMascheroniConstant - 1 := by
  by_cases hm_one : m = 1
  · subst m
    norm_num [ehmR1, ehmHarmonic]
    ring
  · have hm_two : 2 ≤ m := by omega
    have hm_real_pos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hm_real_one_lt : (1 : ℝ) < (m : ℝ) := by
      exact_mod_cast (show 1 < m by omega)
    have hrecip_pos : 0 < 1 / (m : ℝ) := one_div_pos.mpr hm_real_pos
    have hrecip_lt_one : 1 / (m : ℝ) < 1 := by
      exact (div_lt_one₀ hm_real_pos).mpr hm_real_one_lt
    have hfloor : ⌊1 / (m : ℝ)⌋₊ = 0 :=
      Nat.floor_eq_zero.mpr hrecip_lt_one
    have hfract : Int.fract (1 / (m : ℝ)) = 1 / (m : ℝ) :=
      Int.fract_eq_self.mpr ⟨hrecip_pos.le, hrecip_lt_one⟩
    have hm_real_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_real_pos
    unfold ehmR1 ehmHarmonic
    rw [hfloor, hfract]
    simp only [Finset.Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1),
      Finset.sum_empty, sub_zero]
    rw [show 1 / (m : ℝ) = (m : ℝ)⁻¹ by ring, Real.log_inv]
    field_simp [hm_real_ne]
    ring

/-- Ehm's inversion error is exactly its `S₁` double sum minus its `R₁`
correction. -/
theorem ehmInversionError_eq_S1_sub_R1 (S1 R1 : ℝ → ℝ) (N : ℕ) :
    ehmInversionError S1 R1 N =
      ehmS1QuadraticTerm S1 N - ehmR1Correction R1 N := by
  unfold ehmInversionError ehmS1QuadraticTerm ehmR1Correction
  calc
    _ = ∑ m ∈ Finset.Icc 1 N,
        ((dirichletCoeff N m / (m : ℝ) *
          ∑ n ∈ Finset.Icc 1 N, dirichletCoeff N n * S1 ((n : ℝ) / (m : ℝ))) -
        dirichletCoeff N m / (m : ℝ) * R1 (1 / (m : ℝ))) := by
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib]

/-- The elementary `x = 1/m` specialization of Ehm's `R₁` formula.  This is
kept separate from the Gram-kernel identity: it is a finite algebra input
which future analytic work can establish directly from the periodic-function
definition of `R₁`. -/
structure EhmR1ReciprocalPackage (R1 : ℝ → ℝ) where
  reciprocal_formula : ∀ m : ℕ, 0 < m →
    R1 (1 / (m : ℝ)) = (m : ℝ) / 2 - Real.log (m : ℝ) +
      Real.eulerMascheroniConstant - 1

/-- The elementary `R₁` part of Ehm's kernel package is now supplied by a
proof, rather than by an external analytic interface. -/
noncomputable def ehmR1ReciprocalPackage : EhmR1ReciprocalPackage ehmR1 where
  reciprocal_formula := ehmR1_reciprocal_formula

/-- Summing the reciprocal `R₁` formula gives the exact moment combination
which occurs in Ehm's quadratic decomposition. -/
theorem ehmR1Correction_eq_moments
    {R1 : ℝ → ℝ} (HR : EhmR1ReciprocalPackage R1) (N : ℕ) :
    ehmR1Correction R1 N =
      ehmM 0 N / 2 - ehmL 1 N +
        (Real.eulerMascheroniConstant - 1) * ehmL 0 N := by
  classical
  unfold ehmR1Correction ehmM ehmL
  have hhalf :
      (∑ m ∈ Finset.Icc 1 N,
        dirichletCoeff N m / (m : ℝ) * ((m : ℝ) / 2)) =
        (∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m) / 2 := by
    calc
      _ = ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / 2 := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm_pos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp hm).1
        field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm_pos)]
      _ = _ := by rw [← Finset.sum_div]
  have hconstant :
      (∑ m ∈ Finset.Icc 1 N,
        dirichletCoeff N m / (m : ℝ) *
          (Real.eulerMascheroniConstant - 1)) =
        (Real.eulerMascheroniConstant - 1) *
          ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hlog :
      (∑ m ∈ Finset.Icc 1 N,
        dirichletCoeff N m / (m : ℝ) * Real.log (m : ℝ)) =
        ∑ m ∈ Finset.Icc 1 N,
          dirichletCoeff N m * Real.log (m : ℝ) / (m : ℝ) := by
    apply Finset.sum_congr rfl
    intro m _
    ring
  calc
    _ = ∑ m ∈ Finset.Icc 1 N,
        dirichletCoeff N m / (m : ℝ) *
          ((m : ℝ) / 2 - Real.log (m : ℝ) +
            Real.eulerMascheroniConstant - 1) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hm_pos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one
        (Finset.mem_Icc.mp hm).1
      rw [HR.reciprocal_formula m hm_pos]
    _ = ∑ m ∈ Finset.Icc 1 N,
        ((dirichletCoeff N m / (m : ℝ) * ((m : ℝ) / 2) -
          dirichletCoeff N m / (m : ℝ) * Real.log (m : ℝ)) +
          dirichletCoeff N m / (m : ℝ) *
            (Real.eulerMascheroniConstant - 1)) := by
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hhalf, hconstant, hlog]
      simp only [pow_zero, pow_one, mul_one]

/-- The exact analytic input required to identify the finite Gram form with
Ehm's `R₁`/`S₁` inversion error.  This is a cited analytic interface, not an
axiom: a future formalization of Ehm's kernel representation can construct it.
-/
structure EhmKernelPackage where
  S1 : ℝ → ℝ
  R1 : ℝ → ℝ
  quadratic_decomposition : ∀ N : ℕ, 2 ≤ N →
    gramQuadraticForm N = ehmQuadraticMain N + ehmInversionError S1 R1 N

/-- Ehm's pointwise `q = 1` kernel formula, together with the elementary
reciprocal specialization of `R₁`.  It is the analytic input in Ehm's
Theorem 2.1 which is used in Section 8.1; the theorem below proves that this
pointwise formula implies the
finite quadratic decomposition used by the rest of the project. -/
structure EhmPointwiseKernelPackage where
  S1 : ℝ → ℝ
  R1 : ℝ → ℝ
  r1_reciprocal_formula : ∀ m : ℕ, 0 < m →
    R1 (1 / (m : ℝ)) = (m : ℝ) / 2 - Real.log (m : ℝ) +
      Real.eulerMascheroniConstant - 1
  gram_formula : ∀ u v : ℕ, 0 < u → 0 < v →
    VasyuninGram.baezDuarteGramEntry u v =
      (v : ℝ)⁻¹ * (ehmK + Real.log ((v : ℝ) / (u : ℝ)) / 2) +
        (u : ℝ)⁻¹ * S1 ((v : ℝ) / (u : ℝ))

/-- Reduced pointwise Ehm interface after discharging the elementary `R₁`
part.  Constructing this package still requires Ehm's analytic `S₁` series
and the pointwise Gram-kernel formula, but it no longer requires a separate
reciprocal-value assumption for `R₁`. -/
structure EhmS1PointwiseKernelPackage where
  S1 : ℝ → ℝ
  gram_formula : ∀ u v : ℕ, 0 < u → 0 < v →
    VasyuninGram.baezDuarteGramEntry u v =
      (v : ℝ)⁻¹ * (ehmK + Real.log ((v : ℝ) / (u : ℝ)) / 2) +
        (u : ℝ)⁻¹ * S1 ((v : ℝ) / (u : ℝ))

/-- Insert the explicit `ehmR1` function into the reduced pointwise package. -/
noncomputable def EhmS1PointwiseKernelPackage.toEhmPointwiseKernelPackage
    (H : EhmS1PointwiseKernelPackage) : EhmPointwiseKernelPackage where
  S1 := H.S1
  R1 := ehmR1
  r1_reciprocal_formula := ehmR1_reciprocal_formula
  gram_formula := H.gram_formula

/-- Extract the reciprocal `R₁` interface from the pointwise Ehm package. -/
def EhmPointwiseKernelPackage.toR1ReciprocalPackage
    (H : EhmPointwiseKernelPackage) : EhmR1ReciprocalPackage H.R1 where
  reciprocal_formula := H.r1_reciprocal_formula

private theorem sum_mul_sum_Icc (N : ℕ) (f g : ℕ → ℝ) :
    (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N, f u * g v) =
      (∑ u ∈ Finset.Icc 1 N, f u) * (∑ v ∈ Finset.Icc 1 N, g v) := by
  exact (Finset.sum_mul_sum (Finset.Icc 1 N) (Finset.Icc 1 N) f g).symm

/-- Finite summation of Ehm's pointwise Gram-kernel formula.  This theorem is
purely algebraic: it does not use an asymptotic estimate and does not assert
any cancellation. -/
theorem gramQuadraticForm_eq_ehmS1QuadraticTerm_add_moments
    (H : EhmPointwiseKernelPackage) (N : ℕ) :
    gramQuadraticForm N =
      ehmK * ehmM 0 N * ehmL 0 N + ehmM 0 N * ehmL 1 N / 2 -
        ehmM 1 N * ehmL 0 N / 2 + ehmS1QuadraticTerm H.S1 N := by
  classical
  have hentry (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
      dirichletCoeff N u * dirichletCoeff N v *
          VasyuninGram.baezDuarteGramEntry u v =
        dirichletCoeff N u *
            (dirichletCoeff N v / (v : ℝ) * ehmK) +
          dirichletCoeff N u *
            (dirichletCoeff N v * Real.log (v : ℝ) / (v : ℝ) / 2) -
          (dirichletCoeff N u * Real.log (u : ℝ) / 2) *
            (dirichletCoeff N v / (v : ℝ)) +
          (dirichletCoeff N u / (u : ℝ)) *
            (dirichletCoeff N v * H.S1 ((v : ℝ) / (u : ℝ))) := by
    have hu_ne : (u : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hu)
    have hv_ne : (v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hv)
    rw [H.gram_formula u v hu hv, Real.log_div hv_ne hu_ne]
    ring
  have hK :
      (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        dirichletCoeff N u * (dirichletCoeff N v / (v : ℝ) * ehmK)) =
        ehmK * ehmM 0 N * ehmL 0 N := by
    calc
      _ = ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
          (dirichletCoeff N u * ehmK) *
            (dirichletCoeff N v / (v : ℝ)) := by
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = (∑ u ∈ Finset.Icc 1 N, dirichletCoeff N u * ehmK) *
          (∑ v ∈ Finset.Icc 1 N, dirichletCoeff N v / (v : ℝ)) :=
        sum_mul_sum_Icc N _ _
      _ = _ := by
        have hKsum :
            (∑ u ∈ Finset.Icc 1 N, dirichletCoeff N u * ehmK) =
              ehmK * ∑ u ∈ Finset.Icc 1 N, dirichletCoeff N u := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          ring
        rw [hKsum]
        unfold ehmM ehmL
        simp only [pow_zero, mul_one, div_eq_mul_inv]
  have hL1half :
      (∑ v ∈ Finset.Icc 1 N,
        dirichletCoeff N v * Real.log (v : ℝ) / (v : ℝ) / 2) =
        ehmL 1 N / 2 := by
    rw [← Finset.sum_div]
    unfold ehmL
    simp only [pow_one]
  have hV :
      (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        dirichletCoeff N u *
          (dirichletCoeff N v * Real.log (v : ℝ) / (v : ℝ) / 2)) =
        ehmM 0 N * ehmL 1 N / 2 := by
    calc
      _ = (∑ u ∈ Finset.Icc 1 N, dirichletCoeff N u) *
          (∑ v ∈ Finset.Icc 1 N,
            dirichletCoeff N v * Real.log (v : ℝ) / (v : ℝ) / 2) :=
        sum_mul_sum_Icc N _ _
      _ = _ := by
        rw [hL1half]
        unfold ehmM
        simp only [pow_zero, mul_one]
        ring
  have hM1half :
      (∑ u ∈ Finset.Icc 1 N,
        dirichletCoeff N u * Real.log (u : ℝ) / 2) = ehmM 1 N / 2 := by
    rw [← Finset.sum_div]
    unfold ehmM
    simp only [pow_one]
  have hU :
      (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        (dirichletCoeff N u * Real.log (u : ℝ) / 2) *
          (dirichletCoeff N v / (v : ℝ))) =
        ehmM 1 N * ehmL 0 N / 2 := by
    calc
      _ = (∑ u ∈ Finset.Icc 1 N,
          dirichletCoeff N u * Real.log (u : ℝ) / 2) *
          (∑ v ∈ Finset.Icc 1 N, dirichletCoeff N v / (v : ℝ)) :=
        sum_mul_sum_Icc N _ _
      _ = _ := by
        rw [hM1half]
        unfold ehmL
        simp only [pow_zero, mul_one]
        ring
  have hKV :
      (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        (dirichletCoeff N u * (dirichletCoeff N v / (v : ℝ) * ehmK) +
          dirichletCoeff N u *
            (dirichletCoeff N v * Real.log (v : ℝ) / (v : ℝ) / 2))) =
        ehmK * ehmM 0 N * ehmL 0 N + ehmM 0 N * ehmL 1 N / 2 := by
    calc
      _ = ∑ u ∈ Finset.Icc 1 N,
          ((∑ v ∈ Finset.Icc 1 N,
            dirichletCoeff N u * (dirichletCoeff N v / (v : ℝ) * ehmK)) +
          ∑ v ∈ Finset.Icc 1 N,
            dirichletCoeff N u *
              (dirichletCoeff N v * Real.log (v : ℝ) / (v : ℝ) / 2)) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_add_distrib]
      _ = _ := by
        rw [Finset.sum_add_distrib, hK, hV]
  have hS :
      (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        (dirichletCoeff N u / (u : ℝ)) *
          (dirichletCoeff N v * H.S1 ((v : ℝ) / (u : ℝ)))) =
        ehmS1QuadraticTerm H.S1 N := by
    unfold ehmS1QuadraticTerm
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
  unfold gramQuadraticForm
  calc
    _ = ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        (dirichletCoeff N u *
            (dirichletCoeff N v / (v : ℝ) * ehmK) +
          dirichletCoeff N u *
            (dirichletCoeff N v * Real.log (v : ℝ) / (v : ℝ) / 2) -
          (dirichletCoeff N u * Real.log (u : ℝ) / 2) *
            (dirichletCoeff N v / (v : ℝ)) +
          (dirichletCoeff N u / (u : ℝ)) *
            (dirichletCoeff N v * H.S1 ((v : ℝ) / (u : ℝ)))) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hu_pos : 0 < u := lt_of_lt_of_le Nat.zero_lt_one
        (Finset.mem_Icc.mp hu).1
      apply Finset.sum_congr rfl
      intro v hv
      have hv_pos : 0 < v := lt_of_lt_of_le Nat.zero_lt_one
        (Finset.mem_Icc.mp hv).1
      exact hentry u v hu_pos hv_pos
    _ =
        (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
          (dirichletCoeff N u * (dirichletCoeff N v / (v : ℝ) * ehmK) +
            dirichletCoeff N u *
              (dirichletCoeff N v * Real.log (v : ℝ) / (v : ℝ) / 2))) -
        (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
          (dirichletCoeff N u * Real.log (u : ℝ) / 2) *
            (dirichletCoeff N v / (v : ℝ))) +
        (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
          (dirichletCoeff N u / (u : ℝ)) *
            (dirichletCoeff N v * H.S1 ((v : ℝ) / (u : ℝ)))) := by
      calc
        _ = ∑ u ∈ Finset.Icc 1 N,
            ((∑ v ∈ Finset.Icc 1 N,
              ((dirichletCoeff N u * (dirichletCoeff N v / (v : ℝ) * ehmK) +
                dirichletCoeff N u *
                  (dirichletCoeff N v * Real.log (v : ℝ) / (v : ℝ) / 2)) -
                (dirichletCoeff N u * Real.log (u : ℝ) / 2) *
                  (dirichletCoeff N v / (v : ℝ)))) +
            (∑ v ∈ Finset.Icc 1 N,
              (dirichletCoeff N u / (u : ℝ)) *
                (dirichletCoeff N v * H.S1 ((v : ℝ) / (u : ℝ))))) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_add_distrib]
        _ = ∑ u ∈ Finset.Icc 1 N,
            (((∑ v ∈ Finset.Icc 1 N,
              (dirichletCoeff N u * (dirichletCoeff N v / (v : ℝ) * ehmK) +
                dirichletCoeff N u *
                  (dirichletCoeff N v * Real.log (v : ℝ) / (v : ℝ) / 2))) -
              (∑ v ∈ Finset.Icc 1 N,
                (dirichletCoeff N u * Real.log (u : ℝ) / 2) *
                  (dirichletCoeff N v / (v : ℝ)))) +
            (∑ v ∈ Finset.Icc 1 N,
              (dirichletCoeff N u / (u : ℝ)) *
                (dirichletCoeff N v * H.S1 ((v : ℝ) / (u : ℝ))))) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_sub_distrib]
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
      rw [hKV, hU, hS]

/-- The pointwise Ehm formula reconstructs the existing quadratic-decomposition
interface.  In particular, the only remaining analytic work is to construct
the pointwise package and prove the separate coupled cancellation estimate. -/
def EhmPointwiseKernelPackage.toEhmKernelPackage
    (H : EhmPointwiseKernelPackage) : EhmKernelPackage where
  S1 := H.S1
  R1 := H.R1
  quadratic_decomposition := by
    intro N _
    rw [gramQuadraticForm_eq_ehmS1QuadraticTerm_add_moments H N,
      ehmInversionError_eq_S1_sub_R1,
      ehmR1Correction_eq_moments H.toR1ReciprocalPackage N]
    unfold ehmQuadraticMain
    ring

/-- The reduced `S₁` package yields the exact Ehm finite decomposition with
the explicit `ehmR1`; the only imported analytic assertion is its displayed
pointwise Gram formula. -/
noncomputable def EhmS1PointwiseKernelPackage.toEhmKernelPackage
    (H : EhmS1PointwiseKernelPackage) : EhmKernelPackage :=
  H.toEhmPointwiseKernelPackage.toEhmKernelPackage

/-- The correction which remains coupled with Ehm's inversion error after
the linear term and constant in the BCF energy are restored. -/
noncomputable def ehmCoupledRemainder (N : ℕ) : ℝ :=
  ehmL 1 N + (1 - Real.eulerMascheroniConstant) * ehmL 0 N + 1
    + ehmM 0 N * (ehmK * ehmL 0 N + (ehmL 1 N + 1) / 2)
    - (ehmM 1 N * ehmL 0 N) / 2

/-- The BCF linear Gram correction is exactly Ehm's two lowest Landau-type
moments. -/
theorem gramLinearCorrection_eq_ehmL (N : ℕ) :
    gramLinearCorrection N =
      ehmL 1 N + (1 - Real.eulerMascheroniConstant) * ehmL 0 N := by
  classical
  unfold gramLinearCorrection ehmL
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [RH.Certificates.innerProductChiRho_formula]
  have hcast : ((↑(k - 1) : ℝ) + 1) = (k : ℝ) := by
    norm_cast
    omega
  rw [hcast]
  simp only [pow_zero, pow_one]
  ring

/-- The GCD-ratio target is the original quadratic Gram form with its linear
correction and constant restored. -/
theorem coupledGcdRatioExpression_eq_gramQuadraticForm (N : ℕ) :
    coupledGcdRatioExpression N =
      gramQuadraticForm N + 2 * gramLinearCorrection N + 1 := by
  calc
    coupledGcdRatioExpression N = energy N := by
      simpa only [coupledGcdRatioExpression] using
        (energy_eq_gcdRatioFormula N).symm
    _ = gramQuadraticForm N + 2 * gramLinearCorrection N + 1 :=
      energy_eq_gramQuadraticForm_add_linearCorrection N

/-- Ehm's exact decomposition, rewritten as the fully coupled energy which
Task 3 must bound.  This is the reusable bridge from an `R₁`/`S₁` kernel
formula to the existing `CoupledLogTaperCancellationEstimate` interface. -/
theorem coupledGcdRatioExpression_eq_ehmInversionError_add_remainder
    (H : EhmKernelPackage) (N : ℕ) (hN : 2 ≤ N) :
    coupledGcdRatioExpression N =
      ehmInversionError H.S1 H.R1 N + ehmCoupledRemainder N := by
  rw [coupledGcdRatioExpression_eq_gramQuadraticForm,
    H.quadratic_decomposition N hN, gramLinearCorrection_eq_ehmL]
  unfold ehmQuadraticMain ehmCoupledRemainder
  ring

/-- A bound for Ehm's **whole coupled expression** is precisely a bound for
the original Task-3 target.  This equivalence deliberately does not split the
inversion error from the Mertens/Landau remainder. -/
theorem coupledLogTaper_bound_iff_ehmCoupled_bound
    (H : EhmKernelPackage) (C α : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    |coupledGcdRatioExpression N| ≤ C / (Real.log (N : ℝ)) ^ α ↔
      |ehmInversionError H.S1 H.R1 N + ehmCoupledRemainder N| ≤
        C / (Real.log (N : ℝ)) ^ α := by
  rw [coupledGcdRatioExpression_eq_ehmInversionError_add_remainder H N hN]

/-- The still-open Ehm-form analytic estimate.  It is a hypothesis object,
not an axiom and not a theorem proved from the decomposition. -/
structure EhmCoupledCancellationEstimate (H : EhmKernelPackage) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ N : ℕ, 2 ≤ N →
    |ehmInversionError H.S1 H.R1 N + ehmCoupledRemainder N| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- An Ehm-form coupled cancellation estimate instantiates, but does not
prove, the project-wide open cancellation interface. -/
def coupledLogTaperCancellation_of_ehm
    (H : EhmKernelPackage) (HE : EhmCoupledCancellationEstimate H) :
    CoupledLogTaperCancellationEstimate where
  C := HE.C
  C_pos := HE.C_pos
  α := HE.α
  α_pos := HE.α_pos
  bound := fun N hN =>
    (coupledLogTaper_bound_iff_ehmCoupled_bound H HE.C HE.α N hN).mpr
      (HE.bound N hN)

end RH.Criteria.NymanBeurling.BCFLogTaperEhm
