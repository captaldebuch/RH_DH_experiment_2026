import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperSpectral
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmKernel
import RiemannHypothesis.Criteria.NymanBeurling.BBLSAutocorrelation
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

/-!
# Cotangent reduction of the signed BCF logarithmic-taper expression

This file isolates the exact finite algebra needed by a possible
Vasyunin/Bettin--Conrey or automorphic proof route.  It first records the
pointwise Vasyunin evaluation as a reusable package, and then constructs that
package unconditionally from Mathlib's `p = -1` positive-half-line change of
variables and the proved BBLS rational period reduction.

The main identity separates the complete signed H15 expression into

* a factorized product of two finite Möbius moments;
* the elementary logarithmic-ratio bilinear form;
* one oriented Vasyunin cotangent bilinear form; and
* the original linear correction and constant.

In particular, an automorphic estimate must still control the *coupled* sum
of all four pieces.  Bounding the cotangent form in isolation is not enough.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperCotangentReduction

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.VasyuninGram

/-- A clean interface for the classical pointwise Vasyunin evaluation.  This
is a hypothesis structure, not an axiom declaration. -/
structure VasyuninGramFormulaPackage where
  gram_formula : ∀ h k : ℕ, 0 < h → 0 < k →
    baezDuarteGramEntry h k = vasyuninBEntryFormula h k

/-- Axiom-free inversion substitution on the positive half-line.  This is
the specialization `p = -1` of Mathlib's change of variables
`integral_comp_rpow_Ioi`; unlike the older project bridge, it requires no
measurability or integrability hypotheses because the Bochner integral uses
the usual zero value for nonintegrable functions. -/
theorem setIntegral_Ioi_inv_substitution (f : ℝ → ℝ) :
    (∫ x in Set.Ioi (0 : ℝ), f (1 / x)) =
      ∫ t in Set.Ioi (0 : ℝ), f t * (1 / t ^ 2) := by
  have hsub := MeasureTheory.integral_comp_rpow_Ioi
    (g := fun y : ℝ => f (1 / y)) (p := (-1 : ℝ)) (by norm_num)
  symm
  calc
    (∫ t in Set.Ioi (0 : ℝ), f t * (1 / t ^ 2)) =
        ∫ t in Set.Ioi (0 : ℝ),
          (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
            (fun y : ℝ => f (1 / y)) (t ^ (-1 : ℝ)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht
      change f t * (1 / t ^ 2) =
        (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
          f (1 / (t ^ (-1 : ℝ)))
      rw [show (-1 : ℝ) - 1 = -2 by norm_num,
        Real.rpow_neg ht.le, Real.rpow_two, Real.rpow_neg_one]
      simp only [abs_neg, abs_one, one_mul, smul_eq_mul]
      field_simp [ht0]
    _ = ∫ x in Set.Ioi (0 : ℝ), f (1 / x) := hsub

/-- The original Báez--Duarte Gram integral in the BBLS transformed
coordinate.  This is the precise point where the inversion substitution is
used; all remaining steps are the already-proved rational period reduction. -/
theorem baezDuarteGramEntry_eq_bblsIntegral
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    baezDuarteGramEntry h k =
      ∫ t in Set.Ioi (0 : ℝ),
        Int.fract (t / (h : ℝ)) * Int.fract (t / (k : ℝ)) / t ^ 2 := by
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold baezDuarteGramEntry
  calc
    (∫ x in Set.Ioi (0 : ℝ),
        Int.fract (1 / ((h : ℝ) * x)) *
          Int.fract (1 / ((k : ℝ) * x))) =
        ∫ x in Set.Ioi (0 : ℝ),
          (fun t : ℝ =>
            Int.fract (t / (h : ℝ)) * Int.fract (t / (k : ℝ))) (1 / x) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hfirst : (1 / x) / (h : ℝ) = 1 / ((h : ℝ) * x) := by
        field_simp [hh0, hx0]
      have hsecond : (1 / x) / (k : ℝ) = 1 / ((k : ℝ) * x) := by
        field_simp [hk0, hx0]
      change
        Int.fract (1 / ((h : ℝ) * x)) * Int.fract (1 / ((k : ℝ) * x)) =
          Int.fract ((1 / x) / (h : ℝ)) * Int.fract ((1 / x) / (k : ℝ))
      rw [hfirst, hsecond]
    _ = ∫ t in Set.Ioi (0 : ℝ),
          (Int.fract (t / (h : ℝ)) * Int.fract (t / (k : ℝ))) *
            (1 / t ^ 2) :=
      setIntegral_Ioi_inv_substitution
        (fun t : ℝ => Int.fract (t / (h : ℝ)) * Int.fract (t / (k : ℝ)))
    _ = ∫ t in Set.Ioi (0 : ℝ),
          Int.fract (t / (h : ℝ)) * Int.fract (t / (k : ℝ)) / t ^ 2 := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t _
      ring

/-- Axiom-free pointwise Vasyunin formula.  The proof combines the preceding
Mathlib inversion substitution with the clean BBLS period unfolding and
cotangent evaluation; it does not use the older project axiom
`setIntegral_Ioo_inv_substitution_bridge` or the global real
`baezDuarte_prop21`. -/
theorem baezDuarteGramEntry_eq_vasyuninBEntryFormula_proved
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    baezDuarteGramEntry h k = vasyuninBEntryFormula h k := by
  calc
    baezDuarteGramEntry h k =
        ∫ t in Set.Ioi (0 : ℝ),
          Int.fract (t / (h : ℝ)) * Int.fract (t / (k : ℝ)) / t ^ 2 :=
      baezDuarteGramEntry_eq_bblsIntegral h k hh hk
    _ = (∑' n : ℕ, ∫ s in Set.Ioc (0 : ℝ) (Nat.lcm h k : ℝ),
          Int.fract (s / (h : ℝ)) * Int.fract (s / (k : ℝ)) /
            ((n : ℝ) * (Nat.lcm h k : ℝ) + s) ^ 2) :=
      (bbls_period_unfolding h k hh hk).symm
    _ = vasyuninBEntry h k := bbls_tsum_eq_vasyuninBEntry h k hh hk
    _ = vasyuninBEntryFormula h k := rfl

/-- Fully proved pointwise Vasyunin package, now independent of the older
custom inversion axiom. -/
noncomputable def vasyuninGramFormulaPackageProved :
    VasyuninGramFormulaPackage where
  gram_formula := baezDuarteGramEntry_eq_vasyuninBEntryFormula_proved

/-- The rational `S₁` value obtained by solving Ehm's pointwise Gram formula
after replacing the Gram entry by Vasyunin's explicit formula. -/
noncomputable def vasyuninS1RationalKernel (u v : ℕ) : ℝ :=
  (u : ℝ) *
    (vasyuninBEntryFormula u v -
      (v : ℝ)⁻¹ *
        (ehmK + Real.log ((v : ℝ) / (u : ℝ)) / 2))

/-- Exact bridge between the unconditional autocorrelation realization of
Ehm's `S₁` and the cotangent formula, conditional only on the explicitly
packaged pointwise Vasyunin evaluation. -/
theorem ehmS1Autocorrelation_eq_vasyuninS1RationalKernel
    (H : VasyuninGramFormulaPackage) (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ehmS1Autocorrelation ((v : ℝ) / (u : ℝ)) =
      vasyuninS1RationalKernel u v := by
  have hgram := baezDuarteGramEntry_eq_ehmS1Autocorrelation u v hu hv
  rw [H.gram_formula u v hu hv] at hgram
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  unfold vasyuninS1RationalKernel
  field_simp [hu0] at hgram ⊢
  linarith

/-- Unconditional Ehm-to-cotangent rational-kernel bridge. -/
theorem ehmS1Autocorrelation_eq_vasyuninS1RationalKernel_proved
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ehmS1Autocorrelation ((v : ℝ) / (u : ℝ)) =
      vasyuninS1RationalKernel u v :=
  ehmS1Autocorrelation_eq_vasyuninS1RationalKernel
    vasyuninGramFormulaPackageProved u v hu hv

/-- The unweighted finite mass of the logarithmically tapered Möbius
coefficients. -/
noncomputable def cotangentDirichletMass (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, dirichletCoeff N h

/-- The harmonic finite mass of the logarithmically tapered Möbius
coefficients. -/
noncomputable def cotangentDirichletHarmonicMass (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, dirichletCoeff N h / (h : ℝ)

/-- The elementary logarithmic-ratio part of Vasyunin's explicit formula,
summed against the two logarithmically tapered Möbius coefficients. -/
noncomputable def vasyuninLogRatioBilinear (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    dirichletCoeff N h * dirichletCoeff N k *
      (((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) *
        Real.log ((h : ℝ) / (k : ℝ)))

/-- One oriented Vasyunin cotangent bilinear form.  Symmetry of the square
index set turns the two orientations in the pointwise formula into twice
this expression. -/
noncomputable def vasyuninCotangentBilinear (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    dirichletCoeff N h * dirichletCoeff N k /
      ((h : ℝ) * (k : ℝ)) * cotangentSumVFormula h k

/-- The complete finite cotangent-side expression.  The linear correction
and constant remain coupled to the two bilinear pieces. -/
noncomputable def vasyuninCoupledExpression (N : ℕ) : ℝ :=
  (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) *
      cotangentDirichletMass N * cotangentDirichletHarmonicMass N +
    vasyuninLogRatioBilinear N - Real.pi * vasyuninCotangentBilinear N +
    2 * gramLinearCorrection N + 1

/-- The constant part of the double Vasyunin sum factorizes exactly into the
ordinary and harmonic finite coefficient masses. -/
theorem vasyuninConstantBilinear_eq_mass_mul_harmonicMass (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      dirichletCoeff N h * dirichletCoeff N k *
        ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
          (1 / (h : ℝ) + 1 / (k : ℝ)))) =
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) *
        cotangentDirichletMass N * cotangentDirichletHarmonicMass N := by
  classical
  let C := Real.log (2 * Real.pi) - Real.eulerMascheroniConstant
  let S := Finset.Icc 1 N
  have hprod (f g : ℕ → ℝ) :
      (∑ h ∈ S, f h) * (∑ k ∈ S, g k) =
        ∑ h ∈ S, ∑ k ∈ S, f h * g k := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
  have hfirst :
      (∑ h ∈ S, ∑ k ∈ S,
        dirichletCoeff N h * dirichletCoeff N k *
          (C / 2 * (1 / (h : ℝ)))) =
        C / 2 *
          ((∑ h ∈ S, dirichletCoeff N h / (h : ℝ)) *
            ∑ k ∈ S, dirichletCoeff N k) := by
    rw [hprod]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsecond :
      (∑ h ∈ S, ∑ k ∈ S,
        dirichletCoeff N h * dirichletCoeff N k *
          (C / 2 * (1 / (k : ℝ)))) =
        C / 2 *
          ((∑ h ∈ S, dirichletCoeff N h) *
            ∑ k ∈ S, dirichletCoeff N k / (k : ℝ)) := by
    rw [hprod]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro k _
    ring
  change
    (∑ h ∈ S, ∑ k ∈ S,
      dirichletCoeff N h * dirichletCoeff N k *
        (C / 2 * (1 / (h : ℝ) + 1 / (k : ℝ)))) =
      C * (∑ h ∈ S, dirichletCoeff N h) *
        ∑ h ∈ S, dirichletCoeff N h / (h : ℝ)
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hfirst, hsecond]
  ring

/-- On the symmetric square index set, the two cotangent orientations in
Vasyunin's pointwise formula collapse to one oriented bilinear sum. -/
theorem vasyuninSymmetricCotangentBilinear_eq (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      dirichletCoeff N h * dirichletCoeff N k *
        (-Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
          (cotangentSumVFormula h k + cotangentSumVFormula k h))) =
      -Real.pi * vasyuninCotangentBilinear N := by
  classical
  let S := Finset.Icc 1 N
  change
    (∑ h ∈ S, ∑ k ∈ S,
      dirichletCoeff N h * dirichletCoeff N k *
        (-Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
          (cotangentSumVFormula h k + cotangentSumVFormula k h))) =
      -Real.pi *
        ∑ h ∈ S, ∑ k ∈ S,
          dirichletCoeff N h * dirichletCoeff N k /
            ((h : ℝ) * (k : ℝ)) * cotangentSumVFormula h k
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hswap :
      (∑ h ∈ S, ∑ k ∈ S,
        dirichletCoeff N h * dirichletCoeff N k *
          (-Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
            cotangentSumVFormula k h)) =
      ∑ h ∈ S, ∑ k ∈ S,
        dirichletCoeff N h * dirichletCoeff N k *
          (-Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
            cotangentSumVFormula h k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hswap]
  have hsingle :
      (∑ h ∈ S, ∑ k ∈ S,
        dirichletCoeff N h * dirichletCoeff N k *
          (-Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
            cotangentSumVFormula h k)) =
        (-Real.pi / 2) *
          ∑ h ∈ S, ∑ k ∈ S,
            dirichletCoeff N h * dirichletCoeff N k /
              ((h : ℝ) * (k : ℝ)) * cotangentSumVFormula h k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsingle]
  ring

/-- The Gram quadratic form is exactly the three-piece Vasyunin expansion,
assuming only the explicit pointwise Gram formula. -/
theorem gramQuadraticForm_eq_vasyunin_expansion
    (H : VasyuninGramFormulaPackage) (N : ℕ) :
    gramQuadraticForm N =
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) *
          cotangentDirichletMass N * cotangentDirichletHarmonicMass N +
        vasyuninLogRatioBilinear N - Real.pi * vasyuninCotangentBilinear N := by
  classical
  unfold gramQuadraticForm
  have hpointwise :
      (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        dirichletCoeff N h * dirichletCoeff N k * baezDuarteGramEntry h k) =
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        dirichletCoeff N h * dirichletCoeff N k * vasyuninBEntryFormula h k := by
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro k hk
    have hhpos : 0 < h :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hh).1
    have hkpos : 0 < k :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
    rw [H.gram_formula h k hhpos hkpos]
  rw [hpointwise]
  have hsplit :
      (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        dirichletCoeff N h * dirichletCoeff N k * vasyuninBEntryFormula h k) =
      (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        dirichletCoeff N h * dirichletCoeff N k *
          ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
            (1 / (h : ℝ) + 1 / (k : ℝ)))) +
      (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        dirichletCoeff N h * dirichletCoeff N k *
          (((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) *
            Real.log ((h : ℝ) / (k : ℝ)))) +
      (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        dirichletCoeff N h * dirichletCoeff N k *
          (-Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
            (cotangentSumVFormula h k + cotangentSumVFormula k h))) := by
    have hterm (h k : ℕ) :
        dirichletCoeff N h * dirichletCoeff N k * vasyuninBEntryFormula h k =
          dirichletCoeff N h * dirichletCoeff N k *
              ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
                (1 / (h : ℝ) + 1 / (k : ℝ))) +
            dirichletCoeff N h * dirichletCoeff N k *
              (((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) *
                Real.log ((h : ℝ) / (k : ℝ))) +
            dirichletCoeff N h * dirichletCoeff N k *
              (-Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
                (cotangentSumVFormula h k + cotangentSumVFormula k h)) := by
      unfold vasyuninBEntryFormula
      ring
    simp_rw [hterm, Finset.sum_add_distrib]
  rw [hsplit]
  rw [vasyuninConstantBilinear_eq_mass_mul_harmonicMass,
    vasyuninSymmetricCotangentBilinear_eq]
  unfold vasyuninLogRatioBilinear
  ring

/-- Exact cotangent-side realization of the signed H15 expression. -/
theorem coupledGcdRatioExpression_eq_vasyuninCoupledExpression
    (H : VasyuninGramFormulaPackage) (N : ℕ) :
    coupledGcdRatioExpression N = vasyuninCoupledExpression N := by
  rw [← spectralEnergy_eq_coupledGcdRatioExpression,
    ← energy_eq_spectralEnergy,
    energy_eq_gramQuadraticForm_add_linearCorrection,
    gramQuadraticForm_eq_vasyunin_expansion H]
  rfl

/-- Unconditional finite cotangent-side realization of the signed H15
expression. -/
theorem coupledGcdRatioExpression_eq_vasyuninCoupledExpression_proved (N : ℕ) :
    coupledGcdRatioExpression N = vasyuninCoupledExpression N :=
  coupledGcdRatioExpression_eq_vasyuninCoupledExpression
    vasyuninGramFormulaPackageProved N

/-- A putative automorphic estimate must bound the fully coupled Vasyunin
expression, not merely its cotangent summand. -/
structure VasyuninCoupledCancellationEstimate where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ N : ℕ, 2 ≤ N →
    |vasyuninCoupledExpression N| ≤ C / (Real.log (N : ℝ)) ^ α

/-- The exact finite reduction transports a coupled cotangent/automorphic
estimate to the existing H15 cancellation interface. -/
def VasyuninCoupledCancellationEstimate.toCoupledLogTaper
    (Hgram : VasyuninGramFormulaPackage)
    (H : VasyuninCoupledCancellationEstimate) :
    CoupledLogTaperCancellationEstimate where
  C := H.C
  C_pos := H.C_pos
  α := H.α
  α_pos := H.α_pos
  bound N hN := by
    rw [coupledGcdRatioExpression_eq_vasyuninCoupledExpression Hgram]
    exact H.bound N hN

/-- Conversely, the cotangent-side coupled estimate is not a weaker analytic
problem: the exact finite identity transports the original H15 estimate back
to it with the same constants. -/
def VasyuninCoupledCancellationEstimate.ofCoupledLogTaper
    (Hgram : VasyuninGramFormulaPackage)
    (H : CoupledLogTaperCancellationEstimate) :
    VasyuninCoupledCancellationEstimate where
  C := H.C
  C_pos := H.C_pos
  α := H.α
  α_pos := H.α_pos
  bound N hN := by
    rw [← coupledGcdRatioExpression_eq_vasyuninCoupledExpression Hgram]
    exact H.bound N hN

/-- A coupled cotangent/automorphic estimate now closes the existing H15
interface without any additional Gram-formula hypothesis. -/
def VasyuninCoupledCancellationEstimate.toCoupledLogTaperProved
    (H : VasyuninCoupledCancellationEstimate) :
    CoupledLogTaperCancellationEstimate :=
  H.toCoupledLogTaper vasyuninGramFormulaPackageProved

end RH.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
