import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhm

/-!
# An unconditional autocorrelation realization of Ehm's pointwise kernel

The downstream Ehm decomposition only needs the pointwise Gram formula at
positive rational ratios.  This file constructs that package directly from
the concrete Gram integral by positive dilation.  It deliberately avoids the
project's still-axiomatized global `x ↦ 1/x` substitution bridge, and does not
identify the resulting function with Ehm's separate series `Σ k, R₁(kx)`;
that analytic series identity remains an optional reusable theorem.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel

open scoped MeasureTheory
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The positive-half-line fractional-part autocorrelation in the original
Gram coordinate.  Formally proving its equivalence with the more usual
`{t}{rt}/t²` coordinate is not needed for the pointwise kernel package. -/
noncomputable def ehmAutocorrelation (r : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    Int.fract (1 / x) * Int.fract (r / x)

/-- Ehm's `S₁` kernel, realized directly from the autocorrelation identity.
Only its values at positive ratios are used below. -/
noncomputable def ehmS1Autocorrelation (r : ℝ) : ℝ :=
  (ehmAutocorrelation r - ehmK - Real.log r / 2) / r

/-- Scaling the transformed Gram integral gives the autocorrelation at the
rational ratio `v/u`. -/
theorem baezDuarteGramEntry_eq_inv_mul_ehmAutocorrelation
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    baezDuarteGramEntry u v =
      (v : ℝ)⁻¹ * ehmAutocorrelation ((v : ℝ) / (u : ℝ)) := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hcomp := MeasureTheory.integral_comp_mul_right_Ioi
    (fun x : ℝ => Int.fract (1 / x) *
      Int.fract (((v : ℝ) / (u : ℝ)) / x)) 0 hvR
  simp only [zero_mul, smul_eq_mul] at hcomp
  have hcongr : baezDuarteGramEntry u v =
      ∫ x in Set.Ioi (0 : ℝ),
        Int.fract (1 / (x * (v : ℝ))) *
          Int.fract (((v : ℝ) / (u : ℝ)) / (x * (v : ℝ))) := by
    unfold baezDuarteGramEntry
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
    have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hfirst : 1 / ((v : ℝ) * x) = 1 / (x * (v : ℝ)) := by ring
    have hsecond : 1 / ((u : ℝ) * x) =
        ((v : ℝ) / (u : ℝ)) / (x * (v : ℝ)) := by
      field_simp [hu0, hv0, hx0]
    change Int.fract (1 / ((u : ℝ) * x)) *
        Int.fract (1 / ((v : ℝ) * x)) =
      Int.fract (1 / (x * (v : ℝ))) *
        Int.fract (((v : ℝ) / (u : ℝ)) / (x * (v : ℝ)))
    rw [hfirst, hsecond]
    ring
  rw [hcongr, hcomp]
  rfl

/-- The autocorrelation realization satisfies Ehm's pointwise Gram-kernel
formula at every pair of positive natural indices. -/
theorem baezDuarteGramEntry_eq_ehmS1Autocorrelation
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    baezDuarteGramEntry u v =
      (v : ℝ)⁻¹ * (ehmK + Real.log ((v : ℝ) / (u : ℝ)) / 2) +
        (u : ℝ)⁻¹ * ehmS1Autocorrelation ((v : ℝ) / (u : ℝ)) := by
  rw [baezDuarteGramEntry_eq_inv_mul_ehmAutocorrelation u v hu hv]
  unfold ehmS1Autocorrelation
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  field_simp [hu0, hv0]
  ring

/-- Unconditional pointwise Ehm kernel package obtained from the concrete
Gram autocorrelation integral. -/
noncomputable def ehmS1PointwiseKernelPackageProved :
    EhmS1PointwiseKernelPackage where
  S1 := ehmS1Autocorrelation
  gram_formula := baezDuarteGramEntry_eq_ehmS1Autocorrelation

/-- Ehm's reciprocal identity at positive rational ratios.  It follows
from the proved pointwise formula and symmetry of the Gram entry; it is an
exact identity, not a cancellation estimate. -/
theorem ehmS1Autocorrelation_reciprocity_rat
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ehmS1Autocorrelation ((u : ℝ) / (v : ℝ)) =
      ((v : ℝ) / (u : ℝ)) *
          ehmS1Autocorrelation ((v : ℝ) / (u : ℝ)) +
        ehmK * (1 - (v : ℝ) / (u : ℝ)) +
        (1 + (v : ℝ) / (u : ℝ)) / 2 *
          Real.log ((v : ℝ) / (u : ℝ)) := by
  have huv := baezDuarteGramEntry_eq_ehmS1Autocorrelation u v hu hv
  have hvu := baezDuarteGramEntry_eq_ehmS1Autocorrelation v u hv hu
  have hsym := baezDuarteGramEntry_symm u v
  rw [huv, hvu] at hsym
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hratio : (u : ℝ) / (v : ℝ) =
      ((v : ℝ) / (u : ℝ))⁻¹ := by
    field_simp [hu0, hv0]
  have hlog : Real.log ((u : ℝ) / (v : ℝ)) =
      -Real.log ((v : ℝ) / (u : ℝ)) := by
    rw [hratio, Real.log_inv]
  rw [hlog] at hsym
  field_simp [hu0, hv0] at hsym ⊢
  linarith

/-- Pairing the two orientations gives a one-sided kernel at `v/u`, plus
the exact elementary reciprocity completion.  For `u < v`, this places the
only `S₁` value at a ratio greater than one. -/
theorem ehmS1Autocorrelation_pair_reciprocity_rat
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ehmS1Autocorrelation ((v : ℝ) / (u : ℝ)) / (u : ℝ) +
        ehmS1Autocorrelation ((u : ℝ) / (v : ℝ)) / (v : ℝ) =
      2 * ehmS1Autocorrelation ((v : ℝ) / (u : ℝ)) / (u : ℝ) +
        ehmK * (1 / (v : ℝ) - 1 / (u : ℝ)) +
        (1 / 2 : ℝ) * (1 / (v : ℝ) + 1 / (u : ℝ)) *
          Real.log ((v : ℝ) / (u : ℝ)) := by
  rw [ehmS1Autocorrelation_reciprocity_rat u v hu hv]
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  field_simp [hu0, hv0]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
