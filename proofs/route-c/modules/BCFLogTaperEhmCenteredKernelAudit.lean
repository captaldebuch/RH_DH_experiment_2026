import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioNearFar
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCompensator
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperH15ContourEhmSpectralBridge
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Reciprocity and Mellin stop tests for the centred Ehm kernel

There are two different notions of centring in the H15 reduction, and they
must not be conflated.

* Subtracting the elementary reciprocity term from `S₁` produces a kernel
  fixed by the weighted inversion `x ↦ x⁻¹`.
* Removing the `q = 1` term from the `R₁` series produces the genuine
  `q ≥ 2` tail `S₁ - R₁` used by the hyperbolic decomposition.

The first operation gives an exact inversion symmetry.  The second has the
finite Mellin multiplier `∑_{2 ≤ q ≤ K} q⁻ˢ`, which is already nonzero at
`s = 0` for `K = 2`.  Thus the actual H15 tail is not, merely by its
definition, a dyadic wavelet with a factor `1 - 2⁻ˢ`.  Any zero-mode
cancellation must come from the complete signed arithmetic expression and
its residue/diagonal/continuous completion.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmCenteredKernelAudit

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperCancellationAnatomy
open RH.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioNearFar
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCompensator
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmQGeTwoCollapse
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmR1Decay
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMotohashiComparison
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannGaussianAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovGate
open RH.Criteria.NymanBeurling.BCFLogTaperH15ContourEhmSpectralBridge
open RH.Criteria.NymanBeurling.BCFLogTaperH15ContourTraceModes
open RH.Criteria.NymanBeurling.BCFLogTaperH15ResolvedSpectralSplit
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## The exact reciprocity-centred kernel -/

/-- Removing the elementary fixed part in Ehm reciprocity.  This is the
kernel whose weighted inversion is exact. -/
noncomputable def ehmReciprocityCenteredKernel (x : ℝ) : ℝ :=
  ehmS1Autocorrelation x - ehmK + Real.log x / 2

/-- Positive dilation proves the autocorrelation inversion law for every
positive real scale, not only at the rational ratios used by the finite
quadratic form. -/
theorem ehmAutocorrelation_inv {r : ℝ} (hr : 0 < r) :
    ehmAutocorrelation r⁻¹ = r⁻¹ * ehmAutocorrelation r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hcomp := MeasureTheory.integral_comp_mul_right_Ioi
    (fun y : ℝ => Int.fract (r / y) * Int.fract (1 / y)) 0 hr
  simp only [zero_mul, smul_eq_mul] at hcomp
  unfold ehmAutocorrelation
  calc
    (∫ x in Set.Ioi (0 : ℝ),
        Int.fract (1 / x) * Int.fract (r⁻¹ / x)) =
      ∫ x in Set.Ioi (0 : ℝ),
        Int.fract (r / (x * r)) * Int.fract (1 / (x * r)) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          have hx0 : x ≠ 0 := ne_of_gt hx
          field_simp [hr0, hx0]
    _ = r⁻¹ *
        ∫ y in Set.Ioi (0 : ℝ),
          Int.fract (r / y) * Int.fract (1 / y) := hcomp
    _ = r⁻¹ *
        ∫ y in Set.Ioi (0 : ℝ),
          Int.fract (1 / y) * Int.fract (r / y) := by
          congr 1
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro y hy
          ring

/-- The centred kernel satisfies weighted inversion at every positive real
argument. -/
theorem ehmReciprocityCenteredKernel_inv {r : ℝ} (hr : 0 < r) :
    ehmReciprocityCenteredKernel r⁻¹ =
      r * ehmReciprocityCenteredKernel r := by
  unfold ehmReciprocityCenteredKernel ehmS1Autocorrelation
  rw [ehmAutocorrelation_inv hr, Real.log_inv]
  have hr0 : r ≠ 0 := ne_of_gt hr
  field_simp [hr0]
  ring

/-- The natural logarithmic-coordinate normalization of the centred kernel.
The factor `exp(u/2)` converts weighted multiplicative inversion into
ordinary reflection. -/
noncomputable def ehmReciprocityCenteredLogKernel (u : ℝ) : ℝ :=
  Real.exp (u / 2) * ehmReciprocityCenteredKernel (Real.exp u)

/-- In logarithmic coordinates the kernel is exactly even.  This is the
correct structural consequence behind Mellin reflection; evenness does not
imply annihilation of the zero frequency. -/
theorem ehmReciprocityCenteredLogKernel_neg (u : ℝ) :
    ehmReciprocityCenteredLogKernel (-u) =
      ehmReciprocityCenteredLogKernel u := by
  unfold ehmReciprocityCenteredLogKernel
  have hexp : Real.exp (-u) = (Real.exp u)⁻¹ := Real.exp_neg u
  rw [hexp, ehmReciprocityCenteredKernel_inv (Real.exp_pos u)]
  have hfactor : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hfactor]

/-- At positive rational arguments, the centred kernel is fixed by the
weight-one inversion operator `f(x) ↦ x⁻¹ f(x⁻¹)`. -/
theorem ehmReciprocityCenteredKernel_reciprocity_rat
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ehmReciprocityCenteredKernel ((u : ℝ) / (v : ℝ)) =
      ((v : ℝ) / (u : ℝ)) *
        ehmReciprocityCenteredKernel ((v : ℝ) / (u : ℝ)) := by
  unfold ehmReciprocityCenteredKernel
  rw [ehmS1Autocorrelation_reciprocity_rat u v hu hv]
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hratio : (u : ℝ) / (v : ℝ) =
      ((v : ℝ) / (u : ℝ))⁻¹ := by
    field_simp [hu0, hv0]
  have hlog : Real.log ((u : ℝ) / (v : ℝ)) =
      -Real.log ((v : ℝ) / (u : ℝ)) := by
    rw [hratio, Real.log_inv]
  rw [hlog]
  ring

/-- The self-dual value is exactly `-1`.  Inversion centring creates a fixed
kernel, not a pointwise mean-zero kernel. -/
@[simp]
theorem ehmReciprocityCenteredKernel_one :
    ehmReciprocityCenteredKernel 1 = -1 := by
  have hS := ehmS1_one_eq_g11_sub_ehmK
    ehmS1PointwiseKernelPackageProved
  have hG := baezDuarteGramEntry_eq_vasyuninBEntryFormula_proved
    1 1 Nat.one_pos Nat.one_pos
  change ehmS1Autocorrelation 1 =
      baezDuarteGramEntry 1 1 - ehmK at hS
  unfold ehmReciprocityCenteredKernel
  rw [hS, hG, vasyuninBEntryFormula_one_one]
  unfold ehmK
  norm_num
  ring

@[simp]
theorem ehmReciprocityCenteredLogKernel_zero :
    ehmReciprocityCenteredLogKernel 0 = -1 := by
  simp [ehmReciprocityCenteredLogKernel]

/-- Symmetric finite Fourier window of the logarithmic kernel.  Under the
Mellin/logarithm change of variables this is the truncated critical-line
Mellin transform. -/
noncomputable def ehmReciprocityCenteredFourierWindow
    (T t : ℝ) : ℂ :=
  ∫ u : ℝ in -T..T,
    Complex.exp (-I * (t : ℂ) * (u : ℂ)) *
      (ehmReciprocityCenteredLogKernel u : ℂ)

/-- Exact finite Mellin/Fourier reflection.  It follows from inversion
symmetry and says the spectral window is even in frequency; it does not say
the value at frequency zero vanishes. -/
theorem ehmReciprocityCenteredFourierWindow_neg
    (T t : ℝ) :
    ehmReciprocityCenteredFourierWindow T (-t) =
      ehmReciprocityCenteredFourierWindow T t := by
  unfold ehmReciprocityCenteredFourierWindow
  let f : ℝ → ℂ := fun u =>
    Complex.exp (-I * (t : ℂ) * (u : ℂ)) *
      (ehmReciprocityCenteredLogKernel u : ℂ)
  have hpoint : ∀ u : ℝ,
      Complex.exp (-I * ((-t : ℝ) : ℂ) * (u : ℂ)) *
          (ehmReciprocityCenteredLogKernel u : ℂ) =
        f (-u) := by
    intro u
    unfold f
    rw [ehmReciprocityCenteredLogKernel_neg]
    congr 1
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr (fun u _ => hpoint u)]
  simpa [f] using
    (intervalIntegral.integral_comp_neg
      (a := -T) (b := T) (f := f))

/-! ## Exact logarithmic convolution normal form -/

/-- Symmetrically normalized BCF coefficient on the logarithmic lattice. -/
noncomputable def ehmReciprocityCenteredLogWeight
    (N n : ℕ) : ℝ :=
  dirichletCoeff N n * Real.exp (-Real.log (n : ℝ) / 2)

/-- Translation-invariant quadratic form generated by the even log kernel.
This is a finite sum, so no sum/integral exchange is involved. -/
noncomputable def ehmReciprocityCenteredLogConvolutionQuadratic
    (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    ehmReciprocityCenteredLogWeight N m *
      ehmReciprocityCenteredLogWeight N n *
        ehmReciprocityCenteredLogKernel
          (Real.log (n : ℝ) - Real.log (m : ℝ))

private theorem centered_log_convolution_point
    (N m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ehmReciprocityCenteredLogWeight N m *
        ehmReciprocityCenteredLogWeight N n *
          ehmReciprocityCenteredLogKernel
            (Real.log (n : ℝ) - Real.log (m : ℝ)) =
      (dirichletCoeff N m / (m : ℝ)) *
        (dirichletCoeff N n *
          ehmReciprocityCenteredKernel ((n : ℝ) / (m : ℝ))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio :
      Real.exp (Real.log (n : ℝ) - Real.log (m : ℝ)) =
        (n : ℝ) / (m : ℝ) := by
    rw [Real.exp_sub, Real.exp_log hnR, Real.exp_log hmR]
  have hfactor :
      Real.exp (-Real.log (m : ℝ) / 2) *
          Real.exp (-Real.log (n : ℝ) / 2) *
            Real.exp
              ((Real.log (n : ℝ) - Real.log (m : ℝ)) / 2) =
        1 / (m : ℝ) := by
    rw [← Real.exp_add, ← Real.exp_add]
    have hexponent :
        -Real.log (m : ℝ) / 2 + -Real.log (n : ℝ) / 2 +
            (Real.log (n : ℝ) - Real.log (m : ℝ)) / 2 =
          -Real.log (m : ℝ) := by ring
    rw [hexponent, Real.exp_neg, Real.exp_log hmR]
    simp only [one_div]
  unfold ehmReciprocityCenteredLogWeight
    ehmReciprocityCenteredLogKernel
  rw [hratio]
  calc
    dirichletCoeff N m * Real.exp (-Real.log (m : ℝ) / 2) *
          (dirichletCoeff N n * Real.exp (-Real.log (n : ℝ) / 2)) *
          (Real.exp ((Real.log (n : ℝ) - Real.log (m : ℝ)) / 2) *
            ehmReciprocityCenteredKernel ((n : ℝ) / (m : ℝ))) =
        dirichletCoeff N m * dirichletCoeff N n *
          (Real.exp (-Real.log (m : ℝ) / 2) *
            Real.exp (-Real.log (n : ℝ) / 2) *
              Real.exp
                ((Real.log (n : ℝ) - Real.log (m : ℝ)) / 2)) *
          ehmReciprocityCenteredKernel ((n : ℝ) / (m : ℝ)) := by ring
    _ = (dirichletCoeff N m / (m : ℝ)) *
        (dirichletCoeff N n *
          ehmReciprocityCenteredKernel ((n : ℝ) / (m : ℝ))) := by
      rw [hfactor]
      ring

/-- The centred Ehm quadratic form is exactly a convolution quadratic form
on the logarithmic lattice.  This is the rigorous finite version of the
multiplicative-convolution intuition. -/
theorem ehmReciprocityCenteredLogConvolutionQuadratic_eq
    (N : ℕ) :
    ehmReciprocityCenteredLogConvolutionQuadratic N =
      ehmS1QuadraticTerm ehmReciprocityCenteredKernel N := by
  classical
  unfold ehmReciprocityCenteredLogConvolutionQuadratic
    ehmS1QuadraticTerm
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hmMem
  have hm : 0 < m := lt_of_lt_of_le Nat.zero_lt_one
    (Finset.mem_Icc.mp hmMem).1
  apply Finset.sum_congr rfl
  intro n hnMem
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
    (Finset.mem_Icc.mp hnMem).1
  exact centered_log_convolution_point N m n hm hn

/-- The paired Ehm kernel in terms of its genuinely inversion-invariant
part.  The displayed elementary terms are the exact reciprocity completion;
none may be estimated independently before the H15 correction is reattached.
-/
theorem ehmS1Autocorrelation_pair_eq_reciprocityCentered
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ehmS1Autocorrelation ((v : ℝ) / (u : ℝ)) / (u : ℝ) +
        ehmS1Autocorrelation ((u : ℝ) / (v : ℝ)) / (v : ℝ) =
      2 * ehmReciprocityCenteredKernel ((v : ℝ) / (u : ℝ)) / (u : ℝ) +
        ehmK * (1 / (u : ℝ) + 1 / (v : ℝ)) +
        (1 / 2 : ℝ) * (1 / (v : ℝ) - 1 / (u : ℝ)) *
          Real.log ((v : ℝ) / (u : ℝ)) := by
  rw [ehmS1Autocorrelation_pair_reciprocity_rat u v hu hv]
  unfold ehmReciprocityCenteredKernel
  ring

/-! ## Complete H15 expression in reciprocity-centred coordinates -/

/-- The signed upper-triangle sum containing only the weighted
inversion-invariant kernel. -/
noncomputable def ehmReciprocityCenteredUpperTriangleSum (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if m < n then
      dirichletCoeff N m * dirichletCoeff N n *
        (2 * ehmReciprocityCenteredKernel ((n : ℝ) / (m : ℝ)) /
          (m : ℝ))
    else 0

/-- The elementary reciprocity completion left when the invariant kernel is
extracted from the paired Ehm sum. -/
noncomputable def ehmReciprocityElementaryUpperTriangleCompletion
    (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if m < n then
      dirichletCoeff N m * dirichletCoeff N n *
        (ehmK * (1 / (m : ℝ) + 1 / (n : ℝ)) +
          (1 / 2 : ℝ) * (1 / (n : ℝ) - 1 / (m : ℝ)) *
            Real.log ((n : ℝ) / (m : ℝ)))
    else 0

/-- Exact split of the one-sided Ehm form into its invariant kernel and its
elementary reciprocity completion. -/
theorem ehmS1OneSidedUpperTriangleSum_eq_centered_add_elementary
    (N : ℕ) :
    ehmS1OneSidedUpperTriangleSum N =
      ehmReciprocityCenteredUpperTriangleSum N +
        ehmReciprocityElementaryUpperTriangleCompletion N := by
  classical
  unfold ehmS1OneSidedUpperTriangleSum
    ehmReciprocityCenteredUpperTriangleSum
    ehmReciprocityElementaryUpperTriangleCompletion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m < n
  · simp only [hmn, if_true]
    unfold ehmReciprocityCenteredKernel
    ring
  · simp [hmn]

/-- All non-kernel terms which must remain coupled to the centred signed
sum.  Calling this a completion does not assert that it is small or that it
is an orthogonal projection. -/
noncomputable def ehmReciprocityCenteredGlobalCompletion (N : ℕ) : ℝ :=
  ehmReciprocityElementaryUpperTriangleCompletion N +
    (baezDuarteGramEntry 1 1 - ehmK) * logTaperDiagonalMass N +
      ehmS1MomentCorrection N

/-- Exact globally-centred H15 normal form.  This is the valid replacement
for the false pointwise wavelet interpretation of `S₁ - R₁`. -/
theorem coupledGcdRatioExpression_eq_reciprocityCentered
    (N : ℕ) :
    coupledGcdRatioExpression N =
      ehmReciprocityCenteredUpperTriangleSum N +
        ehmReciprocityCenteredGlobalCompletion N := by
  rw [coupledGcdRatioExpression_eq_ehmS1OneSidedUpperTriangle,
    ehmS1OneSidedUpperTriangleSum_eq_centered_add_elementary]
  unfold ehmReciprocityCenteredGlobalCompletion
  ring

/-- Exact compatibility with the completed contour/spectral ledger.  The
reciprocity-centred Ehm expression and the resolved bilinear trace expression
are two presentations of the same signed scalar; there is no comparison
remainder between them. -/
theorem reciprocityCenteredExpression_eq_resolvedSpectralExpression
    {η σL σR : ℝ} (A : H15GaussianMajorantFamilyData η σL σR)
    (D : H15ResolvedDualSpectralDecomposition η σR) (N : ℕ) :
    ehmReciprocityCenteredUpperTriangleSum N +
        ehmReciprocityCenteredGlobalCompletion N =
      h15ContourTraceNamedTotal N η σR +
        h15ResolvedSpectralLedger D
          rationalAnalyticEstermannAtZeroPackage N σL := by
  rw [← coupledGcdRatioExpression_eq_reciprocityCentered]
  rw [← h15EhmMotohashiCommonExpression_eq_coupledGcdRatioExpression]
  exact h15EhmCommonExpression_eq_resolvedSpectralExpression A D N

/-! ## Moment evaluation of the global completion -/

private theorem centered_sum_mul_sum_Icc (N : ℕ) (f g : ℕ → ℝ) :
    (∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N, f u * g v) =
      (∑ u ∈ Finset.Icc 1 N, f u) *
        (∑ v ∈ Finset.Icc 1 N, g v) := by
  exact (Finset.sum_mul_sum (Finset.Icc 1 N) (Finset.Icc 1 N) f g).symm

/-- Replacing `S₁` by its reciprocity-centred part changes the complete
quadratic term by three explicit one-variable moments. -/
theorem ehmS1QuadraticTerm_eq_reciprocityCentered_add_moments
    (N : ℕ) :
    ehmS1QuadraticTerm ehmS1Autocorrelation N =
      ehmS1QuadraticTerm ehmReciprocityCenteredKernel N +
        ehmK * ehmM 0 N * ehmL 0 N +
        ehmM 0 N * ehmL 1 N / 2 -
        ehmM 1 N * ehmL 0 N / 2 := by
  classical
  have hpoint (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
      (dirichletCoeff N m / (m : ℝ)) *
          (dirichletCoeff N n *
            ehmS1Autocorrelation ((n : ℝ) / (m : ℝ))) =
        (dirichletCoeff N m / (m : ℝ)) *
          (dirichletCoeff N n *
            ehmReciprocityCenteredKernel ((n : ℝ) / (m : ℝ))) +
        (dirichletCoeff N m / (m : ℝ)) *
          (dirichletCoeff N n * ehmK) +
        (dirichletCoeff N m * Real.log (m : ℝ) /
          (m : ℝ) / 2) * dirichletCoeff N n -
        (dirichletCoeff N m / (m : ℝ)) *
          (dirichletCoeff N n * Real.log (n : ℝ) / 2) := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    unfold ehmReciprocityCenteredKernel
    rw [Real.log_div hn0 hm0]
    ring
  have hcenter :
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (dirichletCoeff N m / (m : ℝ)) *
          (dirichletCoeff N n *
            ehmReciprocityCenteredKernel ((n : ℝ) / (m : ℝ)))) =
        ehmS1QuadraticTerm ehmReciprocityCenteredKernel N := by
    unfold ehmS1QuadraticTerm
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
  have hK :
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (dirichletCoeff N m / (m : ℝ)) *
          (dirichletCoeff N n * ehmK)) =
        ehmK * ehmM 0 N * ehmL 0 N := by
    calc
      _ = (∑ m ∈ Finset.Icc 1 N,
            dirichletCoeff N m / (m : ℝ)) *
          (∑ n ∈ Finset.Icc 1 N,
            dirichletCoeff N n * ehmK) :=
        centered_sum_mul_sum_Icc N _ _
      _ = _ := by
        unfold ehmM ehmL
        simp only [pow_zero, mul_one]
        rw [← Finset.sum_mul]
        ring
  have hL1 :
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (dirichletCoeff N m * Real.log (m : ℝ) /
          (m : ℝ) / 2) * dirichletCoeff N n) =
        ehmM 0 N * ehmL 1 N / 2 := by
    calc
      _ = (∑ m ∈ Finset.Icc 1 N,
            dirichletCoeff N m * Real.log (m : ℝ) /
              (m : ℝ) / 2) *
          (∑ n ∈ Finset.Icc 1 N, dirichletCoeff N n) :=
        centered_sum_mul_sum_Icc N _ _
      _ = _ := by
        unfold ehmM ehmL
        simp only [pow_zero, pow_one, mul_one]
        rw [← Finset.sum_div]
        ring
  have hM1 :
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (dirichletCoeff N m / (m : ℝ)) *
          (dirichletCoeff N n * Real.log (n : ℝ) / 2)) =
        ehmM 1 N * ehmL 0 N / 2 := by
    calc
      _ = (∑ m ∈ Finset.Icc 1 N,
            dirichletCoeff N m / (m : ℝ)) *
          (∑ n ∈ Finset.Icc 1 N,
            dirichletCoeff N n * Real.log (n : ℝ) / 2) :=
        centered_sum_mul_sum_Icc N _ _
      _ = _ := by
        unfold ehmM ehmL
        simp only [pow_zero, pow_one, mul_one]
        rw [← Finset.sum_div]
        ring
  calc
    ehmS1QuadraticTerm ehmS1Autocorrelation N =
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      (dirichletCoeff N m / (m : ℝ)) *
        (dirichletCoeff N n *
          ehmS1Autocorrelation ((n : ℝ) / (m : ℝ)))) := by
        unfold ehmS1QuadraticTerm
        apply Finset.sum_congr rfl
        intro m hmMem
        rw [Finset.mul_sum]
    _ =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ((dirichletCoeff N m / (m : ℝ)) *
            (dirichletCoeff N n *
              ehmReciprocityCenteredKernel ((n : ℝ) / (m : ℝ))) +
          (dirichletCoeff N m / (m : ℝ)) *
            (dirichletCoeff N n * ehmK) +
          (dirichletCoeff N m * Real.log (m : ℝ) /
            (m : ℝ) / 2) * dirichletCoeff N n -
          (dirichletCoeff N m / (m : ℝ)) *
            (dirichletCoeff N n * Real.log (n : ℝ) / 2)) := by
        apply Finset.sum_congr rfl
        intro m hmMem
        have hm : 0 < m := lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp hmMem).1
        apply Finset.sum_congr rfl
        intro n hnMem
        have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp hnMem).1
        exact hpoint m n hm hn
    _ = ehmS1QuadraticTerm ehmReciprocityCenteredKernel N +
        ehmK * ehmM 0 N * ehmL 0 N +
        ehmM 0 N * ehmL 1 N / 2 -
        ehmM 1 N * ehmL 0 N / 2 := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [hcenter, hK, hL1, hM1]

/-- Weighted inversion turns the off-diagonal quadratic form of the centred
kernel into the one-sided upper-triangle sum. -/
theorem ehmS1UpperTriangleSum_reciprocityCentered (N : ℕ) :
    ehmS1UpperTriangleSum ehmReciprocityCenteredKernel N =
      ehmReciprocityCenteredUpperTriangleSum N := by
  classical
  unfold ehmS1UpperTriangleSum ehmReciprocityCenteredUpperTriangleSum
  apply Finset.sum_congr rfl
  intro m hmMem
  apply Finset.sum_congr rfl
  intro n hnMem
  by_cases hmn : m < n
  · have hm : 0 < m := lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp hmMem).1
    have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp hnMem).1
    simp only [hmn, if_true]
    rw [ehmReciprocityCenteredKernel_reciprocity_rat m n hm hn]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hm0, hn0]
    ring
  · simp [hmn]

/-- The complete centred quadratic form is the signed upper triangle minus
the diagonal mass, because the self-dual kernel value is `-1`. -/
theorem ehmS1QuadraticTerm_reciprocityCentered_eq_upper_sub_diagonal
    (N : ℕ) :
    ehmS1QuadraticTerm ehmReciprocityCenteredKernel N =
      ehmReciprocityCenteredUpperTriangleSum N -
        logTaperDiagonalMass N := by
  rw [ehmS1QuadraticTerm_eq_diagonal_add_offDiagonal,
    ehmS1OffDiagonalTerm_eq_offDiagonalSum,
    ehmS1OffDiagonalSum_eq_symmetrized,
    ehmS1SymmetrizedOffDiagonalSum_eq_symmetricKernelSum,
    ehmS1SymmetricKernelOffDiagonalSum_eq_upperTriangleSum,
    ehmS1UpperTriangleSum_reciprocityCentered]
  unfold ehmS1DiagonalTerm
  rw [ehmReciprocityCenteredKernel_one]
  ring

/-- Combining the convolution identity with the self-dual diagonal value
recovers the signed upper triangle minus the exact diagonal mass. -/
theorem ehmReciprocityCenteredLogConvolutionQuadratic_eq_upper_sub_diagonal
    (N : ℕ) :
    ehmReciprocityCenteredLogConvolutionQuadratic N =
      ehmReciprocityCenteredUpperTriangleSum N -
        logTaperDiagonalMass N := by
  rw [ehmReciprocityCenteredLogConvolutionQuadratic_eq,
    ehmS1QuadraticTerm_reciprocityCentered_eq_upper_sub_diagonal]

/-- Explicit moment formula for the entire non-kernel completion.  This is
the finite algebraic quantity that the two-pole/residual ledger must retain
while estimating the centred signed kernel. -/
theorem ehmReciprocityCenteredGlobalCompletion_eq_moments
    (N : ℕ) :
    ehmReciprocityCenteredGlobalCompletion N =
      -logTaperDiagonalMass N +
        ehmK * ehmM 0 N * ehmL 0 N +
        ehmM 0 N * ehmL 1 N / 2 -
        ehmM 1 N * ehmL 0 N / 2 +
        ehmS1MomentCorrection N := by
  have hCoupled :=
    coupledGcdRatioExpression_eq_ehmS1QuadraticTerm_add_momentCorrection
      ehmS1PointwiseKernelPackageProved N
  change coupledGcdRatioExpression N =
    ehmS1QuadraticTerm ehmS1Autocorrelation N +
      ehmS1MomentCorrection N at hCoupled
  rw [ehmS1QuadraticTerm_eq_reciprocityCentered_add_moments,
    ehmS1QuadraticTerm_reciprocityCentered_eq_upper_sub_diagonal] at hCoupled
  rw [coupledGcdRatioExpression_eq_reciprocityCentered] at hCoupled
  linarith

/-- The diagonal-free finite moment completion which accompanies the full
log-lattice convolution quadratic. -/
noncomputable def ehmReciprocityCenteredMomentCompletion (N : ℕ) : ℝ :=
  ehmK * ehmM 0 N * ehmL 0 N +
    ehmM 0 N * ehmL 1 N / 2 -
      ehmM 1 N * ehmL 0 N / 2 +
        ehmS1MomentCorrection N

theorem diagonal_add_reciprocityCenteredGlobalCompletion
    (N : ℕ) :
    logTaperDiagonalMass N +
        ehmReciprocityCenteredGlobalCompletion N =
      ehmReciprocityCenteredMomentCompletion N := by
  rw [ehmReciprocityCenteredGlobalCompletion_eq_moments]
  unfold ehmReciprocityCenteredMomentCompletion
  ring

/-- Exact spectral-energy decomposition in centred logarithmic coordinates:
an even translation-invariant convolution on `log n`, plus a completely
explicit finite moment completion. -/
theorem spectralEnergy_eq_centeredLogConvolution_add_moments
    (N : ℕ) :
    spectralEnergy N =
      ehmReciprocityCenteredLogConvolutionQuadratic N +
        ehmReciprocityCenteredMomentCompletion N := by
  rw [spectralEnergy_eq_coupledGcdRatioExpression,
    coupledGcdRatioExpression_eq_reciprocityCentered,
    ehmReciprocityCenteredLogConvolutionQuadratic_eq_upper_sub_diagonal]
  rw [← diagonal_add_reciprocityCenteredGlobalCompletion]
  ring

/-- The genuinely open estimate in the cleanest convolution coordinates.
The even kernel and its moment completion remain coupled inside one absolute
value. -/
structure EhmCenteredLogConvolutionCancellationEstimate where
  C : ℝ
  C_pos : 0 < C
  alpha : ℝ
  alpha_pos : 0 < alpha
  bound : ∀ N : ℕ, 2 ≤ N →
    |ehmReciprocityCenteredLogConvolutionQuadratic N +
      ehmReciprocityCenteredMomentCompletion N| ≤
        C / (Real.log (N : ℝ)) ^ alpha

/-- A signed convolution estimate supplies the original H15 cancellation
package with identical quantitative data. -/
noncomputable def EhmCenteredLogConvolutionCancellationEstimate.toCoupled
    (H : EhmCenteredLogConvolutionCancellationEstimate) :
    CoupledLogTaperCancellationEstimate where
  C := H.C
  C_pos := H.C_pos
  α := H.alpha
  α_pos := H.alpha_pos
  bound N hN := by
    rw [← spectralEnergy_eq_coupledGcdRatioExpression,
      spectralEnergy_eq_centeredLogConvolution_add_moments]
    exact H.bound N hN

/-- The honest analytic target in reciprocity-centred coordinates.  The
invariant kernel and the global completion stay within the same absolute
value. -/
structure EhmReciprocityCenteredCoupledCancellationEstimate where
  C : ℝ
  C_pos : 0 < C
  alpha : ℝ
  alpha_pos : 0 < alpha
  bound : ∀ N : ℕ, 2 ≤ N →
    |ehmReciprocityCenteredUpperTriangleSum N +
      ehmReciprocityCenteredGlobalCompletion N| ≤
        C / (Real.log (N : ℝ)) ^ alpha

/-- A bound in centred coordinates is exactly sufficient for the original
coupled H15 estimate, with no loss in constants or exponent. -/
noncomputable def
    EhmReciprocityCenteredCoupledCancellationEstimate.toCoupled
    (H : EhmReciprocityCenteredCoupledCancellationEstimate) :
    CoupledLogTaperCancellationEstimate where
  C := H.C
  C_pos := H.C_pos
  α := H.alpha
  α_pos := H.alpha_pos
  bound N hN := by
    rw [coupledGcdRatioExpression_eq_reciprocityCentered]
    exact H.bound N hN

/-! ## The distinct series-centred kernel -/

/-- The common-coordinate kernel produced by deleting the first `R₁` series
mode.  This is the actual kernel in the collapsed `q ≥ 2` H15 sector. -/
noncomputable def ehmSeriesCenteredKernel
    (S1 R1 : ℝ → ℝ) (x : ℝ) : ℝ :=
  S1 x - R1 x

theorem ehmSeriesCenteredKernel_ratio_eq_qGeTwoLimitKernel
    (S1 R1 : ℝ → ℝ) (d m : ℕ) :
    ehmSeriesCenteredKernel S1 R1 ((d : ℝ) / (m : ℝ)) =
      ehmQGeTwoLimitKernel S1 R1 d m := by
  rfl

/-- Under the rational series bridge, series centring is exactly deletion of
the `q = 1` mode, hence the tail starts at `q = 2`. -/
theorem ehmSeriesCenteredKernel_ratio_eq_tsum_tail
    {S1 R1 : ℝ → ℝ} (HS : EhmR1RationalSeriesBridge S1 R1)
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    ehmSeriesCenteredKernel S1 R1 ((d : ℝ) / (m : ℝ)) =
      ∑' q : ℕ,
        R1 (((q + 2 : ℕ) : ℝ) * ((d : ℝ) / (m : ℝ))) := by
  rw [ehmSeriesCenteredKernel_ratio_eq_qGeTwoLimitKernel]
  exact ehmQGeTwoLimitKernel_eq_tsum_tail HS d m hd hm

/-! ## Finite Mellin multiplier -/

/-- Finite `q ≥ 2` tail, complexified before taking its Mellin transform. -/
noncomputable def ehmR1FiniteTail
    (R1 : ℝ → ℝ) (K : ℕ) (x : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 2 K, (R1 ((q : ℝ) * x) : ℂ)

/-- The exact Mellin multiplier of the finite tail. -/
noncomputable def ehmR1FiniteTailMellinMultiplier
    (K : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ Finset.Icc 2 K, (q : ℂ) ^ (-s)

private theorem hasMellin_finset_dilates
    (R1 : ℝ → ℝ) (s : ℂ) (F : Finset ℕ)
    (hF : ∀ q ∈ F, 0 < q)
    (hR1 : MellinConvergent (fun x : ℝ => (R1 x : ℂ)) s) :
    HasMellin
      (fun x : ℝ => ∑ q ∈ F, (R1 ((q : ℝ) * x) : ℂ)) s
      ((∑ q ∈ F, (q : ℂ) ^ (-s)) *
        mellin (fun x : ℝ => (R1 x : ℂ)) s) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simp [HasMellin, MellinConvergent, mellin]
  | @insert q F hqF ih =>
      have hq : 0 < q := hF q (Finset.mem_insert_self q F)
      have hF' : ∀ r ∈ F, 0 < r := by
        intro r hr
        exact hF r (Finset.mem_insert_of_mem hr)
      have hscaled : MellinConvergent
          (fun x : ℝ => (R1 ((q : ℝ) * x) : ℂ)) s :=
        (MellinConvergent.comp_mul_left (by exact_mod_cast hq)).2 hR1
      have htail := ih hF'
      have hadd := hasMellin_add hscaled htail.1
      refine ⟨?_, ?_⟩
      · simpa [Finset.sum_insert hqF] using hadd.1
      · calc
          mellin
              (fun x : ℝ =>
                ∑ r ∈ insert q F, (R1 ((r : ℝ) * x) : ℂ)) s =
              mellin
                (fun x : ℝ =>
                  (R1 ((q : ℝ) * x) : ℂ) +
                    ∑ r ∈ F, (R1 ((r : ℝ) * x) : ℂ)) s := by
                congr 1
                funext x
                simp [Finset.sum_insert hqF]
          _ = mellin (fun x : ℝ => (R1 ((q : ℝ) * x) : ℂ)) s +
                mellin
                  (fun x : ℝ => ∑ r ∈ F,
                    (R1 ((r : ℝ) * x) : ℂ)) s := hadd.2
          _ = ((q : ℂ) ^ (-s)) *
                mellin (fun x : ℝ => (R1 x : ℂ)) s +
              ((∑ r ∈ F, (r : ℂ) ^ (-s)) *
                mellin (fun x : ℝ => (R1 x : ℂ)) s) := by
              have hscale :
                  mellin (fun x : ℝ => (R1 ((q : ℝ) * x) : ℂ)) s =
                    ((q : ℂ) ^ (-s)) *
                      mellin (fun x : ℝ => (R1 x : ℂ)) s := by
                simpa only [Complex.ofReal_natCast, smul_eq_mul] using
                  (mellin_comp_mul_left
                    (fun x : ℝ => (R1 x : ℂ)) s
                    (by exact_mod_cast hq))
              rw [hscale, htail.2]
          _ = ((∑ r ∈ insert q F, (r : ℂ) ^ (-s)) *
                mellin (fun x : ℝ => (R1 x : ℂ)) s) := by
              rw [Finset.sum_insert hqF]
              ring

/-- On every line where the base `R₁` Mellin integral converges, the finite
H15 tail has precisely the finite Dirichlet multiplier
`∑_{2 ≤ q ≤ K} q⁻ˢ`. -/
theorem hasMellin_ehmR1FiniteTail
    (R1 : ℝ → ℝ) (K : ℕ) (s : ℂ)
    (hR1 : MellinConvergent (fun x : ℝ => (R1 x : ℂ)) s) :
    HasMellin (ehmR1FiniteTail R1 K) s
      (ehmR1FiniteTailMellinMultiplier K s *
        mellin (fun x : ℝ => (R1 x : ℂ)) s) := by
  unfold ehmR1FiniteTail ehmR1FiniteTailMellinMultiplier
  apply hasMellin_finset_dilates R1 s (Finset.Icc 2 K)
  · intro q hq
    have hq2 := (Finset.mem_Icc.mp hq).1
    omega
  · exact hR1

/-! ## The wavelet stop test -/

@[simp]
theorem ehmR1FiniteTailMellinMultiplier_two_zero :
    ehmR1FiniteTailMellinMultiplier 2 0 = 1 := by
  norm_num [ehmR1FiniteTailMellinMultiplier]

/-- The very first nonempty H15 tail already has a nonzero formal zero-mode
multiplier.  Therefore deletion of `q = 1` is not a mean-zero wavelet
projection by itself. -/
theorem ehmR1FiniteTailMellinMultiplier_two_zero_ne_zero :
    ehmR1FiniteTailMellinMultiplier 2 0 ≠ 0 := by
  simp

/-- In particular, the finite tail multiplier cannot be obtained by merely
attaching the dyadic wavelet factor `1 - 2⁻ˢ`. -/
theorem ehmR1FiniteTailMultiplier_not_dyadic_at_zero (z : ℂ) :
    ehmR1FiniteTailMellinMultiplier 2 0 ≠
      (1 - (2 : ℂ) ^ (-(0 : ℂ))) * z := by
  simp

/-! ## Ordinary Fourier-density stop test -/

/-- Assuming only the rational Ehm series bridge already needed by the H15
route, the autocorrelation kernel is quadratically small at positive integer
arguments. -/
theorem abs_ehmS1Autocorrelation_nat_le
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (n : ℕ) (hn : 0 < n) :
    |ehmS1Autocorrelation (n : ℝ)| ≤ 16 / (n : ℝ) ^ 2 := by
  have htail := abs_ehmAutocorrelationQGeTwoLimitKernel_le
    HS n 1 hn Nat.one_pos
  have htail' :
      |ehmS1Autocorrelation (n : ℝ) - ehmR1 (n : ℝ)| ≤
        8 / (n : ℝ) ^ 2 := by
    simpa [ehmQGeTwoLimitKernel] using htail
  have hR1 := ehmConcreteR1QuadraticDecay.bound
    (n : ℝ) (by exact_mod_cast hn)
  have hsplit :
      ehmS1Autocorrelation (n : ℝ) =
        (ehmS1Autocorrelation (n : ℝ) - ehmR1 (n : ℝ)) +
          ehmR1 (n : ℝ) := by ring
  rw [hsplit]
  calc
    |ehmS1Autocorrelation (n : ℝ) - ehmR1 (n : ℝ) + ehmR1 (n : ℝ)| ≤
        |ehmS1Autocorrelation (n : ℝ) - ehmR1 (n : ℝ)| +
          |ehmR1 (n : ℝ)| := abs_add_le _ _
    _ ≤ 8 / (n : ℝ) ^ 2 + 8 / (n : ℝ) ^ 2 :=
      add_le_add htail' hR1
    _ = 16 / (n : ℝ) ^ 2 := by ring

/-- Consequently the reciprocity-centred kernel grows along the positive
integer ray.  The elementary centring which creates inversion symmetry also
creates the large logarithmic mode. -/
theorem ehmReciprocityCenteredKernel_nat_tendsto_atTop
    (HS : EhmAutocorrelationR1RationalSeriesBridge) :
    Tendsto
      (fun n : ℕ =>
        ehmReciprocityCenteredKernel ((n + 1 : ℕ) : ℝ))
      atTop atTop := by
  have hcast : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hlog : Tendsto
      (fun n : ℕ => Real.log (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hhalf : Tendsto
      (fun n : ℕ => Real.log (((n + 1 : ℕ) : ℝ)) / 2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num) hlog
  have hbase : Tendsto
      (fun n : ℕ =>
        Real.log (((n + 1 : ℕ) : ℝ)) / 2 - ehmK - 16)
      atTop atTop := by
    simpa [sub_eq_add_neg, add_assoc] using
      (tendsto_atTop_add_const_right atTop (-ehmK - 16) hhalf)
  apply tendsto_atTop_mono' atTop _ hbase
  filter_upwards with n
  have hn : 0 < n + 1 := by omega
  have habs := abs_ehmS1Autocorrelation_nat_le HS (n + 1) hn
  have hden : 1 ≤ ((((n + 1 : ℕ) : ℝ)) ^ 2) := by
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    nlinarith
  have hfrac : 16 / ((((n + 1 : ℕ) : ℝ)) ^ 2) ≤ 16 := by
    exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
  have habs16 : |ehmS1Autocorrelation (((n + 1 : ℕ) : ℝ))| ≤ 16 :=
    habs.trans hfrac
  have hlower : -16 ≤ ehmS1Autocorrelation (((n + 1 : ℕ) : ℝ)) :=
    (neg_le_neg habs16).trans (neg_abs_le _)
  unfold ehmReciprocityCenteredKernel
  linarith

/-- The even logarithmic kernel is unbounded along the sampled logarithmic
lattice.  Therefore its spectral realization cannot be the Fourier transform
of an ordinary `L¹` density; a pole-subtracted contour or distributional
representation is mandatory. -/
theorem ehmReciprocityCenteredLogKernel_log_nat_tendsto_atTop
    (HS : EhmAutocorrelationR1RationalSeriesBridge) :
    Tendsto
      (fun n : ℕ =>
        ehmReciprocityCenteredLogKernel
          (Real.log (((n + 1 : ℕ) : ℝ))))
      atTop atTop := by
  have hcenter := ehmReciprocityCenteredKernel_nat_tendsto_atTop HS
  apply tendsto_atTop_mono' atTop _ hcenter
  filter_upwards [hcenter.eventually_ge_atTop 0] with n hn
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hn_one : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hlog_nonneg : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg hn_one
  unfold ehmReciprocityCenteredLogKernel
  rw [Real.exp_log hnpos]
  exact le_mul_of_one_le_left hn (Real.one_le_exp (by linarith))

/-- In particular, no constant bounds the sampled log kernel. -/
theorem not_bounded_ehmReciprocityCenteredLogKernel_on_log_nat
    (HS : EhmAutocorrelationR1RationalSeriesBridge) :
    ¬ ∃ B : ℝ, ∀ n : ℕ,
      |ehmReciprocityCenteredLogKernel
        (Real.log (((n + 1 : ℕ) : ℝ)))| ≤ B := by
  rintro ⟨B, hB⟩
  have hlarge :=
    (ehmReciprocityCenteredLogKernel_log_nat_tendsto_atTop HS).eventually_gt_atTop
      (|B| + 1)
  rcases hlarge.exists with ⟨n, hn⟩
  have hsample := hB n
  have hself := le_abs_self
    (ehmReciprocityCenteredLogKernel
      (Real.log (((n + 1 : ℕ) : ℝ))))
  have hBabs : B ≤ |B| := le_abs_self B
  linarith

/-! ## Pole subtraction and the genuinely decaying lattice kernel -/

/-- The even elementary mode forced by the two reciprocity poles.  It is
exactly the large term of the centred logarithmic kernel on either end of
the real line. -/
noncomputable def ehmReciprocityPoleLogMode (u : ℝ) : ℝ :=
  Real.exp (|u| / 2) * (|u| / 2 - ehmK)

/-- The kernel left after the explicit even pole mode is removed.  This is
the first object for which an ordinary Fourier density is not ruled out by
the lattice-growth stop test. -/
noncomputable def ehmReciprocityRegularizedLogKernel (u : ℝ) : ℝ :=
  ehmReciprocityCenteredLogKernel u - ehmReciprocityPoleLogMode u

@[simp]
theorem ehmReciprocityPoleLogMode_neg (u : ℝ) :
    ehmReciprocityPoleLogMode (-u) = ehmReciprocityPoleLogMode u := by
  simp [ehmReciprocityPoleLogMode]

@[simp]
theorem ehmReciprocityRegularizedLogKernel_neg (u : ℝ) :
    ehmReciprocityRegularizedLogKernel (-u) =
      ehmReciprocityRegularizedLogKernel u := by
  simp [ehmReciprocityRegularizedLogKernel,
    ehmReciprocityCenteredLogKernel_neg]

/-- On the positive logarithmic ray, pole subtraction leaves precisely the
autocorrelation kernel, with its natural square-root normalization. -/
theorem ehmReciprocityRegularizedLogKernel_of_nonneg
    {u : ℝ} (hu : 0 ≤ u) :
    ehmReciprocityRegularizedLogKernel u =
      Real.exp (u / 2) * ehmS1Autocorrelation (Real.exp u) := by
  unfold ehmReciprocityRegularizedLogKernel
    ehmReciprocityCenteredLogKernel ehmReciprocityCenteredKernel
    ehmReciprocityPoleLogMode
  rw [abs_of_nonneg hu, Real.log_exp]
  ring

/-- The positive-ray formula and evenness combine into a single global
identity. -/
theorem ehmReciprocityRegularizedLogKernel_eq_abs (u : ℝ) :
    ehmReciprocityRegularizedLogKernel u =
      Real.exp (|u| / 2) *
        ehmS1Autocorrelation (Real.exp |u|) := by
  by_cases hu : 0 ≤ u
  · simpa [abs_of_nonneg hu] using
      (ehmReciprocityRegularizedLogKernel_of_nonneg hu)
  · have hneg : 0 ≤ -u := by linarith [lt_of_not_ge hu]
    calc
      ehmReciprocityRegularizedLogKernel u =
          ehmReciprocityRegularizedLogKernel (-u) :=
        (ehmReciprocityRegularizedLogKernel_neg u).symm
      _ = Real.exp ((-u) / 2) *
          ehmS1Autocorrelation (Real.exp (-u)) :=
        ehmReciprocityRegularizedLogKernel_of_nonneg hneg
      _ = Real.exp (|u| / 2) *
          ehmS1Autocorrelation (Real.exp |u|) := by
        rw [abs_of_neg (lt_of_not_ge hu)]

/-- The full (all-positive-real) Ehm series bridge upgrades the proved
quadratic `R₁` bound to the same decay for `S₁`.  This is a classical kernel
identity obligation, separate from the RH-strength signed sum. -/
theorem abs_ehmS1Autocorrelation_le_of_seriesBridge
    (HS : EhmAutocorrelationR1SeriesBridge)
    {x : ℝ} (hx : 0 < x) :
    |ehmS1Autocorrelation x| ≤ 16 / x ^ 2 := by
  let p : ℕ → ℝ := fun q => 1 / (((q + 1 : ℕ) : ℝ) ^ 2)
  let z : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ (2 : ℕ)
  have hz : Summable z := by
    change Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ))
    exact Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hp : Summable p := by
    have hzShift : Summable (fun q : ℕ => z (q + 1)) :=
      (summable_nat_add_iff 1).2 hz
    simpa [p, z] using hzShift
  have hpSum : (∑' q : ℕ, p q) ≤ 2 := by
    have hsplit := hz.sum_add_tsum_nat_add 1
    have hvalue : (∑' n : ℕ, z n) = Real.pi ^ 2 / 6 := by
      simpa [z] using hasSum_zeta_two.tsum_eq
    rw [hvalue] at hsplit
    have htail : (∑' q : ℕ, p q) = Real.pi ^ 2 / 6 := by
      simpa [p, z] using hsplit
    rw [htail]
    have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
    have hpilt : Real.pi < 3.15 := Real.pi_lt_d2
    nlinarith
  have hmajor : Summable (fun q : ℕ => (8 / x ^ 2) * p q) :=
    hp.mul_left (8 / x ^ 2)
  have hpoint : ∀ q : ℕ,
      |ehmR1 (((q + 1 : ℕ) : ℝ) * x)| ≤
        (8 / x ^ 2) * p q := by
    intro q
    calc
      |ehmR1 (((q + 1 : ℕ) : ℝ) * x)| ≤
          8 / ((((q + 1 : ℕ) : ℝ) * x) ^ 2) :=
        ehmConcreteR1QuadraticDecay.bound _ (mul_pos (by positivity) hx)
      _ = (8 / x ^ 2) * p q := by
        unfold p
        field_simp [ne_of_gt hx]
  rw [← (HS.hasSum_series x hx).tsum_eq]
  calc
    |∑' q : ℕ, ehmR1 (((q + 1 : ℕ) : ℝ) * x)| ≤
        ∑' q : ℕ, (8 / x ^ 2) * p q := by
      have hb := tsum_of_norm_bounded
        (f := fun q : ℕ => ehmR1 (((q + 1 : ℕ) : ℝ) * x))
        hmajor.hasSum
        (fun q => by simpa only [Real.norm_eq_abs] using hpoint q)
      simpa only [Real.norm_eq_abs] using hb
    _ = (8 / x ^ 2) * (∑' q : ℕ, p q) := tsum_mul_left
    _ ≤ (8 / x ^ 2) * 2 := by
      exact mul_le_mul_of_nonneg_left hpSum (by positivity)
    _ = 16 / x ^ 2 := by ring

/-- Under the full Ehm bridge, pole subtraction yields exponential decay on
the entire logarithmic line, not only on rational samples. -/
theorem abs_ehmReciprocityRegularizedLogKernel_le_exp
    (HS : EhmAutocorrelationR1SeriesBridge) (u : ℝ) :
    |ehmReciprocityRegularizedLogKernel u| ≤
      16 * Real.exp (-3 * |u| / 2) := by
  have hx : 0 < Real.exp |u| := Real.exp_pos _
  have hS := abs_ehmS1Autocorrelation_le_of_seriesBridge HS hx
  rw [ehmReciprocityRegularizedLogKernel_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (|u| / 2) *
          |ehmS1Autocorrelation (Real.exp |u|)| ≤
        Real.exp (|u| / 2) * (16 / (Real.exp |u|) ^ 2) :=
      mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le
    _ = 16 * Real.exp (-3 * |u| / 2) := by
      have hsq : (Real.exp |u|) ^ 2 = Real.exp (2 * |u|) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [hsq]
      calc
        Real.exp (|u| / 2) * (16 / Real.exp (2 * |u|)) =
            Real.exp (|u| / 2) *
              (16 * Real.exp (-(2 * |u|))) := by
          congr 2
          rw [div_eq_mul_inv, ← Real.exp_neg]
        _ = 16 *
            (Real.exp (|u| / 2) * Real.exp (-(2 * |u|))) := by ring
        _ = 16 * Real.exp (|u| / 2 + -(2 * |u|)) := by
          rw [Real.exp_add]
        _ = 16 * Real.exp (-3 * |u| / 2) := by
          congr 2
          ring

/-- The elementary Ehm remainder is Borel measurable. -/
theorem measurable_ehmR1 : Measurable ehmR1 := by
  have hH : Measurable ehmHarmonic := by
    have hnat : Measurable (fun n : ℕ => (harmonic n : ℝ)) :=
      measurable_of_countable _
    have hcomp : Measurable
        (fun x : ℝ => (harmonic ⌊x⌋₊ : ℝ)) :=
      hnat.comp Nat.measurable_floor
    convert hcomp using 1
    funext x
    exact ehmHarmonic_eq_harmonic_floor x
  unfold ehmR1
  fun_prop

/-- The all-real series bridge also supplies the measurability needed for
ordinary Fourier integration of the regularized logarithmic kernel. -/
theorem measurable_ehmReciprocityRegularizedLogKernel_of_seriesBridge
    (HS : EhmAutocorrelationR1SeriesBridge) :
    Measurable ehmReciprocityRegularizedLogKernel := by
  have hseries : Measurable (fun u : ℝ =>
      ∑' q : ℕ,
        ehmR1 (((q + 1 : ℕ) : ℝ) * Real.exp |u|)) := by
    apply Measurable.tsum
    intro q
    exact measurable_ehmR1.comp (by fun_prop)
  have hmodel : Measurable (fun u : ℝ =>
      Real.exp (|u| / 2) *
        ∑' q : ℕ,
          ehmR1 (((q + 1 : ℕ) : ℝ) * Real.exp |u|)) := by
    have hfactor : Measurable (fun u : ℝ => Real.exp (|u| / 2)) := by
      fun_prop
    exact hfactor.mul hseries
  convert hmodel using 1
  funext u
  rw [ehmReciprocityRegularizedLogKernel_eq_abs,
    ← (HS.hasSum_series (Real.exp |u|) (Real.exp_pos _)).tsum_eq]

private theorem integrable_ehmReciprocityExponentialMajorant :
    MeasureTheory.Integrable
      (fun u : ℝ => 16 * Real.exp (-3 * |u| / 2)) := by
  let f : ℝ → ℝ := fun u => 16 * Real.exp (-3 * |u| / 2)
  have hleftBase : MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.exp ((3 / 2 : ℝ) * u)) (Set.Iic 0) :=
    integrableOn_exp_mul_Iic (by norm_num) 0
  have hleft : MeasureTheory.IntegrableOn f (Set.Iic 0) := by
    apply MeasureTheory.IntegrableOn.congr_fun
      (hleftBase.const_mul 16) _ measurableSet_Iic
    intro u hu
    unfold f
    rw [abs_of_nonpos hu]
    ring_nf
  have hrightBase : MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.exp ((-3 / 2 : ℝ) * u)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  have hright : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
    apply MeasureTheory.IntegrableOn.congr_fun
      (hrightBase.const_mul 16) _ measurableSet_Ioi
    intro u hu
    unfold f
    rw [abs_of_pos hu]
    ring_nf
  have hall : MeasureTheory.IntegrableOn f
      (Set.Iic (0 : ℝ) ∪ Set.Ioi 0) := hleft.union hright
  have hcover : Set.Iic (0 : ℝ) ∪ Set.Ioi 0 = Set.univ := by
    ext u
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ,
      iff_true]
    exact le_or_gt u 0
  rw [hcover] at hall
  rw [MeasureTheory.integrableOn_univ] at hall
  simpa [f] using hall

/-- Under Ehm's all-real series theorem, the pole-subtracted kernel is an
ordinary `L¹(ℝ)` function.  The Fourier transform is therefore available
without distribution theory for this regularized sector. -/
theorem integrable_ehmReciprocityRegularizedLogKernel_of_seriesBridge
    (HS : EhmAutocorrelationR1SeriesBridge) :
    MeasureTheory.Integrable ehmReciprocityRegularizedLogKernel := by
  apply MeasureTheory.Integrable.mono'
    integrable_ehmReciprocityExponentialMajorant
    (measurable_ehmReciprocityRegularizedLogKernel_of_seriesBridge HS).aestronglyMeasurable
  filter_upwards with u
  exact abs_ehmReciprocityRegularizedLogKernel_le_exp HS u

/-- Ordinary Fourier transform of the pole-subtracted even kernel.  It is
defined for all inputs; the all-real Ehm bridge below certifies absolute
convergence. -/
noncomputable def ehmReciprocityRegularizedFourierDensity (t : ℝ) : ℂ :=
  ∫ u : ℝ,
    Complex.exp (-I * (t : ℂ) * (u : ℂ)) *
      (ehmReciprocityRegularizedLogKernel u : ℂ)

/-- The regularized Fourier integral is absolutely convergent at every real
frequency once Ehm's all-real series theorem is supplied. -/
theorem integrable_ehmReciprocityRegularizedFourierIntegrand
    (HS : EhmAutocorrelationR1SeriesBridge) (t : ℝ) :
    MeasureTheory.Integrable (fun u : ℝ =>
      Complex.exp (-I * (t : ℂ) * (u : ℂ)) *
        (ehmReciprocityRegularizedLogKernel u : ℂ)) := by
  have hregReal :=
    integrable_ehmReciprocityRegularizedLogKernel_of_seriesBridge HS
  have hregAbs : MeasureTheory.Integrable
      (fun u : ℝ => |ehmReciprocityRegularizedLogKernel u|) :=
    hregReal.abs
  have hphaseMeas : Measurable (fun u : ℝ =>
      Complex.exp (-I * (t : ℂ) * (u : ℂ))) := by
    fun_prop
  have hkernelMeas : Measurable (fun u : ℝ =>
      (ehmReciprocityRegularizedLogKernel u : ℂ)) :=
    (measurable_ehmReciprocityRegularizedLogKernel_of_seriesBridge HS).complex_ofReal
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun u : ℝ =>
      Complex.exp (-I * (t : ℂ) * (u : ℂ)) *
        (ehmReciprocityRegularizedLogKernel u : ℂ)) := by
    exact (hphaseMeas.mul hkernelMeas).aestronglyMeasurable
  apply MeasureTheory.Integrable.mono' hregAbs hmeas
  filter_upwards with u
  have hphase :
      -I * (t : ℂ) * (u : ℂ) = ((-t * u : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [Complex.norm_mul, hphase, Complex.norm_exp_ofReal_mul_I, one_mul]
  simp

/-- The ordinary Fourier density inherits exact frequency reflection from
the inversion symmetry of the regularized kernel. -/
theorem ehmReciprocityRegularizedFourierDensity_neg (t : ℝ) :
    ehmReciprocityRegularizedFourierDensity (-t) =
      ehmReciprocityRegularizedFourierDensity t := by
  let f : ℝ → ℂ := fun u =>
    Complex.exp (-I * (t : ℂ) * (u : ℂ)) *
      (ehmReciprocityRegularizedLogKernel u : ℂ)
  have hcomp :=
    (MeasureTheory.Measure.measurePreserving_neg
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)).integral_comp
        measurableEmbedding_neg f
  unfold ehmReciprocityRegularizedFourierDensity
  calc
    (∫ u : ℝ,
        Complex.exp (-I * ((-t : ℝ) : ℂ) * (u : ℂ)) *
          (ehmReciprocityRegularizedLogKernel u : ℂ)) =
      ∫ u : ℝ, f (-u) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        unfold f
        rw [ehmReciprocityRegularizedLogKernel_neg]
        congr 2
        push_cast
        ring
    _ = ∫ u : ℝ, f u := hcomp
    _ = ∫ u : ℝ,
        Complex.exp (-I * (t : ℂ) * (u : ℂ)) *
          (ehmReciprocityRegularizedLogKernel u : ℂ) := rfl

/-- Our angular-frequency convention is the ordinary Mathlib Fourier
transform evaluated at `t / (2 * π)`.  This normalization lemma is purely
algebraic; the all-real Ehm bridge above is what makes both sides genuine
absolutely convergent integrals. -/
theorem ehmReciprocityRegularizedFourierDensity_eq_fourier (t : ℝ) :
    ehmReciprocityRegularizedFourierDensity t =
      FourierTransform.fourier (fun u : ℝ =>
        (ehmReciprocityRegularizedLogKernel u : ℂ))
        (t / (2 * Real.pi)) := by
  rw [Real.fourier_eq']
  unfold ehmReciprocityRegularizedFourierDensity
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  simp only [Real.inner_apply, smul_eq_mul]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Riemann--Lebesgue for the pole-subtracted Ehm kernel.  Under the
all-positive-real Ehm series identity this is the decay of an ordinary
`L¹` Fourier density, rather than the vacuous value of a nonintegrable
Bochner integral. -/
theorem ehmReciprocityRegularizedFourierDensity_tendsto_cocompact
    (HS : EhmAutocorrelationR1SeriesBridge) :
    Tendsto ehmReciprocityRegularizedFourierDensity
      (cocompact ℝ) (nhds 0) := by
  have hL1 := integrable_ehmReciprocityRegularizedLogKernel_of_seriesBridge HS
  have hRL := Real.zero_at_infty_fourier
    (fun u : ℝ => (ehmReciprocityRegularizedLogKernel u : ℂ))
  have hscale : Tendsto (fun t : ℝ => t / (2 * Real.pi))
      (cocompact ℝ) (cocompact ℝ) := by
    let e : ℝ ≃ₜ ℝ := Homeomorph.mulLeft₀ (2 * Real.pi : ℝ)⁻¹ (by
      simp [Real.pi_ne_zero])
    have hmul : Tendsto (e : ℝ → ℝ) (cocompact ℝ) (cocompact ℝ) := by
      have ht : Tendsto (e : ℝ → ℝ) (cocompact ℝ)
          (map (e : ℝ → ℝ) (cocompact ℝ)) := tendsto_map
      simpa only [e.map_cocompact] using ht
    simpa only [e, Homeomorph.coe_mulLeft₀, div_eq_mul_inv, mul_comm] using hmul
  rw [show ehmReciprocityRegularizedFourierDensity =
      (fun t : ℝ =>
        FourierTransform.fourier (fun u : ℝ =>
          (ehmReciprocityRegularizedLogKernel u : ℂ))
          (t / (2 * Real.pi))) by
        funext t
        exact ehmReciprocityRegularizedFourierDensity_eq_fourier t]
  exact hRL.comp hscale

/-- Exact specialization of the regularized kernel to the logarithmic
integer lattice. -/
theorem ehmReciprocityRegularizedLogKernel_log_nat
    (n : ℕ) (hn : 0 < n) :
    ehmReciprocityRegularizedLogKernel (Real.log (n : ℝ)) =
      Real.exp (Real.log (n : ℝ) / 2) *
        ehmS1Autocorrelation (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ehmReciprocityRegularizedLogKernel_of_nonneg
    (Real.log_nonneg (by exact_mod_cast hn)), Real.exp_log hnR]

/-- The rational Ehm series bridge makes the pole-subtracted lattice kernel
quantitatively small.  The deliberately coarse `16/n` majorant avoids any
square-root infrastructure and is already sufficient for convergence. -/
theorem abs_ehmReciprocityRegularizedLogKernel_log_nat_le
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (n : ℕ) (hn : 0 < n) :
    |ehmReciprocityRegularizedLogKernel (Real.log (n : ℝ))| ≤
      16 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnOne
  have hexp : Real.exp (Real.log (n : ℝ) / 2) ≤ (n : ℝ) := by
    calc
      Real.exp (Real.log (n : ℝ) / 2) ≤
          Real.exp (Real.log (n : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = (n : ℝ) := Real.exp_log hnR
  have hS := abs_ehmS1Autocorrelation_nat_le HS n hn
  rw [ehmReciprocityRegularizedLogKernel_log_nat n hn, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (Real.log (n : ℝ) / 2) *
          |ehmS1Autocorrelation (n : ℝ)| ≤
        (n : ℝ) * (16 / (n : ℝ) ^ 2) :=
      mul_le_mul hexp hS (abs_nonneg _) (by positivity)
    _ = 16 / (n : ℝ) := by field_simp

/-- Unlike the raw centred kernel, the pole-subtracted kernel tends to zero
on the logarithmic integer lattice.  This is the first positive analytic
stop test for a Fourier/distributional realization. -/
theorem ehmReciprocityRegularizedLogKernel_log_nat_tendsto_zero
    (HS : EhmAutocorrelationR1RationalSeriesBridge) :
    Tendsto
      (fun n : ℕ =>
        ehmReciprocityRegularizedLogKernel
          (Real.log (((n + 1 : ℕ) : ℝ))))
      atTop (nhds 0) := by
  have hcast : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hinv : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hmajor : Tendsto
      (fun n : ℕ => 16 / (((n + 1 : ℕ) : ℝ))) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv :
      Tendsto (fun n : ℕ => (16 : ℝ) * (((n + 1 : ℕ) : ℝ))⁻¹)
        atTop (nhds (16 * 0)))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero'
    (g := fun n : ℕ => 16 / (((n + 1 : ℕ) : ℝ)))
    (Eventually.of_forall fun n => abs_nonneg _) ?_ hmajor
  · exact Eventually.of_forall fun n =>
      abs_ehmReciprocityRegularizedLogKernel_log_nat_le HS (n + 1) (by omega)

/-- Finite quadratic form generated by the pole-subtracted even kernel. -/
noncomputable def ehmReciprocityRegularizedLogConvolutionQuadratic
    (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    ehmReciprocityCenteredLogWeight N m *
      ehmReciprocityCenteredLogWeight N n *
        ehmReciprocityRegularizedLogKernel
          (Real.log (n : ℝ) - Real.log (m : ℝ))

/-- Finite quadratic form generated by the explicit two-pole mode. -/
noncomputable def ehmReciprocityPoleLogQuadratic (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    ehmReciprocityCenteredLogWeight N m *
      ehmReciprocityCenteredLogWeight N n *
        ehmReciprocityPoleLogMode
          (Real.log (n : ℝ) - Real.log (m : ℝ))

/-- Exact pole/regularized split of the centred convolution. -/
theorem ehmReciprocityCenteredLogConvolutionQuadratic_eq_regularized_add_pole
    (N : ℕ) :
    ehmReciprocityCenteredLogConvolutionQuadratic N =
      ehmReciprocityRegularizedLogConvolutionQuadratic N +
        ehmReciprocityPoleLogQuadratic N := by
  classical
  unfold ehmReciprocityCenteredLogConvolutionQuadratic
    ehmReciprocityRegularizedLogConvolutionQuadratic
    ehmReciprocityPoleLogQuadratic
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  unfold ehmReciprocityRegularizedLogKernel
  ring

/-- The exact low-frequency ledger after pole subtraction.  It must remain
coupled to the regularized convolution; no smallness is asserted. -/
noncomputable def ehmReciprocityPoleMomentCompletion (N : ℕ) : ℝ :=
  ehmReciprocityPoleLogQuadratic N +
    ehmReciprocityCenteredMomentCompletion N

/-- Final pole-subtracted normal form.  The formerly growing kernel has been
replaced by a lattice-decaying kernel, while every pole and moment term is
kept in one explicit finite completion. -/
theorem spectralEnergy_eq_regularizedLogConvolution_add_poleMoments
    (N : ℕ) :
    spectralEnergy N =
      ehmReciprocityRegularizedLogConvolutionQuadratic N +
        ehmReciprocityPoleMomentCompletion N := by
  rw [spectralEnergy_eq_centeredLogConvolution_add_moments,
    ehmReciprocityCenteredLogConvolutionQuadratic_eq_regularized_add_pole]
  unfold ehmReciprocityPoleMomentCompletion
  ring

/-- Difference between the complete finite two-pole/moment term and the
three named contour modes.  This is the exact amount that must be carried by
the elementary, continuous, Eisenstein, or residual trace sectors. -/
noncomputable def ehmReciprocityPoleNamedTraceMismatch
    (N : ℕ) (η σR : ℝ) : ℝ :=
  ehmReciprocityPoleMomentCompletion N -
    h15ContourTraceNamedTotal N η σR

/-- Exact global trace normalization after pole subtraction.  The
regularized Ehm convolution plus the unmatched pole ledger is precisely the
resolved non-named spectral ledger.  In particular, the correction cannot
be assigned to the named residues before the remaining trace sectors are
included. -/
theorem regularizedLogConvolution_add_poleMismatch_eq_resolvedLedger
    {η σL σR : ℝ} (A : H15GaussianMajorantFamilyData η σL σR)
    (D : H15ResolvedDualSpectralDecomposition η σR) (N : ℕ) :
    ehmReciprocityRegularizedLogConvolutionQuadratic N +
        ehmReciprocityPoleNamedTraceMismatch N η σR =
      h15ResolvedSpectralLedger D
        rationalAnalyticEstermannAtZeroPackage N σL := by
  have hresolved :
      spectralEnergy N =
        h15ContourTraceNamedTotal N η σR +
          h15ResolvedSpectralLedger D
            rationalAnalyticEstermannAtZeroPackage N σL := by
    rw [spectralEnergy_eq_coupledGcdRatioExpression,
      coupledGcdRatioExpression_eq_reciprocityCentered]
    exact reciprocityCenteredExpression_eq_resolvedSpectralExpression A D N
  rw [spectralEnergy_eq_regularizedLogConvolution_add_poleMoments] at hresolved
  unfold ehmReciprocityPoleNamedTraceMismatch
  linarith

/-- The sharpened open estimate after the two explicit pole modes have been
removed from the kernel.  This is equivalent to the original H15 target,
but its kernel passes the logarithmic-lattice decay stop test. -/
structure EhmRegularizedLogConvolutionCancellationEstimate where
  C : ℝ
  C_pos : 0 < C
  alpha : ℝ
  alpha_pos : 0 < alpha
  bound : ∀ N : ℕ, 2 ≤ N →
    |ehmReciprocityRegularizedLogConvolutionQuadratic N +
      ehmReciprocityPoleMomentCompletion N| ≤
        C / (Real.log (N : ℝ)) ^ alpha

/-- Pole-subtracted signed cancellation supplies the original coupled H15
estimate without any quantitative loss. -/
noncomputable def EhmRegularizedLogConvolutionCancellationEstimate.toCoupled
    (H : EhmRegularizedLogConvolutionCancellationEstimate) :
    CoupledLogTaperCancellationEstimate where
  C := H.C
  C_pos := H.C_pos
  α := H.alpha
  α_pos := H.alpha_pos
  bound N hN := by
    rw [← spectralEnergy_eq_coupledGcdRatioExpression,
      spectralEnergy_eq_regularizedLogConvolution_add_poleMoments]
    exact H.bound N hN

/-! ## Consequence for the contour projection intuition -/

/-- Residue, completed zero frequency, and Gram diagonal cannot by
themselves be the global H15 correction projection: the assertion already
fails at the first nontrivial cutoff, for every contour parameter. -/
theorem no_named_trace_modes_global_correction_projection :
    ¬ ∃ η c : ℝ, ∀ N : ℕ, 2 ≤ N →
      h15ContourTraceNamedTotal N η c =
        -h15LinearEndpointCorrection N := by
  rintro ⟨η, c, h⟩
  exact h15ContourTraceNamedTotal_two_ne_neg_correction η c (h 2 (by omega))

end RH.Criteria.NymanBeurling.BCFLogTaperEhmCenteredKernelAudit
