import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperCotangentReduction

/-!
# Route B1: the coupled Estermann-at-zero reduction

Bettin--Conrey use the normalization

`D(0, h/k) = 1/4 + (i/2) c₀(h/k)`

for coprime positive `h,k`.  With the Vasyunin convention used by this
project, a change of residues gives `V(h,k) = -c₀(h⁻¹/k)`, and hence

`D(0, h⁻¹/k) = 1/4 - (i/2) V(h,k)`.

This module records that normalization as an explicit package and transports
it through the complete logarithmically tapered gcd-ratio expression.  The
factorized, logarithmic-ratio, linear, and constant corrections are retained.

No analytic continuation or functional equation for the Estermann function
is claimed here.  The canonical package at the end only proves that the
normalization is algebraically consistent; identifying its values with the
analytic Estermann Dirichlet series is the next Route-B theorem.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral
open RH.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The exact special-value normalization needed from an analytic Estermann
family.  Only reduced positive fractions occur in the gcd-ratio sum. -/
structure EstermannAtZeroPackage where
  value : ℕ → ℕ → ℂ
  value_eq_vasyunin : ∀ a q : ℕ, 0 < a → 0 < q → Nat.Coprime a q →
    value a q =
      (1 / 4 : ℂ) - Complex.I / 2 * (cotangentSumVFormula a q : ℂ)

/-- The imaginary part of a normalized Estermann value is `-V(a,q)/2`. -/
theorem EstermannAtZeroPackage.value_im_eq
    (H : EstermannAtZeroPackage) (a q : ℕ)
    (ha : 0 < a) (hq : 0 < q) (hcop : Nat.Coprime a q) :
    (H.value a q).im = -cotangentSumVFormula a q / 2 := by
  rw [H.value_eq_vasyunin a q ha hq hcop]
  simp
  ring

/-- The primitive Gram kernel after replacing both oriented Vasyunin sums by
the imaginary parts of their Estermann values at zero. -/
noncomputable def estermannCoprimeGramKernel
    (H : EstermannAtZeroPackage) (a b : ℕ) : ℝ :=
  (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
      (1 / (a : ℝ) + 1 / (b : ℝ)) +
    ((b : ℝ) - (a : ℝ)) / (2 * (a : ℝ) * (b : ℝ)) *
      Real.log ((a : ℝ) / (b : ℝ)) +
    Real.pi / ((a : ℝ) * (b : ℝ)) *
      ((H.value a b).im + (H.value b a).im)

/-- Pointwise Bettin--Conrey/Vasyunin special-value substitution. -/
theorem vasyuninBEntryFormula_eq_estermannCoprimeGramKernel
    (H : EstermannAtZeroPackage) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) :
    vasyuninBEntryFormula a b = estermannCoprimeGramKernel H a b := by
  unfold vasyuninBEntryFormula estermannCoprimeGramKernel
  rw [H.value_im_eq a b ha hb hcop,
    H.value_im_eq b a hb ha hcop.symm]
  ring

/-- One gcd slice written entirely with primitive Estermann values at zero. -/
noncomputable def estermannCoprimeRatioSlice
    (H : EstermannAtZeroPackage) (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ b ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a b then
      dirichletCoeff N (g * a) * dirichletCoeff N (g * b) *
        (g : ℝ)⁻¹ * estermannCoprimeGramKernel H a b
    else 0

/-- The proved Vasyunin formula and the Estermann special-value normalization
give an exact identity on every positive gcd slice. -/
theorem gramCoprimeRatioSlice_eq_estermannCoprimeRatioSlice
    (H : EstermannAtZeroPackage) (N g : ℕ) :
    gramCoprimeRatioSlice N g = estermannCoprimeRatioSlice H N g := by
  classical
  unfold gramCoprimeRatioSlice estermannCoprimeRatioSlice
  apply Finset.sum_congr rfl
  intro a ha_mem
  have ha : 0 < a :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha_mem).1
  apply Finset.sum_congr rfl
  intro b hb_mem
  have hb : 0 < b :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb_mem).1
  split_ifs with hcop
  · rw [baezDuarteGramEntry_eq_vasyuninBEntryFormula_proved a b ha hb,
      vasyuninBEntryFormula_eq_estermannCoprimeGramKernel H a b ha hb hcop]
  · rfl

/-- The complete coupled Estermann-side expression.  It deliberately keeps
the linear correction and constant inside the analytic target. -/
noncomputable def estermannCoupledExpression
    (H : EstermannAtZeroPackage) (N : ℕ) : ℝ :=
  (∑ g ∈ Finset.Icc 1 N, estermannCoprimeRatioSlice H N g) +
    2 * gramLinearCorrection N + 1

/-- Route B1: exact finite realization of the original coupled H15 expression
by primitive Estermann values at zero. -/
theorem coupledGcdRatioExpression_eq_estermannCoupledExpression
    (H : EstermannAtZeroPackage) (N : ℕ) :
    coupledGcdRatioExpression N = estermannCoupledExpression H N := by
  unfold coupledGcdRatioExpression estermannCoupledExpression
  apply congrArg (fun x : ℝ => x + 2 * gramLinearCorrection N + 1)
  apply Finset.sum_congr rfl
  intro g _
  exact gramCoprimeRatioSlice_eq_estermannCoprimeRatioSlice H N g

/-- The exact analytic output required after Estermann reciprocity and any
subsequent automorphic transform. -/
structure EstermannCoupledCancellationEstimate
    (H : EstermannAtZeroPackage) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ N : ℕ, 2 ≤ N →
    |estermannCoupledExpression H N| ≤ C / (Real.log (N : ℝ)) ^ α

/-- A bound for the complete Estermann expression closes the existing H15
cancellation interface without dropping any correction term. -/
def EstermannCoupledCancellationEstimate.toCoupledLogTaper
    (H : EstermannAtZeroPackage)
    (E : EstermannCoupledCancellationEstimate H) :
    CoupledLogTaperCancellationEstimate where
  C := E.C
  C_pos := E.C_pos
  α := E.α
  α_pos := E.α_pos
  bound N hN := by
    rw [coupledGcdRatioExpression_eq_estermannCoupledExpression H]
    exact E.bound N hN

/-! ## Algebraic consistency of the inverse-residue normalization -/

/-- The formal special value determined by the finite Vasyunin sum.  This is
not a definition of the analytic Estermann function.  Analytically, the
arguments `a,q` correspond to `D(0,a⁻¹/q)`. -/
noncomputable def formalEstermannAtZeroValue (a q : ℕ) : ℂ :=
  (1 / 4 : ℂ) - Complex.I / 2 * (cotangentSumVFormula a q : ℂ)

/-- The normalization package is inhabited without assumptions.  Its value is
the formal finite expression above; a future analytic theorem must identify
this expression with the continued Estermann Dirichlet series. -/
noncomputable def formalEstermannAtZeroPackage : EstermannAtZeroPackage where
  value := formalEstermannAtZeroValue
  value_eq_vasyunin := by
    intro a q _ _ _
    rfl

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction
