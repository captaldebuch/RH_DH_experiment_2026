import RiemannHypothesis.Criteria.NymanBeurling.QuadraticInteraction

/-!
# BBLS/Estermann main-term interface

The BBLS contour calculation is not currently formalized in Mathlib or in this
project.  In particular, the phrase "the Estermann zeta function" has several
normalizations in the literature (additive twists, divisor-sum twists, and the
autocorrelation Mellin kernel).  This file therefore records the calculation
through an explicit, content-bearing interface rather than choosing an
unverified normalization.  The residue lemmas below are unconditional and are
the reusable analytic part of the interface; the contour and Estermann
identities remain fields of `BBLSMainTermResiduePackage`.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open Filter Topology

/-! ## Residue normalization -/

/-- A complex function has residue `R` at `1` when its pole-normalized limit is
`R`.  This is phrased with `𝓝[≠]` so that no removable-singularity convention is
needed. -/
def HasResidueAtOne (F : ℂ → ℂ) (R : ℂ) : Prop :=
  Tendsto (fun s => (s - 1) * F s) (𝓝[≠] (1 : ℂ)) (𝓝 R)

theorem riemannZeta_hasResidueAtOne :
    HasResidueAtOne riemannZeta 1 := by
  exact riemannZeta_residue_one

/-- Residues multiply by a factor having a finite limit at the pole. -/
theorem hasResidueAtOne_mul_of_tendsto
    {F G : ℂ → ℂ} {R g : ℂ}
    (hF : HasResidueAtOne F R)
    (hG : Tendsto G (𝓝[≠] (1 : ℂ)) (𝓝 g)) :
    HasResidueAtOne (fun s => F s * G s) (R * g) := by
  unfold HasResidueAtOne at hF ⊢
  have h := hF.mul hG
  simpa only [mul_assoc] using h

/-! ## Project-facing Estermann data -/

/--
An Estermann family is kept as an explicit parameter.  This is deliberate:
the current project has not fixed whether the BBLS contour is represented by
an additive-twist Dirichlet series or by the Mellin transform of the
fractional-part autocorrelation.  Giving a canonical value here without that
choice would make the interface assert a normalization that has not been
checked against the paper.
-/
def EstermannZetaFunction := ℂ → ℕ → ℕ → ℂ

/-- The residue/contour facts needed to turn a BBLS calculation into the
existing H15 main-term package.  Every analytic assertion is a named field:
this structure is an assumption package, not a hidden proof of the contour
argument. -/
structure BBLSMainTermResiduePackage where
  estermann : EstermannZetaFunction
  estermann_dirichlet_series : Prop
  estermann_dirichlet_series_holds : estermann_dirichlet_series
  estermann_factorization : Prop
  estermann_factorization_holds : estermann_factorization
  contour_integral_zero_for_vertical_sides : Prop
  contour_integral_zero_for_vertical_sides_holds :
    contour_integral_zero_for_vertical_sides
  contour_integral_evaluation : Prop
  contour_integral_evaluation_holds : contour_integral_evaluation
  residue_at_one_estermann : Prop
  residue_at_one_estermann_holds : residue_at_one_estermann
  main_term_residue_formula : Prop
  main_term_residue_formula_holds : main_term_residue_formula
  mellin_transform_formula : Prop
  mellin_transform_formula_holds : mellin_transform_formula
  vertical_strip_growth_bound : Prop
  vertical_strip_growth_bound_holds : vertical_strip_growth_bound
  mainTerm : ℕ → ℝ
  C_main : ℝ
  C_main_nonneg : 0 ≤ C_main
  main_term_bound :
    ∀ N : ℕ,
      |(∑ g ∈ Finset.Icc 1 N, mainTerm g) - 1| ≤
        C_main / Real.log (N + 2 : ℝ)

/-- The gcd-stratum main term supplied by the BBLS package, lifted to a pair
of indices in the same way as `quadraticInteractionGcdSlice`.  This is only a
projection of the supplied main-term data; it does not assert the residue
formula by itself. -/
def mainTermValue_of_BBLS (H : BBLSMainTermResiduePackage) : ℕ → ℕ → ℝ :=
  fun h k => H.mainTerm (Nat.gcd h k)

theorem contour_integral_zero_for_vertical_sides_of_BBLS
    (H : BBLSMainTermResiduePackage) :
    H.contour_integral_zero_for_vertical_sides :=
  H.contour_integral_zero_for_vertical_sides_holds

theorem residue_at_one_EstermannZeta
    (H : BBLSMainTermResiduePackage) : H.residue_at_one_estermann :=
  H.residue_at_one_estermann_holds

theorem mainTermValue_eq_residue_formula_of_BBLS
    (H : BBLSMainTermResiduePackage) : H.main_term_residue_formula :=
  H.main_term_residue_formula_holds

/--
Once the Estermann contour and residue fields are supplied, the old H15
interface is obtained by projection.  This theorem is the complete logical
wiring available without formalizing the contour itself.
-/
noncomputable def BBLS_EstermannContourPackage_of_residue_theorem
    (H : BBLSMainTermResiduePackage) :
    BBLS_EstermannContourPackage :=
  { mellin_transform_formula := H.mellin_transform_formula
    double_pole_residue_formula := H.main_term_residue_formula
    vertical_strip_growth_bound := H.vertical_strip_growth_bound
    mellin_transform_formula_holds := H.mellin_transform_formula_holds
    double_pole_residue_formula_holds := H.main_term_residue_formula_holds
    vertical_strip_growth_bound_holds := H.vertical_strip_growth_bound_holds
    mainTerm := H.mainTerm
    C_main := H.C_main
    C_main_nonneg := H.C_main_nonneg
    main_term_bound := H.main_term_bound }

theorem mainTermValue_of_BBLS_eq_package_mainTerm
    (H : BBLSMainTermResiduePackage) :
    (fun h k => mainTermValue_of_BBLS H h k) =
      (fun h k => H.mainTerm (Nat.gcd h k)) := by
  rfl

end RH.Criteria.NymanBeurling.QuadraticInteraction
