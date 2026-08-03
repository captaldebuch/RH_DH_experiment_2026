import RiemannHypothesis.Criteria.NymanBeurling.H14DvpChain

/-!
# H14: weak effective Perron interface

The repository already contains `WeakEffectivePerronPackage` and the
elementary theorem assembling it into `ClassicalMertensDecay`. The genuinely
analytic part still consists of proving the contour identity and its three
side estimates. This file makes those inputs explicit and connects them to
the existing package; it does not hide the contour argument behind an axiom.
-/

namespace RH.Criteria.NymanBeurling

open MobiusSummatory

/-! A generic, finite-height Perron identity. The identity itself is an input
until the corresponding contour theorem is formalized. -/
structure PerronFormulaInput where
  summatory : ℕ → ℂ
  contourValue : ℕ → ℂ
  truncationError : ℕ → ℂ
  formula : ∀ N : ℕ, summatory N = contourValue N + truncationError N

theorem perron_formula_generic (P : PerronFormulaInput) (N : ℕ) :
    P.summatory N = P.contourValue N + P.truncationError N :=
  P.formula N

/-! The Möbius specialization keeps the coefficient identity visible in the
interface. Its `formula` field is the effective Perron statement still to be
proved from the Dirichlet series and a contour shift. -/
structure MobiusPerronFormulaInput where
  contourValue : ℕ → ℂ
  truncationError : ℕ → ℂ
  formula : ∀ N : ℕ,
    (MobiusSummatory.mobiusSummatory N : ℂ) =
      contourValue N + truncationError N

theorem perron_mobius_summation_formula
    (P : MobiusPerronFormulaInput) (N : ℕ) :
    (MobiusSummatory.mobiusSummatory N : ℂ) =
      P.contourValue N + P.truncationError N :=
  P.formula N

/-! Concrete side-bound data for the real-valued weak package already used by
`H14DvpChain`. The fields are deliberately stated at the same `N ≥ 2`
range as that package, so the conversion below is definitionally direct. -/
structure PerronContourInput where
  contourTerm : ℕ → ℝ
  contourHeight : ℕ → ℝ
  contourHeight_pos : ∀ N : ℕ, 0 < contourHeight N
  C_main : ℝ
  C_error : ℝ
  a : ℝ
  C_main_pos : 0 < C_main
  C_error_pos : 0 < C_error
  a_pos : 0 < a
  contour_term_bound :
    ∀ N : ℕ, 2 ≤ N →
      |contourTerm N| ≤ C_main * (N : ℝ) *
        Real.exp (-a * Real.sqrt (Real.log N))
  approximation_error_bound :
    ∀ N : ℕ, 2 ≤ N →
      |MobiusSummatory.mobiusSummatory N - contourTerm N| ≤
        C_error * (N : ℝ) * Real.exp (-a * Real.sqrt (Real.log N))

/-! Residue bookkeeping is separated from the bounds. `simple_pole_at_one`
records the analytic claim needed to justify residue extraction; the numerical
value is exposed rather than being inferred from an unproved contour theorem.
-/
structure PerronResidueData where
  residueMainTerm : ℕ → ℝ
  residueValue : ℕ → ℝ
  residue_identity : ∀ N : ℕ, residueMainTerm N = residueValue N
  simple_pole_at_one : Prop

/-! Full application data: a zero-free region, explicit contour metadata,
residue bookkeeping, and the real estimates consumed by the decay theorem. -/
structure ZeroFreeRegionPerronApplication where
  zero_free_region : DeLaValleePoussinZeroFreeRegion
  contour : PerronContourInput
  residue : PerronResidueData
  residue_matches_contour :
    ∀ N : ℕ, residue.residueMainTerm N = contour.contourTerm N

def ZeroFreeRegionPerronApplication.toWeakEffectivePerronPackage
    (P : ZeroFreeRegionPerronApplication) : WeakEffectivePerronPackage :=
  { contourTerm := P.contour.contourTerm
    C_main := P.contour.C_main
    C_error := P.contour.C_error
    a := P.contour.a
    C_main_pos := P.contour.C_main_pos
    C_error_pos := P.contour.C_error_pos
    a_pos := P.contour.a_pos
    contour_term_bound := P.contour.contour_term_bound
    approximation_error_bound := P.contour.approximation_error_bound }

/-! Once the contour package is inhabited, this supplies exactly the classical
decay hypothesis required by the rest of H14. -/
noncomputable def classicalMertensDecay_of_zero_free_region_perron
    (P : ZeroFreeRegionPerronApplication) : ClassicalMertensDecay :=
  classicalMertensDecay_of_weakEffectivePerron
    P.toWeakEffectivePerronPackage

theorem perron_contour_bounds
    (P : ZeroFreeRegionPerronApplication) (N : ℕ) (hN : 2 ≤ N) :
    |P.contour.contourTerm N| ≤ P.contour.C_main * (N : ℝ) *
        Real.exp (-P.contour.a * Real.sqrt (Real.log N)) ∧
      |MobiusSummatory.mobiusSummatory N - P.contour.contourTerm N| ≤
        P.contour.C_error * (N : ℝ) *
          Real.exp (-P.contour.a * Real.sqrt (Real.log N)) :=
  ⟨P.contour.contour_term_bound N hN,
    P.contour.approximation_error_bound N hN⟩

end RH.Criteria.NymanBeurling
