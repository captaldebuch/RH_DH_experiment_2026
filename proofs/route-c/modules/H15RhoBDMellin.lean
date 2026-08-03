import RiemannHypothesis.Criteria.NymanBeurling.H15FractionalTail

/-!
# Mellin transform of the Báez--Duarte generators

The generator `rhoBD k` is a positive dilation of the single base function
`x ↦ {1/x}`.  Mathlib already proves the Mellin scaling law for positive
dilations.  We expose that reduction here and isolate the only remaining
analytic identity: the Mellin transform of the base fractional-part function.
-/

namespace RH.Criteria.NymanBeurling.BaezDuarte

open RH.Criteria.NymanBeurling

/-- The undilated fractional-part generator. -/
noncomputable def rhoBDBase (x : ℝ) : ℝ :=
  Int.fract (1 / x)

/-- Each actual Báez--Duarte generator is the base generator composed with the
positive dilation `x ↦ (k+1)x`. -/
theorem rhoBD_eq_rhoBDBase_comp (k : ℕ) (x : ℝ) :
    rhoBD k x = rhoBDBase (((k + 1 : ℕ) : ℝ) * x) := by
  simp [rhoBD, rhoBDBase, Nat.cast_add, Nat.cast_one]

/-- Unconditional Mellin scaling reduction for `rhoBD`. -/
theorem rhoBD_mellin_eq_scaled_base (k : ℕ) (s : ℂ) :
    mellin (fun x : ℝ => (rhoBD k x : ℂ)) s =
      (((((k + 1 : ℕ) : ℝ) : ℂ) ^ (-s))) •
        mellin (fun x : ℝ => (rhoBDBase x : ℂ)) s := by
  have ha : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  simpa only [rhoBD_eq_rhoBDBase_comp, Nat.cast_add, Nat.cast_one,
    Complex.ofReal_natCast] using
    (mellin_comp_mul_left (fun x : ℝ => (rhoBDBase x : ℂ)) s ha)

/-- Inversion turns the base generator into the Mellin transform of the ordinary
fractional-part function.  This is the exact change of variables underlying the
classical integral proof of the remaining base formula. -/
theorem rhoBDBase_mellin_eq_mellin_fract_inv (s : ℂ) :
    mellin (fun x : ℝ => (rhoBDBase x : ℂ)) s =
      mellin (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) (-s : ℂ) := by
  simpa [rhoBDBase, one_div] using
    (mellin_comp_inv (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) s)

/-! ## The single remaining base Mellin debt -/

/-- The exact analytic base identity needed for the generator formula.  It is
left as a content-bearing hypothesis because Mathlib has no fractional-part
Mellin evaluation or the required integration-by-parts continuation. -/
structure RhoBDBaseMellinFormula where
  formula :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s ≠ 0 →
      mellin (fun x : ℝ => (rhoBDBase x : ℂ)) s =
        -(riemannZeta s) / s

/-- Conditional assembly of the exact NB0 generator formula from the one base
Mellin identity. -/
theorem rhoBD_mellin_formula_of_base
    (H : RhoBDBaseMellinFormula)
    (k : ℕ) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsne : s ≠ 0) :
    mellin (fun x : ℝ => (rhoBD k x : ℂ)) s =
      -(riemannZeta s) /
        (s * ((((k + 1 : ℕ) : ℝ) : ℂ) ^ s)) := by
  rw [rhoBD_mellin_eq_scaled_base, H.formula s hs0 hs1 hsne]
  rw [smul_eq_mul, Complex.cpow_neg]
  field_simp

/-- The same conditional formula in the direct natural-to-complex cast
notation used by the NB0 frozen statement.  This is only a presentation
wrapper around `rhoBD_mellin_formula_of_base`. -/
theorem rhoBD_mellin_formula_of_base_nb0
    (H : RhoBDBaseMellinFormula)
    (k : ℕ) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsne : s ≠ 0) :
    mellin (fun x : ℝ => (rhoBD k x : ℂ)) s =
      -(riemannZeta s) / (s * ((k + 1 : ℕ) : ℂ) ^ s) := by
  simpa only [Complex.ofReal_natCast] using
    rhoBD_mellin_formula_of_base H k s hs0 hs1 hsne

end RH.Criteria.NymanBeurling.BaezDuarte
