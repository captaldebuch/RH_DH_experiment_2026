/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB11VasyuninEvaluation
import NBMellinTools.NB12BBLSH15PoleDiagnostic

/-!
# NB15 exploration: certified pre-functional-equation assembly

This file fixes the source side of the H15/NB12 comparison.  It does not try
to identify one local PostFE block with the global Nyman--Beurling energy.
Instead it gives an exact, correction-preserving pre-FE expression and proves
that it is the certified NB8 energy.

The cotangent part is split by the same primitive-interior condition used by
the active NB12 Laurent rows.  The complementary endpoint sector is retained
explicitly.  The final lemmas verify the coefficient and row-weight
normalizations used by NB12.

No contour shift, functional equation, limit, or decay estimate occurs here.
-/

open scoped BigOperators

namespace NBMellinTools.NB15

open NBMellinTools
open NBMellinTools.NB8
open NBMellinTools.NB9
open NBMellinTools.NB10
open NBMellinTools.NB11
open NBMellinTools.NB12

/-! ## Exact certified source -/

/-- The retained constant and linear correction in the certified NB8
normalization. -/
noncomputable def preFECorrection (n : ℕ) : ℝ :=
  bdCorrectionTerm (logTaperLength n) (logTaperCoeffs n)

/-- The elementary constant part of the certified Vasyunin expression. -/
noncomputable def preFEConstant (n : ℕ) : ℝ :=
  vasyuninConstantTerm (logTaperLength n) (logTaperCoeffs n)

/-- The elementary logarithmic-ratio part of the certified Vasyunin
expression. -/
noncomputable def preFELogRatio (n : ℕ) : ℝ :=
  vasyuninLogRatioTerm (logTaperLength n) (logTaperCoeffs n)

/-- The full two-orientation cotangent part before the functional equation. -/
noncomputable def preFECotangent (n : ℕ) : ℝ :=
  vasyuninCotangentTerm (logTaperLength n) (logTaperCoeffs n)

/-- The exact correction-preserving pre-functional-equation assembly. -/
noncomputable def preFEAssembly (n : ℕ) : ℝ :=
  preFECorrection n + preFEConstant n + preFELogRatio n + preFECotangent n

/-- The pre-FE assembly is definitionally the NB10 coupled Vasyunin
expression. -/
theorem preFEAssembly_eq_vasyuninCoupledExpression (n : ℕ) :
    preFEAssembly n =
      vasyuninCoupledExpression (logTaperLength n) (logTaperCoeffs n) := by
  rfl

/-- Certified global bridge: the exact NB8 Nyman--Beurling energy is the
complete pre-FE assembly. -/
theorem logTaperL2Error_eq_preFEAssembly (n : ℕ) :
    logTaperL2Error n = preFEAssembly n := by
  rw [preFEAssembly_eq_vasyuninCoupledExpression]
  exact logTaperL2Error_eq_vasyuninCoupledExpression n

/-! ## Primitive interior versus retained endpoints -/

/-- The positive denominator represented by a zero-based finite index. -/
def finDenominator {N : ℕ} (j : Fin N) : ℕ := j.val + 1

/-- The primitive numerator obtained after removing the common gcd of two
positive denominators. -/
def primitiveLeft {N : ℕ} (j k : Fin N) : ℕ :=
  finDenominator j / Nat.gcd (finDenominator j) (finDenominator k)

/-- The primitive denominator obtained after removing the common gcd. -/
def primitiveRight {N : ℕ} (j k : Fin N) : ℕ :=
  finDenominator k / Nat.gcd (finDenominator j) (finDenominator k)

/-- Exactly the interior condition imposed on the two primitive variables in
`NB12.h15LaurentRowValid`. -/
def IsPrimitiveInterior {N : ℕ} (j k : Fin N) : Prop :=
  2 ≤ primitiveLeft j k ∧ 2 ≤ primitiveRight j k

/-- One complete two-orientation cotangent summand in NB10. -/
noncomputable def preFECotangentSummand
    {N : ℕ} (coeffs : Fin N → ℝ) (j k : Fin N) : ℝ :=
  coeffs j * coeffs k *
    (-Real.pi /
        (2 * ((j.val + 1 : ℕ) : ℝ) * ((k.val + 1 : ℕ) : ℝ)) *
      (vasyuninCotangentSum (j.val + 1) (k.val + 1) +
        vasyuninCotangentSum (k.val + 1) (j.val + 1)))

/-- The part of the certified cotangent sum whose gcd-reduced variables are
both at least two.  This is the finite source sector indexed by active NB12
Laurent rows. -/
noncomputable def preFEInteriorCotangent (n : ℕ) : ℝ :=
  by
    classical
    exact ∑ j : Fin (logTaperLength n), ∑ k : Fin (logTaperLength n),
      if IsPrimitiveInterior j k then
        preFECotangentSummand (logTaperCoeffs n) j k
      else 0

/-- The complementary primitive endpoint sector.  It must travel with the
contour correction ledger; active NB12 rows deliberately exclude it. -/
noncomputable def preFEEndpointCotangent (n : ℕ) : ℝ :=
  by
    classical
    exact ∑ j : Fin (logTaperLength n), ∑ k : Fin (logTaperLength n),
      if IsPrimitiveInterior j k then 0
      else preFECotangentSummand (logTaperCoeffs n) j k

/-- Exact interior/endpoint partition of the certified cotangent term. -/
theorem preFECotangent_eq_interior_add_endpoint (n : ℕ) :
    preFECotangent n =
      preFEInteriorCotangent n + preFEEndpointCotangent n := by
  classical
  unfold preFECotangent vasyuninCotangentTerm
    preFEInteriorCotangent preFEEndpointCotangent preFECotangentSummand
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : IsPrimitiveInterior j k <;> simp [h]

/-- The exact global source written with the NB12 interior sector and its
retained endpoint complement separated. -/
noncomputable def preFESectorAssembly (n : ℕ) : ℝ :=
  preFECorrection n + preFEConstant n + preFELogRatio n +
    preFEInteriorCotangent n + preFEEndpointCotangent n

theorem preFEAssembly_eq_sectorAssembly (n : ℕ) :
    preFEAssembly n = preFESectorAssembly n := by
  rw [preFEAssembly, preFESectorAssembly,
    preFECotangent_eq_interior_add_endpoint]
  ring

/-- Certified energy identity with the primitive endpoint sector visible. -/
theorem logTaperL2Error_eq_preFESectorAssembly (n : ℕ) :
    logTaperL2Error n = preFESectorAssembly n := by
  rw [logTaperL2Error_eq_preFEAssembly, preFEAssembly_eq_sectorAssembly]

/-! ## NB12 normalization checks -/

/-- NB12's natural one-based logarithmic taper is exactly the NB8 finite
coefficient at the corresponding denominator. -/
theorem h15NaturalLogTaperCoeff_eq_logTaperCoeffs
    (n : ℕ) (k : Fin (logTaperLength n)) :
    h15NaturalLogTaperCoeff (logTaperLength n) (k.val + 1) =
      logTaperCoeffs n k := by
  rfl

/-- The coefficient expected for one oriented primitive row after gcd
scaling.  The two orientations carry the same coefficient. -/
noncomputable def preFEOrientedInteriorRowWeight
    (N g a q : ℕ) : ℂ :=
  (h15NaturalLogTaperCoeff N (g * a) *
      h15NaturalLogTaperCoeff N (g * q) /
      (g : ℝ) * Real.pi / ((a : ℝ) * (q : ℝ)) : ℝ)

/-- On active support, the NB12 Laurent-row weight has exactly the certified
Möbius/log-taper and gcd normalization. -/
theorem h15LaurentRowWeight_eq_preFEOrientedInteriorRowWeight
    {N : ℕ} (i : H15LaurentRowIndex N) (hi : h15LaurentRowValid i) :
    h15LaurentRowWeight i =
      preFEOrientedInteriorRowWeight N
        (h15LaurentG i) (h15LaurentA i) (h15LaurentQ i) := by
  simp [h15LaurentRowWeight, hi, preFEOrientedInteriorRowWeight]

/-- Every active NB12 row is genuinely in the primitive interior sector. -/
theorem h15LaurentRowValid_interior
    {N : ℕ} (i : H15LaurentRowIndex N) (hi : h15LaurentRowValid i) :
    2 ≤ h15LaurentA i ∧ 2 ≤ h15LaurentQ i := by
  exact ⟨hi.2.2.1, hi.2.2.2.1⟩

/-- Every active NB12 row uses a coprime primitive pair. -/
theorem h15LaurentRowValid_coprime
    {N : ℕ} (i : H15LaurentRowIndex N) (hi : h15LaurentRowValid i) :
    Nat.Coprime (h15LaurentA i) (h15LaurentQ i) :=
  hi.2.2.2.2

end NBMellinTools.NB15
