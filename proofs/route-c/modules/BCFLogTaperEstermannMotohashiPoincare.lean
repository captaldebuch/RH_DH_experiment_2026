import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Analysis.Seminorm
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSynthesis

/-!
# BT1-C0: a rigorous Poincare-series boundary for the H15 Motohashi route

Motohashi's formal big-cell calculation starts with a seed invariant under a
cusp subgroup and sums it over left cosets.  Mathlib has the required coset
and infinite-sum infrastructure, but no Poincare-series or automorphic
spectral library.  This file supplies the general coset construction and
proves its automorphy and convergence transport exactly.

The H15-specific structure at the end records the two facts that cannot be
manufactured from the arithmetic seed alone:

* an analytic seed on an actual group homogeneous space whose geometric
  coefficient unfolds to the canonical H15 seed aggregate; and
* a uniform family of seminorm bounds for that analytic seed.

No such realization, trace formula, or signed spectral estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPoincare

open Complex
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovGate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovProof
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSeed
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSynthesis

universe u v

section AbstractPoincare

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

/-- Left cosets `H \ Γ`, represented by Mathlib's right-coset relation. -/
abbrev LeftCoset (H : Subgroup Γ) := Quotient (QuotientGroup.rightRel H)

/-- Right multiplication permutes the left cosets `H \ Γ`. -/
def leftCosetMulRightEquiv (H : Subgroup Γ) (δ : Γ) :
    LeftCoset H ≃ LeftCoset H where
  toFun := Quotient.map' (fun γ => γ * δ) (by
    intro a b hab
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab)
  invFun := Quotient.map' (fun γ => γ * δ⁻¹) (by
    intro a b hab
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab)
  left_inv c := by
    induction c using Quotient.inductionOn' with
    | _ γ => simp [Quotient.map'_mk'', mul_assoc]
  right_inv c := by
    induction c using Quotient.inductionOn' with
    | _ γ => simp [Quotient.map'_mk'', mul_assoc]

@[simp]
theorem leftCosetMulRightEquiv_mk (H : Subgroup Γ) (δ γ : Γ) :
    leftCosetMulRightEquiv H δ (Quotient.mk'' γ) =
      Quotient.mk'' (γ * δ) :=
  rfl

/-- A cusp-invariant seed descends to a summand indexed by `H \ Γ`.

The inverse on `γ` is a bookkeeping choice: Mathlib's native quotient
`Γ ⧸ H` represents the opposite coset convention.  Using the explicit
right relation here makes the summand literally `seed (γ • x)`.
-/
def poincareSummand (H : Subgroup Γ) (seed : X → ℂ)
    (seed_invariant : ∀ h : H, ∀ x : X, seed (h.1 • x) = seed x)
    (x : X) : LeftCoset H → ℂ :=
  Quotient.lift (fun γ : Γ => seed (γ • x)) (by
    intro a b hab
    let h : H := ⟨b * a⁻¹, QuotientGroup.rightRel_apply.mp hab⟩
    calc
      seed (a • x) = seed (h.1 • (a • x)) :=
        (seed_invariant h (a • x)).symm
      _ = seed (b • x) := by
        simp [h, mul_smul])

@[simp]
theorem poincareSummand_mk (H : Subgroup Γ) (seed : X → ℂ)
    (seed_invariant : ∀ h : H, ∀ x : X, seed (h.1 • x) = seed x)
    (x : X) (γ : Γ) :
    poincareSummand H seed seed_invariant x (Quotient.mk'' γ) =
      seed (γ • x) :=
  rfl

/-- The Poincare series of a cusp-invariant seed, indexed without choosing
coset representatives. -/
noncomputable def poincareSeries (H : Subgroup Γ) (seed : X → ℂ)
    (seed_invariant : ∀ h : H, ∀ x : X, seed (h.1 • x) = seed x)
    (x : X) : ℂ :=
  ∑' c : LeftCoset H, poincareSummand H seed seed_invariant x c

/-- Translating the evaluation point on the left is the same as permuting
the left-coset index on the right. -/
theorem poincareSummand_smul (H : Subgroup Γ) (seed : X → ℂ)
    (seed_invariant : ∀ h : H, ∀ x : X, seed (h.1 • x) = seed x)
    (δ : Γ) (x : X) (c : LeftCoset H) :
    poincareSummand H seed seed_invariant (δ • x) c =
      poincareSummand H seed seed_invariant x
        (leftCosetMulRightEquiv H δ c) := by
  induction c using Quotient.inductionOn' with
  | _ γ => simp [poincareSummand, mul_smul]

/-- Honest convergence of the Poincare series is preserved by every group
translate. -/
theorem poincareSummable_smul_iff (H : Subgroup Γ) (seed : X → ℂ)
    (seed_invariant : ∀ h : H, ∀ x : X, seed (h.1 • x) = seed x)
    (δ : Γ) (x : X) :
    Summable (poincareSummand H seed seed_invariant (δ • x)) ↔
      Summable (poincareSummand H seed seed_invariant x) := by
  rw [show poincareSummand H seed seed_invariant (δ • x) =
      (poincareSummand H seed seed_invariant x) ∘
        leftCosetMulRightEquiv H δ by
    funext c
    exact poincareSummand_smul H seed seed_invariant δ x c]
  exact (leftCosetMulRightEquiv H δ).summable_iff

/-- The coset Poincare series is `Γ`-automorphic.  This equality is a pure
reindexing theorem; convergence remains available separately through
`poincareSummable_smul_iff` rather than being hidden by totalized `tsum`. -/
theorem poincareSeries_smul (H : Subgroup Γ) (seed : X → ℂ)
    (seed_invariant : ∀ h : H, ∀ x : X, seed (h.1 • x) = seed x)
    (δ : Γ) (x : X) :
    poincareSeries H seed seed_invariant (δ • x) =
      poincareSeries H seed seed_invariant x := by
  unfold poincareSeries
  rw [show poincareSummand H seed seed_invariant (δ • x) =
      (poincareSummand H seed seed_invariant x) ∘
        leftCosetMulRightEquiv H δ by
    funext c
    exact poincareSummand_smul H seed seed_invariant δ x c]
  exact (leftCosetMulRightEquiv H δ).tsum_eq
    (poincareSummand H seed seed_invariant x)

end AbstractPoincare

section H15RealizationBoundary

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
variable (H : Subgroup Γ)

/-- Proof-carrying analytic realization of the canonical H15 arithmetic seed.

This is deliberately parameterized by the ambient group and homogeneous
space.  Mathlib currently provides `SL(2, ℤ)` acting on the upper half-plane,
but Motohashi's two-variable big-cell transform uses the full
`PSL(2, ℝ)`/Kirillov model, which is not yet available.  A legitimate
inhabitant must therefore specify the actual analytic space rather than use a
formal or trivial group.
-/
structure H15MotohashiPoincareSeedRealizationData
    (A : H15ClassicalEstermannData)
    (S : H15MotohashiSeedAdmissibilityData A) where
  seed : ℕ → X → ℂ
  seed_cusp_invariant : ∀ N : ℕ, ∀ h : H, ∀ x : X,
    seed N (h.1 • x) = seed N x
  poincare_summable : ∀ N : ℕ, ∀ x : X,
    Summable (poincareSummand H (seed N) (seed_cusp_invariant N) x)
  geometricCoefficient : (X → ℂ) →ₗ[ℂ] ℂ
  big_cell_unfolding : ∀ N : ℕ,
    geometricCoefficient
        (poincareSeries H (seed N) (seed_cusp_invariant N)) =
      h15MotohashiArithmeticSeedAggregate N A.η S.c / Real.pi
  seedSeminorm : Seminorm ℂ (X → ℂ)
  seminormMajorant : ℕ → ℝ
  seminormMajorant_nonneg : ∀ N : ℕ, 0 ≤ seminormMajorant N
  uniform_seminorm_bound : ∀ N : ℕ,
    seedSeminorm (seed N) ≤ seminormMajorant N

/-- The realized Poincare family is automorphic, with convergence at every
point recorded in the realization data. -/
theorem H15MotohashiPoincareSeedRealizationData.automorphic
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    (P : H15MotohashiPoincareSeedRealizationData (X := X) H A S)
    (N : ℕ) (δ : Γ) (x : X) :
    poincareSeries H (P.seed N) (P.seed_cusp_invariant N) (δ • x) =
      poincareSeries H (P.seed N) (P.seed_cusp_invariant N) x :=
  poincareSeries_smul H (P.seed N) (P.seed_cusp_invariant N) δ x

/-- A spectral decomposition of the *realized geometric coefficient*.  The
correction identity is kept coupled to the physical completion exactly as in
the existing H15 synthesis interface. -/
structure H15MotohashiPoincareSpectralData
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    (P : H15MotohashiPoincareSeedRealizationData (X := X) H A S) where
  arithmeticMain : ℕ → ℝ
  cuspidalPart : ℕ → ℝ
  continuousRemainder : ℕ → ℝ
  spectral_expansion : ∀ N : ℕ,
    (P.geometricCoefficient
      (poincareSeries H (P.seed N) (P.seed_cusp_invariant N))).im =
        arithmeticMain N + cuspidalPart N + continuousRemainder N
  correction_matching : ∀ N : ℕ,
    estermannInteriorElementaryExpression N + arithmeticMain N +
      (S.physicalCorrection N).im +
      estermannEndpointCompletedExpression
        rationalAnalyticEstermannAtZeroPackage N = 0

/-- Exact passage from a genuine Poincare realization and its spectral
expansion to the canonical Motohashi trace data already used by the H15
closure theorem. -/
noncomputable def H15MotohashiPoincareSpectralData.toAutomorphicTraceData
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    {P : H15MotohashiPoincareSeedRealizationData (X := X) H A S}
    (T : H15MotohashiPoincareSpectralData (X := X) H P) :
    H15MotohashiAutomorphicTraceData S where
  arithmeticMain := T.arithmeticMain
  cuspidalPart := T.cuspidalPart
  continuousRemainder := T.continuousRemainder
  poincare_trace N := by
    rw [← P.big_cell_unfolding N]
    exact T.spectral_expansion N
  correction_matching := T.correction_matching

/-- The RH-strength estimate stated directly for the spectral pieces of a
genuine H15 Poincare realization.  The cuspidal and continuous contributions
remain inside one absolute value. -/
structure H15MotohashiPoincareSignedSpectralEstimate
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    {P : H15MotohashiPoincareSeedRealizationData (X := X) H A S}
    (T : H15MotohashiPoincareSpectralData (X := X) H P) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  signed_spectral_bound : ∀ N : ℕ, 2 ≤ N →
    |T.cuspidalPart N + T.continuousRemainder N| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- A signed estimate for a realized Poincare series is exactly the canonical
seed estimate expected by the completed H15 closure pipeline. -/
noncomputable def H15MotohashiPoincareSignedSpectralEstimate.toAutomorphicEstimate
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    {P : H15MotohashiPoincareSeedRealizationData (X := X) H A S}
    {T : H15MotohashiPoincareSpectralData (X := X) H P}
    (E : H15MotohashiPoincareSignedSpectralEstimate (X := X) H T) :
    H15MotohashiAutomorphicSignedSpectralEstimate
      T.toAutomorphicTraceData where
  C := E.C
  C_pos := E.C_pos
  α := E.α
  α_pos := E.α_pos
  signed_spectral_bound := E.signed_spectral_bound

/-- End-to-end reduction from a convergent Poincare realization, its exact
Motohashi spectral expansion and correction match, and the final signed
spectral decay to the existing Baez--Duarte criterion. -/
theorem baezDuarteCriterion_of_motohashiPoincareSynthesis
    {A : H15ClassicalEstermannData}
    {S : H15MotohashiSeedAdmissibilityData A}
    {P : H15MotohashiPoincareSeedRealizationData (X := X) H A S}
    (T : H15MotohashiPoincareSpectralData (X := X) H P)
    (E : H15MotohashiPoincareSignedSpectralEstimate (X := X) H T) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_motohashiSeedSynthesis A S
    T.toAutomorphicTraceData E.toAutomorphicEstimate

end H15RealizationBoundary

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPoincare
