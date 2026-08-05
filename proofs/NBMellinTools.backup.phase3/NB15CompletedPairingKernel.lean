/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15CorrectionPreservingRectangle
import NBMellinTools.NB12BBLSH15SignedRightLine

/-!
# The quadratic type required by a completed H15 contour bridge

A one-variable meromorphic function is acted on linearly by contour
deformation.  The certified NB8 energy, however, is the integral of a squared
norm.  Squaring a complex function with an absolute value does not preserve
holomorphy.  The correct contour-level object must therefore be a
sesquilinear pairing represented by a function of two complex variables.

This file constructs the literal pairing kernels on both sides and proves
their diagonal identities.  It also proves a stop test: two prescribed
boundary functions always admit a naive affine interpolation, so endpoint
equalities alone contain no analytic information and cannot close H15.

No two-variable contour deformation or decay estimate is asserted here.
-/

open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB15

open Complex MeasureTheory
open NBMellinTools.NB12

/-! ## A boundary-only interface is vacuous -/

/-- Affine interpolation between arbitrary boundary data at `sigma=1/2` and
`sigma=3/2`.  This deliberately has no holomorphy claim. -/
noncomputable def affineBoundaryInterpolator
    (left right : ℝ → ℂ) (σ t : ℝ) : ℂ :=
  (((3 / 2 : ℝ) - σ : ℝ) : ℂ) * left t +
    ((σ - (1 / 2 : ℝ) : ℝ) : ℂ) * right t

theorem affineBoundaryInterpolator_half
    (left right : ℝ → ℂ) (t : ℝ) :
    affineBoundaryInterpolator left right (1 / 2) t = left t := by
  norm_num [affineBoundaryInterpolator]

theorem affineBoundaryInterpolator_threeHalf
    (left right : ℝ → ℂ) (t : ℝ) :
    affineBoundaryInterpolator left right (3 / 2) t = right t := by
  norm_num [affineBoundaryInterpolator]

/-- The two boundary equalities proposed in the WP4 note can be satisfied
for the literal H15 functions without using zeta, Estermann continuation, or
residue calculus.  Hence those equalities alone are not a valid success
criterion for a completed integrand. -/
noncomputable def h15NaiveBoundaryInterpolator
    (n : ℕ) (σ t : ℝ) : ℂ :=
  affineBoundaryInterpolator
    (certifiedCriticalLineNumerator n)
    (h15VerticalAggregate n (3 / 2)) σ t

theorem h15NaiveBoundaryInterpolator_half (n : ℕ) (t : ℝ) :
    h15NaiveBoundaryInterpolator n (1 / 2) t =
      certifiedCriticalLineNumerator n t := by
  exact affineBoundaryInterpolator_half _ _ t

theorem h15NaiveBoundaryInterpolator_threeHalf (n : ℕ) (t : ℝ) :
    h15NaiveBoundaryInterpolator n (3 / 2) t =
      h15ActiveContourAggregate n
        (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  exact affineBoundaryInterpolator_threeHalf _ _ t

/-! ## The literal physical Mellin numerator -/

/-- The certified numerator away from the critical-line parameterization.
It is totalized at `s=0`, as are the existing Mellin definitions. -/
noncomputable def certifiedMellinNumerator (n : ℕ) (s : ℂ) : ℂ :=
  (1 - riemannZeta s * certifiedDirichletPolynomial n s) / s

theorem certifiedMellinNumerator_criticalLine (n : ℕ) (t : ℝ) :
    certifiedMellinNumerator n (certifiedCriticalLinePoint t) =
      certifiedCriticalLineNumerator n t := by
  rfl

/-! ## Holomorphic-style two-variable pairing -/

/-- Schwarz-reflected value.  If `F` is holomorphic on a conjugation-stable
domain, this is again holomorphic there; no such analytic claim is needed for
the algebraic identities below. -/
noncomputable def schwarzReflect (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  conj (F (conj z))

/-- The separately complex-variable pairing kernel associated with `F`. -/
noncomputable def completedPairingKernel
    (F : ℂ → ℂ) (z w : ℂ) : ℂ :=
  schwarzReflect F z * F w

/-- On the conjugate diagonal, the pairing kernel is exactly the squared
norm. -/
theorem completedPairingKernel_conj_diagonal
    (F : ℂ → ℂ) (s : ℂ) :
    completedPairingKernel F (conj s) s =
      (Complex.normSq (F s) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp [completedPairingKernel, schwarzReflect]

/-- The genuine two-variable physical pairing kernel. -/
noncomputable def certifiedMellinPairingKernel
    (n : ℕ) (z w : ℂ) : ℂ :=
  completedPairingKernel (certifiedMellinNumerator n) z w

theorem certifiedMellinPairingKernel_criticalDiagonal
    (n : ℕ) (t : ℝ) :
    certifiedMellinPairingKernel n
        (conj (certifiedCriticalLinePoint t))
        (certifiedCriticalLinePoint t) =
      (Complex.normSq (certifiedCriticalLineNumerator n t) : ℂ) := by
  rw [certifiedMellinPairingKernel,
    completedPairingKernel_conj_diagonal,
    certifiedMellinNumerator_criticalLine]

/-- The already certified critical-line energy is exactly the real diagonal
integral of the two-variable physical pairing kernel. -/
theorem certifiedCriticalLineEnergy_eq_pairingDiagonalIntegral
    (n : ℕ) :
    certifiedCriticalLineEnergy n =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        (certifiedMellinPairingKernel n
          (conj (certifiedCriticalLinePoint t))
          (certifiedCriticalLinePoint t)).re := by
  unfold certifiedCriticalLineEnergy
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [certifiedMellinPairingKernel_criticalDiagonal]
  simpa using
    (Complex.normSq_eq_norm_sq (certifiedCriticalLineNumerator n t)).symm

/-! ## The literal Estermann contour pairing -/

/-- The genuine two-variable pairing kernel of the active H15 Estermann
aggregate. -/
noncomputable def h15ActiveContourPairingKernel
    (n : ℕ) (z w : ℂ) : ℂ :=
  completedPairingKernel (h15ActiveContourAggregate n) z w

theorem h15ActiveContourPairingKernel_conj_diagonal
    (n : ℕ) (s : ℂ) :
    h15ActiveContourPairingKernel n (conj s) s =
      (Complex.normSq (h15ActiveContourAggregate n s) : ℂ) := by
  exact completedPairingKernel_conj_diagonal _ s

/-- On the right vertical line, the two-variable contour kernel gives the
literal squared norm of the complete signed H15 aggregate. -/
theorem h15ActiveContourPairingKernel_threeHalfDiagonal
    (n : ℕ) (t : ℝ) :
    h15ActiveContourPairingKernel n
        (conj (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
        (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      (Complex.normSq (h15VerticalAggregate n (3 / 2) t) : ℂ) := by
  exact h15ActiveContourPairingKernel_conj_diagonal _ _

end NBMellinTools.NB15
