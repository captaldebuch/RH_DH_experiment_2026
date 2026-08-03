import RiemannHypothesis.Criteria.NymanBeurling.QuadraticInteraction

/-!
H15 fractional-tail interface.

The finite cutoff Möbius vector is written in reciprocal coordinates.  This
file records the exact one-variable tail exposed by that change of variables.
It does not assume or prove the quantitative tail estimate; that estimate is
the remaining analytic input.  The definitions are chosen so that the
analytic field is strictly more informative than the old opaque quadratic
correlation field.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open scoped MeasureTheory

/-- The finite Möbius sum after the reciprocal change of variables `t = 1/x`.
    The minus sign is omitted so that the limiting value on `t ≥ 1` is `-1`. -/
noncomputable def cutoffMobiusTransformedSum (N : ℕ) (t : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius h : ℤ) : ℝ) * cutoffWeight N h *
      Int.fract (t / (h : ℝ))

/-- The defect from the infinite Möbius inversion identity on the reciprocal
    side.  The separate normalization `∑ μ(h)/h = 0` is needed to identify the
    limiting constant, but is not built into this definition. -/
noncomputable def cutoffMobiusReciprocalTail (N : ℕ) (t : ℝ) : ℝ :=
  1 + cutoffMobiusTransformedSum N t

/-- The weighted reciprocal-tail energy on the interval `t > 1`. -/
noncomputable def cutoffMobiusReciprocalTailEnergy (N : ℕ) : ℝ :=
  ∫ t in Set.Ioi (1 : ℝ),
    cutoffMobiusReciprocalTail N t ^ 2 * (1 / t ^ 2)

/-- The exact contribution of the region `x > 1`, where every fractional part
    has already entered its linear regime. -/
noncomputable def cutoffMobiusInverseIndexEnergy (N : ℕ) : ℝ :=
  (∑ h ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h / (h : ℝ)) ^ 2

/-- The finite original-coordinate Möbius sum, used only for the exact
    pointwise reciprocal-coordinate identity below. -/
noncomputable def cutoffMobiusOriginalSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * Int.fract (1 / ((h : ℝ) * x))

theorem cutoffMobiusOriginalSum_eq_neg_transformed_inv (N : ℕ) (x : ℝ) :
    cutoffMobiusOriginalSum N x =
      -cutoffMobiusTransformedSum N (1 / x) := by
  unfold cutoffMobiusOriginalSum cutoffMobiusTransformedSum cutoffMobiusCoeff
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  have hcast : (h : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hh).1)
  field_simp

/-!
The next package is the recommended H15 gate.  Its first field is a pure
change-of-variables identity; its second field is the actual analytic estimate
for the one-variable reciprocal tail.  Once both are supplied, the existing
`QuadraticInteractionNormResidual` interface follows mechanically.
-/
structure CutoffMobiusFractionalTailPackage where
  C_tail : ℝ
  C_tail_nonneg : 0 ≤ C_tail
  norm_split :
    ∀ N : ℕ,
      cutoffMobiusDefectEnergy N =
        cutoffMobiusReciprocalTailEnergy N +
          cutoffMobiusInverseIndexEnergy N
  tail_package_bound :
    ∀ N : ℕ,
      |explicitQuadraticLogGammaComponent N| +
          |cutoffMobiusReciprocalTailEnergy N +
              cutoffMobiusInverseIndexEnergy N -
              explicitQuadraticLogGammaComponent N| ≤
        C_tail / Real.log (N + 2 : ℝ)

/- The package bridge is deliberately mechanical: no analytic estimate is
   hidden in this theorem. -/
noncomputable def quadraticInteractionNormResidual_of_fractionalTailPackage
    (H : CutoffMobiusFractionalTailPackage) :
    QuadraticInteractionNormResidual := by
  refine
    { C_norm := H.C_tail
      C_norm_nonneg := H.C_tail_nonneg
      norm_loggamma_package_bound := ?_ }
  intro N
  have h := H.tail_package_bound N
  rw [← H.norm_split N] at h
  exact h

end RH.Criteria.NymanBeurling.QuadraticInteraction
