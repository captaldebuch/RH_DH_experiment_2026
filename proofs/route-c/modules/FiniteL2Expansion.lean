import Mathlib

/-!
# Finite quadratic expansions in real L²

This file isolates the finite algebra used by the Báez-Duarte certificate path.
The only analytic hypotheses are integrability of the pairwise products.
-/

open scoped BigOperators

namespace RH.Criteria.NymanBeurling

open MeasureTheory

/-- Expand the squared error of a finite real linear combination under an integral.
    This is the reusable finite-dimensional algebra behind Gram-matrix energy formulas. -/
theorem finite_L2_norm_quadratic_expansion
    {X : Type*} [MeasurableSpace X]
    {ι : Type*} [Fintype ι]
    (μ : Measure X) (f : X → ℝ) (g : ι → X → ℝ) (c : ι → ℝ)
    (hf : Integrable (fun x => f x * f x) μ)
    (hfg : ∀ i, Integrable (fun x => f x * g i x) μ)
    (hgg : ∀ i j, Integrable (fun x => g i x * g j x) μ) :
    ∫ x, (f x - ∑ i, c i * g i x) ^ 2 ∂μ =
      (∑ i, ∑ j, c i * c j * ∫ x, g i x * g j x ∂μ)
      - 2 * ∑ i, c i * ∫ x, f x * g i x ∂μ
      + ∫ x, f x * f x ∂μ := by
  have hcross : Integrable (fun x => ∑ i, (2 * c i) * (f x * g i x)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hfg i).const_mul (2 * c i))
  have hquad : Integrable
      (fun x => ∑ i, ∑ j, (c i * c j) * (g i x * g j x)) μ :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => (hgg i j).const_mul (c i * c j)))
  rw [show (fun x => (f x - ∑ i, c i * g i x) ^ 2) =
      (fun x => f x * f x - ∑ i, (2 * c i) * (f x * g i x) +
        ∑ i, ∑ j, (c i * c j) * (g i x * g j x)) by
    funext x
    have hsquare : (∑ i, c i * g i x) ^ 2 =
        ∑ i, ∑ j, (c i * c j) * (g i x * g j x) := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    calc
      (f x - ∑ i, c i * g i x) ^ 2 =
          f x * f x - 2 * f x * (∑ i, c i * g i x) +
            (∑ i, c i * g i x) ^ 2 := by ring
      _ = f x * f x - ∑ i, (2 * c i) * (f x * g i x) +
            ∑ i, ∑ j, (c i * c j) * (g i x * g j x) := by
        rw [hsquare, Finset.mul_sum]
        ring_nf]
  have hadd := integral_add (hf.sub hcross) hquad
  simp only [Pi.sub_apply] at hadd
  rw [hadd]
  have hsub := integral_sub hf hcross
  rw [hsub]
  simp_rw [integral_finsetSum _ (fun i _ => (hfg i).const_mul (2 * c i))]
  simp_rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hgg i j).const_mul (c i * c j)))]
  simp_rw [integral_finsetSum _ (fun j _ => (hgg _ j).const_mul (c _ * c j))]
  simp only [integral_const_mul]
  rw [Finset.mul_sum]
  ring_nf

end RH.Criteria.NymanBeurling
