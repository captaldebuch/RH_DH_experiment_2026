import Mathlib.Analysis.MellinInversion
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannKernelExtraction

/-!
# Route B8.4: exact outer-sign inverse-Mellin expansion

The normalized Estermann dual value is expanded here according to the two
signs of its outer functional equation on `1 < re s`.  Under an explicit
Bochner/Tonelli certificate, the same expansion may be integrated term by
term on a vertical line.  Both signs are retained, including at the paired
H15-kernel level.

Each outer coefficient still contains the two signs of an inner Hurwitz DFT.
Thus the classical same-sign/opposite-sign Kuznetsov channels arise only after a
further four-sign expansion and regrouping.  This file proves the finite DFT
bridge needed for that next step, but does not mislabel the outer split as a
Kuznetsov decomposition.  No Bessel inversion or trace formula is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannInverseMellin

open Complex MeasureTheory ZMod
open scoped Real
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFunctionalEquation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKernelExtraction

/-- A Hurwitz DFT is exactly a scaled congruence `LFunction` with an additive
character.  This is the finite identity needed to expose the inner pair of
functional-equation signs. -/
theorem estermannAdditiveLFunction_eq_cpow_neg_mul_hurwitzDFT
    {q : ℕ} [NeZero q] (s : ℂ) (k : ZMod q) :
    ZMod.LFunction (fun j : ZMod q => ZMod.stdAddChar (-(j * k))) s =
      (q : ℂ) ^ (-s) *
        ZMod.dft (estermannHurwitzCoefficient (q := q) s) k := by
  unfold ZMod.LFunction estermannHurwitzCoefficient
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]

/-- Equivalent unscaled form of the Hurwitz-DFT identity. -/
theorem estermannHurwitzDFT_eq_cpow_mul_additiveLFunction
    {q : ℕ} [NeZero q] (s : ℂ) (k : ZMod q) :
    ZMod.dft (estermannHurwitzCoefficient (q := q) s) k =
      (q : ℂ) ^ s *
        ZMod.LFunction (fun j : ZMod q => ZMod.stdAddChar (-(j * k))) s := by
  have hq : (q : ℂ) ^ s ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  calc
    ZMod.dft (estermannHurwitzCoefficient (q := q) s) k =
        ((q : ℂ) ^ s * (q : ℂ) ^ (-s)) *
          ZMod.dft (estermannHurwitzCoefficient (q := q) s) k := by
      rw [Complex.cpow_neg, mul_inv_cancel₀ hq, one_mul]
    _ = (q : ℂ) ^ s *
        ZMod.LFunction (fun j : ZMod q => ZMod.stdAddChar (-(j * k))) s := by
      rw [estermannAdditiveLFunction_eq_cpow_neg_mul_hurwitzDFT]
      ring

/-- The `s`-dependent outer coefficient exposed as the sum of two additive
`LFunction`s.  Expanding the outer `LFunction` as well therefore produces
four sign pairs, not merely the two outer signs named below. -/
theorem estermannOuterDualCoefficient_eq_two_additiveLFunctions
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (s : ℂ) (k : ZMod q) :
    estermannOuterDualCoefficient a q hcop s k =
      estermannOuterPositiveFactor q s * (q : ℂ) ^ s *
          ZMod.LFunction
            (fun j : ZMod q =>
              ZMod.stdAddChar
                (-(j * estermannInverseFrequency a hcop k))) s +
        estermannOuterNegativeFactor q s * (q : ℂ) ^ s *
          ZMod.LFunction
            (fun j : ZMod q =>
              ZMod.stdAddChar
                (-(j * (-estermannInverseFrequency a hcop k)))) s := by
  unfold estermannOuterDualCoefficient
  rw [estermannHurwitzDFT_eq_cpow_mul_additiveLFunction,
    estermannHurwitzDFT_eq_cpow_mul_additiveLFunction]
  ring

/-- The common gamma and modulus factor in the normalized dual value. -/
noncomputable def estermannDualGammaFactor (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s

/-- The positive-frequency inverse-Mellin prefactor. -/
noncomputable def estermannPositiveMellinFactor (q : ℕ) (s : ℂ) : ℂ :=
  estermannDualGammaFactor q s *
    Complex.exp (Real.pi * Complex.I * s / 2)

/-- The negative-frequency inverse-Mellin prefactor. -/
noncomputable def estermannNegativeMellinFactor (q : ℕ) (s : ℂ) : ℂ :=
  estermannDualGammaFactor q s *
    Complex.exp (-Real.pi * Complex.I * s / 2)

/-- Positive-frequency half of the normalized Estermann dual value. -/
noncomputable def estermannPositiveDualValue
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) (s : ℂ) : ℂ :=
  estermannPositiveMellinFactor q s *
    ZMod.LFunction (estermannOuterDualCoefficient a q hcop s) s

/-- Negative-frequency half of the normalized Estermann dual value. -/
noncomputable def estermannNegativeDualValue
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) (s : ℂ) : ℂ :=
  estermannNegativeMellinFactor q s *
    ZMod.LFunction
      (fun k : ZMod q => estermannOuterDualCoefficient a q hcop s (-k)) s

/-- The functional-equation output has exactly two frequency signs. -/
theorem estermannNormalizedDualValue_eq_positive_add_negative
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) (s : ℂ) :
    estermannNormalizedDualValue a q hcop s =
      estermannPositiveDualValue a q hcop s +
        estermannNegativeDualValue a q hcop s := by
  unfold estermannNormalizedDualValue estermannPositiveDualValue
    estermannNegativeDualValue estermannPositiveMellinFactor
    estermannNegativeMellinFactor estermannDualGammaFactor
  ring

/-- The `n`th positive-frequency Dirichlet term, including its full Mellin
prefactor. -/
noncomputable def estermannPositiveDualDirichletTerm
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (s : ℂ) (n : ℕ) : ℂ :=
  estermannPositiveMellinFactor q s *
    LSeries.term
      (fun n : ℕ => estermannOuterDualCoefficient a q hcop s (n : ZMod q)) s n

/-- The `n`th negative-frequency Dirichlet term, including its full Mellin
prefactor. -/
noncomputable def estermannNegativeDualDirichletTerm
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (s : ℂ) (n : ℕ) : ℂ :=
  estermannNegativeMellinFactor q s *
    LSeries.term
      (fun n : ℕ =>
        estermannOuterDualCoefficient a q hcop s (-(n : ZMod q))) s n

/-- In the absolute-convergence half-plane the positive dual value is its
ordinary Dirichlet `tsum`. -/
theorem estermannPositiveDualValue_eq_tsum
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) {s : ℂ}
    (hs : 1 < s.re) :
    estermannPositiveDualValue a q hcop s =
      ∑' n : ℕ, estermannPositiveDualDirichletTerm a q hcop s n := by
  rw [estermannPositiveDualValue,
    ZMod.LFunction_eq_LSeries _ hs]
  unfold LSeries estermannPositiveDualDirichletTerm
  rw [← tsum_mul_left]

/-- In the absolute-convergence half-plane the negative dual value is its
ordinary Dirichlet `tsum`. -/
theorem estermannNegativeDualValue_eq_tsum
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) {s : ℂ}
    (hs : 1 < s.re) :
    estermannNegativeDualValue a q hcop s =
      ∑' n : ℕ, estermannNegativeDualDirichletTerm a q hcop s n := by
  rw [estermannNegativeDualValue,
    ZMod.LFunction_eq_LSeries _ hs]
  unfold LSeries estermannNegativeDualDirichletTerm
  rw [← tsum_mul_left]

/-- Exact pointwise two-outer-sign Dirichlet expansion. -/
theorem estermannNormalizedDualValue_eq_two_outer_tsum
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) {s : ℂ}
    (hs : 1 < s.re) :
    estermannNormalizedDualValue a q hcop s =
      (∑' n : ℕ, estermannPositiveDualDirichletTerm a q hcop s n) +
        ∑' n : ℕ, estermannNegativeDualDirichletTerm a q hcop s n := by
  rw [estermannNormalizedDualValue_eq_positive_add_negative,
    estermannPositiveDualValue_eq_tsum _ _ hcop hs,
    estermannNegativeDualValue_eq_tsum _ _ hcop hs]

/-- The positive-frequency term after inserting the vertical-line weight. -/
noncomputable def estermannPositiveInverseMellinIntegrand
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (c : ℝ) (W : ℂ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  W (estermannVerticalPoint c t) *
    estermannPositiveDualDirichletTerm a q hcop
      (estermannVerticalPoint c t) n

/-- The negative-frequency term after inserting the vertical-line weight. -/
noncomputable def estermannNegativeInverseMellinIntegrand
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (c : ℝ) (W : ℂ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  W (estermannVerticalPoint c t) *
    estermannNegativeDualDirichletTerm a q hcop
      (estermannVerticalPoint c t) n

/-- Mathlib's inverse Mellin transform is exactly the vertical Mellin--Barnes
integral with the conventional factor `1 / (2 * π)`.  This identity is
purely definitional and needs no convergence hypothesis. -/
theorem verticalIntegral_cpow_neg_eq_two_pi_mul_mellinInv
    (c : ℝ) (F : ℂ → ℂ) (x : ℝ) :
    (∫ t : ℝ,
        (x : ℂ) ^ (-estermannVerticalPoint c t) *
          F (estermannVerticalPoint c t)) =
      (2 * Real.pi : ℂ) * mellinInv c F x := by
  unfold mellinInv estermannVerticalPoint
  simp only [Complex.real_smul, smul_eq_mul]
  have hcomm :
      (∫ t : ℝ, (x : ℂ) ^ (-(c + t * I)) * F (c + t * I)) =
        ∫ t : ℝ, (x : ℂ) ^ (-(c + I * t)) * F (c + I * t) := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [mul_comm (t : ℂ) I]
  rw [hcomm]
  have hfac :
      (2 * Real.pi : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ)) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  calc
    (∫ t : ℝ, (x : ℂ) ^ (-(c + I * t)) * F (c + I * t)) =
        (∫ t : ℝ, (x : ℂ) ^ (-(c + I * t)) * F (c + I * t)) * 1 := by
          rw [mul_one]
    _ = (∫ t : ℝ, (x : ℂ) ^ (-(c + I * t)) * F (c + I * t)) *
        ((2 * Real.pi : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ))) := by
          rw [hfac]
    _ = _ := by ring

/-- The positive outer-sign Mellin--Barnes profile at frequency `n`. -/
noncomputable def estermannPositiveMellinBarnesProfile
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (W : ℂ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  W s * estermannPositiveMellinFactor q s *
    estermannOuterDualCoefficient a q hcop s (n : ZMod q)

/-- The negative outer-sign Mellin--Barnes profile at frequency `n`. -/
noncomputable def estermannNegativeMellinBarnesProfile
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (W : ℂ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  W s * estermannNegativeMellinFactor q s *
    estermannOuterDualCoefficient a q hcop s (-(n : ZMod q))

/-- Every nonzero positive outer-frequency term is literally a Mathlib
inverse Mellin transform of its Mellin--Barnes profile. -/
theorem integral_positiveInverseMellinIntegrand_eq_mellinInv
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (c : ℝ) (W : ℂ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      estermannPositiveInverseMellinIntegrand a q hcop c W n t) =
      (2 * Real.pi : ℂ) *
        mellinInv c (estermannPositiveMellinBarnesProfile a q hcop W n) n := by
  rw [← verticalIntegral_cpow_neg_eq_two_pi_mul_mellinInv]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold estermannPositiveInverseMellinIntegrand
    estermannPositiveDualDirichletTerm
    estermannPositiveMellinBarnesProfile
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  have hcast : (((n : ℝ) : ℂ)) = (n : ℂ) := by norm_cast
  rw [hcast]
  ring

/-- Every nonzero negative outer-frequency term is literally a Mathlib
inverse Mellin transform of its Mellin--Barnes profile. -/
theorem integral_negativeInverseMellinIntegrand_eq_mellinInv
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (c : ℝ) (W : ℂ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      estermannNegativeInverseMellinIntegrand a q hcop c W n t) =
      (2 * Real.pi : ℂ) *
        mellinInv c (estermannNegativeMellinBarnesProfile a q hcop W n) n := by
  rw [← verticalIntegral_cpow_neg_eq_two_pi_mul_mellinInv]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold estermannNegativeInverseMellinIntegrand
    estermannNegativeDualDirichletTerm
    estermannNegativeMellinBarnesProfile
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  have hcast : (((n : ℝ) : ℂ)) = (n : ℂ) := by norm_cast
  rw [hcast]
  ring

/-- The positive inverse-Mellin series, with every term integrated on the
vertical line. -/
noncomputable def estermannPositiveInverseMellinSeries
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (c : ℝ) (W : ℂ → ℂ) : ℂ :=
  ∑' n : ℕ, ∫ t : ℝ,
    estermannPositiveInverseMellinIntegrand a q hcop c W n t

/-- The negative inverse-Mellin series, with every term integrated on the
vertical line. -/
noncomputable def estermannNegativeInverseMellinSeries
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (c : ℝ) (W : ℂ → ℂ) : ℂ :=
  ∑' n : ℕ, ∫ t : ℝ,
    estermannNegativeInverseMellinIntegrand a q hcop c W n t

/-- Explicit hypotheses needed to exchange the two Dirichlet series with
the vertical Bochner integral.  These are analytic domination conditions,
not hidden conclusions of the functional equation. -/
structure EstermannInverseMellinExchangeData
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (c : ℝ) (W : ℂ → ℂ) : Prop where
  positive_integrable : ∀ n : ℕ,
    Integrable (estermannPositiveInverseMellinIntegrand a q hcop c W n)
  negative_integrable : ∀ n : ℕ,
    Integrable (estermannNegativeInverseMellinIntegrand a q hcop c W n)
  positive_summable_integral_norm : Summable fun n : ℕ ↦
    ∫ t : ℝ, ‖estermannPositiveInverseMellinIntegrand a q hcop c W n t‖
  negative_summable_integral_norm : Summable fun n : ℕ ↦
    ∫ t : ℝ, ‖estermannNegativeInverseMellinIntegrand a q hcop c W n t‖
  positive_sum_integrable : Integrable fun t : ℝ ↦
    ∑' n : ℕ, estermannPositiveInverseMellinIntegrand a q hcop c W n t
  negative_sum_integrable : Integrable fun t : ℝ ↦
    ∑' n : ℕ, estermannNegativeInverseMellinIntegrand a q hcop c W n t

/-- Exact inverse-Mellin expansion of one normalized Estermann vertical
integral.  The strict inequality `1 < c` is precisely the half-plane in
which Mathlib identifies the congruence `LFunction` with its Dirichlet
series. -/
theorem estermannDualVerticalIntegral_eq_inverseMellinSeries
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (c : ℝ) (hc : 1 < c) (W : ℂ → ℂ)
    (H : EstermannInverseMellinExchangeData a q hcop c W) :
    estermannDualVerticalIntegral a q hcop c W =
      estermannPositiveInverseMellinSeries a q hcop c W +
        estermannNegativeInverseMellinSeries a q hcop c W := by
  unfold estermannDualVerticalIntegral
  rw [show (∫ t : ℝ, W (estermannVerticalPoint c t) *
          estermannNormalizedDualValue a q hcop (estermannVerticalPoint c t)) =
        ∫ t : ℝ,
          (∑' n : ℕ,
              estermannPositiveInverseMellinIntegrand a q hcop c W n t) +
            ∑' n : ℕ,
              estermannNegativeInverseMellinIntegrand a q hcop c W n t by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [estermannNormalizedDualValue_eq_two_outer_tsum a q hcop
      (by simpa using hc)]
    unfold estermannPositiveInverseMellinIntegrand
      estermannNegativeInverseMellinIntegrand
    rw [mul_add, tsum_mul_left, tsum_mul_left]]
  rw [integral_add H.positive_sum_integrable H.negative_sum_integrable]
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
      H.positive_integrable H.positive_summable_integral_norm]
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
      H.negative_integrable H.negative_summable_integral_norm]
  rfl

/-- The exchange certificates for both orientations of a coprime H15 pair. -/
structure EstermannPairedInverseMellinExchangeData
    (W : ℂ → ℂ) (c : ℝ)
    (a b : ℕ) (hcop : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : Prop where
  forward : by
    letI : NeZero b := ⟨by omega⟩
    exact EstermannInverseMellinExchangeData
      (inverseResidueNumerator a b hcop) b
      (inverseResidueNumerator_coprime a b hcop) c W
  backward : by
    letI : NeZero a := ⟨by omega⟩
    exact EstermannInverseMellinExchangeData
      (inverseResidueNumerator b a hcop.symm) a
      (inverseResidueNumerator_coprime b a hcop.symm) c W

/-- The positive-frequency inverse-Mellin contribution of both orientations
of a coprime pair. -/
noncomputable def estermannPairedPositiveInverseMellinKernel
    (W : ℂ → ℂ) (c : ℝ)
    (a b : ℕ) (hcop : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : ℂ := by
  letI : NeZero a := ⟨by omega⟩
  letI : NeZero b := ⟨by omega⟩
  exact
    estermannPositiveInverseMellinSeries
        (inverseResidueNumerator a b hcop) b
        (inverseResidueNumerator_coprime a b hcop) c W +
      estermannPositiveInverseMellinSeries
        (inverseResidueNumerator b a hcop.symm) a
        (inverseResidueNumerator_coprime b a hcop.symm) c W

/-- The negative-frequency inverse-Mellin contribution of both orientations
of a coprime pair. -/
noncomputable def estermannPairedNegativeInverseMellinKernel
    (W : ℂ → ℂ) (c : ℝ)
    (a b : ℕ) (hcop : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : ℂ := by
  letI : NeZero a := ⟨by omega⟩
  letI : NeZero b := ⟨by omega⟩
  exact
    estermannNegativeInverseMellinSeries
        (inverseResidueNumerator a b hcop) b
        (inverseResidueNumerator_coprime a b hcop) c W +
      estermannNegativeInverseMellinSeries
        (inverseResidueNumerator b a hcop.symm) a
        (inverseResidueNumerator_coprime b a hcop.symm) c W

/-- Exact two-outer-sign inverse-Mellin expansion of the paired dual kernel. -/
theorem estermannPairedDualKernel_eq_outerInverseMellin
    (W : ℂ → ℂ) (c : ℝ) (hc : 1 < c)
    (a b : ℕ) (hcop : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (H : EstermannPairedInverseMellinExchangeData W c a b hcop ha hb) :
    estermannPairedDualKernel W c a b hcop ha hb =
      estermannPairedPositiveInverseMellinKernel W c a b hcop ha hb +
        estermannPairedNegativeInverseMellinKernel W c a b hcop ha hb := by
  letI : NeZero a := ⟨by omega⟩
  letI : NeZero b := ⟨by omega⟩
  unfold estermannPairedDualKernel
    estermannPairedPositiveInverseMellinKernel
    estermannPairedNegativeInverseMellinKernel
  rw [estermannDualVerticalIntegral_eq_inverseMellinSeries
      _ _ _ c hc W H.forward,
    estermannDualVerticalIntegral_eq_inverseMellinSeries
      _ _ _ c hc W H.backward]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannInverseMellin
