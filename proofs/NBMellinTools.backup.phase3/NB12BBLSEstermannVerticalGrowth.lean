/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSEstermannVerticalKernel

/-!
# NB12n: scalar-Hurwitz reduction of central Estermann growth

This file applies the triangle inequality to the exact finite double-Hurwitz
continuation.  It proves that a modulus-explicit polynomial bound for scalar
Hurwitz zeta on `Re(s)=1/2` supplies the corresponding polynomial bound for
both inverse Estermann twists.

The modulus exponent is retained explicitly.  No modulus-independent bound
is asserted.  The remaining classical input is reduced to a scalar Hurwitz
vertical-growth package at the end of the file.
-/

open scoped BigOperators Topology LSeries.notation
open Complex MeasureTheory Set

namespace NBMellinTools.NB12

/-! ## Numerator-free finite Hurwitz majorant -/

/-- Sum of the scalar Hurwitz norms over one complete residue system. -/
noncomputable def bblsHurwitzResidueNormSum
    (q : ℕ) [NeZero q] (s : ℂ) : ℝ :=
  ∑ r : ZMod q, ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r) s‖

/-- Applying the triangle inequality at both finite Hurwitz levels removes
all dependence on the additive numerator. -/
theorem norm_bblsEstermannHurwitzContinuation_le
    (a q : ℕ) [NeZero q] (s : ℂ) :
    ‖bblsEstermannHurwitzContinuation a q s‖ ≤
      ‖(q : ℂ) ^ (-s)‖ ^ 2 * bblsHurwitzResidueNormSum q s ^ 2 := by
  rw [bblsEstermannHurwitzContinuation_eq_finiteSum]
  unfold bblsEstermannHurwitzFiniteSum bblsHurwitzResidueNormSum
  rw [norm_mul]
  calc
    ‖(q : ℂ) ^ (-s)‖ *
        ‖∑ j : ZMod q,
          ((q : ℂ) ^ (-s) *
              ∑ k : ZMod q,
                bblsEstermannResiduePhase a j k *
                  HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) *
            HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s‖ ≤
      ‖(q : ℂ) ^ (-s)‖ *
        ∑ j : ZMod q,
          ‖((q : ℂ) ^ (-s) *
                ∑ k : ZMod q,
                  bblsEstermannResiduePhase a j k *
                    HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) *
              HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖(q : ℂ) ^ (-s)‖ *
        ∑ j : ZMod q,
          (‖(q : ℂ) ^ (-s)‖ *
              ∑ k : ZMod q,
                ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s‖) *
            ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hinner := norm_sum_le Finset.univ
        (fun k : ZMod q =>
          bblsEstermannResiduePhase a j k *
            HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s)
      simpa [norm_mul, bblsEstermannResiduePhase] using hinner
    _ = ‖(q : ℂ) ^ (-s)‖ ^ 2 *
        (∑ r : ZMod q,
          ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r) s‖) ^ 2 := by
      rw [← Finset.mul_sum]
      ring

/-! ## The exact scalar input -/

/-- Modulus-explicit polynomial growth for scalar rational Hurwitz zeta on
the central line.  This is the classical analytic theorem still missing
from the active Mathlib API. -/
structure BBLSHurwitzCentralPolynomialGrowth where
  exponent : ℕ
  qExponent : ℕ
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (t : ℝ),
    ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
        (bblsEstermannCentralPoint t)‖ ≤
      constant * (q : ℝ) ^ qExponent * (1 + |t|) ^ exponent

/-- The scalar pointwise majorant named for the finite-sum estimates. -/
noncomputable def BBLSHurwitzCentralPolynomialGrowth.pointMajorant
    (H : BBLSHurwitzCentralPolynomialGrowth) (q : ℕ) (t : ℝ) : ℝ :=
  H.constant * (q : ℝ) ^ H.qExponent * (1 + |t|) ^ H.exponent

theorem BBLSHurwitzCentralPolynomialGrowth.pointMajorant_nonneg
    (H : BBLSHurwitzCentralPolynomialGrowth) (q : ℕ) (t : ℝ) :
    0 ≤ H.pointMajorant q t := by
  unfold pointMajorant
  exact mul_nonneg
    (mul_nonneg H.constant_nonneg (pow_nonneg (Nat.cast_nonneg q) _))
    (pow_nonneg (by positivity) _)

/-- Summing the scalar estimate over all residue classes costs one factor
of the modulus. -/
theorem BBLSHurwitzCentralPolynomialGrowth.residueNormSum_le
    (H : BBLSHurwitzCentralPolynomialGrowth)
    (q : ℕ) [NeZero q] (t : ℝ) :
    bblsHurwitzResidueNormSum q (bblsEstermannCentralPoint t) ≤
      (q : ℝ) * H.pointMajorant q t := by
  unfold bblsHurwitzResidueNormSum
  calc
    (∑ r : ZMod q,
        ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
          (bblsEstermannCentralPoint t)‖) ≤
      ∑ _r : ZMod q, H.pointMajorant q t := by
        apply Finset.sum_le_sum
        intro r _
        exact H.bound q r t
    _ = (q : ℝ) * H.pointMajorant q t := by
      simp [nsmul_eq_mul]

/-- The normalizing complex power has norm at most one on the central line.
This uses only positivity of the modulus. -/
theorem norm_q_cpow_neg_bblsEstermannCentralPoint_le_one
    (q : ℕ) [NeZero q] (t : ℝ) :
    ‖(q : ℂ) ^ (-bblsEstermannCentralPoint t)‖ ≤ 1 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hq]
  have hre : (-bblsEstermannCentralPoint t).re = (-1 / 2 : ℝ) := by
    norm_num [bblsEstermannCentralPoint]
  rw [hre]
  exact Real.rpow_le_one_of_one_le_of_nonpos hqOne (by norm_num)

/-- Scalar Hurwitz growth implies a numerator-uniform Estermann bound.  The
displayed `q^(2*beta+2)` is deliberately conservative: it retains both
finite residue sums and only uses `norm(q^(-s)) <= 1`. -/
theorem BBLSHurwitzCentralPolynomialGrowth.estermann_norm_le
    (H : BBLSHurwitzCentralPolynomialGrowth)
    (a q : ℕ) [NeZero q] (t : ℝ) :
    ‖bblsEstermannHurwitzContinuation a q
        (bblsEstermannCentralPoint t)‖ ≤
      H.constant ^ 2 * (q : ℝ) ^ (2 * H.qExponent + 2) *
        (1 + |t|) ^ (2 * H.exponent) := by
  have hsum := H.residueNormSum_le q t
  have hsumNonneg :
      0 ≤ bblsHurwitzResidueNormSum q
        (bblsEstermannCentralPoint t) := by
    unfold bblsHurwitzResidueNormSum
    positivity
  have hqpow := norm_q_cpow_neg_bblsEstermannCentralPoint_le_one q t
  have hqpowNonneg :
      0 ≤ ‖(q : ℂ) ^ (-bblsEstermannCentralPoint t)‖ := norm_nonneg _
  calc
    ‖bblsEstermannHurwitzContinuation a q
        (bblsEstermannCentralPoint t)‖ ≤
      ‖(q : ℂ) ^ (-bblsEstermannCentralPoint t)‖ ^ 2 *
        bblsHurwitzResidueNormSum q
          (bblsEstermannCentralPoint t) ^ 2 :=
      norm_bblsEstermannHurwitzContinuation_le a q _
    _ ≤ 1 ^ 2 * ((q : ℝ) * H.pointMajorant q t) ^ 2 := by
      gcongr
    _ = H.constant ^ 2 * (q : ℝ) ^ (2 * H.qExponent + 2) *
        (1 + |t|) ^ (2 * H.exponent) := by
      unfold BBLSHurwitzCentralPolynomialGrowth.pointMajorant
      rw [show 2 * H.qExponent + 2 = 2 + H.qExponent * 2 by omega,
        pow_add, pow_mul]
      rw [show 2 * H.exponent = H.exponent * 2 by omega, pow_mul]
      ring

/-- The exact constructor reducing both inverse twists to the single scalar
Hurwitz theorem. -/
noncomputable def BBLSHurwitzCentralPolynomialGrowth.toEstermann
    (H : BBLSHurwitzCentralPolynomialGrowth) :
    BBLSEstermannCentralPolynomialGrowth where
  exponent := 2 * H.exponent
  qExponent := 2 * H.qExponent + 2
  constant := 2 * H.constant ^ 2
  constant_nonneg := by positivity
  bound a q _ haq t := by
    have hpos := H.estermann_norm_le
      (bblsEstermannInverseNumerator a q haq) q t
    have hneg := H.estermann_norm_le
      (bblsEstermannNegativeInverseNumerator a q haq) q t
    calc
      _ ≤ (H.constant ^ 2 * (q : ℝ) ^ (2 * H.qExponent + 2) *
          (1 + |t|) ^ (2 * H.exponent)) +
        (H.constant ^ 2 * (q : ℝ) ^ (2 * H.qExponent + 2) *
          (1 + |t|) ^ (2 * H.exponent)) := add_le_add hpos hneg
      _ = (2 * H.constant ^ 2) *
          (q : ℝ) ^ (2 * H.qExponent + 2) *
          (1 + |t|) ^ (2 * H.exponent) := by ring

/-! ## Absorption by the intrinsic Gamma decay -/

/-- A polynomial times a two-sided exponential. -/
noncomputable def bblsPolynomialExponentialMajorant
    (degree : ℕ) (rate : ℝ) (t : ℝ) : ℝ :=
  (1 + |t|) ^ degree * Real.exp (-rate * |t|)

/-- Every polynomial is integrable against a positive two-sided
exponential. -/
theorem integrable_bblsPolynomialExponentialMajorant
    (degree : ℕ) {rate : ℝ} (hrate : 0 < rate) :
    Integrable (bblsPolynomialExponentialMajorant degree rate) := by
  have hmono : ∀ k : ℕ, IntegrableOn
      (fun x : ℝ => x ^ k * Real.exp (-rate * x)) (Ioi 0) := by
    intro k
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (k : ℝ)) (b := rate)
      (by have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith)
      (by norm_num) hrate
    convert h using 1
    ext x
    simp only [Real.rpow_natCast, Real.rpow_one]
  have hpos : IntegrableOn
      (fun x : ℝ => (1 + x) ^ degree * Real.exp (-rate * x))
      (Ioi 0) := by
    rw [show (fun x : ℝ => (1 + x) ^ degree * Real.exp (-rate * x)) =
        fun x : ℝ =>
          ∑ k ∈ Finset.range (degree + 1),
            ((Nat.choose degree k : ℕ) : ℝ) *
              (x ^ (degree - k) * Real.exp (-rate * x)) by
      funext x
      rw [add_pow]
      simp only [one_pow, one_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring]
    exact integrable_finsetSum (μ := volume.restrict (Ioi 0)) _ fun k _ =>
      (hmono (degree - k)).const_mul _
  have hposAbs : IntegrableOn
      (bblsPolynomialExponentialMajorant degree rate) (Ioi 0) := by
    refine hpos.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    simp [bblsPolynomialExponentialMajorant, abs_of_pos hx']
  have hnegAbs : IntegrableOn
      (bblsPolynomialExponentialMajorant degree rate) (Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def, bblsPolynomialExponentialMajorant,
      abs_neg, neg_preimage, neg_Iio, neg_zero] using hposAbs
  rw [← integrableOn_univ, ← Iio_union_Ici, integrableOn_union]
  refine ⟨hnegAbs, ?_⟩
  rwa [integrableOn_Ici_iff_integrableOn_Ioi]

/-- The explicit majorant obtained after combining a polynomial Estermann
bound with the left Abel--Mellin Gamma factor. -/
noncomputable def BBLSEstermannCentralPolynomialGrowth.integrableMajorant
    (H : BBLSEstermannCentralPolynomialGrowth) (q : ℕ) (t : ℝ) : ℝ :=
  (2 * Real.sqrt (2 * Real.pi) * H.constant *
      (q : ℝ) ^ H.qExponent) *
    bblsPolynomialExponentialMajorant H.exponent (Real.pi / 2) t

theorem BBLSEstermannCentralPolynomialGrowth.integrable_integrableMajorant
    (H : BBLSEstermannCentralPolynomialGrowth) (q : ℕ) :
    Integrable (H.integrableMajorant q) := by
  unfold integrableMajorant
  exact (integrable_bblsPolynomialExponentialMajorant H.exponent
    (by positivity : 0 < Real.pi / 2)).const_mul _

/-- The pointwise bound from the previous module is exactly dominated by
the integrable polynomial-exponential profile. -/
theorem BBLSEstermannCentralPolynomialGrowth.norm_leftDualExpression_le_majorant
    (H : BBLSEstermannCentralPolynomialGrowth)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) (t : ℝ) :
    ‖bblsEstermannLeftDualExpression a q haq t‖ ≤
      H.integrableMajorant q t := by
  calc
    _ ≤ H.constant * (q : ℝ) ^ H.qExponent *
        bblsEstermannLeftArchimedeanMajorant t *
          (1 + |t|) ^ H.exponent :=
      norm_bblsEstermannLeftDualExpression_le_of_polynomialGrowth
        H a q haq t
    _ = H.integrableMajorant q t := by
      unfold BBLSEstermannCentralPolynomialGrowth.integrableMajorant
        bblsEstermannLeftArchimedeanMajorant gammaHalfMajorant
        bblsPolynomialExponentialMajorant
      ring

/-- The complete transformed dual row is continuous in the vertical
parameter. -/
theorem continuous_bblsEstermannLeftDualExpression
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) :
    Continuous (fun t : ℝ =>
      bblsEstermannLeftDualExpression a q haq t) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hcentral : ContinuousAt bblsEstermannCentralPoint t := by
    unfold bblsEstermannCentralPoint
    fun_prop
  have hleft : ContinuousAt bblsEstermannLeftPoint t := by
    unfold bblsEstermannLeftPoint
    fun_prop
  have hGammaPoint :
      ContinuousAt Complex.Gamma (bblsEstermannLeftPoint t) := by
    apply Complex.continuousAt_Gamma
    intro n hn
    have hre := congrArg Complex.re hn
    cases n with
    | zero => norm_num [bblsEstermannLeftPoint] at hre
    | succ n =>
        have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
        norm_num [bblsEstermannLeftPoint] at hre
        linarith
  have hGamma : ContinuousAt
      (fun u : ℝ => Complex.Gamma (bblsEstermannLeftPoint u)) t :=
    by
      change ContinuousAt
        (Complex.Gamma ∘ bblsEstermannLeftPoint) t
      exact @ContinuousAt.comp' ℝ ℂ ℂ _ _ _
        bblsEstermannLeftPoint Complex.Gamma t hGammaPoint hleft
  have hfactor : ContinuousAt
      (fun u : ℝ =>
        bblsEstermannClassicalFactor q
          (bblsEstermannCentralPoint u)) t := by
    unfold bblsEstermannClassicalFactor
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    have hbase0 : (2 * (Real.pi : ℂ)) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hqpow : ContinuousAt (fun u : ℝ =>
        (q : ℂ) ^ (2 * bblsEstermannCentralPoint u - 1)) t :=
      (continuousAt_const_cpow hq0).comp (by fun_prop)
    have hbasepow : ContinuousAt (fun u : ℝ =>
        (2 * (Real.pi : ℂ)) ^
          (-2 * bblsEstermannCentralPoint u)) t :=
      (continuousAt_const_cpow hbase0).comp (by fun_prop)
    have hGammaCentralPoint :
        ContinuousAt Complex.Gamma (bblsEstermannCentralPoint t) := by
      apply Complex.continuousAt_Gamma
      intro n hn
      have hre := congrArg Complex.re hn
      norm_num [bblsEstermannCentralPoint] at hre
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hGammaCentral : ContinuousAt (fun u : ℝ =>
        Complex.Gamma (bblsEstermannCentralPoint u)) t := by
      change ContinuousAt
        (Complex.Gamma ∘ bblsEstermannCentralPoint) t
      exact @ContinuousAt.comp' ℝ ℂ ℂ _ _ _
        bblsEstermannCentralPoint Complex.Gamma t
          hGammaCentralPoint hcentral
    exact (((continuousAt_const.mul hqpow).mul hbasepow).mul
      (hGammaCentral.pow 2))
  have hcentral_ne_one : bblsEstermannCentralPoint t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [bblsEstermannCentralPoint] at hre
  have hposPoint :=
    (differentiableAt_bblsEstermannHurwitzContinuation
      (bblsEstermannInverseNumerator a q haq) q hcentral_ne_one).continuousAt
  have hnegPoint :=
    (differentiableAt_bblsEstermannHurwitzContinuation
      (bblsEstermannNegativeInverseNumerator a q haq) q
      hcentral_ne_one).continuousAt
  have hpos : ContinuousAt (fun u : ℝ =>
      bblsEstermannHurwitzContinuation
        (bblsEstermannInverseNumerator a q haq) q
        (bblsEstermannCentralPoint u)) t := by
    change ContinuousAt
      (bblsEstermannHurwitzContinuation
        (bblsEstermannInverseNumerator a q haq) q ∘
          bblsEstermannCentralPoint) t
    exact @ContinuousAt.comp' ℝ ℂ ℂ _ _ _
      bblsEstermannCentralPoint
      (bblsEstermannHurwitzContinuation
        (bblsEstermannInverseNumerator a q haq) q)
      t hposPoint hcentral
  have hneg : ContinuousAt (fun u : ℝ =>
      bblsEstermannHurwitzContinuation
        (bblsEstermannNegativeInverseNumerator a q haq) q
        (bblsEstermannCentralPoint u)) t := by
    change ContinuousAt
      (bblsEstermannHurwitzContinuation
        (bblsEstermannNegativeInverseNumerator a q haq) q ∘
          bblsEstermannCentralPoint) t
    exact @ContinuousAt.comp' ℝ ℂ ℂ _ _ _
      bblsEstermannCentralPoint
      (bblsEstermannHurwitzContinuation
        (bblsEstermannNegativeInverseNumerator a q haq) q)
      t hnegPoint hcentral
  have hcos : ContinuousAt (fun u : ℝ =>
      Complex.cos ((Real.pi : ℂ) *
        bblsEstermannCentralPoint u)) t := by
    fun_prop
  exact (hGamma.mul hfactor).mul (hpos.add (hcos.mul hneg))

/-- Any scalar Hurwitz central-line growth theorem therefore supplies a
genuinely integrable complete transformed Estermann row. -/
theorem integrable_bblsEstermannLeftDualExpression_of_hurwitzGrowth
    (H : BBLSHurwitzCentralPolynomialGrowth)
    (a q : ℕ) [NeZero q] (haq : Nat.Coprime a q) :
    Integrable (fun t : ℝ =>
      bblsEstermannLeftDualExpression a q haq t) := by
  let HE := H.toEstermann
  apply Integrable.mono' (HE.integrable_integrableMajorant q)
  · exact (continuous_bblsEstermannLeftDualExpression a q haq).aestronglyMeasurable
  · filter_upwards [] with t
    exact HE.norm_leftDualExpression_le_majorant a q haq t

end NBMellinTools.NB12
