import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Route B7.4: modulus-explicit vertical bounds for the Estermann continuation

The H15 contour needs growth bounds on the finite Hurwitz representation of
the Estermann continuation.  A bound independent of the modulus is not
assumed here: on strips containing the special value at zero, the cotangent
normalization already shows that modulus dependence must be retained.

This file first proves an unconditional finite triangle-inequality majorant.
It removes the additive numerator completely and reduces all remaining growth
to a finite sum of scalar Hurwitz-zeta norms.  It then states the scalar
vertical-growth input with explicit modulus dependence, ready to be combined
with the Gaussian damping from B7.3.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannVerticalBounds

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour

/-! ## Explicit absorption of polynomial growth by a Gaussian -/

/-- A polynomial factor is absorbed by half of a positive Gaussian exponent.
The displayed constant is deliberately elementary and uniform in `t`. -/
theorem polynomial_mul_gaussian_le_weaker_gaussian
    (η : ℝ) (hη : 0 < η) (n : ℕ) (t : ℝ) :
    (1 + |t|) ^ n * Real.exp (-η * t ^ 2) ≤
      Real.exp ((n : ℝ) ^ 2 / (2 * η)) *
        Real.exp (-(η / 2) * t ^ 2) := by
  have hbase : 1 + |t| ≤ Real.exp |t| := by
    simpa [add_comm] using Real.add_one_le_exp |t|
  have hpow : (1 + |t|) ^ n ≤ (Real.exp |t|) ^ n :=
    pow_le_pow_left₀ (by positivity) hbase n
  have hquad :
      (n : ℝ) * |t| - (η / 2) * t ^ 2 ≤
        (n : ℝ) ^ 2 / (2 * η) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hη)).2
    have hsquare : 0 ≤ (η * |t| - (n : ℝ)) ^ 2 := sq_nonneg _
    have habs : |t| ^ 2 = t ^ 2 := sq_abs t
    rw [← habs]
    nlinarith
  calc
    (1 + |t|) ^ n * Real.exp (-η * t ^ 2) ≤
        (Real.exp |t|) ^ n * Real.exp (-η * t ^ 2) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ) * |t| - η * t ^ 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((n : ℝ) ^ 2 / (2 * η) -
        (η / 2) * t ^ 2) := by
      rw [Real.exp_le_exp]
      nlinarith
    _ = Real.exp ((n : ℝ) ^ 2 / (2 * η)) *
        Real.exp (-(η / 2) * t ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- A polynomial-times-Gaussian vertical majorant, before the polynomial is
absorbed into a weaker Gaussian exponent. -/
def HasPolynomialGaussianVerticalMajorant
    (f : ℂ → ℂ) (σ η C : ℝ) (degree : ℕ) : Prop :=
  ∀ t : ℝ,
    ‖f (estermannVerticalPoint σ t)‖ ≤
      C * (1 + |t|) ^ degree * Real.exp (-η * t ^ 2)

/-- The exact adapter from a polynomial Gaussian bound to the pure Gaussian
interface consumed by the contour package. -/
theorem gaussianMajorant_of_polynomialGaussianMajorant
    (f : ℂ → ℂ) (σ η C : ℝ) (degree : ℕ)
    (hη : 0 < η) (hC : 0 ≤ C)
    (H : HasPolynomialGaussianVerticalMajorant f σ η C degree) :
    HasGaussianVerticalMajorant f σ (η / 2)
      (C * Real.exp ((degree : ℝ) ^ 2 / (2 * η))) := by
  intro t
  calc
    ‖f (estermannVerticalPoint σ t)‖ ≤
        C * (1 + |t|) ^ degree * Real.exp (-η * t ^ 2) := H t
    _ = C * ((1 + |t|) ^ degree * Real.exp (-η * t ^ 2)) := by
      ring
    _ ≤ C * (Real.exp ((degree : ℝ) ^ 2 / (2 * η)) *
        Real.exp (-(η / 2) * t ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (polynomial_mul_gaussian_le_weaker_gaussian η hη degree t) hC
    _ = (C * Real.exp ((degree : ℝ) ^ 2 / (2 * η))) *
        Real.exp (-(η / 2) * t ^ 2) := by
      ring

/-- The Gaussian evaluation weight has a vertical-line bound on either side
of its pole.  The denominator is the distance of the line from `s = 1`. -/
theorem norm_estermannGaussianEvaluationWeight_vertical_le_of_ne
    (η σ t : ℝ) (hσ : σ ≠ 1) :
    ‖estermannGaussianEvaluationWeight η (estermannVerticalPoint σ t)‖ ≤
      (Real.exp (η * (σ - 1) ^ 2) / |σ - 1|) *
        Real.exp (-η * t ^ 2) := by
  have hσsub : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ
  have hσabs : 0 < |σ - 1| := abs_pos.mpr hσsub
  have hden : |σ - 1| ≤
      ‖estermannVerticalPoint σ t - (1 : ℂ)‖ := by
    calc
      |σ - 1| = |(estermannVerticalPoint σ t - (1 : ℂ)).re| := by
        simp [estermannVerticalPoint]
      _ ≤ ‖estermannVerticalPoint σ t - (1 : ℂ)‖ :=
        Complex.abs_re_le_norm _
  unfold estermannGaussianEvaluationWeight estermannEvaluationWeight
  rw [norm_div, norm_estermannGaussianDamping_vertical]
  calc
    Real.exp (η * ((σ - 1) ^ 2 - t ^ 2)) /
        ‖estermannVerticalPoint σ t - (1 : ℂ)‖ ≤
      Real.exp (η * ((σ - 1) ^ 2 - t ^ 2)) / |σ - 1| :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hσabs hden
    _ = (Real.exp (η * (σ - 1) ^ 2) / |σ - 1|) *
        Real.exp (-η * t ^ 2) := by
      rw [show η * ((σ - 1) ^ 2 - t ^ 2) =
          η * (σ - 1) ^ 2 + (-η * t ^ 2) by ring,
        Real.exp_add]
      ring

/-- The finite scalar Hurwitz mass at one complex argument. -/
noncomputable def hurwitzResidueNormSum
    (q : ℕ) [NeZero q] (s : ℂ) : ℝ :=
  ∑ r : ZMod q, ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r) s‖

/-- The numerator-free majorant obtained by applying the triangle inequality
to both finite residue sums. -/
noncomputable def estermannFiniteHurwitzNormMajorant
    (q : ℕ) [NeZero q] (s : ℂ) : ℝ :=
  ‖(q : ℂ) ^ (-s)‖ *
    ∑ j : ZMod q,
      (‖(q : ℂ) ^ (-s)‖ * hurwitzResidueNormSum q s) *
        ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s‖

/-- Unconditional reduction of the Estermann norm to scalar Hurwitz norms.
The right side is independent of the additive numerator `a`. -/
theorem norm_estermannHurwitzContinuation_le_finiteMajorant
    (a q : ℕ) [NeZero q] (s : ℂ) :
    ‖estermannHurwitzContinuation a q s‖ ≤
      estermannFiniteHurwitzNormMajorant q s := by
  rw [estermannHurwitzContinuation_eq_finiteSum]
  unfold estermannHurwitzFiniteSum estermannFiniteHurwitzNormMajorant
  rw [norm_mul]
  calc
    ‖(q : ℂ) ^ (-s)‖ *
        ‖∑ j : ZMod q,
          ((q : ℂ) ^ (-s) *
              ∑ k : ZMod q,
                estermannResiduePhase a j k *
                  HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) *
            HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s‖ ≤
      ‖(q : ℂ) ^ (-s)‖ *
        ∑ j : ZMod q,
          ‖((q : ℂ) ^ (-s) *
                ∑ k : ZMod q,
                  estermannResiduePhase a j k *
                    HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s) *
              HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖(q : ℂ) ^ (-s)‖ *
        ∑ j : ZMod q,
          (‖(q : ℂ) ^ (-s)‖ * hurwitzResidueNormSum q s) *
            ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      unfold hurwitzResidueNormSum
      have hinner := norm_sum_le Finset.univ
        (fun k : ZMod q =>
          estermannResiduePhase a j k *
            HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s)
      simpa [norm_mul, estermannResiduePhase] using hinner

/-- The nested majorant factorizes as the square of the scalar Hurwitz mass.
This identity makes the exact modulus dependence transparent. -/
theorem estermannFiniteHurwitzNormMajorant_eq
    (q : ℕ) [NeZero q] (s : ℂ) :
    estermannFiniteHurwitzNormMajorant q s =
      ‖(q : ℂ) ^ (-s)‖ ^ 2 * hurwitzResidueNormSum q s ^ 2 := by
  unfold estermannFiniteHurwitzNormMajorant hurwitzResidueNormSum
  rw [← Finset.mul_sum]
  ring

/-- The resulting compact unconditional bound. -/
theorem norm_estermannHurwitzContinuation_le
    (a q : ℕ) [NeZero q] (s : ℂ) :
    ‖estermannHurwitzContinuation a q s‖ ≤
      ‖(q : ℂ) ^ (-s)‖ ^ 2 * hurwitzResidueNormSum q s ^ 2 := by
  rw [← estermannFiniteHurwitzNormMajorant_eq]
  exact norm_estermannHurwitzContinuation_le_finiteMajorant a q s

/-- A modulus-explicit scalar Hurwitz bound on a closed vertical strip.  This
is the exact classical analytic input absent from current Mathlib: the
finite Estermann reduction above is already proved. -/
structure HurwitzVerticalStripGrowth
    (σL σR : ℝ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  qExponent : ℕ
  tDegree : ℕ
  bound : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (σ t : ℝ),
    σL ≤ σ → σ ≤ σR →
    ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
      (estermannVerticalPoint σ t)‖ ≤
      C * (q : ℝ) ^ qExponent * (1 + |t|) ^ tDegree

/-- The scalar pointwise majorant named for subsequent formulas. -/
noncomputable def HurwitzVerticalStripGrowth.pointMajorant
    {σL σR : ℝ} (H : HurwitzVerticalStripGrowth σL σR)
    (q : ℕ) (t : ℝ) : ℝ :=
  H.C * (q : ℝ) ^ H.qExponent * (1 + |t|) ^ H.tDegree

theorem HurwitzVerticalStripGrowth.pointMajorant_nonneg
    {σL σR : ℝ} (H : HurwitzVerticalStripGrowth σL σR)
    (q : ℕ) (t : ℝ) :
    0 ≤ H.pointMajorant q t := by
  unfold pointMajorant
  exact mul_nonneg
    (mul_nonneg H.C_nonneg (pow_nonneg (Nat.cast_nonneg q) _))
    (pow_nonneg (by positivity) _)

/-- Summing a scalar strip bound over the residue classes costs exactly one
factor of the modulus. -/
theorem HurwitzVerticalStripGrowth.residueNormSum_le
    {σL σR : ℝ} (H : HurwitzVerticalStripGrowth σL σR)
    (q : ℕ) [NeZero q] (σ t : ℝ)
    (hσL : σL ≤ σ) (hσR : σ ≤ σR) :
    hurwitzResidueNormSum q (estermannVerticalPoint σ t) ≤
      (q : ℝ) * H.pointMajorant q t := by
  unfold hurwitzResidueNormSum
  calc
    (∑ r : ZMod q,
        ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
          (estermannVerticalPoint σ t)‖) ≤
        ∑ _r : ZMod q, H.pointMajorant q t := by
      apply Finset.sum_le_sum
      intro r _
      exact H.bound q r σ t hσL hσR
    _ = (q : ℝ) * H.pointMajorant q t := by
      simp [nsmul_eq_mul]

/-- The resulting modulus-explicit Estermann bound on the strip.  No
dependence on the additive numerator remains. -/
theorem HurwitzVerticalStripGrowth.estermann_norm_le
    {σL σR : ℝ} (H : HurwitzVerticalStripGrowth σL σR)
    (a q : ℕ) [NeZero q] (σ t : ℝ)
    (hσL : σL ≤ σ) (hσR : σ ≤ σR) :
    ‖estermannHurwitzContinuation a q
        (estermannVerticalPoint σ t)‖ ≤
      Real.rpow (q : ℝ) (-σ) ^ 2 *
        ((q : ℝ) * H.pointMajorant q t) ^ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsum := H.residueNormSum_le q σ t hσL hσR
  have hsum_nonneg :
      0 ≤ hurwitzResidueNormSum q (estermannVerticalPoint σ t) := by
    unfold hurwitzResidueNormSum
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc
    ‖estermannHurwitzContinuation a q
        (estermannVerticalPoint σ t)‖ ≤
      ‖(q : ℂ) ^ (-estermannVerticalPoint σ t)‖ ^ 2 *
        hurwitzResidueNormSum q (estermannVerticalPoint σ t) ^ 2 :=
          norm_estermannHurwitzContinuation_le a q _
    _ ≤ ‖(q : ℂ) ^ (-estermannVerticalPoint σ t)‖ ^ 2 *
        ((q : ℝ) * H.pointMajorant q t) ^ 2 := by
      gcongr
    _ = Real.rpow (q : ℝ) (-σ) ^ 2 *
        ((q : ℝ) * H.pointMajorant q t) ^ 2 := by
      have hnorm :
          ‖(q : ℂ) ^ (-estermannVerticalPoint σ t)‖ =
            Real.rpow (q : ℝ) (-σ) := by
        rw [← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hq]
        simp [estermannVerticalPoint]
      rw [hnorm]

/-- Step 1's honest formal endpoint: all Estermann vertical growth follows
from one scalar Hurwitz strip package, with every modulus and polynomial
factor displayed explicitly. -/
structure EstermannVerticalBoundsPackage
    (σL σR : ℝ) where
  hurwitz : HurwitzVerticalStripGrowth σL σR

/-! ## Pole-compatible growth interfaces -/

/-- Polynomial growth on one fixed vertical line.  This is the correct
all-height input for either vertical side of the H15 rectangle, since the
line is chosen away from the Hurwitz pole. -/
structure HurwitzFixedVerticalLineGrowth (σ : ℝ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  qExponent : ℕ
  tDegree : ℕ
  bound : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (t : ℝ),
    ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
      (estermannVerticalPoint σ t)‖ ≤
      C * (q : ℝ) ^ qExponent * (1 + |t|) ^ tDegree

noncomputable def HurwitzFixedVerticalLineGrowth.pointMajorant
    {σ : ℝ} (H : HurwitzFixedVerticalLineGrowth σ)
    (q : ℕ) (t : ℝ) : ℝ :=
  H.C * (q : ℝ) ^ H.qExponent * (1 + |t|) ^ H.tDegree

theorem HurwitzFixedVerticalLineGrowth.pointMajorant_nonneg
    {σ : ℝ} (H : HurwitzFixedVerticalLineGrowth σ)
    (q : ℕ) (t : ℝ) :
    0 ≤ H.pointMajorant q t := by
  unfold pointMajorant
  exact mul_nonneg
    (mul_nonneg H.C_nonneg (pow_nonneg (Nat.cast_nonneg q) _))
    (pow_nonneg (by positivity) _)

/-- A fixed-line scalar estimate controls the finite Hurwitz mass with one
explicit factor of the modulus. -/
theorem HurwitzFixedVerticalLineGrowth.residueNormSum_le
    {σ : ℝ} (H : HurwitzFixedVerticalLineGrowth σ)
    (q : ℕ) [NeZero q] (t : ℝ) :
    hurwitzResidueNormSum q (estermannVerticalPoint σ t) ≤
      (q : ℝ) * H.pointMajorant q t := by
  unfold hurwitzResidueNormSum
  calc
    (∑ r : ZMod q,
      ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
        (estermannVerticalPoint σ t)‖) ≤
      ∑ _r : ZMod q, H.pointMajorant q t := by
        apply Finset.sum_le_sum
        intro r _
        exact H.bound q r t
    _ = (q : ℝ) * H.pointMajorant q t := by
      simp [nsmul_eq_mul]

/-- The fixed-line scalar estimate gives the corresponding
numerator-independent Estermann estimate. -/
theorem HurwitzFixedVerticalLineGrowth.estermann_norm_le
    {σ : ℝ} (H : HurwitzFixedVerticalLineGrowth σ)
    (a q : ℕ) [NeZero q] (t : ℝ) :
    ‖estermannHurwitzContinuation a q
        (estermannVerticalPoint σ t)‖ ≤
      Real.rpow (q : ℝ) (-σ) ^ 2 *
        ((q : ℝ) * H.pointMajorant q t) ^ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsum := H.residueNormSum_le q t
  have hsum_nonneg :
      0 ≤ hurwitzResidueNormSum q
        (estermannVerticalPoint σ t) := by
    unfold hurwitzResidueNormSum
    positivity
  calc
    ‖estermannHurwitzContinuation a q
        (estermannVerticalPoint σ t)‖ ≤
      ‖(q : ℂ) ^ (-estermannVerticalPoint σ t)‖ ^ 2 *
        hurwitzResidueNormSum q
          (estermannVerticalPoint σ t) ^ 2 :=
      norm_estermannHurwitzContinuation_le a q _
    _ ≤ ‖(q : ℂ) ^ (-estermannVerticalPoint σ t)‖ ^ 2 *
        ((q : ℝ) * H.pointMajorant q t) ^ 2 := by
      gcongr
    _ = Real.rpow (q : ℝ) (-σ) ^ 2 *
        ((q : ℝ) * H.pointMajorant q t) ^ 2 := by
      have hnorm :
          ‖(q : ℂ) ^ (-estermannVerticalPoint σ t)‖ =
            Real.rpow (q : ℝ) (-σ) := by
        rw [← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hq]
        simp [estermannVerticalPoint]
      rw [hnorm]

/-- Polynomial growth on a pole-crossing strip is meaningful at large
height.  This is the correct scalar input for the eventual horizontal edges;
unlike `HurwitzVerticalStripGrowth`, it imposes no bound near the pole. -/
structure HurwitzEventuallyVerticalStripGrowth
    (σL σR : ℝ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  qExponent : ℕ
  tDegree : ℕ
  minHeight : ℝ
  bound : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (σ t : ℝ),
    σL ≤ σ → σ ≤ σR → minHeight ≤ |t| →
    ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
      (estermannVerticalPoint σ t)‖ ≤
      C * (q : ℝ) ^ qExponent * (1 + |t|) ^ tDegree

/-! ## The pole-crossing obstruction in the legacy strip interface -/

/-- A finite polynomial bound for the raw Hurwitz zeta function cannot hold
on a closed strip containing `s = 1`.  This follows directly from Mathlib's
proved unit residue at the pole.  Consequently the H15 rectangle must use
fixed-line bounds together with an *eventual* horizontal-strip bound for the
pole-removed numerator; `HurwitzVerticalStripGrowth` cannot itself be
instantiated on the full pole-crossing rectangle. -/
theorem not_nonempty_hurwitzVerticalStripGrowth_of_crosses_one
    {σL σR : ℝ} (hL : σL ≤ 1) (hR : 1 ≤ σR) :
    ¬ Nonempty (HurwitzVerticalStripGrowth σL σR) := by
  rintro ⟨H⟩
  let x : UnitAddCircle := ZMod.toAddCircle (0 : ZMod 1)
  let p : ℝ → ℂ := fun t => estermannVerticalPoint 1 t
  let l : Filter ℝ := nhdsWithin 0 ({0}ᶜ : Set ℝ)
  have hp : Tendsto p l (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt p 0 := by
        unfold p estermannVerticalPoint
        fun_prop
      simpa [p, estermannVerticalPoint] using
        hc.tendsto.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      show p t ∈ ({1}ᶜ : Set ℂ)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      have him := congrArg Complex.im heq
      simp [p, estermannVerticalPoint] at him
      exact ht0 him
  have hres : Tendsto
      (fun t : ℝ =>
        (p t - 1) * HurwitzZeta.hurwitzZeta x (p t))
      l (𝓝 1) := by
    exact (HurwitzZeta.hurwitzZeta_residue_one x).comp hp
  have hupper : ∀ t : ℝ,
      ‖(p t - 1) * HurwitzZeta.hurwitzZeta x (p t)‖ ≤
        |t| * (H.C * (1 + |t|) ^ H.tDegree) := by
    intro t
    rw [norm_mul]
    have hzt := H.bound 1 (0 : ZMod 1) 1 t hL hR
    have hpNorm : ‖p t - 1‖ = |t| := by
      simp [p, estermannVerticalPoint]
    rw [hpNorm]
    simpa [x, p] using
      mul_le_mul_of_nonneg_left hzt (abs_nonneg t)
  have hmaj : Tendsto
      (fun t : ℝ => |t| * (H.C * (1 + |t|) ^ H.tDegree))
      l (𝓝 0) := by
    have hc : ContinuousAt
        (fun t : ℝ => |t| *
          (H.C * (1 + |t|) ^ H.tDegree)) 0 := by
      fun_prop
    convert hc.tendsto.mono_left inf_le_left using 1 <;> norm_num
  have hnorm : Tendsto
      (fun t : ℝ =>
        ‖(p t - 1) * HurwitzZeta.hurwitzZeta x (p t)‖)
      l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall hupper) hmaj
  have hzero : Tendsto
      (fun t : ℝ =>
        (p t - 1) * HurwitzZeta.hurwitzZeta x (p t))
      l (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have h01 : (0 : ℂ) = 1 := tendsto_nhds_unique hzero hres
  norm_num at h01

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannVerticalBounds
