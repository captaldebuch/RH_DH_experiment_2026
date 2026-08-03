import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzGrowth
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannGlobalExchange

/-!
# Route C: inverse-polynomial control of the Abel horizontal edges

Exponential Stirling decay is stronger than the contour limit requires.
Repeated Gamma recurrence shifts the compact real strip into the positive
half-plane.  Each recurrence denominator has norm at least the absolute
height, while the shifted Gamma function is uniformly bounded on a compact
real interval by its defining integral.  This gives inverse-polynomial decay
of arbitrary order without Stirling asymptotics.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHorizontal

open Complex Filter Set Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBoundaryAnalysis
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannGlobalExchange
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVerticalBounds
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelContourLimit
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzGrowth
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReflectionWeight
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine

/-- The product accumulated by shifting Gamma through `n` recurrence
steps. -/
noncomputable def gammaShiftProduct (n : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.range n, (z + (j : ℂ))

/-- Exact iterated Gamma recurrence away from its intervening poles. -/
theorem Gamma_add_nat_eq_gammaShiftProduct_mul
    (n : ℕ) (z : ℂ)
    (hz : ∀ j < n, z + (j : ℂ) ≠ 0) :
    Complex.Gamma (z + n) =
      gammaShiftProduct n z * Complex.Gamma z := by
  induction n with
  | zero => simp [gammaShiftProduct]
  | succ n ih =>
      have hzn : z + (n : ℂ) ≠ 0 := hz n (Nat.lt_succ_self n)
      have hrec := Complex.Gamma_add_one (z + (n : ℂ)) hzn
      have ih' := ih (fun j hj => hz j (Nat.lt_succ_of_lt hj))
      rw [show z + (n.succ : ℕ) = (z + (n : ℂ)) + 1 by
        push_cast
        ring,
        hrec, ih']
      unfold gammaShiftProduct
      rw [Finset.prod_range_succ]
      ring

/-- On a horizontal line, every recurrence factor has norm at least the
absolute height. -/
theorem abs_pow_le_norm_gammaShiftProduct
    (n : ℕ) (c t : ℝ) :
    |t| ^ n ≤
      ‖gammaShiftProduct n
        (estermannVerticalPoint c t)‖ := by
  unfold gammaShiftProduct
  rw [norm_prod]
  calc
    |t| ^ n = ∏ _j ∈ Finset.range n, |t| := by simp
    _ ≤ ∏ j ∈ Finset.range n,
        ‖estermannVerticalPoint c t + (j : ℂ)‖ := by
      apply Finset.prod_le_prod
      · exact fun _ _ => abs_nonneg t
      · intro j hj
        have him := Complex.abs_im_le_norm
          (estermannVerticalPoint c t + (j : ℂ))
        simpa [estermannVerticalPoint] using him

/-- Iterated recurrence bounds Gamma by a positive-line Gamma value divided
by an arbitrary power of the height. -/
theorem norm_Gamma_mul_abs_pow_le_real_Gamma_shift
    (n : ℕ) (c t : ℝ) (ht : t ≠ 0) (hc : 0 < c + n) :
    ‖Complex.Gamma (estermannVerticalPoint c t)‖ * |t| ^ n ≤
      Real.Gamma (c + n) := by
  let z : ℂ := estermannVerticalPoint c t
  have hz : ∀ j < n, z + (j : ℂ) ≠ 0 := by
    intro j hj hzero
    have him := congrArg Complex.im hzero
    simp [z, estermannVerticalPoint] at him
    exact ht him
  have hrec := Gamma_add_nat_eq_gammaShiftProduct_mul n z hz
  have hprod := abs_pow_le_norm_gammaShiftProduct n c t
  have hmul := mul_le_mul_of_nonneg_left hprod
    (norm_nonneg (Complex.Gamma z))
  have harg : z + n = estermannVerticalPoint (c + n) t := by
    dsimp [z, estermannVerticalPoint]
    push_cast
    ring
  have hshift := norm_Gamma_vertical_le_real_Gamma (c + n) t hc
  calc
    ‖Complex.Gamma z‖ * |t| ^ n ≤
        ‖Complex.Gamma z‖ * ‖gammaShiftProduct n z‖ := hmul
    _ = ‖Complex.Gamma (z + n)‖ := by
      rw [hrec, norm_mul]
      ring
    _ = ‖Complex.Gamma (estermannVerticalPoint (c + n) t)‖ := by
      rw [harg]
    _ ≤ Real.Gamma (c + n) := hshift

/-- Gamma admits inverse-polynomial decay of arbitrary order, uniformly on
the real strip `[-1/2, 3/2]`.  The constant is supplied by the extreme value
theorem on the shifted compact interval. -/
theorem exists_gamma_horizontal_inverse_power_bound
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ c ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ),
        ∀ t : ℝ, 1 ≤ |t| →
          ‖Complex.Gamma (estermannVerticalPoint c t)‖ * |t| ^ n ≤ C := by
  let K : Set ℝ := Set.Icc ((n : ℝ) - 1 / 2) ((n : ℝ) + 3 / 2)
  have hK : IsCompact K := isCompact_Icc
  have hKne : K.Nonempty := by
    exact nonempty_Icc.mpr (by linarith)
  have hKpos : K ⊆ Set.Ioi 0 := by
    intro y hy
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact Set.mem_Ioi.mpr (by linarith [hy.1])
  have hcont : ContinuousOn Real.Gamma K :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono hKpos
  obtain ⟨y, hyK, hymax⟩ := hK.exists_isMaxOn hKne hcont
  refine ⟨max 0 (Real.Gamma y), le_max_left _ _, ?_⟩
  intro c hc t ht
  have ht0 : t ≠ 0 := by
    intro h
    norm_num [h] at ht
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcshift : 0 < c + n := by linarith [hc.1]
  have hmem : c + n ∈ K := by
    constructor <;> dsimp [K] <;> linarith [hc.1, hc.2]
  have hrec := norm_Gamma_mul_abs_pow_le_real_Gamma_shift
    n c t ht0 hcshift
  exact hrec.trans ((hymax hmem).trans (le_max_right _ _))

/-! ## Eventual scalar Hurwitz growth lifted to Estermann growth -/

noncomputable def eventualHurwitzPointMajorant
    {σL σR : ℝ} (H : HurwitzEventuallyVerticalStripGrowth σL σR)
    (q : ℕ) (t : ℝ) : ℝ :=
  H.C * (q : ℝ) ^ H.qExponent * (1 + |t|) ^ H.tDegree

theorem eventualHurwitzPointMajorant_nonneg
    {σL σR : ℝ} (H : HurwitzEventuallyVerticalStripGrowth σL σR)
    (q : ℕ) (t : ℝ) :
    0 ≤ eventualHurwitzPointMajorant H q t := by
  unfold eventualHurwitzPointMajorant
  exact mul_nonneg
    (mul_nonneg H.C_nonneg (pow_nonneg (Nat.cast_nonneg q) _))
    (pow_nonneg (by positivity) _)

theorem eventualHurwitz_residueNormSum_le
    {σL σR : ℝ} (H : HurwitzEventuallyVerticalStripGrowth σL σR)
    (q : ℕ) [NeZero q] (σ t : ℝ)
    (hσL : σL ≤ σ) (hσR : σ ≤ σR)
    (ht : H.minHeight ≤ |t|) :
    hurwitzResidueNormSum q (estermannVerticalPoint σ t) ≤
      (q : ℝ) * eventualHurwitzPointMajorant H q t := by
  unfold hurwitzResidueNormSum
  calc
    (∑ r : ZMod q,
      ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
        (estermannVerticalPoint σ t)‖) ≤
      ∑ _r : ZMod q, eventualHurwitzPointMajorant H q t := by
        apply Finset.sum_le_sum
        intro r _
        exact H.bound q r σ t hσL hσR ht
    _ = (q : ℝ) * eventualHurwitzPointMajorant H q t := by
      simp [nsmul_eq_mul]

theorem eventualHurwitz_estermann_norm_le
    {σL σR : ℝ} (H : HurwitzEventuallyVerticalStripGrowth σL σR)
    (a q : ℕ) [NeZero q] (σ t : ℝ)
    (hσL : σL ≤ σ) (hσR : σ ≤ σR)
    (ht : H.minHeight ≤ |t|) :
    ‖estermannHurwitzContinuation a q
        (estermannVerticalPoint σ t)‖ ≤
      Real.rpow (q : ℝ) (-σ) ^ 2 *
        ((q : ℝ) * eventualHurwitzPointMajorant H q t) ^ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsum := eventualHurwitz_residueNormSum_le H q σ t hσL hσR ht
  have hsumNonneg :
      0 ≤ hurwitzResidueNormSum q
        (estermannVerticalPoint σ t) := by
    unfold hurwitzResidueNormSum
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc
    ‖estermannHurwitzContinuation a q
        (estermannVerticalPoint σ t)‖ ≤
      ‖(q : ℂ) ^ (-estermannVerticalPoint σ t)‖ ^ 2 *
        hurwitzResidueNormSum q
          (estermannVerticalPoint σ t) ^ 2 :=
      norm_estermannHurwitzContinuation_le a q _
    _ ≤ ‖(q : ℂ) ^ (-estermannVerticalPoint σ t)‖ ^ 2 *
        ((q : ℝ) * eventualHurwitzPointMajorant H q t) ^ 2 := by
      gcongr
    _ = Real.rpow (q : ℝ) (-σ) ^ 2 *
        ((q : ℝ) * eventualHurwitzPointMajorant H q t) ^ 2 := by
      have hnorm :
          ‖(q : ℂ) ^ (-estermannVerticalPoint σ t)‖ =
            Real.rpow (q : ℝ) (-σ) := by
        rw [← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hq]
        simp [estermannVerticalPoint]
      rw [hnorm]

/-- The polynomial constant obtained after removing the varying real part
from the eventual Estermann strip estimate. -/
noncomputable def eventualEstermannStripConstant
    (H : HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ)) (q : ℕ) : ℝ :=
  (q : ℝ) ^ 2 *
    ((q : ℝ) * (H.C * (q : ℝ) ^ H.qExponent)) ^ 2

theorem eventualEstermannStripConstant_nonneg
    (H : HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ)) (q : ℕ) :
    0 ≤ eventualEstermannStripConstant H q := by
  unfold eventualEstermannStripConstant
  positivity

/-- On the canonical strip, eventual scalar Hurwitz growth gives a uniform
Estermann polynomial bound of twice the scalar degree. -/
theorem eventualHurwitz_estermann_norm_le_uniform
    (H : HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ))
    (a q : ℕ) [NeZero q] (σ t : ℝ)
    (hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ))
    (ht : H.minHeight ≤ |t|) :
    ‖estermannHurwitzContinuation a q
        (estermannVerticalPoint σ t)‖ ≤
      eventualEstermannStripConstant H q *
        (1 + |t|) ^ (2 * H.tDegree) := by
  have hqNat : 1 ≤ q := Nat.pos_iff_ne_zero.mpr (NeZero.ne q)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hqNat
  have hraw := eventualHurwitz_estermann_norm_le H a q σ t hσ.1 hσ.2 ht
  have hpow : Real.rpow (q : ℝ) (-σ) ≤ (q : ℝ) := by
    calc
      Real.rpow (q : ℝ) (-σ) ≤ Real.rpow (q : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le hq (by linarith [hσ.1])
      _ = (q : ℝ) := Real.rpow_one _
  have hpoint :
      eventualHurwitzPointMajorant H q t =
        (H.C * (q : ℝ) ^ H.qExponent) *
          (1 + |t|) ^ H.tDegree := by
    unfold eventualHurwitzPointMajorant
    ring
  rw [hpoint] at hraw
  calc
    ‖estermannHurwitzContinuation a q
        (estermannVerticalPoint σ t)‖ ≤
      Real.rpow (q : ℝ) (-σ) ^ 2 *
        ((q : ℝ) *
          ((H.C * (q : ℝ) ^ H.qExponent) *
            (1 + |t|) ^ H.tDegree)) ^ 2 := hraw
    _ ≤ (q : ℝ) ^ 2 *
        ((q : ℝ) *
          ((H.C * (q : ℝ) ^ H.qExponent) *
            (1 + |t|) ^ H.tDegree)) ^ 2 := by
      have hrpow : 0 ≤ Real.rpow (q : ℝ) (-σ) :=
        Real.rpow_nonneg (Nat.cast_nonneg q) _
      have hsquares : Real.rpow (q : ℝ) (-σ) ^ 2 ≤ (q : ℝ) ^ 2 := by
        exact (sq_le_sq₀ hrpow (Nat.cast_nonneg q)).2 hpow
      exact mul_le_mul_of_nonneg_right hsquares (sq_nonneg _)
    _ = eventualEstermannStripConstant H q *
        (1 + |t|) ^ (2 * H.tDegree) := by
      unfold eventualEstermannStripConstant
      rw [show 2 * H.tDegree = H.tDegree * 2 by omega,
        pow_mul (1 + |t|) H.tDegree 2]
      ring

/-! ## Uniform control of the elementary reflection factor -/

/-- A real-part-uniform bound for `x ^ (s - 1)` on the canonical strip.
The two branches merely record whether real powers increase or decrease as
their exponent grows. -/
noncomputable def abelReflectionPowerBound (x : ℝ) : ℝ :=
  max (Real.rpow x (-2)) x

theorem abelReflectionPowerBound_nonneg (x : ℝ) (hx : 0 < x) :
    0 ≤ abelReflectionPowerBound x := by
  exact le_max_of_le_left (Real.rpow_nonneg hx.le _)

theorem norm_cpow_horizontal_le_abelReflectionPowerBound
    {x : ℝ} (hx : 0 < x) (σ t : ℝ)
    (hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ)) :
    ‖(x : ℂ) ^
        (((σ : ℂ) + (t : ℂ) * Complex.I) - 1)‖ ≤
      abelReflectionPowerBound x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre :
      (((σ : ℂ) + (t : ℂ) * Complex.I) - 1).re = σ - 1 := by
    norm_num [Complex.mul_re]
  rw [hre]
  by_cases hxone : 1 ≤ x
  · apply le_max_of_le_right
    calc
      Real.rpow x (σ - 1) ≤ Real.rpow x 1 :=
        Real.rpow_le_rpow_of_exponent_le hxone (by linarith [hσ.2])
      _ = x := Real.rpow_one x
  · have hxle : x ≤ 1 := le_of_not_ge hxone
    apply le_max_of_le_left
    exact Real.rpow_le_rpow_of_exponent_ge hx hxle (by linarith [hσ.1])

theorem norm_cpow_symmetric_horizontal_le_abelReflectionPowerBound
    {x : ℝ} (hx : 0 < x) (σ T : ℝ)
    (hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ)) :
    ‖(x : ℂ) ^ (((σ : ℂ) - (T : ℂ) * Complex.I) - 1)‖ ≤
      abelReflectionPowerBound x := by
  have h := norm_cpow_horizontal_le_abelReflectionPowerBound hx σ (-T) hσ
  have heq :
      ((σ : ℂ) - (T : ℂ) * Complex.I) - 1 =
        (σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I - 1 := by
    push_cast
    ring
  rw [heq]
  exact h

/-! ## The asymptotically sufficient horizontal package -/

/-- The contour only needs a majorant tending to zero.  Two spare powers
from Gamma recurrence give this convenient profile. -/
noncomputable def abelHorizontalInverseSquareMajorant
    (C T : ℝ) : ℝ :=
  C / T ^ 2

theorem tendsto_abelHorizontalInverseSquareMajorant (C : ℝ) :
    Tendsto (abelHorizontalInverseSquareMajorant C) atTop (𝓝 0) := by
  have hpow : Tendsto (fun T : ℝ => T ^ 2) atTop atTop := by
    simpa [Real.rpow_natCast] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2))
  simpa [abelHorizontalInverseSquareMajorant] using hpow.const_div_atTop C

/-- An eventual inverse-square estimate for the two raw Abel horizontal
edges.  This is strictly weaker than the old exponential-Stirling package
and exactly sufficient for the infinite rectangle. -/
structure BettinConreyAbelHorizontalInverseSquareDecay
    (x : ℝ) (a q : ℕ) [NeZero q] where
  C : ℝ
  C_nonneg : 0 ≤ C
  eventual_bound : ∀ᶠ T : ℝ in atTop,
    1 ≤ T ∧
      HasSymmetricHorizontalBoundAt
        (estermannWeightedIntegrand a q
          (bettinConreyNormalizedAbelReflectionWeight x))
        (-1 / 2 : ℝ) (3 / 2 : ℝ)
        (abelHorizontalInverseSquareMajorant C) T

/-- Inverse-square pointwise control makes the oriented horizontal pair
vanish. -/
theorem BettinConreyAbelHorizontalInverseSquareDecay.horizontal_pair_vanishes
    {x : ℝ} {a q : ℕ} [NeZero q]
    (H : BettinConreyAbelHorizontalInverseSquareDecay x a q) :
    Tendsto
      (symmetricHorizontalEdges
        (estermannWeightedIntegrand a q
          (bettinConreyNormalizedAbelReflectionWeight x))
        (-1 / 2 : ℝ) (3 / 2 : ℝ)) atTop (𝓝 0) := by
  apply horizontal_pair_vanishes_of_eventual_majorant
    (estermannWeightedIntegrand a q
      (bettinConreyNormalizedAbelReflectionWeight x))
    (-1 / 2 : ℝ) (3 / 2 : ℝ)
    (abelHorizontalInverseSquareMajorant H.C)
    (by norm_num)
  · filter_upwards [H.eventual_bound] with T hT
    exact ⟨by linarith [hT.1], hT.2⟩
  · exact tendsto_abelHorizontalInverseSquareMajorant H.C

/-! ## Assembly from eventual Hurwitz growth -/

/-- The coupled product estimate behind horizontal decay.  The Estermann
factor costs `2 * tDegree` powers; Gamma recurrence is shifted by exactly
two more steps. -/
theorem norm_normalizedAbel_horizontal_mul_abs_sq_le
    (H : HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ))
    {x : ℝ} (hx : 0 < x) (a q : ℕ) [NeZero q]
    (Cgamma : ℝ)
    (hgamma : ∀ c ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ),
      ∀ t : ℝ, 1 ≤ |t| →
        ‖Complex.Gamma (estermannVerticalPoint c t)‖ *
            |t| ^ (2 * H.tDegree + 2) ≤ Cgamma)
    (σ t : ℝ) (hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ))
    (ht : 1 ≤ |t|) (hheight : H.minHeight ≤ |t|) :
    ‖estermannWeightedIntegrand a q
        (bettinConreyNormalizedAbelReflectionWeight x)
        (estermannVerticalPoint σ t)‖ * |t| ^ 2 ≤
      Cgamma * abelReflectionPowerBound x *
        eventualEstermannStripConstant H q *
          2 ^ (2 * H.tDegree) := by
  let degree : ℕ := 2 * H.tDegree
  have hσref : 1 - σ ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ) := by
    constructor <;> linarith [hσ.1, hσ.2]
  have hreflect :
      1 - estermannVerticalPoint σ t =
        estermannVerticalPoint (1 - σ) (-t) := by
    unfold estermannVerticalPoint
    push_cast
    ring
  have hGamma := hgamma (1 - σ) hσref (-t) (by simpa using ht)
  have hD := eventualHurwitz_estermann_norm_le_uniform
    H a q (1 - σ) (-t) hσref (by simpa using hheight)
  simp only [abs_neg] at hGamma hD
  have hpower := norm_cpow_horizontal_le_abelReflectionPowerBound hx σ t hσ
  have hpower' :
      ‖(x : ℂ) ^ (estermannVerticalPoint σ t - 1)‖ ≤
        abelReflectionPowerBound x := by
    simpa [estermannVerticalPoint] using hpower
  have hbase : 1 + |t| ≤ 2 * |t| := by linarith
  have hpowBase :
      (1 + |t|) ^ degree ≤ (2 * |t|) ^ degree :=
    pow_le_pow_left₀ (by positivity) hbase degree
  have hD' :
      ‖estermannHurwitzContinuation a q
          (estermannVerticalPoint (1 - σ) (-t))‖ ≤
        eventualEstermannStripConstant H q *
          (2 * |t|) ^ degree := by
    change _ ≤ eventualEstermannStripConstant H q *
      (2 * |t|) ^ degree
    exact hD.trans (mul_le_mul_of_nonneg_left hpowBase
      (eventualEstermannStripConstant_nonneg H q))
  have hintegrand :
      ‖estermannWeightedIntegrand a q
          (bettinConreyNormalizedAbelReflectionWeight x)
          (estermannVerticalPoint σ t)‖ ≤
        ‖Complex.Gamma
            (estermannVerticalPoint (1 - σ) (-t))‖ *
          abelReflectionPowerBound x *
            (eventualEstermannStripConstant H q *
              (2 * |t|) ^ degree) := by
    rw [normalizedWeightedIntegrand_eq_neg_rawReflected]
    unfold bettinConreyRawAbelReflectionWeight
    rw [norm_neg, norm_mul, norm_mul, hreflect]
    calc
      ‖Complex.Gamma (estermannVerticalPoint (1 - σ) (-t))‖ *
          ‖(x : ℂ) ^ (estermannVerticalPoint σ t - 1)‖ *
          ‖estermannHurwitzContinuation a q
            (estermannVerticalPoint (1 - σ) (-t))‖ ≤
        ‖Complex.Gamma (estermannVerticalPoint (1 - σ) (-t))‖ *
          abelReflectionPowerBound x *
          ‖estermannHurwitzContinuation a q
            (estermannVerticalPoint (1 - σ) (-t))‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hpower' (norm_nonneg _)
        · exact norm_nonneg _
      _ ≤ ‖Complex.Gamma (estermannVerticalPoint (1 - σ) (-t))‖ *
          abelReflectionPowerBound x *
            (eventualEstermannStripConstant H q *
              (2 * |t|) ^ degree) := by
        exact mul_le_mul_of_nonneg_left hD'
          (mul_nonneg (norm_nonneg _)
            (abelReflectionPowerBound_nonneg x hx))
  have hmul := mul_le_mul_of_nonneg_right hintegrand (sq_nonneg |t|)
  calc
    ‖estermannWeightedIntegrand a q
        (bettinConreyNormalizedAbelReflectionWeight x)
        (estermannVerticalPoint σ t)‖ * |t| ^ 2 ≤
      (‖Complex.Gamma
          (estermannVerticalPoint (1 - σ) (-t))‖ *
        abelReflectionPowerBound x *
          (eventualEstermannStripConstant H q *
            (2 * |t|) ^ degree)) * |t| ^ 2 := hmul
    _ = (‖Complex.Gamma
          (estermannVerticalPoint (1 - σ) (-t))‖ *
            |t| ^ (degree + 2)) *
        (abelReflectionPowerBound x *
          eventualEstermannStripConstant H q * 2 ^ degree) := by
      rw [mul_pow, pow_add]
      ring
    _ ≤ Cgamma *
        (abelReflectionPowerBound x *
          eventualEstermannStripConstant H q * 2 ^ degree) := by
      apply mul_le_mul_of_nonneg_right
      · simpa [degree] using hGamma
      · exact mul_nonneg
          (mul_nonneg (abelReflectionPowerBound_nonneg x hx)
            (eventualEstermannStripConstant_nonneg H q))
          (pow_nonneg (by norm_num) _)
    _ = Cgamma * abelReflectionPowerBound x *
        eventualEstermannStripConstant H q *
          2 ^ (2 * H.tDegree) := by
      simp only [degree]
      ring

/-- A canonical Gamma constant for the number of recurrence steps demanded
by one eventual Hurwitz-growth package. -/
noncomputable def eventualHurwitzGammaConstant
    (H : HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ)) : ℝ :=
  Classical.choose (exists_gamma_horizontal_inverse_power_bound
    (2 * H.tDegree + 2) (by omega))

theorem eventualHurwitzGammaConstant_nonneg
    (H : HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ)) :
    0 ≤ eventualHurwitzGammaConstant H :=
  (Classical.choose_spec (exists_gamma_horizontal_inverse_power_bound
    (2 * H.tDegree + 2) (by omega))).1

theorem eventualHurwitzGammaConstant_bound
    (H : HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ))
    (c : ℝ) (hc : c ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ))
    (t : ℝ) (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (estermannVerticalPoint c t)‖ *
        |t| ^ (2 * H.tDegree + 2) ≤
      eventualHurwitzGammaConstant H :=
  (Classical.choose_spec (exists_gamma_horizontal_inverse_power_bound
    (2 * H.tDegree + 2) (by omega))).2 c hc t ht

/-- Eventual polynomial Hurwitz growth on the pole-crossing strip supplies
the complete inverse-square horizontal package.  No exponential Stirling
estimate is required. -/
noncomputable def abelHorizontalInverseSquareDecay_of_eventualHurwitzGrowth
    (H : HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ))
    {x : ℝ} (hx : 0 < x) (a q : ℕ) [NeZero q] :
    BettinConreyAbelHorizontalInverseSquareDecay x a q := by
  let Cgamma : ℝ := eventualHurwitzGammaConstant H
  let C : ℝ := Cgamma * abelReflectionPowerBound x *
    eventualEstermannStripConstant H q * 2 ^ (2 * H.tDegree)
  refine
    { C := C
      C_nonneg := ?_
      eventual_bound := ?_ }
  · dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (eventualHurwitzGammaConstant_nonneg H)
          (abelReflectionPowerBound_nonneg x hx))
        (eventualEstermannStripConstant_nonneg H q))
      (pow_nonneg (by norm_num) _)
  · filter_upwards [eventually_ge_atTop (max 1 H.minHeight)] with T hT
    have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
    have hTheight : H.minHeight ≤ T :=
      le_trans (le_max_right _ _) hT
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT1
    have hTabs : |T| = T := abs_of_pos hTpos
    refine ⟨hT1, ?_⟩
    intro σ hσ
    constructor
    · have hmul := norm_normalizedAbel_horizontal_mul_abs_sq_le
        H hx a q Cgamma (eventualHurwitzGammaConstant_bound H) σ T hσ
        (by simpa [hTabs] using hT1)
        (by simpa [hTabs] using hTheight)
      unfold abelHorizontalInverseSquareMajorant
      apply (le_div_iff₀ (sq_pos_of_pos hTpos)).2
      simpa [C, hTabs, estermannVerticalPoint] using hmul
    · have hmul := norm_normalizedAbel_horizontal_mul_abs_sq_le
        H hx a q Cgamma (eventualHurwitzGammaConstant_bound H) σ (-T) hσ
        (by simpa [abs_neg, hTabs] using hT1)
        (by simpa [abs_neg, hTabs] using hTheight)
      unfold abelHorizontalInverseSquareMajorant
      apply (le_div_iff₀ (sq_pos_of_pos hTpos)).2
      simpa [C, abs_neg, hTabs, estermannVerticalPoint,
        sub_eq_add_neg] using hmul

/-- The fixed reflected-line theorem and the eventual strip theorem now
assemble the complete infinite Abel rectangle.  Thus the only remaining
input in this module is scalar Hurwitz growth at large height. -/
noncomputable def abelContourLimitData_of_eventualHurwitzGrowth
    (H : HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ))
    {x : ℝ} (hx : 0 < x) (a q : ℕ) [NeZero q] :
    BettinConreyAbelContourLimitData x a q where
  right_integrable := integrable_normalizedAbel_rightVertical x hx a q
  horizontal_pair_vanishes :=
    BettinConreyAbelHorizontalInverseSquareDecay.horizontal_pair_vanishes
      (abelHorizontalInverseSquareDecay_of_eventualHurwitzGrowth H hx a q)

/-- Exact infinite contour identity, conditional only on the eventual
scalar Hurwitz strip estimate. -/
theorem rightVertical_eq_damped_add_residues_of_eventualHurwitzGrowth
    (H : HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ))
    {x : ℝ} (hx : 0 < x) (a q : ℕ) [NeZero q] :
    estermannPrimalVerticalIntegral a q (3 / 2 : ℝ)
        (bettinConreyNormalizedAbelReflectionWeight x) =
      -(2 * Real.pi : ℝ) * dampedEstermannLambertSeries a q x +
        2 * Real.pi *
          (estermannWeightedResidueCoefficient a q
              (bettinConreyNormalizedAbelReflectionWeight x) +
            estermannHurwitzContinuation a q 0) := by
  exact BettinConreyAbelContourLimitData.rightVertical_eq_damped_add_residues
    hx (abelContourLimitData_of_eventualHurwitzGrowth H hx a q)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHorizontal
