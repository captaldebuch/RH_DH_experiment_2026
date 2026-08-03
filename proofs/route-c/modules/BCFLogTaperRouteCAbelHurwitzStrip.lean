import Mathlib.Analysis.Complex.PhragmenLindelof
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHorizontal

/-!
# Route C: eventual Hurwitz growth on the Abel rectangle

This module constructs the right boundary estimate for the pole-crossing
Hurwitz strip and records the pole-removed Phragmen--Lindelöf target.  The
right boundary is a direct absolutely-convergent Dirichlet-series argument;
the only remaining analytic issue is growth of the holomorphic pole-removed
factor inside the strip.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzStrip

open Complex Filter Set Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVerticalBounds
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzGrowth

/-- Every Dirichlet series with coefficient norm at most one is uniformly
bounded on `Re(s)=3/2` by the constant-series mass. -/
theorem norm_LSeries_three_halves_add_I_mul_le
    {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ)
    (hΦ : ∀ j, ‖Φ j‖ ≤ 1) (t : ℝ) :
    ‖LSeries (Φ ·) (estermannVerticalPoint (3 / 2 : ℝ) t)‖ ≤
      unitThreeHalvesNormMass := by
  let s : ℂ := estermannVerticalPoint (3 / 2 : ℝ) t
  have hs : 1 < s.re := by norm_num [s, estermannVerticalPoint]
  have hsum : LSeriesSummable (Φ ·) s :=
    ZMod.LSeriesSummable_of_one_lt_re Φ hs
  unfold LSeries unitThreeHalvesNormMass
  calc
    ‖∑' n : ℕ, LSeries.term (Φ ·) s n‖ ≤
        ∑' n : ℕ, ‖LSeries.term (Φ ·) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ,
        ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 / 2 : ℂ) n‖ := by
      apply Summable.tsum_le_tsum _ hsum.norm summable_unitThreeHalvesNorm
      intro n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      split_ifs with hn
      · exact le_rfl
      · simp only [s, estermannVerticalPoint_re]
        gcongr
        · simpa using hΦ (n : ZMod q)
        · exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
        · norm_num

/-- Isolating one residue class in `ZMod q` recovers one rational Hurwitz
zeta value from a bounded-coefficient Dirichlet series. -/
theorem delta_LSeries_eq_cpow_mul_hurwitzZeta
    (q : ℕ) [NeZero q] (r : ZMod q) (t : ℝ) :
    LSeries ((fun j : ZMod q => if j = r then (1 : ℂ) else 0) ·)
        (estermannVerticalPoint (3 / 2 : ℝ) t) =
      (q : ℂ) ^
          (-estermannVerticalPoint (3 / 2 : ℝ) t) *
        HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
          (estermannVerticalPoint (3 / 2 : ℝ) t) := by
  let Φ : ZMod q → ℂ := fun j => if j = r then 1 else 0
  have hs : 1 < (estermannVerticalPoint (3 / 2 : ℝ) t).re := by
    norm_num [estermannVerticalPoint]
  have h := ZMod.LFunction_eq_LSeries Φ hs
  unfold ZMod.LFunction at h
  have hsum :
      (∑ j : ZMod q,
        Φ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j)
          (estermannVerticalPoint (3 / 2 : ℝ) t)) =
        HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
          (estermannVerticalPoint (3 / 2 : ℝ) t) := by
    simp [Φ]
  rw [hsum] at h
  simpa [Φ] using h.symm

/-- The right boundary of the canonical strip has an explicit polynomial
modulus loss and no vertical loss. -/
theorem norm_hurwitzZeta_three_halves_add_I_mul_le
    (q : ℕ) [NeZero q] (r : ZMod q) (t : ℝ) :
    ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
        (estermannVerticalPoint (3 / 2 : ℝ) t)‖ ≤
      (q : ℝ) ^ 2 * unitThreeHalvesNormMass := by
  let Φ : ZMod q → ℂ := fun j => if j = r then 1 else 0
  have hΦ : ∀ j, ‖Φ j‖ ≤ 1 := by
    intro j
    simp only [Φ]
    split_ifs <;> simp
  have hseries := norm_LSeries_three_halves_add_I_mul_le Φ hΦ t
  have hdelta := delta_LSeries_eq_cpow_mul_hurwitzZeta q r t
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnormQ :
      ‖(q : ℂ) ^ (-estermannVerticalPoint (3 / 2 : ℝ) t)‖ =
        Real.rpow (q : ℝ) (-(3 / 2 : ℝ)) := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hq]
    simp [estermannVerticalPoint]
  rw [hdelta, norm_mul, hnormQ] at hseries
  have hqpowPos :
      0 < Real.rpow (q : ℝ) (-(3 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos hq _
  have hraw :
      ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
        (estermannVerticalPoint (3 / 2 : ℝ) t)‖ ≤
        unitThreeHalvesNormMass /
          Real.rpow (q : ℝ) (-(3 / 2 : ℝ)) :=
    (le_div_iff₀ hqpowPos).2 (by simpa [mul_comm] using hseries)
  calc
    ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r)
        (estermannVerticalPoint (3 / 2 : ℝ) t)‖ ≤
      unitThreeHalvesNormMass /
        Real.rpow (q : ℝ) (-(3 / 2 : ℝ)) := hraw
    _ = Real.rpow (q : ℝ) (3 / 2 : ℝ) *
        unitThreeHalvesNormMass := by
      have hneg := Real.rpow_neg hq.le (3 / 2 : ℝ)
      have hinv :
          (Real.rpow (q : ℝ) (-(3 / 2 : ℝ)))⁻¹ =
            Real.rpow (q : ℝ) (3 / 2 : ℝ) := by
        calc
          (Real.rpow (q : ℝ) (-(3 / 2 : ℝ)))⁻¹ =
              ((Real.rpow (q : ℝ) (3 / 2 : ℝ))⁻¹)⁻¹ :=
            congrArg Inv.inv hneg
          _ = Real.rpow (q : ℝ) (3 / 2 : ℝ) := inv_inv _
      rw [div_eq_mul_inv, hinv]
      ring
    _ ≤ (q : ℝ) ^ 2 * unitThreeHalvesNormMass := by
      apply mul_le_mul_of_nonneg_right
      · calc
          Real.rpow (q : ℝ) (3 / 2 : ℝ) ≤
              Real.rpow (q : ℝ) 2 :=
            Real.rpow_le_rpow_of_exponent_le
              (by exact_mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne q)))
              (by norm_num)
          _ = (q : ℝ) ^ 2 := by
            simpa using Real.rpow_natCast (q : ℝ) 2
      · exact unitThreeHalvesNormMass_nonneg

/-- The unconditional right endpoint package for the pole-crossing strip.
The modulus loss `q^2` is a harmless integral majorant of `q^(3/2)`. -/
noncomputable def hurwitzThreeHalvesFixedLineGrowth :
    HurwitzFixedVerticalLineGrowth (3 / 2 : ℝ) where
  C := unitThreeHalvesNormMass
  C_nonneg := unitThreeHalvesNormMass_nonneg
  qExponent := 2
  tDegree := 0
  bound q _ r t := by
    simpa [mul_comm] using norm_hurwitzZeta_three_halves_add_I_mul_le q r t

/-! ## Pole removal and the exact Phragmen--Lindelof function -/

/-- The globally patched factor `(s-1) ζ(s,x)` is entire.  Mathlib already
supplies differentiability at the patched pole; away from it the assertion
is elementary from the meromorphic Hurwitz zeta continuation. -/
theorem differentiable_hurwitzPoleRemovedFactor (x : UnitAddCircle) :
    Differentiable ℂ (hurwitzPoleRemovedFactor x) := by
  intro s
  by_cases hs : s = 1
  · simpa [hs] using differentiableAt_hurwitzPoleRemovedFactor x
  · have hprincipal : DifferentiableAt ℂ
        (fun z : ℂ => 1 / (z - 1) / Complex.Gammaℝ z) s := by
      have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
      have hinv : DifferentiableAt ℂ (fun z : ℂ => (z - 1)⁻¹) s :=
        (differentiableAt_id.sub_const 1).inv hsub
      have hgammaInv : DifferentiableAt ℂ
          (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) s :=
        Complex.differentiable_Gammaℝ_inv.differentiableAt
      simpa [div_eq_mul_inv] using hinv.mul hgammaInv
    unfold hurwitzPoleRemovedFactor hurwitzRegularPart
    exact Complex.differentiable_Gammaℝ_inv.differentiableAt.add
      ((differentiableAt_id.sub_const 1).mul
        ((HurwitzZeta.differentiableAt_hurwitzZeta x hs).sub hprincipal))

/-- Divide the pole-removed factor by a quadratic with its only zero at
`-2`, safely to the left of the canonical strip.  Boundary estimates for
this function are constant rather than polynomial. -/
noncomputable def normalizedHurwitzPoleRemovedFactor
    (x : UnitAddCircle) (s : ℂ) : ℂ :=
  hurwitzPoleRemovedFactor x s / (s + 2) ^ 2

theorem differentiableAt_normalizedHurwitzPoleRemovedFactor
    (x : UnitAddCircle) {s : ℂ} (hs : (-1 / 2 : ℝ) ≤ s.re) :
    DifferentiableAt ℂ (normalizedHurwitzPoleRemovedFactor x) s := by
  have hden : s + 2 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith
  unfold normalizedHurwitzPoleRemovedFactor
  exact (differentiable_hurwitzPoleRemovedFactor x).differentiableAt.div
    ((differentiableAt_id.add_const 2).pow 2) (pow_ne_zero 2 hden)

/-- The normalized pole-removed factor satisfies the holomorphy and closed
strip continuity hypothesis of Phragmen--Lindelof. -/
theorem diffContOnCl_normalizedHurwitzPoleRemovedFactor
    (x : UnitAddCircle) :
    DiffContOnCl ℂ (normalizedHurwitzPoleRemovedFactor x)
      (Complex.re ⁻¹' Set.Ioo (-1 / 2 : ℝ) (3 / 2 : ℝ)) := by
  let U : Set ℂ := Complex.re ⁻¹' Set.Ioo (-1 / 2 : ℝ) (3 / 2 : ℝ)
  have hclosure : closure U ⊆
      Complex.re ⁻¹' Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ) := by
    apply closure_minimal
    · intro z hz
      exact ⟨hz.1.le, hz.2.le⟩
    · exact isClosed_Icc.preimage Complex.continuous_re
  constructor
  · intro z hz
    exact DifferentiableAt.differentiableWithinAt
      (differentiableAt_normalizedHurwitzPoleRemovedFactor x hz.1.le)
  · intro z hz
    exact (differentiableAt_normalizedHurwitzPoleRemovedFactor x
      (hclosure hz).1).continuousAt.continuousWithinAt

/-! ## From a normalized strip bound to the contour input -/

/-- On the canonical strip the quadratic normalizing denominator has at
most linear vertical growth. -/
theorem norm_verticalPoint_add_two_le
    (σ t : ℝ) (hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ)) :
    ‖estermannVerticalPoint σ t + 2‖ ≤ 4 * (1 + |t|) := by
  have hdecomp :
      estermannVerticalPoint σ t + 2 =
        ((σ + 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    unfold estermannVerticalPoint
    push_cast
    ring
  rw [hdecomp]
  calc
    ‖((σ + 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ≤
        ‖((σ + 2 : ℝ) : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |σ + 2| + |t| := by
      congr 1
      · rw [Complex.norm_real, Real.norm_eq_abs]
      · simp
    _ ≤ 4 * (1 + |t|) := by
      rw [abs_of_pos (by linarith [hσ.1])]
      linarith [hσ.2, abs_nonneg t]

theorem one_add_abs_le_two_norm_verticalPoint_add_two
    (σ t : ℝ) (hσ : (-1 : ℝ) ≤ σ) :
    1 + |t| ≤ 2 * ‖estermannVerticalPoint σ t + 2‖ := by
  have hre := Complex.abs_re_le_norm (estermannVerticalPoint σ t + 2)
  have him := Complex.abs_im_le_norm (estermannVerticalPoint σ t + 2)
  have hreEq : (estermannVerticalPoint σ t + 2).re = σ + 2 := by
    simp [estermannVerticalPoint]
  have himEq : (estermannVerticalPoint σ t + 2).im = t := by
    simp [estermannVerticalPoint]
  rw [hreEq, abs_of_nonneg (by linarith)] at hre
  rw [himEq] at him
  linarith

theorem one_le_norm_verticalPoint_add_two
    (σ t : ℝ) (hσ : (-1 : ℝ) ≤ σ) :
    1 ≤ ‖estermannVerticalPoint σ t + 2‖ := by
  have hre := Complex.abs_re_le_norm (estermannVerticalPoint σ t + 2)
  have hreEq : (estermannVerticalPoint σ t + 2).re = σ + 2 := by
    simp [estermannVerticalPoint]
  rw [hreEq, abs_of_nonneg (by linarith)] at hre
  linarith

theorem norm_verticalPoint_sub_one_le
    (σ t : ℝ) (hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ)) :
    ‖estermannVerticalPoint σ t - 1‖ ≤ 2 * (1 + |t|) := by
  have hdecomp :
      estermannVerticalPoint σ t - 1 =
        ((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    unfold estermannVerticalPoint
    push_cast
    ring
  have habs : |σ - 1| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  rw [hdecomp]
  calc
    ‖((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ≤
        ‖((σ - 1 : ℝ) : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |σ - 1| + |t| := by
      congr 1
      · rw [Complex.norm_real, Real.norm_eq_abs]
      · simp
    _ ≤ 2 * (1 + |t|) := by linarith [abs_nonneg t]

/-- At height at least one, multiplication by `s-1` cannot decrease a
norm. -/
theorem one_le_norm_verticalPoint_sub_one
    (σ t : ℝ) (ht : 1 ≤ |t|) :
    1 ≤ ‖estermannVerticalPoint σ t - 1‖ := by
  have him := Complex.abs_im_le_norm (estermannVerticalPoint σ t - 1)
  have himEq : (estermannVerticalPoint σ t - 1).im = t := by
    simp [estermannVerticalPoint]
  rw [himEq] at him
  exact ht.trans him

/-- A constant bound for the normalized entire factor, uniform in the
closed strip.  Phragmen--Lindelof will construct this package from its two
proved boundary estimates and one a-priori growth hypothesis. -/
structure NormalizedHurwitzPoleRemovedStripBound where
  C : ℝ
  C_nonneg : 0 ≤ C
  qExponent : ℕ
  bound : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (σ t : ℝ),
    σ ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ) →
    ‖normalizedHurwitzPoleRemovedFactor (ZMod.toAddCircle r)
      (estermannVerticalPoint σ t)‖ ≤ C * (q : ℝ) ^ qExponent

/-- A single constant dominating both normalized boundary lines. -/
noncomputable def normalizedHurwitzBoundaryConstant (q : ℕ) : ℝ :=
  8 * (hurwitzNegativeHalfGrowthConstant +
    (q : ℝ) ^ 2 * unitThreeHalvesNormMass)

theorem normalizedHurwitzBoundaryConstant_nonneg (q : ℕ) :
    0 ≤ normalizedHurwitzBoundaryConstant q := by
  unfold normalizedHurwitzBoundaryConstant
  exact mul_nonneg (by norm_num) (add_nonneg
    hurwitzNegativeHalfGrowthConstant_nonneg
    (mul_nonneg (sq_nonneg _) unitThreeHalvesNormMass_nonneg))

/-- Constant control of the normalized pole-removed factor on the left
boundary. -/
theorem norm_normalizedHurwitzPoleRemovedFactor_left_le
    (q : ℕ) [NeZero q] (r : ZMod q) (t : ℝ) :
    ‖normalizedHurwitzPoleRemovedFactor (ZMod.toAddCircle r)
        (estermannVerticalPoint (-1 / 2 : ℝ) t)‖ ≤
      normalizedHurwitzBoundaryConstant q := by
  let s : ℂ := estermannVerticalPoint (-1 / 2 : ℝ) t
  let A : ℝ := 1 + |t|
  let D : ℝ := ‖s + 2‖
  have hs1 : s ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num [s, estermannVerticalPoint] at hre
  have hden : s + 2 ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num [s, estermannVerticalPoint] at hre
  have hdenPos : 0 < D := by
    exact norm_pos_iff.mpr hden
  have hZ := norm_hurwitzZeta_negative_half_add_I_mul_le q r t
  have hsub := norm_verticalPoint_sub_one_le (-1 / 2 : ℝ) t
    (by constructor <;> norm_num)
  have hpole := hurwitzPoleRemovedFactor_eq_mul_hurwitzZeta
    (ZMod.toAddCircle r) hs1
  have hfactor :
      ‖hurwitzPoleRemovedFactor (ZMod.toAddCircle r) s‖ ≤
        2 * hurwitzNegativeHalfGrowthConstant * A ^ 2 := by
    rw [hpole, norm_mul]
    calc
      ‖s - 1‖ *
          ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r) s‖ ≤
        (2 * A) * (hurwitzNegativeHalfGrowthConstant * A) := by
          apply mul_le_mul hsub hZ (norm_nonneg _)
          exact mul_nonneg (by norm_num) (by positivity)
      _ = 2 * hurwitzNegativeHalfGrowthConstant * A ^ 2 := by ring
  have hAD : A ≤ 2 * D := by
    simpa [A, D, s] using
      one_add_abs_le_two_norm_verticalPoint_add_two (-1 / 2 : ℝ) t (by norm_num)
  have hADsq : A ^ 2 ≤ 4 * D ^ 2 := by
    have hsquares := (sq_le_sq₀ (by dsimp [A]; positivity) (by positivity)).2 hAD
    nlinarith
  have hfactor8 :
      ‖hurwitzPoleRemovedFactor (ZMod.toAddCircle r) s‖ ≤
        (8 * hurwitzNegativeHalfGrowthConstant) * D ^ 2 := by
    calc
      ‖hurwitzPoleRemovedFactor (ZMod.toAddCircle r) s‖ ≤
          2 * hurwitzNegativeHalfGrowthConstant * A ^ 2 := hfactor
      _ ≤ 2 * hurwitzNegativeHalfGrowthConstant * (4 * D ^ 2) :=
        mul_le_mul_of_nonneg_left hADsq
          (mul_nonneg (by norm_num) hurwitzNegativeHalfGrowthConstant_nonneg)
      _ = (8 * hurwitzNegativeHalfGrowthConstant) * D ^ 2 := by ring
  have hcoefficient :
      8 * hurwitzNegativeHalfGrowthConstant ≤
        normalizedHurwitzBoundaryConstant q := by
    unfold normalizedHurwitzBoundaryConstant
    have hqterm : 0 ≤ (q : ℝ) ^ 2 * unitThreeHalvesNormMass :=
      mul_nonneg (sq_nonneg _) unitThreeHalvesNormMass_nonneg
    linarith
  unfold normalizedHurwitzPoleRemovedFactor
  rw [norm_div, norm_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hdenPos)).2
  exact hfactor8.trans
    (mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg D))

/-- Constant control on the absolutely convergent right boundary. -/
theorem norm_normalizedHurwitzPoleRemovedFactor_right_le
    (q : ℕ) [NeZero q] (r : ZMod q) (t : ℝ) :
    ‖normalizedHurwitzPoleRemovedFactor (ZMod.toAddCircle r)
        (estermannVerticalPoint (3 / 2 : ℝ) t)‖ ≤
      normalizedHurwitzBoundaryConstant q := by
  let s : ℂ := estermannVerticalPoint (3 / 2 : ℝ) t
  let A : ℝ := 1 + |t|
  let D : ℝ := ‖s + 2‖
  let Q : ℝ := (q : ℝ) ^ 2 * unitThreeHalvesNormMass
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg (sq_nonneg _) unitThreeHalvesNormMass_nonneg
  have hs1 : s ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num [s, estermannVerticalPoint] at hre
  have hden : s + 2 ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num [s, estermannVerticalPoint] at hre
  have hdenPos : 0 < D := norm_pos_iff.mpr hden
  have hZ := norm_hurwitzZeta_three_halves_add_I_mul_le q r t
  have hsub := norm_verticalPoint_sub_one_le (3 / 2 : ℝ) t
    (by constructor <;> norm_num)
  have hpole := hurwitzPoleRemovedFactor_eq_mul_hurwitzZeta
    (ZMod.toAddCircle r) hs1
  have hfactor :
      ‖hurwitzPoleRemovedFactor (ZMod.toAddCircle r) s‖ ≤
        2 * A * Q := by
    rw [hpole, norm_mul]
    exact mul_le_mul hsub hZ (norm_nonneg _) (by dsimp [A]; positivity)
  have hAD : A ≤ 2 * D := by
    simpa [A, D, s] using
      one_add_abs_le_two_norm_verticalPoint_add_two (3 / 2 : ℝ) t (by norm_num)
  have hDone : 1 ≤ D := by
    simpa [D, s] using
      one_le_norm_verticalPoint_add_two (3 / 2 : ℝ) t (by norm_num)
  have hDD : D ≤ D ^ 2 := by
    nlinarith [sq_nonneg D]
  have hfactor4 :
      ‖hurwitzPoleRemovedFactor (ZMod.toAddCircle r) s‖ ≤
        (4 * Q) * D ^ 2 := by
    calc
      ‖hurwitzPoleRemovedFactor (ZMod.toAddCircle r) s‖ ≤ 2 * A * Q := hfactor
      _ ≤ 2 * (2 * D) * Q := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAD (by norm_num)) hQnonneg
      _ ≤ (4 * Q) * D ^ 2 := by
        calc
          2 * (2 * D) * Q = (4 * Q) * D := by ring
          _ ≤ (4 * Q) * D ^ 2 :=
            mul_le_mul_of_nonneg_left hDD
              (mul_nonneg (by norm_num) hQnonneg)
  have hcoefficient : 4 * Q ≤ normalizedHurwitzBoundaryConstant q := by
    unfold normalizedHurwitzBoundaryConstant
    dsimp [Q]
    have hC := hurwitzNegativeHalfGrowthConstant_nonneg
    have hQ : 0 ≤ (q : ℝ) ^ 2 * unitThreeHalvesNormMass :=
      mul_nonneg (sq_nonneg _) unitThreeHalvesNormMass_nonneg
    linarith
  unfold normalizedHurwitzPoleRemovedFactor
  rw [norm_div, norm_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hdenPos)).2
  exact hfactor4.trans
    (mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg D))

/-- A normalized constant strip bound gives raw Hurwitz growth of degree
two at all heights `|t| ≥ 1`. -/
noncomputable def NormalizedHurwitzPoleRemovedStripBound.toEventuallyGrowth
    (H : NormalizedHurwitzPoleRemovedStripBound) :
    HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ) where
  C := 16 * H.C
  C_nonneg := mul_nonneg (by norm_num) H.C_nonneg
  qExponent := H.qExponent
  tDegree := 2
  minHeight := 1
  bound q _ r σ t hσL hσR ht := by
    let s : ℂ := estermannVerticalPoint σ t
    have hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ) := ⟨hσL, hσR⟩
    have ht0 : t ≠ 0 := by
      intro hzero
      norm_num [hzero] at ht
    have hs1 : s ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp [s, estermannVerticalPoint] at him
      exact ht0 him
    have hden : s + 2 ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      norm_num [s, estermannVerticalPoint] at hre
      linarith [hσL]
    have hdenPos : 0 < ‖s + 2‖ := norm_pos_iff.mpr hden
    have hnorm := H.bound q r σ t hσ
    unfold normalizedHurwitzPoleRemovedFactor at hnorm
    rw [norm_div, norm_pow] at hnorm
    have hfactor :
        ‖hurwitzPoleRemovedFactor (ZMod.toAddCircle r) s‖ ≤
          (H.C * (q : ℝ) ^ H.qExponent) * ‖s + 2‖ ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos hdenPos)).mp hnorm
    have hdenBound := norm_verticalPoint_add_two_le σ t hσ
    have hdenSquare :
        ‖s + 2‖ ^ 2 ≤ 16 * (1 + |t|) ^ 2 := by
      dsimp [s] at hdenBound ⊢
      have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hdenBound
      nlinarith [sq_nonneg (1 + |t|)]
    have hfactor' :
        ‖hurwitzPoleRemovedFactor (ZMod.toAddCircle r) s‖ ≤
          (H.C * (q : ℝ) ^ H.qExponent) *
            (16 * (1 + |t|) ^ 2) :=
      hfactor.trans (mul_le_mul_of_nonneg_left hdenSquare
        (mul_nonneg H.C_nonneg (pow_nonneg (Nat.cast_nonneg q) _)))
    have hpole := hurwitzPoleRemovedFactor_eq_mul_hurwitzZeta
      (ZMod.toAddCircle r) hs1
    have hone := one_le_norm_verticalPoint_sub_one σ t ht
    calc
      ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r) s‖ ≤
          ‖hurwitzPoleRemovedFactor (ZMod.toAddCircle r) s‖ := by
        rw [hpole, norm_mul]
        exact le_mul_of_one_le_left (norm_nonneg _) hone
      _ ≤ (H.C * (q : ℝ) ^ H.qExponent) *
          (16 * (1 + |t|) ^ 2) := hfactor'
      _ = (16 * H.C) * (q : ℝ) ^ H.qExponent *
          (1 + |t|) ^ 2 := by ring

/-- The sole Phragmen--Lindelof-specific classical input still absent from
Mathlib's Hurwitz API: sufficiently small double-exponential a-priori growth
of the normalized entire factor in the open strip.  Boundary control and
the downstream contour conversion are separate proved obligations. -/
structure HurwitzPoleRemovedPhragmenLindelofGrowth where
  growth : ∀ (q : ℕ) [NeZero q] (r : ZMod q),
    ∃ c < Real.pi /
        ((3 / 2 : ℝ) - (-1 / 2 : ℝ)), ∃ B : ℝ,
      normalizedHurwitzPoleRemovedFactor (ZMod.toAddCircle r) =O[
        Filter.comap (abs ∘ Complex.im) atTop ⊓
          Filter.principal
            (Complex.re ⁻¹' Set.Ioo (-1 / 2 : ℝ) (3 / 2 : ℝ))]
        fun z => Real.exp (B * Real.exp (c * |z.im|))

/-- A modulus-independent coefficient dominating the two endpoint
constants after extracting `q^2`. -/
noncomputable def normalizedHurwitzPLGlobalConstant : ℝ :=
  8 * (hurwitzNegativeHalfGrowthConstant + unitThreeHalvesNormMass)

theorem normalizedHurwitzPLGlobalConstant_nonneg :
    0 ≤ normalizedHurwitzPLGlobalConstant := by
  unfold normalizedHurwitzPLGlobalConstant
  exact mul_nonneg (by norm_num)
    (add_nonneg hurwitzNegativeHalfGrowthConstant_nonneg
      unitThreeHalvesNormMass_nonneg)

theorem normalizedHurwitzBoundaryConstant_le_global
    (q : ℕ) [NeZero q] :
    normalizedHurwitzBoundaryConstant q ≤
      normalizedHurwitzPLGlobalConstant * (q : ℝ) ^ 2 := by
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne q))
  have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hCmul : hurwitzNegativeHalfGrowthConstant ≤
      hurwitzNegativeHalfGrowthConstant * (q : ℝ) ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq2
      hurwitzNegativeHalfGrowthConstant_nonneg
  unfold normalizedHurwitzBoundaryConstant normalizedHurwitzPLGlobalConstant
  calc
    8 * (hurwitzNegativeHalfGrowthConstant +
        (q : ℝ) ^ 2 * unitThreeHalvesNormMass) ≤
      8 * (hurwitzNegativeHalfGrowthConstant * (q : ℝ) ^ 2 +
        (q : ℝ) ^ 2 * unitThreeHalvesNormMass) := by
      gcongr
    _ = 8 * (hurwitzNegativeHalfGrowthConstant +
        unitThreeHalvesNormMass) * (q : ℝ) ^ 2 := by ring

/-- Mathlib's vertical-strip Phragmen--Lindelof theorem, with both boundary
conditions discharged, turns the sole a-priori growth field into the
normalized constant strip bound. -/
noncomputable def normalizedHurwitzStripBound_of_plGrowth
    (H : HurwitzPoleRemovedPhragmenLindelofGrowth) :
    NormalizedHurwitzPoleRemovedStripBound where
  C := normalizedHurwitzPLGlobalConstant
  C_nonneg := normalizedHurwitzPLGlobalConstant_nonneg
  qExponent := 2
  bound q _ r σ t hσ := by
    let z : ℂ := estermannVerticalPoint σ t
    have hPL :
        ‖normalizedHurwitzPoleRemovedFactor (ZMod.toAddCircle r) z‖ ≤
          normalizedHurwitzBoundaryConstant q := by
      apply PhragmenLindelof.vertical_strip
        (diffContOnCl_normalizedHurwitzPoleRemovedFactor
          (ZMod.toAddCircle r))
        (H.growth q r)
      · intro w hw
        have heq : w = estermannVerticalPoint (-1 / 2 : ℝ) w.im := by
          apply Complex.ext
          · simpa [estermannVerticalPoint] using hw
          · simp [estermannVerticalPoint]
        rw [heq]
        exact norm_normalizedHurwitzPoleRemovedFactor_left_le q r w.im
      · intro w hw
        have heq : w = estermannVerticalPoint (3 / 2 : ℝ) w.im := by
          apply Complex.ext
          · simpa [estermannVerticalPoint] using hw
          · simp [estermannVerticalPoint]
        rw [heq]
        exact norm_normalizedHurwitzPoleRemovedFactor_right_le q r w.im
      · simpa [z, estermannVerticalPoint] using hσ.1
      · simpa [z, estermannVerticalPoint] using hσ.2
    exact hPL.trans (normalizedHurwitzBoundaryConstant_le_global q)

/-- Complete construction of the scalar eventual strip package from the
single Phragmen--Lindelof growth input. -/
noncomputable def eventualHurwitzGrowth_of_plGrowth
    (H : HurwitzPoleRemovedPhragmenLindelofGrowth) :
    HurwitzEventuallyVerticalStripGrowth
      (-1 / 2 : ℝ) (3 / 2 : ℝ) :=
  (normalizedHurwitzStripBound_of_plGrowth H).toEventuallyGrowth

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelHurwitzStrip
