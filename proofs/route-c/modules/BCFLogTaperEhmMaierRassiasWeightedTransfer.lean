import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMaierRassiasKernelTransfer

/-!
# Weighted-interval transfer audit for Maier--Rassias and H15

This module performs Priority 2 of the Ehm-direct audit.

* It gives exact finite Abel summation for a Möbius--kernel row with an
  arbitrary signed weight and records the maximal-prefix estimate actually
  required to bound that row.
* It expands the Maier--Rassias constituent of the genuine H15 `q = 1` row,
  preserving the taper and keeping the new dilation variable outside.
* It proves that the power-dyadic blocks in Maier--Rassias Theorem 2.1 do not
  partition a natural interval when their base is at least three.
* A two-point counterexample records that a complete-block estimate alone
  cannot control a weighted row; maximal prefixes or extra variation input
  are genuinely necessary.

No asymptotic estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMaierRassiasWeightedTransfer

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDirectFeasibility
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMaierRassiasKernelTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit
open RH.Criteria.NymanBeurling.MobiusSummatory

/-! ## Exact Abel transfer and its required input -/

/-- A Möbius--kernel row on an arbitrary natural interval with a general
real weight. -/
noncomputable def maierRassiasWeightedIntervalRow
    (g : ℝ → ℝ) (w : ℕ → ℝ) (scale : ℝ) (A B : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc A B,
    (((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      g (scale * (d : ℝ))) * w d

/-- The corresponding unweighted signed prefix. -/
noncomputable def maierRassiasIntervalPrefix
    (g : ℝ → ℝ) (scale : ℝ) (A R : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc A R,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      g (scale * (d : ℝ))

/-- Endpoint plus discrete total variation of a real weight. -/
noncomputable def realWeightVariation
    (w : ℕ → ℝ) (A B : ℕ) : ℝ :=
  |w (B + 1)| + ∑ d ∈ Finset.Icc A B, |w d - w (d + 1)|

/-- Exact signed Abel summation.  No absolute value is inserted before the
prefix sums have been formed. -/
theorem maierRassiasWeightedIntervalRow_eq_abel
    (g : ℝ → ℝ) (w : ℕ → ℝ) (scale : ℝ) (A B : ℕ)
    (hAB : A ≤ B) :
    maierRassiasWeightedIntervalRow g w scale A B =
      maierRassiasIntervalPrefix g scale A B * w (B + 1) +
        ∑ d ∈ Finset.Icc A B,
          maierRassiasIntervalPrefix g scale A d *
            (w d - w (d + 1)) := by
  exact finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial_from
    (fun d ↦ ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      g (scale * (d : ℝ))) w A B hAB

/-- Maximal signed prefix control transfers to a weighted interval with
exactly the endpoint-plus-variation loss. -/
theorem abs_maierRassiasWeightedIntervalRow_le
    (g : ℝ → ℝ) (w : ℕ → ℝ) (scale : ℝ) (A B : ℕ) (M : ℝ)
    (hAB : A ≤ B)
    (hprefix : ∀ R ∈ Finset.Icc A B,
      |maierRassiasIntervalPrefix g scale A R| ≤ M) :
    |maierRassiasWeightedIntervalRow g w scale A B| ≤
      M * realWeightVariation w A B := by
  rw [maierRassiasWeightedIntervalRow_eq_abel g w scale A B hAB]
  calc
    |maierRassiasIntervalPrefix g scale A B * w (B + 1) +
        ∑ d ∈ Finset.Icc A B,
          maierRassiasIntervalPrefix g scale A d *
            (w d - w (d + 1))| ≤
        |maierRassiasIntervalPrefix g scale A B * w (B + 1)| +
          ∑ d ∈ Finset.Icc A B,
            |maierRassiasIntervalPrefix g scale A d *
              (w d - w (d + 1))| := by
      exact (abs_add_le _ _).trans
        (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _)
    _ ≤ M * |w (B + 1)| +
        ∑ d ∈ Finset.Icc A B, M * |w d - w (d + 1)| := by
      gcongr with d hd
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (hprefix B (Finset.mem_Icc.mpr ⟨hAB, le_rfl⟩)) (abs_nonneg _)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hprefix d hd) (abs_nonneg _)
    _ = M * realWeightVariation w A B := by
      unfold realWeightVariation
      rw [← Finset.mul_sum]
      ring

/-- The stronger input that a weighted transfer actually needs.  The
published Maier--Rassias theorem is represented separately by
`MaierRassiasPowerSavingEstimate` and does not supply these maximal prefixes. -/
structure MaierRassiasMaximalPowerDyadicEstimate
    (K : MaierRassiasKernel) where
  z0 : ℝ
  z0_pos : 0 < z0
  bound : ∀ D : ℕ, 2 ≤ D → ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ R ∈ Finset.Icc (k ^ D) (2 * k ^ D - 1),
        |maierRassiasIntervalPrefix K.g (1 / (k : ℝ)) (k ^ D) R| ≤
          C * (k : ℝ) ^ ((D : ℝ) - z0 + eps)

/-! ## Exact expansion of the H15 weighted row -/

/-- The weight multiplying the transferred Maier--Rassias kernel in the
actual `q = 1` H15 row. -/
noncomputable def ehmMaierRassiasAbelWeight
    (X m : ℕ) (d : ℕ) : ℝ :=
  ehmDyadicNearPairAmplitude X m d /
    (2 * ((d : ℝ) / (m : ℝ)))

/-- The Maier--Rassias/Bernoulli constituent of the actual H15 `q = 1`
inner row, before the smooth and integer-endpoint constituents are added. -/
noncomputable def ehmTypeIQOneMaierRassiasComponent
    (K X D J m : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (X + 1) D,
    if d ≤ J then
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        ehmDyadicNearPairAmplitude X m d *
          (maierRassiasMobiusHyperbolicPartial K
            ((d : ℝ) / (m : ℝ)) /
              (2 * ((d : ℝ) / (m : ℝ))))
    else 0

/-- The exact expanded row after moving the finite dilation sum outside.
The H15 taper remains inside the `d` sum and the kernel argument is
`k*d/m`. -/
noncomputable def ehmTypeIQOneExpandedMaierRassiasComponent
    (K X D J m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K,
    (((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ)) *
      ∑ d ∈ Finset.Icc (X + 1) D,
        if d ≤ J then
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            maierRassiasKernelPartialSum (K / k)
              (((k * d : ℕ) : ℝ) / (m : ℝ))) *
                ehmMaierRassiasAbelWeight X m d
        else 0

/-- Exact finite expansion of the weighted H15 row.  This is a sum identity,
not an estimate, and no absolute value is taken across `k`. -/
theorem ehmTypeIQOneMaierRassiasComponent_eq_expanded
    (K X D J m : ℕ) :
    ehmTypeIQOneMaierRassiasComponent K X D J m =
      ehmTypeIQOneExpandedMaierRassiasComponent K X D J m := by
  classical
  unfold ehmTypeIQOneMaierRassiasComponent
    ehmTypeIQOneExpandedMaierRassiasComponent
    ehmMaierRassiasAbelWeight
  simp_rw [maierRassiasMobiusHyperbolicPartial]
  calc
    (∑ d ∈ Finset.Icc (X + 1) D,
      if d ≤ J then
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          ehmDyadicNearPairAmplitude X m d *
            ((∑ k ∈ Finset.Icc 1 K,
              (((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ)) *
                maierRassiasKernelPartialSum (K / k)
                  ((k : ℝ) * ((d : ℝ) / (m : ℝ)))) /
              (2 * ((d : ℝ) / (m : ℝ))))
      else 0) =
        ∑ d ∈ Finset.Icc (X + 1) D,
          ∑ k ∈ Finset.Icc 1 K,
            if d ≤ J then
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                ehmDyadicNearPairAmplitude X m d *
                  (((((ArithmeticFunction.moebius k : ℤ) : ℝ) /
                    (k : ℝ)) *
                    maierRassiasKernelPartialSum (K / k)
                      ((k : ℝ) * ((d : ℝ) / (m : ℝ)))) /
                    (2 * ((d : ℝ) / (m : ℝ))))
            else 0 := by
      apply Finset.sum_congr rfl
      intro d hdMem
      by_cases hdJ : d ≤ J
      · simp only [hdJ, if_true]
        rw [Finset.sum_div, Finset.mul_sum]
      · simp [hdJ]
    _ = ∑ k ∈ Finset.Icc 1 K,
          ∑ d ∈ Finset.Icc (X + 1) D,
            if d ≤ J then
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                ehmDyadicNearPairAmplitude X m d *
                  (((((ArithmeticFunction.moebius k : ℤ) : ℝ) /
                    (k : ℝ)) *
                    maierRassiasKernelPartialSum (K / k)
                      ((k : ℝ) * ((d : ℝ) / (m : ℝ)))) /
                    (2 * ((d : ℝ) / (m : ℝ))))
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.Icc 1 K,
        (((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ)) *
          ∑ d ∈ Finset.Icc (X + 1) D,
            if d ≤ J then
              (((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                maierRassiasKernelPartialSum (K / k)
                  (((k * d : ℕ) : ℝ) / (m : ℝ))) *
                  (ehmDyadicNearPairAmplitude X m d /
                    (2 * ((d : ℝ) / (m : ℝ))))
            else 0 := by
      apply Finset.sum_congr rfl
      intro k hkMem
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hdMem
      by_cases hdJ : d ≤ J
      · simp only [hdJ, if_true]
        push_cast
        ring
      · simp [hdJ]

/-! ## Why the published blocks do not supply the needed partition -/

/-- For a base at least three, consecutive Maier--Rassias power-dyadic
blocks have a genuine gap. -/
theorem maierRassiasPowerDyadic_gap
    (k D : ℕ) (hk : 3 ≤ k) :
    2 * k ^ D < k ^ (D + 1) := by
  calc
    2 * k ^ D < k * k ^ D :=
      Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos (by omega) D)
    _ = k ^ (D + 1) := by rw [pow_succ]; ring

/-- The first integer after the `D`th block belongs neither to that block nor
to the next one.  Hence these blocks cannot form an interval partition for
`k ≥ 3`. -/
theorem maierRassiasPowerDyadic_gap_witness
    (k D : ℕ) (hk : 3 ≤ k) :
    2 * k ^ D ∉ Finset.Ico (k ^ D) (2 * k ^ D) ∧
      2 * k ^ D ∉ Finset.Ico (k ^ (D + 1)) (2 * k ^ (D + 1)) := by
  constructor
  · simp
  · simp only [Finset.mem_Ico, not_and_or]
    exact Or.inl (Nat.not_le_of_lt (maierRassiasPowerDyadic_gap k D hk))

/-- A complete-block cancellation statement alone cannot control a weighted
row: this two-point signed block has total zero but a weighted value one. -/
theorem endpoint_block_bound_does_not_control_weighted_row :
    let a : ℕ → ℝ := fun n ↦ if n = 1 then 1 else if n = 2 then -1 else 0
    let w : ℕ → ℝ := fun n ↦ if n = 1 then 1 else 0
    (∑ n ∈ Finset.Icc 1 2, a n) = 0 ∧
      |∑ n ∈ Finset.Icc 1 2, a n * w n| = 1 := by
  have hset : Finset.Icc 1 2 = {1, 2} := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  simp [hset]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMaierRassiasWeightedTransfer
