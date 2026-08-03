import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel

/-!
# Early-block correction-coupled Ehm analysis

The dyadic Abel localization identifies the first divisor blocks `d ≍ X` as
the only place where the unsigned certificate is large.  This file makes the
corresponding signed strategy exact.

* the dyadic indices are split at a cutoff `K`;
* the retained main-plus-linear correction is allocated only to the early
  blocks;
* every early block is bounded only after its signed Abel expression and its
  correction share have been combined;
* the late blocks contain no correction and are handed to a separate
  quadratic-decay estimate; and
* the two estimates assemble into the existing correction-coupled Abel gate.

The finite identities and the assembly theorem are unconditional.  The
structure `EhmEarlyBlockCorrectionCoupledAnalysis` has two analytic fields:
the early per-block signed cancellation and the late absolute tail bound.
The former is the genuine H15-strength input; it is not asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmEarlyBlockCorrection

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularInstantiation

/-! ## Exact early/late partition of the dyadic divisor indices -/

/-- Dyadic divisor blocks at or below the early cutoff `K`. -/
def ehmEarlyDyadicDIndices (X L K : ℕ) : Finset ℕ :=
  (ehmShiftedDyadicDIndices X L).filter (fun k ↦ k ≤ K)

/-- Dyadic divisor blocks strictly above the early cutoff `K`. -/
def ehmLateDyadicDIndices (X L K : ℕ) : Finset ℕ :=
  (ehmShiftedDyadicDIndices X L).filter (fun k ↦ K < k)

theorem mem_ehmEarlyDyadicDIndices {X L K k : ℕ} :
    k ∈ ehmEarlyDyadicDIndices X L K ↔
      k ∈ ehmShiftedDyadicDIndices X L ∧ k ≤ K := by
  simp [ehmEarlyDyadicDIndices]

theorem mem_ehmLateDyadicDIndices {X L K k : ℕ} :
    k ∈ ehmLateDyadicDIndices X L K ↔
      k ∈ ehmShiftedDyadicDIndices X L ∧ K < k := by
  simp [ehmLateDyadicDIndices]

/-- Every cell in an early block has anchored divisor ratio below the next
power of two after the cutoff. -/
theorem early_dyadic_ratio_upper
    {X L K k j : ℕ} (hk : k ∈ ehmEarlyDyadicDIndices X L K)
    (hj : j ∈ ehmShiftedDyadicDBlock X L k) :
    (X + 1 + j) / (X + 1) < 2 ^ (K + 1) := by
  have hsupport := dyadic_support_of_mem_ehmShiftedDyadicDBlock hj
  have hkK := (mem_ehmEarlyDyadicDIndices.mp hk).2
  exact hsupport.2.trans_le
    (Nat.pow_le_pow_right (by omega) (by omega))

/-- Every cell in a late block has anchored divisor ratio at least the first
power of two beyond the early cutoff. -/
theorem late_dyadic_ratio_lower
    {X L K k j : ℕ} (hk : k ∈ ehmLateDyadicDIndices X L K)
    (hj : j ∈ ehmShiftedDyadicDBlock X L k) :
    2 ^ (K + 1) ≤ (X + 1 + j) / (X + 1) := by
  have hsupport := dyadic_support_of_mem_ehmShiftedDyadicDBlock hj
  have hKk : K + 1 ≤ k := by
    have := (mem_ehmLateDyadicDIndices.mp hk).2
    omega
  exact (Nat.pow_le_pow_right (by omega) hKk).trans hsupport.1

/-- The early and late fibers reassemble every sum over dyadic indices. -/
theorem sum_ehmEarly_add_late
    (X L K : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ ehmEarlyDyadicDIndices X L K, f k) +
        (∑ k ∈ ehmLateDyadicDIndices X L K, f k) =
      ∑ k ∈ ehmShiftedDyadicDIndices X L, f k := by
  classical
  simpa only [ehmEarlyDyadicDIndices, ehmLateDyadicDIndices, not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (ehmShiftedDyadicDIndices X L) (fun k ↦ k ≤ K) f)

/-! ## Correction allocations supported on the early blocks -/

/-- A correction allocation whose mass is entirely supported on the early
dyadic indices.  The support condition is stated only on the actual index
set, which is all that enters the finite reassembly. -/
structure EhmEarlySupportedCorrectionAllocation (X L K : ℕ) where
  allocation : EhmDyadicCorrectionAllocation X L
  weight_eq_zero_of_late : ∀ k ∈ ehmLateDyadicDIndices X L K,
    allocation.weight k = 0

/-- The first anchored dyadic index is always present. -/
theorem zero_mem_ehmShiftedDyadicDIndices (X L : ℕ) :
    0 ∈ ehmShiftedDyadicDIndices X L := by
  classical
  unfold ehmShiftedDyadicDIndices
  refine Finset.mem_image.mpr ⟨0, by simp, ?_⟩
  have hx : 0 < X + 1 := by omega
  simp only [ehmShiftedDyadicDIndex, Nat.add_zero, Nat.div_self hx]
  decide

/-- Baseline allocation concentrating the full retained correction on the
first divisor block.  This proves that early-supported allocations are
nonempty; it does not assert that the first block alone satisfies the
analytic decay estimate. -/
noncomputable def ehmFirstBlockCorrectionAllocation (X L : ℕ) :
    EhmDyadicCorrectionAllocation X L where
  weight := fun k ↦ if k = 0 then 1 else 0
  weight_nonneg := by
    intro k
    split_ifs <;> positivity
  mass_one := by
    classical
    simp [zero_mem_ehmShiftedDyadicDIndices X L]

/-- The first-block allocation is supported in the early sector for every
cutoff `K`. -/
noncomputable def ehmFirstBlockEarlySupportedAllocation (X L K : ℕ) :
    EhmEarlySupportedCorrectionAllocation X L K where
  allocation := ehmFirstBlockCorrectionAllocation X L
  weight_eq_zero_of_late := by
    intro k hk
    have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le K)
      (mem_ehmLateDyadicDIndices.mp hk).2
    simp [ehmFirstBlockCorrectionAllocation, Nat.ne_of_gt hkpos]

/-! ## A canonical geometric allocation suggested by the block geometry -/

/-- Supremum of the finite dyadic index set.  Unlike a closed logarithmic
formula, this definition makes the support statement purely finite. -/
def ehmAllDyadicCutoff (X L : ℕ) : ℕ :=
  (ehmShiftedDyadicDIndices X L).sup id

theorem le_ehmAllDyadicCutoff_of_mem
    {X L k : ℕ} (hk : k ∈ ehmShiftedDyadicDIndices X L) :
    k ≤ ehmAllDyadicCutoff X L := by
  unfold ehmAllDyadicCutoff
  exact Finset.le_sup (f := id) hk

/-- Reciprocal-power mass used by the geometric correction allocation. -/
noncomputable def ehmGeometricCorrectionMass (X L : ℕ) : ℝ :=
  ∑ k ∈ ehmShiftedDyadicDIndices X L, 1 / (2 : ℝ) ^ k

theorem ehmGeometricCorrectionMass_pos (X L : ℕ) :
    0 < ehmGeometricCorrectionMass X L := by
  have hzero := zero_mem_ehmShiftedDyadicDIndices X L
  unfold ehmGeometricCorrectionMass
  have hterm : (0 : ℝ) < 1 / (2 : ℝ) ^ (0 : ℕ) := by norm_num
  refine hterm.trans_le ?_
  exact Finset.single_le_sum
    (f := fun k : ℕ ↦ 1 / (2 : ℝ) ^ k)
    (fun k _ ↦ by positivity) hzero

/-- The geometric normalizing mass contains its zeroth term. -/
theorem one_le_ehmGeometricCorrectionMass (X L : ℕ) :
    1 ≤ ehmGeometricCorrectionMass X L := by
  have hzero := zero_mem_ehmShiftedDyadicDIndices X L
  unfold ehmGeometricCorrectionMass
  simpa using Finset.single_le_sum
    (f := fun k : ℕ ↦ 1 / (2 : ℝ) ^ k)
    (fun k _ ↦ by positivity) hzero

/-- The normalization never exceeds the complete geometric series. -/
theorem ehmGeometricCorrectionMass_le_two (X L : ℕ) :
    ehmGeometricCorrectionMass X L ≤ 2 := by
  unfold ehmGeometricCorrectionMass
  calc
    (∑ k ∈ ehmShiftedDyadicDIndices X L, 1 / (2 : ℝ) ^ k) ≤
        ∑' k : ℕ, ((1 : ℝ) / 2) ^ k := by
      simpa [one_div, inv_pow] using
        summable_geometric_two.sum_le_tsum
          (ehmShiftedDyadicDIndices X L) (fun k _ ↦ by positivity)
    _ = 2 := tsum_geometric_two

/-- Canonical normalized geometric weight `w_k proportional to 2^{-k}`. -/
noncomputable def ehmGeometricCorrectionWeight (X L k : ℕ) : ℝ :=
  (1 / (2 : ℝ) ^ k) / ehmGeometricCorrectionMass X L

theorem ehmGeometricCorrectionWeight_nonneg (X L k : ℕ) :
    0 ≤ ehmGeometricCorrectionWeight X L k := by
  unfold ehmGeometricCorrectionWeight
  exact div_nonneg (by positivity) (ehmGeometricCorrectionMass_pos X L).le

/-- Normalization can only decrease the raw reciprocal dyadic weight. -/
theorem ehmGeometricCorrectionWeight_le_inv_pow (X L k : ℕ) :
    ehmGeometricCorrectionWeight X L k ≤ 1 / (2 : ℝ) ^ k := by
  unfold ehmGeometricCorrectionWeight
  exact div_le_self (by positivity) (one_le_ehmGeometricCorrectionMass X L)

/-- Conversely, normalization loses at most a factor two.  Thus the
geometric allocation supplies exactly one inverse dyadic-ratio scale, up to
an absolute constant; it cannot hide arbitrarily many conductor powers. -/
theorem half_inv_pow_le_ehmGeometricCorrectionWeight (X L k : ℕ) :
    (1 / 2 : ℝ) * (1 / (2 : ℝ) ^ k) ≤
      ehmGeometricCorrectionWeight X L k := by
  unfold ehmGeometricCorrectionWeight
  have hmassPos := ehmGeometricCorrectionMass_pos X L
  have hterm : 0 ≤ 1 / (2 : ℝ) ^ k := by positivity
  calc
    (1 / 2 : ℝ) * (1 / (2 : ℝ) ^ k) =
        (1 / (2 : ℝ) ^ k) / 2 := by ring
    _ ≤ (1 / (2 : ℝ) ^ k) / ehmGeometricCorrectionMass X L := by
      exact div_le_div_of_nonneg_left hterm hmassPos
        (ehmGeometricCorrectionMass_le_two X L)

theorem sum_ehmGeometricCorrectionWeight (X L : ℕ) :
    (∑ k ∈ ehmShiftedDyadicDIndices X L,
      ehmGeometricCorrectionWeight X L k) = 1 := by
  unfold ehmGeometricCorrectionWeight ehmGeometricCorrectionMass
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (ehmGeometricCorrectionMass_pos X L))

/-- The normalized geometric correction allocation. -/
noncomputable def ehmGeometricCorrectionAllocation (X L : ℕ) :
    EhmDyadicCorrectionAllocation X L where
  weight := ehmGeometricCorrectionWeight X L
  weight_nonneg := ehmGeometricCorrectionWeight_nonneg X L
  mass_one := sum_ehmGeometricCorrectionWeight X L

/-- At the finite supremum cutoff every actual dyadic block is early, so the
geometric allocation is automatically early-supported. -/
noncomputable def ehmGeometricAllBlocksEarlySupportedAllocation (X L : ℕ) :
    EhmEarlySupportedCorrectionAllocation X L (ehmAllDyadicCutoff X L) where
  allocation := ehmGeometricCorrectionAllocation X L
  weight_eq_zero_of_late := by
    intro k hk
    have hmem := (mem_ehmLateDyadicDIndices.mp hk).1
    have hlate := (mem_ehmLateDyadicDIndices.mp hk).2
    exact False.elim (Nat.not_lt_of_ge
      (le_ehmAllDyadicCutoff_of_mem hmem) hlate)

/-- A late completed block is just the original signed Abel block because an
early-supported allocation assigns it no correction. -/
theorem ehmCorrectionCompletedDyadicAbelBlock_eq_abel_of_late
    (R1 : ℝ → ℝ) (X J M L K k : ℕ)
    (A : EhmEarlySupportedCorrectionAllocation X L K)
    (hk : k ∈ ehmLateDyadicDIndices X L K) :
    ehmCorrectionCompletedDyadicAbelBlock R1 X J M L
        A.allocation k =
      ehmShiftedDyadicAbelExpression R1 X J M L k := by
  unfold ehmCorrectionCompletedDyadicAbelBlock
  rw [A.weight_eq_zero_of_late k hk, zero_mul, add_zero]

/-- The exact correction that would cancel one Abel block is its negative. -/
noncomputable def ehmRequiredDyadicCorrectionShare
    (R1 : ℝ → ℝ) (X J M L k : ℕ) : ℝ :=
  -ehmShiftedDyadicAbelExpression R1 X J M L k

/-- A completed block is exactly the mismatch between the allocated
correction and the correction required to cancel that block.  Hence every
analytic bound below genuinely measures within-block correction coupling. -/
theorem ehmCorrectionCompletedDyadicAbelBlock_eq_mismatch
    (R1 : ℝ → ℝ) (X J M L k : ℕ)
    (A : EhmDyadicCorrectionAllocation X L) :
    ehmCorrectionCompletedDyadicAbelBlock R1 X J M L A k =
      A.weight k * ehmH15RetainedCorrection R1 X J -
        ehmRequiredDyadicCorrectionShare R1 X J M L k := by
  unfold ehmCorrectionCompletedDyadicAbelBlock
    ehmRequiredDyadicCorrectionShare
  ring

/-- Exact signed early/late reassembly.  Correction shares remain inside the
early blocks; the late part is the unmodified signed Ehm--Abel sum. -/
theorem sum_earlyCompleted_add_lateAbel_eq_coupledNearCore
    (R1 : ℝ → ℝ) (X J K : ℕ)
    (A : EhmEarlySupportedCorrectionAllocation X (ehmH15NearDMax X) K)
    (hX : 1 ≤ X) :
    (∑ k ∈ ehmEarlyDyadicDIndices X (ehmH15NearDMax X) K,
        ehmCorrectionCompletedDyadicAbelBlock R1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) A.allocation k) +
      (∑ k ∈ ehmLateDyadicDIndices X (ehmH15NearDMax X) K,
        ehmShiftedDyadicAbelExpression R1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) k) =
        ehmDyadicExplicitCoupledNearCore R1 X
          (ehmExplicitFarCutoff X) J := by
  rw [← sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
    R1 X J A.allocation hX]
  rw [← sum_ehmEarly_add_late X (ehmH15NearDMax X) K]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact (ehmCorrectionCompletedDyadicAbelBlock_eq_abel_of_late
    R1 X J (ehmH15NearMMax X) (ehmH15NearDMax X) K k A hk).symm

/-- Triangle inequality applied only after early correction completion.  In
particular, no absolute value separates an early Abel block from its share of
the main-plus-linear correction. -/
theorem abs_coupledNearCore_le_earlyCompleted_add_lateAbel
    (R1 : ℝ → ℝ) (X J K : ℕ)
    (A : EhmEarlySupportedCorrectionAllocation X (ehmH15NearDMax X) K)
    (hX : 1 ≤ X) :
    |ehmDyadicExplicitCoupledNearCore R1 X
        (ehmExplicitFarCutoff X) J| ≤
      (∑ k ∈ ehmEarlyDyadicDIndices X (ehmH15NearDMax X) K,
        |ehmCorrectionCompletedDyadicAbelBlock R1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) A.allocation k|) +
      (∑ k ∈ ehmLateDyadicDIndices X (ehmH15NearDMax X) K,
        |ehmShiftedDyadicAbelExpression R1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) k|) := by
  rw [← sum_earlyCompleted_add_lateAbel_eq_coupledNearCore
    R1 X J K A hX]
  exact (abs_add_le _ _).trans (add_le_add
    (Finset.abs_sum_le_sum_abs _ _)
    (Finset.abs_sum_le_sum_abs _ _))

/-! ## Sign coherence removes all blockwise triangle loss -/

/-- If every correction-completed block is nonnegative, the sum of block
absolute values is exactly the absolute value of the coupled near core. -/
theorem sum_abs_completed_eq_abs_coupled_of_nonneg
    (R1 : ℝ → ℝ) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X))
    (hX : 1 ≤ X)
    (hblock : ∀ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
      0 ≤ ehmCorrectionCompletedDyadicAbelBlock R1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X) A k) :
    (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
      |ehmCorrectionCompletedDyadicAbelBlock R1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X) A k|) =
      |ehmDyadicExplicitCoupledNearCore R1 X
        (ehmExplicitFarCutoff X) J| := by
  have hcore : 0 ≤ ehmDyadicExplicitCoupledNearCore R1 X
      (ehmExplicitFarCutoff X) J := by
    rw [← sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
      R1 X J A hX]
    exact Finset.sum_nonneg hblock
  rw [abs_of_nonneg hcore]
  rw [← sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
    R1 X J A hX]
  apply Finset.sum_congr rfl
  intro k hk
  rw [abs_of_nonneg (hblock k hk)]

/-- The analogous exact identity when every completed block is
nonpositive. -/
theorem sum_abs_completed_eq_abs_coupled_of_nonpos
    (R1 : ℝ → ℝ) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X))
    (hX : 1 ≤ X)
    (hblock : ∀ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
      ehmCorrectionCompletedDyadicAbelBlock R1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X) A k ≤ 0) :
    (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
      |ehmCorrectionCompletedDyadicAbelBlock R1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X) A k|) =
      |ehmDyadicExplicitCoupledNearCore R1 X
        (ehmExplicitFarCutoff X) J| := by
  have hcore : ehmDyadicExplicitCoupledNearCore R1 X
      (ehmExplicitFarCutoff X) J ≤ 0 := by
    rw [← sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
      R1 X J A hX]
    exact Finset.sum_nonpos hblock
  rw [abs_of_nonpos hcore]
  rw [← sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
    R1 X J A hX]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [abs_of_nonpos (hblock k hk)]

/-! ## The reduced geometric stop-test target -/

/-- The smallest analytic package suggested by the finite geometric-allocation
experiment.  It asks for two facts on a cofinal family of hyperbolic cutoffs:

* all geometrically completed dyadic blocks have one common sign; and
* the single signed coupled near core is `o(X)`.

Under sign coherence the first two lemmas above identify the sum of block
absolute values *exactly* with the absolute value of the coupled core.  Thus
this package does not assume a separate bound for every dyadic block.  Its
cofinal field remains an H15-strength analytic input and is not constructed in
this file. -/
structure EhmGeometricSignCoherentSublinearBound where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_sign_and_core_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      ((∀ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
          0 ≤ ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
            (ehmH15NearMMax X) (ehmH15NearDMax X)
            (ehmGeometricCorrectionAllocation X (ehmH15NearDMax X)) k) ∨
        (∀ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
          ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
            (ehmH15NearMMax X) (ehmH15NearDMax X)
            (ehmGeometricCorrectionAllocation X (ehmH15NearDMax X)) k ≤ 0)) ∧
      |ehmDyadicExplicitCoupledNearCore ehmR1 X
        (ehmExplicitFarCutoff X) J| ≤
          ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- Sign coherence converts the geometric stop-test target directly into the
existing dyadic correction-coupled decay gate, with no blockwise triangle
loss. -/
noncomputable def EhmGeometricSignCoherentSublinearBound.toDyadicDecay
    (H : EhmGeometricSignCoherentSublinearBound) :
    EhmDyadicCorrectionCoupledAbelDecay where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  allocation := fun X ↦
    ehmGeometricCorrectionAllocation X (ehmH15NearDMax X)
  cofinal_completed_block_bound X hX :=
    (H.cofinal_sign_and_core_bound X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, ?_⟩
      rcases hJ.2.1 with hnonneg | hnonpos
      · rw [sum_abs_completed_eq_abs_coupled_of_nonneg
          ehmR1 X J
          (ehmGeometricCorrectionAllocation X (ehmH15NearDMax X))
          (by omega) hnonneg]
        exact hJ.2.2
      · rw [sum_abs_completed_eq_abs_coupled_of_nonpos
          ehmR1 X J
          (ehmGeometricCorrectionAllocation X (ehmH15NearDMax X))
          (by omega) hnonpos]
        exact hJ.2.2

/-- Conditional closure for the reduced geometric target.  This theorem is
an assembly result only; the supplied package contains the unresolved signed
arithmetic estimate. -/
theorem baezDuarteCriterion_of_ehmGeometricSignCoherentSublinearBound
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmGeometricSignCoherentSublinearBound) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicCorrectionCoupledAbelDecay
    HS H.toDyadicDecay

/-! ## Per-block cancellation certificate and closure -/

/-- Exact analytic target for the early-block strategy.

For each outer cutoff `X`, `blockError X k` budgets the residual of the
*completed* `k`-th early block.  The budget is summable across the early
blocks, and its total tends to zero.  The late blocks have a separate null
majorant; because the allocation is early-supported, this late estimate does
not have to carry the correction.

The first analytic field is deliberately blockwise: it formalizes precisely
the assertion that correction coupling supplies the required cancellation
inside each early dyadic block. -/
structure EhmEarlyBlockCorrectionCoupledAnalysis where
  cutoff : ℕ → ℕ
  allocation : ∀ X : ℕ,
    EhmEarlySupportedCorrectionAllocation X (ehmH15NearDMax X) (cutoff X)
  blockError : ℕ → ℕ → ℝ
  blockError_nonneg : ∀ X k, 0 ≤ blockError X k
  etaEarly : ℕ → ℝ
  etaEarly_nonneg : ∀ X, 0 ≤ etaEarly X
  etaEarly_tendsto_zero : Tendsto etaEarly atTop (nhds 0)
  blockError_sum_le : ∀ X,
    (∑ k ∈ ehmEarlyDyadicDIndices X (ehmH15NearDMax X) (cutoff X),
      blockError X k) ≤ etaEarly X
  cofinal_early_block_mismatch_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      ∀ k ∈ ehmEarlyDyadicDIndices X (ehmH15NearDMax X) (cutoff X),
        |(allocation X).allocation.weight k *
              ehmH15RetainedCorrection ehmR1 X J -
            ehmRequiredDyadicCorrectionShare ehmR1 X J
              (ehmH15NearMMax X) (ehmH15NearDMax X) k| ≤
            ((ehmDyadicNBlock X).card : ℝ) * blockError X k
  etaLate : ℕ → ℝ
  etaLate_nonneg : ∀ X, 0 ≤ etaLate X
  etaLate_tendsto_zero : Tendsto etaLate atTop (nhds 0)
  late_uniform_bound : ∀ X : ℕ, 2 ≤ X → ∀ J : ℕ,
    ehmExplicitFarCutoff X ≤ J →
      (∑ k ∈ ehmLateDyadicDIndices X (ehmH15NearDMax X) (cutoff X),
        |ehmShiftedDyadicAbelExpression ehmR1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) k|) ≤
        ((ehmDyadicNBlock X).card : ℝ) * etaLate X

/-- The per-block early cancellation bound sums without losing its coupling
to the correction. -/
theorem EhmEarlyBlockCorrectionCoupledAnalysis.early_sum_bound
    (H : EhmEarlyBlockCorrectionCoupledAnalysis)
    (X J : ℕ) (hblocks :
      ∀ k ∈ ehmEarlyDyadicDIndices X (ehmH15NearDMax X) (H.cutoff X),
        |ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X)
          (H.allocation X).allocation k| ≤
            ((ehmDyadicNBlock X).card : ℝ) * H.blockError X k) :
    (∑ k ∈ ehmEarlyDyadicDIndices X (ehmH15NearDMax X) (H.cutoff X),
      |ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X)
        (H.allocation X).allocation k|) ≤
      ((ehmDyadicNBlock X).card : ℝ) * H.etaEarly X := by
  calc
    (∑ k ∈ ehmEarlyDyadicDIndices X (ehmH15NearDMax X) (H.cutoff X),
      |ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X)
        (H.allocation X).allocation k|) ≤
      ∑ k ∈ ehmEarlyDyadicDIndices X (ehmH15NearDMax X) (H.cutoff X),
        ((ehmDyadicNBlock X).card : ℝ) * H.blockError X k := by
          exact Finset.sum_le_sum hblocks
    _ = ((ehmDyadicNBlock X).card : ℝ) *
        (∑ k ∈ ehmEarlyDyadicDIndices X (ehmH15NearDMax X) (H.cutoff X),
          H.blockError X k) := by rw [Finset.mul_sum]
    _ ≤ ((ehmDyadicNBlock X).card : ℝ) * H.etaEarly X := by
      exact mul_le_mul_of_nonneg_left (H.blockError_sum_le X) (by positivity)

/-- Early correction cancellation plus late decay instantiate the previous
single-field dyadic Abel gate with null majorant `etaEarly + etaLate`. -/
noncomputable def EhmEarlyBlockCorrectionCoupledAnalysis.toDyadicDecay
    (H : EhmEarlyBlockCorrectionCoupledAnalysis) :
    EhmDyadicCorrectionCoupledAbelDecay where
  eta := fun X ↦ H.etaEarly X + H.etaLate X
  eta_nonneg X := add_nonneg (H.etaEarly_nonneg X) (H.etaLate_nonneg X)
  eta_tendsto_zero := by
    simpa using H.etaEarly_tendsto_zero.add H.etaLate_tendsto_zero
  allocation := fun X ↦ (H.allocation X).allocation
  cofinal_completed_block_bound X hX :=
    (H.cofinal_early_block_mismatch_bound X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, ?_⟩
      rw [← sum_ehmEarly_add_late X (ehmH15NearDMax X) (H.cutoff X)]
      have hblocks :
          ∀ k ∈ ehmEarlyDyadicDIndices X (ehmH15NearDMax X) (H.cutoff X),
            |ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
              (ehmH15NearMMax X) (ehmH15NearDMax X)
              (H.allocation X).allocation k| ≤
                ((ehmDyadicNBlock X).card : ℝ) * H.blockError X k := by
        intro k hk
        rw [ehmCorrectionCompletedDyadicAbelBlock_eq_mismatch]
        exact hJ.2 k hk
      have hearly := H.early_sum_bound X J hblocks
      have hlate := H.late_uniform_bound X hX J hJ.1
      have hlateEq :
          (∑ k ∈ ehmLateDyadicDIndices X (ehmH15NearDMax X) (H.cutoff X),
            |ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
              (ehmH15NearMMax X) (ehmH15NearDMax X)
              (H.allocation X).allocation k|) =
          ∑ k ∈ ehmLateDyadicDIndices X (ehmH15NearDMax X) (H.cutoff X),
            |ehmShiftedDyadicAbelExpression ehmR1 X J
              (ehmH15NearMMax X) (ehmH15NearDMax X) k| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ehmCorrectionCompletedDyadicAbelBlock_eq_abel_of_late
          ehmR1 X J (ehmH15NearMMax X) (ehmH15NearDMax X)
          (H.cutoff X) k (H.allocation X) hk]
      rw [hlateEq]
      calc
        (∑ k ∈ ehmEarlyDyadicDIndices X (ehmH15NearDMax X) (H.cutoff X),
            |ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
              (ehmH15NearMMax X) (ehmH15NearDMax X)
              (H.allocation X).allocation k|) +
            (∑ k ∈ ehmLateDyadicDIndices X (ehmH15NearDMax X) (H.cutoff X),
              |ehmShiftedDyadicAbelExpression ehmR1 X J
                (ehmH15NearMMax X) (ehmH15NearDMax X) k|) ≤
          ((ehmDyadicNBlock X).card : ℝ) * H.etaEarly X +
            ((ehmDyadicNBlock X).card : ℝ) * H.etaLate X :=
              add_le_add hearly hlate
        _ = ((ehmDyadicNBlock X).card : ℝ) *
            (H.etaEarly X + H.etaLate X) := by ring

/-- Final conditional closure through the already verified far-sector and
double-cofinal pipeline. -/
theorem baezDuarteCriterion_of_ehmEarlyBlockCorrectionCoupledAnalysis
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmEarlyBlockCorrectionCoupledAnalysis) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicCorrectionCoupledAbelDecay
    HS H.toDyadicDecay

end RH.Criteria.NymanBeurling.BCFLogTaperEhmEarlyBlockCorrection
