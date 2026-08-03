import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmRectangularInstantiation

/-!
# Dyadic correction-coupled Abel localization for the Ehm near core

This file performs the next finite step after the exact shifted-rectangle
instantiation.  The actual divisor `d=X+1+j` is partitioned by the anchored
dyadic index `log2 (d/(X+1))`.  On every block we retain the pure Mobius
signs inside the coefficient and the complete taper--reciprocal--`R1`
expression inside the kernel.

The main and linear terms have no canonical `(m,d)` cell coordinates.  We
therefore introduce a nonnegative unit-mass allocation of their *combined
signed value* among the dyadic blocks.  The allocation has total mass one,
so the sum of the completed blocks is exactly the original coupled near
core.  A neutral cardinality allocation is supplied as a baseline, without
claiming that it models the observed early-block correction.  No constituent
is bounded separately.

The last structure in the file isolates the remaining analytic theorem:
the sum of the absolute values of the correction-completed signed Abel
blocks must be `o(X)`.  All results before that structure are finite
identities or unconditional triangle-inequality bounds.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbolicKernelNormalForm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularInstantiation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge

/-! ## Canonical dyadic partition of the shifted divisor coordinate -/

/-- Dyadic index of the actual divisor `d = X+1+j`, measured relative to
the first divisor `X+1`.  Thus block `k` is the anchored interval where
`d/(X+1)` lies between `2^k` and `2^(k+1)`. -/
def ehmShiftedDyadicDIndex (X j : ℕ) : ℕ :=
  Nat.log2 ((X + 1 + j) / (X + 1))

/-- The finite set of dyadic indices actually met by `[0,L]`. -/
def ehmShiftedDyadicDIndices (X L : ℕ) : Finset ℕ :=
  (Finset.range (L + 1)).image (ehmShiftedDyadicDIndex X)

/-- The `k`-th dyadic fiber in the shifted divisor coordinate. -/
def ehmShiftedDyadicDBlock (X L k : ℕ) : Finset ℕ :=
  (Finset.range (L + 1)).filter
    (fun j ↦ ehmShiftedDyadicDIndex X j = k)

theorem mem_ehmShiftedDyadicDBlock
    {X L k j : ℕ} :
    j ∈ ehmShiftedDyadicDBlock X L k ↔
      j ≤ L ∧ ehmShiftedDyadicDIndex X j = k := by
  simp [ehmShiftedDyadicDBlock]

/-- Membership in the `k`-th fiber has the expected anchored dyadic support. -/
theorem dyadic_support_of_mem_ehmShiftedDyadicDBlock
    {X L k j : ℕ} (hj : j ∈ ehmShiftedDyadicDBlock X L k) :
    2 ^ k ≤ (X + 1 + j) / (X + 1) ∧
      (X + 1 + j) / (X + 1) < 2 ^ (k + 1) := by
  have hk := (mem_ehmShiftedDyadicDBlock.mp hj).2
  subst k
  have hquot : (X + 1 + j) / (X + 1) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos (by omega) (by omega))
  exact ⟨Nat.log2_self_le hquot, Nat.lt_log2_self⟩

/-- The dyadic fibers form an exact partition of the shifted interval. -/
theorem sum_ehmShiftedDyadicDBlocks
    (X L : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ ehmShiftedDyadicDIndices X L,
      ∑ j ∈ ehmShiftedDyadicDBlock X L k, f j) =
        ∑ j ∈ Finset.range (L + 1), f j := by
  classical
  unfold ehmShiftedDyadicDIndices ehmShiftedDyadicDBlock
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · exact fun h ↦ h.1
    · intro hj
      exact ⟨hj, j, hj, rfl⟩
  · intro j _
    rfl

/-! ## Localized signs, sums, and exact reassembly -/

/-- The shifted Mobius pair restricted to one dyadic `d`-fiber. -/
noncomputable def ehmShiftedDyadicArithmeticCoeff
    (X k i j : ℕ) : ℝ :=
  if ehmShiftedDyadicDIndex X j = k then
    ehmShiftedNearArithmeticCoeff X i j
  else 0

/-- One signed dyadic divisor block, with the full complete kernel retained. -/
noncomputable def ehmShiftedDyadicNearBlockSum
    (R1 : ℝ → ℝ) (X J M L k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (L + 1),
    ehmShiftedDyadicArithmeticCoeff X k i j *
      ehmShiftedNearCompleteKernel R1 X J i j

/-- A dyadic block is equivalently the sum over its explicit filtered
coordinate set. -/
theorem ehmShiftedDyadicNearBlockSum_eq_filter
    (R1 : ℝ → ℝ) (X J M L k : ℕ) :
    ehmShiftedDyadicNearBlockSum R1 X J M L k =
      ∑ i ∈ Finset.range (M + 1),
        ∑ j ∈ ehmShiftedDyadicDBlock X L k,
          ehmShiftedNearArithmeticCoeff X i j *
            ehmShiftedNearCompleteKernel R1 X J i j := by
  classical
  unfold ehmShiftedDyadicNearBlockSum ehmShiftedDyadicArithmeticCoeff
    ehmShiftedDyadicDBlock
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j ∈ Finset.range (L + 1),
        (if ehmShiftedDyadicDIndex X j = k then
          ehmShiftedNearArithmeticCoeff X i j else 0) *
          ehmShiftedNearCompleteKernel R1 X J i j) =
        ∑ j ∈ Finset.range (L + 1),
          if ehmShiftedDyadicDIndex X j = k then
            ehmShiftedNearArithmeticCoeff X i j *
              ehmShiftedNearCompleteKernel R1 X J i j
          else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : ehmShiftedDyadicDIndex X j = k <;> simp [hj]
    _ = ∑ j ∈ (Finset.range (L + 1)).filter
          (fun j ↦ ehmShiftedDyadicDIndex X j = k),
          ehmShiftedNearArithmeticCoeff X i j *
            ehmShiftedNearCompleteKernel R1 X J i j := by
          rw [Finset.sum_filter]

/-- Summing all dyadic fibers recovers the exact shifted near rectangle. -/
theorem sum_ehmShiftedDyadicNearBlockSum
    (R1 : ℝ → ℝ) (X J M L : ℕ) :
    (∑ k ∈ ehmShiftedDyadicDIndices X L,
      ehmShiftedDyadicNearBlockSum R1 X J M L k) =
        ehmShiftedNearRectangularSum R1 X J M L := by
  classical
  simp_rw [ehmShiftedDyadicNearBlockSum_eq_filter]
  rw [Finset.sum_comm]
  unfold ehmShiftedNearRectangularSum
  apply Finset.sum_congr rfl
  intro i _
  exact sum_ehmShiftedDyadicDBlocks X L (fun j ↦
    ehmShiftedNearArithmeticCoeff X i j *
      ehmShiftedNearCompleteKernel R1 X J i j)

/-! ## Exact block discrepancy and Abel expressions -/

/-- Shifted Mertens increment restricted to one dyadic divisor fiber. -/
noncomputable def ehmShiftedDyadicMertensPrefix
    (X k K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1),
    if ehmShiftedDyadicDIndex X j = k then
      ((ArithmeticFunction.moebius (X + 1 + j) : ℤ) : ℝ)
    else 0

/-- Every localized rectangular prefix still factors exactly.  Only the
second factor changes: it is now a Mertens increment inside one dyadic
fiber. -/
theorem rectangularPrefix_ehmShiftedDyadicArithmeticCoeff
    (X k i j : ℕ) :
    rectangularPrefix (ehmShiftedDyadicArithmeticCoeff X k) i j =
      ehmShiftedMertensPrefix 1 i *
        ehmShiftedDyadicMertensPrefix X k j := by
  classical
  unfold rectangularPrefix ehmShiftedDyadicArithmeticCoeff
    ehmShiftedNearArithmeticCoeff ehmShiftedMertensPrefix
    ehmShiftedDyadicMertensPrefix
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : ehmShiftedDyadicDIndex X v = k <;>
    simp [hv, Nat.add_comm u 1]

/-- Exact absolute discrepancy factor on one dyadic block. -/
theorem abs_rectangularPrefix_ehmShiftedDyadicArithmeticCoeff
    (X k i j : ℕ) :
    |rectangularPrefix (ehmShiftedDyadicArithmeticCoeff X k) i j| =
      |ehmShiftedMertensPrefix 1 i| *
        |ehmShiftedDyadicMertensPrefix X k j| := by
  rw [rectangularPrefix_ehmShiftedDyadicArithmeticCoeff, abs_mul]

/-- The unconditional baseline still pays the enclosing prefix area.  The
dyadic localization becomes useful only after an arithmetic estimate for
the restricted Mertens increment is inserted. -/
theorem abs_rectangularPrefix_ehmShiftedDyadicArithmeticCoeff_le_area
    (X k i j : ℕ) :
    |rectangularPrefix (ehmShiftedDyadicArithmeticCoeff X k) i j| ≤
      ((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
  rw [abs_rectangularPrefix_ehmShiftedDyadicArithmeticCoeff]
  apply mul_le_mul
  · exact abs_ehmShiftedMertensPrefix_le_length 1 i
  · unfold ehmShiftedDyadicMertensPrefix
    calc
      |∑ v ∈ Finset.range (j + 1),
          if ehmShiftedDyadicDIndex X v = k then
            ((ArithmeticFunction.moebius (X + 1 + v) : ℤ) : ℝ)
          else 0| ≤
          ∑ v ∈ Finset.range (j + 1),
            |if ehmShiftedDyadicDIndex X v = k then
              ((ArithmeticFunction.moebius (X + 1 + v) : ℤ) : ℝ)
            else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ Finset.range (j + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro v _
        split_ifs
        · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
            (n := X + 1 + v)
        · norm_num
      _ = (j + 1 : ℕ) := by simp
  · positivity
  · positivity

/-- The signed four-piece Abel expression for one dyadic block. -/
noncomputable def ehmShiftedDyadicAbelExpression
    (R1 : ℝ → ℝ) (X J M L k : ℕ) : ℝ :=
  rectangularPrefix (ehmShiftedDyadicArithmeticCoeff X k) M L *
      ehmShiftedNearCompleteKernel R1 X J M L +
    (∑ i ∈ Finset.range M,
      rectangularPrefix (ehmShiftedDyadicArithmeticCoeff X k) i L *
        firstForwardDifference
          (ehmShiftedNearCompleteKernel R1 X J) i L) +
    (∑ j ∈ Finset.range L,
      rectangularPrefix (ehmShiftedDyadicArithmeticCoeff X k) M j *
        secondForwardDifference
          (ehmShiftedNearCompleteKernel R1 X J) M j) +
    ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range L,
      rectangularPrefix (ehmShiftedDyadicArithmeticCoeff X k) i j *
        mixedForwardDifference
          (ehmShiftedNearCompleteKernel R1 X J) i j

theorem ehmShiftedDyadicNearBlockSum_eq_abel
    (R1 : ℝ → ℝ) (X J M L k : ℕ) :
    ehmShiftedDyadicNearBlockSum R1 X J M L k =
      ehmShiftedDyadicAbelExpression R1 X J M L k := by
  exact rectangularAbel_identity
    (ehmShiftedDyadicArithmeticCoeff X k)
    (ehmShiftedNearCompleteKernel R1 X J) M L

/-- Sharpest unconditional block estimate supplied by the present finite
machinery: every localized prefix remains paired with the kernel difference
at the same coordinate. -/
theorem abs_ehmShiftedDyadicNearBlockSum_le_weightedAbelCost
    (R1 : ℝ → ℝ) (X J M L k : ℕ) :
    |ehmShiftedDyadicNearBlockSum R1 X J M L k| ≤
      rectangularWeightedTransferCost
        (ehmShiftedDyadicArithmeticCoeff X k)
        (ehmShiftedNearCompleteKernel R1 X J) M L := by
  exact abs_rectangularSum_le_weightedTransferCost
    (ehmShiftedDyadicArithmeticCoeff X k)
    (ehmShiftedNearCompleteKernel R1 X J) M L

/-- A block discrepancy bound `B` transfers directly against the complete
kernel variation.  This is the insertion point for a localized Mertens
estimate. -/
theorem abs_ehmShiftedDyadicNearBlockSum_le_discrepancy_mul_variation
    (R1 : ℝ → ℝ) (X J M L k : ℕ) (B : ℝ)
    (hB : ∀ i ≤ M, ∀ j ≤ L,
      |ehmShiftedMertensPrefix 1 i| *
        |ehmShiftedDyadicMertensPrefix X k j| ≤ B) :
    |ehmShiftedDyadicNearBlockSum R1 X J M L k| ≤
      B * rectangularVariation
        (ehmShiftedNearCompleteKernel R1 X J) M L := by
  apply abs_rectangularSum_le_discrepancy_mul_variation
  intro i hi j hj
  rw [abs_rectangularPrefix_ehmShiftedDyadicArithmeticCoeff]
  exact hB i hi j hj

/-! ## Signed allocation interface for the retained correction -/

/-- The full main plus linear correction, with its internal sign retained. -/
noncomputable def ehmH15RetainedCorrection
    (R1 : ℝ → ℝ) (X J : ℕ) : ℝ :=
  ehmDyadicFullMainJointSum R1 X J +
    ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N

/-- A signed correction allocation is a nonnegative partition of unit mass
over the dyadic divisor blocks.  Its weights multiply the already combined
signed main-plus-linear correction; the main and linear pieces are never
split from one another.

An allocation used in the analytic decay structure below may depend on `X`
but not on the hyperbolic cutoff `J`.  This prevents a new allocation from
being selected separately for every oscillatory sum. -/
structure EhmDyadicCorrectionAllocation (X L : ℕ) where
  weight : ℕ → ℝ
  weight_nonneg : ∀ k, 0 ≤ weight k
  mass_one : (∑ k ∈ ehmShiftedDyadicDIndices X L, weight k) = 1

/-- Neutral baseline weight: the proportion of shifted divisor cells in
the block.  It is canonical as a counting measure, but it is not claimed to
be the analytically optimal correction allocation. -/
noncomputable def ehmCardinalityCorrectionWeight (X L k : ℕ) : ℝ :=
  ((ehmShiftedDyadicDBlock X L k).card : ℝ) / ((L + 1 : ℕ) : ℝ)

theorem ehmCardinalityCorrectionWeight_nonneg (X L k : ℕ) :
    0 ≤ ehmCardinalityCorrectionWeight X L k := by
  unfold ehmCardinalityCorrectionWeight
  positivity

/-- The neutral cardinality weights have total mass exactly one. -/
theorem sum_ehmCardinalityCorrectionWeight (X L : ℕ) :
    (∑ k ∈ ehmShiftedDyadicDIndices X L,
      ehmCardinalityCorrectionWeight X L k) = 1 := by
  have hcardR :
      (∑ k ∈ ehmShiftedDyadicDIndices X L,
        ((ehmShiftedDyadicDBlock X L k).card : ℝ)) =
          ((L + 1 : ℕ) : ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_range] using
        (sum_ehmShiftedDyadicDBlocks X L (fun _ ↦ (1 : ℝ)))
  unfold ehmCardinalityCorrectionWeight
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, hcardR]
  exact mul_inv_cancel₀ (by positivity)

/-- The neutral, cardinality-proportional correction allocation. -/
noncomputable def ehmNeutralCardinalityCorrectionAllocation (X L : ℕ) :
    EhmDyadicCorrectionAllocation X L where
  weight := ehmCardinalityCorrectionWeight X L
  weight_nonneg := ehmCardinalityCorrectionWeight_nonneg X L
  mass_one := sum_ehmCardinalityCorrectionWeight X L

/-- One Abel-localized block after attaching an allocation's share of the
*combined* main and linear correction. -/
noncomputable def ehmCorrectionCompletedDyadicAbelBlock
    (R1 : ℝ → ℝ) (X J M L : ℕ)
    (A : EhmDyadicCorrectionAllocation X L) (k : ℕ) : ℝ :=
  ehmShiftedDyadicAbelExpression R1 X J M L k +
    A.weight k * ehmH15RetainedCorrection R1 X J

/-- Exact correction-coupled reassembly at the proved H15 cutoff. -/
theorem sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
    (R1 : ℝ → ℝ) (X J : ℕ)
    (A : EhmDyadicCorrectionAllocation X (ehmH15NearDMax X))
    (hX : 1 ≤ X) :
    (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
      ehmCorrectionCompletedDyadicAbelBlock R1 X J
        (ehmH15NearMMax X) (ehmH15NearDMax X) A k) =
      ehmDyadicExplicitCoupledNearCore R1 X
        (ehmExplicitFarCutoff X) J := by
  classical
  unfold ehmCorrectionCompletedDyadicAbelBlock
  rw [Finset.sum_add_distrib]
  simp_rw [← ehmShiftedDyadicNearBlockSum_eq_abel]
  rw [sum_ehmShiftedDyadicNearBlockSum,
    ← Finset.sum_mul, A.mass_one, one_mul]
  rw [ehmDyadicExplicitCutoffCoupledNearCore_eq_main_add_shifted_add_remainder
    R1 X J hX]
  unfold ehmH15RetainedCorrection
  ring

/-! ## The exact remaining WP2.4--2.6 decay field -/

/-- Sufficient dyadic correction-coupled Abel estimate at the explicit
polynomial cutoff.  Crucially, the absolute value is taken only *after* the
signed Abel block and its main/linear correction share are recombined.

The right side is `o(X)` because the outer dyadic block has cardinality
comparable to `X` and `eta X → 0`.  Constructing this structure is the
remaining analytic step; it is not asserted here. -/
structure EhmDyadicCorrectionCoupledAbelDecay where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  allocation : ∀ X : ℕ,
    EhmDyadicCorrectionAllocation X (ehmH15NearDMax X)
  cofinal_completed_block_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      (∑ k ∈ ehmShiftedDyadicDIndices X (ehmH15NearDMax X),
        |ehmCorrectionCompletedDyadicAbelBlock ehmR1 X J
          (ehmH15NearMMax X) (ehmH15NearDMax X) (allocation X) k|) ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- The blockwise decay field implies the required absolute bound for the
complete explicit-cutoff coupled near core. -/
theorem EhmDyadicCorrectionCoupledAbelDecay.coupledNearCore_bound
    (H : EhmDyadicCorrectionCoupledAbelDecay) (X : ℕ) (hX : 2 ≤ X) :
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |ehmDyadicExplicitCoupledNearCore ehmR1 X
        (ehmExplicitFarCutoff X) J| ≤
          ((ehmDyadicNBlock X).card : ℝ) * H.eta X := by
  exact (H.cofinal_completed_block_bound X hX).mono fun J hJ ↦ by
    refine ⟨hJ.1, ?_⟩
    rw [← sum_ehmCorrectionCompletedDyadicAbelBlock_eq_coupledNearCore
      ehmR1 X J (H.allocation X) (by omega)]
    exact (Finset.abs_sum_le_sum_abs _ _).trans hJ.2

/-- The single localized Abel decay field instantiates the existing explicit
kernel gate.  Choosing `U=2X` makes the Type-II interval empty but, more
importantly, uses an already proved exact Type-I/II identity; the explicit
far-sector package is then recombined by `toCommonSplit`. -/
noncomputable def EhmDyadicCorrectionCoupledAbelDecay.toKernelGate
    (H : EhmDyadicCorrectionCoupledAbelDecay) :
    EhmDyadicExplicitKernelCoupledAnalyticGate where
  U := fun X ↦ 2 * X
  U_le := fun _ ↦ le_rfl
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  cofinal_bound X hX :=
    (H.coupledNearCore_bound X hX).mono fun J hJ ↦ by
      refine ⟨hJ.1, ?_⟩
      rw [← ehmDyadicExplicitCutoffCoupledNearCore_eq_kernelTypeI_typeII
        ehmR1 X J (2 * X) le_rfl]
      exact (le_abs_self _).trans hJ.2

/-- Conditional WP2 closure, including the already proved explicit far
tail.  The only new analytic assumption is the correction-coupled localized
Abel decay structure above. -/
theorem baezDuarteCriterion_of_ehmDyadicCorrectionCoupledAbelDecay
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicCorrectionCoupledAbelDecay) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicExplicitKernelCoupledAnalyticGate
    HS H.toKernelGate

end RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCorrectionAbel
