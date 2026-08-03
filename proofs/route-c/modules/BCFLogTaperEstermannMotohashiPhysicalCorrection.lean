import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSeed
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannKernelExtraction

/-!
# BT1-B: the explicit physical correction ledger

The extracted H15 contour kernel is not just its right-line Motohashi seed.
It also contains the left-line primal integral and the intrinsic zero residue.
This file aggregates those three pieces separately and proves the exact finite
decomposition.  No contour shift, automorphic trace formula, or decay estimate
is used.

The right-line aggregate is still paired: every coprime pair contains both
orientations.  Its normalization against the one-orientation arithmetic seed
is treated separately below, so no factor of `2` or `2π` is hidden in the
definition of the physical correction.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPhysicalCorrection

open Complex LSeries MeasureTheory
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKernelExtraction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSeed
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannBilinearTraceTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFourToTwoCollapse
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannGlobalExchange
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15MellinAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi

/-- The common finite H15 interior summation operator. -/
noncomputable def h15FiniteInteriorAggregate
    (N : ℕ) (F : ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g), F g a b

theorem h15FiniteInteriorAggregate_sub
    (N : ℕ) (F G : ℕ → ℕ → ℕ → ℂ) :
    h15FiniteInteriorAggregate N (fun g a b => F g a b - G g a b) =
      h15FiniteInteriorAggregate N F - h15FiniteInteriorAggregate N G := by
  simp only [h15FiniteInteriorAggregate, Finset.sum_sub_distrib]

theorem h15FiniteInteriorAggregate_div
    (N : ℕ) (F : ℕ → ℕ → ℕ → ℂ) (z : ℂ) :
    h15FiniteInteriorAggregate N (fun g a b => F g a b / z) =
      h15FiniteInteriorAggregate N F / z := by
  simp only [h15FiniteInteriorAggregate, Finset.sum_div]

/-- One conditional summand of the paired right-line aggregate. -/
noncomputable def estermannInteriorPairedDualSummand
    (W : ℂ → ℂ) (σR : ℝ) (N g a b : ℕ) : ℂ :=
  if hcop : Nat.Coprime a b then
    if ha : 2 ≤ a then
      if hb : 2 ≤ b then
        estermannInteriorValueCoefficient N g a b *
          estermannPairedDualKernel W σR a b hcop ha hb
      else 0
    else 0
  else 0

/-- One conditional summand of the paired left-line aggregate. -/
noncomputable def estermannInteriorPairedPrimalSummand
    (W : ℂ → ℂ) (σL : ℝ) (N g a b : ℕ) : ℂ :=
  if hcop : Nat.Coprime a b then
    if ha : 2 ≤ a then
      if hb : 2 ≤ b then
        estermannInteriorValueCoefficient N g a b *
          estermannPairedPrimalKernel W σL a b hcop ha hb
      else 0
    else 0
  else 0

/-- One conditional summand of the paired zero-residue aggregate. -/
noncomputable def estermannInteriorPairedZeroResidueSummand
    (W : ℂ → ℂ) (N g a b : ℕ) : ℂ :=
  if hcop : Nat.Coprime a b then
    if ha : 2 ≤ a then
      if hb : 2 ≤ b then
        estermannInteriorValueCoefficient N g a b *
          estermannPairedZeroResidue W a b hcop ha hb
      else 0
    else 0
  else 0

/-- One conditional summand of the already extracted kernel. -/
noncomputable def estermannInteriorExtractedSummand
    (W : ℂ → ℂ) (σL σR : ℝ) (N g a b : ℕ) : ℂ :=
  if hcop : Nat.Coprime a b then
    if ha : 2 ≤ a then
      if hb : 2 ≤ b then
        estermannInteriorValueCoefficient N g a b *
          estermannExtractedPairKernel W σL σR a b hcop ha hb
      else 0
    else 0
  else 0

theorem estermannInteriorExtractedSummand_eq_dual_sub_primal_sub_residue
    (W : ℂ → ℂ) (σL σR : ℝ) (N g a b : ℕ) :
    estermannInteriorExtractedSummand W σL σR N g a b =
      estermannInteriorPairedDualSummand W σR N g a b /
          (2 * Real.pi) -
        estermannInteriorPairedPrimalSummand W σL N g a b /
          (2 * Real.pi) -
        estermannInteriorPairedZeroResidueSummand W N g a b := by
  classical
  unfold estermannInteriorExtractedSummand
    estermannInteriorPairedDualSummand
    estermannInteriorPairedPrimalSummand
    estermannInteriorPairedZeroResidueSummand
  by_cases hcop : Nat.Coprime a b
  · by_cases ha : 2 ≤ a
    · by_cases hb : 2 ≤ b
      · simp only [dif_pos hcop, dif_pos ha, dif_pos hb,
          estermannExtractedPairKernel]
        ring
      · simp [ha, hb]
    · simp [ha]
  · simp [hcop]

/-- The complete finite aggregate of the two right-line orientations. -/
noncomputable def estermannInteriorPairedDualAggregate
    (W : ℂ → ℂ) (σR : ℝ) (N : ℕ) : ℂ :=
  h15FiniteInteriorAggregate N
    (estermannInteriorPairedDualSummand W σR N)

/-- One orientation of the normalized right-line kernel. -/
noncomputable def estermannOrientedDualKernel
    (W : ℂ → ℂ) (σR : ℝ)
    (a b : ℕ) (hcop : Nat.Coprime a b)
    (_ha : 2 ≤ a) (hb : 2 ≤ b) : ℂ := by
  letI : NeZero b := ⟨by omega⟩
  exact estermannDualVerticalIntegral
    (inverseResidueNumerator a b hcop) b
    (inverseResidueNumerator_coprime a b hcop) σR W

theorem estermannPairedDualKernel_eq_orientations
    (W : ℂ → ℂ) (σR : ℝ)
    (a b : ℕ) (hcop : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    estermannPairedDualKernel W σR a b hcop ha hb =
      estermannOrientedDualKernel W σR a b hcop ha hb +
        estermannOrientedDualKernel W σR b a hcop.symm hb ha := by
  unfold estermannPairedDualKernel estermannOrientedDualKernel
  rfl

theorem estermannInteriorValueCoefficient_comm
    (N g a b : ℕ) :
    estermannInteriorValueCoefficient N g a b =
      estermannInteriorValueCoefficient N g b a := by
  unfold estermannInteriorValueCoefficient coprimeSliceCoefficient
  push_cast
  ring

/-- The one-orientation right-line aggregate matching the ordered H15
numerator convention. -/
noncomputable def estermannInteriorOrientedDualAggregate
    (W : ℂ → ℂ) (σR : ℝ) (N : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g),
        if hcop : Nat.Coprime a b then
          if ha : 2 ≤ a then
            if hb : 2 ≤ b then
              estermannInteriorValueCoefficient N g a b *
                estermannOrientedDualKernel W σR a b hcop ha hb
            else 0
          else 0
        else 0

/-- The reverse-orientation aggregate, named to make the finite symmetry
argument independent of any integral manipulation. -/
noncomputable def estermannInteriorReverseOrientedDualAggregate
    (W : ℂ → ℂ) (σR : ℝ) (N : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g),
        if hcop : Nat.Coprime a b then
          if ha : 2 ≤ a then
            if hb : 2 ≤ b then
              estermannInteriorValueCoefficient N g a b *
                estermannOrientedDualKernel W σR b a hcop.symm hb ha
            else 0
          else 0
        else 0

/-- Expanding the paired kernel introduces exactly the two ordered
orientations. -/
theorem estermannInteriorPairedDualAggregate_eq_oriented_add_reverse
    (W : ℂ → ℂ) (σR : ℝ) (N : ℕ) :
    estermannInteriorPairedDualAggregate W σR N =
      estermannInteriorOrientedDualAggregate W σR N +
        estermannInteriorReverseOrientedDualAggregate W σR N := by
  classical
  unfold estermannInteriorPairedDualAggregate
    h15FiniteInteriorAggregate
    estermannInteriorPairedDualSummand
    estermannInteriorOrientedDualAggregate
    estermannInteriorReverseOrientedDualAggregate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hcop : Nat.Coprime a b
  · by_cases ha : 2 ≤ a
    · by_cases hb : 2 ≤ b
      · rw [dif_pos hcop, dif_pos ha, dif_pos hb,
          estermannPairedDualKernel_eq_orientations]
        simp only [dif_pos hcop, dif_pos ha, dif_pos hb]
        ring
      · simp [ha, hb]
    · simp [ha]
  · simp [hcop]

/-- Symmetry of the square H15 domain and of its coefficient identifies the
reverse orientation with the natural one. -/
theorem estermannInteriorReverseOrientedDualAggregate_eq_oriented
    (W : ℂ → ℂ) (σR : ℝ) (N : ℕ) :
    estermannInteriorReverseOrientedDualAggregate W σR N =
      estermannInteriorOrientedDualAggregate W σR N := by
  classical
  unfold estermannInteriorReverseOrientedDualAggregate
    estermannInteriorOrientedDualAggregate
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hcop : Nat.Coprime b a
  · by_cases ha : 2 ≤ a
    · by_cases hb : 2 ≤ b
      · rw [dif_pos hcop.symm, dif_pos hcop, dif_pos hb, dif_pos ha,
          dif_pos ha, dif_pos hb]
        rw [estermannInteriorValueCoefficient_comm]
      · simp [ha, hb]
    · simp [ha]
  · have hcop' : ¬Nat.Coprime a b := by
      intro hab
      exact hcop hab.symm
    simp [hcop, hcop']

/-- Consequently the paired right-line aggregate is exactly twice the
one-orientation aggregate. -/
theorem estermannInteriorPairedDualAggregate_eq_two_mul_oriented
    (W : ℂ → ℂ) (σR : ℝ) (N : ℕ) :
    estermannInteriorPairedDualAggregate W σR N =
      2 * estermannInteriorOrientedDualAggregate W σR N := by
  rw [estermannInteriorPairedDualAggregate_eq_oriented_add_reverse,
    estermannInteriorReverseOrientedDualAggregate_eq_oriented]
  ring

private theorem sum_Icc_two_eq_sum_Icc_one_of_eq_zero
    (M : ℕ) (f : ℕ → ℂ)
    (hzero : ∀ n ∈ Finset.Icc 1 M, ¬2 ≤ n → f n = 0) :
    (∑ n ∈ Finset.Icc 2 M, f n) = ∑ n ∈ Finset.Icc 1 M, f n := by
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hnOne hnTwo
    apply hzero n hnOne
    intro hn2
    exact hnTwo (Finset.mem_Icc.mpr
      ⟨hn2, (Finset.mem_Icc.mp hnOne).2⟩)

/-- The same one-orientation aggregate, with the modulus and numerator
ranges written in the natural `Icc 2` order used by the Mellin assembly. -/
noncomputable def estermannInteriorNaturalOrientedDualAggregate
    (W : ℂ → ℂ) (σR : ℝ) (N : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ b ∈ Finset.Icc 2 (N / g),
      ∑ a ∈ Finset.Icc 2 (N / g),
        if hcop : Nat.Coprime a b then
          if ha : 2 ≤ a then
            if hb : 2 ≤ b then
              estermannInteriorValueCoefficient N g a b *
                estermannOrientedDualKernel W σR a b hcop ha hb
            else 0
          else 0
        else 0

/-- Removing the two inactive endpoint rows and swapping the finite square
does not change the ordered dual aggregate. -/
theorem estermannInteriorOrientedDualAggregate_eq_natural
    (W : ℂ → ℂ) (σR : ℝ) (N : ℕ) :
    estermannInteriorOrientedDualAggregate W σR N =
      estermannInteriorNaturalOrientedDualAggregate W σR N := by
  classical
  unfold estermannInteriorOrientedDualAggregate
    estermannInteriorNaturalOrientedDualAggregate
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_comm]
  calc
    (∑ b ∈ Finset.Icc 1 (N / g),
        ∑ a ∈ Finset.Icc 1 (N / g),
          if hcop : Nat.Coprime a b then
            if ha : 2 ≤ a then
              if hb : 2 ≤ b then
                estermannInteriorValueCoefficient N g a b *
                  estermannOrientedDualKernel W σR a b hcop ha hb
              else 0
            else 0
          else 0) =
      ∑ b ∈ Finset.Icc 2 (N / g),
        ∑ a ∈ Finset.Icc 1 (N / g),
          if hcop : Nat.Coprime a b then
            if ha : 2 ≤ a then
              if hb : 2 ≤ b then
                estermannInteriorValueCoefficient N g a b *
                  estermannOrientedDualKernel W σR a b hcop ha hb
              else 0
            else 0
          else 0 := by
      symm
      apply sum_Icc_two_eq_sum_Icc_one_of_eq_zero
      intro b _ hb
      apply Finset.sum_eq_zero
      intro a _
      by_cases hcop : Nat.Coprime a b <;> simp [hcop, hb]
    _ = ∑ b ∈ Finset.Icc 2 (N / g),
        ∑ a ∈ Finset.Icc 2 (N / g),
          if hcop : Nat.Coprime a b then
            if ha : 2 ≤ a then
              if hb : 2 ≤ b then
                estermannInteriorValueCoefficient N g a b *
                  estermannOrientedDualKernel W σR a b hcop ha hb
              else 0
            else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      symm
      apply sum_Icc_two_eq_sum_Icc_one_of_eq_zero
      intro a _ ha
      by_cases hcop : Nat.Coprime a b <;> simp [hcop, ha]

/-- Absolute convergence of one ordered numerator on a Gaussian right line.
This is the local fact needed to move the finite numerator sum through the
integral; it follows from the proved four-to-two identity and the two global
`LSeries` majorants. -/
theorem integrable_estermannOrientedDualSummand_vertical
    (N g a b : ℕ) (hcop : Nat.Coprime a b)
    (_ha : 2 ≤ a) (hb : 2 ≤ b)
    (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    Integrable (fun t : ℝ =>
      estermannInteriorValueCoefficient N g a b *
        estermannGaussianEvaluationWeight η (estermannVerticalPoint c t) *
        @estermannNormalizedDualValue
          (inverseResidueNumerator a b hcop) b ⟨by omega⟩
          (inverseResidueNumerator_coprime a b hcop)
          (estermannVerticalPoint c t)) := by
  letI : NeZero b := ⟨by omega⟩
  let p := estermannPositiveDualNumerator
    (inverseResidueNumerator a b hcop) b
    (inverseResidueNumerator_coprime a b hcop)
  let n := estermannNegativeDualNumerator
    (inverseResidueNumerator a b hcop) b
    (inverseResidueNumerator_coprime a b hcop)
  have hp : Integrable (fun t : ℝ =>
      h15SameSignMellinFactor (estermannGaussianEvaluationWeight η) b
          (estermannVerticalPoint c t) *
        estermannDirichletSeries p b (estermannVerticalPoint c t)) := by
    unfold estermannDirichletSeries
    apply integrable_mul_LSeries_vertical
    · exact integrable_h15SameSignMellinFactor_vertical η c b hη hc
    · exact estermannCoeff_summable p b (by simpa using hc)
  have hn : Integrable (fun t : ℝ =>
      h15OppositeSignMellinFactor (estermannGaussianEvaluationWeight η) b
          (estermannVerticalPoint c t) *
        estermannDirichletSeries n b (estermannVerticalPoint c t)) := by
    unfold estermannDirichletSeries
    apply integrable_mul_LSeries_vertical
    · exact integrable_h15OppositeSignMellinFactor_vertical η c b hη hc
    · exact estermannCoeff_summable n b (by simpa using hc)
  have hsum := hp.add hn
  have hscaled := hsum.const_mul
    (estermannInteriorValueCoefficient N g a b)
  convert hscaled using 1
  funext t
  rw [estermannNormalizedDualValue_eq_classical_four_to_two
    (inverseResidueNumerator a b hcop) b
    (inverseResidueNumerator_coprime a b hcop)
    (by simpa [estermannVerticalPoint] using hc)]
  unfold h15SameSignMellinFactor h15OppositeSignMellinFactor
  dsimp [p, n]
  ring

/-- The integral of one natural numerator row is the corresponding finite
sum of ordered dual vertical integrals. -/
theorem integral_h15NaturalNumeratorDualIntegrand_eq_orientedRow
    (N g b : ℕ) [NeZero b] (hb : 2 ≤ b)
    (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    (∫ t : ℝ,
      h15NaturalNumeratorDualIntegrand N g b
        (estermannGaussianEvaluationWeight η)
        (estermannVerticalPoint c t)) =
      ∑ a ∈ Finset.Icc 2 (N / g),
        if hcop : Nat.Coprime a b then
          if ha : 2 ≤ a then
            if hb' : 2 ≤ b then
              estermannInteriorValueCoefficient N g a b *
                estermannOrientedDualKernel
                  (estermannGaussianEvaluationWeight η) c
                  a b hcop ha hb'
            else 0
          else 0
        else 0 := by
  classical
  unfold h15NaturalNumeratorDualIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a haMem
    have ha : 2 ≤ a := (Finset.mem_Icc.mp haMem).1
    by_cases hcop : Nat.Coprime a b
    · simp only [dif_pos hcop, dif_pos ha, dif_pos hb]
      unfold estermannOrientedDualKernel estermannDualVerticalIntegral
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    · simp [hcop]
  · intro a haMem
    have ha : 2 ≤ a := (Finset.mem_Icc.mp haMem).1
    by_cases hcop : Nat.Coprime a b
    · simp only [dif_pos hcop]
      exact integrable_estermannOrientedDualSummand_vertical
        N g a b hcop ha hb η c hη hc
    · simp [hcop]

/-- The natural one-orientation aggregate is exactly the full right-line H15
Mellin integral.  All exchanges here are finite; absolute convergence of each
row was proved above. -/
theorem estermannInteriorNaturalOrientedDualAggregate_eq_integral
    (N : ℕ) (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    estermannInteriorNaturalOrientedDualAggregate
        (estermannGaussianEvaluationWeight η) c N =
      ∫ t : ℝ,
        h15InteriorNaturalDualIntegrand N
          (estermannGaussianEvaluationWeight η)
          (estermannVerticalPoint c t) := by
  classical
  calc
    estermannInteriorNaturalOrientedDualAggregate
        (estermannGaussianEvaluationWeight η) c N =
      ∑ g ∈ Finset.Icc 1 N,
        ∑ b ∈ Finset.Icc 2 (N / g),
          if hb : 0 < b then
            ∫ t : ℝ,
              @h15NaturalNumeratorDualIntegrand N g b
                ⟨Nat.ne_of_gt hb⟩
                (estermannGaussianEvaluationWeight η)
                (estermannVerticalPoint c t)
          else 0 := by
      unfold estermannInteriorNaturalOrientedDualAggregate
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro b hbMem
      have hb2 : 2 ≤ b := (Finset.mem_Icc.mp hbMem).1
      have hb : 0 < b := lt_of_lt_of_le (by norm_num) hb2
      rw [dif_pos hb]
      exact (@integral_h15NaturalNumeratorDualIntegrand_eq_orientedRow
        N g b ⟨Nat.ne_of_gt hb⟩ hb2 η c hη hc).symm
    _ = ∑ g ∈ Finset.Icc 1 N,
        ∑ b ∈ Finset.Icc 2 (N / g),
          if hb : 0 < b then
            ∫ t : ℝ,
              @h15TwoSignAdditiveIntegrand N g b
                ⟨Nat.ne_of_gt hb⟩
                (estermannGaussianEvaluationWeight η)
                (estermannVerticalPoint c t)
          else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro b hbMem
      have hb2 : 2 ≤ b := (Finset.mem_Icc.mp hbMem).1
      have hb : 0 < b := lt_of_lt_of_le (by norm_num) hb2
      rw [dif_pos hb, dif_pos hb]
      apply integral_congr_ae
      filter_upwards [] with t
      exact @h15NaturalNumeratorDualIntegrand_eq_twoSignAdditive
        N g b ⟨Nat.ne_of_gt hb⟩
        (estermannGaussianEvaluationWeight η)
        (estermannVerticalPoint c t) (by simpa [estermannVerticalPoint] using hc)
    _ = ∫ t : ℝ,
        h15InteriorTwoSignAdditiveIntegrand N
          (estermannGaussianEvaluationWeight η)
          (estermannVerticalPoint c t) :=
      (integral_h15InteriorTwoSignAdditive_eq_rowIntegrals
        N η c hη hc).symm
    _ = ∫ t : ℝ,
        h15InteriorNaturalDualIntegrand N
          (estermannGaussianEvaluationWeight η)
          (estermannVerticalPoint c t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact (h15InteriorNaturalDualIntegrand_eq_twoSignAdditive
        N (estermannGaussianEvaluationWeight η)
        (by simpa [estermannVerticalPoint] using hc)).symm

/-- The one-orientation contour aggregate has precisely the normalization of
the canonical BT1-A arithmetic seed. -/
theorem estermannInteriorOrientedDualAggregate_eq_motohashiSeed
    (N : ℕ) (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    estermannInteriorOrientedDualAggregate
        (estermannGaussianEvaluationWeight η) c N =
      h15MotohashiArithmeticSeedAggregate N η c := by
  rw [estermannInteriorOrientedDualAggregate_eq_natural,
    estermannInteriorNaturalOrientedDualAggregate_eq_integral N η c hη hc,
    h15Interior_integral_eq_zeroCorrectedBilinearKernelAggregate
      N η c hη hc,
    ← h15MotohashiArithmeticSeedAggregate_eq_zeroCorrected]

/-- The paired `2π` contour normalization contributes exactly one factor of
`π⁻¹` to the canonical one-orientation seed. -/
theorem estermannInteriorPairedDual_div_two_pi_eq_seed_div_pi
    (N : ℕ) (η c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    estermannInteriorPairedDualAggregate
        (estermannGaussianEvaluationWeight η) c N /
        (2 * Real.pi) =
      h15MotohashiArithmeticSeedAggregate N η c / Real.pi := by
  rw [estermannInteriorPairedDualAggregate_eq_two_mul_oriented,
    estermannInteriorOrientedDualAggregate_eq_motohashiSeed N η c hη hc]
  field_simp [Real.pi_ne_zero]

/-- The complete finite aggregate of the two left-line orientations. -/
noncomputable def estermannInteriorPairedPrimalAggregate
    (W : ℂ → ℂ) (σL : ℝ) (N : ℕ) : ℂ :=
  h15FiniteInteriorAggregate N
    (estermannInteriorPairedPrimalSummand W σL N)

/-- The complete finite aggregate of the two intrinsic zero residues. -/
noncomputable def estermannInteriorPairedZeroResidueAggregate
    (W : ℂ → ℂ) (N : ℕ) : ℂ :=
  h15FiniteInteriorAggregate N
    (estermannInteriorPairedZeroResidueSummand W N)

/-- The physical completion retained after removing the right-line dual
piece: the signed left-line integral and the signed zero residue. -/
noncomputable def h15MotohashiExplicitPhysicalCorrection
    (W : ℂ → ℂ) (σL : ℝ) (N : ℕ) : ℂ :=
  -(estermannInteriorPairedPrimalAggregate W σL N) /
      (2 * Real.pi) -
    estermannInteriorPairedZeroResidueAggregate W N

/-- Exact finite contour ledger.  In particular, the primal and zero-residue
terms have not been discarded or estimated separately. -/
theorem estermannInteriorExtractedKernelAggregate_eq_pairedDual_add_correction
    (W : ℂ → ℂ) (σL σR : ℝ) (N : ℕ) :
    estermannInteriorExtractedKernelAggregate W σL σR N =
      estermannInteriorPairedDualAggregate W σR N /
          (2 * Real.pi) +
        h15MotohashiExplicitPhysicalCorrection W σL N := by
  classical
  unfold h15MotohashiExplicitPhysicalCorrection
    estermannInteriorPairedDualAggregate
    estermannInteriorPairedPrimalAggregate
    estermannInteriorPairedZeroResidueAggregate
  change h15FiniteInteriorAggregate N
      (estermannInteriorExtractedSummand W σL σR N) = _
  have hfun : estermannInteriorExtractedSummand W σL σR N =
      fun g a b =>
        estermannInteriorPairedDualSummand W σR N g a b /
            (2 * Real.pi) -
          estermannInteriorPairedPrimalSummand W σL N g a b /
            (2 * Real.pi) -
          estermannInteriorPairedZeroResidueSummand W N g a b := by
    funext g a b
    exact estermannInteriorExtractedSummand_eq_dual_sub_primal_sub_residue
      W σL σR N g a b
  rw [hfun]
  rw [h15FiniteInteriorAggregate_sub, h15FiniteInteriorAggregate_sub,
    h15FiniteInteriorAggregate_div, h15FiniteInteriorAggregate_div]
  ring

/-- BT1-B closure: after the global normalization is proved, the extracted
kernel is exactly the `π⁻¹`-normalized canonical Motohashi seed plus the
explicit physical correction. -/
theorem estermannInteriorExtractedKernelAggregate_eq_seed_div_pi_add_correction
    (N : ℕ) (η σL c : ℝ) (hη : 0 < η) (hc : 1 < c) :
    estermannInteriorExtractedKernelAggregate
        (estermannGaussianEvaluationWeight η) σL c N =
      h15MotohashiArithmeticSeedAggregate N η c / Real.pi +
        h15MotohashiExplicitPhysicalCorrection
          (estermannGaussianEvaluationWeight η) σL N := by
  rw [estermannInteriorExtractedKernelAggregate_eq_pairedDual_add_correction,
    estermannInteriorPairedDual_div_two_pi_eq_seed_div_pi N η c hη hc]

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPhysicalCorrection
