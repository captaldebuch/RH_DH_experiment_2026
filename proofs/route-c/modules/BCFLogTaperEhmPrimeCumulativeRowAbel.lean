import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowVariation

/-!
# Abel decomposition of the cumulative reciprocal-phase rows

The outer cutoff rows are numerically coherent, so taking absolute values or
applying Cauchy--Schwarz in that variable cannot provide the missing gain.
This module instead applies finite Abel summation to their exact adjacent-row
variation.  The result separates one endpoint row from a sum of small
inverse-log increments multiplying log-weighted reciprocal-phase rows.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowAbel

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativePhase
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowVariation

/-- Inclusive interval sums are shifted range sums. -/
private theorem sum_Icc_eq_sum_range_shift
    {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (A B : ℕ) (hAB : A ≤ B) :
    (∑ n ∈ Finset.Icc A B, f n) =
      ∑ i ∈ Finset.range (B - A + 1), f (A + i) := by
  apply Finset.sum_bij (fun n _ ↦ n - A)
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro a ha b hb hab
    have haA := (Finset.mem_Icc.mp ha).1
    have hbA := (Finset.mem_Icc.mp hb).1
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    refine ⟨A + i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro n hn
    rw [Nat.add_sub_of_le (Finset.mem_Icc.mp hn).1]

/-- Finite Abel summation with prefix coefficients and a terminal value. -/
private theorem sum_range_mul_eq_prefix_mul_terminal_sub_variation
    (c r : ℕ → ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), c i * r i) =
      (∑ i ∈ Finset.range (n + 1), c i) * r n -
        ∑ i ∈ Finset.range n,
          (∑ j ∈ Finset.range (i + 1), c j) * (r (i + 1) - r i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hc :
          (∑ i ∈ Finset.range ((n + 1) + 1), c i) =
            (∑ i ∈ Finset.range (n + 1), c i) + c (n + 1) :=
        Finset.sum_range_succ c (n + 1)
      have hv :
          (∑ i ∈ Finset.range (n + 1),
              (∑ j ∈ Finset.range (i + 1), c j) *
                (r (i + 1) - r i)) =
            (∑ i ∈ Finset.range n,
              (∑ j ∈ Finset.range (i + 1), c j) *
                (r (i + 1) - r i)) +
              (∑ j ∈ Finset.range (n + 1), c j) *
                (r (n + 1) - r n) :=
        Finset.sum_range_succ _ n
      calc
        (∑ i ∈ Finset.range (n.succ + 1), c i * r i) =
            (∑ i ∈ Finset.range (n + 1), c i * r i) +
              c (n + 1) * r (n + 1) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            Finset.sum_range_succ (fun i ↦ c i * r i) (n + 1)
        _ = ((∑ i ∈ Finset.range (n + 1), c i) * r n -
              ∑ i ∈ Finset.range n,
                (∑ j ∈ Finset.range (i + 1), c j) *
                  (r (i + 1) - r i)) + c (n + 1) * r (n + 1) := by
          rw [ih]
        _ = (∑ i ∈ Finset.range (n.succ + 1), c i) * r n.succ -
              ∑ i ∈ Finset.range n.succ,
                (∑ j ∈ Finset.range (i + 1), c j) *
                  (r (i + 1) - r i) := by
          simp only [Nat.succ_eq_add_one]
          rw [hc, hv]
          ring

/-- Prefix mass of the inverse-log coefficients, starting at `A`. -/
noncomputable def ehmPrimeInverseLogPrefix (A i : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (i + 1),
    ((1 / Real.log ((A + j : ℕ) : ℝ) : ℝ) : ℂ)

/-- One adjacent-row variation term after inserting the exact taper identity. -/
noncomputable def ehmPrimeTaperedRowAbelVariationTerm
    (h : ℤ) (k A i : ℕ) : ℂ :=
  ehmPrimeInverseLogPrefix A i *
    (((1 / Real.log ((A + i : ℕ) : ℝ) -
      1 / Real.log ((A + i + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
        ehmPrimeLogWeightedReciprocalPhaseRow h k (A + i))

/-- Abel form of the row sum on `[A, A+n]`. -/
noncomputable def ehmPrimeTaperedRowAbelForm
    (h : ℤ) (k A n : ℕ) : ℂ :=
  ehmPrimeInverseLogPrefix A n *
      ehmPrimeTaperedReciprocalPhaseRow h k (A + n) -
    ∑ i ∈ Finset.range n,
      ehmPrimeTaperedRowAbelVariationTerm h k A i

/-- Number of active outer-row increments at the index `k`. -/
def ehmPrimeCumulativeRowAbelLength (X k : ℕ) : ℕ :=
  min k (2 * X) - X

/-- The coherent outer-row average is exactly an endpoint row minus the
accumulated inverse-log variation. -/
theorem ehmPrimeShiftedTaperedRowSum_eq_abelForm
    (h : ℤ) (k A n : ℕ) (hA : 2 ≤ A) :
    (∑ i ∈ Finset.range (n + 1),
        ((1 / Real.log ((A + i : ℕ) : ℝ) : ℝ) : ℂ) *
          ehmPrimeTaperedReciprocalPhaseRow h k (A + i)) =
      ehmPrimeTaperedRowAbelForm h k A n := by
  rw [sum_range_mul_eq_prefix_mul_terminal_sub_variation]
  unfold ehmPrimeTaperedRowAbelForm ehmPrimeInverseLogPrefix
    ehmPrimeTaperedRowAbelVariationTerm
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [show A + (i + 1) = A + i + 1 by omega]
  rw [ehmPrimeTaperedReciprocalPhaseRow_succ_sub h k (A + i) (by omega)]
  rfl

/-- At every index after the beginning of the dyadic block, the normalized
cumulative phase is the normalized Abel endpoint-minus-variation form.  The
length stabilizes once `k` passes `2X`. -/
theorem ehmPrimeCumulativeNormalizedPhaseForm_eq_rowAbel_of_le
    (h : ℤ) (X k : ℕ) (hX : 2 ≤ X) (hXk : X ≤ k) :
    ehmPrimeCumulativeNormalizedPhaseForm h X k =
      (1 / ((((k + 1 : ℕ) : ℝ) : ℂ))) *
        ehmPrimeTaperedRowAbelForm h k X
          (ehmPrimeCumulativeRowAbelLength X k) := by
  rw [ehmPrimeCumulativeNormalizedPhaseForm_eq_taperedRows]
  let B := min k (2 * X)
  have hXB : X ≤ B := by
    dsimp [B]
    exact le_min hXk (by omega)
  have hblock :
      (ehmDyadicNBlock X).filter (fun N ↦ N ≤ k) = Finset.Icc X B := by
    ext N
    simp only [ehmDyadicNBlock, Finset.mem_filter, Finset.mem_Icc]
    dsimp [B]
    omega
  rw [hblock, sum_Icc_eq_sum_range_shift _ X B hXB]
  rw [ehmPrimeShiftedTaperedRowSum_eq_abelForm h k X (B - X) hX]
  rfl

/-- On the active half of the dyadic block, the normalized cumulative phase
is the normalized Abel endpoint-minus-variation form. -/
theorem ehmPrimeCumulativeNormalizedPhaseForm_eq_rowAbel
    (h : ℤ) (X k : ℕ) (hX : 2 ≤ X) (hXk : X ≤ k) (hk : k ≤ 2 * X) :
    ehmPrimeCumulativeNormalizedPhaseForm h X k =
      (1 / ((((k + 1 : ℕ) : ℝ) : ℂ))) *
        ehmPrimeTaperedRowAbelForm h k X (k - X) := by
  simpa [ehmPrimeCumulativeRowAbelLength, min_eq_left hk] using
    ehmPrimeCumulativeNormalizedPhaseForm_eq_rowAbel_of_le h X k hX hXk

/-- Direct norm target supplied by the exact row Abel decomposition. -/
theorem norm_ehmPrimeCumulativeNormalizedPhaseForm_le_rowAbelCost
    (h : ℤ) (X k : ℕ) (hX : 2 ≤ X) (hXk : X ≤ k) (hk : k ≤ 2 * X) :
    ‖ehmPrimeCumulativeNormalizedPhaseForm h X k‖ ≤
      ‖(1 / ((((k + 1 : ℕ) : ℝ) : ℂ)))‖ *
        (‖ehmPrimeInverseLogPrefix X (k - X) *
            ehmPrimeTaperedReciprocalPhaseRow h k k‖ +
          ∑ i ∈ Finset.range (k - X),
            ‖ehmPrimeTaperedRowAbelVariationTerm h k X i‖) := by
  rw [ehmPrimeCumulativeNormalizedPhaseForm_eq_rowAbel h X k hX hXk hk,
    norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold ehmPrimeTaperedRowAbelForm
  rw [show X + (k - X) = k by omega]
  calc
    ‖ehmPrimeInverseLogPrefix X (k - X) *
        ehmPrimeTaperedReciprocalPhaseRow h k k -
        ∑ i ∈ Finset.range (k - X),
          ehmPrimeTaperedRowAbelVariationTerm h k X i‖ ≤
      ‖ehmPrimeInverseLogPrefix X (k - X) *
        ehmPrimeTaperedReciprocalPhaseRow h k k‖ +
        ‖∑ i ∈ Finset.range (k - X),
          ehmPrimeTaperedRowAbelVariationTerm h k X i‖ :=
      norm_sub_le _ _
    _ ≤ _ := add_le_add (le_refl _) (norm_sum_le _ _)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeCumulativeRowAbel
