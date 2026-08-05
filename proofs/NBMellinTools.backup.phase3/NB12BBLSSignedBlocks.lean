/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSRowTailBound

/-!
# NB12c: signed dyadic blocks for the BBLS bilinear tail

The quantitative fixed-row estimate in `NB12BBLSRowTailBound` loses too much
when it is inserted term by term.  This file therefore partitions the exact
BBLS bilinear tail into dyadic rectangles while retaining the two signed
coefficients and both moving moduli inside every block.

The partition and reassembly theorem are finite identities.  The final
structure is the precise next analytic interface: each *complete signed
block* may be bounded by a nonnegative envelope, and only the sum of those
envelopes is required to have log-power decay.
-/

open Filter
open scoped BigOperators Topology

namespace NBMellinTools.NB12

open NBMellinTools.NB8

/-! ## Canonical dyadic rectangles -/

/-- Dyadic coordinate of the positive denominator represented by `j : Fin N`.
The underlying denominator is `j.val + 1`, so it is never zero. -/
def bblsDyadicIndex {N : ℕ} (j : Fin N) : ℕ :=
  Nat.log2 (j.val + 1)

/-- Pair of dyadic coordinates attached to a pair of moving moduli. -/
def bblsDyadicIndexPair {N : ℕ} (jk : Fin N × Fin N) : ℕ × ℕ :=
  (bblsDyadicIndex jk.1, bblsDyadicIndex jk.2)

/-- The finite set of dyadic rectangles actually met by the square of
denominators `1, ..., N`. -/
def bblsDyadicIndexPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.univ : Finset (Fin N)).product
      (Finset.univ : Finset (Fin N))).image bblsDyadicIndexPair

/-- The rectangle with dyadic coordinate `rs`. -/
def bblsDyadicPairBlock (N : ℕ) (rs : ℕ × ℕ) :
    Finset (Fin N × Fin N) :=
  ((Finset.univ : Finset (Fin N)).product
      (Finset.univ : Finset (Fin N))).filter
    (fun jk => bblsDyadicIndexPair jk = rs)

theorem mem_bblsDyadicPairBlock
    {N : ℕ} {rs : ℕ × ℕ} {jk : Fin N × Fin N} :
    jk ∈ bblsDyadicPairBlock N rs ↔ bblsDyadicIndexPair jk = rs := by
  simp [bblsDyadicPairBlock]

/-- Membership in a dyadic rectangle gives the expected support bounds for
both positive denominator coordinates. -/
theorem dyadic_support_of_mem_bblsDyadicPairBlock
    {N : ℕ} {rs : ℕ × ℕ} {jk : Fin N × Fin N}
    (hjk : jk ∈ bblsDyadicPairBlock N rs) :
    2 ^ rs.1 ≤ jk.1.val + 1 ∧ jk.1.val + 1 < 2 ^ (rs.1 + 1) ∧
      2 ^ rs.2 ≤ jk.2.val + 1 ∧ jk.2.val + 1 < 2 ^ (rs.2 + 1) := by
  have hrs := mem_bblsDyadicPairBlock.mp hjk
  have hr : bblsDyadicIndex jk.1 = rs.1 := congrArg Prod.fst hrs
  have hs : bblsDyadicIndex jk.2 = rs.2 := congrArg Prod.snd hrs
  have hjpos : jk.1.val + 1 ≠ 0 := by omega
  have hkpos : jk.2.val + 1 ≠ 0 := by omega
  constructor
  · rw [← hr]
    exact Nat.log2_self_le hjpos
  constructor
  · rw [← hr]
    exact Nat.lt_log2_self
  constructor
  · rw [← hs]
    exact Nat.log2_self_le hkpos
  · rw [← hs]
    exact Nat.lt_log2_self

/-! ## Signed block sums and exact reassembly -/

/-- One ordered summand of the exact symmetric BBLS bilinear tail. -/
noncomputable def bblsCotangentBilinearSummand
    {N : ℕ} (coeffs : Fin N → ℝ) (M : ℕ) (jk : Fin N × Fin N) : ℝ :=
  coeffs jk.1 * coeffs jk.2 *
    (-Real.pi /
        (2 * ((jk.1.val + 1 : ℕ) : ℝ) * ((jk.2.val + 1 : ℕ) : ℝ)) *
      (bblsCotangentRowTail (jk.1.val + 1) (jk.2.val + 1) M +
        bblsCotangentRowTail (jk.2.val + 1) (jk.1.val + 1) M))

/-- The complete signed contribution of one dyadic rectangle.  No absolute
value is taken inside this definition. -/
noncomputable def bblsCotangentBilinearDyadicBlock
    (N : ℕ) (coeffs : Fin N → ℝ) (M : ℕ) (rs : ℕ × ℕ) : ℝ :=
  ∑ jk ∈ bblsDyadicPairBlock N rs,
    bblsCotangentBilinearSummand coeffs M jk

/-- The dyadic fibers reassemble any finite sum over the square exactly. -/
theorem sum_bblsDyadicPairBlocks
    {R : Type*} [AddCommMonoid R] (N : ℕ) (f : Fin N × Fin N → R) :
    (∑ rs ∈ bblsDyadicIndexPairs N,
      ∑ jk ∈ bblsDyadicPairBlock N rs, f jk) =
        ∑ jk ∈ (Finset.univ : Finset (Fin N)).product
          (Finset.univ : Finset (Fin N)), f jk := by
  classical
  unfold bblsDyadicIndexPairs bblsDyadicPairBlock
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · ext jk
    simp
  · intro jk _
    rfl

/-- Exact signed dyadic reassembly of the complete BBLS bilinear tail. -/
theorem bblsCotangentBilinearTail_eq_sum_dyadicBlocks
    (N : ℕ) (coeffs : Fin N → ℝ) (M : ℕ) :
  bblsCotangentBilinearTail N coeffs M =
      ∑ rs ∈ bblsDyadicIndexPairs N,
        bblsCotangentBilinearDyadicBlock N coeffs M rs := by
  classical
  unfold bblsCotangentBilinearDyadicBlock
  rw [sum_bblsDyadicPairBlocks]
  unfold bblsCotangentBilinearTail bblsCotangentBilinearSummand
  rw [← Finset.sum_product']
  rfl

/-! ## The genuine signed-block analytic interface -/

/-- A summable envelope for complete signed dyadic rectangles.  This is
strictly more structured than a bound on the already assembled tail: the
first field must control every explicit rectangle, while the second must
show that the total envelope has log-power decay. -/
structure BBLSSignedDyadicBlockLogEstimate where
  envelope : ℕ → ℕ × ℕ → ℝ
  envelope_nonneg : ∀ n rs, 0 ≤ envelope n rs
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  block_bound : ∀ (n : ℕ) (rs : ℕ × ℕ),
    rs ∈ bblsDyadicIndexPairs (logTaperLength n) →
    |bblsCotangentBilinearDyadicBlock
        (logTaperLength n) (logTaperCoeffs n) (vaalerModeCutoff n) rs| ≤
      envelope n rs
  envelope_sum_bound : ∀ n : ℕ,
    (∑ rs ∈ bblsDyadicIndexPairs (logTaperLength n), envelope n rs) ≤
      C / (Real.log (((n + 2 : ℕ) : ℝ))) ^ α

/-- Summable signed dyadic control supplies the exact BBLS bilinear-tail
estimate required by NB12. -/
noncomputable def BBLSSignedDyadicBlockLogEstimate.toBBLSBilinearTailLogEstimate
    (H : BBLSSignedDyadicBlockLogEstimate) : BBLSBilinearTailLogEstimate where
  C := H.C
  C_pos := H.C_pos
  α := H.α
  α_pos := H.α_pos
  bound n := by
    rw [bblsCotangentBilinearTail_eq_sum_dyadicBlocks]
    calc
      |∑ rs ∈ bblsDyadicIndexPairs (logTaperLength n),
          bblsCotangentBilinearDyadicBlock
            (logTaperLength n) (logTaperCoeffs n) (vaalerModeCutoff n) rs| ≤
          ∑ rs ∈ bblsDyadicIndexPairs (logTaperLength n),
            |bblsCotangentBilinearDyadicBlock
              (logTaperLength n) (logTaperCoeffs n) (vaalerModeCutoff n) rs| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ rs ∈ bblsDyadicIndexPairs (logTaperLength n),
          H.envelope n rs := by
        apply Finset.sum_le_sum
        intro rs hrs
        exact H.block_bound n rs hrs
      _ ≤ H.C / (Real.log (((n + 2 : ℕ) : ℝ))) ^ H.α :=
        H.envelope_sum_bound n

/-- The signed dyadic block estimate closes the active Fourier-remainder
gate. -/
theorem fourierRemainderDecay_of_signedDyadicBlockLogEstimate
    (H : BBLSSignedDyadicBlockLogEstimate) : FourierRemainderDecay :=
  fourierRemainderDecay_of_bblsBilinearTailLogEstimate
    H.toBBLSBilinearTailLogEstimate

end NBMellinTools.NB12
