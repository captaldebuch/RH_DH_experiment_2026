import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows

/-!
# Outer-cutoff dispersion for a completed paired Ehm error

The paired additive-row identity keeps the main and near Fourier
contributions together.  A dispersion argument would still have to control
the *completed* real error obtained after that row is combined with all of
the retained correction terms.  This module isolates the elementary outer
averaging step of such an argument.

The average is over the strict dyadic block `(X, 2X]`.  A mean-square bound
for a nonnegative completed error selects one cutoff in the block at which
the error is no larger than the root-mean-square majorant.  If that majorant
tends to zero, the selected cutoffs are cofinal.

No estimate for the paired Ehm row is asserted here.  In particular, this
module does not average over harmonic frequencies and does not infer
smallness of the complete Vaaler sum from one small frequency.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedDispersion

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows

/-! ## The strict outer dyadic block -/

/-- The outer-cutoff block `(X, 2X]`.  The strict lower endpoint makes
successive powers-of-two blocks disjoint. -/
def ehmPairedDyadicNBlock (X : ℕ) : Finset ℕ :=
  Finset.Ioc X (2 * X)

theorem mem_ehmPairedDyadicNBlock_iff (X N : ℕ) :
    N ∈ ehmPairedDyadicNBlock X ↔ X < N ∧ N ≤ 2 * X := by
  simp [ehmPairedDyadicNBlock]

theorem ehmPairedDyadicNBlock_nonempty (X : ℕ) (hX : 1 ≤ X) :
    (ehmPairedDyadicNBlock X).Nonempty := by
  refine ⟨X + 1, ?_⟩
  rw [mem_ehmPairedDyadicNBlock_iff]
  omega

/-! ## Finite minimum and root-mean-square extraction -/

/-- A real-valued function on a nonempty finite set attains its minimum. -/
theorem exists_pairedError_minimizer
    (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℝ) :
    ∃ n ∈ s, ∀ m ∈ s, f n ≤ f m :=
  Finset.exists_min_image s f hs

/-- A nonnegative finite family whose mean square is at most `eta²`
contains a member at most `eta`. -/
theorem exists_mem_le_of_sum_sq_le_card_mul_sq
    (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℝ) (eta : ℝ)
    (hf : ∀ n ∈ s, 0 ≤ f n) (heta : 0 ≤ eta)
    (hmean : ∑ n ∈ s, (f n) ^ 2 ≤ (s.card : ℝ) * eta ^ 2) :
    ∃ n ∈ s, f n ≤ eta := by
  rcases exists_mem_le_of_sum_le_card_mul s hs
      (fun n ↦ (f n) ^ 2) (eta ^ 2) hmean with
    ⟨n, hn, hnsq⟩
  refine ⟨n, hn, ?_⟩
  exact (sq_le_sq₀ (hf n hn) heta).mp hnsq

/-- The minimizing member itself is bounded by the root-mean-square
majorant. -/
theorem exists_minimizer_le_of_sum_sq_le_card_mul_sq
    (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℝ) (eta : ℝ)
    (hf : ∀ n ∈ s, 0 ≤ f n) (heta : 0 ≤ eta)
    (hmean : ∑ n ∈ s, (f n) ^ 2 ≤ (s.card : ℝ) * eta ^ 2) :
    ∃ n ∈ s, f n ≤ eta ∧ ∀ m ∈ s, f n ≤ f m := by
  rcases exists_pairedError_minimizer s hs f with ⟨n, hn, hmin⟩
  rcases exists_mem_le_of_sum_sq_le_card_mul_sq
      s hs f eta hf heta hmean with ⟨m, hm, hm_eta⟩
  exact ⟨n, hn, (hmin m hm).trans hm_eta, hmin⟩

/-! ## Abstract completed-row dispersion interface -/

/-- The norm of a paired row only after its retained correction has been
added.  This small wrapper records the required order of operations: the
two complex contributions are coupled before taking a nonnegative norm. -/
noncomputable def ehmCompletedPairedRowError
    (pairedRow retainedCorrection : ℕ → ℂ) (N : ℕ) : ℝ :=
  ‖pairedRow N + retainedCorrection N‖

theorem ehmCompletedPairedRowError_nonneg
    (pairedRow retainedCorrection : ℕ → ℂ) (N : ℕ) :
    0 ≤ ehmCompletedPairedRowError pairedRow retainedCorrection N :=
  norm_nonneg _

/-- A dyadic mean-square hypothesis for a nonnegative *completed* paired
error.  The parameter `completedPairedError` is deliberately abstract: in
an analytic application it must include the paired additive row and every
correction with which that row must cancel before the norm is taken. -/
structure EhmPairedDyadicMeanSquareVanishing
    (completedPairedError : ℕ → ℝ) where
  error_nonneg : ∀ N, 0 ≤ completedPairedError N
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  square_sum_bound : ∀ X : ℕ, 1 ≤ X →
    ∑ N ∈ ehmPairedDyadicNBlock X, (completedPairedError N) ^ 2 ≤
      ((ehmPairedDyadicNBlock X).card : ℝ) * (eta X) ^ 2

/-- The norm-completed paired-row specialization of the abstract
mean-square interface.  Supplying the analytic square-sum bound remains an
explicit obligation of any application. -/
abbrev EhmCompletedPairedRowDyadicMeanSquareVanishing
    (pairedRow retainedCorrection : ℕ → ℂ) :=
  EhmPairedDyadicMeanSquareVanishing
    (ehmCompletedPairedRowError pairedRow retainedCorrection)

/-- The exact cofinal conclusion furnished by an outer mean-square
argument.  It is weaker than convergence at every cutoff. -/
structure EhmPairedErrorCofinalVanishing
    (completedPairedError : ℕ → ℝ) where
  cofinally_small : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ,
    ∃ N : ℕ, N₀ ≤ N ∧ completedPairedError N < ε

/-- At every positive dyadic scale, the mean-square hypothesis selects a
minimizing cutoff whose completed paired error is at most `eta X`. -/
theorem EhmPairedDyadicMeanSquareVanishing.exists_small_in_block
    {completedPairedError : ℕ → ℝ}
    (H : EhmPairedDyadicMeanSquareVanishing completedPairedError)
    (X : ℕ) (hX : 1 ≤ X) :
    ∃ N ∈ ehmPairedDyadicNBlock X,
      completedPairedError N ≤ H.eta X := by
  exact exists_mem_le_of_sum_sq_le_card_mul_sq
    (ehmPairedDyadicNBlock X) (ehmPairedDyadicNBlock_nonempty X hX)
    completedPairedError (H.eta X)
    (fun N _ ↦ H.error_nonneg N) (H.eta_nonneg X)
    (H.square_sum_bound X hX)

/-- A decaying dyadic mean square yields arbitrarily large cutoffs with
small completed paired error.  It does not yield `Tendsto` of the error
along all natural numbers. -/
noncomputable def EhmPairedDyadicMeanSquareVanishing.toCofinal
    {completedPairedError : ℕ → ℝ}
    (H : EhmPairedDyadicMeanSquareVanishing completedPairedError) :
    EhmPairedErrorCofinalVanishing completedPairedError where
  cofinally_small ε hε N₀ := by
    have heta_event : ∀ᶠ X : ℕ in atTop, H.eta X < ε :=
      H.eta_tendsto_zero.eventually (Iio_mem_nhds hε)
    have hX_event : ∀ᶠ X : ℕ in atTop, max N₀ 1 ≤ X :=
      eventually_ge_atTop (max N₀ 1)
    rcases (heta_event.and hX_event).exists with ⟨X, heta, hX⟩
    have hX1 : 1 ≤ X := (le_max_right N₀ 1).trans hX
    rcases H.exists_small_in_block X hX1 with ⟨N, hNmem, hNeta⟩
    have hXN : X ≤ N :=
      Nat.le_of_lt (mem_ehmPairedDyadicNBlock_iff X N |>.1 hNmem |>.1)
    exact ⟨N, (le_max_left N₀ 1).trans (hX.trans hXN),
      hNeta.trans_lt heta⟩

/-- Equivalently, every positive error threshold is met frequently at
`atTop`.  This is the filter form of cofinal subsequence smallness. -/
theorem EhmPairedDyadicMeanSquareVanishing.frequently_error_lt
    {completedPairedError : ℕ → ℝ}
    (H : EhmPairedDyadicMeanSquareVanishing completedPairedError)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ N : ℕ in atTop, completedPairedError N < ε := by
  rw [frequently_atTop]
  intro N₀
  rcases H.toCofinal.cofinally_small ε hε N₀ with ⟨N, hN₀, hN⟩
  exact ⟨N, hN₀, hN⟩

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedDispersion
