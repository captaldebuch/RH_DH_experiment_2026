import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmQGeTwoCollapse
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTVariation

/-!
# Cutoff-separated additive-ratio form of the collapsed Ehm sector

The `q ≥ 2` collapse leaves a signed bilinear kernel at the ratio `d / m`.
Although that kernel is genuinely joint in `(d,m)`, its logarithmic taper
coefficient separates exactly after restoring the finite outer cutoff `N`.

This is the correct point at which to compare H15 with the literature on
bilinear exponential sums.  The resulting Fourier phases are ordinary
additive ratios `exp(2*pi*i*h*d/m)`, not Kloosterman fractions involving a
modular inverse.  No cancellation estimate is asserted in this module.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioReduction

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTVariation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmQGeTwoCollapse
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit

private theorem sum_sum_sum_rotate
    {R : Type*} [AddCommMonoid R]
    {α β γ : Type*}
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (f : α → β → γ → R) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c) =
      ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c := by
  classical
  calc
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c) =
        ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, f a b c := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c := by
      rw [Finset.sum_comm]

/-- The ratio kernel left after the exact `q ≥ 2` series collapse. -/
noncomputable def ehmQGeTwoLimitKernel
    (S1 R1 : ℝ → ℝ) (d m : ℕ) : ℝ :=
  S1 ((d : ℝ) / (m : ℝ)) - R1 ((d : ℝ) / (m : ℝ))

/-- The `m`-coefficient at one restored outer cutoff. -/
noncomputable def ehmQGeTwoMWeight (N m : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius m : ℤ) : ℝ) / (m : ℝ)) * weight N m

/-- The `d`-coefficient at one restored outer cutoff. -/
noncomputable def ehmQGeTwoDWeight (N d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (-weight N d)

/-- One restored-cutoff slice of the collapsed sector.  On its support, the
coefficient is a product of an `m`-weight and a `d`-weight; only the ratio
kernel remains joint. -/
noncomputable def ehmQGeTwoCutoffSeparatedSlice
    (S1 R1 : ℝ → ℝ) (X D U N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc (X + 1) D,
    if m ≤ N then
      if N < d then
        ehmQGeTwoMWeight N m * ehmQGeTwoDWeight N d *
          ehmQGeTwoLimitKernel S1 R1 d m
      else 0
    else 0

/-- At one `(N,m,d)` point, the original Möbius-pair coefficient factors
into the two one-variable cutoff weights. -/
theorem ehmQGeTwo_cutoff_term_factorization
    (S1 R1 : ℝ → ℝ) (N m d : ℕ) :
    (((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)) / (m : ℝ)) *
      ((-weight N d) * weight N m)) *
        ehmQGeTwoLimitKernel S1 R1 d m =
      ehmQGeTwoMWeight N m * ehmQGeTwoDWeight N d *
        ehmQGeTwoLimitKernel S1 R1 d m := by
  unfold ehmQGeTwoMWeight ehmQGeTwoDWeight
  ring

/-- The fixed-cutoff series limit is exactly a finite sum of separated
cutoff slices.  This is an algebraic identity: no absolute value, limit, or
analytic estimate is used. -/
theorem ehmDyadicNearTypeIQGeTwoSeriesLimit_eq_sum_cutoffSeparated
    (S1 R1 : ℝ → ℝ) (X D U : ℕ) :
    ehmDyadicNearTypeIQGeTwoSeriesLimit S1 R1 X D U =
      ∑ N ∈ ehmDyadicNBlock X,
        ehmQGeTwoCutoffSeparatedSlice S1 R1 X D U N := by
  classical
  unfold ehmDyadicNearTypeIQGeTwoSeriesLimit
    ehmTypeIOuterPairCoefficient
    ehmQGeTwoCutoffSeparatedSlice
    ehmQGeTwoLimitKernel
  simp_rw [ehmDyadicNearPairAmplitude_eq_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [sum_sum_sum_rotate]
  apply Finset.sum_congr rfl
  intro N hNMem
  apply Finset.sum_congr rfl
  intro m hmMem
  apply Finset.sum_congr rfl
  intro d hdMem
  by_cases hmN : m ≤ N
  · simp only [hmN, if_true]
    by_cases hNd : N < d
    · simp only [hNd, if_true]
      simpa only [ehmQGeTwoLimitKernel] using
        ehmQGeTwo_cutoff_term_factorization S1 R1 N m d
    · simp [hNd]
  · simp [hmN]

/-- The analytic input naturally suggested by the separated normal form.
It deliberately estimates the *complete signed sum of cutoff slices*; a
termwise absolute bound would lose the required correction-sensitive
cancellation. -/
structure EhmQGeTwoAdditiveRatioEstimate (S1 R1 : ℝ → ℝ) where
  C : ℝ
  C_pos : 0 < C
  alpha : ℝ
  alpha_pos : 0 < alpha
  bound : ∀ X D U : ℕ, 2 ≤ X →
    |∑ N ∈ ehmDyadicNBlock X,
        ehmQGeTwoCutoffSeparatedSlice S1 R1 X D U N| ≤
      C / (Real.log ((X : ℝ) + 2)) ^ alpha

/-- A signed additive-ratio estimate immediately controls the exact
collapsed `q ≥ 2` series limit. -/
theorem ehmDyadicNearTypeIQGeTwoSeriesLimit_bound_of_additiveRatio
    {S1 R1 : ℝ → ℝ} (H : EhmQGeTwoAdditiveRatioEstimate S1 R1)
    (X D U : ℕ) (hX : 2 ≤ X) :
    |ehmDyadicNearTypeIQGeTwoSeriesLimit S1 R1 X D U| ≤
      H.C / (Real.log ((X : ℝ) + 2)) ^ H.alpha := by
  rw [ehmDyadicNearTypeIQGeTwoSeriesLimit_eq_sum_cutoffSeparated]
  exact H.bound X D U hX

/-- Correction-coupled version of the additive-ratio target.  The argument
`retained` is where an application must place the main, linear, endpoint,
and complementary-sector terms before taking the absolute value. -/
structure EhmQGeTwoCorrectionCoupledAdditiveRatioEstimate
    (S1 R1 : ℝ → ℝ) (retained : ℕ → ℕ → ℕ → ℝ) where
  C : ℝ
  C_pos : 0 < C
  alpha : ℝ
  alpha_pos : 0 < alpha
  bound : ∀ X D U : ℕ, 2 ≤ X →
    |(∑ N ∈ ehmDyadicNBlock X,
        ehmQGeTwoCutoffSeparatedSlice S1 R1 X D U N) +
          retained X D U| ≤
      C / (Real.log ((X : ℝ) + 2)) ^ alpha

/-- The correction-coupled separated estimate rewrites directly to the
collapsed Ehm sector plus the same retained correction. -/
theorem ehmDyadicNearTypeIQGeTwoSeriesLimit_add_retained_bound
    {S1 R1 : ℝ → ℝ} {retained : ℕ → ℕ → ℕ → ℝ}
    (H : EhmQGeTwoCorrectionCoupledAdditiveRatioEstimate
      S1 R1 retained)
    (X D U : ℕ) (hX : 2 ≤ X) :
    |ehmDyadicNearTypeIQGeTwoSeriesLimit S1 R1 X D U +
        retained X D U| ≤
      H.C / (Real.log ((X : ℝ) + 2)) ^ H.alpha := by
  rw [ehmDyadicNearTypeIQGeTwoSeriesLimit_eq_sum_cutoffSeparated]
  exact H.bound X D U hX

end RH.Criteria.NymanBeurling.BCFLogTaperEhmAdditiveRatioReduction
