import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget

/-!
# Möbius-pair factorization and Type-I/II split of the Ehm near core

The near complementary coefficient contains two BCF coefficients evaluated
at the same cutoff.  This file factors out the fixed Möbius signs and proves
that the remaining taper-pair amplitude is nonnegative.  It then splits the
resulting signed bilinear form at an arbitrary outer threshold `U`.

All identities are finite and exact.  The main form and linear remainder stay
coupled to the two bilinear ranges in the final theorem.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicNearCoreReindex

/-- The cutoff average of the two logarithmic tapers on the near support
`m ≤ N < d`.  It is nonpositive on the genuine dyadic range. -/
noncomputable def ehmDyadicNearTaperPairAverage
    (X m d : ℕ) : ℝ :=
  ∑ N ∈ ehmDyadicNBlock X,
    if m ≤ N then
      if N < d then weight N m * weight N d else 0
    else 0

/-- The sign-corrected taper-pair amplitude. -/
noncomputable def ehmDyadicNearPairAmplitude
    (X m d : ℕ) : ℝ :=
  -ehmDyadicNearTaperPairAverage X m d

/-- Exact factorization of the cutoff coefficient into its two fixed Möbius
signs and its taper-pair average. -/
theorem ehmDyadicNearCutoffCoeff_eq_moebius_mul_taperAverage
    (X m d : ℕ) :
    ehmDyadicNearCutoffCoeff X m d =
      ((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) / (m : ℝ)) *
        ehmDyadicNearTaperPairAverage X m d := by
  classical
  unfold ehmDyadicNearCutoffCoeff ehmDyadicNearTaperPairAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N _
  by_cases hmN : m ≤ N <;> by_cases hNd : N < d
  all_goals simp [hmN, hNd, dirichletCoeff]
  all_goals ring_nf

/-- On the support `m ≤ N` of a genuine dyadic block, the first taper is
nonnegative. -/
private theorem weight_nonneg_of_mem_of_le
    (X N m : ℕ) (hX : 2 ≤ X) (hNmem : N ∈ ehmDyadicNBlock X)
    (hm : 1 ≤ m) (hmN : m ≤ N) :
    0 ≤ weight N m := by
  have hN2 : 2 ≤ N := hX.trans (Finset.mem_Icc.mp hNmem).1
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogmN : Real.log (m : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < m by omega))
      (by exact_mod_cast hmN)
  rw [weight_of_two_le hN2]
  exact sub_nonneg.mpr ((div_le_one hlogN).2 hlogmN)

/-- Above the cutoff, the second logarithmic taper is nonpositive. -/
private theorem weight_nonpos_of_mem_of_lt
    (X N d : ℕ) (hX : 2 ≤ X) (hNmem : N ∈ ehmDyadicNBlock X)
    (hNd : N < d) :
    weight N d ≤ 0 := by
  have hN2 : 2 ≤ N := hX.trans (Finset.mem_Icc.mp hNmem).1
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogNd : Real.log (N : ℝ) ≤ Real.log (d : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < N by omega))
      (by exact_mod_cast hNd.le)
  rw [weight_of_two_le hN2]
  have hratio : 1 ≤ Real.log (d : ℝ) / Real.log (N : ℝ) :=
    (le_div_iff₀ hlogN).2 (by simpa using hlogNd)
  linarith

/-- The taper-pair average is nonpositive on the near support. -/
theorem ehmDyadicNearTaperPairAverage_nonpos
    (X m d : ℕ) (hX : 2 ≤ X) (hm : 1 ≤ m) :
    ehmDyadicNearTaperPairAverage X m d ≤ 0 := by
  classical
  unfold ehmDyadicNearTaperPairAverage
  apply Finset.sum_nonpos
  intro N hNmem
  by_cases hmN : m ≤ N
  · simp only [hmN, if_true]
    by_cases hNd : N < d
    · simp only [hNd, if_true]
      exact mul_nonpos_of_nonneg_of_nonpos
        (weight_nonneg_of_mem_of_le X N m hX hNmem hm hmN)
        (weight_nonpos_of_mem_of_lt X N d hX hNmem hNd)
    · simp [hNd]
  · simp [hmN]

/-- The sign-corrected pair amplitude is nonnegative. -/
theorem ehmDyadicNearPairAmplitude_nonneg
    (X m d : ℕ) (hX : 2 ≤ X) (hm : 1 ≤ m) :
    0 ≤ ehmDyadicNearPairAmplitude X m d := by
  unfold ehmDyadicNearPairAmplitude
  exact neg_nonneg.mpr (ehmDyadicNearTaperPairAverage_nonpos X m d hX hm)

/-- The near cutoff coefficient is the negative Möbius-pair sign times a
nonnegative amplitude. -/
theorem ehmDyadicNearCutoffCoeff_eq_neg_moebius_mul_amplitude
    (X m d : ℕ) :
    ehmDyadicNearCutoffCoeff X m d =
      -(((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) / (m : ℝ)) *
        ehmDyadicNearPairAmplitude X m d) := by
  rw [ehmDyadicNearCutoffCoeff_eq_moebius_mul_taperAverage]
  unfold ehmDyadicNearPairAmplitude
  ring

/-- The Möbius-pair bilinear form over an arbitrary `m` interval. -/
noncomputable def ehmDyadicNearMobiusBilinearMRange
    (R1 : ℝ → ℝ) (X D J mLo mHi : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
    ∑ q ∈ Finset.Icc 1 J,
      if d * q ≤ J then
        ((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius d : ℤ) : ℝ)) / (m : ℝ)) *
          ehmDyadicNearPairAmplitude X m d *
            R1 (((d * q : ℕ) : ℝ) / (m : ℝ))
      else 0

/-- The full Möbius-pair near bilinear form. -/
noncomputable def ehmDyadicNearMobiusBilinearJointSum
    (R1 : ℝ → ℝ) (X D J : ℕ) : ℝ :=
  ehmDyadicNearMobiusBilinearMRange R1 X D J 1 (2 * X)

/-- The original complementary joint sum is the negative of the
sign-normalized Möbius-pair bilinear form. -/
theorem ehmDyadicNearComplementaryJointSum_eq_neg_mobiusBilinear
    (R1 : ℝ → ℝ) (X D J : ℕ) :
    ehmDyadicNearComplementaryJointSum R1 X D J =
      -ehmDyadicNearMobiusBilinearJointSum R1 X D J := by
  classical
  unfold ehmDyadicNearComplementaryJointSum
    ehmDyadicNearMobiusBilinearJointSum ehmDyadicNearMobiusBilinearMRange
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hdq : d * q ≤ J
  · simp only [hdq, if_true]
    rw [ehmDyadicNearCutoffCoeff_eq_neg_moebius_mul_amplitude]
    ring
  · simp [hdq]

/-- The short-`m` (Type-I) part at threshold `U`. -/
noncomputable def ehmDyadicNearTypeI
    (R1 : ℝ → ℝ) (X D J U : ℕ) : ℝ :=
  ehmDyadicNearMobiusBilinearMRange R1 X D J 1 U

/-- The complementary long-`m` (Type-II) part at threshold `U`. -/
noncomputable def ehmDyadicNearTypeII
    (R1 : ℝ → ℝ) (X D J U : ℕ) : ℝ :=
  ehmDyadicNearMobiusBilinearMRange R1 X D J (U + 1) (2 * X)

/-- Exact Type-I/II partition of the signed near Möbius-pair form. -/
theorem ehmDyadicNearMobiusBilinearJointSum_eq_typeI_add_typeII
    (R1 : ℝ → ℝ) (X D J U : ℕ) (hU : U ≤ 2 * X) :
    ehmDyadicNearMobiusBilinearJointSum R1 X D J =
      ehmDyadicNearTypeI R1 X D J U +
        ehmDyadicNearTypeII R1 X D J U := by
  classical
  have hwhole :
      Finset.Icc 1 (2 * X) =
        Finset.Icc 1 U ∪ Finset.Icc (U + 1) (2 * X) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdis :
      Disjoint (Finset.Icc 1 U) (Finset.Icc (U + 1) (2 * X)) := by
    apply Finset.disjoint_left.mpr
    intro m hmI hmII
    have hmU := (Finset.mem_Icc.mp hmI).2
    have hUm := (Finset.mem_Icc.mp hmII).1
    omega
  unfold ehmDyadicNearMobiusBilinearJointSum ehmDyadicNearTypeI
    ehmDyadicNearTypeII ehmDyadicNearMobiusBilinearMRange
  rw [hwhole, Finset.sum_union hdis]

/-- The indivisible coupled near core in exact Type-I/II coordinates.  The
main form and linear remainder retain their signs and remain in the same
identity. -/
theorem ehmDyadicExplicitCoupledNearCore_eq_typeI_typeII
    (R1 : ℝ → ℝ) (X D J U : ℕ) (hU : U ≤ 2 * X) :
    ehmDyadicExplicitCoupledNearCore R1 X D J =
      ehmDyadicFullMainJointSum R1 X J +
        ehmDyadicNearTypeI R1 X D J U +
        ehmDyadicNearTypeII R1 X D J U +
        ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N := by
  unfold ehmDyadicExplicitCoupledNearCore
  rw [ehmDyadicNearComplementaryJointSum_eq_neg_mobiusBilinear]
  rw [sub_neg_eq_add, ehmDyadicNearMobiusBilinearJointSum_eq_typeI_add_typeII
    R1 X D J U hU]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit
