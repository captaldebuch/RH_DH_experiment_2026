import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmComplementarySector

/-!
# Rectangular dispersion blocks for the Ehm near core

The near/far reduction leaves a signed near core consisting of a full von
Mangoldt transform, a complementary-divisor correction, and the linear
moment remainder.  This file first regroups the complementary hyperbola by
its product coordinate.  The result is one finite signed bilinear form in
the outer Möbius variable `m` and the product variable `j`.

We then split that bilinear form exactly at arbitrary cutoffs `M` and `K`.
Iterating the two-cut identity produces dyadic rectangles, while the theorem
itself does not impose powers-of-two bookkeeping.  Crucially, each block
retains the difference between the von Mangoldt coefficient and the near
complementary-divisor coefficient.  No triangle inequality or unsigned
majorization is used here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmDispersionBlocks

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryTail
open RH.Criteria.NymanBeurling.BCFLogTaperEhmComplementarySector
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbola

/-- The signed coefficient remaining at product coordinate `j` after the
near complementary divisors `N < d <= D` are removed from the full von
Mangoldt coefficient. -/
noncomputable def ehmNearDispersionCoeff (N D j : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) -
    ∑ d ∈ Finset.Icc (N + 1) D,
      if d ∣ j then dirichletCoeff N d else 0

/-- One rectangular block of the signed near bilinear form. -/
noncomputable def ehmFiniteNearDispersionBlock
    (R1 : ℝ → ℝ) (N D _J mLo mHi jLo jHi : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc mLo mHi, dirichletCoeff N m / (m : ℝ) *
    ∑ j ∈ Finset.Icc jLo jHi,
      ehmNearDispersionCoeff N D j *
        R1 ((j : ℝ) / (m : ℝ))

/-- The whole signed near bilinear form, before adding the coupled linear
moment remainder. -/
noncomputable def ehmFiniteNearDispersionBilinear
    (R1 : ℝ → ℝ) (N D J : ℕ) : ℝ :=
  ehmFiniteNearDispersionBlock R1 N D J 1 N 2 J

/-- A rectangular block using the original finite log-taper divisor
convolution.  On product coordinates `j <= D` this agrees exactly with the
near-dispersion block. -/
noncomputable def ehmFiniteLogTaperConvolutionBlock
    (R1 : ℝ → ℝ) (N _J mLo mHi jLo jHi : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc mLo mHi, dirichletCoeff N m / (m : ℝ) *
    ∑ j ∈ Finset.Icc jLo jHi,
      ehmLogTaperDivisorCoeff N j * R1 ((j : ℝ) / (m : ℝ))

private theorem hyperbolicRow_eq_divisibleRow
    (f : ℕ → ℝ) (d J : ℕ) (hd : 2 ≤ d) :
    (∑ q ∈ Finset.Icc 1 J, if d * q ≤ J then f (d * q) else 0) =
      ∑ j ∈ Finset.Icc 2 J, if d ∣ j then f j else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun q _ => d * q)
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hdqJ⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq1, _⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · have hdle : d ≤ d * q := by
          simpa using Nat.mul_le_mul_left d hq1
        omega
      · exact hdqJ
    · exact dvd_mul_right d q
  · intro a _ b _ hab
    exact Nat.mul_left_cancel (by omega) hab
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjIcc, hdj⟩
    rcases Finset.mem_Icc.mp hjIcc with ⟨hjlo, hjJ⟩
    refine ⟨j / d, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · exact Nat.div_pos (Nat.le_of_dvd (by omega) hdj) (by omega)
        · exact (Nat.div_le_self j d).trans hjJ
      · rw [Nat.mul_div_cancel' hdj]
        exact hjJ
    · exact Nat.mul_div_cancel' hdj
  · intro q _
    rfl

/-- Product-coordinate regrouping of the signed near complementary sector.
The divisibility sum is retained with its Möbius/log-taper signs. -/
theorem ehmFiniteComplementaryDivisorNearSum_eq_productGrouped
    (R1 : ℝ → ℝ) (N D J : ℕ) (x : ℝ) (hN : 1 ≤ N) :
    ehmFiniteComplementaryDivisorNearSum R1 N D J x =
      ∑ j ∈ Finset.Icc 2 J,
        (∑ d ∈ Finset.Icc (N + 1) D,
          if d ∣ j then dirichletCoeff N d else 0) *
          R1 ((j : ℝ) * x) := by
  classical
  unfold ehmFiniteComplementaryDivisorNearSum
  calc
    (∑ d ∈ Finset.Icc (N + 1) D, ∑ q ∈ Finset.Icc 1 J,
        if d * q ≤ J then
          dirichletCoeff N d * R1 (((d * q : ℕ) : ℝ) * x)
        else 0) =
        ∑ d ∈ Finset.Icc (N + 1) D, ∑ j ∈ Finset.Icc 2 J,
          if d ∣ j then
            dirichletCoeff N d * R1 ((j : ℝ) * x)
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hdmem
      have hd : 2 ≤ d := by
        have := (Finset.mem_Icc.mp hdmem).1
        omega
      exact hyperbolicRow_eq_divisibleRow
        (fun j => dirichletCoeff N d * R1 ((j : ℝ) * x)) d J hd
    _ = ∑ j ∈ Finset.Icc 2 J, ∑ d ∈ Finset.Icc (N + 1) D,
          if d ∣ j then
            dirichletCoeff N d * R1 ((j : ℝ) * x)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.Icc 2 J,
        (∑ d ∈ Finset.Icc (N + 1) D,
          if d ∣ j then dirichletCoeff N d else 0) *
          R1 ((j : ℝ) * x) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hdj : d ∣ j <;> simp [hdj]

/-- Below the divisor cutoff `D`, the coupled near coefficient collapses
exactly to the original log-taper divisor convolution.  Above `D` no such
replacement is made. -/
theorem ehmNearDispersionCoeff_eq_logTaperDivisorCoeff
    (N D j : ℕ) (hN : 2 ≤ N) (hj : 2 ≤ j) (hjD : j ≤ D) :
    ehmNearDispersionCoeff N D j = ehmLogTaperDivisorCoeff N j := by
  classical
  have hset :
      (Finset.Icc (N + 1) D).filter (fun d => d ∣ j) =
        j.divisors.filter (fun d => N < d) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdlo, _⟩, hdj⟩
      exact ⟨⟨hdj, by omega⟩, by omega⟩
    · rintro ⟨⟨hdj, hjne⟩, hNd⟩
      have hdjle : d ≤ j := Nat.le_of_dvd (by omega) hdj
      exact ⟨⟨by omega, hdjle.trans hjD⟩, hdj⟩
  have hnear :
      (∑ d ∈ Finset.Icc (N + 1) D,
        if d ∣ j then dirichletCoeff N d else 0) =
        ehmLogTaperMissingDivisorCoeff N j := by
    rw [← Finset.sum_filter, hset]
    unfold ehmLogTaperMissingDivisorCoeff
    rw [← Finset.sum_filter]
  unfold ehmNearDispersionCoeff
  rw [hnear]
  exact (ehmLogTaperDivisorCoeff_eq_vonMangoldt_sub_missing
    N j hN hj).symm

/-- Any low-product rectangle ending at or before `D` is an exact block of
the original log-taper divisor convolution. -/
theorem ehmFiniteNearDispersionBlock_eq_logTaperConvolutionBlock
    (R1 : ℝ → ℝ) (N D J mLo mHi jLo jHi : ℕ)
    (hN : 2 ≤ N) (hjLo : 2 ≤ jLo) (hjHiD : jHi ≤ D) :
    ehmFiniteNearDispersionBlock R1 N D J mLo mHi jLo jHi =
      ehmFiniteLogTaperConvolutionBlock R1 N J mLo mHi jLo jHi := by
  classical
  unfold ehmFiniteNearDispersionBlock ehmFiniteLogTaperConvolutionBlock
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  apply Finset.sum_congr rfl
  intro j hjmem
  rw [ehmNearDispersionCoeff_eq_logTaperDivisorCoeff N D j hN
    (hjLo.trans (Finset.mem_Icc.mp hjmem).1)
    ((Finset.mem_Icc.mp hjmem).2.trans hjHiD)]

/-- The full-von-Mangoldt-minus-near-complementary row is exactly the row
with coefficient `ehmNearDispersionCoeff`. -/
theorem ehmFiniteFullVonMangoldtTransform_sub_nearSum_eq_dispersionRow
    (R1 : ℝ → ℝ) (N D J : ℕ) (m : ℕ) (hN : 1 ≤ N) :
    ehmFiniteFullVonMangoldtTransform R1 N J (1 / (m : ℝ)) -
        ehmFiniteComplementaryDivisorNearSum R1 N D J (1 / (m : ℝ)) =
      ∑ j ∈ Finset.Icc 2 J,
        ehmNearDispersionCoeff N D j * R1 ((j : ℝ) / (m : ℝ)) := by
  classical
  rw [ehmFiniteComplementaryDivisorNearSum_eq_productGrouped
    R1 N D J (1 / (m : ℝ)) hN]
  unfold ehmFiniteFullVonMangoldtTransform ehmNearDispersionCoeff
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have harg : (j : ℝ) * (1 / (m : ℝ)) = (j : ℝ) / (m : ℝ) := by ring
  rw [harg]
  ring

/-- Exact bilinear form of the signed near core.  The linear correction is
kept coupled as the final summand rather than estimated separately. -/
theorem ehmFiniteComplementaryDivisorNearCore_eq_dispersionBilinear_add_remainder
    (R1 : ℝ → ℝ) (N D J : ℕ) (hN : 1 ≤ N) :
    ehmFiniteComplementaryDivisorNearCore R1 N D J =
      ehmFiniteNearDispersionBilinear R1 N D J + ehmCoupledRemainder N := by
  classical
  unfold ehmFiniteComplementaryDivisorNearCore
    ehmFiniteFullVonMangoldtTransformOuter
    ehmFiniteComplementaryDivisorNearOuter
    ehmFiniteNearDispersionBilinear
    ehmFiniteNearDispersionBlock
  rw [← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [← mul_sub]
  rw [ehmFiniteFullVonMangoldtTransform_sub_nearSum_eq_dispersionRow
    R1 N D J m hN]

private theorem sum_rectangle_split
    (f : ℕ → ℕ → ℝ) (N J M K : ℕ)
    (hM : M ≤ N) (hKlo : 2 ≤ K) (hK : K ≤ J) :
    (∑ m ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 2 J, f m j) =
      (∑ m ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 2 K, f m j) +
      (∑ m ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc (K + 1) J, f m j) +
      (∑ m ∈ Finset.Icc (M + 1) N, ∑ j ∈ Finset.Icc 2 K, f m j) +
      (∑ m ∈ Finset.Icc (M + 1) N,
        ∑ j ∈ Finset.Icc (K + 1) J, f m j) := by
  classical
  have hmset :
      Finset.Icc 1 N = Finset.Icc 1 M ∪ Finset.Icc (M + 1) N := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hmdis : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1) N) := by
    apply Finset.disjoint_left.mpr
    intro m hmlo hmhi
    have hmM := (Finset.mem_Icc.mp hmlo).2
    have hMm := (Finset.mem_Icc.mp hmhi).1
    omega
  have hjset :
      Finset.Icc 2 J = Finset.Icc 2 K ∪ Finset.Icc (K + 1) J := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hjdis : Disjoint (Finset.Icc 2 K) (Finset.Icc (K + 1) J) := by
    apply Finset.disjoint_left.mpr
    intro j hjlo hjhi
    have hjK := (Finset.mem_Icc.mp hjlo).2
    have hKj := (Finset.mem_Icc.mp hjhi).1
    omega
  have hsplit (S : Finset ℕ) :
      (∑ m ∈ S, ∑ j ∈ Finset.Icc 2 J, f m j) =
        (∑ m ∈ S, ∑ j ∈ Finset.Icc 2 K, f m j) +
        (∑ m ∈ S, ∑ j ∈ Finset.Icc (K + 1) J, f m j) := by
    rw [hjset]
    simp_rw [Finset.sum_union hjdis]
    exact Finset.sum_add_distrib
  rw [hmset, Finset.sum_union hmdis,
    hsplit (Finset.Icc 1 M), hsplit (Finset.Icc (M + 1) N)]
  ring

/-- Exact four-rectangle split of the signed near bilinear form.  Repeated
application gives any finite (in particular dyadic) rectangular partition.
Every rectangle retains the coupled arithmetic coefficient. -/
theorem ehmFiniteNearDispersionBilinear_eq_fourBlocks
    (R1 : ℝ → ℝ) (N D J M K : ℕ)
    (hM : M ≤ N) (hKlo : 2 ≤ K) (hK : K ≤ J) :
    ehmFiniteNearDispersionBilinear R1 N D J =
      ehmFiniteNearDispersionBlock R1 N D J 1 M 2 K +
      ehmFiniteNearDispersionBlock R1 N D J 1 M (K + 1) J +
      ehmFiniteNearDispersionBlock R1 N D J (M + 1) N 2 K +
      ehmFiniteNearDispersionBlock R1 N D J (M + 1) N (K + 1) J := by
  unfold ehmFiniteNearDispersionBilinear ehmFiniteNearDispersionBlock
  simp_rw [Finset.mul_sum]
  exact sum_rectangle_split
    (fun m j => dirichletCoeff N m / (m : ℝ) *
      (ehmNearDispersionCoeff N D j * R1 ((j : ℝ) / (m : ℝ))))
    N J M K hM hKlo hK

/-- Four-block form of the complete signed near core, including the linear
moment correction. -/
theorem ehmFiniteComplementaryDivisorNearCore_eq_fourBlocks_add_remainder
    (R1 : ℝ → ℝ) (N D J M K : ℕ) (hN : 1 ≤ N)
    (hM : M ≤ N) (hKlo : 2 ≤ K) (hK : K ≤ J) :
    ehmFiniteComplementaryDivisorNearCore R1 N D J =
      ehmFiniteNearDispersionBlock R1 N D J 1 M 2 K +
      ehmFiniteNearDispersionBlock R1 N D J 1 M (K + 1) J +
      ehmFiniteNearDispersionBlock R1 N D J (M + 1) N 2 K +
      ehmFiniteNearDispersionBlock R1 N D J (M + 1) N (K + 1) J +
      ehmCoupledRemainder N := by
  rw [ehmFiniteComplementaryDivisorNearCore_eq_dispersionBilinear_add_remainder
    R1 N D J hN,
    ehmFiniteNearDispersionBilinear_eq_fourBlocks R1 N D J M K hM hKlo hK]

/-- Split at the natural product cutoff `K = D`.  The two low-product
rectangles become ordinary log-taper divisor-convolution blocks; the two
high-product rectangles retain the full signed
von-Mangoldt-minus-complementary coefficient.  This is the finite Type-I/II
starting point supplied by the Ehm near/far decomposition. -/
theorem ehmFiniteComplementaryDivisorNearCore_eq_lowConvolution_highDispersion
    (R1 : ℝ → ℝ) (N D J M : ℕ)
    (hN : 2 ≤ N) (hM : M ≤ N) (hDlo : 2 ≤ D) (hD : D ≤ J) :
    ehmFiniteComplementaryDivisorNearCore R1 N D J =
      ehmFiniteLogTaperConvolutionBlock R1 N J 1 M 2 D +
      ehmFiniteNearDispersionBlock R1 N D J 1 M (D + 1) J +
      ehmFiniteLogTaperConvolutionBlock R1 N J (M + 1) N 2 D +
      ehmFiniteNearDispersionBlock R1 N D J (M + 1) N (D + 1) J +
      ehmCoupledRemainder N := by
  rw [ehmFiniteComplementaryDivisorNearCore_eq_fourBlocks_add_remainder
    R1 N D J M D (by omega) hM hDlo hD,
    ehmFiniteNearDispersionBlock_eq_logTaperConvolutionBlock
      R1 N D J 1 M 2 D hN (by omega) le_rfl,
    ehmFiniteNearDispersionBlock_eq_logTaperConvolutionBlock
      R1 N D J (M + 1) N 2 D hN (by omega) le_rfl]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmDispersionBlocks
