import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmVaalerNormalizedCharacters

/-!
# Paired additive rows for the normalized Ehm Vaaler kernel

This module groups the normalized near row by its product coordinate
`n = d * q` and combines it with the normalized main row before taking any
absolute values.  Every identity is finite and exact.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerNormalizedCharacters

/-! ## Product-coordinate form of one harmonic row -/

private theorem hyperbolicRow_eq_divisibleRow
    (f : ℕ → ℂ) (d J : ℕ) (hd : 0 < d) :
    (∑ q ∈ Finset.Icc 1 J, if d * q ≤ J then f (d * q) else 0) =
      ∑ n ∈ Finset.Icc 1 J, if d ∣ n then f n else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun q _ ↦ d * q)
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hdqJ⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq1, _⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hd (lt_of_lt_of_le Nat.zero_lt_one hq1), hdqJ⟩,
      dvd_mul_right d q⟩
  · intro a _ b _ hab
    exact Nat.mul_left_cancel hd hab
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hdn⟩
    rcases Finset.mem_Icc.mp hnIcc with ⟨hn1, hnJ⟩
    refine ⟨n / d, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      have hndivpos : 0 < n / d :=
        Nat.div_pos
          (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hn1) hdn) hd
      exact ⟨Finset.mem_Icc.mpr
        ⟨hndivpos, (Nat.div_le_self n d).trans hnJ⟩, by
          rw [Nat.mul_div_cancel' hdn]
          exact hnJ⟩
    · exact Nat.mul_div_cancel' hdn
  · intro q _
    rfl

private theorem hyperbolicRow_eq_divisibleRowFromTwo
    (f : ℕ → ℂ) (d J : ℕ) (hd : 2 ≤ d) :
    (∑ q ∈ Finset.Icc 1 J, if d * q ≤ J then f (d * q) else 0) =
      ∑ n ∈ Finset.Icc 2 J, if d ∣ n then f n else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun q _ ↦ d * q)
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hdqJ⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq1, _⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr
      ⟨by
        have hdle : d ≤ d * q := by
          simpa using Nat.mul_le_mul_left d hq1
        exact hd.trans hdle,
        hdqJ⟩,
      dvd_mul_right d q⟩
  · intro a _ b _ hab
    exact Nat.mul_left_cancel (by omega) hab
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hdn⟩
    rcases Finset.mem_Icc.mp hnIcc with ⟨hn2, hnJ⟩
    refine ⟨n / d, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · exact Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (by omega)
        · exact (Nat.div_le_self n d).trans hnJ
      · rw [Nat.mul_div_cancel' hdn]
        exact hnJ
    · exact Nat.mul_div_cancel' hdn
  · intro q _
    rfl

private theorem ehmVaalerHarmonicPhaseTerm_eq_productTerm
    (h : ℤ) (q d m : ℕ) (hd : 0 < d) (hq : 0 < q) :
    ehmVaalerRationalPhase h q d m / (q : ℂ) =
      (d : ℂ) * ehmVaalerRationalPhase h (d * q) 1 m /
        ((d * q : ℕ) : ℂ) := by
  have hphase :
      ehmVaalerRationalPhase h q d m =
        ehmVaalerRationalPhase h (d * q) 1 m := by
    unfold ehmVaalerRationalPhase
    congr 1
    push_cast
    ring
  rw [hphase]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp [hdC, hqC]

/-- Multiplication by `d` identifies the harmonic `q`-row with the
divisible product coordinates `n = d*q`. -/
theorem ehmVaalerHarmonicPhaseRow_eq_productGrouped
    (h : ℤ) (J m d : ℕ) (hd : 0 < d) :
    ehmVaalerHarmonicPhaseRow h J m d =
      ∑ n ∈ Finset.Icc 1 J, if d ∣ n then
        (d : ℂ) * ehmVaalerRationalPhase h n 1 m / (n : ℂ)
      else 0 := by
  classical
  have hfilter :
      (Finset.Icc 1 J).filter (fun q ↦ d * q ≤ J) =
        Finset.Icc 1 (J / d) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hq1, _⟩, hdqJ⟩
      exact ⟨hq1,
        (Nat.le_div_iff_mul_le hd).2 (by simpa [Nat.mul_comm] using hdqJ)⟩
    · rintro ⟨hq1, hqdiv⟩
      have hqdJ : q * d ≤ J := (Nat.le_div_iff_mul_le hd).1 hqdiv
      have hqJ : q ≤ J := hqdiv.trans (Nat.div_le_self J d)
      exact ⟨⟨hq1, hqJ⟩, by simpa [Nat.mul_comm] using hqdJ⟩
  unfold ehmVaalerHarmonicPhaseRow
  calc
    (∑ q ∈ Finset.Icc 1 (J / d),
        ehmVaalerRationalPhase h q d m / (q : ℂ)) =
        ∑ q ∈ Finset.Icc 1 J, if d * q ≤ J then
          ehmVaalerRationalPhase h q d m / (q : ℂ)
        else 0 := by
      rw [← Finset.sum_filter, hfilter]
    _ = ∑ q ∈ Finset.Icc 1 J, if d * q ≤ J then
          (d : ℂ) * ehmVaalerRationalPhase h (d * q) 1 m /
            ((d * q : ℕ) : ℂ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro q hqmem
      by_cases hdqJ : d * q ≤ J
      · simp only [hdqJ, if_true]
        exact ehmVaalerHarmonicPhaseTerm_eq_productTerm h q d m hd
          (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hqmem).1)
      · simp [hdqJ]
    _ = ∑ n ∈ Finset.Icc 1 J, if d ∣ n then
          (d : ℂ) * ehmVaalerRationalPhase h n 1 m / (n : ℂ)
        else 0 :=
      hyperbolicRow_eq_divisibleRow
        (fun n ↦ (d : ℂ) * ehmVaalerRationalPhase h n 1 m / (n : ℂ))
        d J hd

/-- When `2 ≤ d`, every product `d*q` is at least two, so the grouped row
can use exactly the same product interval as the von Mangoldt main row. -/
theorem ehmVaalerHarmonicPhaseRow_eq_productGroupedFromTwo
    (h : ℤ) (J m d : ℕ) (hd : 2 ≤ d) :
    ehmVaalerHarmonicPhaseRow h J m d =
      ∑ n ∈ Finset.Icc 2 J, if d ∣ n then
        (d : ℂ) * ehmVaalerRationalPhase h n 1 m / (n : ℂ)
      else 0 := by
  classical
  have hfilter :
      (Finset.Icc 1 J).filter (fun q ↦ d * q ≤ J) =
        Finset.Icc 1 (J / d) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hq1, _⟩, hdqJ⟩
      exact ⟨hq1,
        (Nat.le_div_iff_mul_le (by omega)).2
          (by simpa [Nat.mul_comm] using hdqJ)⟩
    · rintro ⟨hq1, hqdiv⟩
      have hqdJ : q * d ≤ J :=
        (Nat.le_div_iff_mul_le (by omega)).1 hqdiv
      have hqJ : q ≤ J := hqdiv.trans (Nat.div_le_self J d)
      exact ⟨⟨hq1, hqJ⟩, by simpa [Nat.mul_comm] using hqdJ⟩
  unfold ehmVaalerHarmonicPhaseRow
  calc
    (∑ q ∈ Finset.Icc 1 (J / d),
        ehmVaalerRationalPhase h q d m / (q : ℂ)) =
        ∑ q ∈ Finset.Icc 1 J, if d * q ≤ J then
          ehmVaalerRationalPhase h q d m / (q : ℂ)
        else 0 := by
      rw [← Finset.sum_filter, hfilter]
    _ = ∑ q ∈ Finset.Icc 1 J, if d * q ≤ J then
          (d : ℂ) * ehmVaalerRationalPhase h (d * q) 1 m /
            ((d * q : ℕ) : ℂ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro q hqmem
      by_cases hdqJ : d * q ≤ J
      · simp only [hdqJ, if_true]
        exact ehmVaalerHarmonicPhaseTerm_eq_productTerm h q d m
          (by omega)
          (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hqmem).1)
      · simp [hdqJ]
    _ = ∑ n ∈ Finset.Icc 2 J, if d ∣ n then
          (d : ℂ) * ehmVaalerRationalPhase h n 1 m / (n : ℂ)
        else 0 :=
      hyperbolicRow_eq_divisibleRowFromTwo
        (fun n ↦ (d : ℂ) * ehmVaalerRationalPhase h n 1 m / (n : ℂ))
        d J hd

/-! ## Paired coefficients and rows -/

/-- The signed near coefficient at product coordinate `n`, retaining all
divisors `X < d ≤ D` of `n`. -/
noncomputable def ehmDyadicVaalerNearProductCoefficient
    (X D m n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (X + 1) D,
    if d ∣ n then
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        ehmDyadicNearPairAmplitude X m d
    else 0

/-- The main and near coefficients paired before any absolute value is
taken.  The common factor `1/n` is kept in the row definition below. -/
noncomputable def ehmDyadicVaalerPairedProductCoefficient
    (X D m n : ℕ) : ℝ :=
  ehmDyadicLogTaperAverage X m * ArithmeticFunction.vonMangoldt n +
    ehmDyadicVaalerNearProductCoefficient X D m n

/-- One additive row in the common product coordinate `n`. -/
noncomputable def ehmDyadicVaalerPairedAdditiveRow
    (h : ℤ) (X D J m : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 J,
    ((ehmDyadicVaalerPairedProductCoefficient X D m n / (n : ℝ) : ℝ) : ℂ) *
      ehmVaalerRationalPhase h n 1 m

/-- The signed Möbius sum of paired additive rows on an arbitrary common
`m`-range. -/
noncomputable def ehmDyadicVaalerPairedAdditiveRowsMRange
    (h : ℤ) (X D J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi,
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ehmDyadicVaalerPairedAdditiveRow h X D J m)

/-- The normalized main phase restricted to an arbitrary `m`-interval. -/
noncomputable def ehmDyadicVaalerNormalizedMainPhaseFormMRange
    (h : ℤ) (X J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ n ∈ Finset.Icc 2 J,
    (((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
      ehmDyadicLogTaperAverage X m *
      (ArithmeticFunction.vonMangoldt n / (n : ℝ))) : ℝ) : ℂ) *
        ehmVaalerRationalPhase h n 1 m

/-- The main component in additive-row form on an arbitrary `m`-range. -/
noncomputable def ehmDyadicVaalerMainAdditiveRowsMRange
    (h : ℤ) (X J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi,
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ∑ n ∈ Finset.Icc 2 J,
        (((ehmDyadicLogTaperAverage X m *
          ArithmeticFunction.vonMangoldt n / (n : ℝ) : ℝ) : ℂ) *
            ehmVaalerRationalPhase h n 1 m))

/-- The reindexed near component in additive-row form. -/
noncomputable def ehmDyadicVaalerNearProductRowsMRange
    (h : ℤ) (X D J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi,
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
      ∑ n ∈ Finset.Icc 2 J,
        (((ehmDyadicVaalerNearProductCoefficient X D m n /
          (n : ℝ) : ℝ) : ℂ) * ehmVaalerRationalPhase h n 1 m))

/-! ## Exact main and near regrouping -/

theorem ehmDyadicVaalerNormalizedMainPhaseFormMRange_eq_additiveRows
    (h : ℤ) (X J mLo mHi : ℕ) :
    ehmDyadicVaalerNormalizedMainPhaseFormMRange h X J mLo mHi =
      ehmDyadicVaalerMainAdditiveRowsMRange h X J mLo mHi := by
  classical
  unfold ehmDyadicVaalerNormalizedMainPhaseFormMRange
    ehmDyadicVaalerMainAdditiveRowsMRange
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

theorem ehmDyadicVaalerNormalizedMainPhaseForm_eq_mRange
    (h : ℤ) (X J : ℕ) :
    ehmDyadicVaalerNormalizedMainPhaseForm h X J =
      ehmDyadicVaalerNormalizedMainPhaseFormMRange h X J 1 (2 * X) := by
  rfl

/-- Exact reindexing of the normalized near form by `n = d*q`.
The hypothesis `1 ≤ X` ensures every near divisor `d ≥ X+1` is at least
two, matching the main row's product range `2 ≤ n ≤ J`. -/
theorem ehmDyadicVaalerNormalizedNearPhaseFormMRange_eq_productRows
    (h : ℤ) (X D J mLo mHi : ℕ) (hX : 1 ≤ X) :
    ehmDyadicVaalerNormalizedNearPhaseFormMRange h X D J mLo mHi =
      ehmDyadicVaalerNearProductRowsMRange h X D J mLo mHi := by
  classical
  unfold ehmDyadicVaalerNormalizedNearPhaseFormMRange
    ehmDyadicVaalerNearProductRowsMRange
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  calc
    (∑ d ∈ Finset.Icc (X + 1) D,
        (((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          ehmDyadicNearPairAmplitude X m d / (d : ℝ)) : ℝ) : ℂ) *
            ehmVaalerHarmonicPhaseRow h J m d) =
      ∑ d ∈ Finset.Icc (X + 1) D,
        (((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          ehmDyadicNearPairAmplitude X m d / (d : ℝ)) : ℝ) : ℂ) *
          ∑ n ∈ Finset.Icc 2 J, if d ∣ n then
            (d : ℂ) * ehmVaalerRationalPhase h n 1 m / (n : ℂ)
          else 0 := by
        apply Finset.sum_congr rfl
        intro d hdmem
        rw [ehmVaalerHarmonicPhaseRow_eq_productGroupedFromTwo h J m d]
        have hdlo := (Finset.mem_Icc.mp hdmem).1
        omega
    _ = ∑ n ∈ Finset.Icc 2 J,
        ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          (((ehmDyadicVaalerNearProductCoefficient X D m n /
            (n : ℝ) : ℝ) : ℂ) * ehmVaalerRationalPhase h n 1 m)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hnmem
      unfold ehmDyadicVaalerNearProductCoefficient
      rw [Finset.sum_div]
      push_cast
      rw [← mul_assoc, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hdmem
      have hdpos : 0 < d := by
        have hdlo := (Finset.mem_Icc.mp hdmem).1
        omega
      have hnpos : 0 < n := by
        have hnlo := (Finset.mem_Icc.mp hnmem).1
        omega
      by_cases hdn : d ∣ n
      · simp only [hdn, if_true]
        have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
        have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
        push_cast
        field_simp [hdC, hnC]
      · simp [hdn]

/-! ## Main-plus-near pairing on a common `m`-range -/

/-- The normalized main and near forms on the same `m`-range are exactly
one signed Möbius sum of paired additive rows. -/
theorem ehmDyadicVaalerNormalizedMain_add_nearMRange_eq_pairedAdditiveRows
    (h : ℤ) (X D J mLo mHi : ℕ) (hX : 1 ≤ X) :
    ehmDyadicVaalerNormalizedMainPhaseFormMRange h X J mLo mHi +
        ehmDyadicVaalerNormalizedNearPhaseFormMRange
          h X D J mLo mHi =
      ehmDyadicVaalerPairedAdditiveRowsMRange
        h X D J mLo mHi := by
  rw [ehmDyadicVaalerNormalizedMainPhaseFormMRange_eq_additiveRows,
    ehmDyadicVaalerNormalizedNearPhaseFormMRange_eq_productRows
      h X D J mLo mHi hX]
  classical
  unfold ehmDyadicVaalerMainAdditiveRowsMRange
    ehmDyadicVaalerNearProductRowsMRange
    ehmDyadicVaalerPairedAdditiveRowsMRange
    ehmDyadicVaalerPairedAdditiveRow
    ehmDyadicVaalerPairedProductCoefficient
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

private theorem ehmDyadicVaalerNormalizedMainPhaseFormMRange_split
    (h : ℤ) (X J U : ℕ) (hU : U ≤ 2 * X) :
    ehmDyadicVaalerNormalizedMainPhaseFormMRange h X J 1 (2 * X) =
      ehmDyadicVaalerNormalizedMainPhaseFormMRange h X J 1 U +
        ehmDyadicVaalerNormalizedMainPhaseFormMRange
          h X J (U + 1) (2 * X) := by
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
  unfold ehmDyadicVaalerNormalizedMainPhaseFormMRange
  rw [hwhole, Finset.sum_union hdis]

theorem ehmDyadicVaalerPairedAdditiveRowsMRange_split
    (h : ℤ) (X D J U : ℕ) (hU : U ≤ 2 * X) :
    ehmDyadicVaalerPairedAdditiveRowsMRange h X D J 1 (2 * X) =
      ehmDyadicVaalerPairedAdditiveRowsMRange h X D J 1 U +
        ehmDyadicVaalerPairedAdditiveRowsMRange
          h X D J (U + 1) (2 * X) := by
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
  unfold ehmDyadicVaalerPairedAdditiveRowsMRange
  rw [hwhole, Finset.sum_union hdis]

/-! ## Reconstruction of the complete normalized kernel phase -/

/-- Under the honest Type-I/II range condition, the complete normalized
kernel phase is the sum of the paired short- and long-`m` additive rows. -/
theorem ehmDyadicVaalerNormalizedKernelPhaseForm_eq_pairedTypeI_add_TypeII
    (h : ℤ) (X D J U : ℕ) (hX : 1 ≤ X) (hU : U ≤ 2 * X) :
    ehmDyadicVaalerNormalizedKernelPhaseForm h X D J U =
      ehmDyadicVaalerPairedAdditiveRowsMRange h X D J 1 U +
        ehmDyadicVaalerPairedAdditiveRowsMRange
          h X D J (U + 1) (2 * X) := by
  unfold ehmDyadicVaalerNormalizedKernelPhaseForm
  rw [ehmDyadicVaalerNormalizedMainPhaseForm_eq_mRange,
    ehmDyadicVaalerNormalizedMainPhaseFormMRange_split h X J U hU]
  rw [← ehmDyadicVaalerNormalizedMain_add_nearMRange_eq_pairedAdditiveRows
      h X D J 1 U hX,
    ← ehmDyadicVaalerNormalizedMain_add_nearMRange_eq_pairedAdditiveRows
      h X D J (U + 1) (2 * X) hX]
  ring

/-- Final one-row reconstruction: the normalized main, Type-I, and Type-II
frequency contributions form one product-coordinate additive row on
`1 ≤ m ≤ 2X`. -/
theorem ehmDyadicVaalerNormalizedKernelPhaseForm_eq_pairedAdditiveRows
    (h : ℤ) (X D J U : ℕ) (hX : 1 ≤ X) (hU : U ≤ 2 * X) :
    ehmDyadicVaalerNormalizedKernelPhaseForm h X D J U =
      ehmDyadicVaalerPairedAdditiveRowsMRange
        h X D J 1 (2 * X) := by
  rw [ehmDyadicVaalerNormalizedKernelPhaseForm_eq_pairedTypeI_add_TypeII
    h X D J U hX hU]
  exact (ehmDyadicVaalerPairedAdditiveRowsMRange_split
    h X D J U hU).symm

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows
