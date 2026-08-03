import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmVaalerNormalizedCharacters

/-!
# Abel summation and resonance bounds for the Ehm harmonic phase row

The normalized near Vaaler form contains the finite harmonic row

```text
sum_{1 <= q <= Q} exp(2*pi*i*h*q*d/m) / q.
```

This file applies finite Abel summation, evaluates the geometric prefixes,
and proves the standard nonresonant bound.  It also identifies resonance
exactly as the integer divisibility condition `m | h*d`.

These estimates control the inner `q` variable.  They do not supply the
remaining signed cancellation in the outer Möbius variables `m,d`.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmHarmonicAbel

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerNormalizedCharacters

/-- The first `K` terms of the unweighted additive-character row. -/
noncomputable def ehmVaalerGeometricPrefix
    (h : ℤ) (K m d : ℕ) : ℂ :=
  ∑ r ∈ Finset.range K,
    ehmVaalerRationalPhase h (r + 1) d m

/-- Reindex the positive harmonic row by `Finset.range`. -/
theorem ehmVaalerHarmonicSum_eq_range
    (h : ℤ) (Q m d : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q,
      ehmVaalerRationalPhase h q d m / (q : ℂ)) =
    ∑ i ∈ Finset.range Q,
      ((1 : ℂ) / ((i + 1 : ℕ) : ℂ)) *
        ehmVaalerRationalPhase h (i + 1) d m := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.one_add]
  ring

/-- Exact finite Abel summation for the harmonic reciprocal phase. -/
theorem ehmVaalerHarmonicSum_eq_abel
    (h : ℤ) (Q m d : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q,
      ehmVaalerRationalPhase h q d m / (q : ℂ)) =
      ((1 : ℂ) / (Q : ℂ)) * ehmVaalerGeometricPrefix h Q m d +
      ∑ i ∈ Finset.range (Q - 1),
        (((1 : ℂ) / ((i + 1 : ℕ) : ℂ)) -
          ((1 : ℂ) / ((i + 2 : ℕ) : ℂ))) *
            ehmVaalerGeometricPrefix h (i + 1) m d := by
  rw [ehmVaalerHarmonicSum_eq_range]
  have hs := Finset.sum_range_by_parts
    (fun i : ℕ ↦ (1 : ℂ) / ((i + 1 : ℕ) : ℂ))
    (fun i : ℕ ↦ ehmVaalerRationalPhase h (i + 1) d m) Q
  simp only [smul_eq_mul] at hs
  rw [hs]
  unfold ehmVaalerGeometricPrefix
  by_cases hQ : Q = 0
  · simp [hQ]
  · have hsub : Q - 1 + 1 = Q :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hQ)
    rw [hsub]
    simp_rw [Nat.add_assoc, Nat.one_add]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Rational phases form powers of their first-step phase. -/
theorem ehmVaalerRationalPhase_eq_pow
    (h : ℤ) (q d m : ℕ) :
    ehmVaalerRationalPhase h q d m =
      (ehmVaalerRationalPhase h 1 d m) ^ q := by
  rw [ehmVaalerRationalPhase_eq_exp,
    ehmVaalerRationalPhase_eq_exp]
  rw [show
    (((2 * Real.pi * (h : ℝ) *
      (((q * d : ℕ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I) =
      (q : ℂ) *
        (((2 * Real.pi * (h : ℝ) *
          (((1 * d : ℕ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I) by
    push_cast
    ring]
  exact Complex.exp_nat_mul _ q

theorem norm_ehmVaalerRationalPhase
    (h : ℤ) (q d m : ℕ) :
    ‖ehmVaalerRationalPhase h q d m‖ = 1 := by
  rw [ehmVaalerRationalPhase_eq_exp]
  exact Complex.norm_exp_ofReal_mul_I _

/-- A geometric prefix is the usual finite geometric series multiplied by
its first-step phase. -/
theorem ehmVaalerGeometricPrefix_eq_geomSum
    (h : ℤ) (K m d : ℕ) :
    ehmVaalerGeometricPrefix h K m d =
      ehmVaalerRationalPhase h 1 d m *
        ∑ r ∈ Finset.range K,
          (ehmVaalerRationalPhase h 1 d m) ^ r := by
  classical
  unfold ehmVaalerGeometricPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [ehmVaalerRationalPhase_eq_pow, pow_succ']

theorem ehmVaalerGeometricPrefix_mul_phase_sub_one
    (h : ℤ) (K m d : ℕ) :
    ehmVaalerGeometricPrefix h K m d *
        (ehmVaalerRationalPhase h 1 d m - 1) =
      (ehmVaalerRationalPhase h 1 d m) ^ (K + 1) -
        ehmVaalerRationalPhase h 1 d m := by
  rw [ehmVaalerGeometricPrefix_eq_geomSum]
  rw [mul_assoc, geom_sum_mul]
  rw [pow_succ']
  ring

/-- Standard nonresonant geometric-prefix bound. -/
theorem norm_ehmVaalerGeometricPrefix_le
    (h : ℤ) (K m d : ℕ)
    (hnon : ehmVaalerRationalPhase h 1 d m ≠ 1) :
    ‖ehmVaalerGeometricPrefix h K m d‖ ≤
      2 / ‖ehmVaalerRationalPhase h 1 d m - 1‖ := by
  let z := ehmVaalerRationalPhase h 1 d m
  have hz : ‖z‖ = 1 := norm_ehmVaalerRationalPhase h 1 d m
  have hden : 0 < ‖z - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hnon)
  have hclosed : ehmVaalerGeometricPrefix h K m d =
      (z ^ (K + 1) - z) / (z - 1) := by
    apply (eq_div_iff (sub_ne_zero.mpr hnon)).2
    simpa [z] using
      ehmVaalerGeometricPrefix_mul_phase_sub_one h K m d
  rw [hclosed, norm_div]
  apply (div_le_div_iff_of_pos_right hden).2
  calc
    ‖z ^ (K + 1) - z‖ ≤ ‖z ^ (K + 1)‖ + ‖z‖ :=
      norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, one_pow]; norm_num

/-! ## Exact resonance classification -/

theorem complex_exp_int_rational_eq_one_iff_dvd
    (k : ℤ) (N : ℕ) (hN : N ≠ 0) :
    Complex.exp
      (2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ)) = 1 ↔
        (N : ℤ) ∣ k := by
  rw [Complex.exp_eq_one_iff]
  conv in _ = _ =>
    rw [← mul_comm (2 * Real.pi * Complex.I), mul_div_assoc,
      mul_right_inj' (by simp)]
  field_simp [Nat.cast_ne_zero.mpr hN]
  norm_cast

/-- A nonzero Vaaler frequency can still resonate.  Resonance occurs
precisely on the divisibility diagonal `m | h*d`. -/
theorem ehmVaalerRationalPhase_one_eq_one_iff_dvd
    (h : ℤ) (d m : ℕ) (hm : m ≠ 0) :
    ehmVaalerRationalPhase h 1 d m = 1 ↔
      (m : ℤ) ∣ h * (d : ℤ) := by
  rw [ehmVaalerRationalPhase_eq_exp]
  rw [show
    (((2 * Real.pi * (h : ℝ) *
      (((1 * d : ℕ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I) =
      2 * Real.pi * Complex.I * ((h * (d : ℤ) : ℤ) : ℂ) /
        (m : ℂ) by
    push_cast
    ring]
  exact complex_exp_int_rational_eq_one_iff_dvd
    (h * (d : ℤ)) m hm

/-! ## Harmonic row bound -/

private theorem harmonicCoefficientSum (Q : ℕ) (hQ : 0 < Q) :
    (1 : ℝ) / (Q : ℝ) +
      ∑ i ∈ Finset.range (Q - 1),
        ((1 : ℝ) / ((i + 1 : ℕ) : ℝ) -
          (1 : ℝ) / ((i + 2 : ℕ) : ℝ)) = 1 := by
  have hs := Finset.sum_range_sub'
    (fun i : ℕ ↦ (1 : ℝ) / ((i + 1 : ℕ) : ℝ)) (Q - 1)
  have hsub : Q - 1 + 1 = Q := Nat.sub_add_cancel hQ
  simp only [Nat.zero_add, Nat.cast_one, div_one, hsub] at hs
  linarith

private theorem norm_one_div_natCast (n : ℕ) :
    ‖(1 : ℂ) / (n : ℂ)‖ = (1 : ℝ) / (n : ℝ) := by
  rw [norm_div]
  simp

private theorem harmonicDifference_nonneg (i : ℕ) :
    0 ≤ (1 : ℝ) / ((i + 1 : ℕ) : ℝ) -
      (1 : ℝ) / ((i + 2 : ℕ) : ℝ) := by
  have hi : (0 : ℝ) < (i + 1 : ℕ) := by positivity
  have hle : ((i + 1 : ℕ) : ℝ) ≤ (i + 2 : ℕ) := by
    norm_cast
    omega
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hi hle)

private theorem norm_harmonicDifference (i : ℕ) :
    ‖((1 : ℂ) / ((i + 1 : ℕ) : ℂ)) -
      ((1 : ℂ) / ((i + 2 : ℕ) : ℂ))‖ =
        (1 : ℝ) / ((i + 1 : ℕ) : ℝ) -
          (1 : ℝ) / ((i + 2 : ℕ) : ℝ) := by
  have hnonneg := harmonicDifference_nonneg i
  rw [show
    ((1 : ℂ) / ((i + 1 : ℕ) : ℂ)) -
      ((1 : ℂ) / ((i + 2 : ℕ) : ℂ)) =
        (((1 : ℝ) / ((i + 1 : ℕ) : ℝ) -
          (1 : ℝ) / ((i + 2 : ℕ) : ℝ) : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]

/-- Abel summation transfers the geometric-prefix bound to the entire
harmonic row, uniformly in its length. -/
theorem norm_ehmVaalerHarmonicPhaseRow_le
    (h : ℤ) (J m d : ℕ)
    (hnon : ehmVaalerRationalPhase h 1 d m ≠ 1) :
    ‖ehmVaalerHarmonicPhaseRow h J m d‖ ≤
      2 / ‖ehmVaalerRationalPhase h 1 d m - 1‖ := by
  let Q := J / d
  let M : ℝ := 2 / ‖ehmVaalerRationalPhase h 1 d m - 1‖
  have hM : 0 ≤ M := div_nonneg (by norm_num) (norm_nonneg _)
  unfold ehmVaalerHarmonicPhaseRow
  change ‖∑ q ∈ Finset.Icc 1 Q,
    ehmVaalerRationalPhase h q d m / (q : ℂ)‖ ≤ _
  by_cases hQ : Q = 0
  · simp [hQ, hM, M]
  · have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ
    rw [ehmVaalerHarmonicSum_eq_abel]
    calc
      ‖(1 / (Q : ℂ)) * ehmVaalerGeometricPrefix h Q m d +
          ∑ i ∈ Finset.range (Q - 1),
            (1 / ((i + 1 : ℕ) : ℂ) -
              1 / ((i + 2 : ℕ) : ℂ)) *
                ehmVaalerGeometricPrefix h (i + 1) m d‖ ≤
        ‖(1 / (Q : ℂ)) * ehmVaalerGeometricPrefix h Q m d‖ +
          ‖∑ i ∈ Finset.range (Q - 1),
            (1 / ((i + 1 : ℕ) : ℂ) -
              1 / ((i + 2 : ℕ) : ℂ)) *
                ehmVaalerGeometricPrefix h (i + 1) m d‖ :=
        norm_add_le _ _
      _ ≤ ‖(1 / (Q : ℂ)) * ehmVaalerGeometricPrefix h Q m d‖ +
          ∑ i ∈ Finset.range (Q - 1),
            ‖(1 / ((i + 1 : ℕ) : ℂ) -
              1 / ((i + 2 : ℕ) : ℂ)) *
                ehmVaalerGeometricPrefix h (i + 1) m d‖ := by
        gcongr
        exact norm_sum_le _ _
      _ ≤ ((1 : ℝ) / (Q : ℝ)) * M +
          ∑ i ∈ Finset.range (Q - 1),
            ((1 : ℝ) / ((i + 1 : ℕ) : ℝ) -
              (1 : ℝ) / ((i + 2 : ℕ) : ℝ)) * M := by
        gcongr with i hi
        · rw [norm_mul, norm_one_div_natCast]
          gcongr
          exact norm_ehmVaalerGeometricPrefix_le h Q m d hnon
        · rw [norm_mul, norm_harmonicDifference]
          exact mul_le_mul_of_nonneg_left
            (norm_ehmVaalerGeometricPrefix_le h (i + 1) m d hnon)
            (harmonicDifference_nonneg i)
      _ = M := by
        rw [← Finset.sum_mul]
        rw [← add_mul, harmonicCoefficientSum Q hQpos]
        simp
      _ = 2 / ‖ehmVaalerRationalPhase h 1 d m - 1‖ := rfl

/-- Divisibility is the only obstruction to the nonresonant harmonic-row
bound. -/
theorem norm_ehmVaalerHarmonicPhaseRow_le_of_not_dvd
    (h : ℤ) (J m d : ℕ) (hm : m ≠ 0)
    (hnon : ¬(m : ℤ) ∣ h * (d : ℤ)) :
    ‖ehmVaalerHarmonicPhaseRow h J m d‖ ≤
      2 / ‖ehmVaalerRationalPhase h 1 d m - 1‖ := by
  apply norm_ehmVaalerHarmonicPhaseRow_le
  exact fun hphase ↦ hnon
    ((ehmVaalerRationalPhase_one_eq_one_iff_dvd h d m hm).1 hphase)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmHarmonicAbel
