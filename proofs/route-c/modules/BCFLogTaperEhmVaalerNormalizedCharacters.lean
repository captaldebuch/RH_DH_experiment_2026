import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmVaalerAnalyticGate

/-!
# Normalized nonzero additive characters for the Ehm Vaaler route

The reciprocal quotient contributes a factor `m/(q*d)` (or `m/j`).  This
file cancels that factor exactly against the `1/m` already present in the
Möbius cutoff coefficients.  The resulting phase forms display the signed
Möbius variables and harmonic weights without artificial denominators.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerNormalizedCharacters

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit

/-! ## Harmonic phase rows -/

/-- The genuinely oscillatory harmonic row left after removing the rational
quotient denominator. -/
noncomputable def ehmVaalerHarmonicPhaseRow
    (h : ℤ) (J m d : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (J / d),
    ehmVaalerRationalPhase h q d m / (q : ℂ)

/-- The quotient-weighted row is exactly `m/d` times its harmonic form. -/
theorem ehmVaalerWeightedPhaseRow_eq_mul_harmonic
    (h : ℤ) (J m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    ehmVaalerWeightedPhaseRow h J m d =
      (((m : ℝ) / (d : ℝ) : ℝ) : ℂ) *
        ehmVaalerHarmonicPhaseRow h J m d := by
  classical
  unfold ehmVaalerWeightedPhaseRow ehmVaalerHarmonicPhaseRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
  have hmR : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdR : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hqR : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  push_cast
  field_simp [hmR, hdR, hqR]

/-! ## Main-form normalization -/

/-- The completed main phase after exact cancellation of the artificial
`m` denominator. -/
noncomputable def ehmDyadicVaalerNormalizedMainPhaseForm
    (h : ℤ) (X J : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
    (((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
      ehmDyadicLogTaperAverage X m *
      (ArithmeticFunction.vonMangoldt j / (j : ℝ))) : ℝ) : ℂ) *
        ehmVaalerRationalPhase h j 1 m

theorem ehmDyadicVaalerMainPhaseSummand_normalized
    (h : ℤ) (X m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    ((ArithmeticFunction.vonMangoldt j *
      ehmDyadicMobiusCutoffCoeff X m : ℝ) : ℂ) *
        ehmVaalerRationalPhase h j 1 m /
          ((((j : ℝ) / (m : ℝ)) : ℝ) : ℂ) =
      (((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        ehmDyadicLogTaperAverage X m *
        (ArithmeticFunction.vonMangoldt j / (j : ℝ))) : ℝ) : ℂ) *
          ehmVaalerRationalPhase h j 1 m := by
  rw [ehmDyadicMobiusCutoffCoeff_eq_moebius_mul_average]
  have hmR : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hjR : (j : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
  push_cast
  field_simp [hmR, hjR]

theorem ehmDyadicVaalerMainPhaseForm_eq_normalized
    (h : ℤ) (X J : ℕ) :
    ehmDyadicVaalerMainPhaseForm h X J =
      ehmDyadicVaalerNormalizedMainPhaseForm h X J := by
  classical
  unfold ehmDyadicVaalerMainPhaseForm
    ehmDyadicVaalerNormalizedMainPhaseForm
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  apply Finset.sum_congr rfl
  intro j hj
  have hjpos : 0 < j := by
    have : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    omega
  exact ehmDyadicVaalerMainPhaseSummand_normalized h X m j hmpos hjpos

/-! ## Near Type-I/II normalization -/

/-- The normalized near phase form.  Its coefficient is visibly
`mu(m)*mu(d)*amplitude/d`, and its inner oscillation has harmonic weight
`1/q`. -/
noncomputable def ehmDyadicVaalerNormalizedNearPhaseFormMRange
    (h : ℤ) (X D J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
    (((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ehmDyadicNearPairAmplitude X m d / (d : ℝ)) : ℝ) : ℂ) *
        ehmVaalerHarmonicPhaseRow h J m d

theorem ehmDyadicVaalerNearPhaseSummand_normalized
    (h : ℤ) (X J m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    (ehmDyadicNearKernelWeight X m d : ℂ) *
        ehmVaalerWeightedPhaseRow h J m d =
      (((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        ehmDyadicNearPairAmplitude X m d / (d : ℝ)) : ℝ) : ℂ) *
          ehmVaalerHarmonicPhaseRow h J m d := by
  rw [ehmVaalerWeightedPhaseRow_eq_mul_harmonic h J m d hm hd]
  unfold ehmDyadicNearKernelWeight
  have hmR : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdR : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp [hmR, hdR]

theorem ehmDyadicVaalerNearPhaseFormMRange_eq_normalized
    (h : ℤ) (X D J mLo mHi : ℕ) (hmLo : 0 < mLo) :
    ehmDyadicVaalerNearPhaseFormMRange h X D J mLo mHi =
      ehmDyadicVaalerNormalizedNearPhaseFormMRange
        h X D J mLo mHi := by
  classical
  unfold ehmDyadicVaalerNearPhaseFormMRange
    ehmDyadicVaalerNormalizedNearPhaseFormMRange
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := lt_of_lt_of_le hmLo (Finset.mem_Icc.mp hm).1
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := by
    have : X + 1 ≤ d := (Finset.mem_Icc.mp hd).1
    omega
  exact ehmDyadicVaalerNearPhaseSummand_normalized
    h X J m d hmpos hdpos

/-- The complete normalized phase at one nonzero (or zero) frequency. -/
noncomputable def ehmDyadicVaalerNormalizedKernelPhaseForm
    (h : ℤ) (X D J U : ℕ) : ℂ :=
  ehmDyadicVaalerNormalizedMainPhaseForm h X J +
    ehmDyadicVaalerNormalizedNearPhaseFormMRange h X D J 1 U +
    ehmDyadicVaalerNormalizedNearPhaseFormMRange
      h X D J (U + 1) (2 * X)

theorem ehmDyadicVaalerKernelNormalPhaseForm_eq_normalized
    (h : ℤ) (X D J U : ℕ) :
    ehmDyadicVaalerKernelNormalPhaseForm h X D J U =
      ehmDyadicVaalerNormalizedKernelPhaseForm h X D J U := by
  unfold ehmDyadicVaalerKernelNormalPhaseForm
    ehmDyadicVaalerNormalizedKernelPhaseForm
  rw [ehmDyadicVaalerMainPhaseForm_eq_normalized,
    ehmDyadicVaalerNearPhaseFormMRange_eq_normalized h X D J 1 U (by omega),
    ehmDyadicVaalerNearPhaseFormMRange_eq_normalized
      h X D J (U + 1) (2 * X) (by omega)]

/-- The remaining Fourier sum in its final normalized signed-Möbius form. -/
theorem ehmDyadicVaalerKernelNormalNonzeroModes_eq_normalized
    (V : QuadraticInteraction.VaalerSawtoothPackage)
    (H X D J U : ℕ) :
    ehmDyadicVaalerKernelNormalNonzeroModes V H X D J U =
      ∑ h ∈ (V.frequencies H).erase 0,
        V.coefficient H h *
          ehmDyadicVaalerNormalizedKernelPhaseForm h X D J U := by
  classical
  unfold ehmDyadicVaalerKernelNormalNonzeroModes
  apply Finset.sum_congr rfl
  intro h _
  rw [ehmDyadicVaalerKernelNormalPhaseForm_eq_normalized]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerNormalizedCharacters
