import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmHarmonicResonanceSplit

/-!
# Burgess-route orientation audit for the Ehm Vaaler forms

The normalized main term admits two exact orientations.  With `m` fixed it
is a von-Mangoldt-weighted additive character sum in `j`; with `j` fixed it
is a Möbius-weighted reciprocal phase sum in `m`.  The normalized near term
has the analogous reciprocal `m`-orientation, with a coupled `(m,d)`
amplitude and the harmonic phase row already treated by finite Abel
summation.

These identities identify the precise obstruction to a direct application
of a classical or mixed Burgess estimate: the multiplicative coefficient in
the reciprocal variable is `moebius m`, not a nonprincipal Dirichlet
character, and the phase in that variable is `exp(2*pi*i*A/m)`, not an
additive polynomial phase.  No Burgess estimate is assumed in this file.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmBurgessAudit

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHarmonicAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHarmonicResonanceSplit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerNormalizedCharacters

/-! ## Main term: additive-prime and reciprocal-Mobius orientations -/

/-- The signed dyadic Möbius weight in the normalized main form. -/
noncomputable def ehmDyadicVaalerMainMobiusWeight
    (X m : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
    ehmDyadicLogTaperAverage X m

/-- The logarithmic prime weight in the normalized main form. -/
noncomputable def ehmDyadicVaalerMainPrimeWeight (j : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt j / (j : ℝ)

/-- For fixed denominator `m`, the main row is an additive exponential sum
over the prime variable `j`. -/
noncomputable def ehmVaalerMainAdditivePrimeRow
    (h : ℤ) (J m : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 2 J,
    (ehmDyadicVaalerMainPrimeWeight j : ℂ) *
      ehmVaalerRationalPhase h j 1 m

/-- For fixed prime index `j`, the same main form is a Möbius-weighted
reciprocal exponential sum in `m`. -/
noncomputable def ehmVaalerMainReciprocalMobiusColumn
    (h : ℤ) (X j : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (2 * X),
    (ehmDyadicVaalerMainMobiusWeight X m : ℂ) *
      ehmVaalerRationalPhase h j 1 m

/-- Exact row orientation: an outer signed Möbius sum of additive prime
rows. -/
theorem ehmDyadicVaalerNormalizedMainPhaseForm_eq_mobius_additiveRows
    (h : ℤ) (X J : ℕ) :
    ehmDyadicVaalerNormalizedMainPhaseForm h X J =
      ∑ m ∈ Finset.Icc 1 (2 * X),
        (ehmDyadicVaalerMainMobiusWeight X m : ℂ) *
          ehmVaalerMainAdditivePrimeRow h J m := by
  classical
  unfold ehmDyadicVaalerNormalizedMainPhaseForm
    ehmDyadicVaalerMainMobiusWeight ehmVaalerMainAdditivePrimeRow
    ehmDyadicVaalerMainPrimeWeight
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- Exact column orientation: an outer von-Mangoldt sum of reciprocal
Möbius columns. -/
theorem ehmDyadicVaalerNormalizedMainPhaseForm_eq_prime_reciprocalColumns
    (h : ℤ) (X J : ℕ) :
    ehmDyadicVaalerNormalizedMainPhaseForm h X J =
      ∑ j ∈ Finset.Icc 2 J,
        (ehmDyadicVaalerMainPrimeWeight j : ℂ) *
          ehmVaalerMainReciprocalMobiusColumn h X j := by
  classical
  rw [ehmDyadicVaalerNormalizedMainPhaseForm_eq_mobius_additiveRows]
  unfold ehmVaalerMainAdditivePrimeRow
    ehmVaalerMainReciprocalMobiusColumn
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- In the row orientation the phase is the ordinary additive character
`exp(2*pi*i*h*j/m)` in `j`. -/
theorem ehmVaalerMainPhase_eq_additiveCharacter
    (h : ℤ) (j m : ℕ) :
    ehmVaalerRationalPhase h j 1 m =
      Complex.exp
        (((2 * Real.pi * (h : ℝ) *
          ((j : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  simpa using ehmVaalerRationalPhase_eq_exp h j 1 m

/-! ## Near term: reciprocal-Mobius columns with coupled amplitudes -/

/-- The signed Möbius weight of one near `(m,d)` amplitude before the
outer divisor weight is applied. -/
noncomputable def ehmDyadicVaalerNearMobiusAmplitude
    (X m d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
    ehmDyadicNearPairAmplitude X m d

/-- The outer signed divisor weight in the normalized near form. -/
noncomputable def ehmDyadicVaalerNearDivisorWeight (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ)

/-- For fixed `d`, the near form is a Möbius-weighted reciprocal column in
`m`; its amplitude remains genuinely coupled to `d`. -/
noncomputable def ehmVaalerNearReciprocalMobiusColumn
    (h : ℤ) (X J d mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi,
    (ehmDyadicVaalerNearMobiusAmplitude X m d : ℂ) *
      ehmVaalerHarmonicPhaseRow h J m d

/-- Exact near-column orientation.  This preserves the signs of both
Möbius factors and the full coupled amplitude. -/
theorem ehmDyadicVaalerNormalizedNearPhaseFormMRange_eq_reciprocalColumns
    (h : ℤ) (X D J mLo mHi : ℕ) :
    ehmDyadicVaalerNormalizedNearPhaseFormMRange
        h X D J mLo mHi =
      ∑ d ∈ Finset.Icc (X + 1) D,
        (ehmDyadicVaalerNearDivisorWeight d : ℂ) *
          ehmVaalerNearReciprocalMobiusColumn h X J d mLo mHi := by
  classical
  unfold ehmDyadicVaalerNormalizedNearPhaseFormMRange
    ehmDyadicVaalerNearDivisorWeight
    ehmVaalerNearReciprocalMobiusColumn
    ehmDyadicVaalerNearMobiusAmplitude
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  push_cast
  ring

/-- The near-column phase is reciprocal in `m`, with numerator `h*q*d`.
The harmonic `q`-sum is therefore not a Burgess sum in the reciprocal
variable. -/
theorem ehmVaalerNearPhase_eq_reciprocalCharacter
    (h : ℤ) (q d m : ℕ) :
    ehmVaalerRationalPhase h q d m =
      Complex.exp
        (((2 * Real.pi * (h : ℝ) *
          (((q * d : ℕ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I) :=
  ehmVaalerRationalPhase_eq_exp h q d m

end RH.Criteria.NymanBeurling.BCFLogTaperEhmBurgessAudit
