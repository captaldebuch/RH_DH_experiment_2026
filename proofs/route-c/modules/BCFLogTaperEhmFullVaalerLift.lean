import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit

/-!
# Full weighted Vaaler lift for the Ehm Type-I/II form

This file lifts the row-level Vaaler identity through the complete weighted
`(m,d)` Möbius bilinear sum and through the completed von-Mangoldt main form.
It then reorganizes the finite sums by Fourier frequency.

Everything here is an exact finite identity.  The zero and nonzero modes are
separated without claiming that either cancels or is small.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbolicKernelNormalForm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit
open RH.Criteria.NymanBeurling.QuadraticInteraction
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## Weighted near bilinear lift -/

/-- The real weight multiplying one collapsed near `q`-kernel. -/
noncomputable def ehmDyadicNearKernelWeight (X m d : ℕ) : ℝ :=
  ((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)) / (m : ℝ)) *
    ehmDyadicNearPairAmplitude X m d

/-- The Vaaler approximant lifted through an arbitrary `m` interval of the
near bilinear form. -/
noncomputable def ehmDyadicVaalerNearApproxMRange
    (V : VaalerSawtoothPackage) (H X D J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
    (ehmDyadicNearKernelWeight X m d : ℂ) *
      ehmVaalerBernoulliKernelApprox V H J m d

/-- The complete Vaaler error lifted through the same weighted interval. -/
noncomputable def ehmDyadicVaalerNearErrorMRange
    (V : VaalerSawtoothPackage) (H X D J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
    (ehmDyadicNearKernelWeight X m d : ℂ) *
      ehmVaalerBernoulliKernelError V H J m d

/-- The full real near Möbius kernel is the displayed weighted form. -/
theorem ehmDyadicNearMobiusKernelMRange_eq_weighted
    (R1 : ℝ → ℝ) (X D J mLo mHi : ℕ) :
    ehmDyadicNearMobiusKernelMRange R1 X D J mLo mHi =
      ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
        ehmDyadicNearKernelWeight X m d *
          ehmDyadicReciprocalQKernel R1 J m d := by
  unfold ehmDyadicNearMobiusKernelMRange ehmDyadicNearKernelWeight
  rfl

/-- Exact Vaaler decomposition after all near Möbius and taper weights have
been inserted. -/
theorem ehmDyadicNearBernoulliMRange_eq_vaaler
    (V : VaalerSawtoothPackage) (H X D J mLo mHi : ℕ) :
    ((ehmDyadicNearMobiusKernelMRange ehmR1BernoulliSawtoothPart
      X D J mLo mHi : ℝ) : ℂ) =
      ehmDyadicVaalerNearApproxMRange V H X D J mLo mHi +
        ehmDyadicVaalerNearErrorMRange V H X D J mLo mHi := by
  rw [ehmDyadicNearMobiusKernelMRange_eq_weighted]
  calc
    ((∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
        ehmDyadicNearKernelWeight X m d *
          ehmDyadicReciprocalQKernel ehmR1BernoulliSawtoothPart
            J m d : ℝ) : ℂ) =
      ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
        (ehmDyadicNearKernelWeight X m d : ℂ) *
          ((ehmDyadicReciprocalQKernel ehmR1BernoulliSawtoothPart
            J m d : ℝ) : ℂ) := by
      push_cast
      rfl
    _ = ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
        (ehmDyadicNearKernelWeight X m d : ℂ) *
          (ehmVaalerBernoulliKernelApprox V H J m d +
            ehmVaalerBernoulliKernelError V H J m d) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro d _
      rw [ehmDyadicBernoulliQKernel_eq_vaaler]
    _ = ehmDyadicVaalerNearApproxMRange V H X D J mLo mHi +
        ehmDyadicVaalerNearErrorMRange V H X D J mLo mHi := by
      unfold ehmDyadicVaalerNearApproxMRange
        ehmDyadicVaalerNearErrorMRange
      simp_rw [mul_add, Finset.sum_add_distrib]

/-! ## Completed main-form lift -/

/-- Vaaler approximant for one Bernoulli quotient at the rational point
`j/m`, already expanded into its finite Fourier modes. -/
noncomputable def ehmVaalerBernoulliPointApprox
    (V : VaalerSawtoothPackage) (H j m : ℕ) : ℂ :=
  ∑ h ∈ V.frequencies H,
    V.coefficient H h * ehmVaalerRationalPhase h j 1 m /
      ((((j : ℝ) / (m : ℝ)) : ℝ) : ℂ)

/-- Vaaler error for the same Bernoulli quotient. -/
noncomputable def ehmVaalerBernoulliPointError
    (V : VaalerSawtoothPackage) (H j m : ℕ) : ℂ :=
  vaalerSawtoothError V H ((j : ℝ) / (m : ℝ)) /
    ((((j : ℝ) / (m : ℝ)) : ℝ) : ℂ)

/-- Exact Vaaler expansion at one positive rational point. -/
theorem ehmR1BernoulliSawtoothPart_natRatio_eq_vaaler
    (V : VaalerSawtoothPackage) (H j m : ℕ) :
    ((ehmR1BernoulliSawtoothPart ((j : ℝ) / (m : ℝ)) : ℝ) : ℂ) =
      ehmVaalerBernoulliPointApprox V H j m +
        ehmVaalerBernoulliPointError V H j m := by
  unfold ehmR1BernoulliSawtoothPart ehmVaalerBernoulliPointApprox
    ehmVaalerBernoulliPointError ehmVaalerRationalPhase
  push_cast
  rw [vaalerSawtooth_decomposition]
  rw [add_div]
  congr 1
  rw [vaalerSawtoothApprox, V.finite_fourier, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- The completed von-Mangoldt main-form Vaaler approximant. -/
noncomputable def ehmDyadicVaalerMainApprox
    (V : VaalerSawtoothPackage) (H X J : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
    ((ArithmeticFunction.vonMangoldt j *
      ehmDyadicMobiusCutoffCoeff X m : ℝ) : ℂ) *
        ehmVaalerBernoulliPointApprox V H j m

/-- The completed main-form Vaaler error. -/
noncomputable def ehmDyadicVaalerMainError
    (V : VaalerSawtoothPackage) (H X J : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
    ((ArithmeticFunction.vonMangoldt j *
      ehmDyadicMobiusCutoffCoeff X m : ℝ) : ℂ) *
        ehmVaalerBernoulliPointError V H j m

/-- Exact Vaaler decomposition of the completed main form. -/
theorem ehmDyadicFullMainBernoulli_eq_vaaler
    (V : VaalerSawtoothPackage) (H X J : ℕ) :
    ((ehmDyadicFullMainJointSum ehmR1BernoulliSawtoothPart X J : ℝ) : ℂ) =
      ehmDyadicVaalerMainApprox V H X J +
        ehmDyadicVaalerMainError V H X J := by
  unfold ehmDyadicFullMainJointSum
  calc
    ((∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
        ArithmeticFunction.vonMangoldt j *
          ehmDyadicMobiusCutoffCoeff X m *
            ehmR1BernoulliSawtoothPart
              ((j : ℝ) / (m : ℝ)) : ℝ) : ℂ) =
      ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
        ((ArithmeticFunction.vonMangoldt j *
          ehmDyadicMobiusCutoffCoeff X m : ℝ) : ℂ) *
            ((ehmR1BernoulliSawtoothPart
              ((j : ℝ) / (m : ℝ)) : ℝ) : ℂ) := by
      push_cast
      rfl
    _ = ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
        ((ArithmeticFunction.vonMangoldt j *
          ehmDyadicMobiusCutoffCoeff X m : ℝ) : ℂ) *
            (ehmVaalerBernoulliPointApprox V H j m +
              ehmVaalerBernoulliPointError V H j m) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro j _
      rw [ehmR1BernoulliSawtoothPart_natRatio_eq_vaaler]
    _ = ehmDyadicVaalerMainApprox V H X J +
        ehmDyadicVaalerMainError V H X J := by
      unfold ehmDyadicVaalerMainApprox ehmDyadicVaalerMainError
      simp_rw [mul_add, Finset.sum_add_distrib]

/-! ## Type-I/II and coupled normal-form lift -/

/-- The Type-I Vaaler approximant in the collapsed kernel coordinates. -/
noncomputable def ehmDyadicVaalerNearTypeIApprox
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) : ℂ :=
  ehmDyadicVaalerNearApproxMRange V H X D J 1 U

/-- The Type-I accumulated Vaaler error. -/
noncomputable def ehmDyadicVaalerNearTypeIError
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) : ℂ :=
  ehmDyadicVaalerNearErrorMRange V H X D J 1 U

/-- The Type-II Vaaler approximant in the collapsed kernel coordinates. -/
noncomputable def ehmDyadicVaalerNearTypeIIApprox
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) : ℂ :=
  ehmDyadicVaalerNearApproxMRange V H X D J (U + 1) (2 * X)

/-- The Type-II accumulated Vaaler error. -/
noncomputable def ehmDyadicVaalerNearTypeIIError
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) : ℂ :=
  ehmDyadicVaalerNearErrorMRange V H X D J (U + 1) (2 * X)

theorem ehmDyadicNearKernelTypeI_Bernoulli_eq_vaaler
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) :
    ((ehmDyadicNearKernelTypeI ehmR1BernoulliSawtoothPart
      X D J U : ℝ) : ℂ) =
      ehmDyadicVaalerNearTypeIApprox V H X D J U +
        ehmDyadicVaalerNearTypeIError V H X D J U := by
  simpa [ehmDyadicNearKernelTypeI,
    ehmDyadicVaalerNearTypeIApprox, ehmDyadicVaalerNearTypeIError] using
      ehmDyadicNearBernoulliMRange_eq_vaaler V H X D J 1 U

theorem ehmDyadicNearKernelTypeII_Bernoulli_eq_vaaler
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) :
    ((ehmDyadicNearKernelTypeII ehmR1BernoulliSawtoothPart
      X D J U : ℝ) : ℂ) =
      ehmDyadicVaalerNearTypeIIApprox V H X D J U +
        ehmDyadicVaalerNearTypeIIError V H X D J U := by
  simpa [ehmDyadicNearKernelTypeII,
    ehmDyadicVaalerNearTypeIIApprox, ehmDyadicVaalerNearTypeIIError] using
      ehmDyadicNearBernoulliMRange_eq_vaaler
        V H X D J (U + 1) (2 * X)

/-- The complete Vaaler approximant for the main plus Type-I plus Type-II
Bernoulli normal form. -/
noncomputable def ehmDyadicVaalerKernelNormalApprox
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) : ℂ :=
  ehmDyadicVaalerMainApprox V H X J +
    ehmDyadicVaalerNearTypeIApprox V H X D J U +
    ehmDyadicVaalerNearTypeIIApprox V H X D J U

/-- The matching accumulated Vaaler error for all three finite forms. -/
noncomputable def ehmDyadicVaalerKernelNormalError
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) : ℂ :=
  ehmDyadicVaalerMainError V H X J +
    ehmDyadicVaalerNearTypeIError V H X D J U +
    ehmDyadicVaalerNearTypeIIError V H X D J U

/-- Exact Vaaler lift through the full completed weighted `(m,d)` form. -/
theorem ehmDyadicKernelNormalBernoulli_eq_vaaler
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) :
    ((ehmDyadicKernelNormalCoupledPart ehmR1BernoulliSawtoothPart
      X D J U : ℝ) : ℂ) =
      ehmDyadicVaalerKernelNormalApprox V H X D J U +
        ehmDyadicVaalerKernelNormalError V H X D J U := by
  unfold ehmDyadicKernelNormalCoupledPart
  push_cast
  rw [ehmDyadicFullMainBernoulli_eq_vaaler,
    ehmDyadicNearKernelTypeI_Bernoulli_eq_vaaler,
    ehmDyadicNearKernelTypeII_Bernoulli_eq_vaaler]
  unfold ehmDyadicVaalerKernelNormalApprox
    ehmDyadicVaalerKernelNormalError
  ring

/-! ## Frequency-first reciprocal-phase form -/

/-- The completed main-form contribution carried by one Vaaler frequency. -/
noncomputable def ehmDyadicVaalerMainPhaseForm
    (h : ℤ) (X J : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
    ((ArithmeticFunction.vonMangoldt j *
      ehmDyadicMobiusCutoffCoeff X m : ℝ) : ℂ) *
        ehmVaalerRationalPhase h j 1 m /
          ((((j : ℝ) / (m : ℝ)) : ℝ) : ℂ)

/-- The near `(m,d)` contribution carried by one Vaaler frequency on an
arbitrary `m` interval. -/
noncomputable def ehmDyadicVaalerNearPhaseFormMRange
    (h : ℤ) (X D J mLo mHi : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
    (ehmDyadicNearKernelWeight X m d : ℂ) *
      ehmVaalerWeightedPhaseRow h J m d

/-- One frequency of the complete main plus Type-I plus Type-II normal form. -/
noncomputable def ehmDyadicVaalerKernelNormalPhaseForm
    (h : ℤ) (X D J U : ℕ) : ℂ :=
  ehmDyadicVaalerMainPhaseForm h X J +
    ehmDyadicVaalerNearPhaseFormMRange h X D J 1 U +
    ehmDyadicVaalerNearPhaseFormMRange h X D J (U + 1) (2 * X)

theorem ehmDyadicVaalerMainApprox_eq_frequencySum
    (V : VaalerSawtoothPackage) (H X J : ℕ) :
    ehmDyadicVaalerMainApprox V H X J =
      ∑ h ∈ V.frequencies H,
        V.coefficient H h * ehmDyadicVaalerMainPhaseForm h X J := by
  classical
  unfold ehmDyadicVaalerMainApprox ehmVaalerBernoulliPointApprox
    ehmDyadicVaalerMainPhaseForm
  calc
    (∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
        ((ArithmeticFunction.vonMangoldt j *
          ehmDyadicMobiusCutoffCoeff X m : ℝ) : ℂ) *
          ∑ h ∈ V.frequencies H,
            V.coefficient H h * ehmVaalerRationalPhase h j 1 m /
              ((((j : ℝ) / (m : ℝ)) : ℝ) : ℂ)) =
      ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
        ∑ h ∈ V.frequencies H,
          ((ArithmeticFunction.vonMangoldt j *
            ehmDyadicMobiusCutoffCoeff X m : ℝ) : ℂ) *
            (V.coefficient H h * ehmVaalerRationalPhase h j 1 m /
              ((((j : ℝ) / (m : ℝ)) : ℝ) : ℂ)) := by
        simp_rw [Finset.mul_sum]
    _ =
      ∑ m ∈ Finset.Icc 1 (2 * X), ∑ h ∈ V.frequencies H,
        ∑ j ∈ Finset.Icc 2 J,
          ((ArithmeticFunction.vonMangoldt j *
            ehmDyadicMobiusCutoffCoeff X m : ℝ) : ℂ) *
            (V.coefficient H h * ehmVaalerRationalPhase h j 1 m /
              ((((j : ℝ) / (m : ℝ)) : ℝ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.sum_comm]
    _ = ∑ h ∈ V.frequencies H, ∑ m ∈ Finset.Icc 1 (2 * X),
        ∑ j ∈ Finset.Icc 2 J,
          ((ArithmeticFunction.vonMangoldt j *
            ehmDyadicMobiusCutoffCoeff X m : ℝ) : ℂ) *
            (V.coefficient H h * ehmVaalerRationalPhase h j 1 m /
              ((((j : ℝ) / (m : ℝ)) : ℝ) : ℂ)) := by
        rw [Finset.sum_comm]
    _ = ∑ h ∈ V.frequencies H,
        V.coefficient H h *
          ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
            ((ArithmeticFunction.vonMangoldt j *
              ehmDyadicMobiusCutoffCoeff X m : ℝ) : ℂ) *
                ehmVaalerRationalPhase h j 1 m /
                  ((((j : ℝ) / (m : ℝ)) : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro h _
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro j _
        ring

theorem ehmDyadicVaalerNearApproxMRange_eq_frequencySum
    (V : VaalerSawtoothPackage) (H X D J mLo mHi : ℕ) :
    ehmDyadicVaalerNearApproxMRange V H X D J mLo mHi =
      ∑ h ∈ V.frequencies H,
        V.coefficient H h *
          ehmDyadicVaalerNearPhaseFormMRange h X D J mLo mHi := by
  classical
  unfold ehmDyadicVaalerNearApproxMRange
    ehmVaalerBernoulliKernelApprox
    ehmDyadicVaalerNearPhaseFormMRange
  calc
    (∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
        (ehmDyadicNearKernelWeight X m d : ℂ) *
          ∑ h ∈ V.frequencies H,
            V.coefficient H h * ehmVaalerWeightedPhaseRow h J m d) =
      ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
        ∑ h ∈ V.frequencies H,
          (ehmDyadicNearKernelWeight X m d : ℂ) *
            (V.coefficient H h * ehmVaalerWeightedPhaseRow h J m d) := by
        simp_rw [Finset.mul_sum]
    _ =
      ∑ m ∈ Finset.Icc mLo mHi, ∑ h ∈ V.frequencies H,
        ∑ d ∈ Finset.Icc (X + 1) D,
          (ehmDyadicNearKernelWeight X m d : ℂ) *
            (V.coefficient H h * ehmVaalerWeightedPhaseRow h J m d) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.sum_comm]
    _ = ∑ h ∈ V.frequencies H, ∑ m ∈ Finset.Icc mLo mHi,
        ∑ d ∈ Finset.Icc (X + 1) D,
          (ehmDyadicNearKernelWeight X m d : ℂ) *
            (V.coefficient H h * ehmVaalerWeightedPhaseRow h J m d) := by
        rw [Finset.sum_comm]
    _ = ∑ h ∈ V.frequencies H,
        V.coefficient H h *
          ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
            (ehmDyadicNearKernelWeight X m d : ℂ) *
              ehmVaalerWeightedPhaseRow h J m d := by
        apply Finset.sum_congr rfl
        intro h _
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro d _
        ring

/-- The complete approximant is now a single finite sum of explicit
reciprocal additive characters, one row per Vaaler frequency. -/
theorem ehmDyadicVaalerKernelNormalApprox_eq_frequencySum
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) :
    ehmDyadicVaalerKernelNormalApprox V H X D J U =
      ∑ h ∈ V.frequencies H,
        V.coefficient H h *
          ehmDyadicVaalerKernelNormalPhaseForm h X D J U := by
  rw [ehmDyadicVaalerKernelNormalApprox,
    ehmDyadicVaalerMainApprox_eq_frequencySum,
    ehmDyadicVaalerNearTypeIApprox,
    ehmDyadicVaalerNearApproxMRange_eq_frequencySum,
    ehmDyadicVaalerNearTypeIIApprox,
    ehmDyadicVaalerNearApproxMRange_eq_frequencySum]
  unfold ehmDyadicVaalerKernelNormalPhaseForm
  simp_rw [mul_add, Finset.sum_add_distrib]

/-! ## Exact zero/nonzero mode split -/

/-- The zero-frequency contribution, including the possibility that a
generic package does not list frequency zero. -/
noncomputable def ehmDyadicVaalerKernelNormalZeroMode
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) : ℂ :=
  if (0 : ℤ) ∈ V.frequencies H then
    V.coefficient H 0 *
      ehmDyadicVaalerKernelNormalPhaseForm 0 X D J U
  else 0

/-- All explicitly oscillatory Vaaler modes. -/
noncomputable def ehmDyadicVaalerKernelNormalNonzeroModes
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies H).erase 0,
    V.coefficient H h *
      ehmDyadicVaalerKernelNormalPhaseForm h X D J U

/-- Exact split of the full approximant into its nonoscillatory row and
the remaining nonzero additive characters. -/
theorem ehmDyadicVaalerKernelNormalApprox_eq_zero_add_nonzero
    (V : VaalerSawtoothPackage) (H X D J U : ℕ) :
    ehmDyadicVaalerKernelNormalApprox V H X D J U =
      ehmDyadicVaalerKernelNormalZeroMode V H X D J U +
        ehmDyadicVaalerKernelNormalNonzeroModes V H X D J U := by
  classical
  rw [ehmDyadicVaalerKernelNormalApprox_eq_frequencySum]
  unfold ehmDyadicVaalerKernelNormalZeroMode
    ehmDyadicVaalerKernelNormalNonzeroModes
  by_cases hzero : (0 : ℤ) ∈ V.frequencies H
  · simp only [hzero, if_true]
    rw [add_comm]
    exact (Finset.sum_erase_add _ _ hzero).symm
  · simp only [hzero, if_false, zero_add]
    rw [Finset.erase_eq_self.mpr hzero]

/-- The precise extra property needed to remove the zero mode.  It is not
part of `VaalerSawtoothPackage`, whose interface intentionally permits a
generic finite Fourier decomposition. -/
def VaalerSawtoothHasZeroCoefficient
    (V : VaalerSawtoothPackage) : Prop :=
  ∀ H, V.coefficient H 0 = 0

theorem ehmDyadicVaalerKernelNormalZeroMode_eq_zero
    (V : VaalerSawtoothPackage) (hV : VaalerSawtoothHasZeroCoefficient V)
    (H X D J U : ℕ) :
    ehmDyadicVaalerKernelNormalZeroMode V H X D J U = 0 := by
  unfold ehmDyadicVaalerKernelNormalZeroMode
  split_ifs
  · rw [hV H, zero_mul]
  · rfl

/-- For a zero-mean Vaaler polynomial, the approximant consists exactly of
the nonzero reciprocal additive characters. -/
theorem ehmDyadicVaalerKernelNormalApprox_eq_nonzeroModes
    (V : VaalerSawtoothPackage) (hV : VaalerSawtoothHasZeroCoefficient V)
    (H X D J U : ℕ) :
    ehmDyadicVaalerKernelNormalApprox V H X D J U =
      ehmDyadicVaalerKernelNormalNonzeroModes V H X D J U := by
  rw [ehmDyadicVaalerKernelNormalApprox_eq_zero_add_nonzero,
    ehmDyadicVaalerKernelNormalZeroMode_eq_zero V hV, zero_add]

/-! ## Endpoint-resonance lift -/

/-- Closed divisibility form of one integer-endpoint reciprocal row. -/
noncomputable def ehmDyadicEndpointQKernelClosed
    (J m d : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (J / d),
    if m ∣ d * q then
      (m : ℝ) / (2 * ((d * q : ℕ) : ℝ))
    else 0

theorem ehmDyadicReciprocalQKernel_endpoint_eq_closed
    (J m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    ehmDyadicReciprocalQKernel ehmR1IntegerEndpointPart J m d =
      ehmDyadicEndpointQKernelClosed J m d := by
  classical
  unfold ehmDyadicReciprocalQKernel ehmR1PartialSeries
    ehmDyadicEndpointQKernelClosed
  apply Finset.sum_congr rfl
  intro q hq
  have hqpos : 0 < q := by
    exact (Finset.mem_Icc.mp hq).1
  have harg :
      (q : ℝ) * ((d : ℝ) / (m : ℝ)) =
        ((d * q : ℕ) : ℝ) / (m : ℝ) := by
    push_cast
    ring
  rw [harg, ehmR1IntegerEndpointPart_dq_div_m d q m hd hqpos hm]

/-- Closed endpoint contribution of the completed von-Mangoldt main form. -/
noncomputable def ehmDyadicEndpointMainClosed (X J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (2 * X), ∑ j ∈ Finset.Icc 2 J,
    ArithmeticFunction.vonMangoldt j *
      ehmDyadicMobiusCutoffCoeff X m *
        (if m ∣ j then (m : ℝ) / (2 * (j : ℝ)) else 0)

theorem ehmDyadicFullMainEndpoint_eq_closed (X J : ℕ) :
    ehmDyadicFullMainJointSum ehmR1IntegerEndpointPart X J =
      ehmDyadicEndpointMainClosed X J := by
  classical
  unfold ehmDyadicFullMainJointSum ehmDyadicEndpointMainClosed
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  apply Finset.sum_congr rfl
  intro j hj
  have hjpos : 0 < j := by
    have : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    omega
  rw [ehmR1IntegerEndpointPart_natRatio j m hjpos hmpos]

/-- Closed endpoint contribution of a weighted near `(m,d)` interval. -/
noncomputable def ehmDyadicEndpointNearClosedMRange
    (X D J mLo mHi : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc mLo mHi, ∑ d ∈ Finset.Icc (X + 1) D,
    ehmDyadicNearKernelWeight X m d *
      ehmDyadicEndpointQKernelClosed J m d

theorem ehmDyadicNearEndpointMRange_eq_closed
    (X D J mLo mHi : ℕ) (hmLo : 0 < mLo) :
    ehmDyadicNearMobiusKernelMRange ehmR1IntegerEndpointPart
      X D J mLo mHi =
        ehmDyadicEndpointNearClosedMRange X D J mLo mHi := by
  classical
  rw [ehmDyadicNearMobiusKernelMRange_eq_weighted]
  unfold ehmDyadicEndpointNearClosedMRange
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := lt_of_lt_of_le hmLo (Finset.mem_Icc.mp hm).1
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := by
    have : X + 1 ≤ d := (Finset.mem_Icc.mp hd).1
    omega
  rw [ehmDyadicReciprocalQKernel_endpoint_eq_closed J m d hmpos hdpos]

/-- The full endpoint normal form is an exact sum over the resonances
`m ∣ j` and `m ∣ d*q`; no smallness or cancellation is hidden here. -/
noncomputable def ehmDyadicEndpointKernelNormalClosed
    (X D J U : ℕ) : ℝ :=
  ehmDyadicEndpointMainClosed X J +
    ehmDyadicEndpointNearClosedMRange X D J 1 U +
    ehmDyadicEndpointNearClosedMRange X D J (U + 1) (2 * X)

theorem ehmDyadicKernelNormalEndpoint_eq_closed
    (X D J U : ℕ) :
    ehmDyadicKernelNormalCoupledPart ehmR1IntegerEndpointPart
      X D J U = ehmDyadicEndpointKernelNormalClosed X D J U := by
  unfold ehmDyadicKernelNormalCoupledPart
    ehmDyadicNearKernelTypeI ehmDyadicNearKernelTypeII
    ehmDyadicEndpointKernelNormalClosed
  rw [ehmDyadicFullMainEndpoint_eq_closed,
    ehmDyadicNearEndpointMRange_eq_closed X D J 1 U (by omega),
    ehmDyadicNearEndpointMRange_eq_closed X D J (U + 1) (2 * X) (by omega)]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
