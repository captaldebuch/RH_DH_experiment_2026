import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMomentRemainderStopTest

/-!
# MacLeod endpoint compensation in the retained Ehm boundary

Ehm's Proposition 8.2 does not estimate the finite von Mangoldt transform.
It identifies one exact endpoint transform inside the moment remainder.  This
module substitutes that identity into the retained boundary without taking
absolute values of either piece.

The resulting normal form is

`(finite main - Phi1(N) / N) + MacLeod core`.

It is an exact finite identity.  Decay of the displayed signed sum remains
the analytic research problem.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMacLeodCompensation

open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMacLeod
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMomentRemainderStopTest
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRetainedCorrectionAudit

/-- The part of the raw-moment remainder left after Ehm--MacLeod extracts
the normalized endpoint transform `Phi1(N) / N`. -/
noncomputable def ehmMacLeodMomentCore (N : ℕ) : ℝ :=
  rawMobiusHarmonicMoment 0 N * Real.log N +
      rawMobiusMoment 0 N / (2 * (N : ℝ)) + 1 / (N : ℝ) -
    (rawMobiusHarmonicMoment 2 N +
        (1 - Real.eulerMascheroniConstant) *
          rawMobiusHarmonicMoment 1 N) / Real.log N +
    ehmRawTaperedM0 N *
      (ehmK * ehmRawTaperedL0 N + (ehmRawTaperedL1 N + 1) / 2) -
    (ehmRawTaperedM1 N * ehmRawTaperedL0 N) / 2

/-- Proposition 8.2 extracts the normalized MacLeod transform from the
linear part of the tapered correction. -/
theorem ehmTaperedLinearCorrection_eq_macleod
    (N : ℕ) (hN : 2 ≤ N) :
    ehmRawTaperedL1 N +
        (1 - Real.eulerMascheroniConstant) * ehmRawTaperedL0 N + 1 =
      rawMobiusHarmonicMoment 0 N * Real.log N +
        rawMobiusMoment 0 N / (2 * (N : ℝ)) + 1 / (N : ℝ) -
        (rawMobiusHarmonicMoment 2 N +
            (1 - Real.eulerMascheroniConstant) *
              rawMobiusHarmonicMoment 1 N) / Real.log N -
        ehmMacLeodPhi1 N / (N : ℝ) := by
  have hNR : (N : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have hlog : Real.log (N : ℝ) ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one (by positivity)
      (by exact_mod_cast (by omega : N ≠ 1))
  have hMac := ehm_macleod_proposition_8_2 N hN
  unfold ehmDeltaCenteredRawL0 ehmCenteredRawL1 at hMac
  have hbase :
      rawMobiusHarmonicMoment 1 N +
          (1 - Real.eulerMascheroniConstant) *
            rawMobiusHarmonicMoment 0 N + 1 =
        rawMobiusHarmonicMoment 0 N * Real.log N +
          rawMobiusMoment 0 N / (2 * (N : ℝ)) -
          ehmMacLeodPhi1 N / (N : ℝ) + 1 / (N : ℝ) := by
    field_simp [hlog] at hMac
    field_simp [hNR]
    nlinarith [hMac]
  unfold ehmRawTaperedL0 ehmRawTaperedL1
  rw [show
      rawMobiusHarmonicMoment 1 N -
            rawMobiusHarmonicMoment 2 N / Real.log N +
          (1 - Real.eulerMascheroniConstant) *
            (rawMobiusHarmonicMoment 0 N -
              rawMobiusHarmonicMoment 1 N / Real.log N) + 1 =
        (rawMobiusHarmonicMoment 1 N +
            (1 - Real.eulerMascheroniConstant) *
              rawMobiusHarmonicMoment 0 N + 1) -
          (rawMobiusHarmonicMoment 2 N +
            (1 - Real.eulerMascheroniConstant) *
              rawMobiusHarmonicMoment 1 N) / Real.log N by ring,
    hbase]
  ring

/-- Exact substitution of Ehm (2024), Proposition 8.2, into the six-moment
normal form.  In particular, this theorem makes no size assertion about
either the MacLeod core or `Phi1`. -/
theorem ehmMomentRemainderRawNormalForm_eq_macleodCore_sub_phi
    (N : ℕ) (hN : 2 ≤ N) :
    ehmMomentRemainderRawNormalForm N =
      ehmMacLeodMomentCore N - ehmMacLeodPhi1 N / (N : ℝ) := by
  unfold ehmMomentRemainderRawNormalForm ehmMacLeodMomentCore
  rw [ehmTaperedLinearCorrection_eq_macleod N hN]
  ring

/-! ## MacLeod rows inside the finite von Mangoldt main -/

/-- The logarithmically differentiated MacLeod row. -/
noncomputable def ehmMacLeodLogPhi1 (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 j,
    ((ArithmeticFunction.moebius m : ℤ) : ℝ) * Real.log (m : ℝ) *
      (((j : ℝ) / (m : ℝ)) * ehmR1 ((j : ℝ) / (m : ℝ)))

/-- The MacLeod row with the BCF logarithmic taper at outer cutoff `N`. -/
noncomputable def ehmMacLeodTaperedPhi1 (N j : ℕ) : ℝ :=
  ehmMacLeodPhi1 j - ehmMacLeodLogPhi1 j / Real.log N

/-- The lower-triangular `m ≤ j` row of the full finite main. -/
noncomputable def ehmFiniteMacLeodLowerRow (N j : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 j, dirichletCoeff N m / (m : ℝ) *
    ehmR1 ((j : ℝ) / (m : ℝ))

/-- Exact row identity: below the diagonal, the BCF taper converts the
MacLeod transform into `Phi1 - LogPhi1 / log N`. -/
theorem ehmFiniteMacLeodLowerRow_eq_taperedPhi
    (N j : ℕ) (hN : 2 ≤ N) (hj : 1 ≤ j) :
    ehmFiniteMacLeodLowerRow N j =
      ehmMacLeodTaperedPhi1 N j / (j : ℝ) := by
  classical
  have hjR : (j : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : j ≠ 0)
  have hlog : Real.log (N : ℝ) ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one (by positivity)
      (by exact_mod_cast (by omega : N ≠ 1))
  unfold ehmFiniteMacLeodLowerRow ehmMacLeodTaperedPhi1
    ehmMacLeodPhi1 ehmMacLeodLogPhi1
  calc
    (∑ m ∈ Finset.Icc 1 j,
        dirichletCoeff N m / (m : ℝ) * ehmR1 ((j : ℝ) / (m : ℝ))) =
        ∑ m ∈ Finset.Icc 1 j,
          ((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
                (((j : ℝ) / (m : ℝ)) * ehmR1 ((j : ℝ) / (m : ℝ))) -
              ((ArithmeticFunction.moebius m : ℤ) : ℝ) * Real.log (m : ℝ) *
                (((j : ℝ) / (m : ℝ)) * ehmR1 ((j : ℝ) / (m : ℝ))) /
                  Real.log N) / (j : ℝ)) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmpos : 0 < m :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
      unfold dirichletCoeff
      rw [weight_of_two_le hN]
      field_simp [hjR, hmR, hlog]
    _ = (∑ m ∈ Finset.Icc 1 j,
          (((ArithmeticFunction.moebius m : ℤ) : ℝ) *
                (((j : ℝ) / (m : ℝ)) * ehmR1 ((j : ℝ) / (m : ℝ))) -
              ((ArithmeticFunction.moebius m : ℤ) : ℝ) * Real.log (m : ℝ) *
                (((j : ℝ) / (m : ℝ)) * ehmR1 ((j : ℝ) / (m : ℝ))) /
                  Real.log N)) / (j : ℝ) := by
      rw [Finset.sum_div]
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_div]

/-- The complete lower-triangular contribution `2 ≤ j ≤ N` of the finite
von Mangoldt transform. -/
noncomputable def ehmFiniteVonMangoldtMacLeodLowerTriangle (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 N,
    ArithmeticFunction.vonMangoldt j / Real.log N *
      ehmFiniteMacLeodLowerRow N j

/-- The same lower triangle after exact MacLeod row recovery. -/
noncomputable def ehmFiniteVonMangoldtTaperedPhiAggregate (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 N,
    ArithmeticFunction.vonMangoldt j / Real.log N *
      (ehmMacLeodTaperedPhi1 N j / (j : ℝ))

/-- The lower main is not a single endpoint `Phi1(N)`: it is exactly the
von-Mangoldt average of all tapered MacLeod rows up to `N`. -/
theorem ehmFiniteVonMangoldtMacLeodLowerTriangle_eq_taperedPhiAggregate
    (N : ℕ) (hN : 2 ≤ N) :
    ehmFiniteVonMangoldtMacLeodLowerTriangle N =
      ehmFiniteVonMangoldtTaperedPhiAggregate N := by
  unfold ehmFiniteVonMangoldtMacLeodLowerTriangle
    ehmFiniteVonMangoldtTaperedPhiAggregate
  apply Finset.sum_congr rfl
  intro j hj
  rw [ehmFiniteMacLeodLowerRow_eq_taperedPhi N j hN
    ((by norm_num : 1 ≤ 2).trans (Finset.mem_Icc.mp hj).1)]

/-! ## Exact three-sector decomposition of the complete finite main -/

/-- Joint `(j,m)` form of the full finite von Mangoldt main. -/
noncomputable def ehmFiniteVonMangoldtJointMain (N J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 J, ∑ m ∈ Finset.Icc 1 N,
    ArithmeticFunction.vonMangoldt j / Real.log N *
      (dirichletCoeff N m / (m : ℝ) * ehmR1 ((j : ℝ) / (m : ℝ)))

/-- The sector below the diagonal and below the outer cutoff: `m ≤ j ≤ N`. -/
noncomputable def ehmFiniteVonMangoldtMacLeodSector (N J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 J, ∑ m ∈ Finset.Icc 1 N,
    if j ≤ N ∧ m ≤ j then
      ArithmeticFunction.vonMangoldt j / Real.log N *
        (dirichletCoeff N m / (m : ℝ) * ehmR1 ((j : ℝ) / (m : ℝ)))
    else 0

/-- The strict upper triangle `j < m ≤ N`. -/
noncomputable def ehmFiniteVonMangoldtUpperSector (N J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 J, ∑ m ∈ Finset.Icc 1 N,
    if j < m then
      ArithmeticFunction.vonMangoldt j / Real.log N *
        (dirichletCoeff N m / (m : ℝ) * ehmR1 ((j : ℝ) / (m : ℝ)))
    else 0

/-- The high von Mangoldt sector `N < j ≤ J`. -/
noncomputable def ehmFiniteVonMangoldtHighSector (N J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 J, ∑ m ∈ Finset.Icc 1 N,
    if N < j then
      ArithmeticFunction.vonMangoldt j / Real.log N *
        (dirichletCoeff N m / (m : ℝ) * ehmR1 ((j : ℝ) / (m : ℝ)))
    else 0

/-- The original outer transform is exactly its joint `(j,m)` reindexing. -/
theorem ehmFiniteFullVonMangoldtTransformOuter_eq_joint
    (N J : ℕ) :
    ehmFiniteFullVonMangoldtTransformOuter ehmR1 N J =
      ehmFiniteVonMangoldtJointMain N J := by
  classical
  unfold ehmFiniteFullVonMangoldtTransformOuter
    ehmFiniteFullVonMangoldtTransform ehmFiniteVonMangoldtJointMain
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro m _
  ring_nf

/-- Every pair in the finite main lies in exactly one of the MacLeod,
strict-upper, or high sectors.  No absolute value is introduced. -/
theorem ehmFiniteVonMangoldtJointMain_eq_threeSectors
    (N J : ℕ) :
    ehmFiniteVonMangoldtJointMain N J =
      ehmFiniteVonMangoldtMacLeodSector N J +
        ehmFiniteVonMangoldtUpperSector N J +
          ehmFiniteVonMangoldtHighSector N J := by
  classical
  unfold ehmFiniteVonMangoldtJointMain
    ehmFiniteVonMangoldtMacLeodSector
    ehmFiniteVonMangoldtUpperSector
    ehmFiniteVonMangoldtHighSector
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hjN : j ≤ N
  · by_cases hmj : m ≤ j
    · have hnot : ¬j < m := by omega
      simp [hjN, hmj, hnot]
    · have hjm : j < m := by omega
      simp [hjN, hmj, hjm]
  · have hNj : N < j := by omega
    have hnotjm : ¬j < m := by
      intro hjm
      have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
      omega
    simp [hjN, hNj, hnotjm]

/-- The complete main therefore has an exact three-sector decomposition. -/
theorem ehmFiniteFullVonMangoldtTransformOuter_eq_threeSectors
    (N J : ℕ) :
    ehmFiniteFullVonMangoldtTransformOuter ehmR1 N J =
      ehmFiniteVonMangoldtMacLeodSector N J +
        ehmFiniteVonMangoldtUpperSector N J +
          ehmFiniteVonMangoldtHighSector N J := by
  rw [ehmFiniteFullVonMangoldtTransformOuter_eq_joint,
    ehmFiniteVonMangoldtJointMain_eq_threeSectors]

/-- The lower sector after replacing each row by its exact tapered MacLeod
transform. -/
noncomputable def ehmFiniteVonMangoldtTaperedPhiSector (N J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 J,
    if j ≤ N then
      ArithmeticFunction.vonMangoldt j / Real.log N *
        (ehmMacLeodTaperedPhi1 N j / (j : ℝ))
    else 0

/-- Exact recovery of the whole lower sector as a von-Mangoldt average of
tapered MacLeod rows. -/
theorem ehmFiniteVonMangoldtMacLeodSector_eq_taperedPhiSector
    (N J : ℕ) (hN : 2 ≤ N) :
    ehmFiniteVonMangoldtMacLeodSector N J =
      ehmFiniteVonMangoldtTaperedPhiSector N J := by
  classical
  unfold ehmFiniteVonMangoldtMacLeodSector
    ehmFiniteVonMangoldtTaperedPhiSector
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjN : j ≤ N
  · rw [show
        (∑ m ∈ Finset.Icc 1 N,
          if j ≤ N ∧ m ≤ j then
            ArithmeticFunction.vonMangoldt j / Real.log N *
              (dirichletCoeff N m / (m : ℝ) *
                ehmR1 ((j : ℝ) / (m : ℝ)))
          else 0) =
        ArithmeticFunction.vonMangoldt j / Real.log N *
          ehmFiniteMacLeodLowerRow N j by
        unfold ehmFiniteMacLeodLowerRow
        rw [Finset.mul_sum]
        simp only [hjN, true_and]
        rw [← Finset.sum_filter]
        have hfilter :
            (Finset.Icc 1 N).filter (fun m ↦ m ≤ j) = Finset.Icc 1 j := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_Icc]
          omega
        rw [hfilter],
      ehmFiniteMacLeodLowerRow_eq_taperedPhi N j hN
        ((by norm_num : 1 ≤ 2).trans (Finset.mem_Icc.mp hj).1),
      if_pos hjN]
  · simp [hjN]

/-- The full finite main with the normalized MacLeod endpoint removed.
The subtraction is kept signed. -/
noncomputable def ehmFiniteMainMinusMacLeodEndpoint
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ehmFiniteFullVonMangoldtTransformOuter R1 N J -
    ehmMacLeodPhi1 N / (N : ℝ)

/-- The corrected retained summand in its exact MacLeod compensation form. -/
noncomputable def ehmFiniteMacLeodCompensationDefect
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ehmFiniteMainMinusMacLeodEndpoint R1 N J + ehmMacLeodMomentCore N

/-- The MacLeod compensation form is exactly the previously validated
main--moment defect. -/
theorem ehmFiniteMacLeodCompensationDefect_eq_mainMoment
    (R1 : ℝ → ℝ) (N J : ℕ) (hN : 2 ≤ N) :
    ehmFiniteMacLeodCompensationDefect R1 N J =
      ehmFiniteMainMomentCompensationDefect R1 N J := by
  unfold ehmFiniteMacLeodCompensationDefect
    ehmFiniteMainMinusMacLeodEndpoint
    ehmFiniteMainMomentCompensationDefect
  rw [ehmMomentRemainderRawNormalForm_eq_macleodCore_sub_phi N hN]
  ring

/-- Hence the MacLeod normal form is also exactly the indivisible retained
outer-cutoff summand. -/
theorem ehmFiniteMacLeodCompensationDefect_eq_retainedSummand
    (R1 : ℝ → ℝ) (N J : ℕ) (hN : 2 ≤ N) :
    ehmFiniteMacLeodCompensationDefect R1 N J =
      ehmFiniteRetainedCorrectionSummand R1 N J := by
  rw [ehmFiniteMacLeodCompensationDefect_eq_mainMoment R1 N J hN,
    ehmFiniteMainMomentCompensationDefect_eq_retainedSummand R1 N J hN]

/-- Final exact compensation anatomy: the retained summand consists of the
tapered MacLeod-row average, the strict upper triangle, the high sector, and
the MacLeod moment core minus its single endpoint. -/
theorem ehmFiniteMacLeodCompensationDefect_eq_fourSectors
    (N J : ℕ) (hN : 2 ≤ N) :
    ehmFiniteMacLeodCompensationDefect ehmR1 N J =
      ehmFiniteVonMangoldtTaperedPhiSector N J +
        ehmFiniteVonMangoldtUpperSector N J +
          ehmFiniteVonMangoldtHighSector N J -
            ehmMacLeodPhi1 N / (N : ℝ) + ehmMacLeodMomentCore N := by
  unfold ehmFiniteMacLeodCompensationDefect
    ehmFiniteMainMinusMacLeodEndpoint
  rw [ehmFiniteFullVonMangoldtTransformOuter_eq_threeSectors,
    ehmFiniteVonMangoldtMacLeodSector_eq_taperedPhiSector N J hN]

/-- Research interface after the exact MacLeod substitution.  The endpoint
and core remain in one absolute value; no false separate decay premise is
introduced. -/
structure EhmRetainedCorrectionMacLeodInverseCutoffBound where
  C : ℝ
  C_nonneg : 0 ≤ C
  coupled_bound : ∀ X N J : ℕ, 2 ≤ X →
    N ∈ ehmDyadicNBlock X → ehmExplicitFarCutoff X ≤ J →
    |ehmFiniteMainMinusMacLeodEndpoint ehmR1 N J +
        ehmMacLeodMomentCore N| ≤ C / (N : ℝ)

/-- The exact MacLeod target instantiates the main--moment stop-test
interface and therefore all existing retained-correction consequences. -/
noncomputable def EhmRetainedCorrectionMacLeodInverseCutoffBound.toMainMoment
    (H : EhmRetainedCorrectionMacLeodInverseCutoffBound) :
    EhmRetainedCorrectionMainMomentInverseCutoffBound where
  C := H.C
  C_nonneg := H.C_nonneg
  coupled_bound X N J hX hN hJ := by
    rw [← ehmFiniteMacLeodCompensationDefect_eq_mainMoment
      ehmR1 N J (hX.trans (Finset.mem_Icc.mp hN).1)]
    exact H.coupled_bound X N J hX hN hJ

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMacLeodCompensation
