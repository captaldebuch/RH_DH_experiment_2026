import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMacLeodCompensation

/-!
# High-sector compensation after the MacLeod stop test

The natural cutoff `J = N` contains the tapered MacLeod rows and the strict
upper triangle, but no high von Mangoldt sector.  This module proves that the
complete retained defect at any `J ≥ N` is exactly its natural-cutoff value
plus the signed high tail `N < j ≤ J`.

This isolates the next analytic target without estimating either summand
separately.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmHighSectorCompensation

open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMacLeodCompensation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMomentRemainderStopTest

/-- The high part of the joint von Mangoldt main, written on its natural
interval rather than through an indicator. -/
noncomputable def ehmFiniteVonMangoldtHighTail (N J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc (N + 1) J, ∑ m ∈ Finset.Icc 1 N,
    ArithmeticFunction.vonMangoldt j / Real.log N *
      (dirichletCoeff N m / (m : ℝ) * ehmR1 ((j : ℝ) / (m : ℝ)))

/-- The indicator-form high sector agrees exactly with the interval tail. -/
theorem ehmFiniteVonMangoldtHighSector_eq_highTail
    (N J : ℕ) (hN : 2 ≤ N) :
    ehmFiniteVonMangoldtHighSector N J =
      ehmFiniteVonMangoldtHighTail N J := by
  classical
  unfold ehmFiniteVonMangoldtHighSector ehmFiniteVonMangoldtHighTail
  calc
    (∑ j ∈ Finset.Icc 2 J, ∑ m ∈ Finset.Icc 1 N,
        if N < j then
          ArithmeticFunction.vonMangoldt j / Real.log N *
            (dirichletCoeff N m / (m : ℝ) * ehmR1 ((j : ℝ) / (m : ℝ)))
        else 0) =
      ∑ j ∈ Finset.Icc 2 J,
        if N < j then
          ∑ m ∈ Finset.Icc 1 N,
            ArithmeticFunction.vonMangoldt j / Real.log N *
              (dirichletCoeff N m / (m : ℝ) *
                ehmR1 ((j : ℝ) / (m : ℝ)))
        else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hNj : N < j <;> simp [hNj]
    _ = ∑ j ∈ (Finset.Icc 2 J).filter (fun j ↦ N < j),
        ∑ m ∈ Finset.Icc 1 N,
          ArithmeticFunction.vonMangoldt j / Real.log N *
            (dirichletCoeff N m / (m : ℝ) *
              ehmR1 ((j : ℝ) / (m : ℝ))) := by
          rw [Finset.sum_filter]
    _ = _ := by
      have hfilter :
          (Finset.Icc 2 J).filter (fun j ↦ N < j) =
            Finset.Icc (N + 1) J := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [hfilter]

/-- Exact partition of the joint main at `j = N`. -/
theorem ehmFiniteVonMangoldtJointMain_eq_atCutoff_add_highTail
    (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteVonMangoldtJointMain N J =
      ehmFiniteVonMangoldtJointMain N N +
        ehmFiniteVonMangoldtHighTail N J := by
  classical
  have hwhole :
      Finset.Icc 2 J =
        Finset.Icc 2 N ∪ Finset.Icc (N + 1) J := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdis :
      Disjoint (Finset.Icc 2 N) (Finset.Icc (N + 1) J) := by
    apply Finset.disjoint_left.mpr
    intro j hjN hjTail
    have hjN' := (Finset.mem_Icc.mp hjN).2
    have hjTail' := (Finset.mem_Icc.mp hjTail).1
    omega
  unfold ehmFiniteVonMangoldtJointMain ehmFiniteVonMangoldtHighTail
  rw [hwhole, Finset.sum_union hdis]

/-- The original full main at `J ≥ N` equals its natural-cutoff value plus
the signed high tail. -/
theorem ehmFiniteFullVonMangoldtTransformOuter_eq_atCutoff_add_highTail
    (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteFullVonMangoldtTransformOuter ehmR1 N J =
      ehmFiniteFullVonMangoldtTransformOuter ehmR1 N N +
        ehmFiniteVonMangoldtHighTail N J := by
  rw [ehmFiniteFullVonMangoldtTransformOuter_eq_joint,
    ehmFiniteFullVonMangoldtTransformOuter_eq_joint,
    ehmFiniteVonMangoldtJointMain_eq_atCutoff_add_highTail N J hN hNJ]

/-- The complete retained defect at the natural hyperbolic cutoff `J=N`. -/
noncomputable def ehmFiniteNaturalCutoffDefect (N : ℕ) : ℝ :=
  ehmFiniteMacLeodCompensationDefect ehmR1 N N

/-- Exact high-sector compensation identity.  The high tail is not a
remainder to be bounded absolutely: it must stay coupled to the natural
cutoff defect. -/
theorem ehmFiniteMacLeodCompensationDefect_eq_natural_add_highTail
    (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteMacLeodCompensationDefect ehmR1 N J =
      ehmFiniteNaturalCutoffDefect N +
        ehmFiniteVonMangoldtHighTail N J := by
  unfold ehmFiniteNaturalCutoffDefect
    ehmFiniteMacLeodCompensationDefect
    ehmFiniteMainMinusMacLeodEndpoint
  rw [ehmFiniteFullVonMangoldtTransformOuter_eq_atCutoff_add_highTail
    N J hN hNJ]
  ring

/-! ## Mean-prime centering of the high tail -/

/-- The deterministic high tail obtained by replacing `Λ(j)` by its mean
value `1`. -/
noncomputable def ehmFiniteVonMangoldtHighUnitTail (N J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc (N + 1) J, ∑ m ∈ Finset.Icc 1 N,
    1 / Real.log N *
      (dirichletCoeff N m / (m : ℝ) * ehmR1 ((j : ℝ) / (m : ℝ)))

/-- The centered prime-discrepancy part of the high tail. -/
noncomputable def ehmFiniteVonMangoldtHighCenteredTail (N J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc (N + 1) J, ∑ m ∈ Finset.Icc 1 N,
    (ArithmeticFunction.vonMangoldt j - 1) / Real.log N *
      (dirichletCoeff N m / (m : ℝ) * ehmR1 ((j : ℝ) / (m : ℝ)))

/-- Exact centering `Λ = 1 + (Λ - 1)` inside the high sector. -/
theorem ehmFiniteVonMangoldtHighTail_eq_unit_add_centered
    (N J : ℕ) :
    ehmFiniteVonMangoldtHighTail N J =
      ehmFiniteVonMangoldtHighUnitTail N J +
        ehmFiniteVonMangoldtHighCenteredTail N J := by
  classical
  unfold ehmFiniteVonMangoldtHighTail
    ehmFiniteVonMangoldtHighUnitTail
    ehmFiniteVonMangoldtHighCenteredTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- The natural-cutoff defect completed by the deterministic mean-prime
tail. -/
noncomputable def ehmFiniteMeanPrimeCompletedDefect (N J : ℕ) : ℝ :=
  ehmFiniteNaturalCutoffDefect N +
    ehmFiniteVonMangoldtHighUnitTail N J

/-- Exact centered-prime form of the retained defect.  The deterministic
completion and the `Λ-1` fluctuation remain in one signed expression. -/
theorem ehmFiniteMacLeodCompensationDefect_eq_meanPrime_add_centered
    (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteMacLeodCompensationDefect ehmR1 N J =
      ehmFiniteMeanPrimeCompletedDefect N J +
        ehmFiniteVonMangoldtHighCenteredTail N J := by
  rw [ehmFiniteMacLeodCompensationDefect_eq_natural_add_highTail
    N J hN hNJ,
    ehmFiniteVonMangoldtHighTail_eq_unit_add_centered]
  unfold ehmFiniteMeanPrimeCompletedDefect
  ring

/-- The analytically honest inverse-cutoff target after the natural-cutoff
stop test.  It retains cancellation between the natural defect and high
tail inside one absolute value. -/
structure EhmRetainedCorrectionHighSectorCompensationBound where
  C : ℝ
  C_nonneg : 0 ≤ C
  coupled_bound : ∀ X N J : ℕ, 2 ≤ X →
    N ∈ ehmDyadicNBlock X → ehmExplicitFarCutoff X ≤ J →
    |ehmFiniteNaturalCutoffDefect N +
        ehmFiniteVonMangoldtHighTail N J| ≤ C / (N : ℝ)

/-- Equivalent research interface after centering the von Mangoldt weight.
It deliberately does not bound the unit and centered tails separately. -/
structure EhmRetainedCorrectionCenteredPrimeCompensationBound where
  C : ℝ
  C_nonneg : 0 ≤ C
  coupled_bound : ∀ X N J : ℕ, 2 ≤ X →
    N ∈ ehmDyadicNBlock X → ehmExplicitFarCutoff X ≤ J →
    |ehmFiniteMeanPrimeCompletedDefect N J +
        ehmFiniteVonMangoldtHighCenteredTail N J| ≤ C / (N : ℝ)

/-- Centered-prime compensation is exactly the high-sector target. -/
noncomputable def
    EhmRetainedCorrectionCenteredPrimeCompensationBound.toHighSector
    (H : EhmRetainedCorrectionCenteredPrimeCompensationBound) :
    EhmRetainedCorrectionHighSectorCompensationBound where
  C := H.C
  C_nonneg := H.C_nonneg
  coupled_bound X N J hX hN hJ := by
    rw [ehmFiniteVonMangoldtHighTail_eq_unit_add_centered]
    rw [show
      ehmFiniteNaturalCutoffDefect N +
          (ehmFiniteVonMangoldtHighUnitTail N J +
            ehmFiniteVonMangoldtHighCenteredTail N J) =
        ehmFiniteMeanPrimeCompletedDefect N J +
          ehmFiniteVonMangoldtHighCenteredTail N J by
        unfold ehmFiniteMeanPrimeCompletedDefect
        ring]
    exact H.coupled_bound X N J hX hN hJ

/-- The high-sector compensation target instantiates the exact MacLeod
research interface. -/
noncomputable def
    EhmRetainedCorrectionHighSectorCompensationBound.toMacLeod
    (H : EhmRetainedCorrectionHighSectorCompensationBound) :
    EhmRetainedCorrectionMacLeodInverseCutoffBound where
  C := H.C
  C_nonneg := H.C_nonneg
  coupled_bound X N J hX hN hJ := by
    have hNtwo : 2 ≤ N := hX.trans (Finset.mem_Icc.mp hN).1
    have hNJ : N ≤ J :=
      (Finset.mem_Icc.mp hN).2.trans
        ((two_mul_le_ehmExplicitFarCutoff X).trans hJ)
    change |ehmFiniteMacLeodCompensationDefect ehmR1 N J| ≤
      H.C / (N : ℝ)
    rw [ehmFiniteMacLeodCompensationDefect_eq_natural_add_highTail
      N J hNtwo hNJ]
    exact H.coupled_bound X N J hX hN hJ

end RH.Criteria.NymanBeurling.BCFLogTaperEhmHighSectorCompensation
