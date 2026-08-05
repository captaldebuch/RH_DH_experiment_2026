/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15GCDReindex
import NBMellinTools.NB15EstermannVasyuninAtZero

/-!
# Assemble the certified Gram form from active Estermann values

The preceding modules independently provide the exact gcd reindexing of the
certified Nyman--Beurling energy and the genuine rational Estermann value at
zero.  This file joins them.  The Vasyunin cotangent terms in every primitive
interior Gram row are replaced by imaginary parts of the active Hurwitz
continuation.

The endpoint sector is retained unchanged.  No asymptotic estimate, packaged
special value, or RH input occurs.
-/

open scoped BigOperators

namespace NBMellinTools.NB15

open NBMellinTools.NB8
open NBMellinTools.NB10
open NBMellinTools.NB12
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The active inverse-frequency Estermann continuation at zero, made total
at the irrelevant modulus zero. -/
noncomputable def activeInverseEstermannZero (a q : ℕ) : ℂ :=
  if hq : q = 0 then 0
  else
    @bblsEstermannHurwitzContinuation
      (@inverseResidue a q ⟨hq⟩) q ⟨hq⟩ 0

theorem activeInverseEstermannZero_eq
    (a q : ℕ) (hq : 0 < q) :
    activeInverseEstermannZero a q =
      @bblsEstermannHurwitzContinuation
        (@inverseResidue a q ⟨hq.ne'⟩) q ⟨hq.ne'⟩ 0 := by
  simp only [activeInverseEstermannZero, dif_neg hq.ne']

/-- A reduced Vasyunin cotangent row is exactly minus twice the imaginary
part of the active inverse-frequency Estermann value. -/
theorem cotangentSumVFormula_eq_neg_two_mul_estermann_im
    (a q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a q) :
    cotangentSumVFormula a q =
      -2 * (activeInverseEstermannZero a q).im := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [activeInverseEstermannZero_eq a q hq,
    bblsInverseEstermann_zero_eq_vasyunin a q hcop]
  simp

/-- The active Estermann form of one primitive Gram entry. -/
noncomputable def estermannGramFormula (a q : ℕ) : ℝ :=
  (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
      (1 / (a : ℝ) + 1 / (q : ℝ)) +
    ((q : ℝ) - (a : ℝ)) / (2 * (a : ℝ) * (q : ℝ)) *
      Real.log ((a : ℝ) / (q : ℝ)) +
    Real.pi / ((a : ℝ) * (q : ℝ)) *
      ((activeInverseEstermannZero a q).im +
        (activeInverseEstermannZero q a).im)

/-- Exact replacement of the two Vasyunin cotangent rows by genuine active
Estermann special values. -/
theorem vasyuninBEntryFormula_eq_estermannGramFormula
    (a q : ℕ) (ha : 0 < a) (hq : 0 < q)
    (hcop : Nat.Coprime a q) :
    vasyuninBEntryFormula a q = estermannGramFormula a q := by
  have hcop' : Nat.Coprime q a := hcop.symm
  unfold vasyuninBEntryFormula estermannGramFormula
  rw [cotangentSumVFormula_eq_neg_two_mul_estermann_im a q hq hcop,
    cotangentSumVFormula_eq_neg_two_mul_estermann_im q a ha hcop']
  ring

/-- The primitive interior slice expressed entirely through active
Estermann values. -/
noncomputable def oneBasedEstermannInteriorSlice (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ q ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a q ∧ 2 ≤ a ∧ 2 ≤ q then
      h15NaturalLogTaperCoeff N (g * a) *
        h15NaturalLogTaperCoeff N (g * q) *
        (g : ℝ)⁻¹ * estermannGramFormula a q
    else 0

theorem oneBasedVasyuninInteriorSlice_eq_estermann
    (N g : ℕ) :
    oneBasedVasyuninInteriorSlice N g =
      oneBasedEstermannInteriorSlice N g := by
  classical
  unfold oneBasedVasyuninInteriorSlice oneBasedEstermannInteriorSlice
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro q _
  split_ifs with h
  · rw [vasyuninBEntryFormula_eq_estermannGramFormula a q
      (by omega) (by omega) h.1]
  · rfl

noncomputable def oneBasedEstermannInterior (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N, oneBasedEstermannInteriorSlice N g

theorem oneBasedVasyuninInterior_eq_estermann (N : ℕ) :
    oneBasedVasyuninInterior N = oneBasedEstermannInterior N := by
  unfold oneBasedVasyuninInterior oneBasedEstermannInterior
  apply Finset.sum_congr rfl
  intro g _
  exact oneBasedVasyuninInteriorSlice_eq_estermann N g

/-- Exact active Estermann assembly of the certified logarithmic-taper
Nyman--Beurling energy.  Only the primitive interior is transformed; the
pre-functional-equation correction and endpoint rows remain explicit. -/
theorem logTaperL2Error_eq_gcdEstermannInterior_add_endpoint
    (n : ℕ) :
    logTaperL2Error n =
      preFECorrection n +
        oneBasedEstermannInterior (logTaperLength n) +
        oneBasedVasyuninEndpoint (logTaperLength n) := by
  rw [logTaperL2Error_eq_gcdVasyuninInterior_add_endpoint,
    oneBasedVasyuninInterior_eq_estermann]

end NBMellinTools.NB15
