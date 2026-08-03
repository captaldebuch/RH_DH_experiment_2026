/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15EstermannGramAssembly
import NBMellinTools.NB12BBLSH15BettinChandeeInstantiation
import NBMellinTools.NB12BBLSH15Rectangle

/-!
# Exact H15 row assembly at the Estermann endpoint

This module identifies the two genuine Estermann special values in each
primitive Gram entry with the two orientations of the actual NB12 H15 row
type. Invalid rows remain present with zero weight. This is the finite
assembly needed before any contour shift or limiting argument.
-/

open scoped BigOperators

namespace NBMellinTools.NB15

open NBMellinTools.NB8
open NBMellinTools.NB12
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## Elementary and special-value sectors -/

noncomputable def estermannGramElementaryFormula (a q : ℕ) : ℝ :=
  (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
      (1 / (a : ℝ) + 1 / (q : ℝ)) +
    ((q : ℝ) - (a : ℝ)) / (2 * (a : ℝ) * (q : ℝ)) *
      Real.log ((a : ℝ) / (q : ℝ))

noncomputable def estermannGramSpecialValueFormula (a q : ℕ) : ℝ :=
  Real.pi / ((a : ℝ) * (q : ℝ)) *
    ((activeInverseEstermannZero a q).im +
      (activeInverseEstermannZero q a).im)

theorem estermannGramFormula_eq_elementary_add_specialValue
    (a q : ℕ) :
    estermannGramFormula a q =
      estermannGramElementaryFormula a q +
        estermannGramSpecialValueFormula a q := by
  rfl

noncomputable def oneBasedEstermannElementaryInteriorSlice
    (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ q ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a q ∧ 2 ≤ a ∧ 2 ≤ q then
      h15NaturalLogTaperCoeff N (g * a) *
        h15NaturalLogTaperCoeff N (g * q) *
        (g : ℝ)⁻¹ * estermannGramElementaryFormula a q
    else 0

noncomputable def oneBasedEstermannSpecialValueInteriorSlice
    (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ q ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a q ∧ 2 ≤ a ∧ 2 ≤ q then
      h15NaturalLogTaperCoeff N (g * a) *
        h15NaturalLogTaperCoeff N (g * q) *
        (g : ℝ)⁻¹ * estermannGramSpecialValueFormula a q
    else 0

theorem oneBasedEstermannInteriorSlice_eq_elementary_add_specialValue
    (N g : ℕ) :
    oneBasedEstermannInteriorSlice N g =
      oneBasedEstermannElementaryInteriorSlice N g +
        oneBasedEstermannSpecialValueInteriorSlice N g := by
  classical
  unfold oneBasedEstermannInteriorSlice
    oneBasedEstermannElementaryInteriorSlice
    oneBasedEstermannSpecialValueInteriorSlice
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : Nat.Coprime a q ∧ 2 ≤ a ∧ 2 ≤ q
  · simp only [if_pos h,
      estermannGramFormula_eq_elementary_add_specialValue]
    ring
  · simp [h]

noncomputable def oneBasedEstermannElementaryInterior (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N, oneBasedEstermannElementaryInteriorSlice N g

noncomputable def oneBasedEstermannSpecialValueInterior (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N, oneBasedEstermannSpecialValueInteriorSlice N g

theorem oneBasedEstermannInterior_eq_elementary_add_specialValue
    (N : ℕ) :
    oneBasedEstermannInterior N =
      oneBasedEstermannElementaryInterior N +
        oneBasedEstermannSpecialValueInterior N := by
  unfold oneBasedEstermannInterior oneBasedEstermannElementaryInterior
    oneBasedEstermannSpecialValueInterior
  simp_rw [oneBasedEstermannInteriorSlice_eq_elementary_add_specialValue]
  exact Finset.sum_add_distrib

/-! ## The actual NB12 row endpoint -/

/-- Total active continuation at zero for a natural numerator and modulus.
The zero-modulus branch is irrelevant to H15 but removes typeclass plumbing
from finite reindexing. -/
noncomputable def activeEstermannZero (a q : ℕ) : ℂ :=
  if hq : q = 0 then 0
  else @bblsEstermannHurwitzContinuation a q ⟨hq⟩ 0

noncomputable def h15LaurentRowEstermannZeroValue
    {N : ℕ} (i : H15LaurentRowIndex N) : ℂ :=
  activeEstermannZero (h15LaurentRow i).numerator
    (h15LaurentRow i).denominator

theorem h15InverseResidueNumerator_eq_inverseResidue
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    h15InverseResidueNumerator a q hcop = inverseResidue a q := by
  unfold h15InverseResidueNumerator inverseResidue
  rfl

theorem h15LaurentRowEstermannZeroValue_orientation_zero
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i)
    (horientation : h15LaurentOrientation i = 0) :
    h15LaurentRowEstermannZeroValue i =
      activeInverseEstermannZero (h15LaurentA i) (h15LaurentQ i) := by
  have hq0 : h15LaurentQ i ≠ 0 := by simp [h15LaurentQ]
  letI : NeZero (h15LaurentQ i) := ⟨hq0⟩
  unfold h15LaurentRowEstermannZeroValue
  rw [h15LaurentRow_numerator_eq_inverse_of_orientation_zero
      i hvalid horientation,
    h15LaurentRow_denominator_eq_q_of_orientation_zero
      i hvalid horientation,
    h15InverseResidueNumerator_eq_inverseResidue]
  exact (activeInverseEstermannZero_eq _ _
    (by simp [h15LaurentQ])).symm

theorem h15LaurentRowEstermannZeroValue_orientation_one
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i)
    (horientation : h15LaurentOrientation i = 1) :
    h15LaurentRowEstermannZeroValue i =
      activeInverseEstermannZero (h15LaurentQ i) (h15LaurentA i) := by
  have ha0 : h15LaurentA i ≠ 0 := by simp [h15LaurentA]
  letI : NeZero (h15LaurentA i) := ⟨ha0⟩
  have hden : (h15LaurentRow i).denominator = h15LaurentA i := by
    have hne : h15LaurentOrientation i ≠ 0 := by omega
    simp [h15LaurentRow_denominator, h15LaurentReducedDenominator,
      hne, hvalid.2.2.2.2.symm.gcd_eq_one]
  unfold h15LaurentRowEstermannZeroValue
  rw [h15LaurentRow_numerator_eq_inverse_of_orientation_one
      i hvalid horientation, hden,
    h15InverseResidueNumerator_eq_inverseResidue]
  exact (activeInverseEstermannZero_eq _ _
    (by simp [h15LaurentA])).symm

/-- The literal finite endpoint aggregate on the exact NB12 H15 row type. -/
noncomputable def h15LaurentEstermannZeroAggregate (N : ℕ) : ℝ :=
  ∑ i : H15LaurentRowIndex N,
    (h15LaurentRowWeight i * h15LaurentRowEstermannZeroValue i).im

/-! ## Exact finite reindexing -/

/-- The same special-value interior on the full positive cube, with the
hyperbolic cutoff retained as a predicate. -/
noncomputable def oneBasedEstermannSpecialValueFullBox (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N,
    ∑ q ∈ Finset.Icc 1 N,
      if g * a ≤ N ∧ g * q ≤ N ∧
          Nat.Coprime a q ∧ 2 ≤ a ∧ 2 ≤ q then
        h15NaturalLogTaperCoeff N (g * a) *
          h15NaturalLogTaperCoeff N (g * q) *
          (g : ℝ)⁻¹ * estermannGramSpecialValueFormula a q
      else 0

private theorem Icc_div_eq_filter_mul_le
    (N g : ℕ) (hg : 0 < g) :
    Finset.Icc 1 (N / g) =
      (Finset.Icc 1 N).filter (fun a => g * a ≤ N) := by
  ext a
  simp only [Finset.mem_Icc, Finset.mem_filter]
  constructor
  · intro ha
    have hga : g * a ≤ N := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hg).mp ha.2
    have haN : a ≤ N :=
      (Nat.le_mul_of_pos_left a hg).trans hga
    exact ⟨⟨ha.1, haN⟩, hga⟩
  · intro ha
    exact ⟨ha.1.1, (Nat.le_div_iff_mul_le hg).mpr
      (by simpa [Nat.mul_comm] using ha.2)⟩

theorem oneBasedEstermannSpecialValueInterior_eq_fullBox (N : ℕ) :
    oneBasedEstermannSpecialValueInterior N =
      oneBasedEstermannSpecialValueFullBox N := by
  classical
  unfold oneBasedEstermannSpecialValueInterior
    oneBasedEstermannSpecialValueInteriorSlice
    oneBasedEstermannSpecialValueFullBox
  apply Finset.sum_congr rfl
  intro g hgmem
  have hg : 0 < g :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hgmem).1
  rw [Icc_div_eq_filter_mul_le N g hg]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hga : g * a ≤ N
  · simp only [if_pos hga]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hgq : g * q ≤ N
    · by_cases hrest : Nat.Coprime a q ∧ 2 ≤ a ∧ 2 ≤ q
      · simp [hga, hgq, hrest]
      · simp [hga, hgq, hrest]
    · simp [hga, hgq]
  · simp [hga]

private theorem sum_Icc_one_eq_sum_fin
    {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    (∑ n ∈ Finset.Icc 1 N, f n) =
      ∑ i : Fin N, f (i.val + 1) := by
  classical
  apply Finset.sum_bij (fun n hn => ⟨n - 1, by
    simp only [Finset.mem_Icc] at hn
    omega⟩)
  · intro n hn
    simp
  · intro a ha b hb hab
    simp only [Fin.mk.injEq] at hab
    simp only [Finset.mem_Icc] at ha hb
    omega
  · intro i hi
    refine ⟨i.val + 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · apply Fin.ext
      simp
  · intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [Nat.sub_add_cancel hn1]

theorem oneBasedEstermannSpecialValueFullBox_eq_laurentAggregate
    (N : ℕ) :
    oneBasedEstermannSpecialValueFullBox N =
      h15LaurentEstermannZeroAggregate N := by
  classical
  unfold oneBasedEstermannSpecialValueFullBox
    h15LaurentEstermannZeroAggregate
  rw [sum_Icc_one_eq_sum_fin]
  simp_rw [sum_Icc_one_eq_sum_fin]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro q _
  let i0 : H15LaurentRowIndex N := (g, a, q, 0)
  let i1 : H15LaurentRowIndex N := (g, a, q, 1)
  by_cases h :
      (g.val + 1) * (a.val + 1) ≤ N ∧
        (g.val + 1) * (q.val + 1) ≤ N ∧
        Nat.Coprime (a.val + 1) (q.val + 1) ∧
        2 ≤ a.val + 1 ∧ 2 ≤ q.val + 1
  · have hv0 : h15LaurentRowValid i0 := by
      exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2, h.2.2.1⟩
    have hv1 : h15LaurentRowValid i1 := by
      exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2, h.2.2.1⟩
    have ho0 : h15LaurentOrientation i0 = 0 := by
      simp [i0, h15LaurentOrientation]
    have ho1 : h15LaurentOrientation i1 = 1 := by
      simp [i1, h15LaurentOrientation]
    rw [if_pos h]
    change
      h15NaturalLogTaperCoeff N ((g.val + 1) * (a.val + 1)) *
          h15NaturalLogTaperCoeff N ((g.val + 1) * (q.val + 1)) *
          ((g.val + 1 : ℕ) : ℝ)⁻¹ *
          estermannGramSpecialValueFormula (a.val + 1) (q.val + 1) =
        (h15LaurentRowWeight i0 *
            h15LaurentRowEstermannZeroValue i0).im +
          (h15LaurentRowWeight i1 *
            h15LaurentRowEstermannZeroValue i1).im
    rw [h15LaurentRowEstermannZeroValue_orientation_zero i0 hv0 ho0,
      h15LaurentRowEstermannZeroValue_orientation_one i1 hv1 ho1]
    simp only [h15LaurentRowWeight, if_pos hv0, if_pos hv1]
    unfold estermannGramSpecialValueFormula
    simp only [i0, i1, h15LaurentG, h15LaurentA, h15LaurentQ,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero]
    ring
  · have hnv0 : ¬ h15LaurentRowValid i0 := by
      intro hv
      apply h
      exact ⟨hv.1, hv.2.1, hv.2.2.2.2, hv.2.2.1, hv.2.2.2.1⟩
    have hnv1 : ¬ h15LaurentRowValid i1 := by
      intro hv
      apply h
      exact ⟨hv.1, hv.2.1, hv.2.2.2.2, hv.2.2.1, hv.2.2.2.1⟩
    rw [if_neg h]
    simp [i0, i1, h15LaurentRowWeight, hnv0, hnv1]

theorem oneBasedEstermannSpecialValueInterior_eq_laurentAggregate
    (N : ℕ) :
    oneBasedEstermannSpecialValueInterior N =
      h15LaurentEstermannZeroAggregate N :=
  (oneBasedEstermannSpecialValueInterior_eq_fullBox N).trans
    (oneBasedEstermannSpecialValueFullBox_eq_laurentAggregate N)

/-- Everything in the certified energy not belonging to the finite
Estermann special-value row aggregate.  The endpoint is deliberately
retained here. -/
noncomputable def h15CertifiedElementaryEndpointLedger (n : ℕ) : ℝ :=
  preFECorrection n +
    oneBasedEstermannElementaryInterior (logTaperLength n) +
    oneBasedVasyuninEndpoint (logTaperLength n)

/-- Exact finite assembly type forced by the certified energy: one explicit
elementary/endpoint ledger plus the actual finite NB12 Estermann row
aggregate. -/
theorem logTaperL2Error_eq_elementaryEndpoint_add_laurentAggregate
    (n : ℕ) :
    logTaperL2Error n =
      h15CertifiedElementaryEndpointLedger n +
        h15LaurentEstermannZeroAggregate (logTaperLength n) := by
  rw [logTaperL2Error_eq_gcdEstermannInterior_add_endpoint,
    oneBasedEstermannInterior_eq_elementary_add_specialValue,
    oneBasedEstermannSpecialValueInterior_eq_laurentAggregate]
  unfold h15CertifiedElementaryEndpointLedger
  ring

/-! ## Identification with the contour residue amplitude -/

theorem h15LaurentRowEstermannZeroValue_eq_continuation
    {N : ℕ} (i : H15LaurentRowIndex N) :
    h15LaurentRowEstermannZeroValue i =
      @bblsEstermannHurwitzContinuation
        (h15LaurentRow i).numerator (h15LaurentRow i).denominator
        ⟨(h15LaurentRow i).denominator_pos.ne'⟩ 0 := by
  unfold h15LaurentRowEstermannZeroValue activeEstermannZero
  simp only [dif_neg (h15LaurentRow i).denominator_pos.ne']

/-- The certified special-value sector is precisely the imaginary part of
the undamped amplitude of the additional s=1 contour residue. -/
theorem h15LaurentEstermannZeroAggregate_eq_additionalResidueAmplitude_im
    (N : ℕ) :
    h15LaurentEstermannZeroAggregate N =
      (bblsFiniteAdditionalResidueAmplitude
        (h15LaurentRowWeight (N := N))
        (h15LaurentRow (N := N))).im := by
  classical
  unfold h15LaurentEstermannZeroAggregate
    bblsFiniteAdditionalResidueAmplitude
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [h15LaurentRowEstermannZeroValue_eq_continuation]

theorem h15LaurentEstermannZeroAggregate_eq_h15Amplitude_im
    (n : ℕ) :
    h15LaurentEstermannZeroAggregate (logTaperLength n) =
      (h15AdditionalResidueAmplitude n).im := by
  exact h15LaurentEstermannZeroAggregate_eq_additionalResidueAmplitude_im _

/-- Exact global assembly in the contour vocabulary.  The energy contains
the undamped s=1 residue amplitude itself, not the adaptively damped residue.
Consequently, decay of damping times amplitude cannot by itself imply decay
of the certified energy. -/
theorem logTaperL2Error_eq_elementaryEndpoint_add_additionalResidueAmplitude_im
    (n : ℕ) :
    logTaperL2Error n =
      h15CertifiedElementaryEndpointLedger n +
        (h15AdditionalResidueAmplitude n).im := by
  rw [logTaperL2Error_eq_elementaryEndpoint_add_laurentAggregate,
    h15LaurentEstermannZeroAggregate_eq_h15Amplitude_im]

/-- Exact recovery of the undamped amplitude from the specialized contour
residue.  The inverse damping factor is essential. -/
theorem h15ContourDamping_inv_mul_globalAdditionalResidue
    (n : ℕ) :
    ((h15ContourDamping n : ℂ)⁻¹ *
      h15GlobalAdditionalResidue n) =
        h15AdditionalResidueAmplitude n := by
  rw [h15GlobalAdditionalResidue_eq_adaptive]
  have hδ : (h15ContourDamping n : ℂ) ≠ 0 := by
    exact_mod_cast (h15ContourDamping_pos n).ne'
  field_simp

/-- Equivalent exact energy formula using the actual contour residue.  It
exhibits the inverse damping loss explicitly. -/
theorem logTaperL2Error_eq_elementaryEndpoint_add_rescaledContourResidue_im
    (n : ℕ) :
    logTaperL2Error n =
      h15CertifiedElementaryEndpointLedger n +
        (((h15ContourDamping n : ℂ)⁻¹ *
          h15GlobalAdditionalResidue n).im) := by
  rw [h15ContourDamping_inv_mul_globalAdditionalResidue]
  exact
    logTaperL2Error_eq_elementaryEndpoint_add_additionalResidueAmplitude_im n

end NBMellinTools.NB15
