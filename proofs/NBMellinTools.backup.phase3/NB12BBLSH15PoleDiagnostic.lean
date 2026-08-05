/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSCorrectionBridge

/-!
# NB12r: the actual H15 pole diagnostic

This file inserts the signed Möbius logarithmic taper and the two oriented
primitive rational rows of the H15 Estermann interior into the active Laurent
ledger.

The structural stop test is negative: the global `s⁻³` coefficient is already
nonzero at cutoff `N = 4`.  The `s⁻²` coefficient is consequently not an
identically vanishing function of the Abel damping either.  Thus the retained
H15 correction cannot be matched by the first-order finite part before the
higher polar modes have been subtracted by the rectangle/endpoint ledger.

The last section records the exact replacement: a correction--finite-part
piece plus a polar residual.  It is an identity, not an estimate.
-/

open scoped BigOperators Topology
open Complex

namespace NBMellinTools.NB12

open NBMellinTools.NB8

/-! ## The finite H15 row family -/

/-- A finite index contains the gcd slice, the two primitive variables and
one of the two orientations.  Natural values are shifted by one below. -/
abbrev H15LaurentRowIndex (N : ℕ) := Fin N × Fin N × Fin N × Fin 2

def h15LaurentG {N : ℕ} (i : H15LaurentRowIndex N) : ℕ := i.1.val + 1
def h15LaurentA {N : ℕ} (i : H15LaurentRowIndex N) : ℕ := i.2.1.val + 1
def h15LaurentQ {N : ℕ} (i : H15LaurentRowIndex N) : ℕ := i.2.2.1.val + 1
def h15LaurentOrientation {N : ℕ} (i : H15LaurentRowIndex N) : ℕ :=
  i.2.2.2.val

/-- Denominator of the selected orientation, reduced for the zero-weight
invalid rows as well.  On a genuine H15 row it is exactly `q` or `a`. -/
def h15LaurentReducedDenominator {N : ℕ}
    (i : H15LaurentRowIndex N) : ℕ :=
  let a₀ := if h15LaurentOrientation i = 0 then h15LaurentA i else h15LaurentQ i
  let q₀ := if h15LaurentOrientation i = 0 then h15LaurentQ i else h15LaurentA i
  q₀ / Nat.gcd a₀ q₀

/-- Canonical inverse-residue numerator used by the H15 Estermann rows. -/
noncomputable def h15InverseResidueNumerator
    (a q : ℕ) (hcop : Nat.Coprime a q) : ℕ :=
  (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ).val : ZMod q).val

theorem h15InverseResidueNumerator_coprime
    (a q : ℕ) (hcop : Nat.Coprime a q) :
    Nat.Coprime (h15InverseResidueNumerator a q hcop) q := by
  unfold h15InverseResidueNumerator
  exact ZMod.val_coe_unit_coprime ((ZMod.unitOfCoprime a hcop)⁻¹)

/-- A total reduced row.  Invalid indices receive a harmless reduced row and
zero arithmetic weight; valid indices specialize to the two inverse-residue
orientations of the H15 interior. -/
noncomputable def h15LaurentRow {N : ℕ}
    (i : H15LaurentRowIndex N) : BBLSReducedRational := by
  let a₀ := if h15LaurentOrientation i = 0 then h15LaurentA i else h15LaurentQ i
  let q₀ := if h15LaurentOrientation i = 0 then h15LaurentQ i else h15LaurentA i
  let d := Nat.gcd a₀ q₀
  have ha₀ : 0 < a₀ := by
    by_cases h : h15LaurentOrientation i = 0 <;>
      simp [a₀, h15LaurentA, h15LaurentQ, h]
  have hq₀ : 0 < q₀ := by
    by_cases h : h15LaurentOrientation i = 0 <;>
      simp [q₀, h15LaurentA, h15LaurentQ, h]
  have hd : 0 < d := Nat.gcd_pos_of_pos_left q₀ ha₀
  let a := a₀ / d
  let q := q₀ / d
  have hq : 0 < q := Nat.div_pos (Nat.gcd_le_right a₀ hq₀) hd
  have hcop : Nat.Coprime a q := Nat.coprime_div_gcd_div_gcd hd
  exact
    { numerator := h15InverseResidueNumerator a q hcop
      denominator := q
      denominator_pos := hq
      coprime := h15InverseResidueNumerator_coprime a q hcop }

@[simp] theorem h15LaurentRow_denominator {N : ℕ}
    (i : H15LaurentRowIndex N) :
    (h15LaurentRow i).denominator = h15LaurentReducedDenominator i := by
  rfl

/-- Total natural-index form of the active signed log-taper coefficient.
Its product agrees with the historical positive-Dirichlet-polynomial
normalization because the two global minus signs cancel. -/
noncomputable def h15NaturalLogTaperCoeff (N m : ℕ) : ℝ :=
  -((ArithmeticFunction.moebius m : ℤ) : ℝ) *
    (Real.log ((N : ℝ) / (m : ℝ)) / Real.log (N : ℝ))

/-- Interior support: `ga,gq ≤ N`, primitive variables at least two, and
coprime primitive pair. -/
def h15LaurentRowValid {N : ℕ} (i : H15LaurentRowIndex N) : Prop :=
  h15LaurentG i * h15LaurentA i ≤ N ∧
    h15LaurentG i * h15LaurentQ i ≤ N ∧
    2 ≤ h15LaurentA i ∧ 2 ≤ h15LaurentQ i ∧
    Nat.Coprime (h15LaurentA i) (h15LaurentQ i)

/-- Exact H15 coefficient multiplying one oriented active Estermann row.
Both orientations have the same real coefficient
`c_N(ga)c_N(gq) · π/(g a q)`. -/
noncomputable def h15LaurentRowWeight {N : ℕ}
    (i : H15LaurentRowIndex N) : ℂ := by
  classical
  exact if h15LaurentRowValid i then
    (h15NaturalLogTaperCoeff N (h15LaurentG i * h15LaurentA i) *
      h15NaturalLogTaperCoeff N (h15LaurentG i * h15LaurentQ i) /
      (h15LaurentG i : ℝ) * Real.pi /
      ((h15LaurentA i : ℝ) * (h15LaurentQ i : ℝ)) : ℝ)
  else 0

/-- Actual H15 global cubic Laurent coefficient at sequence index `n`. -/
noncomputable def h15GlobalThirdOrderCoefficient (n : ℕ) : ℂ :=
  bblsFiniteThirdOrderAggregate
    (h15LaurentRowWeight (N := logTaperLength n))
    (h15LaurentRow (N := logTaperLength n))

/-- Actual H15 global quadratic Laurent coefficient at sequence index `n`. -/
noncomputable def h15GlobalSecondOrderCoefficient
    (damping : ℝ) (n : ℕ) : ℂ :=
  bblsFiniteSecondOrderAggregate damping
    (h15LaurentRowWeight (N := logTaperLength n))
    (h15LaurentRow (N := logTaperLength n))

/-! ## The stop test -/

set_option maxHeartbeats 2000000 in
-- The proof evaluates the complete `4 × 4 × 4 × 2` finite row family.
/-- Exact value of the cubic coefficient at cutoff `N = 4` (`n = 2`).
Only the ordered primitive pairs `(2,3)` and `(3,2)` survive. -/
theorem h15GlobalThirdOrderCoefficient_two_formula :
    h15GlobalThirdOrderCoefficient 2 =
      (-5 * Real.pi / 18 : ℝ) *
        logTaperCoeffs 2 ⟨1, by simp [logTaperLength]⟩ *
        logTaperCoeffs 2 ⟨2, by simp [logTaperLength]⟩ := by
  classical
  unfold h15GlobalThirdOrderCoefficient bblsFiniteThirdOrderAggregate
  simp only [logTaperLength]
  change (∑ i : Fin 4 × Fin 4 × Fin 4 × Fin 2,
      h15LaurentRowWeight i *
        bblsActiveThirdOrderCoefficient (h15LaurentRow i)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_four, Fin.sum_univ_two]
  simp [h15LaurentRowWeight, h15LaurentRowValid,
    h15NaturalLogTaperCoeff, h15LaurentG, h15LaurentA, h15LaurentQ,
    h15LaurentOrientation, h15LaurentReducedDenominator,
    bblsActiveThirdOrderCoefficient]
  simp [show Odd 3 by decide, logTaperCoeffs, logTaperLength]
  ring

private theorem h15LogTaperCoeff_two_pos :
    0 < logTaperCoeffs 2 ⟨1, by simp [logTaperLength]⟩ := by
  change 0 < -((ArithmeticFunction.moebius 2 : ℤ) : ℝ) *
    (Real.log ((4 : ℝ) / 2) / Real.log 4)
  rw [show (4 : ℝ) / 2 = 2 by norm_num]
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2)]
  norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  positivity

private theorem h15LogTaperCoeff_three_pos :
    0 < logTaperCoeffs 2 ⟨2, by simp [logTaperLength]⟩ := by
  change 0 < -((ArithmeticFunction.moebius 3 : ℤ) : ℝ) *
    (Real.log ((4 : ℝ) / 3) / Real.log 4)
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)]
  norm_num
  have hlog43 : 0 < Real.log ((4 : ℝ) / 3) :=
    Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  positivity

/-- Priority-1 diagnostic: the actual H15 cubic global mode does not vanish. -/
theorem h15GlobalThirdOrderCoefficient_two_ne_zero :
    h15GlobalThirdOrderCoefficient 2 ≠ 0 := by
  rw [h15GlobalThirdOrderCoefficient_two_formula]
  have hneg :
      (-5 * Real.pi / 18 : ℝ) *
          logTaperCoeffs 2 ⟨1, by simp [logTaperLength]⟩ *
          logTaperCoeffs 2 ⟨2, by simp [logTaperLength]⟩ < 0 := by
    have hfirst : (-5 * Real.pi / 18 : ℝ) < 0 := by
      nlinarith [Real.pi_pos]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos hfirst h15LogTaperCoeff_two_pos)
      h15LogTaperCoeff_three_pos
  exact_mod_cast (ne_of_lt hneg)

/-- Changing the Abel damping changes the quadratic pole coefficient by the
logarithmic increment times the cubic coefficient. -/
theorem bblsFiniteSecondOrderAggregate_sub
    {ι : Type*} [Fintype ι]
    (d₁ d₂ : ℝ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational) :
    bblsFiniteSecondOrderAggregate d₁ weight row -
        bblsFiniteSecondOrderAggregate d₂ weight row =
      (Complex.log (d₁ : ℂ) - Complex.log (d₂ : ℂ)) *
        bblsFiniteThirdOrderAggregate weight row := by
  unfold bblsFiniteSecondOrderAggregate bblsFiniteThirdOrderAggregate
  rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold bblsActiveSecondOrderCoefficient bblsActiveThirdOrderCoefficient
  ring

theorem h15GlobalSecondOrderCoefficient_exp_sub_one :
    h15GlobalSecondOrderCoefficient (Real.exp 1) 2 -
        h15GlobalSecondOrderCoefficient 1 2 =
      h15GlobalThirdOrderCoefficient 2 := by
  unfold h15GlobalSecondOrderCoefficient h15GlobalThirdOrderCoefficient
  rw [bblsFiniteSecondOrderAggregate_sub]
  rw [Complex.ofReal_exp]
  rw [Complex.log_exp]
  · simp
  · norm_num [Real.pi_pos]
  · exact_mod_cast Real.pi_nonneg

/-- Priority-1 diagnostic for the quadratic mode: it cannot vanish
identically in the damping parameter. -/
theorem h15GlobalSecondOrderCoefficient_not_identically_zero :
    h15GlobalSecondOrderCoefficient 1 2 ≠ 0 ∨
      h15GlobalSecondOrderCoefficient (Real.exp 1) 2 ≠ 0 := by
  by_contra h
  push Not at h
  have hd : h15GlobalSecondOrderCoefficient (Real.exp 1) 2 -
      h15GlobalSecondOrderCoefficient 1 2 = 0 := by
    rw [h.1, h.2]
    ring
  rw [h15GlobalSecondOrderCoefficient_exp_sub_one] at hd
  exact h15GlobalThirdOrderCoefficient_two_ne_zero hd

/-! ## Exact-plus-residual contingency -/

/-- Weighted denominator moment.  It is the negative cubic coefficient. -/
noncomputable def bblsDenominatorMoment
    {ι : Type*} [Fintype ι]
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) : ℂ :=
  ∑ i, weight i * ((row i).denominator : ℂ)⁻¹

/-- Weighted coefficient of the simple Hurwitz pole. -/
noncomputable def bblsSimplePoleMoment
    {ι : Type*} [Fintype ι]
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) : ℂ :=
  ∑ i, weight i *
    (2 * ((Real.eulerMascheroniConstant : ℂ) -
      Complex.log ((row i).denominator : ℂ)) /
      ((row i).denominator : ℂ))

/-- Weighted finite parts at the Estermann pole. -/
noncomputable def bblsFinitePartMoment
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) : ℂ :=
  ∑ i, weight i *
    (bblsChosenActiveTriplePolePackage damping hdamping (row i)).finitePart 1

/-- Damping-dependent polar contribution to the first-order coefficient. -/
noncomputable def bblsFirstOrderPolarResidual
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational) : ℂ :=
  bblsActiveReflectedWeightSecondCoefficient damping *
      bblsDenominatorMoment weight row -
    (-((Real.eulerMascheroniConstant : ℂ) +
      Complex.log (damping : ℂ))) * bblsSimplePoleMoment weight row

/-- Damping-independent-in-form exact correction/finite-part piece. -/
noncomputable def bblsCorrectionFinitePartGap
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping) (retainedCorrection : ℂ)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) : ℂ :=
  retainedCorrection - bblsFinitePartMoment damping hdamping weight row

theorem bblsFiniteThirdOrderAggregate_eq_neg_denominatorMoment
    {ι : Type*} [Fintype ι]
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    bblsFiniteThirdOrderAggregate weight row =
      -bblsDenominatorMoment weight row := by
  unfold bblsFiniteThirdOrderAggregate bblsDenominatorMoment
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold bblsActiveThirdOrderCoefficient
  ring

theorem bblsFiniteSecondOrderAggregate_eq_moments
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational) :
    bblsFiniteSecondOrderAggregate damping weight row =
      (-((Real.eulerMascheroniConstant : ℂ) +
          Complex.log (damping : ℂ))) *
          bblsDenominatorMoment weight row +
        bblsSimplePoleMoment weight row := by
  unfold bblsFiniteSecondOrderAggregate bblsDenominatorMoment
    bblsSimplePoleMoment
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold bblsActiveSecondOrderCoefficient
  ring

theorem bblsFiniteFirstOrderAggregate_eq_exact_add_residual
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (weight : ι → ℂ) (row : ι → BBLSReducedRational) :
    bblsFiniteFirstOrderAggregate damping hdamping weight row =
      bblsFirstOrderPolarResidual damping weight row -
        bblsFinitePartMoment damping hdamping weight row := by
  unfold bblsFiniteFirstOrderAggregate bblsFirstOrderPolarResidual
    bblsDenominatorMoment bblsSimplePoleMoment bblsFinitePartMoment
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold bblsActiveFirstOrderCoefficient
  ring

/-- Priority-2 contingency identity `G = G_exact + E_residual`.  Any uniform
bound must keep the polar residual coupled to the two higher residue modes;
discarding it is not justified by exact numerator completion alone. -/
theorem bblsGlobalCorrectionGap_eq_exact_add_polarResidual
    {ι : Type*} [Fintype ι]
    (damping : ℝ) (hdamping : 0 < damping)
    (retainedCorrection : ℂ) (weight : ι → ℂ)
    (row : ι → BBLSReducedRational) :
    bblsGlobalCorrectionGap damping hdamping
        retainedCorrection weight row =
      bblsCorrectionFinitePartGap damping hdamping
          retainedCorrection weight row +
        bblsFirstOrderPolarResidual damping weight row := by
  unfold bblsGlobalCorrectionGap bblsCorrectionFinitePartGap
  rw [bblsFiniteFirstOrderAggregate_eq_exact_add_residual]
  ring

end NBMellinTools.NB12
