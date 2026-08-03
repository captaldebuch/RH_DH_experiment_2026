import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCReciprocityPassage
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannFiniteFourier

/-!
# Route C: the central Bettin--Conrey sum in the H15 convention

Auli--Bayad--Beck define

`c_a(h/q) = q^a * sum_{m=1}^{q-1} cot(pi*m*h/q) * zeta(-a,m/q)`.

At `a = 0`, the Hurwitz value is `1/2-m/q`.  With the Vasyunin convention in
this project, multiplication by the reduced numerator permutes the nonzero
residues and gives the exact finite identity

`c_0(a⁻¹/q) = -V(a,q)`.

This module proves that identity from the existing finite Fourier endpoint.
It is the convention-matching step needed before the Auli--Bayad--Beck period
function can be inserted into the complete Route-C mean.  It does not assert
any outer-cutoff estimate.

References:

* J. S. Auli, A. Bayad, M. Beck, *Reciprocity Theorems for Bettin--Conrey
  Sums*, Theorem 1.1 and the definition preceding it, arXiv:1601.06839.
* S. Bettin, B. Conrey, *Period functions and cotangent sums*, Theorem 4,
  arXiv:1111.0931.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodRealization

open scoped BigOperators
open Filter
open ZMod
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFiniteFourier
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperCotangentReduction
open RH.Criteria.NymanBeurling.BCFLogTaperEnergyMeanAnatomy
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCReciprocityPassage
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The literal finite `a = 0` Bettin--Conrey sum.  It is complex-valued only
to match the analytic family; every summand is real. -/
noncomputable def bettinConreyCentralFiniteSum (h q : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ico 1 q,
    (cotangentTermV (m * h) q : ℂ) *
      ((1 : ℂ) / 2 - (m : ℂ) / (q : ℂ))

/-- The same central value on the complete residue system.  The zero residue
is harmless because `residueCotangent 0 = 0`. -/
noncomputable def bettinConreyCentralResidueSum
    (h q : ℕ) [NeZero q] : ℂ :=
  ∑ m : ZMod q,
    residueCotangent ((h : ZMod q) * m) *
      periodicBernoulliOneValue m

/-- Cotangent is unchanged when its natural numerator is reduced modulo its
positive denominator. -/
theorem cotangentTermV_mod (n q : ℕ) (hq : 0 < q) :
    cotangentTermV (n % q) q = cotangentTermV n q := by
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have hn : n % q + q * (n / q) = n := Nat.mod_add_div n q
  have hnR :
      ((n % q : ℕ) : ℝ) + (q : ℝ) * ((n / q : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast hn
  have harg :
      Real.pi * (n : ℝ) / q =
        Real.pi * ((n % q : ℕ) : ℝ) / q +
          ((n / q : ℕ) : ℝ) * Real.pi := by
    rw [← hnR]
    field_simp [hqR]
  unfold cotangentTermV
  rw [harg, Real.cos_add_nat_mul_pi, Real.sin_add_nat_mul_pi]
  have hsign : ((-1 : ℝ) ^ (n / q)) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hsign]

/-- The natural finite sum is exactly its complete-residue formulation for a
reduced positive fraction. -/
theorem bettinConreyCentralFiniteSum_eq_residueSum
    (h q : ℕ) [NeZero q] (hcop : Nat.Coprime h q) :
    bettinConreyCentralFiniteSum h q =
      bettinConreyCentralResidueSum h q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [bettinConreyCentralResidueSum,
    sum_zmod_eq_sum_Ioc_of_zero
      (fun m : ZMod q =>
        residueCotangent ((h : ZMod q) * m) *
          periodicBernoulliOneValue m)]
  · unfold bettinConreyCentralFiniteSum
    rw [show Finset.Ico 1 q = Finset.Ioc 0 (q - 1) by
      ext m
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    have hm_lt : m < q := by omega
    have hm_ne : (m : ZMod q) ≠ 0 := by
      intro hz
      have hval := congrArg (ZMod.val : ZMod q → ℕ) hz
      rw [ZMod.val_natCast_of_lt hm_lt] at hval
      simp only [ZMod.val_zero] at hval
      omega
    have hhm_ne : (h : ZMod q) * (m : ZMod q) ≠ 0 := by
      intro hz
      have hunit : IsUnit (h : ZMod q) :=
        (ZMod.isUnit_iff_coprime h q).mpr hcop
      exact hm_ne (hunit.mul_right_eq_zero.mp hz)
    have hval :
        ((h : ZMod q) * (m : ZMod q)).val = (h * m) % q := by
      rw [← Nat.cast_mul, ZMod.val_natCast]
    have hcot :
        residueCotangent ((h : ZMod q) * (m : ZMod q)) =
          (cotangentTermV (m * h) q : ℂ) := by
      unfold residueCotangent
      rw [if_neg hhm_ne, hval]
      norm_cast
      simpa [Nat.mul_comm] using cotangentTermV_mod (h * m) q hq
    have hbernoulli :
        periodicBernoulliOneValue (m : ZMod q) =
          (1 : ℂ) / 2 - (m : ℂ) / (q : ℂ) := by
      simp only [periodicBernoulliOneValue, if_neg hm_ne]
      rw [ZMod.val_natCast_of_lt hm_lt]
    rw [hcot, hbernoulli]
  · simp

/-- Multiplication by the reduced numerator reindexes the literal central
Bettin--Conrey sum into the Bernoulli--cotangent pairing used by the finite
Estermann endpoint. -/
theorem bettinConreyCentralResidueSum_inverse_eq_neg_vasyunin
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    bettinConreyCentralResidueSum (inverseResidue a q) q =
      -(cotangentSumVFormula a q : ℂ) := by
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a hcop
  let F : ZMod q → ℂ := fun m =>
    residueCotangent ((inverseResidue a q : ZMod q) * m) *
      periodicBernoulliOneValue m
  have hinv (r : ZMod q) :
      (inverseResidue a q : ZMod q) * ((a : ZMod q) * r) = r := by
    have hia :
        (inverseResidue a q : ZMod q) * (a : ZMod q) = 1 := by
      simpa only [Nat.cast_mul] using
        inverseResidue_mul_mod_eq_one a q hcop
    rw [← mul_assoc, hia, one_mul]
  unfold bettinConreyCentralResidueSum
  change (∑ m : ZMod q, F m) = _
  calc
    (∑ m : ZMod q, F m) = ∑ r : ZMod q, F (u.val * r) := by
      symm
      exact Fintype.sum_equiv u.mulLeft _ _ (fun r => rfl)
    _ = ∑ r : ZMod q,
          residueCotangent r *
            periodicBernoulliOneValue ((a : ZMod q) * r) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [F, u, ZMod.coe_unitOfCoprime]
      rw [hinv]
    _ = -(cotangentSumVFormula a q : ℂ) :=
      sum_residueCotangent_mul_bernoulli_unitMul a q hcop

/-- Exact `a = 0` convention match in the natural finite-sum notation of
Auli--Bayad--Beck. -/
theorem bettinConreyCentralFiniteSum_inverse_eq_neg_vasyunin
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    bettinConreyCentralFiniteSum (inverseResidue a q) q =
      -(cotangentSumVFormula a q : ℂ) := by
  rw [bettinConreyCentralFiniteSum_eq_residueSum
    (inverseResidue a q) q]
  · exact bettinConreyCentralResidueSum_inverse_eq_neg_vasyunin a q hcop
  · let u : (ZMod q)ˣ := ZMod.unitOfCoprime a hcop
    simpa [u, inverseResidue, ZMod.unitOfCoprime] using
      ZMod.val_coe_unit_coprime (u⁻¹)

/-! ## Lift through the complete primitive H15 expression -/

/-- Totalized central Bettin--Conrey value in the inverse-numerator
normalization used by H15.  The zero modulus never occurs in the primitive
sum; assigning it zero keeps the definition total. -/
noncomputable def bettinConreyCentralInverseValue (a q : ℕ) : ℂ :=
  if hq : q = 0 then 0
  else
    bettinConreyCentralFiniteSum
      (@inverseResidue a q ⟨hq⟩) q

/-- On a reduced positive fraction, the totalized value is exactly the
negative Vasyunin sum. -/
theorem bettinConreyCentralInverseValue_eq_neg_vasyunin
    (a q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a q) :
    bettinConreyCentralInverseValue a q =
      -(cotangentSumVFormula a q : ℂ) := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  unfold bettinConreyCentralInverseValue
  rw [dif_neg (Nat.ne_of_gt hq)]
  exact bettinConreyCentralFiniteSum_inverse_eq_neg_vasyunin a q hcop

/-- The primitive Gram kernel written with the literal `a = 0`
Bettin--Conrey sums.  Both orientations are retained. -/
noncomputable def bettinConreyCentralCoprimeGramKernel
    (a b : ℕ) : ℝ :=
  (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
      (1 / (a : ℝ) + 1 / (b : ℝ)) +
    ((b : ℝ) - (a : ℝ)) / (2 * (a : ℝ) * (b : ℝ)) *
      Real.log ((a : ℝ) / (b : ℝ)) +
    Real.pi / (2 * (a : ℝ) * (b : ℝ)) *
      ((bettinConreyCentralInverseValue a b).re +
        (bettinConreyCentralInverseValue b a).re)

/-- Exact pointwise convention match for the primitive Gram kernel. -/
theorem vasyuninBEntryFormula_eq_bettinConreyCentralCoprimeGramKernel
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) :
    vasyuninBEntryFormula a b =
      bettinConreyCentralCoprimeGramKernel a b := by
  unfold vasyuninBEntryFormula bettinConreyCentralCoprimeGramKernel
  rw [bettinConreyCentralInverseValue_eq_neg_vasyunin a b hb hcop,
    bettinConreyCentralInverseValue_eq_neg_vasyunin b a ha hcop.symm]
  simp
  ring

/-- One complete gcd slice with its primitive cotangent terms replaced by
the literal central Bettin--Conrey sums. -/
noncomputable def bettinConreyCentralCoprimeRatioSlice
    (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ b ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a b then
      dirichletCoeff N (g * a) * dirichletCoeff N (g * b) *
        (g : ℝ)⁻¹ * bettinConreyCentralCoprimeGramKernel a b
    else 0

/-- Every primitive H15 gcd slice has the central Bettin--Conrey
realization, with no estimate and no omitted endpoint. -/
theorem gramCoprimeRatioSlice_eq_bettinConreyCentralCoprimeRatioSlice
    (N g : ℕ) :
    gramCoprimeRatioSlice N g =
      bettinConreyCentralCoprimeRatioSlice N g := by
  classical
  unfold gramCoprimeRatioSlice bettinConreyCentralCoprimeRatioSlice
  apply Finset.sum_congr rfl
  intro a ha_mem
  have ha : 0 < a :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha_mem).1
  apply Finset.sum_congr rfl
  intro b hb_mem
  have hb : 0 < b :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb_mem).1
  split_ifs with hcop
  · rw [baezDuarteGramEntry_eq_vasyuninBEntryFormula_proved a b ha hb,
      vasyuninBEntryFormula_eq_bettinConreyCentralCoprimeGramKernel
        a b ha hb hcop]
  · rfl

/-- Complete H15 expression in central Bettin--Conrey coordinates.  The
original linear correction and endpoint constant remain inside the same
signed quantity. -/
noncomputable def bettinConreyCentralCoupledExpression (N : ℕ) : ℝ :=
  (∑ g ∈ Finset.Icc 1 N,
      bettinConreyCentralCoprimeRatioSlice N g) +
    2 * gramLinearCorrection N + 1

/-- The central Bettin--Conrey coordinate change preserves the complete H15
expression exactly. -/
theorem coupledGcdRatioExpression_eq_bettinConreyCentralCoupledExpression
    (N : ℕ) :
    coupledGcdRatioExpression N =
      bettinConreyCentralCoupledExpression N := by
  unfold coupledGcdRatioExpression bettinConreyCentralCoupledExpression
  apply congrArg (fun x : ℝ => x + 2 * gramLinearCorrection N + 1)
  apply Finset.sum_congr rfl
  intro g _
  exact gramCoprimeRatioSlice_eq_bettinConreyCentralCoprimeRatioSlice N g

/-- Dyadic mean of the complete central Bettin--Conrey realization. -/
noncomputable def ehmDyadicBettinConreyCentralCoupledMean (X : ℕ) : ℝ :=
  (∑ N ∈ ehmDyadicNBlock X,
      bettinConreyCentralCoupledExpression N) /
    ((ehmDyadicNBlock X).card : ℝ)

/-- The lifted central realization is exactly the canonical energy mean. -/
theorem ehmDyadicBettinConreyCentralCoupledMean_eq_energyMean (X : ℕ) :
    ehmDyadicBettinConreyCentralCoupledMean X =
      ehmDyadicExactEnergyMean X := by
  unfold ehmDyadicBettinConreyCentralCoupledMean ehmDyadicExactEnergyMean
  congr 1
  apply Finset.sum_congr rfl
  intro N _
  rw [← coupledGcdRatioExpression_eq_bettinConreyCentralCoupledExpression]
  simpa only [coupledGcdRatioExpression] using
    (energy_eq_gcdRatioFormula N).symm

/-- Consequently the only remaining Route-C assertion is still the complete
outer-scale signed limit.  The exact Auli--Bayad--Beck convention match does
not weaken or solve that analytic gate. -/
theorem tendsto_bettinConreyCentralCoupledMean_zero_iff_energyMean :
    Filter.Tendsto ehmDyadicBettinConreyCentralCoupledMean Filter.atTop
        (nhds 0) ↔
      Filter.Tendsto ehmDyadicExactEnergyMean Filter.atTop (nhds 0) := by
  apply tendsto_congr'
  exact Filter.Eventually.of_forall
    ehmDyadicBettinConreyCentralCoupledMean_eq_energyMean

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodRealization
