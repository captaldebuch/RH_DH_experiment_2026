import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperBettinConreyReciprocity
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperCancellationAnatomy
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction

/-!
# Route B7.2: finite aggregation of the Bettin--Conrey pole residue

The literal local Bettin--Conrey correction has a pole at `a = 0`, whose
residue coefficient is `-1 / (π h)`.  This file inserts that residue
coefficient into the exact coprime gcd slices used by H15 and performs the
finite aggregation before any estimate is attempted.

The result is deliberately a bookkeeping theorem, not a cancellation
claim.  It shows that the local reciprocity correction produces an explicit
quadratic coprime-pair moment.  The original H15 linear correction and
constant remain as a separate, explicitly named discrepancy.  Consequently
the local master reciprocity does not by itself discharge the global signed
Kuznetsov gate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroReduction

/-- The coefficient left after extracting the primitive Gram kernel from the
`g`-th gcd slice. -/
noncomputable def coprimeSliceCoefficient
    (N g a b : ℕ) : ℝ :=
  dirichletCoeff N (g * a) * dirichletCoeff N (g * b) * (g : ℝ)⁻¹

/-- The coefficient multiplying a symmetric pair of cotangent sums in the
primitive Vasyunin kernel. -/
noncomputable def vasyuninPairCoefficient
    (N g a b : ℕ) : ℂ :=
  (coprimeSliceCoefficient N g a b *
      (-Real.pi / (2 * (a : ℝ) * (b : ℝ))) : ℝ)

/-- The standard representative of the inverse of `a` modulo `q`.  The
coprimality proof makes `a` a unit in `ZMod q`; taking the natural value after
inversion fixes the numerator convention used by the Estermann--Vasyunin
bridge. -/
noncomputable def inverseResidueNumerator
    (a q : ℕ) (hcop : Nat.Coprime a q) : ℕ :=
  (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ).val : ZMod q).val

/-- For a genuine modulus `q ≥ 2`, the inverse-residue representative lies
in the positive range.  Modulus one is excluded because its sole residue has
natural representative zero and belongs to the endpoint sector. -/
theorem inverseResidueNumerator_pos
    (a q : ℕ) (hcop : Nat.Coprime a q) (hq : 2 ≤ q) :
    0 < inverseResidueNumerator a q hcop := by
  haveI : Fact (1 < q) := ⟨by omega⟩
  unfold inverseResidueNumerator
  rw [ZMod.val_pos]
  exact Units.ne_zero _

/-- The complete finite H15-weighted sum of the two orientations of the
scaled Bettin--Conrey residue probe at parameter `z`. -/
noncomputable def bettinConreyCorrectionAggregate
    (z : ℂ) (N : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g),
        if hcop : Nat.Coprime a b then
          if _ha : 2 ≤ a then
            if _hb : 2 ≤ b then
              vasyuninPairCoefficient N g a b *
                (bettinConreyCorrection z
                    (inverseResidueNumerator a b hcop) b +
                  bettinConreyCorrection z
                    (inverseResidueNumerator b a hcop.symm) a)
            else 0
          else 0
        else 0

/-- The explicit real quadratic moment obtained from the pole residue of the
local Bettin--Conrey correction.  Both orientations are retained in the
definition, so its normalization can be compared directly with the
Vasyunin pair coefficient.  This is not the Laurent finite part. -/
noncomputable def bettinConreyCentralCorrection (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g),
        if hcop : Nat.Coprime a b then
          if _ha : 2 ≤ a then
            if _hb : 2 ≤ b then
              coprimeSliceCoefficient N g a b *
                (1 / (2 * (a : ℝ) * (b : ℝ)) *
                  (1 / (inverseResidueNumerator a b hcop : ℝ) +
                    1 / (inverseResidueNumerator b a hcop.symm : ℝ)))
            else 0
          else 0
        else 0

/-- The weighted local correction has the displayed central value.  The
positivity assumptions are exactly those supplied by the finite interval
indices in the aggregate. -/
theorem tendsto_weighted_bettinConrey_pair
    (N g a b h₁ k₁ h₂ k₂ : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hh₁ : 0 < h₁) (hk₁ : 0 < k₁)
    (hh₂ : 0 < h₂) (hk₂ : 0 < k₂) :
    Tendsto
      (fun z : ℂ =>
        vasyuninPairCoefficient N g a b *
          (bettinConreyCorrection z h₁ k₁ +
            bettinConreyCorrection z h₂ k₂))
      (𝓝[≠] 0)
      (𝓝 (coprimeSliceCoefficient N g a b *
        (1 / (2 * (a : ℝ) * (b : ℝ)) *
          (1 / (h₁ : ℝ) + 1 / (h₂ : ℝ))) : ℝ)) := by
  have hab := (tendsto_bettinConreyCorrection_zero h₁ k₁ hh₁ hk₁).add
    (tendsto_bettinConreyCorrection_zero h₂ k₂ hh₂ hk₂)
  have hconst : Tendsto
      (fun _ : ℂ => vasyuninPairCoefficient N g a b)
      (𝓝[≠] 0) (𝓝 (vasyuninPairCoefficient N g a b)) :=
    tendsto_const_nhds
  have hweighted := hconst.mul hab
  have hvalue :
      vasyuninPairCoefficient N g a b *
          (-1 / ((Real.pi : ℂ) * (h₁ : ℂ)) +
            -1 / ((Real.pi : ℂ) * (h₂ : ℂ))) =
        (coprimeSliceCoefficient N g a b *
          (1 / (2 * (a : ℝ) * (b : ℝ)) *
            (1 / (h₁ : ℝ) + 1 / (h₂ : ℝ))) : ℝ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    have hh₁0 : (h₁ : ℂ) ≠ 0 := by exact_mod_cast hh₁.ne'
    have hh₂0 : (h₂ : ℂ) ≠ 0 := by exact_mod_cast hh₂.ne'
    unfold vasyuninPairCoefficient
    push_cast
    field_simp [hpi, ha0, hb0, hh₁0, hh₂0]
    ring
  simpa only [hvalue] using hweighted

/-- Exact finite aggregation of the singular Bettin--Conrey pole residue. -/
theorem tendsto_bettinConreyCorrectionAggregate_zero (N : ℕ) :
    Tendsto (fun z : ℂ => bettinConreyCorrectionAggregate z N)
      (𝓝[≠] 0) (𝓝 (bettinConreyCentralCorrection N : ℂ)) := by
  classical
  unfold bettinConreyCorrectionAggregate
  have hsum : Tendsto
      (fun z : ℂ =>
        ∑ g ∈ Finset.Icc 1 N,
          ∑ a ∈ Finset.Icc 1 (N / g),
            ∑ b ∈ Finset.Icc 1 (N / g),
              if hcop : Nat.Coprime a b then
                if ha : 2 ≤ a then
                  if hb : 2 ≤ b then
                    vasyuninPairCoefficient N g a b *
                      (bettinConreyCorrection z
                          (inverseResidueNumerator a b hcop) b +
                        bettinConreyCorrection z
                          (inverseResidueNumerator b a hcop.symm) a)
                  else 0
                else 0
              else 0)
      (𝓝[≠] 0)
      (𝓝 (∑ g ∈ Finset.Icc 1 N,
        ∑ a ∈ Finset.Icc 1 (N / g),
          ∑ b ∈ Finset.Icc 1 (N / g),
            if hcop : Nat.Coprime a b then
              if ha : 2 ≤ a then
                if hb : 2 ≤ b then
                  ((coprimeSliceCoefficient N g a b *
                    (1 / (2 * (a : ℝ) * (b : ℝ)) *
                      (1 / (inverseResidueNumerator a b hcop : ℝ) +
                        1 / (inverseResidueNumerator b a hcop.symm : ℝ))) : ℝ) : ℂ)
                else 0
              else 0
            else 0)) := by
    apply tendsto_finsetSum
    intro g hg
    apply tendsto_finsetSum
    intro a ha
    apply tendsto_finsetSum
    intro b hb
    by_cases hcop : Nat.Coprime a b
    · by_cases ha2 : 2 ≤ a
      · by_cases hb2 : 2 ≤ b
        · simp only [dif_pos hcop, dif_pos ha2, dif_pos hb2]
          exact tendsto_weighted_bettinConrey_pair N g a b
            (inverseResidueNumerator a b hcop) b
            (inverseResidueNumerator b a hcop.symm) a
            (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1)
            (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb).1)
            (inverseResidueNumerator_pos a b hcop hb2)
            (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb).1)
            (inverseResidueNumerator_pos b a hcop.symm ha2)
            (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1)
        · simp only [dif_pos hcop, dif_pos ha2, dif_neg hb2]
          exact tendsto_const_nhds
      · simp only [dif_pos hcop, dif_neg ha2]
        exact tendsto_const_nhds
    · simp only [dif_neg hcop]
      exact tendsto_const_nhds
  have hcast : (bettinConreyCentralCorrection N : ℂ) =
      ∑ g ∈ Finset.Icc 1 N,
        ∑ a ∈ Finset.Icc 1 (N / g),
          ∑ b ∈ Finset.Icc 1 (N / g),
            if hcop : Nat.Coprime a b then
              if ha : 2 ≤ a then
                if hb : 2 ≤ b then
                  ((coprimeSliceCoefficient N g a b *
                    (1 / (2 * (a : ℝ) * (b : ℝ)) *
                      (1 / (inverseResidueNumerator a b hcop : ℝ) +
                        1 / (inverseResidueNumerator b a hcop.symm : ℝ))) : ℝ) : ℂ)
                else 0
              else 0
            else 0 := by
    unfold bettinConreyCentralCorrection
    push_cast
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hcop : Nat.Coprime a b
    · by_cases ha2 : 2 ≤ a
      · by_cases hb2 : 2 ≤ b
        · rw [dif_pos hcop, dif_pos hcop, dif_pos ha2, dif_pos ha2,
            dif_pos hb2, dif_pos hb2]
          rw [Complex.ofReal_mul]
          congr 1
          simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_add,
            Complex.ofReal_inv, Complex.ofReal_one]
          norm_num
        · rw [dif_pos hcop, dif_pos hcop, dif_pos ha2, dif_pos ha2,
            dif_neg hb2, dif_neg hb2]
          norm_num
      · rw [dif_pos hcop, dif_pos hcop, dif_neg ha2, dif_neg ha2]
        norm_num
    · rw [dif_neg hcop, dif_neg hcop]
      norm_num
  rw [hcast]
  exact hsum

/-- The exact finite discrepancy after the central reciprocity correction is
coupled to the original H15 linear term and constant.  Vanishing of this
quantity is what would be needed for the local correction to close that part
of the global expression. -/
noncomputable def bettinConreyRetainedCorrectionDiscrepancy (N : ℕ) : ℝ :=
  bettinConreyCentralCorrection N + 2 * gramLinearCorrection N + 1

/-- The correction-matching question is exactly the vanishing of the named
finite discrepancy; no analytic estimate is hidden in this equivalence. -/
theorem bettinConrey_cancels_retainedCorrection_iff (N : ℕ) :
    bettinConreyCentralCorrection N =
        -(2 * gramLinearCorrection N + 1) ↔
      bettinConreyRetainedCorrectionDiscrepancy N = 0 := by
  unfold bettinConreyRetainedCorrectionDiscrepancy
  constructor <;> intro h
  · rw [h]
    ring
  · linarith

/-! ## First nontrivial cutoff: the two corrections do not coincide -/

@[simp] theorem dirichletCoeff_two_one : dirichletCoeff 2 1 = 1 := by
  unfold dirichletCoeff
  rw [weight_one (N := 2) (by norm_num)]
  norm_num

@[simp] theorem dirichletCoeff_two_two : dirichletCoeff 2 2 = 0 := by
  unfold dirichletCoeff
  rw [weight_cutoff (N := 2) (by norm_num)]
  ring

/-- At `N = 2` the only nonzero coefficient comes from the modulus-one
endpoint.  The genuine inverse-residue interior correction is therefore
zero. -/
theorem bettinConreyCentralCorrection_two :
    bettinConreyCentralCorrection 2 = 0 := by
  classical
  unfold bettinConreyCentralCorrection
  apply Finset.sum_eq_zero
  intro g hg
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b _hb
  by_cases hcop : Nat.Coprime a b
  · rw [dif_pos hcop]
    by_cases ha2 : 2 ≤ a
    · rw [dif_pos ha2]
      have hgpos : 0 < g :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hg).1
      have hmul : g * a ≤ 2 :=
        by simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hgpos).mp (Finset.mem_Icc.mp ha).2
      have htwo_mul : g * 2 ≤ g * a := Nat.mul_le_mul_left g ha2
      have hga : g * a = 2 := by omega
      have hcoeff : dirichletCoeff 2 (g * a) = 0 := by
        rw [hga]
        exact dirichletCoeff_two_two
      unfold coprimeSliceCoefficient
      rw [hcoeff]
      simp
    · rw [dif_neg ha2]
  · rw [dif_neg hcop]

/-- The original H15 linear correction at the same cutoff is
`1 - EulerGamma`; the endpoint coefficient at `2` vanishes. -/
theorem gramLinearCorrection_two :
    gramLinearCorrection 2 = 1 - Real.eulerMascheroniConstant := by
  have h12 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [RH.Criteria.NymanBeurling.BCFLogTaperCancellationAnatomy.gramLinearCorrection_eq_explicit,
    h12]
  norm_num

/-- The first nontrivial cutoff already rules out an exact identification of
the local Bettin--Conrey central term with the negative retained H15
correction.  Therefore a global transformed/off-diagonal contribution is
still necessary. -/
theorem bettinConreyCentralCorrection_two_ne_neg_retained :
    bettinConreyCentralCorrection 2 ≠
      -(2 * gramLinearCorrection 2 + 1) := by
  rw [bettinConreyCentralCorrection_two, gramLinearCorrection_two]
  intro h
  have hγ : Real.eulerMascheroniConstant = 3 / 2 := by linarith
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

/-- Equivalently, the explicit retained-correction discrepancy is already
nonzero at the first nontrivial cutoff. -/
theorem bettinConreyRetainedCorrectionDiscrepancy_two_ne_zero :
    bettinConreyRetainedCorrectionDiscrepancy 2 ≠ 0 := by
  intro hzero
  exact bettinConreyCentralCorrection_two_ne_neg_retained
    ((bettinConrey_cancels_retainedCorrection_iff 2).mpr hzero)

/-! ## Exact interior/endpoint split of the Estermann expression -/

/-- The primitive Estermann slice with both moduli at least two.  This is the
sector on which both inverse-residue Bettin--Conrey corrections have positive
numerators in their standard representatives. -/
noncomputable def estermannInteriorCoprimeRatioSlice
    (H : EstermannAtZeroPackage) (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ b ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a b ∧ 2 ≤ a ∧ 2 ≤ b then
      dirichletCoeff N (g * a) * dirichletCoeff N (g * b) *
        (g : ℝ)⁻¹ * estermannCoprimeGramKernel H a b
    else 0

/-- The complementary modulus-one endpoint sector. -/
noncomputable def estermannEndpointCoprimeRatioSlice
    (H : EstermannAtZeroPackage) (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ b ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a b ∧ ¬(2 ≤ a ∧ 2 ≤ b) then
      dirichletCoeff N (g * a) * dirichletCoeff N (g * b) *
        (g : ℝ)⁻¹ * estermannCoprimeGramKernel H a b
    else 0

/-- Every primitive Estermann slice is exactly the sum of its genuine
inverse-residue interior and modulus-one endpoint sectors. -/
theorem estermannCoprimeRatioSlice_eq_interior_add_endpoint
    (H : EstermannAtZeroPackage) (N g : ℕ) :
    estermannCoprimeRatioSlice H N g =
      estermannInteriorCoprimeRatioSlice H N g +
        estermannEndpointCoprimeRatioSlice H N g := by
  classical
  unfold estermannCoprimeRatioSlice estermannInteriorCoprimeRatioSlice
    estermannEndpointCoprimeRatioSlice
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hcop : Nat.Coprime a b
  · by_cases hinterior : 2 ≤ a ∧ 2 ≤ b
    · simp [hinterior]
    · simp [hinterior]
  · simp [hcop]

/-- The complete automorphic interior sector. -/
noncomputable def estermannInteriorExpression
    (H : EstermannAtZeroPackage) (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N, estermannInteriorCoprimeRatioSlice H N g

/-- The endpoint sector completed by the original H15 linear correction and
constant.  B7.2 shows that these terms cannot be replaced by the local
interior reciprocity correction. -/
noncomputable def estermannEndpointCompletedExpression
    (H : EstermannAtZeroPackage) (N : ℕ) : ℝ :=
  (∑ g ∈ Finset.Icc 1 N, estermannEndpointCoprimeRatioSlice H N g) +
    2 * gramLinearCorrection N + 1

/-- Exact global split: the full H15 Estermann expression is the signed sum
of the automorphic interior and the completed endpoint sector. -/
theorem estermannCoupledExpression_eq_interior_add_endpointCompleted
    (H : EstermannAtZeroPackage) (N : ℕ) :
    estermannCoupledExpression H N =
      estermannInteriorExpression H N +
        estermannEndpointCompletedExpression H N := by
  unfold estermannCoupledExpression estermannInteriorExpression
    estermannEndpointCompletedExpression
  have hs :
      (∑ g ∈ Finset.Icc 1 N, estermannCoprimeRatioSlice H N g) =
        ∑ g ∈ Finset.Icc 1 N,
          (estermannInteriorCoprimeRatioSlice H N g +
            estermannEndpointCoprimeRatioSlice H N g) := by
    apply Finset.sum_congr rfl
    intro g _
    exact estermannCoprimeRatioSlice_eq_interior_add_endpoint H N g
  rw [hs, Finset.sum_add_distrib]
  ring

/-- The same endpoint-completed split transported back to the original H15
coupled expression. -/
theorem coupledGcdRatioExpression_eq_estermannInterior_add_endpointCompleted
    (H : EstermannAtZeroPackage) (N : ℕ) :
    RH.Criteria.NymanBeurling.BCFLogTaperSpectral.coupledGcdRatioExpression N =
      estermannInteriorExpression H N +
        estermannEndpointCompletedExpression H N := by
  rw [coupledGcdRatioExpression_eq_estermannCoupledExpression H,
    estermannCoupledExpression_eq_interior_add_endpointCompleted H]

end RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
