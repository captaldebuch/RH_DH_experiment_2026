import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovGate

/-!
# Route C: the source-normalized central period value

Auli--Bayad--Beck define

`c_a(h/q) = q^a * sum_{m=1}^{q-1} cot(pi*m*h/q) * zeta(-a,m/q)`.

This module defines that finite family and proves its central limit from the
unconditional rational Hurwitz value already available in the project.  A
precise proposition-valued package then records Bettin--Conrey's master
reciprocity.  From that package we prove, rather than assume, that

`-i*zeta(-a)*psi_a(h/k)`

tends to the source-normalized central side isolated in
`BCFLogTaperRouteCCentralReciprocity`.  Finally the result is lifted through
the complete primitive H15 interior aggregation at every fixed cutoff.

No uniform outer-cutoff estimate is asserted.

Reference: J. S. Auli, A. Bayad, M. Beck, *Reciprocity Theorems for
Bettin--Conrey Sums*, Theorem 1.1, arXiv:1601.06839.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKuznetsovGate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodRealization
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The literal finite Auli--Bayad--Beck family `c_a(h/q)` for a nonzero
modulus. -/
noncomputable def auliBettinConreyFiniteSum
    (z : ℂ) (h q : ℕ) [NeZero q] : ℂ :=
  (q : ℂ) ^ z *
    ∑ m ∈ Finset.Ico 1 q,
      (cotangentTermV (m * h) q : ℂ) *
        HurwitzZeta.hurwitzZeta
          (ZMod.toAddCircle (m : ZMod q)) (-z)

/-- Totalization at modulus zero.  H15 uses only positive moduli. -/
noncomputable def auliBettinConreyFiniteSumTotal
    (z : ℂ) (h q : ℕ) : ℂ :=
  if hq : q = 0 then 0
  else @auliBettinConreyFiniteSum z h q ⟨hq⟩

/-- At `z = 0`, the analytic finite family is exactly the literal central
Bettin--Conrey sum. -/
theorem auliBettinConreyFiniteSum_zero
    (h q : ℕ) [NeZero q] :
    auliBettinConreyFiniteSum 0 h q =
      bettinConreyCentralFiniteSum h q := by
  unfold auliBettinConreyFiniteSum bettinConreyCentralFiniteSum
  rw [Complex.cpow_zero, one_mul]
  apply Finset.sum_congr rfl
  intro m hm
  have hq : 0 < q := NeZero.pos q
  have hm_ge : 1 ≤ m := (Finset.mem_Ico.mp hm).1
  have hm_lt : m < q := (Finset.mem_Ico.mp hm).2
  have hm_ne : (m : ZMod q) ≠ 0 := by
    intro hz
    have hval := congrArg (ZMod.val : ZMod q → ℕ) hz
    rw [ZMod.val_natCast_of_lt hm_lt] at hval
    simp only [ZMod.val_zero] at hval
    omega
  simp only [neg_zero]
  rw [rationalHurwitzZeroFormula.value_eq (m : ZMod q)]
  simp only [periodicBernoulliOneValue, if_neg hm_ne]
  rw [ZMod.val_natCast_of_lt hm_lt]

/-- The finite analytic family is continuous at the central parameter. -/
theorem continuousAt_auliBettinConreyFiniteSum_zero
    (h q : ℕ) [NeZero q] :
    ContinuousAt (fun z : ℂ => auliBettinConreyFiniteSum z h q) 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne q)
  have hpow : ContinuousAt (fun z : ℂ => (q : ℂ) ^ z) 0 :=
    continuousAt_const_cpow hq0
  apply hpow.mul
  refine tendsto_finsetSum (Finset.Ico 1 q) fun m _hm => ?_
  have hzeta : DifferentiableAt ℂ
      (HurwitzZeta.hurwitzZeta (ZMod.toAddCircle (m : ZMod q))) 0 :=
    HurwitzZeta.differentiableAt_hurwitzZeta _ (by norm_num)
  exact tendsto_const_nhds.mul
    (hzeta.continuousAt.comp_of_eq continuousAt_id.neg (by simp))

/-- The actual Auli--Bayad--Beck finite family tends to its central finite
sum, with no analytic hypothesis. -/
theorem tendsto_auliBettinConreyFiniteSumTotal_zero
    (h q : ℕ) (hq : 0 < q) :
    Tendsto (fun z : ℂ => auliBettinConreyFiniteSumTotal z h q)
      (𝓝[≠] 0) (𝓝 (bettinConreyCentralFiniteSum h q)) := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hc : Tendsto (fun z : ℂ => auliBettinConreyFiniteSum z h q)
      (nhdsWithin 0 {0}ᶜ) (nhds (auliBettinConreyFiniteSum 0 h q)) :=
    (continuousAt_auliBettinConreyFiniteSum_zero h q).tendsto.mono_left
      (inf_le_left : nhdsWithin (0 : ℂ) {0}ᶜ ≤ nhds 0)
  rw [← auliBettinConreyFiniteSum_zero h q]
  convert hc using 1
  funext z
  unfold auliBettinConreyFiniteSumTotal
  rw [dif_neg (Nat.ne_of_gt hq)]

/-- Exact rational form of Bettin--Conrey master reciprocity.  The negative
reciprocal cotangent sum is written using its elementary oddness.  This is a
cited analytic interface; no inhabitant is declared here. -/
structure AuliBettinConreyRationalReciprocityPackage where
  periodFunction : ℂ → ℂ → ℂ
  reciprocity : ∀ (z : ℂ) (h k : ℕ), z ≠ 0 → 0 < h → 0 < k →
    Nat.Coprime h k →
      auliBettinConreyFiniteSumTotal z h k -
          (((k : ℂ) / (h : ℂ)) ^ (1 + z)) *
            (-auliBettinConreyFiniteSumTotal z k h) +
          bettinConreyCorrection z h k =
        -I * riemannZeta (-z) *
          periodFunction z (((h : ℝ) / (k : ℝ) : ℝ) : ℂ)

/-- The period side in the normalization of the source reciprocity formula.
The leading parameter in `bettinConreyCorrection` already cancels the zeta
pole, so no additional polar subtraction belongs here. -/
noncomputable def auliBettinConreyRenormalizedPeriodSide
    (H : AuliBettinConreyRationalReciprocityPackage)
    (z : ℂ) (h k : ℕ) : ℂ :=
  -I * riemannZeta (-z) *
    H.periodFunction z (((h : ℝ) / (k : ℝ) : ℝ) : ℂ)

/-- Complex version of the real source-normalized central side. -/
noncomputable def bettinConreyCentralFinitePartSideC
    (h k : ℕ) : ℂ :=
  bettinConreyCentralFiniteSum h k +
    ((k : ℂ) / (h : ℂ)) * bettinConreyCentralFiniteSum k h +
    (-1 / ((Real.pi : ℂ) * (h : ℂ)))

/-- Every central finite sum is real. -/
theorem bettinConreyCentralFiniteSum_im (h k : ℕ) :
    (bettinConreyCentralFiniteSum h k).im = 0 := by
  unfold bettinConreyCentralFiniteSum
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro m _hm
  simp [Complex.mul_im]

/-- The complex presentation of the central finite sum is the canonical
embedding of its real part. -/
theorem bettinConreyCentralFiniteSum_eq_ofReal_re (h k : ℕ) :
    bettinConreyCentralFiniteSum h k =
      ((bettinConreyCentralFiniteSum h k).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [bettinConreyCentralFiniteSum_im]

/-- For positive integer arguments, the complex and real central sides
agree under the canonical embedding. -/
theorem bettinConreyCentralFinitePartSideC_eq_ofReal
    (h k : ℕ) (_hh : 0 < h) (_hk : 0 < k) :
    bettinConreyCentralFinitePartSideC h k =
      (bettinConreyCentralFinitePartSide h k : ℂ) := by
  unfold bettinConreyCentralFinitePartSideC
    bettinConreyCentralFinitePartSide
    bettinConreyCentralValueRe
    bettinConreyCentralFinitePartCorrection
  rw [bettinConreyCentralFiniteSum_eq_ofReal_re h k,
    bettinConreyCentralFiniteSum_eq_ofReal_re k h]
  push_cast
  simp

/-- The source master reciprocity plus the proved finite-family limit gives
the source-normalized central period value.  No additional period limit is
assumed. -/
theorem tendsto_auliBettinConreyRenormalizedPeriodSide_zero
    (H : AuliBettinConreyRationalReciprocityPackage)
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    Tendsto (fun z : ℂ =>
        auliBettinConreyRenormalizedPeriodSide H z h k)
      (𝓝[≠] 0) (𝓝 (bettinConreyCentralFinitePartSide h k : ℂ)) := by
  have hfirst := tendsto_auliBettinConreyFiniteSumTotal_zero h k hk
  have hnegative :=
    (tendsto_auliBettinConreyFiniteSumTotal_zero k h hh).neg
  have hbase0 : ((k : ℂ) / (h : ℂ)) ≠ 0 := by
    exact div_ne_zero (by exact_mod_cast hk.ne') (by exact_mod_cast hh.ne')
  have hpow : Tendsto
      (fun z : ℂ => ((k : ℂ) / (h : ℂ)) ^ (1 + z))
      (𝓝[≠] 0) (𝓝 ((k : ℂ) / (h : ℂ))) := by
    have hc : ContinuousAt
        (fun z : ℂ => ((k : ℂ) / (h : ℂ)) ^ (1 + z)) 0 := by
      exact (continuousAt_const_cpow hbase0).comp
        (continuousAt_const.add continuousAt_id)
    simpa [hbase0] using hc.tendsto.mono_left inf_le_left
  have hcorrection := tendsto_bettinConreyCorrection_zero h k hh hk
  have htotal := hfirst.sub (hpow.mul hnegative) |>.add hcorrection
  have heq :
      (fun z : ℂ => auliBettinConreyRenormalizedPeriodSide H z h k) =ᶠ[𝓝[≠] 0]
        (fun z : ℂ =>
          auliBettinConreyFiniteSumTotal z h k -
              (((k : ℂ) / (h : ℂ)) ^ (1 + z)) *
                (-auliBettinConreyFiniteSumTotal z k h) +
            bettinConreyCorrection z h k) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [auliBettinConreyRenormalizedPeriodSide,
      ← H.reciprocity z h k hz hh hk hcop]
  rw [← bettinConreyCentralFinitePartSideC_eq_ofReal h k hh hk]
  have hrenorm := htotal.congr' heq.symm
  convert hrenorm using 1
  unfold bettinConreyCentralFinitePartSideC
  ring

/-! ## Fixed-cutoff H15 aggregation -/

/-- One primitive H15 pair with the actual punctured period side in place of
its central finite part. -/
noncomputable def routeCInteriorRenormalizedPeriodPair
    (H : AuliBettinConreyRationalReciprocityPackage)
    (z : ℂ) (N g a b : ℕ) : ℂ :=
  if hcop : Nat.Coprime a b then
    if _ha : 2 ≤ a then
      if _hb : 2 ≤ b then
        -(routeCCentralPairScale N g a b : ℂ) *
          (auliBettinConreyRenormalizedPeriodSide H z
              (inverseResidueNumerator a b hcop) b +
            auliBettinConreyRenormalizedPeriodSide H z
              (inverseResidueNumerator b a hcop.symm) a)
      else 0
    else 0
  else 0

/-- Complex presentation of the already formalized real central period pair. -/
noncomputable def routeCInteriorCentralPeriodPairC
    (N g a b : ℕ) : ℂ :=
  if hcop : Nat.Coprime a b then
    if _ha : 2 ≤ a then
      if _hb : 2 ≤ b then
        -(routeCCentralPairScale N g a b : ℂ) *
          ((bettinConreyCentralFinitePartSide
              (inverseResidueNumerator a b hcop) b : ℂ) +
            (bettinConreyCentralFinitePartSide
              (inverseResidueNumerator b a hcop.symm) a : ℂ))
      else 0
    else 0
  else 0

theorem routeCInteriorCentralPeriodPairC_eq_ofReal
    (N g a b : ℕ) :
    routeCInteriorCentralPeriodPairC N g a b =
      (routeCInteriorCentralPeriodPair N g a b : ℂ) := by
  classical
  unfold routeCInteriorCentralPeriodPairC
    routeCInteriorCentralPeriodPair routeCInteriorPairLift
  split_ifs <;> push_cast <;> ring

/-- Coefficientwise central passage through an actual primitive H15 pair. -/
theorem tendsto_routeCInteriorRenormalizedPeriodPair_zero
    (H : AuliBettinConreyRationalReciprocityPackage)
    (N g a b : ℕ) :
    Tendsto (fun z : ℂ =>
        routeCInteriorRenormalizedPeriodPair H z N g a b)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (routeCInteriorCentralPeriodPairC N g a b)) := by
  classical
  unfold routeCInteriorRenormalizedPeriodPair
    routeCInteriorCentralPeriodPairC
  by_cases hcop : Nat.Coprime a b
  · simp only [dif_pos hcop]
    by_cases ha : 2 ≤ a
    · simp only [dif_pos ha]
      by_cases hb : 2 ≤ b
      · simp only [dif_pos hb]
        have hh₁ : 0 < inverseResidueNumerator a b hcop :=
          inverseResidueNumerator_pos a b hcop hb
        have hh₂ : 0 < inverseResidueNumerator b a hcop.symm :=
          inverseResidueNumerator_pos b a hcop.symm ha
        have h₁ := tendsto_auliBettinConreyRenormalizedPeriodSide_zero
          H (inverseResidueNumerator a b hcop) b hh₁ (by omega)
            (inverseResidueNumerator_coprime a b hcop)
        have h₂ := tendsto_auliBettinConreyRenormalizedPeriodSide_zero
          H (inverseResidueNumerator b a hcop.symm) a hh₂ (by omega)
            (inverseResidueNumerator_coprime b a hcop.symm)
        exact tendsto_const_nhds.mul (h₁.add h₂)
      · simp only [dif_neg hb]
        exact tendsto_const_nhds
    · simp only [dif_neg ha]
      exact tendsto_const_nhds
  · simp only [dif_neg hcop]
    exact tendsto_const_nhds

/-- The punctured period side summed over every primitive interior pair at a
fixed H15 cutoff. -/
noncomputable def routeCInteriorRenormalizedPeriodAggregate
    (H : AuliBettinConreyRationalReciprocityPackage)
    (z : ℂ) (N : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g),
        routeCInteriorRenormalizedPeriodPair H z N g a b

noncomputable def routeCInteriorCentralPeriodAggregateC (N : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g),
        routeCInteriorCentralPeriodPairC N g a b

theorem routeCInteriorCentralPeriodAggregateC_eq_ofReal (N : ℕ) :
    routeCInteriorCentralPeriodAggregateC N =
      (routeCInteriorCentralPeriodAggregate N : ℂ) := by
  unfold routeCInteriorCentralPeriodAggregateC
    routeCInteriorCentralPeriodAggregate routeCInteriorPairAggregate
  simp_rw [routeCInteriorCentralPeriodPairC_eq_ofReal]
  push_cast
  rfl

/-- Finite aggregation commutes with the central punctured limit.  This is
pointwise in `N`; no uniform outer-cutoff interchange is claimed. -/
theorem tendsto_routeCInteriorRenormalizedPeriodAggregate_zero
    (H : AuliBettinConreyRationalReciprocityPackage) (N : ℕ) :
    Tendsto (fun z : ℂ =>
        routeCInteriorRenormalizedPeriodAggregate H z N)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (routeCInteriorCentralPeriodAggregate N : ℂ)) := by
  rw [← routeCInteriorCentralPeriodAggregateC_eq_ofReal]
  unfold routeCInteriorRenormalizedPeriodAggregate
    routeCInteriorCentralPeriodAggregateC
  refine tendsto_finsetSum (Finset.Icc 1 N) fun g _hg => ?_
  refine tendsto_finsetSum (Finset.Icc 1 (N / g)) fun a _ha => ?_
  refine tendsto_finsetSum (Finset.Icc 1 (N / g)) fun b _hb => ?_
  exact tendsto_routeCInteriorRenormalizedPeriodPair_zero H N g a b

/-- Reattach the genuine dual cotangent aggregate after the analytic period
side has been renormalized.  The dual term is independent of the central
parameter. -/
noncomputable def routeCInteriorRenormalizedPeriodDualAggregate
    (H : AuliBettinConreyRationalReciprocityPackage)
    (z : ℂ) (N : ℕ) : ℂ :=
  routeCInteriorRenormalizedPeriodAggregate H z N +
    (routeCInteriorCentralDualAggregate N : ℂ)

/-- At every fixed cutoff, the period-plus-dual expression converges to the
literal central cotangent aggregate after subtraction of the genuine Laurent
finite part.  This is the exact finite Route-C synthesis identity. -/
theorem tendsto_routeCInteriorRenormalizedPeriodDualAggregate_zero
    (H : AuliBettinConreyRationalReciprocityPackage) (N : ℕ) :
    Tendsto (fun z : ℂ =>
        routeCInteriorRenormalizedPeriodDualAggregate H z N)
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((routeCInteriorCentralCotangentAggregate N -
        routeCInteriorCentralFinitePartAggregate N : ℝ) : ℂ)) := by
  have ht :=
    (tendsto_routeCInteriorRenormalizedPeriodAggregate_zero H N).add
      (tendsto_const_nhds : Tendsto
        (fun _ : ℂ => (routeCInteriorCentralDualAggregate N : ℂ))
        (nhdsWithin 0 {0}ᶜ)
        (nhds (routeCInteriorCentralDualAggregate N : ℂ)))
  have htarget :
      ((routeCInteriorCentralCotangentAggregate N -
          routeCInteriorCentralFinitePartAggregate N : ℝ) : ℂ) =
        (routeCInteriorCentralPeriodAggregate N : ℂ) +
          (routeCInteriorCentralDualAggregate N : ℂ) := by
    rw [routeCInteriorCentralCotangent_sub_finitePart]
    push_cast
    rfl
  rw [htarget]
  simpa [routeCInteriorRenormalizedPeriodDualAggregate] using ht

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
