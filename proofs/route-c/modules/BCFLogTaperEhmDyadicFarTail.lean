import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCommonSplit

/-!
# Uniform vanishing of the dyadic Ehm far divisor tail

The common near/far split leaves the positive quantity

```text
sum N in [X,2X], 16*N^2 *
  sum d in (D,J], |a_N(d)|/d^2.
```

This file proves that a common cutoff `D=D(X)` can make that quantity
uniformly negligible for every `J ≥ D(X)`.  The argument is routine and
unconditional: the logarithmic taper gives
`|a_N(d)| = O_N(1 + sqrt d)`, so `|a_N(d)|/d^2` is summable.  Vanishing of
tails of the resulting finite dyadic sum supplies `D(X)`.

After this module, the far complementary sector is no longer an analytic
obstruction.  The remaining open input is the signed common near-core mean.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicFarTail

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicCommonSplit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSignedAverage

/-! ## Summability of the logarithmic divisor tail -/

/-- For a fixed genuine BCF cutoff, the absolute logarithmic coefficient
divided by `d²` is summable. -/
theorem summable_abs_dirichletCoeff_div_sq
    (N : ℕ) (hN : 2 ≤ N) :
    Summable (fun d : ℕ => |dirichletCoeff N d| / (d : ℝ) ^ 2) := by
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hs2 : Summable (fun d : ℕ => 1 / (d : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs32 : Summable (fun d : ℕ => 1 / (d : ℝ) ^ (3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hmajor : Summable (fun d : ℕ =>
      1 / (d : ℝ) ^ (2 : ℕ) +
        (2 / Real.log (N : ℝ)) * (1 / (d : ℝ) ^ (3 / 2 : ℝ))) :=
    hs2.add (hs32.mul_left (2 / Real.log (N : ℝ)))
  apply Summable.of_norm_bounded hmajor
  intro d
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _)
    (sq_nonneg (d : ℝ)))]
  by_cases hd0 : d = 0
  · subst d
    norm_num
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (Nat.pos_of_ne_zero hd0)
  have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd0))
  have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hratio0 : 0 ≤ Real.log (d : ℝ) / Real.log (N : ℝ) :=
    div_nonneg hlogd0 hlogN.le
  have hweight : |weight N d| ≤
      1 + Real.log (d : ℝ) / Real.log (N : ℝ) := by
    rw [weight_of_two_le hN]
    calc
      |1 - Real.log (d : ℝ) / Real.log (N : ℝ)| ≤
          |(1 : ℝ)| + |Real.log (d : ℝ) / Real.log (N : ℝ)| :=
        abs_sub _ _
      _ = 1 + Real.log (d : ℝ) / Real.log (N : ℝ) := by
        rw [abs_one, abs_of_nonneg hratio0]
  have hlogd : Real.log (d : ℝ) ≤
      2 * (d : ℝ) ^ (1 / 2 : ℝ) := by
    have h := Real.log_le_rpow_div
      (x := (d : ℝ)) (ε := (1 / 2 : ℝ)) hdpos.le (by norm_num)
    nlinarith
  have hcoeff : |dirichletCoeff N d| ≤
      1 + (2 / Real.log (N : ℝ)) * (d : ℝ) ^ (1 / 2 : ℝ) := by
    unfold dirichletCoeff
    rw [abs_mul]
    calc
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |weight N d| ≤
          1 * (1 + Real.log (d : ℝ) / Real.log (N : ℝ)) := by
        gcongr
      _ = 1 + Real.log (d : ℝ) / Real.log (N : ℝ) := by ring
      _ ≤ 1 + (2 * (d : ℝ) ^ (1 / 2 : ℝ)) /
          Real.log (N : ℝ) := by
        have hdiv := (div_le_div_iff_of_pos_right hlogN).mpr hlogd
        simpa [add_comm] using add_le_add_left hdiv 1
      _ = _ := by ring
  calc
    |dirichletCoeff N d| / (d : ℝ) ^ 2 ≤
        (1 + (2 / Real.log (N : ℝ)) * (d : ℝ) ^ (1 / 2 : ℝ)) /
          (d : ℝ) ^ 2 := by gcongr
    _ = 1 / (d : ℝ) ^ (2 : ℕ) +
        (2 / Real.log (N : ℝ)) * (1 / (d : ℝ) ^ (3 / 2 : ℝ)) := by
      have hpow2 : (d : ℝ) ^ (2 : ℕ) = (d : ℝ) ^ (2 : ℝ) :=
        (Real.rpow_natCast (d : ℝ) 2).symm
      rw [hpow2]
      have hratio :
          (d : ℝ) ^ (1 / 2 : ℝ) / (d : ℝ) ^ (2 : ℝ) =
            1 / (d : ℝ) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_sub hdpos]
        norm_num
        exact Real.rpow_neg hdpos.le (3 / 2 : ℝ)
      rw [add_div, mul_div_assoc, hratio]

/-- The finite dyadic sum of weighted divisor-tail sequences is summable. -/
theorem summable_ehmDyadicDivisorTailSeries
    (X : ℕ) (hX : 2 ≤ X) :
    Summable (fun d : ℕ =>
      ∑ N ∈ ehmDyadicNBlock X,
        16 * (N : ℝ) ^ 2 *
          (|dirichletCoeff N d| / (d : ℝ) ^ 2)) := by
  classical
  have hsum : ∀ S : Finset ℕ, (∀ N ∈ S, 2 ≤ N) →
      Summable (fun d : ℕ =>
        ∑ N ∈ S, 16 * (N : ℝ) ^ 2 *
          (|dirichletCoeff N d| / (d : ℝ) ^ 2)) := by
    intro S hS
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
        have ha2 : 2 ≤ a := hS a (Finset.mem_insert_self a S)
        have hSa : Summable (fun d : ℕ =>
            16 * (a : ℝ) ^ 2 *
              (|dirichletCoeff a d| / (d : ℝ) ^ 2)) :=
          (summable_abs_dirichletCoeff_div_sq a ha2).mul_left
            (16 * (a : ℝ) ^ 2)
        have hSS : ∀ N ∈ S, 2 ≤ N := fun N hmem ↦
          hS N (Finset.mem_insert_of_mem hmem)
        simpa [Finset.sum_insert, ha] using hSa.add (ih hSS)
  exact hsum (ehmDyadicNBlock X) fun N hNmem ↦
    hX.trans (Finset.mem_Icc.mp hNmem).1

/-- Reindex the finite dyadic tail mass with the divisor variable outside. -/
theorem ehmDyadicCommonDivisorTailMass_eq_divisorSum
    (X D J : ℕ) :
    ehmDyadicCommonDivisorTailMass X D J =
      ∑ d ∈ Finset.Icc (D + 1) J,
        ∑ N ∈ ehmDyadicNBlock X,
          16 * (N : ℝ) ^ 2 *
            (|dirichletCoeff N d| / (d : ℝ) ^ 2) := by
  unfold ehmDyadicCommonDivisorTailMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem exists_uniform_finite_tail_lt
    (f : ℕ → ℝ) (hf : Summable f) (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ J : ℕ, D ≤ J →
      (∑ d ∈ Finset.Icc (D + 1) J, f d) < ε := by
  rw [summable_iff_vanishing] at hf
  rcases hf (Set.Iio ε) (Iio_mem_nhds hε) with ⟨s, hs⟩
  refine ⟨s.sup id, ?_⟩
  intro D hD J _hDJ
  have hdis : Disjoint (Finset.Icc (D + 1) J) s := by
    apply Finset.disjoint_left.mpr
    intro d hdI hdS
    have hdle : d ≤ s.sup id := Finset.le_sup (f := id) hdS
    have hdlo := (Finset.mem_Icc.mp hdI).1
    omega
  exact hs (Finset.Icc (D + 1) J) hdis

/-- For every dyadic block and every positive tolerance, one common cutoff
makes the explicit far-tail mass uniformly small in all later hyperbolic
cutoffs. -/
theorem exists_commonCutoff_tailMass_lt
    (X : ℕ) (hX : 2 ≤ X) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ, 2 * X ≤ D ∧ ∀ J : ℕ, D ≤ J →
      ehmDyadicCommonDivisorTailMass X D J < ε := by
  let f : ℕ → ℝ := fun d ↦
    ∑ N ∈ ehmDyadicNBlock X,
      16 * (N : ℝ) ^ 2 *
        (|dirichletCoeff N d| / (d : ℝ) ^ 2)
  have hf : Summable f := summable_ehmDyadicDivisorTailSeries X hX
  rcases exists_uniform_finite_tail_lt f hf ε hε with ⟨D₀, hD₀⟩
  refine ⟨max (2 * X) D₀, le_max_left _ _, ?_⟩
  intro J hJ
  rw [ehmDyadicCommonDivisorTailMass_eq_divisorSum]
  exact hD₀ (max (2 * X) D₀) (le_max_right _ _) J hJ

/-! ## A proved uniform far-tail package -/

/-- Uniform dyadic vanishing data for the positive far-tail mass. -/
structure EhmDyadicUniformFarTailVanishing where
  D : ℕ → ℕ
  D_ge : ∀ X, 2 * X ≤ D X
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  uniform_bound : ∀ X : ℕ, 2 ≤ X → ∀ J : ℕ, D X ≤ J →
    ehmDyadicCommonDivisorTailMass X (D X) J ≤
      ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- The explicit positive far-tail problem is unconditionally solved with
majorant `1/(X+1)`. -/
noncomputable def ehmDyadicUniformFarTailVanishing :
    EhmDyadicUniformFarTailVanishing := by
  let eta : ℕ → ℝ := fun X ↦ 1 / ((X : ℝ) + 1)
  have heta_pos : ∀ X, 0 < eta X := fun X ↦ by
    unfold eta
    positivity
  have hchoice : ∀ X : ℕ, 2 ≤ X →
      ∃ D : ℕ, 2 * X ≤ D ∧ ∀ J : ℕ, D ≤ J →
        ehmDyadicCommonDivisorTailMass X D J < eta X :=
    fun X hX ↦ exists_commonCutoff_tailMass_lt X hX (eta X) (heta_pos X)
  let D : ℕ → ℕ := fun X ↦ if hX : 2 ≤ X then
    Classical.choose (hchoice X hX) else 2 * X
  refine
    { D := D
      D_ge := ?_
      eta := eta
      eta_nonneg := fun X ↦ (heta_pos X).le
      eta_tendsto_zero := ?_
      uniform_bound := ?_ }
  · intro X
    by_cases hX : 2 ≤ X
    · simp only [D, dif_pos hX]
      exact (Classical.choose_spec (hchoice X hX)).1
    · simp [D, hX]
  · simpa [eta, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro X hX J hDJ
    have hspec := (Classical.choose_spec (hchoice X hX)).2 J
    have hD : D X = Classical.choose (hchoice X hX) := by
      simp [D, hX]
    have htail : ehmDyadicCommonDivisorTailMass X (D X) J < eta X := by
      rw [hD]
      exact hspec (by simpa [hD] using hDJ)
    have hcard : (1 : ℝ) ≤ ((ehmDyadicNBlock X).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (ehmDyadicNBlock_nonempty X)
    calc
      ehmDyadicCommonDivisorTailMass X (D X) J ≤ eta X := htail.le
      _ ≤ ((ehmDyadicNBlock X).card : ℝ) * eta X := by
        nlinarith [heta_pos X]

/-! ## The sole remaining signed near-core target -/

/-- With the proved common far cutoff frozen, this is the remaining signed
analytic hypothesis. -/
structure EhmDyadicCommonNearCoreSignedAverageVanishing where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmDyadicUniformFarTailVanishing.D X ≤ J ∧
      ehmDyadicCommonNearCoreSum ehmR1 X
          (ehmDyadicUniformFarTailVanishing.D X) J ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- Combining the sole remaining signed near-core estimate with the proved
far-tail package gives the common-split closure package. -/
noncomputable def EhmDyadicCommonNearCoreSignedAverageVanishing.toCommonSplit
    (H : EhmDyadicCommonNearCoreSignedAverageVanishing) :
    EhmDyadicCommonSplitSignedAverageVanishing where
  D := ehmDyadicUniformFarTailVanishing.D
  D_ge := ehmDyadicUniformFarTailVanishing.D_ge
  etaNear := H.eta
  etaNear_nonneg := H.eta_nonneg
  etaNear_tendsto_zero := H.eta_tendsto_zero
  etaFar := ehmDyadicUniformFarTailVanishing.eta
  etaFar_nonneg := ehmDyadicUniformFarTailVanishing.eta_nonneg
  etaFar_tendsto_zero := ehmDyadicUniformFarTailVanishing.eta_tendsto_zero
  near_cofinal_bound := H.cofinal_bound
  far_uniform_bound := ehmDyadicUniformFarTailVanishing.uniform_bound

/-- The signed common near-core estimate is now the only new analytic input
needed by this route to close the Báez--Duarte criterion. -/
theorem baezDuarteCriterion_of_ehmDyadicCommonNearCoreSignedAverage
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicCommonNearCoreSignedAverageVanishing) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicCommonSplitSignedAverage HS
    H.toCommonSplit

end RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicFarTail
