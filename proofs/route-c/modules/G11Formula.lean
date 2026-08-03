import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Criteria.NymanBeurling.G11IntegralEvaluation
import RiemannHypothesis.Certificates.TranscendentalBounds

namespace RH.Criteria.NymanBeurling.VasyuninGram

open scoped MeasureTheory
open RH.Certificates.TranscendentalBounds

theorem G11_equals_integral_axiom :
  baezDuarteGramEntry 1 1 = G11Integral := by
  unfold baezDuarteGramEntry G11Integral
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  unfold G11OriginalIntegrand
  simp only [Nat.cast_one, one_mul]
  ring

theorem G11_formula_theorem :
  baezDuarteGramEntry 1 1 = Real.log (2 * Real.pi) - EulerGamma := by
  rw [G11_equals_integral_axiom, G11_integral_eval_theorem]

theorem G11_log_gamma_interval_theorem :
  (((6303 / 5000 : ℚ) : ℝ)
     ≤ Real.log (2 * Real.pi) - EulerGamma) ∧
  (Real.log (2 * Real.pi) - EulerGamma
     ≤ ((12607 / 10000 : ℚ) : ℝ)) := by
  have h_log := log_two_pi_interval_theorem
  have h_gamma : ((57721 / 100000 : ℚ) : ℝ) ≤ EulerGamma ∧ EulerGamma ≤ ((57722 / 100000 : ℚ) : ℝ) := euler_gamma_interval_theorem
  constructor
  · linarith [h_log.1, h_gamma.2]
  · linarith [h_log.2, h_gamma.1]

theorem G11_interval_axiom :
  (((6303 / 5000 : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 1) ∧
  (baezDuarteGramEntry 1 1 ≤ ((12607 / 10000 : ℚ) : ℝ)) := by
  rw [G11_formula_theorem]
  exact G11_log_gamma_interval_theorem

/-- The Vasyunin explicit formula at `h = k = 1` reduces to `log(2π) - γ`: the cotangent
    sum `cotangentSumVFormula 1 1` is an empty sum (`Finset.Ico 1 1 = ∅`), and the middle
    `(k - h)/(2hk) * log(h/k)` term vanishes since `k - h = 0`. -/
theorem vasyuninBEntryFormula_one_one :
    vasyuninBEntryFormula 1 1 = Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
  unfold vasyuninBEntryFormula cotangentSumVFormula
  norm_num

/-- Base case (`h = k = 1`) of the diagonal bridge field `vasyuninBEntry_diagonal`.

    IMPORTANT SCOPE NOTE: this is *not* a proof of the general structure field
    `vasyuninBEntry_diagonal : ∀ h : ℕ, baezDuarteGramEntry h h = vasyuninBEntry h h`,
    which is a universal statement over all `h`. This lemma only establishes the `h = 1`
    instance, by combining the already-proved `G11_formula_theorem` (that
    `baezDuarteGramEntry 1 1 = Real.log (2 * Real.pi) - EulerGamma`, where `EulerGamma` is
    Mathlib's `Real.eulerMascheroniConstant` under a local alias, defeq/`rfl`-equal) with the
    formula reduction `vasyuninBEntryFormula_one_one` above. The fully general diagonal case
    (arbitrary `h`) requires genuinely new integral-evaluation work generalizing
    `G11IntegralEvaluation.lean` beyond `h = k = 1`, and is intentionally out of scope here. -/
theorem vasyuninBEntry_diagonal_one :
    baezDuarteGramEntry 1 1 = vasyuninBEntry 1 1 := by
  rw [G11_formula_theorem, vasyuninBEntry_eq_formula, vasyuninBEntryFormula_one_one]
  rfl

theorem baez_duarte_diagonal_scaling (k : ℕ) (hk : 0 < k) :
    baezDuarteGramEntry k k = (1 / (k : ℝ)) * baezDuarteGramEntry 1 1 := by
  simp only [baezDuarteGramEntry]
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have h_kk : (∫ x in Set.Ioi (0 : ℝ), Int.fract (1 / ((k : ℝ) * x)) *
                  Int.fract (1 / ((k : ℝ) * x))) =
              ∫ x in Set.Ioi (0 : ℝ), Int.fract (1 / (x * (k : ℝ))) *
                  Int.fract (1 / (x * (k : ℝ))) := by
    congr 1; apply funext; intro x; ring_nf
  rw [h_kk]
  have h_comp := MeasureTheory.integral_comp_mul_right_Ioi
    (fun y => Int.fract (1 / y) * Int.fract (1 / y)) 0 hk_pos
  simp only [zero_mul] at h_comp
  rw [h_comp]
  simp only [smul_eq_mul, one_div, Nat.cast_one, one_mul]

theorem vasyuninBEntry_diagonal_scaling (k : ℕ) :
    vasyuninBEntry k k = (1 / (k : ℝ)) * vasyuninBEntry 1 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [vasyuninBEntry_eq_formula, vasyuninBEntry_eq_formula]
    unfold vasyuninBEntryFormula cotangentSumVFormula
    simp
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    have hkR_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
    rw [vasyuninBEntry_eq_formula k k]
    unfold vasyuninBEntryFormula
    have h_vanish : ((k : ℝ) - (k : ℝ)) = 0 := sub_self _
    have h_sum : cotangentSumVFormula k k = 0 := by
      unfold cotangentSumVFormula
      apply Finset.sum_eq_zero
      intro a _ha
      have : (((a * k : ℕ) : ℝ) / (k : ℝ)) = a := by
        push_cast
        exact mul_div_cancel_right₀ _ (ne_of_gt hkR_pos)
      rw [this, Int.fract_natCast, zero_mul]
    simp only [h_vanish, zero_div, zero_mul, sub_zero, h_sum, add_zero, mul_zero]
    rw [vasyuninBEntry_eq_formula 1 1, vasyuninBEntryFormula_one_one]
    ring

theorem vasyuninBEntry_diagonal_proof (h : ℕ) :
    baezDuarteGramEntry h h = vasyuninBEntry h h := by
  rcases eq_or_ne h 0 with rfl | hh
  · unfold baezDuarteGramEntry vasyuninBEntry vasyuninBEntryFormula cotangentSumVFormula
    simp
  · have hh_pos : 0 < h := Nat.pos_of_ne_zero hh
    rw [baez_duarte_diagonal_scaling h hh_pos, vasyuninBEntry_diagonal_scaling h]
    rw [vasyuninBEntry_diagonal_one]

end RH.Criteria.NymanBeurling.VasyuninGram
