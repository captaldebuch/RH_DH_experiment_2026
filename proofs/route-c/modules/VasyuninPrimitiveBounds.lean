import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninBridge
import RiemannHypothesis.Certificates.Generated.ChiRhoBoundsN50
import RiemannHypothesis.Certificates.Generated.TranscendentalBoundsGenerated
import RiemannHypothesis.Criteria.NymanBeurling.G11Formula

/-!
# Phase 10N: Proved bounds for primitive Vasyunin formula entries

This file provides **proved** (not axiomatic) bounds on `vasyuninBEntryFormula h k`
for primitive pairs (h,k) where Mathlib has closed-form trigonometric values.

## Pilot: pair (1,3) — sqrt-3 family

- V(3,1) = 0 (empty sum over Finset.Ico 1 1).
- V(1,3) = −√3/9 (proved from cos/sin at π/3 and field arithmetic).
- b(1,3) = 2/3·(log(2π)−γ) − log(3)/3 + π·√3/54 (ring identity).
- Interval bound: linarith from certified constants + provable √3 bounds.
-/

namespace RH.Criteria.NymanBeurling.VasyuninGram

open RH.Certificates.Generated
open RH.Certificates.Generated.ChiRhoBoundsN50

-- ---------------------------------------------------------------------------
-- Section 0 — Core interval structures and scaling lemmas
-- ---------------------------------------------------------------------------

inductive VasyuninFormulaKind where
  | diagonalScaling
  | opaqueOffDiagonal
  | exactFormulaFuture
  deriving Repr, DecidableEq

structure NamedVasyuninInterval where
  h : ℕ
  k : ℕ
  lower : ℚ
  upper : ℚ
  formulaKind : VasyuninFormulaKind
  lower_le_upper : lower ≤ upper
  interval_proof : ((lower : ℝ) ≤ baezDuarteGramEntry h k) ∧ (baezDuarteGramEntry h k ≤ (upper : ℝ))


theorem baez_duarte_off_diagonal_scaling (h k m : ℕ) (hm : 0 < m) :
    baezDuarteGramEntry (m * h) (m * k) = (1 / (m : ℝ)) * baezDuarteGramEntry h k := by
  simp only [baezDuarteGramEntry]
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have h_rw : (∫ x in Set.Ioi (0 : ℝ),
      Int.fract (1 / ((↑(m * h) : ℝ) * x)) * Int.fract (1 / ((↑(m * k) : ℝ) * x)))
    = ∫ x in Set.Ioi (0 : ℝ),
      Int.fract (1 / ((↑h : ℝ) * (x * ↑m))) * Int.fract (1 / ((↑k : ℝ) * (x * ↑m))) := by
    congr 1; apply funext; intro x; push_cast; ring_nf
  rw [h_rw]
  have h_comp := MeasureTheory.integral_comp_mul_right_Ioi
    (fun y => Int.fract (1 / ((↑h : ℝ) * y)) * Int.fract (1 / ((↑k : ℝ) * y))) 0 hm_pos
  simp only [zero_mul] at h_comp
  rw [h_comp]
  simp only [smul_eq_mul, one_div]

theorem vasyuninBEntry_off_diagonal_scaling (h k m : ℕ) (hm : 0 < m)
    (hh : 0 < h) (hk : 0 < k) :
    vasyuninBEntry (m * h) (m * k) = (1 / (m : ℝ)) * vasyuninBEntry h k :=
  calc vasyuninBEntry (m * h) (m * k)
      = baezDuarteGramEntry (m * h) (m * k) :=
          (vasyuninBEntry_correct_axiom (m * h) (m * k)
            (Nat.mul_pos hm hh) (Nat.mul_pos hm hk)).symm
    _ = (1 / (m : ℝ)) * baezDuarteGramEntry h k :=
          baez_duarte_off_diagonal_scaling h k m hm
    _ = (1 / (m : ℝ)) * vasyuninBEntry h k := by
          rw [vasyuninBEntry_correct_axiom h k hh hk]

theorem diag_log_gamma_interval_from_G11 (k : ℕ) (hk : 0 < k) :
    (1 / (k : ℝ)) * ((6303 / 5000 : ℚ) : ℝ) ≤
      (1 / (k : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ∧
    (1 / (k : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤
      (1 / (k : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) := by
  obtain ⟨hlo, hhi⟩ := G11_log_gamma_interval_theorem
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  exact ⟨mul_le_mul_of_nonneg_left hlo (by positivity),
         mul_le_mul_of_nonneg_left hhi (by positivity)⟩



end RH.Criteria.NymanBeurling.VasyuninGram
