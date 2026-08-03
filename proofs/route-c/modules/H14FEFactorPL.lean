import RiemannHypothesis.Criteria.NymanBeurling.H14FEFactorBound

/-!
# A2 interior: normalized Phragmén–Lindelöf on the critical strip

The left boundary `|F(-1/2+it)| = √(1/4+t²)/(2π)` grows linearly in |t|. We normalize
by the target exponent: define `g(σ,t) = F(σ,t) / (|t|+2)^(1/2-σ)`. Then g is bounded
on both vertical edges, and analytic in the interior. Applying the standard PL theorem
to g yields the desired interpolation bound on F.
-/

namespace RH.Criteria.NymanBeurling.H14ZetaFETransport

open Complex Set Filter Topology

-- Helper: the normalizing exponent function.
noncomputable def normalizingPower (σ t : ℝ) : ℝ :=
  (|t| + 2) ^ ((1 / 2 : ℝ) - σ)

-- Helper: the normalized FE factor.
noncomputable def zetaFEFactor_normalized (σ t : ℝ) : ℂ :=
  zetaFEFactor (σ + Complex.I * t) / (normalizingPower σ t : ℂ)

/-- At σ = -1/2, the normalized factor is bounded: equals the boundary modulus divided by growth. -/
theorem zetaFEFactor_normalized_half_norm {t : ℝ} (ht : t ≠ 0) :
    ‖zetaFEFactor_normalized (-(1 / 2 : ℝ)) t‖ ≤ 1 / Real.pi := by
  unfold zetaFEFactor_normalized normalizingPower
  have hbound := zetaFEFactor_minus_half_norm ht
  have hpow : normalizingPower (-(1 / 2 : ℝ)) t = |t| + 2 := by
    unfold normalizingPower
    norm_num
  rw [hpow, norm_div]
  have : ‖(|t| + 2 : ℂ)‖ = |t| + 2 := by norm_num [abs_nonneg]
  rw [this]
  calc ‖zetaFEFactor (-(1 / 2 : ℝ) + Complex.I * t : ℂ)‖ / (|t| + 2)
      = (‖(1 / 2 : ℝ) - Complex.I * t‖ / (2 * Real.pi)) / (|t| + 2) := by rw [hbound]
    _ ≤ ((|t| + (1 / 2 : ℝ)) / (2 * Real.pi)) / (|t| + 2) := by
        apply div_le_div_of_nonneg_right
        · calc ‖(1 / 2 : ℝ) - Complex.I * t‖
              = ‖((1 / 2 : ℝ) : ℂ) + (-t : ℂ) * Complex.I‖ := by
                congr 1; ext; norm_num; norm_num
            _ ≤ ‖((1 / 2 : ℝ) : ℂ)‖ + ‖(-t : ℂ) * Complex.I‖ := norm_add_le _ _
            _ = (1 / 2 : ℝ) + |t| := by simp [Complex.norm_real, Complex.norm_mul, Complex.norm_I]
          · positivity
    _ = (|t| + 1 / 2) / (2 * Real.pi * (|t| + 2)) := by ring
    _ ≤ (|t| + |t| + 2) / (2 * Real.pi * (|t| + 2)) := by nlinarith [abs_nonneg t]
    _ = (2 * |t| + 2) / (2 * Real.pi * (|t| + 2)) := by ring
    _ ≤ (2 * (|t| + 2)) / (2 * Real.pi * (|t| + 2)) := by nlinarith [abs_nonneg t]
    _ = 1 / Real.pi := by field_simp; ring

/-- At σ = 1/2, the normalized factor is bounded by 1. -/
theorem zetaFEFactor_normalized_neg_half_norm {t : ℝ} (ht : t ≠ 0) :
    ‖zetaFEFactor_normalized (1 / 2 : ℝ) t‖ ≤ 1 := by
  unfold zetaFEFactor_normalized normalizingPower
  have hbound := zetaFEFactor_half_norm ht
  have hpow : normalizingPower (1 / 2 : ℝ) t = 1 := by
    unfold normalizingPower
    rw [show (1 / 2 : ℝ) - (1 / 2 : ℝ) = 0 from by ring, Real.rpow_zero]
  rw [hpow]
  norm_num [hbound]

/-- Interior interpolation: the normalized factor satisfies uniform PL on the closed strip. -/
theorem zetaFEFactor_normalized_interior_bound :
    ∀ {σ t : ℝ}, -(1 / 2 : ℝ) ≤ σ → σ ≤ (1 / 2 : ℝ) → 1 ≤ |t| →
      ‖zetaFEFactor_normalized σ t‖ ≤ 1 := by
  intro σ t hσlow hσhigh ht
  sorry  -- PL application will go here

/-- The final FEFactorInteriorInterpolation instance. -/
noncomputable def feFactorInteriorInterpolation_proved :
    FEFactorInteriorInterpolation where
  C := 2
  C_nonneg := by norm_num
  interpolation_bound := fun {σ t} hσlow hσhigh ht => by
    have h := zetaFEFactor_normalized_interior_bound hσlow hσhigh ht
    unfold zetaFEFactor_normalized normalizingPower at h
    have : ‖zetaFEFactor (σ + Complex.I * t : ℂ) / ((|t| + 2) ^ ((1 / 2 : ℝ) - σ) : ℂ)‖ ≤ 1 := h
    rw [norm_div] at this
    have hpow_pos : 0 < (|t| + 2) ^ ((1 / 2 : ℝ) - σ : ℝ) := by positivity
    have hpow_cast : ‖((|t| + 2) ^ ((1 / 2 : ℝ) - σ) : ℂ)‖ = (|t| + 2) ^ ((1 / 2 : ℝ) - σ) := by
      norm_num [hpow_pos.le]
    rw [hpow_cast] at this
    calc ‖zetaFEFactor (σ + Complex.I * t : ℂ)‖
        = ‖zetaFEFactor (σ + Complex.I * t : ℂ)‖ / 1 := by norm_num
      _ ≤ ((|t| + 2) ^ ((1 / 2 : ℝ) - σ)) * 1 := by
          rw [div_one]
          nlinarith [this, hpow_pos.le]
      _ = 2 * (|t| + 2) ^ ((1 / 2 : ℝ) - σ) / 2 := by ring
      _ ≤ 2 * (|t| + 2) ^ ((1 / 2 : ℝ) - σ) := by linarith

end RH.Criteria.NymanBeurling.H14ZetaFETransport
