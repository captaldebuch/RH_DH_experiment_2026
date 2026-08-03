import RiemannHypothesis.Criteria.NymanBeurling.QuadraticInteraction
import RiemannHypothesis.Criteria.NymanBeurling.H14ZetaFETransport

/-!
# H15 smooth component: separability and conditional factor bounds

The smooth term in the quadratic interaction is completely separable.  This
file records that algebra and the exact factor estimates needed to turn bounds
on the two one-variable sums into a bound for the smooth quadratic component.
The latter estimates are intentionally hypotheses: the available H14 decay
bound controls the inverse-index factor, but does not by itself provide a
uniform bound for the unweighted factor.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.CutoffMobiusKernels

/-- The smooth part of the two-variable kernel. -/
noncomputable def smoothPart (h k : ℕ) : ℝ :=
  (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
    (1 / (h : ℝ) + 1 / (k : ℝ))

theorem smooth_part_separable_decomposition (h k : ℕ) :
    smoothPart h k =
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
        (1 / (h : ℝ) + 1 / (k : ℝ)) := by
  rfl

/-- The smooth quadratic form is the sum of two rank-one products. -/
theorem smooth_quadratic_form_separable (N : ℕ) (c : ℕ → ℝ) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c h * c k * smoothPart h k) =
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
        ((∑ h ∈ Finset.Icc 1 N, c h / (h : ℝ)) *
            (∑ k ∈ Finset.Icc 1 N, c k) +
          (∑ h ∈ Finset.Icc 1 N, c h) *
            (∑ k ∈ Finset.Icc 1 N, c k / (k : ℝ))) := by
  classical
  let S := Finset.Icc 1 N
  let A := (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2
  change (∑ h ∈ S, ∑ k ∈ S, c h * c k * (A *
      (1 / (h : ℝ) + 1 / (k : ℝ)))) =
    A * ((∑ h ∈ S, c h / (h : ℝ)) * (∑ k ∈ S, c k) +
      (∑ h ∈ S, c h) * (∑ k ∈ S, c k / (k : ℝ)))
  rw [smooth_part_quadratic_sum_eq_linear_product N c]
  ring

/-- The usual logarithmic majorant for the finite harmonic sum.  This is the
same elementary estimate used in the Euler--Maclaurin part of H14. -/
theorem harmonic_sum_log_bound (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, 1 / (h : ℝ)) ≤
      1 + Real.log (N + 1 : ℝ) := by
  classical
  by_cases hN : N = 0
  · subst N
    simp
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hrewrite :
      (∑ h ∈ Finset.Icc 1 N, 1 / (h : ℝ)) =
        ∑ n ∈ Finset.range N, 1 / ((n + 1 : ℕ) : ℝ) := by
    apply Finset.sum_bij (fun n _ => n - 1)
    · intro n hn
      have hn' : 1 ≤ n ∧ n ≤ N := by simpa [Finset.mem_Icc] using hn
      simp only [Finset.mem_range]
      omega
    · intro a ha b hb hab
      have ha' : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hb' : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      omega
    · intro b hb
      simp only [Finset.mem_range] at hb
      refine ⟨b + 1, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        omega
      · simp
    · intro n hn
      have hn' : 1 ≤ n ∧ n ≤ N := by simpa [Finset.mem_Icc] using hn
      rw [Nat.sub_add_cancel hn'.1]
  rw [hrewrite]
  simpa [one_div] using
    RH.Criteria.NymanBeurling.H14ZetaFETransport.sum_range_inv_le N

/-- A coefficient-wise harmonic majorant.  This is the valid form of the
elementary truncation estimate; it does not discard the size of the second
finite sum. -/
theorem truncated_harmonic_bound (N : ℕ) (c : ℕ → ℝ) (A : ℝ)
    (hA : 0 ≤ A)
    (hc : ∀ h ∈ Finset.Icc 1 N, |c h| ≤ A) :
    (∑ h ∈ Finset.Icc 1 N, |c h| / (h : ℝ)) ≤
      A * (1 + Real.log (N + 1 : ℝ)) := by
  calc
    (∑ h ∈ Finset.Icc 1 N, |c h| / (h : ℝ)) ≤
        ∑ h ∈ Finset.Icc 1 N, A / (h : ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      apply div_le_div_of_nonneg_right (hc h hh)
      positivity
    _ = A * (∑ h ∈ Finset.Icc 1 N, 1 / (h : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ ≤ A * (1 + Real.log (N + 1 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (harmonic_sum_log_bound N) hA

/-- The correct unconditional coefficient-size estimate for the smooth form.
The factor `N` is explicit: a mere pointwise bound on the coefficients cannot
give the logarithmic saving requested by H15. -/
theorem smooth_quadratic_form_bound_of_coeff_bound
    (N : ℕ) (c : ℕ → ℝ) (A : ℝ)
    (hA : 0 ≤ A)
    (hc : ∀ h ∈ Finset.Icc 1 N, |c h| ≤ A) :
    |∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c h * c k * smoothPart h k| ≤
      |Real.log (2 * Real.pi) - Real.eulerMascheroniConstant| *
        (A ^ 2 * N * (1 + Real.log (N + 1 : ℝ))) := by
  let S := Finset.Icc 1 N
  let L := Real.log (2 * Real.pi) - Real.eulerMascheroniConstant
  let Ainv := ∑ h ∈ S, c h / (h : ℝ)
  let Aplain := ∑ h ∈ S, c h
  have hinv : |Ainv| ≤ A * (1 + Real.log (N + 1 : ℝ)) := by
    calc
      |Ainv| ≤ ∑ h ∈ S, |c h| / (h : ℝ) := by
        dsimp [Ainv]
        calc
          |∑ h ∈ S, c h / (h : ℝ)| ≤
              ∑ h ∈ S, |c h / (h : ℝ)| :=
            Finset.abs_sum_le_sum_abs (fun h : ℕ => c h / (h : ℝ)) S
          _ = ∑ h ∈ S, |c h| / (h : ℝ) := by
            apply Finset.sum_congr rfl
            intro h hh
            have hhpos : (0 : ℝ) < (h : ℝ) := by
              exact_mod_cast
                (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hh).1)
            rw [abs_div, abs_of_pos hhpos]
      _ ≤ A * (1 + Real.log (N + 1 : ℝ)) := by
        exact truncated_harmonic_bound N c A hA hc
  have hplain : |Aplain| ≤ A * N := by
    calc
      |Aplain| ≤ ∑ h ∈ S, |c h| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ S, A := by
        apply Finset.sum_le_sum
        intro h hh
        exact hc h hh
      _ = A * N := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp
        ring
  rw [smooth_quadratic_form_separable]
  calc
    |(Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 *
        (Ainv * Aplain + Aplain * Ainv)| ≤
        |(Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2| *
          (|Ainv * Aplain| + |Aplain * Ainv|) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ = |L| * (|Ainv| * |Aplain|) := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      simp only [abs_mul]
      ring
    _ ≤ |L| * ((A * (1 + Real.log (N + 1 : ℝ))) * (A * N)) := by
      have hlog : 0 ≤ Real.log (N + 1 : ℝ) := by
        exact Real.log_nonneg (by norm_cast; omega)
      have hleft : 0 ≤ A * (1 + Real.log (N + 1 : ℝ)) := by
        exact mul_nonneg hA (by linarith)
      have hright : 0 ≤ A * N := by positivity
      have hmul : |Ainv| * |Aplain| ≤
          (A * (1 + Real.log (N + 1 : ℝ))) * (A * N) := by
        exact mul_le_mul hinv hplain (abs_nonneg _) hleft
      exact mul_le_mul_of_nonneg_left hmul (abs_nonneg _)
    _ = |L| * (A ^ 2 * N * (1 + Real.log (N + 1 : ℝ))) := by ring

/-- A generic factor package for the smooth product.  The first field is the
inverse-index factor and the second is the unweighted factor. -/
structure ExplicitQuadraticSmoothComponentBound where
  C_inv : ℝ
  C_plain : ℝ
  C_inv_nonneg : 0 ≤ C_inv
  C_plain_nonneg : 0 ≤ C_plain
  inv_factor_bound : ∀ N : ℕ,
    |∑ h ∈ Finset.Icc 1 N, cutoffMobiusCoeff N h / (h : ℝ)| ≤
      C_inv / Real.log (N + 2 : ℝ) ^ 2
  plain_factor_bound : ∀ N : ℕ,
    |∑ h ∈ Finset.Icc 1 N, cutoffMobiusCoeff N h| ≤ C_plain

theorem explicitQuadraticLogGammaComponent_bound_of_factor_bounds
    (H : ExplicitQuadraticSmoothComponentBound) (N : ℕ) :
    |explicitQuadraticLogGammaComponent N| ≤
      |Real.log (2 * Real.pi) - Real.eulerMascheroniConstant| *
        (H.C_inv * H.C_plain) / Real.log (N + 2 : ℝ) ^ 2 := by
  rw [explicitQuadraticLogGammaComponent_eq_smooth_product]
  let L := Real.log (2 * Real.pi) - Real.eulerMascheroniConstant
  let A := ∑ h ∈ Finset.Icc 1 N, cutoffMobiusCoeff N h / (h : ℝ)
  let B := ∑ h ∈ Finset.Icc 1 N, cutoffMobiusCoeff N h
  have hA := H.inv_factor_bound N
  have hB := H.plain_factor_bound N
  have hlog : 0 ≤ Real.log (N + 2 : ℝ) := by
    exact Real.log_nonneg (by norm_cast; omega)
  have hden : 0 ≤ Real.log (N + 2 : ℝ) ^ 2 := sq_nonneg _
  have hboundA : 0 ≤ H.C_inv / Real.log (N + 2 : ℝ) ^ 2 :=
    div_nonneg H.C_inv_nonneg hden
  have hprod : |A * B| ≤
      (H.C_inv / Real.log (N + 2 : ℝ) ^ 2) * H.C_plain := by
    rw [abs_mul]
    exact mul_le_mul hA hB (abs_nonneg _) hboundA
  calc
    |L * A * B| = |L| * |A * B| := by
      simp only [abs_mul]
      ring
    _ ≤ |L| * ((H.C_inv / Real.log (N + 2 : ℝ) ^ 2) * H.C_plain) :=
      mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    _ = |L| * (H.C_inv * H.C_plain) /
        Real.log (N + 2 : ℝ) ^ 2 := by
      have hlogpos : 0 < Real.log (N + 2 : ℝ) := by
        apply Real.log_pos
        norm_cast
        omega
      field_simp [ne_of_gt hlogpos]

end RH.Criteria.NymanBeurling.QuadraticInteraction
