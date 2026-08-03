import RiemannHypothesis.Criteria.NymanBeurling.H14ZetaFETransport

/-!
# A2: boundary identities for the functional-equation factor

The reflection-formula algebra and the two boundary moduli are unconditional.
The interior interpolation estimate is isolated in `FEFactorInteriorInterpolation`:
Mathlib does not currently expose the required vertical-strip Gamma estimate.
-/

namespace RH.Criteria.NymanBeurling.H14ZetaFETransport

open Complex MeasureTheory Set Filter Topology
open RH.Criteria.NymanBeurling.H14ZetaEM

/-- Reflection-formula inversion of the functional-equation factor off the real axis. -/
theorem zetaFEFactor_mul_complement {w : ℂ} (hw : w.im ≠ 0) :
    zetaFEFactor w * zetaFEFactor (1 - w) = 1 := by
  unfold zetaFEFactor
  have hsin : Complex.sin (Real.pi * w) ≠ 0 := by
    intro h
    rw [Complex.sin_eq_zero_iff] at h
    rcases h with ⟨n, hn⟩
    have him : w.im = 0 := by
      have h' := congrArg Complex.im hn
      simp at h'
      linarith
    exact hw him
  have hpow :
      (2 * (Real.pi : ℂ)) ^ (w - 1) *
          (2 * (Real.pi : ℂ)) ^ ((1 - w) - 1) =
        (2 * (Real.pi : ℂ))⁻¹ := by
    rw [← Complex.cpow_add]
    · rw [show w - 1 + ((1 - w) - 1) = -1 by ring]
      simp
      have hpi : (Real.pi : ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_pos.ne'
      rw [Complex.cpow_neg_one]
      field_simp [hpi]
    · norm_num
  have htrig :
      Complex.cos (Real.pi * (1 - w) / 2) *
          Complex.cos (Real.pi * (1 - (1 - w)) / 2) =
        Complex.sin (Real.pi * w) / 2 := by
    rw [show (1 - (1 - w) : ℂ) = w by ring]
    rw [show (Real.pi : ℂ) * (1 - w) / 2 =
        (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * w / 2 by ring]
    rw [Complex.cos_sub]
    rw [show Complex.cos ((Real.pi : ℂ) / 2) = 0 by
      have h : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h, ← Complex.ofReal_cos]
      norm_num,
      show Complex.sin ((Real.pi : ℂ) / 2) = 1 by
        have h : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
          push_cast
          ring
        rw [h, ← Complex.ofReal_sin]
        norm_num]
    rw [show (Real.pi : ℂ) * w = 2 * ((Real.pi : ℂ) * w / 2) by ring,
      Complex.sin_two_mul]
    ring
  rw [show (1 - w) - 1 = -w by ring]
  calc
    2 * (2 * (Real.pi : ℂ)) ^ (w - 1) * Complex.Gamma (1 - w) *
          Complex.cos ((Real.pi : ℂ) * (1 - w) / 2) *
        (2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma (1 - (1 - w)) *
          Complex.cos ((Real.pi : ℂ) * (1 - (1 - w)) / 2)) =
      4 * ((2 * (Real.pi : ℂ)) ^ (w - 1) *
          (2 * (Real.pi : ℂ)) ^ ((1 - w) - 1)) *
        (Complex.Gamma (1 - w) * Complex.Gamma w) *
        (Complex.cos ((Real.pi : ℂ) * (1 - w) / 2) *
          Complex.cos ((Real.pi : ℂ) * w / 2)) := by ring
    _ = 4 * (2 * (Real.pi : ℂ))⁻¹ *
        (Complex.Gamma (1 - w) * Complex.Gamma w) *
        (Complex.sin ((Real.pi : ℂ) * w) / 2) := by
      have htrig' :
          Complex.cos ((Real.pi : ℂ) * (1 - w) / 2) *
              Complex.cos ((Real.pi : ℂ) * w / 2) =
            Complex.sin ((Real.pi : ℂ) * w) / 2 := by
        simpa only [show (1 - (1 - w) : ℂ) = w by ring] using htrig
      rw [hpow, htrig']
    _ = 1 := by
      rw [show Complex.Gamma (1 - w) * Complex.Gamma w =
          (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w) by
        rw [mul_comm, Complex.Gamma_mul_Gamma_one_sub]]
      field_simp [hsin]
      ring

/-- Conjugation symmetry of the factor (the base `2π` is positive real). -/
theorem zetaFEFactor_conj (w : ℂ) :
    zetaFEFactor ((starRingEnd ℂ) w) = (starRingEnd ℂ) (zetaFEFactor w) := by
  unfold zetaFEFactor
  have hbase : (starRingEnd ℂ) (2 * (Real.pi : ℂ)) = 2 * (Real.pi : ℂ) := by
    rw [map_mul, Complex.conj_ofReal, map_ofNat]
  have harg : (starRingEnd ℂ) (w - 1) = (starRingEnd ℂ) w - 1 := by
    rw [map_sub, map_one]
  have hpow :
      (2 * (Real.pi : ℂ)) ^ ((starRingEnd ℂ) w - 1) =
        (starRingEnd ℂ) ((2 * (Real.pi : ℂ)) ^ (w - 1)) := by
    rw [← harg, Complex.cpow_conj]
    · rw [hbase]
    · have hp : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hp, Complex.arg_ofReal_of_nonneg (by positivity)]
      positivity
  have hgamma : Complex.Gamma (1 - (starRingEnd ℂ) w) =
      (starRingEnd ℂ) (Complex.Gamma (1 - w)) := by
    have h : (1 : ℂ) - (starRingEnd ℂ) w =
        (starRingEnd ℂ) (1 - w) := by rw [map_sub, map_one]
    rw [h, Complex.Gamma_conj]
  have hcos : Complex.cos ((Real.pi : ℂ) *
      (1 - (starRingEnd ℂ) w) / 2) =
      (starRingEnd ℂ) (Complex.cos ((Real.pi : ℂ) * (1 - w) / 2)) := by
    have h : (1 : ℂ) - (starRingEnd ℂ) w =
        (starRingEnd ℂ) (1 - w) := by rw [map_sub, map_one]
    rw [h]
    rw [← Complex.cos_conj]
    congr 1
    rw [show (Real.pi : ℂ) * (1 - w) / 2 =
        ((Real.pi : ℂ) * (1 - w)) * (2 : ℂ)⁻¹ by ring]
    rw [map_mul (starRingEnd ℂ), map_inv₀ (starRingEnd ℂ),
      map_mul (starRingEnd ℂ), map_ofNat (starRingEnd ℂ) 2,
      Complex.conj_ofReal]
    apply Complex.ext <;> simp <;> ring
  rw [hpow, hgamma, hcos]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal]

/-- The factor is unimodular on the critical boundary line. -/
theorem zetaFEFactor_half_norm {t : ℝ} (ht : t ≠ 0) :
    ‖zetaFEFactor ((1 / 2 : ℝ) + Complex.I * t : ℂ)‖ = 1 := by
  let w : ℂ := (1 / 2 : ℝ) + Complex.I * t
  have him : w.im ≠ 0 := by
    change ((1 / 2 : ℝ) + Complex.I * t : ℂ).im ≠ 0
    rw [RH.Criteria.NymanBeurling.H14ZetaEM.im_sigma_add_I_mul]
    exact ht
  have hcomp : (1 : ℂ) - w = (starRingEnd ℂ) w := by
    dsimp [w]
    apply Complex.ext <;> simp <;> ring
  have hinv := zetaFEFactor_mul_complement him
  have hconj := zetaFEFactor_conj w
  rw [hcomp, hconj] at hinv
  have hsq : ‖zetaFEFactor w‖ ^ 2 = 1 := by
    have hn := congrArg norm hinv
    rw [norm_mul, norm_one, Complex.norm_conj] at hn
    nlinarith
  have hnorm : ‖zetaFEFactor w‖ = 1 := by
    nlinarith [norm_nonneg (zetaFEFactor w)]
  exact hnorm

lemma sin_pi_half_add_I_mul (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((1 / 2 : ℝ) + Complex.I * t)) =
      (Real.cosh (Real.pi * t) : ℂ) := by
  rw [show (Real.pi : ℂ) * ((1 / 2 : ℝ) + Complex.I * t) =
      (Real.pi / 2 : ℂ) + (Real.pi * t) * Complex.I by push_cast; ring]
  rw [Complex.sin_add_mul_I]
  rw [show Complex.sin ((Real.pi : ℂ) / 2) = 1 by
      have h : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h, ← Complex.ofReal_sin]
      norm_num,
    show Complex.cos ((Real.pi : ℂ) / 2) = 0 by
      have h : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h, ← Complex.ofReal_cos]
      norm_num]
  simp [Complex.ofReal_cosh]

lemma normSq_cos_three_half_sub_I_mul (t : ℝ) :
    Complex.normSq (Complex.cos ((Real.pi : ℂ) *
      ((3 / 2 : ℝ) - Complex.I * t) / 2)) = Real.cosh (Real.pi * t) / 2 := by
  rw [show (Real.pi : ℂ) * ((3 / 2 : ℝ) - Complex.I * t) / 2 =
      (3 * Real.pi / 4 : ℂ) + (-Real.pi * t / 2) * Complex.I by
        push_cast
        ring]
  rw [Complex.cos_add_mul_I]
  have harg : (3 * Real.pi / 4 : ℂ) = ((3 * Real.pi / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    show (-Real.pi * t / 2 : ℂ) = ((-Real.pi * t / 2 : ℝ) : ℂ) by
      push_cast
      ring,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rw [show ((Real.cos (3 * Real.pi / 4) * Real.cosh (-Real.pi * t / 2) : ℝ) : ℂ) -
        (Real.sin (3 * Real.pi / 4) * Real.sinh (-Real.pi * t / 2) : ℝ) * Complex.I =
      ((Real.cos (3 * Real.pi / 4) * Real.cosh (-Real.pi * t / 2) : ℝ) : ℂ) +
        (-Real.sin (3 * Real.pi / 4) * Real.sinh (-Real.pi * t / 2) : ℝ) * Complex.I by
      push_cast
      ring]
  rw [Complex.normSq_add_mul_I]
  rw [show (3 * Real.pi / 4 : ℝ) = Real.pi - Real.pi / 4 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_four, Real.sin_pi_sub,
    Real.sin_pi_div_four]
  have hneg : -Real.pi * t / 2 = -(Real.pi * t / 2) := by ring
  rw [hneg, Real.cosh_neg, Real.sinh_neg]
  rw [show Real.pi * t = 2 * (Real.pi * t / 2) by ring, Real.cosh_two_mul]
  ring_nf
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma normSq_gamma_half_add_I_mul (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℝ) + Complex.I * t)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  let a : ℂ := (1 / 2 : ℝ) + Complex.I * t
  have ha : (1 - a) = (starRingEnd ℂ) a := by
    dsimp [a]
    apply Complex.ext <;> simp <;> ring
  have hgamma := Complex.Gamma_mul_Gamma_one_sub a
  rw [ha, Complex.Gamma_conj] at hgamma
  have hsin : Complex.sin (Real.pi * a) = (Real.cosh (Real.pi * t) : ℂ) := by
    exact sin_pi_half_add_I_mul t
  rw [hsin] at hgamma
  have hnorm : (‖Complex.Gamma a‖ ^ 2 : ℂ) =
      (starRingEnd ℂ) (Complex.Gamma a) * Complex.Gamma a := by
    calc
      (‖Complex.Gamma a‖ ^ 2 : ℂ) =
          (Complex.normSq (Complex.Gamma a) : ℂ) := by
            exact_mod_cast (Complex.normSq_eq_norm_sq (Complex.Gamma a)).symm
      _ = (starRingEnd ℂ) (Complex.Gamma a) * Complex.Gamma a :=
        Complex.normSq_eq_conj_mul_self
  have hnorm' : ‖Complex.Gamma a‖ ^ 2 =
      (Complex.Gamma a).re * (Complex.Gamma a).re +
        (Complex.Gamma a).im * (Complex.Gamma a).im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hgamma_norm : (‖Complex.Gamma a‖ ^ 2 : ℂ) =
      (Real.pi : ℂ) / (Real.cosh (Real.pi * t) : ℂ) := by
    rw [hnorm]
    calc
      (starRingEnd ℂ) (Complex.Gamma a) * Complex.Gamma a =
          Complex.Gamma a * (starRingEnd ℂ) (Complex.Gamma a) := by ring
      _ = (Real.pi : ℂ) / (Real.cosh (Real.pi * t) : ℂ) := hgamma
  have hgamma' : ‖Complex.Gamma a‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
    exact_mod_cast hgamma_norm
  simpa [a] using hgamma'

/-- Exact modulus on the left boundary `Re w = -1/2`. -/
theorem zetaFEFactor_minus_half_norm {t : ℝ} (ht : t ≠ 0) :
    ‖zetaFEFactor (-(1 / 2 : ℝ) + Complex.I * t : ℂ)‖ =
      ‖(1 / 2 : ℝ) - Complex.I * t‖ / (2 * Real.pi) := by
  let w : ℂ := -(1 / 2 : ℝ) + Complex.I * t
  have hbase : 0 < (2 * Real.pi : ℝ) := by positivity
  have hgamma_add :
      ‖Complex.Gamma ((3 / 2 : ℝ) - Complex.I * t)‖ ^ 2 =
        ((1 / 2 : ℝ) ^ 2 + t ^ 2) *
          (Real.pi / Real.cosh (Real.pi * (-t))) := by
    have hz : ((1 / 2 : ℝ) - Complex.I * t : ℂ) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact ht (by linarith)
    have hg := Complex.Gamma_add_one ((1 / 2 : ℝ) - Complex.I * t) hz
    have hn := normSq_gamma_half_add_I_mul (-t)
    have hn' :
        ‖Complex.Gamma ((1 / 2 : ℝ) - Complex.I * t)‖ ^ 2 =
          Real.pi / Real.cosh (Real.pi * (-t)) := by
      convert hn using 1 <;> push_cast <;> ring
    rw [show ((1 / 2 : ℝ) - Complex.I * t : ℂ) + 1 =
        (3 / 2 : ℝ) - Complex.I * t by push_cast; ring] at hg
    rw [hg, norm_mul, mul_pow]
    rw [show ‖((1 / 2 : ℝ) - Complex.I * t : ℂ)‖ ^ 2 =
        (1 / 2 : ℝ) ^ 2 + t ^ 2 by
      rw [Complex.sq_norm]
      rw [show ((1 / 2 : ℝ) - Complex.I * t : ℂ) =
          ((1 / 2 : ℝ) : ℂ) + (-t : ℝ) * Complex.I by push_cast; ring]
      rw [Complex.normSq_add_mul_I]
      ring]
    rw [hn']
  have hcos :
      ‖Complex.cos ((Real.pi : ℂ) *
          ((3 / 2 : ℝ) - Complex.I * t) / 2)‖ ^ 2 =
        Real.cosh (Real.pi * t) / 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normSq_cos_three_half_sub_I_mul t
  have hnorm :
      ‖zetaFEFactor w‖ ^ 2 =
        (2 * (2 * Real.pi) ^ (-(3 / 2 : ℝ))) ^ 2 *
          (((1 / 2 : ℝ) ^ 2 + t ^ 2) *
            (Real.pi / Real.cosh (Real.pi * (-t)))) *
          (Real.cosh (Real.pi * t) / 2) := by
    unfold zetaFEFactor w
    rw [norm_mul, norm_mul, norm_mul]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hbase_cast : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hbase_cast, norm_cpow_eq_rpow_re_of_pos (by positivity)]
    norm_num
    rw [show (1 : ℂ) - (-(1 / 2 : ℂ) + Complex.I * (t : ℂ)) =
        (3 / 2 : ℝ) - Complex.I * t by push_cast; ring]
    rw [mul_pow, mul_pow, mul_pow]
    have hgamma_add' := hgamma_add
    have hneg : Real.pi * (-t) = -(Real.pi * t) := by ring
    rw [hneg, Real.cosh_neg] at hgamma_add'
    rw [hgamma_add', hcos]
    congr 1
    ring
  have hnorm' :
      ‖zetaFEFactor w‖ ^ 2 =
        ‖(1 / 2 : ℝ) - Complex.I * t‖ ^ 2 / (2 * Real.pi) ^ 2 := by
    rw [hnorm]
    have hneg : Real.pi * (-t) = -(Real.pi * t) := by ring
    rw [hneg, Real.cosh_neg]
    rw [show ‖(1 / 2 : ℝ) - Complex.I * t‖ ^ 2 =
        (1 / 2 : ℝ) ^ 2 + t ^ 2 by
      rw [Complex.sq_norm]
      rw [show ((1 / 2 : ℝ) - Complex.I * t : ℂ) =
          ((1 / 2 : ℝ) : ℂ) + (-t : ℝ) * Complex.I by push_cast; ring]
      rw [Complex.normSq_add_mul_I]
      ring]
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp [hpi]
    have hpow2 : ((2 * Real.pi : ℝ) ^ (-(3 / 2 : ℝ))) ^ (2 : ℕ) =
        (2 * Real.pi : ℝ) ^ (-3 : ℝ) := by
      have h := Real.rpow_mul (show 0 ≤ (2 * Real.pi : ℝ) by positivity)
        (-(3 / 2 : ℝ)) (2 : ℝ)
      have h2 := Real.rpow_natCast ((2 * Real.pi : ℝ) ^ (-(3 / 2 : ℝ))) 2
      rw [← h2]
      convert h.symm using 1 <;> norm_num
    rw [hpow2, Real.rpow_neg (by positivity)]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
    rw [← Real.rpow_natCast]
    field_simp [hpi]
    norm_num [Real.rpow_natCast]
  have hrnonneg : 0 ≤ ‖(1 / 2 : ℝ) - Complex.I * t‖ / (2 * Real.pi) := by positivity
  have hsquare : ‖zetaFEFactor w‖ ^ 2 =
      (‖(1 / 2 : ℝ) - Complex.I * t‖ / (2 * Real.pi)) ^ 2 := by
    rw [hnorm']
    field_simp [ne_of_gt Real.pi_pos]
  nlinarith [norm_nonneg (zetaFEFactor w)]

/-!
The remaining interpolation is isolated without changing the target exponent
or quantifier range.  Supplying this structure is exactly the missing
Phragmén--Lindelöf/Gamma vertical estimate.
-/
structure FEFactorInteriorInterpolation where
  C : ℝ
  C_nonneg : 0 ≤ C
  interpolation_bound :
    ∀ {σ t : ℝ}, -(1 / 2 : ℝ) ≤ σ → σ ≤ (1 / 2 : ℝ) → 1 ≤ |t| →
      ‖zetaFEFactor (σ + Complex.I * t : ℂ)‖ ≤
        C * (|t| + 2) ^ ((1 / 2 : ℝ) - σ)

/-- Mechanical packaging of the isolated interior interpolation residual. -/
noncomputable def zetaFEFactorVerticalBound_of_interior
    (H : FEFactorInteriorInterpolation) : ZetaFEFactorVerticalBound :=
  { C := H.C
    C_nonneg := H.C_nonneg
    factor_bound := H.interpolation_bound }

end RH.Criteria.NymanBeurling.H14ZetaFETransport
