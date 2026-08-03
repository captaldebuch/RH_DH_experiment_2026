import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptotic

/-!
# Route C: extraction of the Bettin--Conrey oscillatory asymptotic

Theorem 2 of Bettin--Conrey, *A reciprocity formula for a cotangent sum*,
IMRN 2013 (24), proves

`g_m - 1/m ~ 2^(5/4) * pi^(3/4) * m^(-3/4) * exp(-2*sqrt(pi*m)) *
  sin(2*sqrt(pi*m) + 3*pi/8)`.

Here `g_m` is the coefficient represented in this development by
`bettinConreyCentralTaylorCoefficient m`.  This is not the more general
coefficient family whose polynomial factor is `m^(-1/4)`.

This file records the paper's literal oscillatory statement and proves, with
no analytic assumption beyond that statement, that it supplies the eventual
positive envelope consumed by Route C.  Thus the only missing classical work
after this file is the source proof of the oscillatory asymptotic itself:
Mellin--Barnes convolution, the order-one Bessel-kernel estimate, and the
saddle integral in Lemma 3 of the paper.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptoticExtraction

open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptotic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTransformTail

/-- The positive leading amplitude `2^(5/4) * pi^(3/4)` in the source
coefficient asymptotic. -/
noncomputable def bettinConreyCentralSourceAmplitude : ℝ :=
  Real.rpow 2 (5 / 4 : ℝ) * Real.rpow Real.pi (3 / 4 : ℝ)

theorem bettinConreyCentralSourceAmplitude_pos :
    0 < bettinConreyCentralSourceAmplitude := by
  unfold bettinConreyCentralSourceAmplitude
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos Real.pi_pos _)

theorem bettinConreyCentralSourceAmplitude_nonneg :
    0 ≤ bettinConreyCentralSourceAmplitude :=
  bettinConreyCentralSourceAmplitude_pos.le

/-- The oscillatory phase `2*sqrt(pi*m) + 3*pi/8` in the source theorem. -/
noncomputable def bettinConreyCentralSourcePhase (m : ℕ) : ℝ :=
  2 * Real.sqrt (Real.pi * (m : ℝ)) + 3 * Real.pi / 8

/-- A faithful, proposition-valued form of Bettin--Conrey's coefficient
asymptotic.  The error is relative to the root-exponential majorant and tends
to zero.  No inhabitant is postulated in this file. -/
structure BettinConreyCentralCoefficientOscillatoryAsymptotic where
  error : ℕ → ℂ
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  eventually_eq : ∀ᶠ m : ℕ in atTop,
    bettinConreyCentralCenteredCoefficient m =
      ((bettinConreyCentralSourceAmplitude *
        bettinConreyCentralSourceMajorant m : ℝ) : ℂ) *
        ((Real.sin (bettinConreyCentralSourcePhase m) : ℂ) + error m)

private theorem eventually_norm_error_le_one
    (H : BettinConreyCentralCoefficientOscillatoryAsymptotic) :
    ∀ᶠ m : ℕ in atTop, ‖H.error m‖ ≤ 1 := by
  have hnorm : Tendsto (fun m => ‖H.error m‖) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp H.error_tendsto_zero
  exact hnorm.eventually_le_const zero_lt_one

private theorem norm_sin_add_error_le_two (x : ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ 1) :
    ‖(Real.sin x : ℂ) + z‖ ≤ 2 := by
  calc
    ‖(Real.sin x : ℂ) + z‖
        ≤ ‖(Real.sin x : ℂ)‖ + ‖z‖ := norm_add_le _ _
    _ = |Real.sin x| + ‖z‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one x) hz
    _ = 2 := by norm_num

/-- The exact oscillatory theorem implies the source envelope, with the sine
and vanishing relative error absorbed into twice the leading amplitude. -/
noncomputable def
    BettinConreyCentralCoefficientOscillatoryAsymptotic.toSourceBound
    (H : BettinConreyCentralCoefficientOscillatoryAsymptotic) :
    BettinConreyCentralCoefficientSourceAsymptoticBound where
  scale := 2 * bettinConreyCentralSourceAmplitude
  scale_nonneg := mul_nonneg (by norm_num)
    bettinConreyCentralSourceAmplitude_nonneg
  eventually_bound := by
    filter_upwards [H.eventually_eq, eventually_norm_error_le_one H]
      with m hm herr
    rw [hm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg bettinConreyCentralSourceAmplitude_nonneg
        (bettinConreyCentralSourceMajorant_nonneg m))]
    calc
      (bettinConreyCentralSourceAmplitude *
          bettinConreyCentralSourceMajorant m) *
          ‖(Real.sin (bettinConreyCentralSourcePhase m) : ℂ) + H.error m‖
          ≤ (bettinConreyCentralSourceAmplitude *
              bettinConreyCentralSourceMajorant m) * 2 :=
            mul_le_mul_of_nonneg_left
              (norm_sin_add_error_le_two _ _ herr)
              (mul_nonneg bettinConreyCentralSourceAmplitude_nonneg
                (bettinConreyCentralSourceMajorant_nonneg m))
      _ = (2 * bettinConreyCentralSourceAmplitude) *
            bettinConreyCentralSourceMajorant m := by ring

/-- The source oscillatory asymptotic therefore supplies the all-index decay
package used by the finite-prefix absorption and Route C assembly. -/
noncomputable def
    BettinConreyCentralCoefficientOscillatoryAsymptotic.toRootDecay
    (H : BettinConreyCentralCoefficientOscillatoryAsymptotic) :
    BettinConreyCentralCoefficientRootDecay :=
  H.toSourceBound.toRootDecay

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptoticExtraction
