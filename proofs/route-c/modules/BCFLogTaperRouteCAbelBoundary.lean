import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPeriod

/-!
# Route C: the rational Abel boundary

This module fixes the exact central normalization used in Bettin--Conrey's
proof of cotangent reciprocity.  For a reduced positive rational `h/k`, the
paper approaches the boundary along

`z_delta = (h/k) * (1 + i*delta)`, `delta > 0`.

The first result below identifies the corresponding divisor Lambert series
with the exponentially damped Estermann series constructed by the raw
Mellin theorem.  The period is kept coupled: neither of its two Lambert rows
has a finite undamped boundary value by itself.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelBoundary

open Complex Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPeriod
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero

/-- The non-tangential rational boundary path used in the proof of
Bettin--Conrey Theorem 4. -/
noncomputable def bettinConreyRationalDampedPoint
    (h k : ℕ) (δ : ℝ) : ℂ :=
  (((h : ℝ) / (k : ℝ) : ℝ) : ℂ) * (1 + Complex.I * δ)

/-- The real exponential damping parameter on the first Lambert row. -/
noncomputable def bettinConreyRationalDamping
    (h k : ℕ) (δ : ℝ) : ℝ :=
  2 * Real.pi * ((h : ℝ) / (k : ℝ)) * δ

theorem bettinConreyRationalDamping_pos
    (h k : ℕ) {δ : ℝ} (hh : 0 < h) (hk : 0 < k) (hδ : 0 < δ) :
    0 < bettinConreyRationalDamping h k δ := by
  unfold bettinConreyRationalDamping
  positivity

theorem bettinConreyRationalDampedPoint_im
    (h k : ℕ) (δ : ℝ) :
    (bettinConreyRationalDampedPoint h k δ).im =
      ((h : ℝ) / (k : ℝ)) * δ := by
  unfold bettinConreyRationalDampedPoint
  norm_num

theorem bettinConreyRationalDampedPoint_im_pos
    (h k : ℕ) {δ : ℝ} (hh : 0 < h) (hk : 0 < k) (hδ : 0 < δ) :
    0 < (bettinConreyRationalDampedPoint h k δ).im := by
  rw [bettinConreyRationalDampedPoint_im]
  positivity

/-- The damped path tends to its positive rational boundary point. -/
theorem tendsto_bettinConreyRationalDampedPoint_zero
    (h k : ℕ) :
    Tendsto (bettinConreyRationalDampedPoint h k)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ))) := by
  have hcont : ContinuousAt
      (bettinConreyRationalDampedPoint h k) 0 := by
    unfold bettinConreyRationalDampedPoint
    fun_prop
  simpa [bettinConreyRationalDampedPoint] using
    hcont.tendsto.mono_left inf_le_left

/-- One positive-frequency term on the rational boundary path is the
Estermann additive character times the expected real exponential damping. -/
theorem centralLambertTerm_rationalDampedPoint
    (h k n : ℕ) (δ : ℝ) (hk : 0 < k) :
    (((n + 1).divisors.card : ℕ) : ℂ) *
        Complex.exp
          ((2 * Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) *
            bettinConreyRationalDampedPoint h k δ) =
      LSeries.term (estermannCoeff h k) 0 (n + 1) *
        Real.exp (-(bettinConreyRationalDamping h k δ * (n + 1))) := by
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
  simp only [Complex.cpow_zero, div_one, estermannCoeff,
    estermannDivisorCoeff_apply]
  have hexponent :
      (2 * Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) *
          bettinConreyRationalDampedPoint h k δ =
        ((((2 * Real.pi * (h : ℝ) / (k : ℝ) *
            ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) +
          ((-(bettinConreyRationalDamping h k δ * (n + 1)) : ℝ) : ℂ)) := by
    unfold bettinConreyRationalDampedPoint bettinConreyRationalDamping
    push_cast
    field_simp [Nat.ne_of_gt hk]
    calc
      Complex.I * (h : ℂ) * (1 + Complex.I * (δ : ℂ)) =
          Complex.I * (h : ℂ) + (Complex.I * Complex.I) * (h : ℂ) * (δ : ℂ) := by
            ring
      _ = (h : ℂ) * (Complex.I + -(δ : ℂ)) := by
            rw [Complex.I_mul_I]
            ring
  rw [hexponent, Complex.exp_add, ← Complex.ofReal_exp]
  unfold estermannAdditivePhase
  ring

/-- Phase 1's damped Estermann series is literally the divisor Lambert
series evaluated on Bettin--Conrey's rational boundary path. -/
theorem centralLambertSeries_rationalDampedPoint
    (h k : ℕ) {δ : ℝ} (hh : 0 < h) (hk : 0 < k) (hδ : 0 < δ) :
    bettinConreyCentralLambertSeries
        (bettinConreyRationalDampedPoint h k δ) =
      dampedEstermannLambertSeries h k
        (bettinConreyRationalDamping h k δ) := by
  have hdamp := bettinConreyRationalDamping_pos h k hh hk hδ
  have hs := summable_dampedEstermannLambertSeries h k hdamp
  unfold dampedEstermannLambertSeries
  rw [hs.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_mul, zero_add]
  unfold bettinConreyCentralLambertSeries
  apply tsum_congr
  intro n
  simpa only [Nat.cast_add, Nat.cast_one] using
    centralLambertTerm_rationalDampedPoint h k n δ hk

/-- The exact coupled Abel period.  Keeping the two rows together is
essential: their singular main terms cancel only in this expression. -/
noncomputable def bettinConreyRationalDampedPeriod
    (h k : ℕ) (δ : ℝ) : ℂ :=
  bettinConreyCentralLambertPeriod
    (bettinConreyRationalDampedPoint h k δ)

/-- The corrected central boundary value dictated by the Eisenstein
normalization `E_1 = 1 - 4*S_0`. -/
noncomputable def bettinConreyCentralAbelBoundaryValue
    (h k : ℕ) : ℂ :=
  let x : ℂ := (((h : ℝ) / (k : ℝ) : ℝ) : ℂ)
  (1 - x⁻¹ - bettinConreyPsiZero x) / 4

/-- Phase 2's genuine analytic target.  This is a coupled limit; it does not
assert convergence of either Lambert row separately. -/
def BettinConreyCentralRationalAbelBoundary : Prop :=
  ∀ h k : ℕ, 0 < h → 0 < k → Nat.Coprime h k →
    Tendsto (bettinConreyRationalDampedPeriod h k)
      (𝓝[>] (0 : ℝ))
      (𝓝 (bettinConreyCentralAbelBoundaryValue h k))

/-- On the upper half-plane, the corrected Lambert/`psi_0` identification
already gives the Phase 2 Abel boundary once the literal `psi_0` is known to
be continuous at the positive rational point. -/
theorem centralRationalAbelBoundary_of_identification
    (H : BettinConreyLambertPsiZeroIdentification)
    (hpsi : ∀ x : ℂ, 0 < x.re → ContinuousAt bettinConreyPsiZero x) :
    BettinConreyCentralRationalAbelBoundary := by
  intro h k hh hk hcop
  let x : ℂ := (((h : ℝ) / (k : ℝ) : ℝ) : ℂ)
  have hxre : 0 < x.re := by
    dsimp [x]
    positivity
  have hpoint := tendsto_bettinConreyRationalDampedPoint_zero h k
  have hpsiLimit := (hpsi x hxre).tendsto.comp hpoint
  have hinvLimit : Tendsto
      (fun δ : ℝ ↦ (bettinConreyRationalDampedPoint h k δ)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 x⁻¹) := by
    exact (continuousAt_inv₀ (by
      dsimp [x]
      exact Complex.ofReal_ne_zero.mpr (div_ne_zero
        (by exact_mod_cast hh.ne') (by exact_mod_cast hk.ne')))).tendsto.comp hpoint
  have hformula :
      (fun δ : ℝ ↦ bettinConreyRationalDampedPeriod h k δ) =ᶠ[𝓝[>] 0]
        (fun δ : ℝ ↦
          (1 - (bettinConreyRationalDampedPoint h k δ)⁻¹ -
            bettinConreyPsiZero (bettinConreyRationalDampedPoint h k δ)) / 4) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact H.eq_on_upperHalfPlane _
      (bettinConreyRationalDampedPoint_im_pos h k hh hk hδ)
  apply Tendsto.congr' hformula.symm
  unfold bettinConreyCentralAbelBoundaryValue
  dsimp only [x]
  exact ((tendsto_const_nhds.sub hinvLimit).sub hpsiLimit).div_const 4

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelBoundary
