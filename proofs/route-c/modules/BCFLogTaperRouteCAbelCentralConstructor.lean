import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelBoundary
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCCentralOnlyAssembly

/-!
# Route C: central rational theorem from the Abel boundary

This module is the Phase 3 constructor for the central Abel programme.  It
keeps distinct the two boundary evaluations of the same coupled Lambert
period:

* the analytic value containing the literal `psi_0`;
* the finite value containing the rational cotangent finite part.

Uniqueness of limits then gives central reciprocity.  Separately, continuity
of `psi_0` transfers the upper-half-plane three-term relation to the positive
rational boundary.  No boundary evaluation is asserted without proof.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelCentralConstructor

open Complex Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelBoundary
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralOnlyAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPeriod
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero

/-- The finite-side value predicted for the coupled Abel period.  The sign
and factor are forced by

`finitePart = (i/2) psi_0`

and the corrected normalization

`period = (1 - x⁻¹ - psi_0) / 4`. -/
noncomputable def bettinConreyCentralFiniteAbelBoundaryValue
    (h k : ℕ) : ℂ :=
  let x : ℂ := (((h : ℝ) / (k : ℝ) : ℝ) : ℂ)
  (1 - x⁻¹ + 2 * I * (bettinConreyCentralFinitePartSide h k : ℂ)) / 4

/-- The second genuine Phase 2 boundary theorem: Abel summation of the
coupled divisor period produces the finite cotangent side.  This proposition
is deliberately separate from the analytic `psi_0` evaluation. -/
def BettinConreyCentralRationalFiniteAbelEvaluation : Prop :=
  ∀ h k : ℕ, 0 < h → 0 < k → Nat.Coprime h k →
    Tendsto (bettinConreyRationalDampedPeriod h k)
      (𝓝[>] (0 : ℝ))
      (𝓝 (bettinConreyCentralFiniteAbelBoundaryValue h k))

/-- The analytic and finite Abel evaluations of the same coupled period give
the exact central cotangent reciprocity value by uniqueness of limits. -/
theorem central_reciprocity_of_two_abel_boundaries
    (HA : BettinConreyCentralRationalAbelBoundary)
    (HF : BettinConreyCentralRationalFiniteAbelEvaluation)
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    (bettinConreyCentralFinitePartSide h k : ℂ) =
      I / 2 * bettinConreyPsiZero
        ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ)) := by
  have hEq := tendsto_nhds_unique
    (HF h k hh hk hcop) (HA h k hh hk hcop)
  unfold bettinConreyCentralFiniteAbelBoundaryValue
    bettinConreyCentralAbelBoundaryValue at hEq
  dsimp only at hEq
  have hlin :
      2 * I * (bettinConreyCentralFinitePartSide h k : ℂ) =
        -bettinConreyPsiZero ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ)) := by
    linear_combination 4 * hEq
  calc
    (bettinConreyCentralFinitePartSide h k : ℂ) =
        (-I / 2) *
          (2 * I * (bettinConreyCentralFinitePartSide h k : ℂ)) := by
            symm
            calc
              (-I / 2) *
                    (2 * I * (bettinConreyCentralFinitePartSide h k : ℂ)) =
                  ((-I) * I) *
                    (bettinConreyCentralFinitePartSide h k : ℂ) := by ring
              _ = (bettinConreyCentralFinitePartSide h k : ℂ) := by
                rw [neg_mul, Complex.I_mul_I]
                ring
    _ = (-I / 2) *
        (-bettinConreyPsiZero ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ))) := by
          rw [hlin]
    _ = I / 2 * bettinConreyPsiZero
        ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ)) := by ring

/-- A vertical approach transfers the upper-half-plane period relation to
every positive real boundary point once the literal `psi_0` is continuous
there and at its two transformed points. -/
theorem bettinConreyPsiZero_threeTerm_on_posReal
    (H : BettinConreyLambertPsiZeroIdentification)
    (hpsi : ∀ z : ℂ, 0 < z.re → ContinuousAt bettinConreyPsiZero z)
    (x : ℝ) (hx : 0 < x) :
    bettinConreyPsiZero (x : ℂ) -
        bettinConreyPsiZero ((x : ℂ) + 1) =
      (((x : ℂ) + 1)⁻¹) *
        bettinConreyPsiZero ((x : ℂ) / ((x : ℂ) + 1)) := by
  let path : ℝ → ℂ := fun δ ↦ (x : ℂ) + I * δ
  have hpath : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have hc : ContinuousAt path 0 := by
      dsimp [path]
      fun_prop
    simpa [path] using hc.tendsto.mono_left inf_le_left
  have hx1 : ((x : ℂ) + 1) ≠ 0 := by
    exact ne_of_apply_ne Complex.re (by norm_num; linarith)
  have hpath1 : Tendsto (fun δ ↦ path δ + 1)
      (𝓝[>] (0 : ℝ)) (𝓝 ((x : ℂ) + 1)) :=
    hpath.add_const 1
  have hratio : Tendsto (fun δ ↦ path δ / (path δ + 1))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((x : ℂ) / ((x : ℂ) + 1))) :=
    hpath.div hpath1 hx1
  have hinv : Tendsto (fun δ ↦ (path δ + 1)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (((x : ℂ) + 1)⁻¹)) :=
    hpath1.inv₀ hx1
  have hxRe : 0 < ((x : ℂ)).re := by simpa using hx
  have hx1Re : 0 < ((x : ℂ) + 1).re := by
    norm_num
    linarith
  have hratioVal :
      (x : ℂ) / ((x : ℂ) + 1) = ((x / (x + 1) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hratioRe : 0 < ((x : ℂ) / ((x : ℂ) + 1)).re := by
    rw [hratioVal]
    simpa only [ofReal_re] using div_pos hx (by linarith : 0 < x + 1)
  have hleft := ((hpsi _ hxRe).tendsto.comp hpath).sub
    ((hpsi _ hx1Re).tendsto.comp hpath1)
  have hright := hinv.mul ((hpsi _ hratioRe).tendsto.comp hratio)
  have heq :
      (fun δ : ℝ ↦
        bettinConreyPsiZero (path δ) -
          bettinConreyPsiZero (path δ + 1)) =ᶠ[𝓝[>] 0]
      (fun δ : ℝ ↦
        (path δ + 1)⁻¹ *
          bettinConreyPsiZero (path δ / (path δ + 1))) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    apply bettinConreyPsiZero_threeTerm_on_upperHalfPlane H
    dsimp [path]
    simpa using hδ
  exact tendsto_nhds_unique (hleft.congr' heq) hright

/-- Positive-rational specialization of the preceding boundary relation in
the exact arithmetic form consumed by Euclidean descent. -/
theorem bettinConreyPsiZero_rational_threeTerm_of_identification
    (H : BettinConreyLambertPsiZeroIdentification)
    (hpsi : ∀ z : ℂ, 0 < z.re → ContinuousAt bettinConreyPsiZero z)
    (h k : ℕ) (hk : 0 < k) (hkh : k < h) :
    bettinConreyPsiZero
          (((((h - k : ℕ) : ℝ) / (k : ℝ) : ℝ) : ℂ)) -
        bettinConreyPsiZero ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ)) =
      ((k : ℂ) / (h : ℂ)) *
        bettinConreyPsiZero
          (((((h - k : ℕ) : ℝ) / (h : ℝ) : ℝ) : ℂ)) := by
  have hsub : 0 < h - k := Nat.sub_pos_of_lt hkh
  have hbase := bettinConreyPsiZero_threeTerm_on_posReal H hpsi
    (((h - k : ℕ) : ℝ) / (k : ℝ)) (div_pos (by exact_mod_cast hsub) (by exact_mod_cast hk))
  have hh : 0 < h := Nat.zero_lt_of_lt hkh
  have hx1 :
      (((((h - k : ℕ) : ℝ) / (k : ℝ) : ℝ) : ℂ) + 1) =
        ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ)) := by
    push_cast
    rw [Nat.cast_sub hkh.le]
    field_simp [Nat.ne_of_gt hk]
    ring
  have hfactor :
      (((((h - k : ℕ) : ℝ) / (k : ℝ) : ℝ) : ℂ) + 1)⁻¹ =
        (k : ℂ) / (h : ℂ) := by
    rw [hx1]
    push_cast
    field_simp [Nat.ne_of_gt hk, Nat.ne_of_gt hh]
  have hratio :
      (((((h - k : ℕ) : ℝ) / (k : ℝ) : ℝ) : ℂ) /
          (((((h - k : ℕ) : ℝ) / (k : ℝ) : ℝ) : ℂ) + 1)) =
        (((((h - k : ℕ) : ℝ) / (h : ℝ) : ℝ) : ℂ)) := by
    rw [hx1]
    push_cast
    field_simp [Nat.ne_of_gt hk, Nat.ne_of_gt hh]
  rw [hfactor, hratio, hx1] at hbase
  exact hbase

/-- Minimal Phase 3 input bundle.  The identification and continuity fields
produce the analytic Abel evaluation; `finiteBoundary` is the independent
finite-cotangent evaluation of the same coupled limit. -/
structure BettinConreyCentralAbelConstructorData where
  finiteBoundary : BettinConreyCentralRationalFiniteAbelEvaluation
  identification : BettinConreyLambertPsiZeroIdentification
  psiContinuous : ∀ z : ℂ, 0 < z.re → ContinuousAt bettinConreyPsiZero z

/-- The analytic boundary field is not an additional hypothesis: it follows
from the corrected upper-half-plane identification by continuity. -/
theorem BettinConreyCentralAbelConstructorData.toAnalyticBoundary
    (D : BettinConreyCentralAbelConstructorData) :
    BettinConreyCentralRationalAbelBoundary :=
  centralRationalAbelBoundary_of_identification
    D.identification D.psiContinuous

/-- Phase 3 is mechanically complete once the genuine Phase 2 boundary data
exist: it constructs exactly the rational central theorem used downstream. -/
noncomputable def BettinConreyCentralAbelConstructorData.toCentralRationalTheorem
    (D : BettinConreyCentralAbelConstructorData) :
    BettinConreyPsiZeroCentralRationalTheorem where
  reciprocity := fun h k hh hk hcop ↦
    central_reciprocity_of_two_abel_boundaries
      D.toAnalyticBoundary D.finiteBoundary h k hh hk hcop
  threeTerm := fun h k hk hkh ↦
    bettinConreyPsiZero_rational_threeTerm_of_identification
      D.identification D.psiContinuous h k hk hkh

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelCentralConstructor
