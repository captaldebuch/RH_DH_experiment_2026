import Mathlib.NumberTheory.Bernoulli
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCThreeTermDefect

/-!
# Route C: the source central Taylor row

Bettin--Conrey give the exact expansion

`(pi*i/2) * (1+z) * psi_0(1+z) = -1-z/2 + sum_{m>=2} a_m*(-z)^m`

on `|z| < 1`, with an explicit Bernoulli--zeta formula for `a_m` and
root-exponential decay of `a_m - 1/m`.  Since the source-normalized central
period side is `(i/2) * psi_0`, the harmonic `1/m` row must be retained in the
completed term; only the centered coefficient row is absolutely summable.

This module formalizes that separation.  The source theorem is represented
in its literal period-function normalization, and an axiom-free constructor
turns it into the finite-row package used downstream.  No cited statement is
silently promoted to an axiom.  From such data Lean proves the logarithmic
resummation, local absolute summability, and the complete handoff to the
existing Euclidean descent and adaptive H15 stop test.

Reference: S. Bettin and B. Conrey, *Period functions and cotangent sums*,
Algebra & Number Theory 7 (2013), pp. 7--8, Theorem 2 and the displayed
`a_m` formula preceding it.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAdaptiveTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCThreeTermDefect
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTransformTail

/-- The auxiliary coefficient `b_n = zeta(n) B_n / n` used by
Bettin--Conrey. -/
noncomputable def bettinConreyCentralTaylorB (n : ℕ) : ℂ :=
  riemannZeta (n : ℂ) * (((bernoulli n : ℚ) : ℂ)) / (n : ℂ)

/-- Bettin--Conrey's exact central Taylor coefficient `a_m`.  The formula is
used only for `m >= 2`; totalization at the smaller indices is harmless. -/
noncomputable def bettinConreyCentralTaylorCoefficient (m : ℕ) : ℂ :=
  1 / ((m : ℂ) * ((m + 1 : ℕ) : ℂ)) +
    2 * bettinConreyCentralTaylorB m +
    2 * ∑ j ∈ Finset.range (m - 1),
      ((Nat.choose (m - 1) j : ℕ) : ℂ) *
        bettinConreyCentralTaylorB (j + 2)

/-- The genuinely decaying part of the Taylor coefficient. -/
noncomputable def bettinConreyCentralCenteredCoefficient (m : ℕ) : ℂ :=
  bettinConreyCentralTaylorCoefficient m - 1 / (m : ℂ)

/-- The positive rational argument `x = h/k`. -/
noncomputable def routeCUnitIntervalRatio (h k : ℕ) : ℝ :=
  (h : ℝ) / (k : ℝ)

/-- The Taylor variable `y = 1-x = -(x-1)`. -/
noncomputable def routeCUnitIntervalTaylorVariable (h k : ℕ) : ℝ :=
  1 - routeCUnitIntervalRatio h k

/-- The raw `a_{n+2} y^{n+2}` Taylor row. -/
noncomputable def routeCCentralTaylorRawMode (h k n : ℕ) : ℂ :=
  bettinConreyCentralTaylorCoefficient (n + 2) *
    (routeCUnitIntervalTaylorVariable h k : ℂ) ^ (n + 2)

/-- The centered `(a_{n+2}-1/(n+2)) y^{n+2}` Taylor row. -/
noncomputable def routeCCentralTaylorCenteredNumeratorMode
    (h k n : ℕ) : ℂ :=
  bettinConreyCentralCenteredCoefficient (n + 2) *
    (routeCUnitIntervalTaylorVariable h k : ℂ) ^ (n + 2)

/-- The completed elementary numerator after the harmonic row is resummed. -/
noncomputable def routeCCentralTaylorCompletedNumerator (h k : ℕ) : ℂ :=
  -1 + (routeCUnitIntervalTaylorVariable h k : ℂ) / 2 -
    Complex.log (routeCUnitIntervalRatio h k : ℂ) -
    (routeCUnitIntervalTaylorVariable h k : ℂ)

/-- The completed local period term. -/
noncomputable def routeCCentralTaylorCompleted (h k : ℕ) : ℂ :=
  routeCCentralTaylorCompletedNumerator h k /
    ((Real.pi : ℂ) * (routeCUnitIntervalRatio h k : ℂ))

/-- One centered local mode, including the source factor `1/(pi*x)`. -/
noncomputable def routeCCentralTaylorCenteredMode (h k n : ℕ) : ℂ :=
  if 0 < h ∧ h ≤ k then
    routeCCentralTaylorCenteredNumeratorMode h k n /
      ((Real.pi : ℂ) * (routeCUnitIntervalRatio h k : ℂ))
  else 0

/-- The two analytic statements extracted from Bettin--Conrey's source
Taylor theorem.  This is an interface, not a new assertion. -/
structure BettinConreyCentralTaylorPackage where
  decayScale : ℝ
  decayRate : ℝ
  decayScale_nonneg : 0 ≤ decayScale
  decayRate_pos : 0 < decayRate
  centered_bound : ∀ m : ℕ, 2 ≤ m →
    ‖bettinConreyCentralCenteredCoefficient m‖ ≤
      (decayScale : ℝ) * routeCRootExponentialMajorant (decayRate : ℝ) m
  taylor_eq : ∀ h k : ℕ, 0 < h → 0 < k → h ≤ k → Nat.Coprime h k →
    (bettinConreyCentralFinitePartSide h k : ℂ) =
      (-1 + (routeCUnitIntervalTaylorVariable h k : ℂ) / 2 +
        ∑' n : ℕ, routeCCentralTaylorRawMode h k n) /
      ((Real.pi : ℂ) * (routeCUnitIntervalRatio h k : ℂ))

/-- Literal source-level form of the analytic input.  The first field is the
central specialization of Bettin--Conrey reciprocity, the second is their
displayed Taylor theorem

`(pi*i/2) (1+z) psi_0(1+z) = -1-z/2 + sum_{m>=2} a_m(-z)^m`,

and the remaining fields record the uniform root-exponential envelope
deduced from the coefficient asymptotic.  This structure is deliberately an
interface: an inhabitant must ultimately come from a formal proof of the
paper's analytic theorem. -/
structure BettinConreyCentralTaylorAnalyticTheorem where
  psiZero : ℂ → ℂ
  central_reciprocity : ∀ h k : ℕ, 0 < h → 0 < k → h ≤ k → Nat.Coprime h k →
    (bettinConreyCentralFinitePartSide h k : ℂ) =
      I / 2 * psiZero (routeCUnitIntervalRatio h k : ℂ)
  taylor_hasSum : ∀ z : ℂ, ‖z‖ < 1 →
    HasSum
      (fun n : ℕ =>
        bettinConreyCentralTaylorCoefficient (n + 2) * (-z) ^ (n + 2))
      ((Real.pi : ℂ) * I / 2 * (1 + z) * psiZero (1 + z) + 1 + z / 2)
  decayScale : ℝ
  decayRate : ℝ
  decayScale_nonneg : 0 ≤ decayScale
  decayRate_pos : 0 < decayRate
  centered_bound : ∀ m : ℕ, 2 ≤ m →
    ‖bettinConreyCentralCenteredCoefficient m‖ ≤
      decayScale * routeCRootExponentialMajorant decayRate m

theorem routeCUnitIntervalRatio_pos
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    0 < routeCUnitIntervalRatio h k := by
  unfold routeCUnitIntervalRatio
  positivity

theorem routeCUnitIntervalRatio_le_one
    (h k : ℕ) (hk : 0 < k) (hhk : h ≤ k) :
    routeCUnitIntervalRatio h k ≤ 1 := by
  unfold routeCUnitIntervalRatio
  exact (div_le_one (by exact_mod_cast hk)).2 (by exact_mod_cast hhk)

theorem routeCUnitIntervalTaylorVariable_nonneg
    (h k : ℕ) (hk : 0 < k) (hhk : h ≤ k) :
    0 ≤ routeCUnitIntervalTaylorVariable h k := by
  unfold routeCUnitIntervalTaylorVariable
  linarith [routeCUnitIntervalRatio_le_one h k hk hhk]

theorem routeCUnitIntervalTaylorVariable_lt_one
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    routeCUnitIntervalTaylorVariable h k < 1 := by
  unfold routeCUnitIntervalTaylorVariable
  linarith [routeCUnitIntervalRatio_pos h k hh hk]

/-- For `0 < h/k <= 1`, the source expansion point `z=h/k-1` lies in the
open unit disc. -/
theorem norm_routeCUnitIntervalRatio_sub_one_lt_one
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k) :
    ‖(routeCUnitIntervalRatio h k : ℂ) - 1‖ < 1 := by
  have hx0 := routeCUnitIntervalRatio_pos h k hh hk
  have hx1 := routeCUnitIntervalRatio_le_one h k hk hhk
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonpos]
  · linarith
  · linarith

/-- A formal proof of Bettin--Conrey's source-normalized analytic theorem
constructs the exact downstream Taylor package.  In particular, the signs
and the factor `pi*x` are not assumed a second time: Lean derives them from
the displayed source series and central reciprocity. -/
noncomputable def BettinConreyCentralTaylorAnalyticTheorem.toPackage
    (T : BettinConreyCentralTaylorAnalyticTheorem) :
    BettinConreyCentralTaylorPackage where
  decayScale := T.decayScale
  decayRate := T.decayRate
  decayScale_nonneg := T.decayScale_nonneg
  decayRate_pos := T.decayRate_pos
  centered_bound := T.centered_bound
  taylor_eq := by
    intro h k hh hk hhk hcop
    let x : ℂ := (routeCUnitIntervalRatio h k : ℂ)
    have hx0 : x ≠ 0 := by
      have hxR : routeCUnitIntervalRatio h k ≠ 0 :=
        (routeCUnitIntervalRatio_pos h k hh hk).ne'
      simpa [x] using (Complex.ofReal_ne_zero.mpr hxR)
    have hz : ‖x - 1‖ < 1 := by
      simpa [x] using
        norm_routeCUnitIntervalRatio_sub_one_lt_one h k hh hk hhk
    have hsource := (T.taylor_hasSum (x - 1) hz).tsum_eq
    have hy : (routeCUnitIntervalTaylorVariable h k : ℂ) = -(x - 1) := by
      unfold routeCUnitIntervalTaylorVariable
      dsimp [x]
      push_cast
      ring
    have hraw :
        (∑' n : ℕ, routeCCentralTaylorRawMode h k n) =
          (Real.pi : ℂ) * I / 2 * x * T.psiZero x + 1 + (x - 1) / 2 := by
      calc
        (∑' n : ℕ, routeCCentralTaylorRawMode h k n) =
            ∑' n : ℕ,
              bettinConreyCentralTaylorCoefficient (n + 2) *
                (-(x - 1)) ^ (n + 2) := by
                  congr 1
                  funext n
                  simp only [routeCCentralTaylorRawMode, hy]
        _ = (Real.pi : ℂ) * I / 2 * (1 + (x - 1)) *
              T.psiZero (1 + (x - 1)) + 1 + (x - 1) / 2 := hsource
        _ = (Real.pi : ℂ) * I / 2 * x * T.psiZero x + 1 + (x - 1) / 2 := by
          ring_nf
    rw [T.central_reciprocity h k hh hk hhk hcop, hraw, hy]
    dsimp [x] at hx0 ⊢
    field_simp [hx0, Real.pi_ne_zero]
    ring

/-- The root-exponential source estimate makes the shifted centered
coefficient row absolutely summable before evaluation at a rational point. -/
theorem BettinConreyCentralTaylorPackage.centeredCoefficient_shift_norm_summable
    (P : BettinConreyCentralTaylorPackage) :
    Summable (fun n : ℕ =>
      ‖bettinConreyCentralCenteredCoefficient (n + 2)‖) := by
  have hmajor : Summable (fun n : ℕ =>
      P.decayScale * routeCRootExponentialMajorant P.decayRate (n + 2)) :=
    ((summable_nat_add_iff 2).2
      (summable_routeCRootExponentialMajorant P.decayRate P.decayRate_pos)).mul_left
        P.decayScale
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => P.centered_bound (n + 2) (by omega)) hmajor

/-- On `0 < h/k <= 1`, evaluation by `y^(n+2)` preserves absolute
summability of the centered numerator row. -/
theorem BettinConreyCentralTaylorPackage.centeredNumeratorMode_norm_summable
    (P : BettinConreyCentralTaylorPackage)
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k) :
    Summable (fun n : ℕ =>
      ‖routeCCentralTaylorCenteredNumeratorMode h k n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) P.centeredCoefficient_shift_norm_summable
  unfold routeCCentralTaylorCenteredNumeratorMode
  rw [norm_mul, norm_pow]
  have hynorm_le :
      ‖(routeCUnitIntervalTaylorVariable h k : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg
      (routeCUnitIntervalTaylorVariable_nonneg h k hk hhk)]
    exact (routeCUnitIntervalTaylorVariable_lt_one h k hh hk).le
  have hpow :
      ‖(routeCUnitIntervalTaylorVariable h k : ℂ)‖ ^ (n + 2) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) hynorm_le
  exact mul_le_of_le_one_right (norm_nonneg _) hpow

/-- The harmonic Taylor row is exactly `-log x -(1-x)`. -/
theorem hasSum_routeCCentralTaylorHarmonic
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k) :
    HasSum
      (fun n : ℕ =>
        (routeCUnitIntervalTaylorVariable h k : ℂ) ^ (n + 2) /
          ((n + 2 : ℕ) : ℂ))
      (-Complex.log (routeCUnitIntervalRatio h k : ℂ) -
        (routeCUnitIntervalTaylorVariable h k : ℂ)) := by
  have hy0 := routeCUnitIntervalTaylorVariable_nonneg h k hk hhk
  have hy1 := routeCUnitIntervalTaylorVariable_lt_one h k hh hk
  have hynorm : ‖(routeCUnitIntervalTaylorVariable h k : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, abs_of_nonneg hy0] using hy1
  have hfull := Complex.hasSum_taylorSeries_neg_log hynorm
  have hshift := (hasSum_nat_add_iff' 2).2 hfull
  convert hshift using 1
  have hxy :
      (1 : ℂ) - (routeCUnitIntervalTaylorVariable h k : ℂ) =
        (routeCUnitIntervalRatio h k : ℂ) := by
    unfold routeCUnitIntervalTaylorVariable
    push_cast
    ring
  rw [hxy]
  norm_num [Finset.sum_range_succ]

/-- The raw Taylor row splits exactly into its harmonic and centered parts. -/
theorem BettinConreyCentralTaylorPackage.tsum_raw_eq_harmonic_add_centered
    (P : BettinConreyCentralTaylorPackage)
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k) :
    (∑' n : ℕ, routeCCentralTaylorRawMode h k n) =
      (-Complex.log (routeCUnitIntervalRatio h k : ℂ) -
        (routeCUnitIntervalTaylorVariable h k : ℂ)) +
      ∑' n : ℕ, routeCCentralTaylorCenteredNumeratorMode h k n := by
  have hharm := (hasSum_routeCCentralTaylorHarmonic h k hh hk hhk).summable
  have hcenter := (P.centeredNumeratorMode_norm_summable h k hh hk hhk).of_norm
  have hraw :
      (fun n : ℕ => routeCCentralTaylorRawMode h k n) =
        (fun n : ℕ =>
          (routeCUnitIntervalTaylorVariable h k : ℂ) ^ (n + 2) /
              ((n + 2 : ℕ) : ℂ) +
            routeCCentralTaylorCenteredNumeratorMode h k n) := by
    funext n
    unfold routeCCentralTaylorRawMode
      routeCCentralTaylorCenteredNumeratorMode
      bettinConreyCentralCenteredCoefficient
    ring
  rw [hraw, hharm.tsum_add hcenter,
    (hasSum_routeCCentralTaylorHarmonic h k hh hk hhk).tsum_eq]

/-- The centered row remains absolutely summable after division by the fixed
nonzero local factor `pi*x`. -/
theorem BettinConreyCentralTaylorPackage.centeredMode_norm_summable
    (P : BettinConreyCentralTaylorPackage)
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k) :
    Summable (fun n : ℕ => ‖routeCCentralTaylorCenteredMode h k n‖) := by
  have hnum := P.centeredNumeratorMode_norm_summable h k hh hk hhk
  have hden :
      ‖(Real.pi : ℂ) * (routeCUnitIntervalRatio h k : ℂ)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (by exact_mod_cast (routeCUnitIntervalRatio_pos h k hh hk).ne')
  apply (hnum.mul_left
    (1 / ‖(Real.pi : ℂ) * (routeCUnitIntervalRatio h k : ℂ)‖)).congr
  intro n
  rw [routeCCentralTaylorCenteredMode, if_pos ⟨hh, hhk⟩]
  rw [norm_div]
  field_simp

/-- The source Taylor package supplies the exact unit-interval coefficient
data required by the already-proved homogeneous Euclidean descent. -/
noncomputable def BettinConreyCentralTaylorPackage.toUnitIntervalTaylorData
    (P : BettinConreyCentralTaylorPackage) :
    RouteCUnitIntervalTaylorCoefficientData where
  baseCompleted := routeCCentralTaylorCompleted
  baseCenteredMode := routeCCentralTaylorCenteredMode
  baseCenteredMode_norm_summable := fun h k => by
    by_cases hcond : 0 < h ∧ h ≤ k
    · have hk : 0 < k := lt_of_lt_of_le hcond.1 hcond.2
      exact P.centeredMode_norm_summable h k hcond.1 hk hcond.2
    · simp [routeCCentralTaylorCenteredMode, hcond]
  base_eq := fun h k hh hk hhk hcop => by
    rw [P.taylor_eq h k hh hk hhk hcop,
      P.tsum_raw_eq_harmonic_add_centered h k hh hk hhk]
    unfold routeCCentralTaylorCompleted routeCCentralTaylorCompletedNumerator
      routeCCentralTaylorCenteredMode
    have hcond : 0 < h ∧ h ≤ k := ⟨hh, hhk⟩
    simp only [if_pos hcond]
    rw [tsum_div_const]
    ring

/-- Complete source-level handoff: the paper's Taylor and three-term
packages reduce H15 to the adaptive completed low-mode limit. -/
theorem exists_cofinal_routeCCentralTaylorLowMode_iff_target
    (P : BettinConreyCentralTaylorPackage)
    (H : AuliBettinConreyRationalReciprocityPackage)
    (T : AuliBettinConreyRationalThreeTermPackage H) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ =>
          routeCAdaptiveTransformLow
            ((P.toUnitIntervalTaylorData.toPeriodCoefficientData H T).toLocalPeriodData.toPrimitiveSummableData.toNormSummableTransfer)
            (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) :=
  exists_cofinal_routeCUnitIntervalTaylorLowMode_iff_target
    P.toUnitIntervalTaylorData H T

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
