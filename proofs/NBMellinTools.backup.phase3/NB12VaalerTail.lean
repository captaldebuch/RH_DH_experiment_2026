/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB11SmoothDecay
import RiemannHypothesis.Criteria.NymanBeurling.BBLSPhiOne

/-!
# NB12: genuine finite Fourier truncation of the Vasyunin term

This file replaces the former degenerate split `low = full`, `high = 0` by a
genuine finite Fourier approximation of the centered fractional-part
function.  The construction is deliberately elementary: it uses the ordinary
degree-`M` sine series rather than claiming the sharper Vaaler majorant.

The remainder is defined as the exact pointwise difference and is generally
nonzero.  It is then lifted through each finite Vasyunin cotangent row and the
complete signed coefficient bilinear form.  The resulting low-plus-remainder
identity is exact and unconditional.  No asymptotic bound for the remainder is
asserted; its decay is isolated as `FourierRemainderDecay`.
-/

open Filter
open scoped BigOperators

namespace NBMellinTools.NB12

open NBMellinTools.NB8
open NBMellinTools.NB10
open RH.Criteria.NymanBeurling.VasyuninGram

/-- Proposed Fourier cutoff scale for the `n`th log-taper approximant. -/
noncomputable def vaalerModeCutoff (n : ℕ) : ℕ :=
  Nat.floor ((Real.log ((logTaperLength n : ℕ) : ℝ)) ^ 5) + 1

/-- The centered periodic fractional-part function in the normalization used
by the active Vasyunin sum. At integers its value is `-1/2`. -/
noncomputable def centeredFract (x : ℝ) : ℝ :=
  Int.fract x - 1 / 2

/-- Ordinary degree-`M` Fourier sine polynomial for the centered fractional
part: `-∑_{1≤m≤M} sin(2πmx)/(πm)`. -/
noncomputable def fourierSawtoothApprox (M : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    -(Real.sin (2 * Real.pi * (m : ℝ) * x) /
      (Real.pi * (m : ℝ)))

/-- Approximation to the uncentered fractional part. -/
noncomputable def fourierFractApprox (M : ℕ) (x : ℝ) : ℝ :=
  1 / 2 + fourierSawtoothApprox M x

/-- Exact, generally nonzero, pointwise Fourier remainder. -/
noncomputable def fourierFractRemainder (M : ℕ) (x : ℝ) : ℝ :=
  Int.fract x - fourierFractApprox M x

/-- At a jump of the fractional-part function the ordinary sine series takes
the midpoint value.  Consequently the uncentered remainder is exactly
`-1/2`, independently of the cutoff.  This is why pointwise uniform
convergence cannot be used to prove `FourierRemainderDecay`. -/
theorem fourierFractRemainder_natCast (M r : ℕ) :
    fourierFractRemainder M (r : ℝ) = -(1 / 2 : ℝ) := by
  have hsin : ∀ m : ℕ,
      Real.sin (2 * Real.pi * (m : ℝ) * (r : ℝ)) = 0 := by
    intro m
    rw [show 2 * Real.pi * (m : ℝ) * (r : ℝ) =
        ((2 * m * r : ℕ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  unfold fourierFractRemainder fourierFractApprox fourierSawtoothApprox
  rw [Int.fract_natCast]
  simp_rw [hsin]
  simp

/-- The indicator of rational arguments that hit a jump of the sawtooth,
weighted by the matching cotangent row. -/
noncomputable def rationalJumpCotangentSum (h k : ℕ) : ℝ :=
  ∑ a ∈ Finset.Ico 1 k,
    if Int.fract ((a : ℝ) * ((h : ℝ) / (k : ℝ))) = 0 then
      cotangentTerm a k
    else 0

/-- Although the ordinary Fourier series has a fixed `-1/2` error at rational
integer hits, those hits cancel *exactly* in every positive cotangent row by
the involution `a ↦ k-a`.  Thus the discontinuity is not the obstruction in
the aggregate Fourier remainder. -/
theorem rationalJumpCotangentSum_eq_zero (h k : ℕ) (hk : 0 < k) :
    rationalJumpCotangentSum h k = 0 := by
  classical
  have hset : Finset.Ico 1 k = Finset.Ioc 0 (k - 1) := by
    ext a
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  unfold rationalJumpCotangentSum
  rw [hset]
  apply Finset.sum_involution (fun a _ => k - a)
  · intro a ha
    have hiff := fract_rat_reflect_eq_zero_iff h k hk a ha
    have hcotV := cotangentTermV_reflect k hk a ha
    have hcot : cotangentTerm (k - a) k = -cotangentTerm a k := by
      exact hcotV
    by_cases hz : Int.fract ((a : ℝ) * ((h : ℝ) / (k : ℝ))) = 0
    · rw [if_pos hz, if_pos (hiff.mpr hz), hcot]
      ring
    · rw [if_neg hz, if_neg (fun hz' => hz (hiff.mp hz'))]
      ring
  · intro a ha hne heq
    apply hne
    simp only [Finset.mem_Ioc] at ha
    have hk2a : k = 2 * a := by omega
    have hcot : cotangentTerm a k = 0 := by
      unfold cotangentTerm
      have ha0 : 0 < a := ha.1
      have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha0)
      have harg : Real.pi * (a : ℝ) / (k : ℝ) = Real.pi / 2 := by
        rw [hk2a]
        push_cast
        field_simp
      rw [harg, Real.cos_pi_div_two]
      simp
    rw [hcot]
    split <;> rfl
  · intro a ha
    simp only [Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Ioc] at ha
    omega

/-- Fourier remainder for the Dedekind-sawtooth convention, whose value at
integer jumps is zero. -/
noncomputable def dedekindFourierRemainder (M : ℕ) (x : ℝ) : ℝ :=
  bernoulliB1 x - fourierSawtoothApprox M x

/-- Pointwise, the uncentered remainder differs from the Dedekind remainder
only by the half-sized jump indicator. -/
theorem fourierFractRemainder_eq_dedekind_sub_jump (M : ℕ) (x : ℝ) :
    fourierFractRemainder M x =
      dedekindFourierRemainder M x -
        (if Int.fract x = 0 then 1 / 2 else 0) := by
  unfold fourierFractRemainder fourierFractApprox
    dedekindFourierRemainder bernoulliB1
  by_cases hx : Int.fract x = 0
  · simp [hx]
    ring
  · simp [hx]
    ring

/-- Exact pointwise low-plus-remainder decomposition. -/
theorem fract_eq_fourierFractApprox_add_remainder (M : ℕ) (x : ℝ) :
    Int.fract x =
      fourierFractApprox M x + fourierFractRemainder M x := by
  unfold fourierFractRemainder
  ring

/-- The degree-`M` contribution to one oriented Vasyunin cotangent row. -/
noncomputable def vasyuninFourierLowRow (h k M : ℕ) : ℝ :=
  ∑ a ∈ Finset.Ico 1 k,
    fourierFractApprox M
        (((a * h : ℕ) : ℝ) / (k : ℝ)) *
      cotangentTerm a k

/-- The exact remainder contribution to one oriented Vasyunin row. -/
noncomputable def vasyuninFourierRemainderRow (h k M : ℕ) : ℝ :=
  ∑ a ∈ Finset.Ico 1 k,
    fourierFractRemainder M
        (((a * h : ℕ) : ℝ) / (k : ℝ)) *
      cotangentTerm a k

/-- After summation against a positive cotangent row, the discontinuity term
vanishes exactly.  Therefore the active remainder can be studied using the
Dedekind sawtooth, for which ordinary Fourier convergence has the correct
value at every rational point. -/
theorem vasyuninFourierRemainderRow_eq_dedekind
    (h k M : ℕ) (hk : 0 < k) :
    vasyuninFourierRemainderRow h k M =
      ∑ a ∈ Finset.Ico 1 k,
        dedekindFourierRemainder M
            (((a * h : ℕ) : ℝ) / (k : ℝ)) *
          cotangentTerm a k := by
  classical
  unfold vasyuninFourierRemainderRow
  have hpoint : ∀ a : ℕ,
      fourierFractRemainder M
            (((a * h : ℕ) : ℝ) / (k : ℝ)) * cotangentTerm a k =
        dedekindFourierRemainder M
            (((a * h : ℕ) : ℝ) / (k : ℝ)) * cotangentTerm a k -
          (1 / 2 : ℝ) *
            (if Int.fract ((a : ℝ) * ((h : ℝ) / (k : ℝ))) = 0 then
              cotangentTerm a k
            else 0) := by
    intro a
    have harg : (((a * h : ℕ) : ℝ) / (k : ℝ)) =
        (a : ℝ) * ((h : ℝ) / (k : ℝ)) := by
      push_cast
      ring
    rw [fourierFractRemainder_eq_dedekind_sub_jump, harg]
    split <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  change
    (∑ a ∈ Finset.Ico 1 k,
        dedekindFourierRemainder M
            (((a * h : ℕ) : ℝ) / (k : ℝ)) * cotangentTerm a k) -
      (1 / 2 : ℝ) * rationalJumpCotangentSum h k = _
  rw [rationalJumpCotangentSum_eq_zero h k hk]
  ring

/-- Exact Fourier decomposition of each finite Vasyunin cotangent row. -/
theorem vasyuninCotangentSum_eq_fourierLow_add_remainder
    (h k M : ℕ) :
    vasyuninCotangentSum h k =
      vasyuninFourierLowRow h k M +
        vasyuninFourierRemainderRow h k M := by
  classical
  unfold vasyuninCotangentSum vasyuninFourierLowRow
    vasyuninFourierRemainderRow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [fract_eq_fourierFractApprox_add_remainder]
  ring

/-- Genuine finite-mode part of the complete symmetric cotangent bilinear
form. Unlike the former scaffold, this depends nontrivially on `M`. -/
noncomputable def vasyuninLowModeCore
    (N : ℕ) (coeffs : Fin N → ℝ) (M : ℕ) : ℝ :=
  ∑ j : Fin N, ∑ k : Fin N,
    coeffs j * coeffs k *
      (-Real.pi /
          (2 * ((j.val + 1 : ℕ) : ℝ) * ((k.val + 1 : ℕ) : ℝ)) *
        (vasyuninFourierLowRow (j.val + 1) (k.val + 1) M +
          vasyuninFourierLowRow (k.val + 1) (j.val + 1) M))

/-- Exact nonzero Fourier remainder in the complete symmetric cotangent
bilinear form. The historical name is retained for downstream compatibility,
but no Vaaler-quality bound is claimed. -/
noncomputable def vaalerHighModeTail
    (N : ℕ) (coeffs : Fin N → ℝ) (M : ℕ) : ℝ :=
  ∑ j : Fin N, ∑ k : Fin N,
    coeffs j * coeffs k *
      (-Real.pi /
          (2 * ((j.val + 1 : ℕ) : ℝ) * ((k.val + 1 : ℕ) : ℝ)) *
        (vasyuninFourierRemainderRow (j.val + 1) (k.val + 1) M +
          vasyuninFourierRemainderRow (k.val + 1) (j.val + 1) M))

/-- The same complete signed remainder after replacing every uncentered row
by its exactly equal Dedekind-sawtooth row. -/
noncomputable def dedekindFourierRemainderTail
    (N : ℕ) (coeffs : Fin N → ℝ) (M : ℕ) : ℝ :=
  ∑ j : Fin N, ∑ k : Fin N,
    coeffs j * coeffs k *
      (-Real.pi /
          (2 * ((j.val + 1 : ℕ) : ℝ) * ((k.val + 1 : ℕ) : ℝ)) *
        ((∑ a ∈ Finset.Ico 1 (k.val + 1),
            dedekindFourierRemainder M
                (((a * (j.val + 1) : ℕ) : ℝ) /
                  ((k.val + 1 : ℕ) : ℝ)) *
              cotangentTerm a (k.val + 1)) +
          (∑ a ∈ Finset.Ico 1 (j.val + 1),
            dedekindFourierRemainder M
                (((a * (k.val + 1) : ℕ) : ℝ) /
                  ((j.val + 1 : ℕ) : ℝ)) *
              cotangentTerm a (j.val + 1))))

/-- Exact aggregate removal of all rational jump modes. -/
theorem vaalerHighModeTail_eq_dedekind
    (N : ℕ) (coeffs : Fin N → ℝ) (M : ℕ) :
    vaalerHighModeTail N coeffs M =
      dedekindFourierRemainderTail N coeffs M := by
  classical
  unfold vaalerHighModeTail dedekindFourierRemainderTail
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [vasyuninFourierRemainderRow_eq_dedekind
      (j.val + 1) (k.val + 1) M (Nat.succ_pos _),
    vasyuninFourierRemainderRow_eq_dedekind
      (k.val + 1) (j.val + 1) M (Nat.succ_pos _)]

private theorem weighted_rows_split
    (c : ℝ) (j k M : ℕ) :
    c * (vasyuninCotangentSum (j + 1) (k + 1) +
        vasyuninCotangentSum (k + 1) (j + 1)) =
      c * (vasyuninFourierLowRow (j + 1) (k + 1) M +
        vasyuninFourierLowRow (k + 1) (j + 1) M) +
      c * (vasyuninFourierRemainderRow (j + 1) (k + 1) M +
        vasyuninFourierRemainderRow (k + 1) (j + 1) M) := by
  rw [vasyuninCotangentSum_eq_fourierLow_add_remainder,
    vasyuninCotangentSum_eq_fourierLow_add_remainder]
  ring

/-- Exact decomposition of the complete cotangent term into a genuine finite
Fourier core and its nonzero remainder. -/
theorem vasyuninCotangentTerm_eq_low_add_high
    (N : ℕ) (coeffs : Fin N → ℝ) (M : ℕ) :
    vasyuninCotangentTerm N coeffs =
      vasyuninLowModeCore N coeffs M +
        vaalerHighModeTail N coeffs M := by
  classical
  unfold vasyuninCotangentTerm vasyuninLowModeCore vaalerHighModeTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [vasyuninCotangentSum_eq_fourierLow_add_remainder,
    vasyuninCotangentSum_eq_fourierLow_add_remainder]
  ring

/-- The genuine analytic target that the Fourier remainder at the proposed
cutoff tends to zero. It is not proved in this file. -/
def FourierRemainderDecay : Prop :=
  Tendsto
    (fun n : ℕ =>
      vaalerHighModeTail
        (logTaperLength n) (logTaperCoeffs n) (vaalerModeCutoff n))
    atTop (nhds 0)

/-- Compatibility name for older downstream interfaces. -/
abbrev VaalerHighModeTailDecay : Prop := FourierRemainderDecay

/-- A quantitative version of the exact remaining Fourier-tail estimate.
The bound is on the *complete signed bilinear expression*; replacing it by a
termwise absolute-value estimate would discard the Möbius cancellation. -/
structure FourierRemainderLogEstimate where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ n : ℕ,
    |vaalerHighModeTail
        (logTaperLength n) (logTaperCoeffs n) (vaalerModeCutoff n)| ≤
      C / (Real.log (((n + 2 : ℕ) : ℝ))) ^ α

/-- A log-power estimate for the complete signed Fourier remainder proves
`FourierRemainderDecay`.  This theorem is the exact interface at which a
Vaaler/dispersion or Ehm spectral estimate can be inserted. -/
theorem fourierRemainderDecay_of_logEstimate
    (H : FourierRemainderLogEstimate) :
    FourierRemainderDecay := by
  have harg : Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hlog : Tendsto
      (fun n : ℕ => Real.log (((n + 2 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  have hrpow : Tendsto
      (fun n : ℕ => (Real.log (((n + 2 : ℕ) : ℝ))) ^ H.α)
      atTop atTop :=
    (tendsto_rpow_atTop H.α_pos).comp hlog
  have hmajorant : Tendsto
      (fun n : ℕ => H.C /
        (Real.log (((n + 2 : ℕ) : ℝ))) ^ H.α)
      atTop (nhds 0) := by
    have hinv : Tendsto
        (fun n : ℕ => ((Real.log (((n + 2 : ℕ) : ℝ))) ^ H.α)⁻¹)
        atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hrpow
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  unfold FourierRemainderDecay
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) ?_
    hmajorant
  exact Eventually.of_forall H.bound

/-- Decay of both the genuine finite core and its exact remainder implies
decay of the full cotangent term. -/
theorem tendsto_vasyuninCotangentTerm_of_low_mode
    (hlow : Tendsto
      (fun n : ℕ =>
        vasyuninLowModeCore
          (logTaperLength n) (logTaperCoeffs n) (vaalerModeCutoff n))
      atTop (nhds 0))
    (hrem : FourierRemainderDecay) :
    Tendsto
      (fun n : ℕ =>
        vasyuninCotangentTerm
          (logTaperLength n) (logTaperCoeffs n))
      atTop (nhds 0) := by
  have heq :
      (fun n : ℕ =>
        vasyuninCotangentTerm
          (logTaperLength n) (logTaperCoeffs n)) =
      (fun n : ℕ =>
        vasyuninLowModeCore
            (logTaperLength n) (logTaperCoeffs n) (vaalerModeCutoff n) +
          vaalerHighModeTail
            (logTaperLength n) (logTaperCoeffs n) (vaalerModeCutoff n)) := by
    funext n
    exact vasyuninCotangentTerm_eq_low_add_high _ _ _
  rw [heq]
  simpa using hlow.add hrem

end NBMellinTools.NB12
