import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorElementaryTransfer

/-!
# Route C: transferred contour remainder on the positive ray

The contour estimate controls the `g₀` remainder in a punctured complex
sector.  The central Taylor theorem uses the coupled transfer

`pi * ((1+z) R(z) - R(z/(1+z)))`.

This module transports the sectorial little-o estimate to positive real
inputs, proves that the nonlinear Möbius argument preserves every required
order, and retains both remainder terms inside the same signed expression.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorTransferredRemainder

open Complex Filter Set Topology Asymptotics
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorRemainderOrder
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorThreeTermTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorInfiniteRectangle

/-- The positive real germ at the origin. -/
def routeCTaylorPositiveAtZero : Filter ℝ := nhdsWithin 0 (Ioi 0)

/-- Positive real inputs land in the zero-angle punctured complex sector. -/
theorem tendsto_ofReal_routeCTaylorClosedPuncturedSector_zero :
    Tendsto (fun x : ℝ => (x : ℂ)) routeCTaylorPositiveAtZero
      (nhdsWithin 0 (routeCTaylorClosedPuncturedSector 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa [routeCTaylorPositiveAtZero] using
      (Complex.continuous_ofReal.tendsto 0).mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change (x : ℂ) ≠ 0 ∧ |Complex.arg (x : ℂ)| ≤ 0
    constructor
    · exact Complex.ofReal_ne_zero.mpr hx.ne'
    · rw [Complex.arg_ofReal_of_nonneg hx.le]
      simp

/-- The Möbius-transformed positive ray lands in the same punctured sector
and tends to its vertex. -/
theorem tendsto_routeCTaylorMobius_ofReal_sector_zero :
    Tendsto
      (fun x : ℝ => ((x / (1 + x) : ℝ) : ℂ))
      routeCTaylorPositiveAtZero
      (nhdsWithin 0 (routeCTaylorClosedPuncturedSector 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : ContinuousAt
        (fun x : ℝ => ((x / (1 + x) : ℝ) : ℂ)) 0 := by
      have hreal : ContinuousAt (fun x : ℝ => x / (1 + x)) 0 := by
        apply ContinuousAt.div₀ continuousAt_id
          (continuousAt_const.add continuousAt_id)
        norm_num
      simpa [Function.comp_def] using
        Complex.continuous_ofReal.continuousAt.comp hreal
    simpa [routeCTaylorPositiveAtZero] using
      hcont.tendsto.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    have hx1 : 0 < 1 + x := by linarith
    have hy : 0 < x / (1 + x) := div_pos hx hx1
    change ((x / (1 + x) : ℝ) : ℂ) ≠ 0 ∧
      |Complex.arg ((x / (1 + x) : ℝ) : ℂ)| ≤ 0
    constructor
    · exact Complex.ofReal_ne_zero.mpr hy.ne'
    · rw [Complex.arg_ofReal_of_nonneg hy.le]
      simp

/-! ## Comparison with ordinary complex monomials -/

theorem routeCTaylorOfRealRpow_isBigO_complexPow (d : ℕ) :
    (fun x : ℝ => ‖(x : ℂ)‖ ^ (d : ℝ)) =O[routeCTaylorPositiveAtZero]
      (fun x : ℝ => (x : ℂ) ^ d) := by
  apply IsBigO.of_bound 1
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  have hleft : ‖‖(x : ℂ)‖ ^ (d : ℝ)‖ = x ^ d := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
      Real.rpow_natCast]
  have hright : ‖(x : ℂ) ^ d‖ = x ^ d := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  rw [hleft, hright]
  simp

theorem routeCTaylorMobiusRpow_isBigO_complexPow (d : ℕ) :
    (fun x : ℝ =>
      ‖((x / (1 + x) : ℝ) : ℂ)‖ ^ (d : ℝ)) =O[
        routeCTaylorPositiveAtZero]
      (fun x : ℝ => (x : ℂ) ^ d) := by
  apply IsBigO.of_bound 1
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  have hx1 : 0 < 1 + x := by linarith
  have hy0 : 0 ≤ x / (1 + x) := (div_pos hx hx1).le
  have hyle : x / (1 + x) ≤ x := by
    apply (div_le_iff₀ hx1).2
    nlinarith [mul_nonneg hx.le hx.le]
  have hleft : ‖‖((x / (1 + x) : ℝ) : ℂ)‖ ^ (d : ℝ)‖ =
      (x / (1 + x)) ^ d := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0,
      Real.rpow_natCast]
  have hright : ‖(x : ℂ) ^ d‖ = x ^ d := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  rw [hleft, hright]
  simpa using Real.rpow_le_rpow hy0 hyle (Nat.cast_nonneg d)

/-! ## Each remainder and the complete signed transfer -/

theorem bettinConreyGZeroFiniteTaylorRemainder_ofReal_isLittleO
    (M : ℕ) (hM : 1 ≤ M) (d : ℕ)
    (hd : (d : ℝ) < routeCTaylorRemainderExponent M) :
    (fun x : ℝ =>
      bettinConreyGZeroFiniteTaylorRemainder (x : ℂ) M) =o[
        routeCTaylorPositiveAtZero]
      (fun x : ℝ => (x : ℂ) ^ d) := by
  have hbase := bettinConreyGZeroFiniteTaylorRemainder_isLittleO
    M hM 0 Real.pi_pos (d : ℝ) hd
  have hcomp := hbase.comp_tendsto
    tendsto_ofReal_routeCTaylorClosedPuncturedSector_zero
  exact hcomp.trans_isBigO (routeCTaylorOfRealRpow_isBigO_complexPow d)

theorem bettinConreyGZeroFiniteTaylorRemainder_mobius_isLittleO
    (M : ℕ) (hM : 1 ≤ M) (d : ℕ)
    (hd : (d : ℝ) < routeCTaylorRemainderExponent M) :
    (fun x : ℝ => bettinConreyGZeroFiniteTaylorRemainder
      ((x / (1 + x) : ℝ) : ℂ) M) =o[routeCTaylorPositiveAtZero]
      (fun x : ℝ => (x : ℂ) ^ d) := by
  have hbase := bettinConreyGZeroFiniteTaylorRemainder_isLittleO
    M hM 0 Real.pi_pos (d : ℝ) hd
  have hcomp := hbase.comp_tendsto
    tendsto_routeCTaylorMobius_ofReal_sector_zero
  exact hcomp.trans_isBigO (routeCTaylorMobiusRpow_isBigO_complexPow d)

theorem one_add_ofReal_isBigO_one :
    (fun x : ℝ => 1 + (x : ℂ)) =O[routeCTaylorPositiveAtZero]
      (fun _ : ℝ => (1 : ℂ)) := by
  apply IsBigO.of_bound 2
  have hlt : ∀ᶠ x : ℝ in routeCTaylorPositiveAtZero, x < 1 := by
    exact (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      inf_le_left
  filter_upwards [self_mem_nhdsWithin, hlt] with x hxpos hxlt
  change 0 < x at hxpos
  have hx1 : 0 < 1 + x := by linarith
  rw [show 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx1]
  norm_num
  linarith

/-- **Transferred remainder theorem.**  Below the shifted contour order,
the complete signed remainder transfer is little-o of the corresponding
ordinary complex monomial on the positive ray. -/
theorem routeCTaylorFiniteRemainderTransfer_ofReal_isLittleO
    (M : ℕ) (hM : 1 ≤ M) (d : ℕ)
    (hd : (d : ℝ) < routeCTaylorRemainderExponent M) :
    (fun x : ℝ => routeCTaylorFiniteRemainderTransfer (x : ℂ) M) =o[
      routeCTaylorPositiveAtZero] (fun x : ℝ => (x : ℂ) ^ d) := by
  have hx := bettinConreyGZeroFiniteTaylorRemainder_ofReal_isLittleO
    M hM d hd
  have hy := bettinConreyGZeroFiniteTaylorRemainder_mobius_isLittleO
    M hM d hd
  have hprodRaw := one_add_ofReal_isBigO_one.mul_isLittleO hx
  have hprod :
      (fun x : ℝ => (1 + (x : ℂ)) *
        bettinConreyGZeroFiniteTaylorRemainder (x : ℂ) M) =o[
        routeCTaylorPositiveAtZero] (fun x : ℝ => (x : ℂ) ^ d) := by
    exact hprodRaw.congr (fun _ => rfl) (fun x => by simp)
  have hdiff := hprod.sub hy
  have hscaled := hdiff.const_mul_left (Real.pi : ℂ)
  apply hscaled.congr
  · intro x
    unfold routeCTaylorFiniteRemainderTransfer routeCTaylorMobiusArgument
    congr 3
    push_cast
    ring
  · intro x
    rfl

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorTransferredRemainder
