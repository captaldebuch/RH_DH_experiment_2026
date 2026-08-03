import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic

/-!
# Route C: the source root-exponential asymptotic

Bettin--Conrey obtain, up to a bounded oscillatory factor,

`(a_m - 1/m) = O(exp(-2*sqrt(pi*m)) / m^(3/4))`.

This file records that literal profile and proves that it is stronger than
the simpler `exp(-c*sqrt m)` envelope used by the H15 transform-tail
machinery.  The conversion is unconditional and absorbs no arithmetic
estimate.  What remains external is precisely the paper's saddle-point
bound producing the displayed profile.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptotic

open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTransformTail

/-- The root-exponential profile in the source asymptotic, including its
polynomial factor `m^(-3/4)`. -/
noncomputable def bettinConreyCentralSourceMajorant (m : ℕ) : ℝ :=
  Real.exp (-2 * Real.sqrt (Real.pi * (m : ℝ))) /
    Real.rpow (m : ℝ) (3 / 4 : ℝ)

theorem bettinConreyCentralSourceMajorant_nonneg (m : ℕ) :
    0 ≤ bettinConreyCentralSourceMajorant m := by
  unfold bettinConreyCentralSourceMajorant
  exact div_nonneg (Real.exp_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg m) _)

/-- The source profile is bounded by the downstream profile with its natural
rate `2*sqrt pi`. -/
theorem bettinConreyCentralSourceMajorant_le_rootExponential
    (m : ℕ) (hm : 1 ≤ m) :
    bettinConreyCentralSourceMajorant m ≤
      routeCRootExponentialMajorant (2 * Real.sqrt Real.pi) m := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : 1 ≤ Real.rpow (m : ℝ) (3 / 4 : ℝ) :=
    Real.one_le_rpow hmR (by norm_num)
  unfold bettinConreyCentralSourceMajorant
    routeCRootExponentialMajorant
  rw [Real.sqrt_mul Real.pi_nonneg]
  have heq :
      -2 * (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) =
        -(2 * Real.sqrt Real.pi) * Real.sqrt (m : ℝ) := by ring
  rw [heq]
  exact div_le_self (Real.exp_nonneg _) hden

/-- The exact estimate furnished by the source saddle-point argument after
the bounded sine and error factors have been absorbed into `scale`.  This is
a proposition-valued interface, not an axiom or an asserted inhabitant. -/
structure BettinConreyCentralCoefficientSourceAsymptoticBound where
  scale : ℝ
  scale_nonneg : 0 ≤ scale
  eventually_bound : ∀ᶠ m : ℕ in atTop,
    ‖bettinConreyCentralCenteredCoefficient m‖ ≤
      scale * bettinConreyCentralSourceMajorant m

/-- The literal source asymptotic implies the exact eventual envelope used
by the already-proved finite-prefix absorption theorem. -/
noncomputable def
    BettinConreyCentralCoefficientSourceAsymptoticBound.toEnvelope
    (H : BettinConreyCentralCoefficientSourceAsymptoticBound) :
    BettinConreyCentralCoefficientAsymptoticEnvelope where
  scale := H.scale
  rate := 2 * Real.sqrt Real.pi
  scale_nonneg := H.scale_nonneg
  rate_pos := by positivity
  eventually_bound := by
    filter_upwards [H.eventually_bound, eventually_ge_atTop (1 : ℕ)]
      with m hm hm1
    exact hm.trans (mul_le_mul_of_nonneg_left
      (bettinConreyCentralSourceMajorant_le_rootExponential m hm1)
      H.scale_nonneg)

/-- Consequently the paper's asymptotic produces a global all-index decay
package after the already formalized finite-prefix absorption. -/
noncomputable def
    BettinConreyCentralCoefficientSourceAsymptoticBound.toRootDecay
    (H : BettinConreyCentralCoefficientSourceAsymptoticBound) :
    BettinConreyCentralCoefficientRootDecay :=
  H.toEnvelope.toRootDecay

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCRootAsymptotic
