import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorRemainderOrder
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPhaseEvaluation
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroHolomorphic

/-!
# Route C: transfer of the `g₀` expansion through the three-term relation

The contour argument gives an exact finite expansion for `g₀`.  The Taylor
theorem, however, is stated for the normalized central period at `1 + z`.
This file performs the missing algebraic transport on the positive real axis.

The elementary logarithmic part is deliberately kept in source form.  This
prevents a branch-sensitive logarithm simplification from being hidden in the
transport theorem.  The finite residue polynomial and the exact left-line
remainder are then transferred by the same Möbius map `z ↦ z/(1+z)`.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorThreeTermTransfer

open Complex
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelCentralConstructor
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCLambertPhaseEvaluation
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZeroHolomorphic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorInfiniteRectangle

/-- The logarithmic part of the source definition of `psi₀`. -/
noncomputable def bettinConreyPsiZeroElementaryPart (z : ℂ) : ℂ :=
  -2 *
      (Complex.log ((2 * Real.pi : ℂ) * z) -
        (Real.eulerMascheroniConstant : ℂ)) /
      ((Real.pi : ℂ) * I * z)

theorem bettinConreyPsiZero_eq_elementary_sub_gZero (z : ℂ) :
    bettinConreyPsiZero z =
      bettinConreyPsiZeroElementaryPart z -
        2 * I * bettinConreyGZero z := by
  rfl

/-- The fractional-linear argument forced by the central three-term
relation. -/
noncomputable def routeCTaylorMobiusArgument (z : ℂ) : ℂ :=
  z / (1 + z)

/-- The complete elementary contribution after the three-term relation.
It remains in source-logarithm form, so this definition is valid without a
choice of logarithm branch beyond the one already present in `psi₀`. -/
noncomputable def routeCTaylorRawElementaryTransfer (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * I / 2 *
      ((1 + z) * bettinConreyPsiZeroElementaryPart z -
        bettinConreyPsiZeroElementaryPart
          (routeCTaylorMobiusArgument z)) +
    1 + z / 2

/-- Transfer of the finite residue polynomial through `z ↦ z/(1+z)`. -/
noncomputable def routeCTaylorFinitePolynomialTransfer
    (z : ℂ) (M : ℕ) : ℂ :=
  (Real.pi : ℂ) *
    ((1 + z) * bettinConreyGZeroFiniteTaylorPolynomial z M -
      bettinConreyGZeroFiniteTaylorPolynomial
        (routeCTaylorMobiusArgument z) M)

/-- Transfer of the exact shifted-line remainder through the same map. -/
noncomputable def routeCTaylorFiniteRemainderTransfer
    (z : ℂ) (M : ℕ) : ℂ :=
  (Real.pi : ℂ) *
    ((1 + z) * bettinConreyGZeroFiniteTaylorRemainder z M -
      bettinConreyGZeroFiniteTaylorRemainder
        (routeCTaylorMobiusArgument z) M)

/-- The unconditional positive-real three-term relation, with all analytic
identification and continuity inputs discharged by the preceding Route C
modules. -/
theorem bettinConreyPsiZero_threeTerm_on_posReal_proved
    (x : ℝ) (hx : 0 < x) :
    bettinConreyPsiZero (x : ℂ) -
        bettinConreyPsiZero ((x : ℂ) + 1) =
      (((x : ℂ) + 1)⁻¹) *
        bettinConreyPsiZero ((x : ℂ) / ((x : ℂ) + 1)) := by
  exact bettinConreyPsiZero_threeTerm_on_posReal
    bettinConreyLambertPsiZeroIdentification_proved
    (fun z hz ↦
      (differentiableAt_bettinConreyPsiZero z hz).continuousAt)
    x hx

/-- Before expanding `g₀`, the three-term relation already gives the exact
normalized decomposition into the elementary source term and a transported
`g₀` difference. -/
theorem bettinConreyPsiZeroTaylorFunction_ofReal_eq_gZeroTransfer
    (x : ℝ) (hx : 0 < x) :
    bettinConreyPsiZeroTaylorFunction (x : ℂ) =
      routeCTaylorRawElementaryTransfer (x : ℂ) +
        (Real.pi : ℂ) *
          ((1 + (x : ℂ)) * bettinConreyGZero (x : ℂ) -
            bettinConreyGZero
              (routeCTaylorMobiusArgument (x : ℂ))) := by
  let z : ℂ := (x : ℂ)
  have hz1 : z + 1 ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    dsimp [z]
    linarith
  have hthree := bettinConreyPsiZero_threeTerm_on_posReal_proved x hx
  have hthree' : bettinConreyPsiZero z -
        bettinConreyPsiZero (1 + z) =
      (1 + z)⁻¹ *
        bettinConreyPsiZero (routeCTaylorMobiusArgument z) := by
    simpa [z, routeCTaylorMobiusArgument, add_comm] using hthree
  have hpsi : bettinConreyPsiZero (1 + z) =
      bettinConreyPsiZero z -
        (1 + z)⁻¹ *
          bettinConreyPsiZero (routeCTaylorMobiusArgument z) := by
    linear_combination -hthree'
  have hone : 1 + z ≠ 0 := by
    simpa [add_comm] using hz1
  have hscaled :
      (1 + z) * bettinConreyPsiZero (1 + z) =
        (1 + z) * bettinConreyPsiZero z -
          bettinConreyPsiZero (routeCTaylorMobiusArgument z) := by
    rw [hpsi]
    field_simp [hone]
  change bettinConreyPsiZeroTaylorFunction z = _
  unfold bettinConreyPsiZeroTaylorFunction
  rw [mul_assoc ((Real.pi : ℂ) * I / 2)]
  rw [hscaled]
  rw [bettinConreyPsiZero_eq_elementary_sub_gZero,
    bettinConreyPsiZero_eq_elementary_sub_gZero]
  unfold routeCTaylorRawElementaryTransfer
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact arbitrary-order transport of the contour Taylor expansion.  The
identity is valid on every positive real input and contains no asymptotic
notation: the last summand is the literal shifted-line integral remainder. -/
theorem bettinConreyPsiZeroTaylorFunction_ofReal_eq_finiteTransfer
    (x : ℝ) (hx : 0 < x) (M : ℕ) (hM : 1 ≤ M) :
    bettinConreyPsiZeroTaylorFunction (x : ℂ) =
      routeCTaylorRawElementaryTransfer (x : ℂ) +
        routeCTaylorFinitePolynomialTransfer (x : ℂ) M +
          routeCTaylorFiniteRemainderTransfer (x : ℂ) M := by
  let z : ℂ := (x : ℂ)
  let y : ℝ := x / (x + 1)
  have hy : 0 < y := by
    dsimp [y]
    exact div_pos hx (by linarith)
  have hz0 : z ≠ 0 := by
    exact ofReal_ne_zero.mpr hx.ne'
  have hy0 : (y : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr hy.ne'
  have hmobius : routeCTaylorMobiusArgument z = (y : ℂ) := by
    dsimp [routeCTaylorMobiusArgument, z, y]
    push_cast
    simp [add_comm]
  have hargz : |Complex.arg z| ≤ (0 : ℝ) := by
    have := Complex.arg_ofReal_of_nonneg hx.le
    simp [z, this]
  have hargy : |Complex.arg (y : ℂ)| ≤ (0 : ℝ) := by
    have := Complex.arg_ofReal_of_nonneg hy.le
    simp [this]
  have hzExpansion :=
    bettinConreyGZero_eq_finiteTaylorPolynomial_add_remainder
      z hz0 M hM hargz Real.pi_pos
  have hyExpansion :=
    bettinConreyGZero_eq_finiteTaylorPolynomial_add_remainder
      (y : ℂ) hy0 M hM hargy Real.pi_pos
  rw [bettinConreyPsiZeroTaylorFunction_ofReal_eq_gZeroTransfer x hx]
  change routeCTaylorRawElementaryTransfer z +
      (Real.pi : ℂ) *
        ((1 + z) * bettinConreyGZero z -
          bettinConreyGZero (routeCTaylorMobiusArgument z)) = _
  rw [hmobius, hzExpansion, hyExpansion]
  unfold routeCTaylorFinitePolynomialTransfer
    routeCTaylorFiniteRemainderTransfer
  rw [hmobius]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorThreeTermTransfer
