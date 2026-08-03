import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiTraceAudit

/-!
# BT1-C5A: Motohashi local Sobolev support translation

Motohashi's Iwasawa-coordinate formula is

`Omega = -u^2 (partial_x^2 + partial_u^2) + u partial_x partial_theta`

and `w = partial_theta`.  Hence one application of `Omega + w` has four
principal differential pieces.  When it is composed with an existing
polynomial-coefficient differential monomial, the product rule for the
`partial_u^2` piece also produces two lower pieces.

This file records that finite support calculation without pretending that
Mathlib already contains the full `PSL(2,R)` automorphic Sobolev theory.  It
proves that after `a` applications:

* total differential order is at most `2a`;
* the polynomial degree in the Iwasawa radial coordinate is at most `2a`;
* both bounds are sharp, because repeated use of the `u^2 partial_x^2` term
  reaches them simultaneously.

At the H15 radial sample `u=q^2`, the sharp polynomial coefficient is
`q^(4a)`.  Retaining the exact H15 `q^(-2)` normalization leaves the
power-ledger exponent `4a-2`.  This is a support/seminorm budget, not a lower
bound for the value of the signed spectral expression: individual
derivatives can still cancel, and a full analytic translation must control
their coefficients and `L2` norms.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSobolevTranslation

open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiTraceAudit

/-- Symbolic local monomial
`u^uDegree partial_x^xOrder partial_u^uOrder partial_theta^thetaOrder`.
The frozen left big-cell coordinate `x₁` is absent because the Casimir acts
by right differentiation on the remaining Iwasawa factor. -/
structure H15MotohashiIwasawaMonomial where
  xOrder : ℕ
  uOrder : ℕ
  thetaOrder : ℕ
  uDegree : ℕ
deriving DecidableEq, Repr

/-- Total differential order of a local monomial. -/
def H15MotohashiIwasawaMonomial.differentialOrder
    (M : H15MotohashiIwasawaMonomial) : ℕ :=
  M.xOrder + M.uOrder + M.thetaOrder

/-- The identity differential monomial. -/
def h15MotohashiIwasawaInitialMonomial :
    H15MotohashiIwasawaMonomial where
  xOrder := 0
  uOrder := 0
  thetaOrder := 0
  uDegree := 0

/-- One symbolic application of `Omega + w` after the product rule is
expanded.  The guarded `uuFirst` and `uuCoefficient` cases correspond to
one or two radial derivatives landing on an existing power of `u`. -/
inductive H15MotohashiIwasawaSobolevStep :
    H15MotohashiIwasawaMonomial →
      H15MotohashiIwasawaMonomial → Prop
  | xx (M) : H15MotohashiIwasawaSobolevStep M
      { M with xOrder := M.xOrder + 2, uDegree := M.uDegree + 2 }
  | uuTop (M) : H15MotohashiIwasawaSobolevStep M
      { M with uOrder := M.uOrder + 2, uDegree := M.uDegree + 2 }
  | uuFirst (M) (hM : 1 ≤ M.uDegree) :
      H15MotohashiIwasawaSobolevStep M
        { M with uOrder := M.uOrder + 1, uDegree := M.uDegree + 1 }
  | uuCoefficient (M) (hM : 2 ≤ M.uDegree) :
      H15MotohashiIwasawaSobolevStep M M
  | xTheta (M) : H15MotohashiIwasawaSobolevStep M
      { M with
        xOrder := M.xOrder + 1
        thetaOrder := M.thetaOrder + 1
        uDegree := M.uDegree + 1 }
  | theta (M) : H15MotohashiIwasawaSobolevStep M
      { M with thetaOrder := M.thetaOrder + 1 }

/-- Every local Casimir/K-type step increases total differential order by at
most two. -/
theorem H15MotohashiIwasawaSobolevStep.differentialOrder_le
    {M M' : H15MotohashiIwasawaMonomial}
    (h : H15MotohashiIwasawaSobolevStep M M') :
    M'.differentialOrder ≤ M.differentialOrder + 2 := by
  cases h <;>
    simp [H15MotohashiIwasawaMonomial.differentialOrder] <;> omega

/-- Every step increases radial polynomial degree by at most two. -/
theorem H15MotohashiIwasawaSobolevStep.uDegree_le
    {M M' : H15MotohashiIwasawaMonomial}
    (h : H15MotohashiIwasawaSobolevStep M M') :
    M'.uDegree ≤ M.uDegree + 2 := by
  cases h <;> simp

/-- Reachability after exactly `a` symbolic applications of `Omega + w`. -/
inductive H15MotohashiIwasawaSobolevReachable :
    ℕ → H15MotohashiIwasawaMonomial → Prop
  | zero : H15MotohashiIwasawaSobolevReachable 0
      h15MotohashiIwasawaInitialMonomial
  | succ {a M M'} : H15MotohashiIwasawaSobolevReachable a M →
      H15MotohashiIwasawaSobolevStep M M' →
        H15MotohashiIwasawaSobolevReachable (a + 1) M'

/-- Exact finite differential-order envelope for the `a`-th Motohashi
Sobolev operator. -/
theorem H15MotohashiIwasawaSobolevReachable.differentialOrder_le
    {a : ℕ} {M : H15MotohashiIwasawaMonomial}
    (h : H15MotohashiIwasawaSobolevReachable a M) :
    M.differentialOrder ≤ 2 * a := by
  induction h with
  | zero => simp [h15MotohashiIwasawaInitialMonomial,
      H15MotohashiIwasawaMonomial.differentialOrder]
  | succ hstep hlocal ih =>
      exact hlocal.differentialOrder_le.trans (by omega)

/-- Exact finite radial-degree envelope. -/
theorem H15MotohashiIwasawaSobolevReachable.uDegree_le
    {a : ℕ} {M : H15MotohashiIwasawaMonomial}
    (h : H15MotohashiIwasawaSobolevReachable a M) :
    M.uDegree ≤ 2 * a := by
  induction h with
  | zero => simp [h15MotohashiIwasawaInitialMonomial]
  | succ hstep hlocal ih =>
      exact hlocal.uDegree_le.trans (by omega)

/-- The repeated `u^2 partial_x^2` branch. -/
def h15MotohashiIwasawaWorstXMonomial (a : ℕ) :
    H15MotohashiIwasawaMonomial where
  xOrder := 2 * a
  uOrder := 0
  thetaOrder := 0
  uDegree := 2 * a

/-- Sharpness: the simultaneous upper corner `(differentialOrder,uDegree)
=(2a,2a)` really occurs in the symbolic expansion. -/
theorem h15MotohashiIwasawaWorstXMonomial_reachable (a : ℕ) :
    H15MotohashiIwasawaSobolevReachable a
      (h15MotohashiIwasawaWorstXMonomial a) := by
  induction a with
  | zero => exact H15MotohashiIwasawaSobolevReachable.zero
  | succ a ih =>
      have hstep := H15MotohashiIwasawaSobolevStep.xx
        (h15MotohashiIwasawaWorstXMonomial a)
      simpa [h15MotohashiIwasawaWorstXMonomial, Nat.mul_succ] using
        H15MotohashiIwasawaSobolevReachable.succ ih hstep

@[simp]
theorem h15MotohashiIwasawaWorstXMonomial_differentialOrder (a : ℕ) :
    (h15MotohashiIwasawaWorstXMonomial a).differentialOrder = 2 * a := by
  simp [h15MotohashiIwasawaWorstXMonomial,
    H15MotohashiIwasawaMonomial.differentialOrder]

@[simp]
theorem h15MotohashiIwasawaWorstXMonomial_uDegree (a : ℕ) :
    (h15MotohashiIwasawaWorstXMonomial a).uDegree = 2 * a := by
  simp [h15MotohashiIwasawaWorstXMonomial]

/-! ## Translation to the H15 modulus-power ledger -/

/-- Polynomial radial order forced by the sharp support envelope of
`(Omega+w)^a`. -/
def h15MotohashiIwasawaRadialOrder (a : ℕ) : ℕ := 2 * a

/-- At `u=q^2`, the sharp radial polynomial coefficient has order `q^(4a)`. -/
theorem h15MotohashiIwasawaWorstRadialPower
    (q a : ℕ) :
    (((q : ℝ) ^ 2) ^ h15MotohashiIwasawaRadialOrder a) =
      (q : ℝ) ^ (4 * a) := by
  change (((q : ℝ) ^ 2) ^ (2 * a)) = (q : ℝ) ^ (4 * a)
  calc
    ((q : ℝ) ^ 2) ^ (2 * a) = (q : ℝ) ^ (2 * (2 * a)) :=
      (pow_mul (q : ℝ) 2 (2 * a)).symm
    _ = (q : ℝ) ^ (4 * a) := by
      congr 1
      omega

/-- After the exact H15 `q^(-2)` arithmetic normalization, Casimir power
`a >= 1` has residual exponent `4a-2` in the sharp local support ledger. -/
theorem h15MotohashiResidualExponent_iwasawaRadialOrder
    (a : ℕ) (ha : 1 ≤ a) :
    h15MotohashiResidualExponent
        (h15MotohashiIwasawaRadialOrder a) = 4 * a - 2 := by
  simp [h15MotohashiResidualExponent, h15MotohashiIwasawaRadialOrder]
  omega

/-- The first safe crude Sobolev power `a=3` from the source audit would
carry residual exponent ten in this unoptimized local support ledger. -/
theorem h15MotohashiResidualExponent_crudeCasimirThree :
    h15MotohashiResidualExponent
        (h15MotohashiIwasawaRadialOrder 3) = 10 := by
  norm_num [h15MotohashiResidualExponent_iwasawaRadialOrder]

/-- One surplus conductor power over the crude `a=3` support ledger is
eleven.  This is a quantitative target, not a claim that such a gain is
available. -/
theorem h15MotohashiOneSurplusGain_crudeCasimirThree :
    h15MotohashiResidualExponent
          (h15MotohashiIwasawaRadialOrder 3) + 1 = 11 := by
  norm_num [h15MotohashiResidualExponent_iwasawaRadialOrder]

/-- Proof-carrying analytic translation still required after the symbolic
support computation.  An inhabitant must bound the actual complete H15 seed
in the group Sobolev norm; the symbolic envelope alone does not bound
derivative values or their `L2` integrals. -/
structure H15MotohashiLocalSobolevTranslationData where
  casimirPower : ℕ
  casimirPower_pos : 0 < casimirPower
  localSobolevCost : ℕ → ℝ
  C : ℝ
  C_nonneg : 0 ≤ C
  localSobolevCost_nonneg : ∀ N, 0 ≤ localSobolevCost N
  bound : ∀ N,
    localSobolevCost N ≤ C *
      (((N + 1 : ℕ) : ℝ) ^
        h15MotohashiResidualExponent
          (h15MotohashiIwasawaRadialOrder casimirPower))

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSobolevTranslation
