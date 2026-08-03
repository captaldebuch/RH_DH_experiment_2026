import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannFourToTwoCollapse
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannKloosterman

/-!
# Route B8.6: finite inverse-coordinate Kloosterman completion

This file proves the exact finite Fourier completion which converts a unit
sum with additive phase into a complete family of Kloosterman sums.  The
identity is stated first without division by the modulus, so it remains valid
as pure finite algebra and keeps every normalization visible.

The zero Fourier mode is split off explicitly.  It is the Ramanujan sum
`c_q(n)`, not the false two-case expression sometimes quoted for arbitrary
composite `q`.  In general

`c_q(n) = μ(q / gcd(q,n)) φ(q) / φ(q / gcd(q,n))`.

No Weil bound, trace formula, or correction matching is asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloostermanCompletion

open AddChar Complex ZMod
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloosterman

/-- Finite Fourier coefficient of a unit weight after inversion of its
coordinate. -/
noncomputable def inverseCoordinateFourierCoefficient
    {q : ℕ} [NeZero q] (A : (ZMod q)ˣ → ℂ) (m : ZMod q) : ℂ :=
  ∑ y : (ZMod q)ˣ,
    A (y⁻¹) * ZMod.stdAddChar (-(m * (y : ZMod q)))

/-- The degenerate Kloosterman frequency is the classical Ramanujan sum. -/
noncomputable def ramanujanSum
    {q : ℕ} [NeZero q] (n : ZMod q) : ℂ :=
  ∑ x : (ZMod q)ˣ, ZMod.stdAddChar (n * (x : ZMod q))

@[simp] theorem inverseCoordinateFourierCoefficient_zero
    {q : ℕ} [NeZero q] (A : (ZMod q)ˣ → ℂ) :
    inverseCoordinateFourierCoefficient A 0 =
      ∑ y : (ZMod q)ˣ, A (y⁻¹) := by
  classical
  unfold inverseCoordinateFourierCoefficient
  simp

theorem kloostermanSum_zero_eq_ramanujanSum
    {q : ℕ} [NeZero q] (n : ZMod q) :
    kloostermanSum n 0 = ramanujanSum n := by
  classical
  unfold kloostermanSum ramanujanSum
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- Orthogonality in the completed Fourier frequency forces the inverse
coordinate `y = x⁻¹`. -/
theorem inverseCoordinatePhase_orthogonality
    {q : ℕ} [NeZero q] (n : ZMod q)
    (x y : (ZMod q)ˣ) :
    (∑ m : ZMod q,
        ZMod.stdAddChar (-(m * (y : ZMod q))) *
          ZMod.stdAddChar
            (n * (x : ZMod q) +
              m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) =
      ZMod.stdAddChar (n * (x : ZMod q)) *
        (if y = x⁻¹ then (q : ℂ) else 0) := by
  classical
  calc
    (∑ m : ZMod q,
        ZMod.stdAddChar (-(m * (y : ZMod q))) *
          ZMod.stdAddChar
            (n * (x : ZMod q) +
              m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) =
      ZMod.stdAddChar (n * (x : ZMod q)) *
        ∑ m : ZMod q,
          ZMod.stdAddChar
            (m * (((x⁻¹ : (ZMod q)ˣ) : ZMod q) - (y : ZMod q))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [← map_add_eq_mul, ← map_add_eq_mul]
      apply congrArg ZMod.stdAddChar
      ring
    _ = ZMod.stdAddChar (n * (x : ZMod q)) *
        (if (((x⁻¹ : (ZMod q)ˣ) : ZMod q) - (y : ZMod q)) = 0
          then (q : ℂ) else 0) := by
      rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
      simp only [ZMod.card, Nat.cast_ite, Nat.cast_zero]
    _ = ZMod.stdAddChar (n * (x : ZMod q)) *
        (if y = x⁻¹ then (q : ℂ) else 0) := by
      have hiff :
          (((x⁻¹ : (ZMod q)ˣ) : ZMod q) - (y : ZMod q)) = 0 ↔
            y = x⁻¹ := by
        constructor
        · intro hzero
          apply Units.ext
          exact (sub_eq_zero.mp hzero).symm
        · intro hunit
          apply sub_eq_zero.mpr
          exact congrArg Units.val hunit.symm
      simp only [hiff]

/-- Scaled inverse-coordinate completion:

`Σ_m Â_inv(m) S_q(n,m) = q Σ_{x∈U_q} A(x)e_q(nx)`.

The unscaled `1/q` form follows by division since a nonzero natural modulus
has nonzero complex cast. -/
theorem sum_fourierCoefficient_mul_kloostermanSum
    {q : ℕ} [NeZero q] (A : (ZMod q)ˣ → ℂ) (n : ZMod q) :
    (∑ m : ZMod q,
        inverseCoordinateFourierCoefficient A m * kloostermanSum n m) =
      (q : ℂ) *
        ∑ x : (ZMod q)ˣ,
          A x * ZMod.stdAddChar (n * (x : ZMod q)) := by
  classical
  unfold inverseCoordinateFourierCoefficient kloostermanSum
  calc
    (∑ m : ZMod q,
        (∑ y : (ZMod q)ˣ,
          A (y⁻¹) * ZMod.stdAddChar (-(m * (y : ZMod q)))) *
        ∑ x : (ZMod q)ˣ,
          ZMod.stdAddChar
            (n * (x : ZMod q) +
              m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) =
      ∑ y : (ZMod q)ˣ, ∑ x : (ZMod q)ˣ,
        A (y⁻¹) *
          ∑ m : ZMod q,
            ZMod.stdAddChar (-(m * (y : ZMod q))) *
              ZMod.stdAddChar
                (n * (x : ZMod q) +
                  m * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = ∑ y : (ZMod q)ˣ, ∑ x : (ZMod q)ˣ,
        A (y⁻¹) * ZMod.stdAddChar (n * (x : ZMod q)) *
          (if y = x⁻¹ then (q : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      rw [inverseCoordinatePhase_orthogonality]
      ring
    _ = ∑ x : (ZMod q)ˣ,
        A x * ZMod.stdAddChar (n * (x : ZMod q)) * (q : ℂ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp
    _ = (q : ℂ) *
        ∑ x : (ZMod q)ˣ,
          A x * ZMod.stdAddChar (n * (x : ZMod q)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- The usual divided completion formula. -/
theorem unitAdditiveSum_eq_kloostermanCompletion
    {q : ℕ} [NeZero q] (A : (ZMod q)ˣ → ℂ) (n : ZMod q) :
    (∑ x : (ZMod q)ˣ,
        A x * ZMod.stdAddChar (n * (x : ZMod q))) =
      (q : ℂ)⁻¹ *
        ∑ m : ZMod q,
          inverseCoordinateFourierCoefficient A m * kloostermanSum n m := by
  have hq : (q : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [sum_fourierCoefficient_mul_kloostermanSum]
  field_simp

/-- Exact decomposition into the degenerate `m=0` Ramanujan mode and all
nonzero Kloosterman frequencies. -/
theorem kloostermanCompletion_eq_zeroMode_add_nonzero
    {q : ℕ} [NeZero q] (A : (ZMod q)ˣ → ℂ) (n : ZMod q) :
    (∑ m : ZMod q,
        inverseCoordinateFourierCoefficient A m * kloostermanSum n m) =
      inverseCoordinateFourierCoefficient A 0 * ramanujanSum n +
        ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
          inverseCoordinateFourierCoefficient A m * kloostermanSum n m := by
  classical
  rw [← Finset.sum_erase_add Finset.univ
    (fun m : ZMod q =>
      inverseCoordinateFourierCoefficient A m * kloostermanSum n m)
    (by simp)]
  rw [kloostermanSum_zero_eq_ramanujanSum]
  exact add_comm _ _

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloostermanCompletion
