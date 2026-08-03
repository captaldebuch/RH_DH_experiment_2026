import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannInverseMellin

/-!
# Route B8.5: the finite two-dimensional DFT collapse

This file proves the finite character identity which underlies the classical
four-to-two sign collapse in the Estermann functional equation.  It is a
pure identity on `ZMod q`; no rearrangement of infinite series, Mellin
inversion, or trace formula is used.

The analytic corollary identifying the four functional-equation sign pairs
with the two classical Estermann series is intentionally left to the next
module, where absolute convergence hypotheses can be stated explicitly.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannFourToTwoCollapse

open AddChar Complex ZMod
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannFunctionalEquation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannInverseMellin

/-- The complete two-dimensional additive Fourier transform of the
bilinear phase `(x,y) ↦ e(hxy/q)`. -/
noncomputable def estermannTwoDimensionalDFTSum
    (h q : ℕ) [NeZero q] (u v : ZMod q) : ℂ :=
  ∑ x : ZMod q, ∑ y : ZMod q,
    ZMod.stdAddChar ((h : ZMod q) * x * y - x * u - y * v)

/-- Multiplication by a reduced numerator followed by its normalized inverse
frequency is the identity. -/
theorem mul_estermannInverseFrequency
    (h : ℕ) {q : ℕ} [NeZero q] (hcop : Nat.Coprime h q)
    (v : ZMod q) :
    (h : ZMod q) * estermannInverseFrequency h hcop v = v := by
  unfold estermannInverseFrequency
  rw [← ZMod.coe_unitOfCoprime h hcop]
  rw [← mul_assoc, ← Units.val_mul]
  simp

/-- The supporting point of the collapsed inner Fourier transform is unique. -/
theorem mul_eq_iff_eq_estermannInverseFrequency
    (h : ℕ) {q : ℕ} [NeZero q] (hcop : Nat.Coprime h q)
    (x v : ZMod q) :
    (h : ZMod q) * x = v ↔ x = estermannInverseFrequency h hcop v := by
  constructor
  · intro hx
    have hinv :
        ((ZMod.unitOfCoprime h hcop)⁻¹ : (ZMod q)ˣ).val *
            (h : ZMod q) = 1 := by
      rw [← ZMod.coe_unitOfCoprime h hcop, ← Units.val_mul]
      simp
    calc
      x = 1 * x := by simp
      _ = (((ZMod.unitOfCoprime h hcop)⁻¹ : (ZMod q)ˣ).val *
          (h : ZMod q)) * x := by rw [hinv]
      _ = ((ZMod.unitOfCoprime h hcop)⁻¹ : (ZMod q)ˣ).val *
          ((h : ZMod q) * x) := by ring
      _ = ((ZMod.unitOfCoprime h hcop)⁻¹ : (ZMod q)ˣ).val * v := by rw [hx]
      _ = estermannInverseFrequency h hcop v := by
        rfl
  · intro hx
    rw [hx]
    exact mul_estermannInverseFrequency h hcop v

/-- The inner `y`-sum is the point mass produced by the first finite Fourier
transform. -/
theorem estermannTwoDimensionalDFT_inner
    (h q : ℕ) [NeZero q] (u v x : ZMod q) :
    (∑ y : ZMod q,
      ZMod.stdAddChar ((h : ZMod q) * x * y - x * u - y * v)) =
      ZMod.stdAddChar (-(x * u)) *
        (if v = (h : ZMod q) * x then (q : ℂ) else 0) := by
  calc
    (∑ y : ZMod q,
        ZMod.stdAddChar ((h : ZMod q) * x * y - x * u - y * v)) =
        ZMod.stdAddChar (-(x * u)) *
          ZMod.dft (estermannInnerCoefficient h x) v := by
      rw [ZMod.dft_apply]
      simp only [estermannInnerCoefficient, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      unfold estermannResiduePhase
      rw [← map_add_eq_mul, ← map_add_eq_mul]
      apply congrArg ZMod.stdAddChar
      ring
    _ = ZMod.stdAddChar (-(x * u)) *
        (if v = (h : ZMod q) * x then (q : ℂ) else 0) := by
      rw [dft_estermannInnerCoefficient]

/-- Exact two-dimensional DFT collapse:

`sum_{x,y mod q} e((hxy-xu-yv)/q) = q e(-h⁻¹uv/q)`.
-/
theorem estermannTwoDimensionalDFTSum_eq
    (h q : ℕ) [NeZero q] (hcop : Nat.Coprime h q)
    (u v : ZMod q) :
    estermannTwoDimensionalDFTSum h q u v =
      (q : ℂ) *
        ZMod.stdAddChar (-(estermannInverseFrequency h hcop (u * v))) := by
  classical
  unfold estermannTwoDimensionalDFTSum
  simp_rw [estermannTwoDimensionalDFT_inner]
  have hsupport (x : ZMod q) :
      v = (h : ZMod q) * x ↔
        x = estermannInverseFrequency h hcop v := by
    rw [eq_comm, mul_eq_iff_eq_estermannInverseFrequency h hcop]
  simp_rw [hsupport]
  simp only [mul_ite, mul_zero, Fintype.sum_ite_eq']
  rw [mul_comm]
  congr 1
  apply congrArg ZMod.stdAddChar
  unfold estermannInverseFrequency
  ring

/-! ## The two dual residue classes -/

/-- The least natural representative of the inverse of a reduced numerator
modulo `q`. -/
noncomputable def estermannPositiveDualNumerator
    (h q : ℕ) (hcop : Nat.Coprime h q) : ℕ :=
  (((ZMod.unitOfCoprime h hcop)⁻¹ : (ZMod q)ˣ).val : ZMod q).val

/-- The least natural representative of the negative inverse of a reduced
numerator modulo `q`. -/
noncomputable def estermannNegativeDualNumerator
    (h q : ℕ) (hcop : Nat.Coprime h q) : ℕ :=
  (-(((ZMod.unitOfCoprime h hcop)⁻¹ : (ZMod q)ˣ).val : ZMod q)).val

@[simp] theorem positiveDualNumerator_cast
    (h q : ℕ) [NeZero q] (hcop : Nat.Coprime h q) :
    (estermannPositiveDualNumerator h q hcop : ZMod q) =
      ((ZMod.unitOfCoprime h hcop)⁻¹ : (ZMod q)ˣ).val := by
  unfold estermannPositiveDualNumerator
  exact ZMod.natCast_zmod_val _

@[simp] theorem negativeDualNumerator_cast
    (h q : ℕ) [NeZero q] (hcop : Nat.Coprime h q) :
    (estermannNegativeDualNumerator h q hcop : ZMod q) =
      -((ZMod.unitOfCoprime h hcop)⁻¹ : (ZMod q)ˣ).val := by
  unfold estermannNegativeDualNumerator
  exact ZMod.natCast_zmod_val _

/-! ## Linearity of the finite Hurwitz realization -/

/-- The congruence `LFunction` is additive in its periodic coefficient. -/
theorem estermannLFunction_add
    {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) (s : ℂ) :
    ZMod.LFunction (fun x => f x + g x) s =
      ZMod.LFunction f s + ZMod.LFunction g s := by
  unfold ZMod.LFunction
  simp only [add_mul, Finset.sum_add_distrib, mul_add]

/-- The congruence `LFunction` commutes with a constant scalar. -/
theorem estermannLFunction_const_mul
    {q : ℕ} [NeZero q] (c : ℂ) (f : ZMod q → ℂ) (s : ℂ) :
    ZMod.LFunction (fun x => c * f x) s =
      c * ZMod.LFunction f s := by
  unfold ZMod.LFunction
  simp only [mul_assoc, Finset.mul_sum]
  ring

/-- The nested positive inverse phase is precisely the finite Hurwitz
continuation at the inverse numerator. -/
theorem nestedPositiveInverseLFunction_eq_continuation
    (h q : ℕ) [NeZero q] (hcop : Nat.Coprime h q) (s : ℂ) :
    ZMod.LFunction
        (fun k : ZMod q =>
          ZMod.LFunction
            (fun j : ZMod q =>
              ZMod.stdAddChar
                (j * estermannInverseFrequency h hcop k)) s) s =
      estermannHurwitzContinuation
        (estermannPositiveDualNumerator h q hcop) q s := by
  unfold estermannHurwitzContinuation estermannResiduePhase
  congr 1
  funext k
  congr 1
  funext j
  apply congrArg ZMod.stdAddChar
  rw [positiveDualNumerator_cast]
  unfold estermannInverseFrequency
  ring

/-- The nested negative inverse phase is precisely the finite Hurwitz
continuation at the negative inverse numerator. -/
theorem nestedNegativeInverseLFunction_eq_continuation
    (h q : ℕ) [NeZero q] (hcop : Nat.Coprime h q) (s : ℂ) :
    ZMod.LFunction
        (fun k : ZMod q =>
          ZMod.LFunction
            (fun j : ZMod q =>
              ZMod.stdAddChar
                (-(j * estermannInverseFrequency h hcop k))) s) s =
      estermannHurwitzContinuation
        (estermannNegativeDualNumerator h q hcop) q s := by
  unfold estermannHurwitzContinuation estermannResiduePhase
  congr 1
  funext k
  congr 1
  funext j
  apply congrArg ZMod.stdAddChar
  rw [negativeDualNumerator_cast]
  unfold estermannInverseFrequency
  ring

/-! ## Four functional-equation signs collapsed to two Estermann values -/

/-- Exact scalar of the positive inverse-residue Estermann value.  This form
deliberately retains the factors used by the two nested Mathlib functional
equations, so no complex-power branch law is hidden. -/
noncomputable def estermannPositiveCollapsedFactor
    (q : ℕ) (s : ℂ) : ℂ :=
  estermannDualGammaFactor q s *
    (Complex.exp (Real.pi * Complex.I * s / 2) *
        (estermannOuterNegativeFactor q s * (q : ℂ) ^ s) +
      Complex.exp (-Real.pi * Complex.I * s / 2) *
        (estermannOuterPositiveFactor q s * (q : ℂ) ^ s))

/-- Exact scalar of the negative inverse-residue Estermann value.  The two
equal-sign exponential factors later combine to `2 cos (πs)`. -/
noncomputable def estermannNegativeCollapsedFactor
    (q : ℕ) (s : ℂ) : ℂ :=
  estermannDualGammaFactor q s *
    (Complex.exp (Real.pi * Complex.I * s / 2) *
        (estermannOuterPositiveFactor q s * (q : ℂ) ^ s) +
      Complex.exp (-Real.pi * Complex.I * s / 2) *
        (estermannOuterNegativeFactor q s * (q : ℂ) ^ s))

/-- Common gamma/modulus factor after the four signs have collapsed.  Its
complex-power factors are kept in the order supplied by the two functional
equations; this is the branch-safe version of
`q^(2s-1) (2π)^(-2s) Γ(s)^2`. -/
noncomputable def estermannCollapsedCommonFactor
    (q : ℕ) (s : ℂ) : ℂ :=
  estermannDualGammaFactor q s * estermannDualGammaFactor q s *
    ((q : ℂ) ^ (-s) * (q : ℂ) * (q : ℂ) ^ s)

theorem estermannOuterPositiveFactor_eq
    (q : ℕ) (s : ℂ) :
    estermannOuterPositiveFactor q s =
      estermannDualGammaFactor q s *
        Complex.exp (Real.pi * Complex.I * s / 2) *
          ((q : ℂ) ^ (-s) * (q : ℂ)) := by
  rfl

theorem estermannOuterNegativeFactor_eq
    (q : ℕ) (s : ℂ) :
    estermannOuterNegativeFactor q s =
      estermannDualGammaFactor q s *
        Complex.exp (-Real.pi * Complex.I * s / 2) *
          ((q : ℂ) ^ (-s) * (q : ℂ)) := by
  rfl

private theorem exp_opposite_pair
    (G Q x : ℂ) :
    G * (Complex.exp x * (G * Complex.exp (-x) * Q) +
      Complex.exp (-x) * (G * Complex.exp x * Q)) =
        2 * (G * G * Q) := by
  have hexp : Complex.exp x * Complex.exp (-x) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hexp' : Complex.exp (-x) * Complex.exp x = 1 := by
    rw [mul_comm, hexp]
  calc
    G * (Complex.exp x * (G * Complex.exp (-x) * Q) +
        Complex.exp (-x) * (G * Complex.exp x * Q)) =
        G * G * Q *
          (Complex.exp x * Complex.exp (-x) +
            Complex.exp (-x) * Complex.exp x) := by ring
    _ = 2 * (G * G * Q) := by rw [hexp, hexp']; ring

private theorem exp_equal_sign_pair
    (G Q x : ℂ) :
    G * (Complex.exp x * (G * Complex.exp x * Q) +
      Complex.exp (-x) * (G * Complex.exp (-x) * Q)) =
        2 * Complex.cos (-Complex.I * (2 * x)) * (G * G * Q) := by
  have hcos :
      Complex.exp x ^ 2 + Complex.exp (-x) ^ 2 =
        2 * Complex.cos (-Complex.I * (2 * x)) := by
    have hi : (-Complex.I * (2 * x)) * Complex.I = 2 * x := by
      calc
        (-Complex.I * (2 * x)) * Complex.I =
            -(Complex.I * Complex.I) * (2 * x) := by ring
        _ = 2 * x := by rw [Complex.I_mul_I]; ring
    have hni : -(-Complex.I * (2 * x)) * Complex.I = -(2 * x) := by
      calc
        -(-Complex.I * (2 * x)) * Complex.I =
            (Complex.I * Complex.I) * (2 * x) := by ring
        _ = -(2 * x) := by rw [Complex.I_mul_I]; ring
    have hplus : Complex.exp x ^ 2 = Complex.exp (2 * x) := by
      rw [pow_two, ← Complex.exp_add]
      congr 1
      ring
    have hminus : Complex.exp (-x) ^ 2 = Complex.exp (-(2 * x)) := by
      rw [pow_two, ← Complex.exp_add]
      congr 1
      ring
    rw [hplus, hminus]
    simpa only [hi, hni] using
      (Complex.two_cos (-Complex.I * (2 * x))).symm
  calc
    G * (Complex.exp x * (G * Complex.exp x * Q) +
        Complex.exp (-x) * (G * Complex.exp (-x) * Q)) =
        G * G * Q * (Complex.exp x ^ 2 + Complex.exp (-x) ^ 2) := by ring
    _ = 2 * Complex.cos (-Complex.I * (2 * x)) * (G * G * Q) := by
      rw [hcos]
      ring

/-- The opposite-sign pairs give exactly twice the common factor. -/
theorem estermannPositiveCollapsedFactor_eq
    (q : ℕ) (s : ℂ) :
    estermannPositiveCollapsedFactor q s =
      2 * estermannCollapsedCommonFactor q s := by
  rw [estermannPositiveCollapsedFactor, estermannOuterPositiveFactor_eq,
    estermannOuterNegativeFactor_eq]
  unfold estermannCollapsedCommonFactor
  have hnegarg :
      -Real.pi * Complex.I * s / 2 =
        -(Real.pi * Complex.I * s / 2) := by ring
  rw [hnegarg]
  simpa only [mul_assoc] using
    exp_opposite_pair (estermannDualGammaFactor q s)
      ((q : ℂ) ^ (-s) * (q : ℂ) * (q : ℂ) ^ s)
      (Real.pi * Complex.I * s / 2)

/-- The equal-sign pairs give the cosine branch of the classical Estermann
functional equation. -/
theorem estermannNegativeCollapsedFactor_eq
    (q : ℕ) (s : ℂ) :
    estermannNegativeCollapsedFactor q s =
      2 * Complex.cos (Real.pi * s) *
        estermannCollapsedCommonFactor q s := by
  rw [estermannNegativeCollapsedFactor, estermannOuterPositiveFactor_eq,
    estermannOuterNegativeFactor_eq]
  unfold estermannCollapsedCommonFactor
  have harg :
      -Complex.I * (2 * (Real.pi * Complex.I * s / 2)) = Real.pi * s := by
    calc
      -Complex.I * (2 * (Real.pi * Complex.I * s / 2)) =
          -(Complex.I * Complex.I) * (Real.pi * s) := by ring
      _ = Real.pi * s := by rw [Complex.I_mul_I]; ring
  have hnegarg :
      -Real.pi * Complex.I * s / 2 =
        -(Real.pi * Complex.I * s / 2) := by ring
  rw [hnegarg]
  rw [← harg]
  simpa only [mul_assoc] using
    exp_equal_sign_pair (estermannDualGammaFactor q s)
      ((q : ℂ) ^ (-s) * (q : ℂ) * (q : ℂ) ^ s)
      (Real.pi * Complex.I * s / 2)

/-- The complete two-level functional-equation output has only two classical
Estermann values after the four sign pairs are regrouped.  This identity is
valid at the finite-Hurwitz level for every `s`; it uses neither absolute
convergence nor interchange of infinite sums. -/
theorem estermannNormalizedDualValue_eq_two_continuations
    (h q : ℕ) [NeZero q] (hcop : Nat.Coprime h q) (s : ℂ) :
    estermannNormalizedDualValue h q hcop s =
      estermannPositiveCollapsedFactor q s *
          estermannHurwitzContinuation
            (estermannPositiveDualNumerator h q hcop) q s +
        estermannNegativeCollapsedFactor q s *
          estermannHurwitzContinuation
            (estermannNegativeDualNumerator h q hcop) q s := by
  have hpositive :
      ZMod.LFunction (estermannOuterDualCoefficient h q hcop s) s =
        (estermannOuterPositiveFactor q s * (q : ℂ) ^ s) *
            estermannHurwitzContinuation
              (estermannNegativeDualNumerator h q hcop) q s +
          (estermannOuterNegativeFactor q s * (q : ℂ) ^ s) *
            estermannHurwitzContinuation
              (estermannPositiveDualNumerator h q hcop) q s := by
    have hfun : estermannOuterDualCoefficient h q hcop s =
        fun k : ZMod q =>
          (estermannOuterPositiveFactor q s * (q : ℂ) ^ s) *
              ZMod.LFunction
                (fun j : ZMod q =>
                  ZMod.stdAddChar
                    (-(j * estermannInverseFrequency h hcop k))) s +
            (estermannOuterNegativeFactor q s * (q : ℂ) ^ s) *
              ZMod.LFunction
                (fun j : ZMod q =>
                  ZMod.stdAddChar
                    (j * estermannInverseFrequency h hcop k)) s := by
      funext k
      rw [estermannOuterDualCoefficient_eq_two_additiveLFunctions]
      congr 1
      apply congrArg (fun z =>
        estermannOuterNegativeFactor q s * (q : ℂ) ^ s *
          ZMod.LFunction z s)
      funext j
      apply congrArg ZMod.stdAddChar
      ring
    rw [hfun, estermannLFunction_add,
      estermannLFunction_const_mul, estermannLFunction_const_mul,
      nestedNegativeInverseLFunction_eq_continuation,
      nestedPositiveInverseLFunction_eq_continuation]
  have hnegative :
      ZMod.LFunction
          (fun k : ZMod q => estermannOuterDualCoefficient h q hcop s (-k)) s =
        (estermannOuterPositiveFactor q s * (q : ℂ) ^ s) *
            estermannHurwitzContinuation
              (estermannPositiveDualNumerator h q hcop) q s +
          (estermannOuterNegativeFactor q s * (q : ℂ) ^ s) *
            estermannHurwitzContinuation
              (estermannNegativeDualNumerator h q hcop) q s := by
    have hfun :
        (fun k : ZMod q => estermannOuterDualCoefficient h q hcop s (-k)) =
          fun k : ZMod q =>
            (estermannOuterPositiveFactor q s * (q : ℂ) ^ s) *
                ZMod.LFunction
                  (fun j : ZMod q =>
                    ZMod.stdAddChar
                      (j * estermannInverseFrequency h hcop k)) s +
              (estermannOuterNegativeFactor q s * (q : ℂ) ^ s) *
                ZMod.LFunction
                  (fun j : ZMod q =>
                    ZMod.stdAddChar
                      (-(j * estermannInverseFrequency h hcop k))) s := by
      funext k
      rw [estermannOuterDualCoefficient_eq_two_additiveLFunctions]
      unfold estermannInverseFrequency
      congr 1
      · apply congrArg (fun z =>
          estermannOuterPositiveFactor q s * (q : ℂ) ^ s *
            ZMod.LFunction z s)
        funext j
        apply congrArg ZMod.stdAddChar
        ring
      · apply congrArg (fun z =>
          estermannOuterNegativeFactor q s * (q : ℂ) ^ s *
            ZMod.LFunction z s)
        funext j
        apply congrArg ZMod.stdAddChar
        ring
    rw [hfun, estermannLFunction_add,
      estermannLFunction_const_mul, estermannLFunction_const_mul,
      nestedPositiveInverseLFunction_eq_continuation,
      nestedNegativeInverseLFunction_eq_continuation]
  unfold estermannNormalizedDualValue
  rw [hpositive, hnegative]
  unfold estermannPositiveCollapsedFactor estermannNegativeCollapsedFactor
    estermannDualGammaFactor
  ring

/-- On `re s > 1`, the finite-Hurwitz collapse is the corresponding identity
for the two absolutely convergent classical Estermann Dirichlet series. -/
theorem estermannNormalizedDualValue_eq_two_dirichletSeries
    (h q : ℕ) [NeZero q] (hcop : Nat.Coprime h q) {s : ℂ}
    (hs : 1 < s.re) :
    estermannNormalizedDualValue h q hcop s =
      estermannPositiveCollapsedFactor q s *
          estermannDirichletSeries
            (estermannPositiveDualNumerator h q hcop) q s +
        estermannNegativeCollapsedFactor q s *
          estermannDirichletSeries
            (estermannNegativeDualNumerator h q hcop) q s := by
  rw [estermannNormalizedDualValue_eq_two_continuations,
    estermannHurwitzContinuation_eq_dirichletSeries _ _ hs,
    estermannHurwitzContinuation_eq_dirichletSeries _ _ hs]

/-- Classical `2D + 2 cos(πs) D` form of the four-to-two collapse, with the
branch-safe common gamma/modulus factor displayed explicitly. -/
theorem estermannNormalizedDualValue_eq_classical_four_to_two
    (h q : ℕ) [NeZero q] (hcop : Nat.Coprime h q) {s : ℂ}
    (hs : 1 < s.re) :
    estermannNormalizedDualValue h q hcop s =
      estermannCollapsedCommonFactor q s *
        (2 * estermannDirichletSeries
              (estermannPositiveDualNumerator h q hcop) q s +
          2 * Complex.cos (Real.pi * s) *
            estermannDirichletSeries
              (estermannNegativeDualNumerator h q hcop) q s) := by
  rw [estermannNormalizedDualValue_eq_two_dirichletSeries h q hcop hs,
    estermannPositiveCollapsedFactor_eq,
    estermannNegativeCollapsedFactor_eq]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannFourToTwoCollapse
