import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz

/-!
# Route B4: a two-level Estermann functional equation

The finite Hurwitz continuation is a nested congruence `LFunction`.  Mathlib's
functional equation therefore applies twice.  This module records:

* the exact discrete Fourier transform of the inner bilinear additive phase;
* the resulting one-variable inner functional equation;
* the outer functional equation for the complete Estermann continuation.

The remaining classical simplification is a finite DFT calculation coupling
the two displayed levels; no analytic-continuation assumption remains.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannFunctionalEquation

open AddChar Complex LSeries HurwitzZeta ZMod
open scoped BigOperators LSeries.notation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz

/-! ## The outer inverse-frequency normalization -/

/-- The Hurwitz coefficient before multiplication of its residue by the
Estermann numerator. -/
noncomputable def estermannHurwitzCoefficient
    {q : ℕ} [NeZero q] (s : ℂ) (j : ZMod q) : ℂ :=
  HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s

/-- Multiplication of a Fourier frequency by the inverse of a reduced
numerator. -/
noncomputable def estermannInverseFrequency
    (a : ℕ) {q : ℕ} (hcop : Nat.Coprime a q) (k : ZMod q) : ZMod q :=
  ((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ).val * k

/-- The outer DFT of a Hurwitz coefficient composed with multiplication by a
reduced numerator is the original DFT at the inverse frequency.  This is the
exact finite-algebra step which produces modular inverses in the classical
Estermann functional equation. -/
theorem dft_estermannHurwitzCoefficient_mul
    (a : ℕ) {q : ℕ} [NeZero q] (hcop : Nat.Coprime a q)
    (s : ℂ) (k : ZMod q) :
    ZMod.dft
        (fun j : ZMod q =>
          estermannHurwitzCoefficient s ((a : ZMod q) * j)) k =
      ZMod.dft (estermannHurwitzCoefficient (q := q) s)
        (estermannInverseFrequency a hcop k) := by
  simpa [estermannInverseFrequency, ZMod.coe_unitOfCoprime] using
    (ZMod.dft_comp_unitMul
      (estermannHurwitzCoefficient (q := q) s)
      (ZMod.unitOfCoprime a hcop) k)

/-- The same inverse-frequency rule after negating the multiplied residue. -/
theorem dft_estermannHurwitzCoefficient_neg_mul
    (a : ℕ) {q : ℕ} [NeZero q] (hcop : Nat.Coprime a q)
    (s : ℂ) (k : ZMod q) :
    ZMod.dft
        (fun j : ZMod q =>
          estermannHurwitzCoefficient s (-((a : ZMod q) * j))) k =
      ZMod.dft (estermannHurwitzCoefficient (q := q) s)
        (-(estermannInverseFrequency a hcop k)) := by
  have hfun :
      (fun j : ZMod q =>
        estermannHurwitzCoefficient s (-((a : ZMod q) * j))) =
        fun j : ZMod q =>
          estermannHurwitzCoefficient s ((a : ZMod q) * (-j)) := by
    funext j
    congr 2
    ring
  rw [hfun]
  have hneg := congrFun
    (ZMod.dft_comp_neg
      (fun j : ZMod q =>
        estermannHurwitzCoefficient s ((a : ZMod q) * j))) k
  rw [hneg]
  simpa [estermannInverseFrequency] using
    (dft_estermannHurwitzCoefficient_mul a hcop s (-k))

/-- The inner periodic coefficient at a fixed outer residue. -/
noncomputable def estermannInnerCoefficient
    (a : ℕ) {q : ℕ} [NeZero q] (j k : ZMod q) : ℂ :=
  estermannResiduePhase a j k

/-- The DFT of the inner additive character is a point mass. -/
theorem dft_estermannInnerCoefficient
    (a : ℕ) {q : ℕ} [NeZero q] (j k : ZMod q) :
    ZMod.dft (estermannInnerCoefficient a j) k =
      if k = (a : ZMod q) * j then (q : ℂ) else 0 := by
  classical
  rw [ZMod.dft_apply]
  simp only [estermannInnerCoefficient, estermannResiduePhase, smul_eq_mul]
  calc
    (∑ x : ZMod q,
        ZMod.stdAddChar (-(x * k)) *
          ZMod.stdAddChar ((a : ZMod q) * j * x)) =
        ∑ x : ZMod q,
          ZMod.stdAddChar (x * ((a : ZMod q) * j - k)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← map_add_eq_mul]
      congr 1
      ring
    _ = if (a : ZMod q) * j - k = 0 then (q : ℂ) else 0 := by
      simpa using
        (AddChar.sum_mulShift ((a : ZMod q) * j - k)
          (ZMod.isPrimitive_stdAddChar q))
    _ = if k = (a : ZMod q) * j then (q : ℂ) else 0 := by
      simp only [sub_eq_zero]
      split_ifs <;> simp_all

/-- Negating the input of the inner phase negates its outer frequency. -/
theorem estermannInnerCoefficient_comp_neg
    (a : ℕ) {q : ℕ} [NeZero q] (j : ZMod q) :
    (fun k => estermannInnerCoefficient a j (-k)) =
      estermannInnerCoefficient a (-j) := by
  funext k
  unfold estermannInnerCoefficient estermannResiduePhase
  apply congrArg ZMod.stdAddChar
  ring

/-- The L-function of the inner DFT is a single Hurwitz-zeta term. -/
theorem LFunction_dft_estermannInnerCoefficient
    (a : ℕ) {q : ℕ} [NeZero q] (j : ZMod q) (s : ℂ) :
    ZMod.LFunction (ZMod.dft (estermannInnerCoefficient a j)) s =
      (q : ℂ) ^ (-s) * (q : ℂ) *
        HurwitzZeta.hurwitzZeta
          (ZMod.toAddCircle ((a : ZMod q) * j)) s := by
  unfold ZMod.LFunction
  simp_rw [dft_estermannInnerCoefficient]
  simp
  ring

/-- Inner functional equation after the DFT has been collapsed to its single
supporting residue class. -/
theorem estermannInnerLFunction_one_sub
    (a : ℕ) {q : ℕ} [NeZero q] (j : ZMod q) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    ZMod.LFunction (estermannInnerCoefficient a j) (1 - s) =
      (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        (Complex.exp (Real.pi * Complex.I * s / 2) *
            ((q : ℂ) ^ (-s) * (q : ℂ) *
              HurwitzZeta.hurwitzZeta
                (ZMod.toAddCircle ((a : ZMod q) * j)) s) +
          Complex.exp (-Real.pi * Complex.I * s / 2) *
            ((q : ℂ) ^ (-s) * (q : ℂ) *
              HurwitzZeta.hurwitzZeta
                (ZMod.toAddCircle (-((a : ZMod q) * j))) s)) := by
  rw [ZMod.LFunction_one_sub _ hs (Or.inr hs1)]
  rw [LFunction_dft_estermannInnerCoefficient]
  have hneg : (fun x => estermannInnerCoefficient a j (-x)) =
      estermannInnerCoefficient a (-j) :=
    estermannInnerCoefficient_comp_neg a j
  rw [hneg, LFunction_dft_estermannInnerCoefficient]
  congr 3
  · congr 5
    ring

/-- The explicit Hurwitz-zeta value produced by the inner functional
equation. -/
noncomputable def estermannInnerFunctionalValue
    (a : ℕ) {q : ℕ} [NeZero q] (s : ℂ) (j : ZMod q) : ℂ :=
  (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
    (Complex.exp (Real.pi * Complex.I * s / 2) *
        ((q : ℂ) ^ (-s) * (q : ℂ) *
          HurwitzZeta.hurwitzZeta
            (ZMod.toAddCircle ((a : ZMod q) * j)) s) +
      Complex.exp (-Real.pi * Complex.I * s / 2) *
        ((q : ℂ) ^ (-s) * (q : ℂ) *
          HurwitzZeta.hurwitzZeta
            (ZMod.toAddCircle (-((a : ZMod q) * j))) s))

/-- Scalar multiplying the positive-frequency outer Hurwitz transform. -/
noncomputable def estermannOuterPositiveFactor
    (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
    Complex.exp (Real.pi * Complex.I * s / 2) *
      ((q : ℂ) ^ (-s) * (q : ℂ))

/-- Scalar multiplying the negative-frequency outer Hurwitz transform. -/
noncomputable def estermannOuterNegativeFactor
    (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
    Complex.exp (-Real.pi * Complex.I * s / 2) *
      ((q : ℂ) ^ (-s) * (q : ℂ))

/-- Collapse the outer DFT to two Hurwitz DFTs at the inverse frequencies.
This is the complete finite normalization step.  No analytic continuation or
summation estimate is used here. -/
theorem dft_estermannInnerFunctionalValue
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (s : ℂ) (k : ZMod q) :
    ZMod.dft (estermannInnerFunctionalValue (q := q) a s) k =
      estermannOuterPositiveFactor q s *
          ZMod.dft (estermannHurwitzCoefficient (q := q) s)
            (estermannInverseFrequency a hcop k) +
        estermannOuterNegativeFactor q s *
          ZMod.dft (estermannHurwitzCoefficient (q := q) s)
            (-(estermannInverseFrequency a hcop k)) := by
  have hfun : estermannInnerFunctionalValue (q := q) a s =
      fun j : ZMod q =>
        estermannOuterPositiveFactor q s *
            estermannHurwitzCoefficient s ((a : ZMod q) * j) +
          estermannOuterNegativeFactor q s *
            estermannHurwitzCoefficient s (-((a : ZMod q) * j)) := by
    funext j
    unfold estermannInnerFunctionalValue estermannOuterPositiveFactor
      estermannOuterNegativeFactor estermannHurwitzCoefficient
    ring
  rw [hfun]
  change ZMod.dft
      ((fun j : ZMod q => estermannOuterPositiveFactor q s *
          estermannHurwitzCoefficient s ((a : ZMod q) * j)) +
        (fun j : ZMod q => estermannOuterNegativeFactor q s *
          estermannHurwitzCoefficient s (-((a : ZMod q) * j)))) k = _
  rw [map_add]
  simp only [Pi.add_apply]
  rw [congrFun (ZMod.dft_const_mul
    (estermannOuterPositiveFactor q s)
    (fun j : ZMod q =>
      estermannHurwitzCoefficient s ((a : ZMod q) * j))) k]
  rw [congrFun (ZMod.dft_const_mul
    (estermannOuterNegativeFactor q s)
    (fun j : ZMod q =>
      estermannHurwitzCoefficient s (-((a : ZMod q) * j)))) k]
  rw [dft_estermannHurwitzCoefficient_mul a hcop s k,
    dft_estermannHurwitzCoefficient_neg_mul a hcop s k]

/-- The normalized outer dual coefficient occurring in the Estermann
functional equation. -/
noncomputable def estermannOuterDualCoefficient
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (s : ℂ) (k : ZMod q) : ℂ :=
  estermannOuterPositiveFactor q s *
      ZMod.dft (estermannHurwitzCoefficient (q := q) s)
        (estermannInverseFrequency a hcop k) +
    estermannOuterNegativeFactor q s *
      ZMod.dft (estermannHurwitzCoefficient (q := q) s)
        (-(estermannInverseFrequency a hcop k))

/-- Function-level form of the outer DFT normalization. -/
theorem dft_estermannInnerFunctionalValue_eq_outerDual
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) (s : ℂ) :
    ZMod.dft (estermannInnerFunctionalValue (q := q) a s) =
      estermannOuterDualCoefficient a q hcop s := by
  funext k
  exact dft_estermannInnerFunctionalValue a q hcop s k

/-- Negating the outer residue negates the already normalized dual
frequency. -/
theorem dft_estermannInnerFunctionalValue_comp_neg_eq_outerDual
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) (s : ℂ) :
    ZMod.dft
        (fun j : ZMod q => estermannInnerFunctionalValue (q := q) a s (-j)) =
      fun k => estermannOuterDualCoefficient a q hcop s (-k) := by
  rw [ZMod.dft_comp_neg,
    dft_estermannInnerFunctionalValue_eq_outerDual a q hcop s]

/-- Pointwise replacement of every inner `LFunction(1-s)` by its explicit
Hurwitz functional-equation value. -/
theorem estermannInnerLFunction_one_sub_eq_functionalValue
    (a : ℕ) {q : ℕ} [NeZero q] {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    (fun j : ZMod q =>
      ZMod.LFunction (estermannInnerCoefficient a j) (1 - s)) =
        estermannInnerFunctionalValue a s := by
  funext j
  simpa [estermannInnerFunctionalValue] using
    estermannInnerLFunction_one_sub a j hs hs1

/-- The outer periodic coefficient of the Estermann continuation. -/
noncomputable def estermannOuterCoefficient
    (a q : ℕ) [NeZero q] (s : ℂ) (j : ZMod q) : ℂ :=
  ZMod.LFunction (estermannInnerCoefficient a j) s

/-- The complete continuation satisfies Mathlib's exact congruence-L-function
functional equation at the outer level. -/
theorem estermannHurwitzContinuation_one_sub
    (a q : ℕ) [NeZero q] {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    estermannHurwitzContinuation a q (1 - s) =
      (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        (Complex.exp (Real.pi * Complex.I * s / 2) *
            ZMod.LFunction
              (ZMod.dft (estermannOuterCoefficient a q (1 - s))) s +
          Complex.exp (-Real.pi * Complex.I * s / 2) *
            ZMod.LFunction
              (ZMod.dft
                (fun j => estermannOuterCoefficient a q (1 - s) (-j))) s) := by
  unfold estermannHurwitzContinuation estermannOuterCoefficient
  exact ZMod.LFunction_one_sub _ hs (Or.inr hs1)

/-- Fully explicit two-level functional equation: both inner analytic
continuations have been replaced by finite Hurwitz-zeta expressions at `s`.
The remaining DFTs are finite algebra. -/
theorem estermannHurwitzContinuation_one_sub_explicit
    (a q : ℕ) [NeZero q] {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    estermannHurwitzContinuation a q (1 - s) =
      (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        (Complex.exp (Real.pi * Complex.I * s / 2) *
            ZMod.LFunction
              (ZMod.dft (estermannInnerFunctionalValue (q := q) a s)) s +
          Complex.exp (-Real.pi * Complex.I * s / 2) *
            ZMod.LFunction
              (ZMod.dft
                (fun j : ZMod q =>
                  estermannInnerFunctionalValue (q := q) a s (-j))) s) := by
  rw [estermannHurwitzContinuation_one_sub a q hs hs1]
  have hcoeff :=
    estermannInnerLFunction_one_sub_eq_functionalValue (q := q) a hs hs1
  unfold estermannOuterCoefficient
  rw [hcoeff]
  have hneg :
      (fun j : ZMod q =>
        ZMod.LFunction (estermannInnerCoefficient a (-j)) (1 - s)) =
          fun j : ZMod q =>
            estermannInnerFunctionalValue (q := q) a s (-j) := by
    funext j
    exact congrFun hcoeff (-j)
  rw [hneg]

/-- The two-level functional equation with its outer finite Fourier transform
fully normalized at the inverse residue frequencies.  The remaining objects
are ordinary congruence `LFunction`s of the displayed dual coefficient; this
is the correct starting point for Mellin inversion and Voronoi summation. -/
theorem estermannHurwitzContinuation_one_sub_normalized
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    estermannHurwitzContinuation a q (1 - s) =
      (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
        (Complex.exp (Real.pi * Complex.I * s / 2) *
            ZMod.LFunction
              (estermannOuterDualCoefficient a q hcop s) s +
          Complex.exp (-Real.pi * Complex.I * s / 2) *
            ZMod.LFunction
              (fun k : ZMod q =>
                estermannOuterDualCoefficient a q hcop s (-k)) s) := by
  rw [estermannHurwitzContinuation_one_sub_explicit a q hs hs1]
  rw [dft_estermannInnerFunctionalValue_eq_outerDual a q hcop s,
    dft_estermannInnerFunctionalValue_comp_neg_eq_outerDual a q hcop s]

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannFunctionalEquation
