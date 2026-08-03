import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCReciprocalContour

/-!
# The simple Laurent coefficient of a reduced Estermann twist

For a reduced additive twist, the simple coefficient at `s = 1` is

`2 * (gamma - log q) / q`.

The proof differentiates the finite pole-removed Hurwitz numerator already
constructed in `BCFLogTaperEstermannContourShift`.  Additive-character
orthogonality removes every nonzero residue after differentiation, so only
the zero Hurwitz mode remains.  This is the finite analytic calculation in
the classical Laurent expansion; it introduces no boundary assumption.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannSimpleLaurent

open Complex Filter Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz

/-- Every pole-removed Hurwitz factor has value one at the removed pole. -/
theorem hurwitzPoleRemovedFactor_one (x : UnitAddCircle) :
    hurwitzPoleRemovedFactor x 1 = 1 := by
  simp [hurwitzPoleRemovedFactor, Complex.Gammaℝ_one]

/-- At the zero residue, the derivative of the pole-removed Hurwitz factor
is Euler's constant. -/
theorem hasDerivAt_hurwitzPoleRemovedFactor_zero :
    HasDerivAt (hurwitzPoleRemovedFactor (0 : UnitAddCircle))
      (Real.eulerMascheroniConstant : ℂ) 1 := by
  have hgammaInv : HasDerivAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
      (((Real.eulerMascheroniConstant : ℂ) + Complex.log (4 * Real.pi)) / 2) 1 := by
    have h := Complex.hasDerivAt_Gammaℝ_one.inv
      (by rw [Complex.Gammaℝ_one]; norm_num)
    convert h using 1
    rw [Complex.Gammaℝ_one]
    ring
  have hregular : DifferentiableAt ℂ
      (hurwitzRegularPart (0 : UnitAddCircle)) 1 :=
    HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div 0
  have hlinear := ((hasDerivAt_id (x := (1 : ℂ))).sub_const 1).mul
    hregular.hasDerivAt
  have hsum := hgammaInv.add hlinear
  convert hsum using 1
  simp only [hurwitzRegularPart, sub_self, zero_mul, div_zero, one_mul, id_eq]
  rw [HurwitzZeta.hurwitzZeta_zero, riemannZeta_one]
  ring

/-- Orthogonality in the outer residue variable. -/
theorem sum_estermannResiduePhase_outer
    (a q : ℕ) [NeZero q] (k : ZMod q) :
    ∑ j : ZMod q, estermannResiduePhase a j k =
      if (a : ZMod q) * k = 0 then (q : ℂ) else 0 := by
  rw [← sum_estermannResiduePhase a q k]
  apply Finset.sum_congr rfl
  intro j _
  unfold estermannResiduePhase
  apply congrArg ZMod.stdAddChar
  ring

/-- Character orthogonality with an arbitrary weight on the second residue. -/
theorem sum_sum_estermannResiduePhase_mul_right
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (f : ZMod q → ℂ) :
    ∑ j : ZMod q, ∑ k : ZMod q,
        estermannResiduePhase a j k * f k = (q : ℂ) * f 0 := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_estermannResiduePhase_outer]
  have ha : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 hcop
  have hz : ∀ k : ZMod q, (a : ZMod q) * k = 0 ↔ k = 0 := by
    intro k
    exact ha.mul_right_eq_zero
  simp only [hz]
  simp

/-- Character orthogonality with an arbitrary weight on the first residue. -/
theorem sum_sum_estermannResiduePhase_mul_left
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q)
    (f : ZMod q → ℂ) :
    ∑ j : ZMod q, (∑ k : ZMod q,
        estermannResiduePhase a j k) * f j = (q : ℂ) * f 0 := by
  classical
  simp_rw [sum_estermannResiduePhase]
  have ha : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 hcop
  have hz : ∀ j : ZMod q, (a : ZMod q) * j = 0 ↔ j = 0 := by
    intro j
    exact ha.mul_right_eq_zero
  simp only [hz]
  simp

/-- The derivative of the modulus factor `q^(-s)` at one. -/
theorem hasDerivAt_modulus_cpow_neg (q : ℕ) [NeZero q] :
    HasDerivAt (fun s : ℂ => (q : ℂ) ^ (-s))
      (-Complex.log (q : ℂ) * (q : ℂ)⁻¹) 1 := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hraw := (hasDerivAt_neg' (1 : ℂ)).const_cpow
    (c := (q : ℂ)) (Or.inl hq)
  convert hraw using 1
  · rw [Complex.cpow_neg_one]
    ring

/-- The classical simple Laurent coefficient of a reduced Estermann twist.
The additive numerator disappears from the answer by finite character
orthogonality. -/
theorem estermannSimplePoleCoefficient_eq
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    estermannSimplePoleCoefficient a q =
      2 * ((Real.eulerMascheroniConstant : ℂ) - Complex.log (q : ℂ)) /
        (q : ℂ) := by
  let H : ZMod q → ℂ → ℂ := fun r =>
    hurwitzPoleRemovedFactor (ZMod.toAddCircle r)
  let dH : ZMod q → ℂ := fun r => deriv (H r) 1
  let Q : ℂ → ℂ := fun s => (q : ℂ) ^ (-s)
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hQ : HasDerivAt Q
      (-Complex.log (q : ℂ) * (q : ℂ)⁻¹) 1 :=
    hasDerivAt_modulus_cpow_neg q
  have hH (r : ZMod q) : HasDerivAt (H r) (dH r) 1 := by
    exact (differentiableAt_hurwitzPoleRemovedFactor
      (ZMod.toAddCircle r)).hasDerivAt
  have hH0 : dH 0 = (Real.eulerMascheroniConstant : ℂ) := by
    change deriv (hurwitzPoleRemovedFactor (ZMod.toAddCircle (0 : ZMod q))) 1 = _
    rw [map_zero]
    exact HasDerivAt.deriv hasDerivAt_hurwitzPoleRemovedFactor_zero
  have hinner (j : ZMod q) : HasDerivAt
      (fun s : ℂ => Q s * ∑ k : ZMod q,
        estermannResiduePhase a j k * H k s)
      ((-Complex.log (q : ℂ) * (q : ℂ)⁻¹) *
          (∑ k : ZMod q, estermannResiduePhase a j k) +
        (q : ℂ)⁻¹ *
          (∑ k : ZMod q, estermannResiduePhase a j k * dH k)) 1 := by
    have hsum : HasDerivAt
        (fun s : ℂ => ∑ k : ZMod q,
          estermannResiduePhase a j k * H k s)
        (∑ k : ZMod q, estermannResiduePhase a j k * dH k) 1 := by
      exact HasDerivAt.fun_sum fun k _ => (hH k).const_mul _
    convert hQ.mul hsum using 1
    · simp only [Q, H, hurwitzPoleRemovedFactor_one, mul_one]
      rw [Complex.cpow_neg_one]
  have hbody (j : ZMod q) : HasDerivAt
      (fun s : ℂ =>
        (Q s * ∑ k : ZMod q,
          estermannResiduePhase a j k * H k s) * H j s)
      (((-Complex.log (q : ℂ) * (q : ℂ)⁻¹) *
            (∑ k : ZMod q, estermannResiduePhase a j k) +
          (q : ℂ)⁻¹ *
            (∑ k : ZMod q, estermannResiduePhase a j k * dH k)) +
        ((q : ℂ)⁻¹ *
            (∑ k : ZMod q, estermannResiduePhase a j k)) * dH j) 1 := by
    convert (hinner j).mul (hH j) using 1
    · simp only [H, hurwitzPoleRemovedFactor_one, mul_one]
      simp [Q, Complex.cpow_neg_one]
  have htotal : HasDerivAt (estermannPoleRemovedNumerator a q)
      ((-Complex.log (q : ℂ) * (q : ℂ)⁻¹) *
          (∑ j : ZMod q, (q : ℂ)⁻¹ *
            (∑ k : ZMod q, estermannResiduePhase a j k)) +
        (q : ℂ)⁻¹ *
          (∑ j : ZMod q,
            (((-Complex.log (q : ℂ) * (q : ℂ)⁻¹) *
                (∑ k : ZMod q, estermannResiduePhase a j k) +
              (q : ℂ)⁻¹ *
                (∑ k : ZMod q,
                  estermannResiduePhase a j k * dH k)) +
            ((q : ℂ)⁻¹ *
                (∑ k : ZMod q, estermannResiduePhase a j k)) * dH j))) 1 := by
    have hsum := HasDerivAt.fun_sum fun j (_ : j ∈ Finset.univ) => hbody j
    have hraw := hQ.mul hsum
    change HasDerivAt (fun s : ℂ =>
      Q s * ∑ j : ZMod q,
        (Q s * ∑ k : ZMod q,
          estermannResiduePhase a j k * H k s) * H j s) _ 1
    convert hraw using 1
    simp only [H, hurwitzPoleRemovedFactor_one, mul_one]
    rw [show Q 1 = (q : ℂ)⁻¹ by simp [Q, Complex.cpow_neg_one]]
  rw [estermannSimplePoleCoefficient, htotal.deriv]
  have hlead :
      (∑ j : ZMod q, (q : ℂ)⁻¹ *
        (∑ k : ZMod q, estermannResiduePhase a j k)) =
          (q : ℂ)⁻¹ * (q : ℂ) := by
    rw [← Finset.mul_sum,
      sum_sum_estermannResiduePhase_eq_modulus a q hcop]
  have hA :
      (∑ j : ZMod q,
        (-Complex.log (q : ℂ) * (q : ℂ)⁻¹) *
          (∑ k : ZMod q, estermannResiduePhase a j k)) =
        (-Complex.log (q : ℂ) * (q : ℂ)⁻¹) * (q : ℂ) := by
    rw [← Finset.mul_sum,
      sum_sum_estermannResiduePhase_eq_modulus a q hcop]
  have hB :
      (∑ j : ZMod q, (q : ℂ)⁻¹ *
        (∑ k : ZMod q, estermannResiduePhase a j k * dH k)) =
          (q : ℂ)⁻¹ * ((q : ℂ) * dH 0) := by
    rw [← Finset.mul_sum,
      sum_sum_estermannResiduePhase_mul_right a q hcop dH]
  have hC :
      (∑ j : ZMod q,
        ((q : ℂ)⁻¹ *
          (∑ k : ZMod q, estermannResiduePhase a j k)) * dH j) =
          (q : ℂ)⁻¹ * ((q : ℂ) * dH 0) := by
    calc
      _ = (q : ℂ)⁻¹ *
          (∑ j : ZMod q,
            (∑ k : ZMod q, estermannResiduePhase a j k) * dH j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = _ := by
        rw [sum_sum_estermannResiduePhase_mul_left a q hcop dH]
  have hsumderiv :
      (∑ j : ZMod q,
        (((-Complex.log (q : ℂ) * (q : ℂ)⁻¹) *
              (∑ k : ZMod q, estermannResiduePhase a j k) +
            (q : ℂ)⁻¹ *
              (∑ k : ZMod q,
                estermannResiduePhase a j k * dH k)) +
          ((q : ℂ)⁻¹ *
              (∑ k : ZMod q, estermannResiduePhase a j k)) * dH j)) =
        (-Complex.log (q : ℂ) * (q : ℂ)⁻¹) * (q : ℂ) +
          (q : ℂ)⁻¹ * ((q : ℂ) * dH 0) +
          (q : ℂ)⁻¹ * ((q : ℂ) * dH 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [hA, hB, hC]
  rw [hlead, hsumderiv, hH0]
  field_simp [hq]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannSimpleLaurent
