import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannRegularizedKernels

/-!
# Route B9.5: mandatory H15 modulus-separation audit

This file answers the mandatory WP5 question by exact finite algebra.  The
interior value coefficient has a scalar modulus factor and a natural-
numerator amplitude independent of the modulus.  After inverse-coordinate
completion, however, the remaining phase is
`e_q(-m a⁻¹)`, which depends jointly on `(q,m)`.

Summing that joint phase against the completed Kloosterman family gives the
decisive identity

`Σ_m e_q(-m a⁻¹) S_q(±n,m) = q e_q(±na)`.

After removal of `m=0`, the residual kernel is therefore
`q e_q(±na) - c_q(±n)`.  Its Ramanujan term cancels the completion zero mode
exactly, returning the original additive row.  It does not reproduce the
external H15 endpoint/linear correction and it does not yield a standard
Kuznetsov family with modulus-independent completed coefficients.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannModulusSeparation

open AddChar Complex ZMod
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15NumeratorCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloosterman
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloostermanCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15MellinAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries

/-- The scalar part of the H15 interior coefficient depending on the modulus
but not on the numerator or completed frequency. -/
noncomputable def h15ModulusScalar (N g q : ℕ) : ℂ :=
  (dirichletCoeff N (g * q) * (q : ℝ)⁻¹ : ℝ)

/-- The part of the H15 interior coefficient depending on its natural
numerator but not on the modulus or completed frequency. -/
noncomputable def h15NumeratorScalar (N g a : ℕ) : ℂ :=
  (dirichletCoeff N (g * a) * (g : ℝ)⁻¹ * Real.pi * (a : ℝ)⁻¹ : ℝ)

/-- The original coefficient has an exact elementary modulus/numerator
factorisation. -/
theorem estermannInteriorValueCoefficient_eq_modulus_mul_numerator
    (N g a q : ℕ) :
    estermannInteriorValueCoefficient N g a q =
      h15ModulusScalar N g q * h15NumeratorScalar N g a := by
  unfold estermannInteriorValueCoefficient coprimeSliceCoefficient
    h15ModulusScalar h15NumeratorScalar
  push_cast
  ring

/-- The residue-class weight after extracting the scalar modulus factor.
Its amplitudes are modulus-independent, but its support and residue map still
live in `(ZMod q)ˣ`. -/
noncomputable def h15SeparatedUnitNumeratorWeight
    (N g q : ℕ) [NeZero q] (x : (ZMod q)ˣ) : ℂ :=
  ∑ a ∈ Finset.Icc 2 (N / g),
    if hcop : Nat.Coprime a q then
      if x = ZMod.unitOfCoprime a hcop then
        h15NumeratorScalar N g a
      else 0
    else 0

theorem h15UnitNumeratorWeight_eq_modulus_mul_separated
    (N g q : ℕ) [NeZero q] (x : (ZMod q)ˣ) :
    h15UnitNumeratorWeight N g q x =
      h15ModulusScalar N g q * h15SeparatedUnitNumeratorWeight N g q x := by
  classical
  unfold h15UnitNumeratorWeight h15SeparatedUnitNumeratorWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hcop : Nat.Coprime a q
  · rw [dif_pos hcop, dif_pos hcop]
    by_cases hx : x = ZMod.unitOfCoprime a hcop
    · rw [if_pos hx, if_pos hx,
        estermannInteriorValueCoefficient_eq_modulus_mul_numerator]
    · rw [if_neg hx, if_neg hx]
      ring
  · rw [dif_neg hcop, dif_neg hcop]
    ring

/-- The same scalar factors out of the inverse-coordinate Fourier
coefficient. -/
theorem inverseCoordinateFourierCoefficient_h15UnitWeight_eq
    (N g q : ℕ) [NeZero q] (m : ZMod q) :
    inverseCoordinateFourierCoefficient (h15UnitNumeratorWeight N g q) m =
      h15ModulusScalar N g q *
        inverseCoordinateFourierCoefficient
          (h15SeparatedUnitNumeratorWeight N g q) m := by
  classical
  unfold inverseCoordinateFourierCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [h15UnitNumeratorWeight_eq_modulus_mul_separated]
  ring

/-- The still-coupled inverse phase attached to a natural numerator. -/
noncomputable def h15InverseResiduePhase
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) (m : ZMod q) : ℂ :=
  ZMod.stdAddChar
    (-(m * (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ) : ZMod q)))

/-- Exact expansion of the separated Fourier coefficient back over natural
numerators.  This is the decisive WP5 formula: the amplitude is independent
of `q`, but the phase still depends jointly on `(q,m)` through inversion in
`ZMod q`. -/
theorem inverseCoordinateFourierCoefficient_separated_eq_numeratorSum
    (N g q : ℕ) [NeZero q] (m : ZMod q) :
    inverseCoordinateFourierCoefficient
        (h15SeparatedUnitNumeratorWeight N g q) m =
      ∑ a ∈ Finset.Icc 2 (N / g),
        if hcop : Nat.Coprime a q then
          h15NumeratorScalar N g a * h15InverseResiduePhase a q hcop m
        else 0 := by
  classical
  unfold inverseCoordinateFourierCoefficient h15SeparatedUnitNumeratorWeight
    h15InverseResiduePhase
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hcop : Nat.Coprime a q
  · simp_rw [dif_pos hcop]
    rw [Fintype.sum_eq_single ((ZMod.unitOfCoprime a hcop)⁻¹)]
    · simp
    · intro y hy
      rw [if_neg (by
        intro hEq
        apply hy
        calc
          y = (y⁻¹)⁻¹ := by simp
          _ = (ZMod.unitOfCoprime a hcop)⁻¹ := congrArg Inv.inv hEq)]
      simp
  · simp [hcop]

/-- The full Fourier weight is separated as far as exact algebra permits. -/
theorem inverseCoordinateFourierCoefficient_h15UnitWeight_eq_numeratorSum
    (N g q : ℕ) [NeZero q] (m : ZMod q) :
    inverseCoordinateFourierCoefficient (h15UnitNumeratorWeight N g q) m =
      h15ModulusScalar N g q *
        ∑ a ∈ Finset.Icc 2 (N / g),
          if hcop : Nat.Coprime a q then
            h15NumeratorScalar N g a * h15InverseResiduePhase a q hcop m
          else 0 := by
  rw [inverseCoordinateFourierCoefficient_h15UnitWeight_eq,
    inverseCoordinateFourierCoefficient_separated_eq_numeratorSum]

theorem inverseCoordinateFourierCoefficient_h15UnitWeight_zero_eq
    (N g q : ℕ) [NeZero q] :
    inverseCoordinateFourierCoefficient (h15UnitNumeratorWeight N g q) 0 =
      h15ModulusScalar N g q *
        ∑ a ∈ Finset.Icc 2 (N / g),
          if Nat.Coprime a q then h15NumeratorScalar N g a else 0 := by
  rw [inverseCoordinateFourierCoefficient_h15UnitWeight_eq_numeratorSum]
  apply congrArg (h15ModulusScalar N g q * ·)
  apply Finset.sum_congr rfl
  intro a _
  by_cases hcop : Nat.Coprime a q
  · simp only [dif_pos hcop, if_pos hcop]
    unfold h15InverseResiduePhase
    simp
  · simp [hcop]

/-- The joint inverse-phase/Kloosterman kernel left after extracting the
modulus-independent natural-numerator amplitude. -/
noncomputable def h15SameSignJointCompletedKernel
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) (n : ℕ) : ℂ :=
  ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
    h15InverseResiduePhase a q hcop m * kloostermanSum (n : ZMod q) m

noncomputable def h15OppositeSignJointCompletedKernel
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) (n : ℕ) : ℂ :=
  ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
    h15InverseResiduePhase a q hcop m * kloostermanSum (-(n : ZMod q)) m

theorem h15SameSignNonzeroModeCoefficient_eq_numeratorJointSum
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15SameSignNonzeroModeCoefficient N g q n =
      estermannDivisorCoeff n * (q : ℂ)⁻¹ * h15ModulusScalar N g q *
        ∑ a ∈ Finset.Icc 2 (N / g),
          if hcop : Nat.Coprime a q then
            h15NumeratorScalar N g a *
              h15SameSignJointCompletedKernel a q hcop n
          else 0 := by
  classical
  unfold h15SameSignNonzeroModeCoefficient
  simp_rw [inverseCoordinateFourierCoefficient_h15UnitWeight_eq_numeratorSum]
  unfold h15SameSignJointCompletedKernel
  rw [mul_assoc (estermannDivisorCoeff n * (q : ℂ)⁻¹)
    (h15ModulusScalar N g q)]
  apply congrArg (estermannDivisorCoeff n * (q : ℂ)⁻¹ * ·)
  calc
    (∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
        (h15ModulusScalar N g q *
          ∑ a ∈ Finset.Icc 2 (N / g),
            if hcop : Nat.Coprime a q then
              h15NumeratorScalar N g a * h15InverseResiduePhase a q hcop m
            else 0) * kloostermanSum (n : ZMod q) m) =
      h15ModulusScalar N g q *
        ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
          (∑ a ∈ Finset.Icc 2 (N / g),
            if hcop : Nat.Coprime a q then
              h15NumeratorScalar N g a * h15InverseResiduePhase a q hcop m
            else 0) * kloostermanSum (n : ZMod q) m := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro m _
              ring
    _ = h15ModulusScalar N g q *
        ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
          ∑ a ∈ Finset.Icc 2 (N / g),
            (if hcop : Nat.Coprime a q then
              h15NumeratorScalar N g a * h15InverseResiduePhase a q hcop m
            else 0) * kloostermanSum (n : ZMod q) m := by
              congr 1
              apply Finset.sum_congr rfl
              intro m _
              rw [Finset.sum_mul]
    _ = h15ModulusScalar N g q *
        ∑ a ∈ Finset.Icc 2 (N / g),
          ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
            (if hcop : Nat.Coprime a q then
              h15NumeratorScalar N g a * h15InverseResiduePhase a q hcop m
            else 0) * kloostermanSum (n : ZMod q) m := by
              congr 1
              rw [Finset.sum_comm]
    _ = h15ModulusScalar N g q *
        ∑ a ∈ Finset.Icc 2 (N / g),
          if hcop : Nat.Coprime a q then
            h15NumeratorScalar N g a *
              ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
                h15InverseResiduePhase a q hcop m *
                  kloostermanSum (n : ZMod q) m
          else 0 := by
              congr 1
              apply Finset.sum_congr rfl
              intro a _
              by_cases hcop : Nat.Coprime a q
              · simp_rw [dif_pos hcop, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro m _
                ring
              · simp [hcop]

theorem h15OppositeSignNonzeroModeCoefficient_eq_numeratorJointSum
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15OppositeSignNonzeroModeCoefficient N g q n =
      estermannDivisorCoeff n * (q : ℂ)⁻¹ * h15ModulusScalar N g q *
        ∑ a ∈ Finset.Icc 2 (N / g),
          if hcop : Nat.Coprime a q then
            h15NumeratorScalar N g a *
              h15OppositeSignJointCompletedKernel a q hcop n
          else 0 := by
  classical
  unfold h15OppositeSignNonzeroModeCoefficient
  simp_rw [inverseCoordinateFourierCoefficient_h15UnitWeight_eq_numeratorSum]
  unfold h15OppositeSignJointCompletedKernel
  rw [mul_assoc (estermannDivisorCoeff n * (q : ℂ)⁻¹)
    (h15ModulusScalar N g q)]
  apply congrArg (estermannDivisorCoeff n * (q : ℂ)⁻¹ * ·)
  calc
    (∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
        (h15ModulusScalar N g q *
          ∑ a ∈ Finset.Icc 2 (N / g),
            if hcop : Nat.Coprime a q then
              h15NumeratorScalar N g a * h15InverseResiduePhase a q hcop m
            else 0) * kloostermanSum (-(n : ZMod q)) m) =
      h15ModulusScalar N g q *
        ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
          (∑ a ∈ Finset.Icc 2 (N / g),
            if hcop : Nat.Coprime a q then
              h15NumeratorScalar N g a * h15InverseResiduePhase a q hcop m
            else 0) * kloostermanSum (-(n : ZMod q)) m := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro m _
              ring
    _ = h15ModulusScalar N g q *
        ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
          ∑ a ∈ Finset.Icc 2 (N / g),
            (if hcop : Nat.Coprime a q then
              h15NumeratorScalar N g a * h15InverseResiduePhase a q hcop m
            else 0) * kloostermanSum (-(n : ZMod q)) m := by
              congr 1
              apply Finset.sum_congr rfl
              intro m _
              rw [Finset.sum_mul]
    _ = h15ModulusScalar N g q *
        ∑ a ∈ Finset.Icc 2 (N / g),
          ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
            (if hcop : Nat.Coprime a q then
              h15NumeratorScalar N g a * h15InverseResiduePhase a q hcop m
            else 0) * kloostermanSum (-(n : ZMod q)) m := by
              congr 1
              rw [Finset.sum_comm]
    _ = h15ModulusScalar N g q *
        ∑ a ∈ Finset.Icc 2 (N / g),
          if hcop : Nat.Coprime a q then
            h15NumeratorScalar N g a *
              ∑ m ∈ (Finset.univ.erase (0 : ZMod q)),
                h15InverseResiduePhase a q hcop m *
                  kloostermanSum (-(n : ZMod q)) m
          else 0 := by
              congr 1
              apply Finset.sum_congr rfl
              intro a _
              by_cases hcop : Nat.Coprime a q
              · simp_rw [dif_pos hcop, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro m _
                ring
              · simp [hcop]

/-! ## Exact collapse of the residual joint kernel -/

theorem sum_inverseUnitPhase_mul_kloostermanSum
    {q : ℕ} [NeZero q] (x : (ZMod q)ˣ) (n : ZMod q) :
    (∑ m : ZMod q,
      ZMod.stdAddChar
          (-(m * (((x⁻¹ : (ZMod q)ˣ) : ZMod q)))) *
        kloostermanSum n m) =
      (q : ℂ) * ZMod.stdAddChar (n * (x : ZMod q)) := by
  classical
  unfold kloostermanSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ y : (ZMod q)ˣ, ∑ m : ZMod q,
        ZMod.stdAddChar (-(m * (((x⁻¹ : (ZMod q)ˣ) : ZMod q)))) *
          ZMod.stdAddChar
            (n * (y : ZMod q) +
              m * ((y⁻¹ : (ZMod q)ˣ) : ZMod q))) =
      ∑ y : (ZMod q)ˣ,
        ZMod.stdAddChar (n * (y : ZMod q)) *
          (if x⁻¹ = y⁻¹ then (q : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro y _
            exact inverseCoordinatePhase_orthogonality n y x⁻¹
    _ = (q : ℂ) * ZMod.stdAddChar (n * (x : ZMod q)) := by
      rw [Fintype.sum_eq_single x]
      · simp
        ring
      · intro y hy
        rw [if_neg (by
          intro hinv
          apply hy
          exact inv_injective hinv.symm)]
        ring

theorem h15SameSignJointCompletedKernel_eq
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) (n : ℕ) :
    h15SameSignJointCompletedKernel a q hcop n =
      (q : ℂ) * ZMod.stdAddChar ((n : ZMod q) * (a : ZMod q)) -
        ramanujanSum (n : ZMod q) := by
  classical
  have hfull := sum_inverseUnitPhase_mul_kloostermanSum
    (ZMod.unitOfCoprime a hcop) (n : ZMod q)
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun m : ZMod q =>
      h15InverseResiduePhase a q hcop m * kloostermanSum (n : ZMod q) m)
    (by simp : (0 : ZMod q) ∈ Finset.univ)
  unfold h15SameSignJointCompletedKernel h15InverseResiduePhase
  rw [ZMod.coe_unitOfCoprime] at hfull
  change
    (∑ m ∈ Finset.univ.erase (0 : ZMod q),
      ZMod.stdAddChar
          (-(m * (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ) : ZMod q))) *
        kloostermanSum (n : ZMod q) m) +
      ZMod.stdAddChar
          (-((0 : ZMod q) *
            (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ) : ZMod q))) *
        kloostermanSum (n : ZMod q) 0 =
      ∑ m : ZMod q,
        ZMod.stdAddChar
            (-(m * (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ) : ZMod q))) *
          kloostermanSum (n : ZMod q) m at hsplit
  simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul,
    kloostermanSum_zero_eq_ramanujanSum] at hsplit
  rw [← hfull]
  linear_combination hsplit

theorem h15OppositeSignJointCompletedKernel_eq
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) (n : ℕ) :
    h15OppositeSignJointCompletedKernel a q hcop n =
      (q : ℂ) * ZMod.stdAddChar (-((n : ZMod q) * (a : ZMod q))) -
        ramanujanSum (-(n : ZMod q)) := by
  classical
  have hfull := sum_inverseUnitPhase_mul_kloostermanSum
    (ZMod.unitOfCoprime a hcop) (-(n : ZMod q))
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun m : ZMod q =>
      h15InverseResiduePhase a q hcop m *
        kloostermanSum (-(n : ZMod q)) m)
    (by simp : (0 : ZMod q) ∈ Finset.univ)
  unfold h15OppositeSignJointCompletedKernel h15InverseResiduePhase
  rw [ZMod.coe_unitOfCoprime] at hfull
  change
    (∑ m ∈ Finset.univ.erase (0 : ZMod q),
      ZMod.stdAddChar
          (-(m * (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ) : ZMod q))) *
        kloostermanSum (-(n : ZMod q)) m) +
      ZMod.stdAddChar
          (-((0 : ZMod q) *
            (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ) : ZMod q))) *
        kloostermanSum (-(n : ZMod q)) 0 =
      ∑ m : ZMod q,
        ZMod.stdAddChar
            (-(m * (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ) : ZMod q))) *
          kloostermanSum (-(n : ZMod q)) m at hsplit
  simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul,
    kloostermanSum_zero_eq_ramanujanSum] at hsplit
  have hfull' :
      (∑ m : ZMod q,
        ZMod.stdAddChar
            (-(m * (((ZMod.unitOfCoprime a hcop)⁻¹ : (ZMod q)ˣ) : ZMod q))) *
          kloostermanSum (-(n : ZMod q)) m) =
        (q : ℂ) * ZMod.stdAddChar (-((n : ZMod q) * (a : ZMod q))) := by
    convert hfull using 1
    congr 1
    apply congrArg ZMod.stdAddChar
    ring
  rw [← hfull']
  linear_combination hsplit

theorem h15SameSignZeroModeCoefficient_eq_separated
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15SameSignZeroModeCoefficient N g q n =
      estermannDivisorCoeff n * (q : ℂ)⁻¹ * h15ModulusScalar N g q *
        ((∑ a ∈ Finset.Icc 2 (N / g),
          if Nat.Coprime a q then h15NumeratorScalar N g a else 0) *
            ramanujanSum (n : ZMod q)) := by
  unfold h15SameSignZeroModeCoefficient
  rw [inverseCoordinateFourierCoefficient_h15UnitWeight_zero_eq]
  ring

theorem h15OppositeSignZeroModeCoefficient_eq_separated
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15OppositeSignZeroModeCoefficient N g q n =
      estermannDivisorCoeff n * (q : ℂ)⁻¹ * h15ModulusScalar N g q *
        ((∑ a ∈ Finset.Icc 2 (N / g),
          if Nat.Coprime a q then h15NumeratorScalar N g a else 0) *
            ramanujanSum (-(n : ZMod q))) := by
  unfold h15OppositeSignZeroModeCoefficient
  rw [inverseCoordinateFourierCoefficient_h15UnitWeight_zero_eq]
  ring

theorem h15SameSignNonzeroModeCoefficient_eq_collapsed
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15SameSignNonzeroModeCoefficient N g q n =
      estermannDivisorCoeff n * (q : ℂ)⁻¹ * h15ModulusScalar N g q *
        ∑ a ∈ Finset.Icc 2 (N / g),
          if _hcop : Nat.Coprime a q then
            h15NumeratorScalar N g a *
              ((q : ℂ) * ZMod.stdAddChar ((n : ZMod q) * (a : ZMod q)) -
                ramanujanSum (n : ZMod q))
          else 0 := by
  rw [h15SameSignNonzeroModeCoefficient_eq_numeratorJointSum]
  apply congrArg
  apply Finset.sum_congr rfl
  intro a _
  by_cases hcop : Nat.Coprime a q
  · simp only [dif_pos hcop]
    rw [h15SameSignJointCompletedKernel_eq]
  · simp [hcop]

theorem h15OppositeSignNonzeroModeCoefficient_eq_collapsed
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15OppositeSignNonzeroModeCoefficient N g q n =
      estermannDivisorCoeff n * (q : ℂ)⁻¹ * h15ModulusScalar N g q *
        ∑ a ∈ Finset.Icc 2 (N / g),
          if _hcop : Nat.Coprime a q then
            h15NumeratorScalar N g a *
              ((q : ℂ) * ZMod.stdAddChar (-((n : ZMod q) * (a : ZMod q))) -
                ramanujanSum (-(n : ZMod q)))
          else 0 := by
  rw [h15OppositeSignNonzeroModeCoefficient_eq_numeratorJointSum]
  apply congrArg
  apply Finset.sum_congr rfl
  intro a _
  by_cases hcop : Nat.Coprime a q
  · simp only [dif_pos hcop]
    rw [h15OppositeSignJointCompletedKernel_eq]
  · simp [hcop]

noncomputable def h15SameSignSeparatedAdditiveCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  estermannDivisorCoeff n * h15ModulusScalar N g q *
    ∑ a ∈ Finset.Icc 2 (N / g),
      if Nat.Coprime a q then
        h15NumeratorScalar N g a *
          ZMod.stdAddChar ((n : ZMod q) * (a : ZMod q))
      else 0

noncomputable def h15OppositeSignSeparatedAdditiveCoefficient
    (N g q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  estermannDivisorCoeff n * h15ModulusScalar N g q *
    ∑ a ∈ Finset.Icc 2 (N / g),
      if Nat.Coprime a q then
        h15NumeratorScalar N g a *
          ZMod.stdAddChar (-((n : ZMod q) * (a : ZMod q)))
      else 0

/-- The nonzero-mode Ramanujan term cancels the completion zero mode exactly.
No external H15 endpoint or linear correction is produced. -/
theorem h15SameSign_zero_add_nonzero_eq_separatedAdditive
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15SameSignZeroModeCoefficient N g q n +
        h15SameSignNonzeroModeCoefficient N g q n =
      h15SameSignSeparatedAdditiveCoefficient N g q n := by
  classical
  rw [h15SameSignZeroModeCoefficient_eq_separated,
    h15SameSignNonzeroModeCoefficient_eq_collapsed]
  unfold h15SameSignSeparatedAdditiveCoefficient
  have hsum :
      (∑ a ∈ Finset.Icc 2 (N / g),
        if _hcop : Nat.Coprime a q then
          h15NumeratorScalar N g a *
            ((q : ℂ) * ZMod.stdAddChar ((n : ZMod q) * (a : ZMod q)) -
              ramanujanSum (n : ZMod q))
        else 0) =
      (q : ℂ) *
          (∑ a ∈ Finset.Icc 2 (N / g),
            if Nat.Coprime a q then
              h15NumeratorScalar N g a *
                ZMod.stdAddChar ((n : ZMod q) * (a : ZMod q))
            else 0) -
        (∑ a ∈ Finset.Icc 2 (N / g),
          if Nat.Coprime a q then h15NumeratorScalar N g a else 0) *
            ramanujanSum (n : ZMod q) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hcop : Nat.Coprime a q
    · simp only [dif_pos hcop, if_pos hcop]
      ring
    · simp only [dif_neg hcop, if_neg hcop]
      ring
  rw [hsum]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  field_simp [hq]
  ring

theorem h15OppositeSign_zero_add_nonzero_eq_separatedAdditive
    (N g q : ℕ) [NeZero q] (n : ℕ) :
    h15OppositeSignZeroModeCoefficient N g q n +
        h15OppositeSignNonzeroModeCoefficient N g q n =
      h15OppositeSignSeparatedAdditiveCoefficient N g q n := by
  classical
  rw [h15OppositeSignZeroModeCoefficient_eq_separated,
    h15OppositeSignNonzeroModeCoefficient_eq_collapsed]
  unfold h15OppositeSignSeparatedAdditiveCoefficient
  have hsum :
      (∑ a ∈ Finset.Icc 2 (N / g),
        if _hcop : Nat.Coprime a q then
          h15NumeratorScalar N g a *
            ((q : ℂ) * ZMod.stdAddChar (-((n : ZMod q) * (a : ZMod q))) -
              ramanujanSum (-(n : ZMod q)))
        else 0) =
      (q : ℂ) *
          (∑ a ∈ Finset.Icc 2 (N / g),
            if Nat.Coprime a q then
              h15NumeratorScalar N g a *
                ZMod.stdAddChar (-((n : ZMod q) * (a : ZMod q)))
            else 0) -
        (∑ a ∈ Finset.Icc 2 (N / g),
          if Nat.Coprime a q then h15NumeratorScalar N g a else 0) *
            ramanujanSum (-(n : ZMod q)) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hcop : Nat.Coprime a q
    · simp only [dif_pos hcop, if_pos hcop]
      ring
    · simp only [dif_neg hcop, if_neg hcop]
      ring
  rw [hsum]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  field_simp [hq]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannModulusSeparation
