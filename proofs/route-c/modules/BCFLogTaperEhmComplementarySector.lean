import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmComplementaryDivisor
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmR1Decay
import Mathlib.Analysis.PSeries

/-!
# Near/far splitting of the Ehm complementary divisor sector

The complementary hyperbolic sector `N < d`, `d*q ≤ J` still contains the
signed arithmetic cancellation needed by H15.  This file introduces an
auxiliary divisor threshold `D`.  The range `N < d ≤ D` is left completely
signed, while the genuinely far range `D < d ≤ J` admits a termwise bound
from the proved quadratic decay of Ehm's elementary `R₁` kernel.

The resulting majorant is finite and unconditional.  It is deliberately not
advertised as a proof of uniform H15 cancellation: summing it over the full
outer range loses the Möbius signs, so a separate uniform-in-`N` argument is
still required.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmComplementarySector

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
open RH.Criteria.NymanBeurling.BCFLogTaperEhmComplementaryDivisor
open RH.Criteria.NymanBeurling.BCFLogTaperEhmR1Decay
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary

/-- The signed complementary sector with divisor coordinate at most `D`. -/
noncomputable def ehmFiniteComplementaryDivisorNearSum
    (R1 : ℝ → ℝ) (N D J : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc (N + 1) D, ∑ q ∈ Finset.Icc 1 J,
    if d * q ≤ J then
      dirichletCoeff N d * R1 (((d * q : ℕ) : ℝ) * x)
    else 0

/-- The signed complementary sector beyond the auxiliary divisor threshold
`D`. -/
noncomputable def ehmFiniteComplementaryDivisorFarSum
    (R1 : ℝ → ℝ) (N D J : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc (D + 1) J, ∑ q ∈ Finset.Icc 1 J,
    if d * q ≤ J then
      dirichletCoeff N d * R1 (((d * q : ℕ) : ℝ) * x)
    else 0

/-- Exact near/far split of the complementary divisor hyperbola. -/
theorem ehmFiniteComplementaryDivisorHyperbolicSum_eq_near_add_far
    (R1 : ℝ → ℝ) (N D J : ℕ) (x : ℝ)
    (hND : N ≤ D) (hDJ : D ≤ J) :
    ehmFiniteComplementaryDivisorHyperbolicSum R1 N J x =
      ehmFiniteComplementaryDivisorNearSum R1 N D J x +
        ehmFiniteComplementaryDivisorFarSum R1 N D J x := by
  classical
  have hwhole :
      Finset.Icc (N + 1) J =
        Finset.Icc (N + 1) D ∪ Finset.Icc (D + 1) J := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdis :
      Disjoint (Finset.Icc (N + 1) D) (Finset.Icc (D + 1) J) := by
    apply Finset.disjoint_left.mpr
    intro d hdNear hdFar
    have hdD := (Finset.mem_Icc.mp hdNear).2
    have hDd := (Finset.mem_Icc.mp hdFar).1
    omega
  unfold ehmFiniteComplementaryDivisorHyperbolicSum
    ehmFiniteComplementaryDivisorNearSum
    ehmFiniteComplementaryDivisorFarSum
  rw [hwhole, Finset.sum_union hdis]

/-- Outer BCF sum of the signed near complementary sector. -/
noncomputable def ehmFiniteComplementaryDivisorNearOuter
    (R1 : ℝ → ℝ) (N D J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) *
    ehmFiniteComplementaryDivisorNearSum R1 N D J (1 / (m : ℝ))

/-- Outer BCF sum of the signed far complementary sector. -/
noncomputable def ehmFiniteComplementaryDivisorFarOuter
    (R1 : ℝ → ℝ) (N D J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) *
    ehmFiniteComplementaryDivisorFarSum R1 N D J (1 / (m : ℝ))

/-- Exact near/far split after insertion into the outer BCF sum. -/
theorem ehmFiniteComplementaryDivisorHyperbolicOuter_eq_near_add_far
    (R1 : ℝ → ℝ) (N D J : ℕ) (hND : N ≤ D) (hDJ : D ≤ J) :
    ehmFiniteComplementaryDivisorHyperbolicOuter R1 N J =
      ehmFiniteComplementaryDivisorNearOuter R1 N D J +
        ehmFiniteComplementaryDivisorFarOuter R1 N D J := by
  classical
  unfold ehmFiniteComplementaryDivisorHyperbolicOuter
    ehmFiniteComplementaryDivisorNearOuter
    ehmFiniteComplementaryDivisorFarOuter
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [ehmFiniteComplementaryDivisorHyperbolicSum_eq_near_add_far
    R1 N D J (1 / (m : ℝ)) hND hDJ]
  ring

/-- A finite majorant for the far sector whose summand separates into the
outer coefficient mass, the far-divisor coefficient mass with quadratic
decay, and the reciprocal-square hyperbolic-row mass. -/
noncomputable def ehmComplementaryDivisorFarMajorant
    (C : ℝ) (N D J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    ∑ d ∈ Finset.Icc (D + 1) J, ∑ q ∈ Finset.Icc 1 J,
      C * (|dirichletCoeff N m| * (m : ℝ)) *
        (|dirichletCoeff N d| / (d : ℝ) ^ 2) *
          (1 / (q : ℝ) ^ 2)

/-- The finite far majorant factors exactly into its outer, divisor-tail,
and reciprocal-square masses. -/
theorem ehmComplementaryDivisorFarMajorant_eq_product
    (C : ℝ) (N D J : ℕ) :
    ehmComplementaryDivisorFarMajorant C N D J =
      C *
        (∑ m ∈ Finset.Icc 1 N, |dirichletCoeff N m| * (m : ℝ)) *
        (∑ d ∈ Finset.Icc (D + 1) J,
          |dirichletCoeff N d| / (d : ℝ) ^ 2) *
        (∑ q ∈ Finset.Icc 1 J, 1 / (q : ℝ) ^ 2) := by
  classical
  let M := Finset.Icc 1 N
  let T := Finset.Icc (D + 1) J
  let Q := Finset.Icc 1 J
  let A : ℕ → ℝ := fun m ↦ |dirichletCoeff N m| * (m : ℝ)
  let B : ℕ → ℝ := fun d ↦ |dirichletCoeff N d| / (d : ℝ) ^ 2
  let Z : ℕ → ℝ := fun q ↦ 1 / (q : ℝ) ^ 2
  have htwo :
      (∑ m ∈ M, ∑ d ∈ T, C * A m * B d) =
        C * (∑ m ∈ M, A m) * (∑ d ∈ T, B d) := by
    calc
      (∑ m ∈ M, ∑ d ∈ T, C * A m * B d) =
          C * ∑ m ∈ M, ∑ d ∈ T, A m * B d := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ = C * ((∑ m ∈ M, A m) * (∑ d ∈ T, B d)) := by
        rw [Finset.sum_mul_sum]
      _ = _ := by ring
  change (∑ m ∈ M, ∑ d ∈ T, ∑ q ∈ Q, C * A m * B d * Z q) = _
  change _ = C * (∑ m ∈ M, A m) * (∑ d ∈ T, B d) * (∑ q ∈ Q, Z q)
  calc
    (∑ m ∈ M, ∑ d ∈ T, ∑ q ∈ Q, C * A m * B d * Z q) =
        (∑ m ∈ M, ∑ d ∈ T, C * A m * B d) * (∑ q ∈ Q, Z q) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
    _ = _ := by rw [htwo]

/-- On the Dirichlet-polynomial range, the logarithmic taper and the Möbius
coefficient both have absolute value at most one. -/
theorem abs_dirichletCoeff_le_one_of_le
    (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N) :
    |dirichletCoeff N m| ≤ 1 := by
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogm0 : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm)
  have hlogmN : Real.log (m : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hmN)
  have hratio0 : 0 ≤ Real.log (m : ℝ) / Real.log (N : ℝ) :=
    div_nonneg hlogm0 hlogN.le
  have hratio1 : Real.log (m : ℝ) / Real.log (N : ℝ) ≤ 1 :=
    (div_le_one hlogN).2 hlogmN
  have hweight0 : 0 ≤ weight N m := by
    rw [weight_of_two_le hN]
    linarith
  have hweight1 : weight N m ≤ 1 := by
    rw [weight_of_two_le hN]
    linarith
  have hmu : |((ArithmeticFunction.moebius m : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
  unfold dirichletCoeff
  rw [abs_mul, abs_of_nonneg hweight0]
  calc
    |((ArithmeticFunction.moebius m : ℤ) : ℝ)| * weight N m ≤
        1 * weight N m := mul_le_mul_of_nonneg_right hmu hweight0
    _ ≤ 1 := by simpa using hweight1

/-- The unsigned outer coefficient mass is at most `N²`. -/
theorem ehmOuterCoefficientMass_le_sq (N : ℕ) (hN : 2 ≤ N) :
    (∑ m ∈ Finset.Icc 1 N, |dirichletCoeff N m| * (m : ℝ)) ≤
      (N : ℝ) ^ 2 := by
  calc
    (∑ m ∈ Finset.Icc 1 N, |dirichletCoeff N m| * (m : ℝ)) ≤
        ∑ _m ∈ Finset.Icc 1 N, (N : ℝ) := by
      apply Finset.sum_le_sum
      intro m hmMem
      have hm := (Finset.mem_Icc.mp hmMem).1
      have hmN := (Finset.mem_Icc.mp hmMem).2
      calc
        |dirichletCoeff N m| * (m : ℝ) ≤ 1 * (m : ℝ) := by
          gcongr
          exact abs_dirichletCoeff_le_one_of_le N m hN hm hmN
        _ ≤ (N : ℝ) := by simpa using (show (m : ℝ) ≤ N by exact_mod_cast hmN)
    _ ≤ (N : ℝ) * (N : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      gcongr
      rw [Nat.card_Icc]
      omega
    _ = (N : ℝ) ^ 2 := by ring

/-- Every finite reciprocal-square row beginning at one has mass at most
two.  This intentionally uses a simple telescoping bound rather than the
exact value `π²/6`. -/
theorem ehmReciprocalSquareMass_le_two (J : ℕ) :
    (∑ q ∈ Finset.Icc 1 J, 1 / (q : ℝ) ^ 2) ≤ 2 := by
  have hsets : Finset.Icc 1 J = Finset.Ioo 0 (J + 1) := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  rw [hsets]
  simpa [one_div] using (sum_Ioo_inv_sq_le (α := ℝ) 0 (J + 1))

/-- After the routine outer and reciprocal-square estimates, the only
unsigned quantity left in the far majorant is the logarithmically weighted
divisor tail. -/
theorem ehmComplementaryDivisorFarMajorant_le_divisorTail
    (N D J : ℕ) (hN : 2 ≤ N) :
    ehmComplementaryDivisorFarMajorant 8 N D J ≤
      16 * (N : ℝ) ^ 2 *
        (∑ d ∈ Finset.Icc (D + 1) J,
          |dirichletCoeff N d| / (d : ℝ) ^ 2) := by
  rw [ehmComplementaryDivisorFarMajorant_eq_product]
  have houter := ehmOuterCoefficientMass_le_sq N hN
  have hq := ehmReciprocalSquareMass_le_two J
  calc
    8 * (∑ m ∈ Finset.Icc 1 N, |dirichletCoeff N m| * (m : ℝ)) *
          (∑ d ∈ Finset.Icc (D + 1) J,
            |dirichletCoeff N d| / (d : ℝ) ^ 2) *
          (∑ q ∈ Finset.Icc 1 J, 1 / (q : ℝ) ^ 2) ≤
        8 * (N : ℝ) ^ 2 *
          (∑ d ∈ Finset.Icc (D + 1) J,
            |dirichletCoeff N d| / (d : ℝ) ^ 2) * 2 := by
      gcongr
    _ = _ := by ring

private theorem farSummand_bound
    (R1 : ℝ → ℝ) (C : ℝ)
    (hC : ∀ y : ℝ, 0 < y → |R1 y| ≤ C / y ^ 2)
    (N m d q : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hq : 1 ≤ q) :
    |dirichletCoeff N m / (m : ℝ) *
        (dirichletCoeff N d * R1 (((d * q : ℕ) : ℝ) / (m : ℝ)))| ≤
      C * (|dirichletCoeff N m| * (m : ℝ)) *
        (|dirichletCoeff N d| / (d : ℝ) ^ 2) *
          (1 / (q : ℝ) ^ 2) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hratio :
      (((d * q : ℕ) : ℝ) / (m : ℝ)) = (d : ℝ) * (q : ℝ) / (m : ℝ) := by
    push_cast
    rfl
  have hypos : 0 < (((d * q : ℕ) : ℝ) / (m : ℝ)) := by
    rw [hratio]
    positivity
  have hR := hC _ hypos
  rw [abs_mul, abs_div, abs_of_pos hmpos, abs_mul]
  calc
    |dirichletCoeff N m| / (m : ℝ) *
          (|dirichletCoeff N d| *
            |R1 (((d * q : ℕ) : ℝ) / (m : ℝ))|) ≤
        |dirichletCoeff N m| / (m : ℝ) *
          (|dirichletCoeff N d| *
            (C / ((((d * q : ℕ) : ℝ) / (m : ℝ)) ^ 2))) := by
      gcongr
    _ = C * (|dirichletCoeff N m| * (m : ℝ)) *
        (|dirichletCoeff N d| / (d : ℝ) ^ 2) *
          (1 / (q : ℝ) ^ 2) := by
      rw [hratio]
      field_simp [ne_of_gt hmpos, ne_of_gt hdpos, ne_of_gt hqpos]

/-- Quadratic decay of `R1` bounds the far complementary sector by the
explicit separable finite majorant.  The result is uniform in the hyperbolic
constraint `d*q ≤ J`, which is discarded only in this already-far range. -/
theorem abs_ehmFiniteComplementaryDivisorFarOuter_le_majorant
    (R1 : ℝ → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ y : ℝ, 0 < y → |R1 y| ≤ C / y ^ 2)
    (N D J : ℕ) :
    |ehmFiniteComplementaryDivisorFarOuter R1 N D J| ≤
      ehmComplementaryDivisorFarMajorant C N D J := by
  classical
  unfold ehmFiniteComplementaryDivisorFarOuter
    ehmFiniteComplementaryDivisorFarSum
    ehmComplementaryDivisorFarMajorant
  calc
    |∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) *
        ∑ d ∈ Finset.Icc (D + 1) J, ∑ q ∈ Finset.Icc 1 J,
          if d * q ≤ J then
            dirichletCoeff N d *
              R1 (((d * q : ℕ) : ℝ) * (1 / (m : ℝ)))
          else 0| ≤
        ∑ m ∈ Finset.Icc 1 N,
          |dirichletCoeff N m / (m : ℝ) *
            ∑ d ∈ Finset.Icc (D + 1) J, ∑ q ∈ Finset.Icc 1 J,
              if d * q ≤ J then
                dirichletCoeff N d *
                  R1 (((d * q : ℕ) : ℝ) * (1 / (m : ℝ)))
              else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 N,
        ∑ d ∈ Finset.Icc (D + 1) J, ∑ q ∈ Finset.Icc 1 J,
          C * (|dirichletCoeff N m| * (m : ℝ)) *
            (|dirichletCoeff N d| / (d : ℝ) ^ 2) *
              (1 / (q : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro m hmMem
      have hm : 1 ≤ m := (Finset.mem_Icc.mp hmMem).1
      rw [abs_mul]
      calc
        |dirichletCoeff N m / (m : ℝ)| *
            |∑ d ∈ Finset.Icc (D + 1) J, ∑ q ∈ Finset.Icc 1 J,
              if d * q ≤ J then
                dirichletCoeff N d *
                  R1 (((d * q : ℕ) : ℝ) * (1 / (m : ℝ)))
              else 0| ≤
          |dirichletCoeff N m / (m : ℝ)| *
            ∑ d ∈ Finset.Icc (D + 1) J,
              |∑ q ∈ Finset.Icc 1 J,
                if d * q ≤ J then
                  dirichletCoeff N d *
                    R1 (((d * q : ℕ) : ℝ) * (1 / (m : ℝ)))
                else 0| := by
            gcongr
            exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ |dirichletCoeff N m / (m : ℝ)| *
            ∑ d ∈ Finset.Icc (D + 1) J,
              ∑ q ∈ Finset.Icc 1 J,
                |if d * q ≤ J then
                  dirichletCoeff N d *
                    R1 (((d * q : ℕ) : ℝ) * (1 / (m : ℝ)))
                else 0| := by
            gcongr with d hdMem
            exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro d hdMem
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro q hqMem
          have hd : 1 ≤ d := by
            have := (Finset.mem_Icc.mp hdMem).1
            omega
          have hq : 1 ≤ q := (Finset.mem_Icc.mp hqMem).1
          by_cases hdq : d * q ≤ J
          · simp only [hdq, if_true, abs_mul]
            have harg :
                (((d * q : ℕ) : ℝ) * (1 / (m : ℝ))) =
                  ((d * q : ℕ) : ℝ) / (m : ℝ) := by ring
            rw [harg]
            simpa [abs_mul, abs_div, abs_of_pos (by exact_mod_cast
              (lt_of_lt_of_le Nat.zero_lt_one hm) : (0 : ℝ) < m)] using
              farSummand_bound R1 C hC N m d q hm hd hq
          · simp only [hdq, if_false, abs_zero]
            have hnonneg :
                0 ≤ C * (|dirichletCoeff N m| * (m : ℝ)) *
                  (|dirichletCoeff N d| / (d : ℝ) ^ 2) *
                    (1 / (q : ℝ) ^ 2) := by positivity
            simpa only [mul_zero] using hnonneg

/-- Concrete far-sector bound for Ehm's elementary `R₁`, with the proved
constant `8`. -/
theorem abs_ehmFiniteComplementaryDivisorFarOuter_ehmR1_le
    (N D J : ℕ) :
    |ehmFiniteComplementaryDivisorFarOuter ehmR1 N D J| ≤
      ehmComplementaryDivisorFarMajorant 8 N D J := by
  exact abs_ehmFiniteComplementaryDivisorFarOuter_le_majorant
    ehmR1 8 (by norm_num) ehmConcreteR1QuadraticDecay.bound N D J

/-- The completed boundary with only the signed near complementary sector
removed.  This is the arithmetic core which remains after the far range is
handled by quadratic decay. -/
noncomputable def ehmFiniteComplementaryDivisorNearCore
    (R1 : ℝ → ℝ) (N D J : ℕ) : ℝ :=
  ehmFiniteFullVonMangoldtTransformOuter R1 N J -
    ehmFiniteComplementaryDivisorNearOuter R1 N D J +
      ehmCoupledRemainder N

/-- Exact reduction of the full coupled boundary to its signed near core
minus the far complementary sector. -/
theorem ehmFiniteCoupledBoundaryExpression_eq_nearCore_sub_far
    (R1 : ℝ → ℝ) (N D J : ℕ)
    (hN : 2 ≤ N) (hND : N ≤ D) (hDJ : D ≤ J) :
    ehmFiniteCoupledBoundaryExpression R1 N J =
      ehmFiniteComplementaryDivisorNearCore R1 N D J -
        ehmFiniteComplementaryDivisorFarOuter R1 N D J := by
  rw [ehmFiniteCoupledBoundaryExpression_eq_fullOuter_sub_complementary_add_remainder
    R1 N J hN (hND.trans hDJ),
    ehmFiniteComplementaryDivisorHyperbolicOuter_eq_near_add_far
      R1 N D J hND hDJ]
  unfold ehmFiniteComplementaryDivisorNearCore
  ring

/-- Unconditional near/far reduction for the concrete Ehm kernel.  Only the
near core remains signed; the discarded far sector is paid for by the
explicit quadratic-decay majorant. -/
theorem abs_ehmFiniteCoupledBoundaryExpression_le_nearCore_add_farMajorant
    (N D J : ℕ) (hN : 2 ≤ N) (hND : N ≤ D) (hDJ : D ≤ J) :
    |ehmFiniteCoupledBoundaryExpression ehmR1 N J| ≤
      |ehmFiniteComplementaryDivisorNearCore ehmR1 N D J| +
        ehmComplementaryDivisorFarMajorant 8 N D J := by
  rw [ehmFiniteCoupledBoundaryExpression_eq_nearCore_sub_far
    ehmR1 N D J hN hND hDJ]
  exact (abs_sub _ _).trans
    (add_le_add_right
      (abs_ehmFiniteComplementaryDivisorFarOuter_ehmR1_le N D J) _)

/-- A split research target for the concrete Ehm boundary.  The near core is
controlled only cofinally in the hyperbolic cutoff and retains all arithmetic
signs.  The far range is controlled uniformly by the explicit nonnegative
majorant supplied by quadratic decay. -/
structure EhmComplementaryNearFarCofinalControl where
  D : ℕ → ℕ
  D_ge : ∀ N : ℕ, N ≤ D N
  C_near : ℝ
  C_near_pos : 0 < C_near
  C_far : ℝ
  C_far_pos : 0 < C_far
  α : ℝ
  α_pos : 0 < α
  near_cofinal_bound : ∀ N : ℕ, 2 ≤ N → ∀ J₀ : ℕ,
    ∃ J : ℕ, max (D N) J₀ ≤ J ∧
      |ehmFiniteComplementaryDivisorNearCore ehmR1 N (D N) J| ≤
        C_near / (Real.log (N : ℝ)) ^ α
  far_bound : ∀ N : ℕ, 2 ≤ N → ∀ J : ℕ, D N ≤ J →
    ehmComplementaryDivisorFarMajorant 8 N (D N) J ≤
      C_far / (Real.log (N : ℝ)) ^ α

/-- The split near/far target supplies the cofinal coupled-boundary control
used by the rational Ehm series bridge. -/
noncomputable def EhmComplementaryNearFarCofinalControl.toCofinal
    (H : EhmComplementaryNearFarCofinalControl) :
    EhmAutocorrelationCofinalCoupledBoundaryControl where
  C := H.C_near + H.C_far
  C_pos := by linarith [H.C_near_pos, H.C_far_pos]
  α := H.α
  α_pos := H.α_pos
  cofinal_bound N hN J₀ := by
    rcases H.near_cofinal_bound N hN J₀ with ⟨J, hJ, hnear⟩
    have hND : N ≤ H.D N := H.D_ge N
    have hDJ : H.D N ≤ J := (Nat.le_max_left (H.D N) J₀).trans hJ
    have hNJ₀ : max N J₀ ≤ J := by
      apply max_le
      · exact hND.trans hDJ
      · exact (Nat.le_max_right (H.D N) J₀).trans hJ
    refine ⟨J, hNJ₀, ?_⟩
    calc
      |ehmFiniteCoupledBoundaryExpression ehmR1 N J| ≤
          |ehmFiniteComplementaryDivisorNearCore ehmR1 N (H.D N) J| +
            ehmComplementaryDivisorFarMajorant 8 N (H.D N) J :=
        abs_ehmFiniteCoupledBoundaryExpression_le_nearCore_add_farMajorant
          N (H.D N) J hN hND hDJ
      _ ≤ H.C_near / (Real.log (N : ℝ)) ^ H.α +
          H.C_far / (Real.log (N : ℝ)) ^ H.α :=
        add_le_add hnear (H.far_bound N hN J hDJ)
      _ = (H.C_near + H.C_far) / (Real.log (N : ℝ)) ^ H.α := by ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmComplementarySector
