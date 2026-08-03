import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPoincare

/-!
# BT1-C1: the H15 big-cell seed and the cusp-invariance stop test

Motohashi's big-cell Poincare seed is periodic in its first unipotent
coordinate.  The Kloosterman sum appears only *after* orbiting this seed, so
the correct local object is the H15 coefficient with the Kloosterman factor
removed.

This file performs that removal exactly and proves the cusp transformation
law for the resulting finite-modulus/infinite-divisor seed.  In particular,
the joint dependence of the completed coefficient on `(q,m)` does not break
cusp invariance: it is independent of the translated coordinate, while
`m.val` is an integral Fourier frequency.

The result is deliberately not called Kuznetsov admissibility.  A trace
formula still requires a single smooth radial interpolation of all modulus
samples with uniform seminorm control.  The final structure records that
remaining BT1-C2 gate explicitly.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiCuspInvariance

open Complex
open scoped BigOperators ContDiff
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15NumeratorCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloosterman
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloostermanCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSeed
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPoincare
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries

/-- The three real coordinates of Motohashi's open Bruhat cell.  The present
stop test uses only the two unipotent variables and the radial variable; no
claim that this is already a formal model of `PSL(2, ℝ)` is made. -/
structure H15MotohashiBigCellCoordinates where
  x₁ : ℝ
  x₂ : ℝ
  u : ℝ

/-- Translation by the integer cusp subgroup in the first unipotent
coordinate. -/
def h15CuspTranslate (k : ℤ) (z : H15MotohashiBigCellCoordinates) :
    H15MotohashiBigCellCoordinates where
  x₁ := z.x₁ + k
  x₂ := z.x₂
  u := z.u

@[simp]
theorem h15CuspTranslate_zero (z : H15MotohashiBigCellCoordinates) :
    h15CuspTranslate 0 z = z := by
  cases z
  simp [h15CuspTranslate]

@[simp]
theorem h15CuspTranslate_add (k l : ℤ)
    (z : H15MotohashiBigCellCoordinates) :
    h15CuspTranslate (k + l) z =
      h15CuspTranslate k (h15CuspTranslate l z) := by
  cases z
  simp only [h15CuspTranslate, Int.cast_add]
  congr 1
  · abel

/-- The additive character with an integral frequency. -/
noncomputable def h15IntegralFourierPhase (r : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((r : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) * x)

/-- Integral Fourier modes are invariant under integer cusp translation. -/
@[simp]
theorem h15IntegralFourierPhase_add_int (r k : ℤ) (x : ℝ) :
    h15IntegralFourierPhase r (x + k) = h15IntegralFourierPhase r x := by
  unfold h15IntegralFourierPhase
  rw [show (((x + k : ℝ) : ℂ)) = (x : ℂ) + (k : ℂ) by
    push_cast
    rfl]
  rw [show (r : ℂ) * ((2 * Real.pi : ℂ) * I) * ((x : ℂ) + k) =
      (r : ℂ) * ((2 * Real.pi : ℂ) * I) * x +
        (r * k : ℤ) * ((2 * Real.pi : ℂ) * I) by
    push_cast
    ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- The H15 arithmetic coefficient before the Kloosterman orbit is taken.
This is the object that can occur as a Fourier coefficient of a geometric
big-cell seed. -/
noncomputable def h15MotohashiPreKloostermanCoefficient
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) : ℂ :=
  estermannDivisorCoeff n * (q : ℂ)⁻¹ *
      inverseCoordinateFourierCoefficient
        (h15UnitNumeratorWeight N g q) m *
    ((2 * Real.pi : ℂ) * h15MotohashiSignedKernel sign η c q n)

/-- Exact pre-orbit factorization: the already formalized arithmetic seed is
the geometric coefficient times its Kloosterman orbit. -/
theorem h15MotohashiArithmeticSeed_eq_preKloosterman_mul
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) :
    h15MotohashiArithmeticSeed N g q sign η c n m =
      h15MotohashiPreKloostermanCoefficient N g q sign η c n m *
        kloostermanSum (h15MotohashiSignedFrequency sign q n) m := by
  unfold h15MotohashiArithmeticSeed h15MotohashiPreKloostermanCoefficient
  ring

/-- The signed second unipotent frequency. -/
def h15MotohashiSignedIntegerFrequency
    (sign : H15MotohashiSign) (n : ℕ) : ℤ :=
  match sign with
  | .same => n
  | .opposite => -(n : ℤ)

/-- One Fourier term of the candidate big-cell seed.  `radial q` is kept
abstract because constructing it with *uniform* Motohashi seminorms is the
next analytic gate. -/
noncomputable def h15MotohashiBigCellFourierTerm
    (radial : ℕ → ℝ → ℂ)
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q)
    (z : H15MotohashiBigCellCoordinates) : ℂ :=
  h15MotohashiPreKloostermanCoefficient N g q sign η c n m *
    radial q z.u *
    h15IntegralFourierPhase (m.val : ℤ) z.x₁ *
    h15IntegralFourierPhase (h15MotohashiSignedIntegerFrequency sign n) z.x₂

/-- **BT1-C1 stop test, one mode.**  Arbitrary joint `(q,m)` dependence of
the H15 coefficient is compatible with the integer cusp law. -/
theorem h15MotohashiBigCellFourierTerm_cusp_invariant
    (radial : ℕ → ℝ → ℂ)
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) (k : ℤ)
    (z : H15MotohashiBigCellCoordinates) :
    h15MotohashiBigCellFourierTerm radial N g q sign η c n m
        (h15CuspTranslate k z) =
      h15MotohashiBigCellFourierTerm radial N g q sign η c n m z := by
  simp [h15MotohashiBigCellFourierTerm, h15CuspTranslate]

/-- One sign and one modulus row of the candidate seed. -/
noncomputable def h15MotohashiBigCellRow
    (radial : ℕ → ℝ → ℂ)
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (z : H15MotohashiBigCellCoordinates) : ℂ :=
  ∑' n : ℕ, ∑ m : ZMod q,
    h15MotohashiBigCellFourierTerm radial N g q sign η c n m z

/-- Cusp invariance survives both the finite completed-frequency orbit and
the infinite divisor-frequency series.  This equality does not use the
totalized value of a divergent series: it is termwise. -/
theorem h15MotohashiBigCellRow_cusp_invariant
    (radial : ℕ → ℝ → ℂ)
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (k : ℤ) (z : H15MotohashiBigCellCoordinates) :
    h15MotohashiBigCellRow radial N g q sign η c
        (h15CuspTranslate k z) =
      h15MotohashiBigCellRow radial N g q sign η c z := by
  apply tsum_congr
  intro n
  apply Finset.sum_congr rfl
  intro m _
  exact h15MotohashiBigCellFourierTerm_cusp_invariant
    radial N g q sign η c n m k z

/-- The two functional-equation signs in one row. -/
noncomputable def h15MotohashiBigCellTwoSignRow
    (radial : ℕ → ℝ → ℂ)
    (N g q : ℕ) [NeZero q] (η c : ℝ)
    (z : H15MotohashiBigCellCoordinates) : ℂ :=
  h15MotohashiBigCellRow radial N g q .same η c z +
    h15MotohashiBigCellRow radial N g q .opposite η c z

theorem h15MotohashiBigCellTwoSignRow_cusp_invariant
    (radial : ℕ → ℝ → ℂ)
    (N g q : ℕ) [NeZero q] (η c : ℝ)
    (k : ℤ) (z : H15MotohashiBigCellCoordinates) :
    h15MotohashiBigCellTwoSignRow radial N g q η c
        (h15CuspTranslate k z) =
      h15MotohashiBigCellTwoSignRow radial N g q η c z := by
  simp only [h15MotohashiBigCellTwoSignRow]
  rw [h15MotohashiBigCellRow_cusp_invariant,
    h15MotohashiBigCellRow_cusp_invariant]

/-- Finite H15 sum over gcd slices and moduli. -/
noncomputable def h15MotohashiBigCellSeed
    (radial : ℕ → ℝ → ℂ) (N : ℕ) (η c : ℝ)
    (z : H15MotohashiBigCellCoordinates) : ℂ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ q ∈ Finset.Icc 2 (N / g),
      if hq : 0 < q then
        @h15MotohashiBigCellTwoSignRow radial N g q
          ⟨Nat.ne_of_gt hq⟩ η c z
      else 0

/-- **BT1-C1 stop test, complete finite H15 family.**  The candidate
pre-Kloosterman big-cell seed obeys the cusp transformation law exactly. -/
theorem h15MotohashiBigCellSeed_cusp_invariant
    (radial : ℕ → ℝ → ℂ) (N : ℕ) (η c : ℝ)
    (k : ℤ) (z : H15MotohashiBigCellCoordinates) :
    h15MotohashiBigCellSeed radial N η c (h15CuspTranslate k z) =
      h15MotohashiBigCellSeed radial N η c z := by
  classical
  unfold h15MotohashiBigCellSeed
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro q _
  split_ifs with hq
  · exact @h15MotohashiBigCellTwoSignRow_cusp_invariant radial N g q
      ⟨Nat.ne_of_gt hq⟩ η c k z
  · rfl

/-- Radial sample used by the Motohashi/Kloosterman expansion: modulus `q`
is read at the positive radial coordinate `q²`. -/
def h15MotohashiRadialSample (q : ℕ) : ℝ := (q : ℝ) ^ 2

/-- The radial interpolation part of the seed realization. -/
structure H15MotohashiRadialInterpolationData where
  radial : ℕ → ℝ → ℂ
  sample_one : ∀ q : ℕ,
    radial q (h15MotohashiRadialSample q) = 1
  sample_zero : ∀ q r : ℕ, q ≠ r →
    radial q (h15MotohashiRadialSample r) = 0
  smooth : ∀ q : ℕ, ContDiff ℝ ∞ (radial q)
  compact_support : ∀ q : ℕ, HasCompactSupport (radial q)

/-- A fixed-width smooth bump centered at the Motohashi sample `q²`. -/
noncomputable def h15MotohashiRadialBump (q : ℕ) :
    ContDiffBump (h15MotohashiRadialSample q) where
  rIn := 1 / 4
  rOut := 1 / 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Explicit smooth modulus selector.  Distinct square samples are at least
one unit apart, so fixed radius `1/3` separates all of them. -/
noncomputable def h15MotohashiRadialSelector (q : ℕ) (u : ℝ) : ℂ :=
  (h15MotohashiRadialBump q u : ℝ)

@[simp]
theorem h15MotohashiRadialSelector_sample_self (q : ℕ) :
    h15MotohashiRadialSelector q (h15MotohashiRadialSample q) = 1 := by
  unfold h15MotohashiRadialSelector
  norm_cast
  apply ContDiffBump.one_of_mem_closedBall
  exact Metric.mem_closedBall_self (h15MotohashiRadialBump q).rIn_pos.le

theorem h15MotohashiRadialSelector_sample_ne (q r : ℕ) (hqr : q ≠ r) :
    h15MotohashiRadialSelector q (h15MotohashiRadialSample r) = 0 := by
  unfold h15MotohashiRadialSelector
  norm_cast
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq]
  rcases lt_or_gt_of_ne hqr with hlt | hgt
  · have hstep : (q : ℝ) + 1 ≤ (r : ℝ) := by
      exact_mod_cast (Nat.add_one_le_iff.mpr hlt)
    have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    have hdiff : (1 : ℝ) ≤
        h15MotohashiRadialSample r - h15MotohashiRadialSample q := by
      unfold h15MotohashiRadialSample
      nlinarith
    rw [abs_of_nonneg (by linarith :
      0 ≤ h15MotohashiRadialSample r - h15MotohashiRadialSample q)]
    norm_num [h15MotohashiRadialBump]
    linarith
  · have hstep : (r : ℝ) + 1 ≤ (q : ℝ) := by
      exact_mod_cast (Nat.add_one_le_iff.mpr hgt)
    have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have hdiff : (1 : ℝ) ≤
        h15MotohashiRadialSample q - h15MotohashiRadialSample r := by
      unfold h15MotohashiRadialSample
      nlinarith
    rw [abs_of_nonpos (by linarith :
      h15MotohashiRadialSample r - h15MotohashiRadialSample q ≤ 0)]
    norm_num [h15MotohashiRadialBump]
    linarith

theorem h15MotohashiRadialSelector_smooth (q : ℕ) :
    ContDiff ℝ ∞ (h15MotohashiRadialSelector q) := by
  exact Complex.ofRealCLM.contDiff.comp (h15MotohashiRadialBump q).contDiff

theorem h15MotohashiRadialSelector_hasCompactSupport (q : ℕ) :
    HasCompactSupport (h15MotohashiRadialSelector q) := by
  exact (h15MotohashiRadialBump q).hasCompactSupport.comp_left rfl

/-- Smooth radial interpolation is available unconditionally; it is not the
source of a BT1 obstruction. -/
noncomputable def h15MotohashiRadialInterpolation :
    H15MotohashiRadialInterpolationData where
  radial := h15MotohashiRadialSelector
  sample_one := h15MotohashiRadialSelector_sample_self
  sample_zero := h15MotohashiRadialSelector_sample_ne
  smooth := h15MotohashiRadialSelector_smooth
  compact_support := h15MotohashiRadialSelector_hasCompactSupport

/-- The remaining analytic gate after BT1-C1.  The seminorm is an *external,
fixed* Motohashi/Kirillov seminorm, so it cannot be chosen to be zero by an
inhabitant.  The bound is imposed on the complete H15 seed, not merely on its
radial selector. -/
structure H15MotohashiBigCellSeminormControl
    (R : H15MotohashiRadialInterpolationData)
    (p : Seminorm ℂ (H15MotohashiBigCellCoordinates → ℂ))
    (η c : ℝ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  uniform_seed_bound : ∀ N : ℕ,
    p (h15MotohashiBigCellSeed R.radial N η c) ≤ C

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiCuspInvariance
