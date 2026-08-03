import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperMSTTPolynomialPhase

/-!
# Polynomial approximation of Ehm reciprocal phases

This module gives an exact finite Taylor identity for `A / m` around a
positive block base `x`, packages the Taylor part as a real polynomial in
`m`, and transfers the exact remainder to a unit-circle phase bound.

It is the algebraic bridge needed before applying a polynomial-phase
Möbius estimate to the low-product Ehm rows.  No asymptotic choice of block
length or Taylor degree is made here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmReciprocalTaylor

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperMSTTPolynomialPhase

/-! ## Exact reciprocal Taylor identity -/

/-- Taylor polynomial value for `A/(x+r)`, through degree `K` in `r`. -/
noncomputable def reciprocalTaylorValue
    (A x : ℝ) (K : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1),
    (-1 : ℝ) ^ j * A * r ^ j / x ^ (j + 1)

/-- Exact remainder after truncating `A/(x+r)` at degree `K`. -/
noncomputable def reciprocalTaylorRemainder
    (A x : ℝ) (K : ℕ) (r : ℝ) : ℝ :=
  (-1 : ℝ) ^ (K + 1) * A * r ^ (K + 1) /
    (x ^ (K + 1) * (x + r))

private theorem reciprocalTaylorValue_succ
    (A x : ℝ) (K : ℕ) (r : ℝ) :
    reciprocalTaylorValue A x (K + 1) r =
      reciprocalTaylorValue A x K r +
        (-1 : ℝ) ^ (K + 1) * A * r ^ (K + 1) /
          x ^ (K + 2) := by
  unfold reciprocalTaylorValue
  rw [show K + 1 + 1 = (K + 1) + 1 by omega,
    Finset.sum_range_succ]

private theorem reciprocalTaylorRemainder_step
    (A x : ℝ) (K : ℕ) (r : ℝ) (hx : x ≠ 0) (hxr : x + r ≠ 0) :
    reciprocalTaylorRemainder A x K r =
      (-1 : ℝ) ^ (K + 1) * A * r ^ (K + 1) / x ^ (K + 2) +
        reciprocalTaylorRemainder A x (K + 1) r := by
  unfold reciprocalTaylorRemainder
  field_simp [hx, hxr]
  ring

/-- Finite geometric expansion of the reciprocal function. -/
theorem reciprocal_eq_taylor_add_remainder
    (A x r : ℝ) (K : ℕ) (hx : x ≠ 0) (hxr : x + r ≠ 0) :
    A / (x + r) =
      reciprocalTaylorValue A x K r +
        reciprocalTaylorRemainder A x K r := by
  induction K with
  | zero =>
      simp [reciprocalTaylorValue, reciprocalTaylorRemainder]
      field_simp [hx, hxr]
      ring
  | succ K ih =>
      rw [ih]
      rw [reciprocalTaylorRemainder_step A x K r hx hxr,
        reciprocalTaylorValue_succ]
      ring

/-- Uniform elementary remainder bound on `0 <= r <= R`. -/
theorem abs_reciprocalTaylorRemainder_le
    (A x r R : ℝ) (K : ℕ)
    (hx : 0 < x) (hr : 0 ≤ r) (hrR : r ≤ R) :
    |reciprocalTaylorRemainder A x K r| ≤
      |A| * R ^ (K + 1) / x ^ (K + 2) := by
  have hR : 0 ≤ R := hr.trans hrR
  have hxr : 0 < x + r := add_pos_of_pos_of_nonneg hx hr
  unfold reciprocalTaylorRemainder
  rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_pow, abs_of_nonneg hr, abs_mul, abs_pow,
    abs_of_pos hx, abs_of_pos hxr]
  have hxpow : 0 < x ^ (K + 1) := pow_pos hx _
  have hxpow' : 0 < x ^ (K + 2) := pow_pos hx _
  have hden : x ^ (K + 2) ≤ x ^ (K + 1) * (x + r) := by
    rw [show K + 2 = (K + 1) + 1 by omega, pow_succ]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hr) hxpow.le
  gcongr

/-! ## Polynomial packaging -/

/-- The Taylor approximation as a polynomial in the original variable
`m`; its local coordinate is `m-x`. -/
noncomputable def reciprocalTaylorPolynomial
    (A x : ℝ) (K : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (K + 1),
    Polynomial.C (((-1 : ℝ) ^ j * A) / x ^ (j + 1)) *
      (Polynomial.X - Polynomial.C x) ^ j

theorem reciprocalTaylorPolynomial_eval
    (A x : ℝ) (K : ℕ) (m : ℝ) :
    (reciprocalTaylorPolynomial A x K).eval m =
      reciprocalTaylorValue A x K (m - x) := by
  classical
  unfold reciprocalTaylorPolynomial reciprocalTaylorValue
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X]
  ring

/-- The reciprocal Taylor polynomial has degree at most its truncation
order, uniformly in `A` and `x`. -/
theorem reciprocalTaylorPolynomial_natDegree_le
    (A x : ℝ) (K : ℕ) :
    (reciprocalTaylorPolynomial A x K).natDegree ≤ K := by
  classical
  unfold reciprocalTaylorPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjK : j ≤ K := by
    have := Finset.mem_range.mp hj
    omega
  calc
    (Polynomial.C (((-1 : ℝ) ^ j * A) / x ^ (j + 1)) *
        (Polynomial.X - Polynomial.C x) ^ j).natDegree ≤
      (Polynomial.C (((-1 : ℝ) ^ j * A) / x ^ (j + 1))).natDegree +
        ((Polynomial.X - Polynomial.C x) ^ j).natDegree :=
          Polynomial.natDegree_mul_le
    _ ≤ 0 + j * (Polynomial.X - Polynomial.C x).natDegree := by
      gcongr
      · rw [Polynomial.natDegree_C]
      · exact Polynomial.natDegree_pow_le
    _ ≤ 0 + j * 1 := by
      gcongr
      calc
        (Polynomial.X - Polynomial.C x).natDegree ≤
            max Polynomial.X.natDegree (Polynomial.C x).natDegree :=
          Polynomial.natDegree_sub_le _ _
        _ = 1 := by rw [Polynomial.natDegree_X, Polynomial.natDegree_C]; rfl
    _ ≤ K := by simpa using hjK

/-! ## Unit-circle stability -/

/-- The phase `exp(i*u)` for a real argument. -/
noncomputable def unitCirclePhase (u : ℝ) : ℂ :=
  Complex.exp ((u : ℂ) * Complex.I)

theorem norm_unitCirclePhase (u : ℝ) :
    ‖unitCirclePhase u‖ = 1 := by
  unfold unitCirclePhase
  exact Complex.norm_exp_ofReal_mul_I _

/-- The real unit-circle phase is one-Lipschitz. -/
theorem norm_unitCirclePhase_sub_le (u v : ℝ) :
    ‖unitCirclePhase u - unitCirclePhase v‖ ≤ |u - v| := by
  have hfactor :
      unitCirclePhase u - unitCirclePhase v =
        unitCirclePhase v *
          (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) := by
    unfold unitCirclePhase
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfactor, norm_mul, norm_unitCirclePhase, one_mul]
  simpa [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - v))

/-- Stability of the standard additive phase `e(t)=exp(2*pi*i*t)`. -/
theorem norm_additivePhase_sub_le (u v : ℝ) :
    ‖unitCirclePhase (2 * Real.pi * u) -
        unitCirclePhase (2 * Real.pi * v)‖ ≤
      2 * Real.pi * |u - v| := by
  calc
    ‖unitCirclePhase (2 * Real.pi * u) -
        unitCirclePhase (2 * Real.pi * v)‖ ≤
      |2 * Real.pi * u - 2 * Real.pi * v| :=
        norm_unitCirclePhase_sub_le _ _
    _ = 2 * Real.pi * |u - v| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

/-! ## Ehm reciprocal phase approximation -/

theorem ehmVaalerRationalPhase_eq_unitCirclePhase
    (h : ℤ) (n m : ℕ) :
    ehmVaalerRationalPhase h n 1 m =
      unitCirclePhase
        (2 * Real.pi * ((h : ℝ) * (n : ℝ) / (m : ℝ))) := by
  rw [ehmVaalerRationalPhase_eq_exp]
  unfold unitCirclePhase
  congr 2
  push_cast
  ring

theorem msttPolynomialPhase_reciprocalTaylorPolynomial
    (A x : ℝ) (K m : ℕ) :
    msttPolynomialPhase (reciprocalTaylorPolynomial A x K) m =
      unitCirclePhase
        (2 * Real.pi * reciprocalTaylorValue A x K ((m : ℝ) - x)) := by
  unfold msttPolynomialPhase unitCirclePhase
  rw [reciprocalTaylorPolynomial_eval]

/-- Explicit pointwise phase error on a reciprocal block. -/
theorem norm_ehmVaalerRationalPhase_sub_reciprocalTaylor_le
    (h : ℤ) (n m K : ℕ) (x : ℝ)
    (hx : x ≠ 0) (hm : m ≠ 0) :
    ‖ehmVaalerRationalPhase h n 1 m -
        msttPolynomialPhase
          (reciprocalTaylorPolynomial ((h : ℝ) * (n : ℝ)) x K) m‖ ≤
      2 * Real.pi *
        |reciprocalTaylorRemainder
          ((h : ℝ) * (n : ℝ)) x K ((m : ℝ) - x)| := by
  rw [ehmVaalerRationalPhase_eq_unitCirclePhase,
    msttPolynomialPhase_reciprocalTaylorPolynomial]
  have hmx : x + ((m : ℝ) - x) ≠ 0 := by
    simpa using (Nat.cast_ne_zero.mpr hm : (m : ℝ) ≠ 0)
  have hexact := reciprocal_eq_taylor_add_remainder
    ((h : ℝ) * (n : ℝ)) x ((m : ℝ) - x) K hx hmx
  have hden :
      ((h : ℝ) * (n : ℝ)) / (m : ℝ) =
        reciprocalTaylorValue ((h : ℝ) * (n : ℝ)) x K ((m : ℝ) - x) +
          reciprocalTaylorRemainder
            ((h : ℝ) * (n : ℝ)) x K ((m : ℝ) - x) := by
    simpa using hexact
  calc
    ‖unitCirclePhase
          (2 * Real.pi * ((h : ℝ) * (n : ℝ) / (m : ℝ))) -
        unitCirclePhase
          (2 * Real.pi * reciprocalTaylorValue
            ((h : ℝ) * (n : ℝ)) x K ((m : ℝ) - x))‖ ≤
      2 * Real.pi *
        |((h : ℝ) * (n : ℝ) / (m : ℝ)) -
          reciprocalTaylorValue
            ((h : ℝ) * (n : ℝ)) x K ((m : ℝ) - x)| :=
        norm_additivePhase_sub_le _ _
    _ = 2 * Real.pi *
        |reciprocalTaylorRemainder
          ((h : ℝ) * (n : ℝ)) x K ((m : ℝ) - x)| := by
      rw [hden]
      ring_nf

end RH.Criteria.NymanBeurling.BCFLogTaperEhmReciprocalTaylor
