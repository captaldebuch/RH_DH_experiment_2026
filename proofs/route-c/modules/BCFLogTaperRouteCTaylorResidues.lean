import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorLineMajorant

/-!
# Route C: the odd Taylor residues of the central Mellin integrand

Moving the defining contour of Bettin--Conrey's `g₀` to the left crosses the
negative odd integers `1 - 2 n`.  This file proves, directly from the zeta
and sine factors, that these points are genuine simple poles and computes
their coefficients.  After the factor two coming from the source
normalization `1 / (π i)`, the result is precisely the Bernoulli--zeta row in
Bettin--Conrey Theorem 2.

No contour-shift hypothesis or asymptotic estimate is used here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues

open Complex Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero

/-- The meromorphic integrand whose restriction to `Re s = -1/2` defines
`g₀` before multiplication by `1/π`. -/
noncomputable def bettinConreyGZeroMeromorphicIntegrand
    (u s : ℂ) : ℂ :=
  riemannZeta s * riemannZeta (1 - s) /
      Complex.sin ((Real.pi : ℂ) * s) * u ^ (-s)

/-- The `n`-th negative odd pole crossed by the Taylor contour shift. -/
def routeCTaylorPolePoint (n : ℕ) : ℂ :=
  1 - 2 * (n : ℂ)

theorem routeCTaylorPolePoint_ne_one (n : ℕ) (hn : 1 ≤ n) :
    routeCTaylorPolePoint n ≠ 1 := by
  unfold routeCTaylorPolePoint
  intro h
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  apply hn0
  linear_combination -h / 2

theorem one_sub_routeCTaylorPolePoint (n : ℕ) :
    1 - routeCTaylorPolePoint n = (2 * n : ℕ) := by
  unfold routeCTaylorPolePoint
  push_cast
  ring

theorem neg_routeCTaylorPolePoint (n : ℕ) (_hn : 1 ≤ n) :
    -routeCTaylorPolePoint n = ((2 * n - 1 : ℕ) : ℂ) := by
  unfold routeCTaylorPolePoint
  have hle : 1 ≤ 2 * n := by omega
  push_cast [Nat.cast_sub hle]
  ring

theorem sin_pi_mul_routeCTaylorPolePoint (n : ℕ) (_hn : 1 ≤ n) :
    Complex.sin ((Real.pi : ℂ) * routeCTaylorPolePoint n) = 0 := by
  rw [show (Real.pi : ℂ) * routeCTaylorPolePoint n =
      -(((n : ℕ) : ℂ) * (2 * (Real.pi : ℂ)) - (Real.pi : ℂ)) by
        unfold routeCTaylorPolePoint
        ring]
  rw [Complex.sin_neg, Complex.sin_nat_mul_two_pi_sub]
  simp

theorem cos_pi_mul_routeCTaylorPolePoint
    (n : ℕ) (_hn : 1 ≤ n) :
    Complex.cos ((Real.pi : ℂ) * routeCTaylorPolePoint n) = -1 := by
  rw [show (Real.pi : ℂ) * routeCTaylorPolePoint n =
      -(((n : ℕ) : ℂ) * (2 * (Real.pi : ℂ)) - (Real.pi : ℂ)) by
        unfold routeCTaylorPolePoint
        ring]
  rw [Complex.cos_neg, Complex.cos_nat_mul_two_pi_sub_pi]

/-- The sine denominator has slope `-π` at every crossed odd point. -/
theorem hasDerivAt_sin_pi_mul_routeCTaylorPolePoint
    (n : ℕ) (hn : 1 ≤ n) :
    HasDerivAt
      (fun s : ℂ => Complex.sin ((Real.pi : ℂ) * s))
      (-(Real.pi : ℂ)) (routeCTaylorPolePoint n) := by
  have hinner : HasDerivAt
      (fun s : ℂ => (Real.pi : ℂ) * s)
      (Real.pi : ℂ) (routeCTaylorPolePoint n) := by
    simpa [mul_comm] using
      (hasDerivAt_id (x := routeCTaylorPolePoint n)).const_mul
        (Real.pi : ℂ)
  convert (Complex.hasDerivAt_sin
    ((Real.pi : ℂ) * routeCTaylorPolePoint n)).comp
      (routeCTaylorPolePoint n) hinner using 1
  rw [cos_pi_mul_routeCTaylorPolePoint n hn]
  ring

/-- The reciprocal sine quotient has the exact local limit required for
the simple residue computation. -/
theorem tendsto_sub_pole_div_sin
    (n : ℕ) (hn : 1 ≤ n) :
    Tendsto
      (fun s : ℂ =>
        (s - routeCTaylorPolePoint n) /
          Complex.sin ((Real.pi : ℂ) * s))
      (nhdsWithin (routeCTaylorPolePoint n)
        ({routeCTaylorPolePoint n}ᶜ : Set ℂ))
      (𝓝 (-(1 / (Real.pi : ℂ)))) := by
  have hslope :=
    (hasDerivAt_sin_pi_mul_routeCTaylorPolePoint n hn).tendsto_slope
  have hslope' : Tendsto
      (fun s : ℂ =>
        Complex.sin ((Real.pi : ℂ) * s) /
          (s - routeCTaylorPolePoint n))
      (nhdsWithin (routeCTaylorPolePoint n)
        ({routeCTaylorPolePoint n}ᶜ : Set ℂ))
      (𝓝 (-(Real.pi : ℂ))) := by
    apply hslope.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsp : s ≠ routeCTaylorPolePoint n := by simpa using hs
    rw [slope_def_field,
      sin_pi_mul_routeCTaylorPolePoint n hn, sub_zero]
  have hpi : (-(Real.pi : ℂ)) ≠ 0 := by
    exact neg_ne_zero.mpr (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hinv := hslope'.inv₀ hpi
  convert hinv using 1
  · funext s
    simp only [inv_div]
  · field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The unnormalized residue of the central Mellin integrand at
`s = 1 - 2n`. -/
noncomputable def bettinConreyGZeroOddResidue
    (u : ℂ) (n : ℕ) : ℂ :=
  -riemannZeta (routeCTaylorPolePoint n) *
      riemannZeta (2 * n : ℕ) * u ^ (2 * n - 1) /
        (Real.pi : ℂ)

/-- Each negative odd point is a genuine simple pole with the displayed
residue.  This punctured-limit form is sufficient for the subsequent
finite subtraction construction. -/
theorem bettinConreyGZeroMeromorphicIntegrand_residue_limit
    (u : ℂ) (hu : u ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    Tendsto
      (fun s : ℂ =>
        (s - routeCTaylorPolePoint n) *
          bettinConreyGZeroMeromorphicIntegrand u s)
      (nhdsWithin (routeCTaylorPolePoint n)
        ({routeCTaylorPolePoint n}ᶜ : Set ℂ))
      (𝓝 (bettinConreyGZeroOddResidue u n)) := by
  let p := routeCTaylorPolePoint n
  have hp1 : p ≠ 1 := routeCTaylorPolePoint_ne_one n hn
  have hzetaLeft : Tendsto riemannZeta
      (nhdsWithin p ({p}ᶜ : Set ℂ))
      (𝓝 (riemannZeta p)) :=
    (differentiableAt_riemannZeta hp1).continuousAt.tendsto.mono_left
      inf_le_left
  have honep : 1 - p = (2 * n : ℕ) := one_sub_routeCTaylorPolePoint n
  have htwo_ne_one : (1 - p) ≠ 1 := by
    rw [honep]
    exact_mod_cast (by omega : 2 * n ≠ 1)
  have hzetaRight : Tendsto (fun s : ℂ => riemannZeta (1 - s))
      (nhdsWithin p ({p}ᶜ : Set ℂ))
      (𝓝 (riemannZeta (1 - p))) := by
    exact ((differentiableAt_riemannZeta htwo_ne_one).continuousAt.comp
      (by fun_prop)).tendsto.mono_left inf_le_left
  have hpow : Tendsto (fun s : ℂ => u ^ (-s))
      (nhdsWithin p ({p}ᶜ : Set ℂ))
      (𝓝 (u ^ (-p))) := by
    exact ((continuousAt_const_cpow hu).comp (by fun_prop)).tendsto.mono_left
      inf_le_left
  have hquot := tendsto_sub_pole_div_sin n hn
  have hlim := ((hzetaLeft.mul hzetaRight).mul hpow).mul hquot
  convert hlim using 1
  · funext s
    unfold bettinConreyGZeroMeromorphicIntegrand
    ring
  · rw [honep, neg_routeCTaylorPolePoint n hn, cpow_natCast]
    unfold bettinConreyGZeroOddResidue
    congr 1
    dsimp [p]
    ring


/-- Euler's even-zeta formula turns the analytic residue into exactly the
Bernoulli--zeta monomial printed in Bettin--Conrey's Taylor expansion. -/
theorem bettinConreyGZeroOddResidue_eq_bernoulli
    (u : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    bettinConreyGZeroOddResidue u n =
      (-1 : ℂ) ^ n * (((bernoulli (2 * n) : ℚ) : ℂ)) /
          (Nat.factorial (2 * n) : ℂ) *
        riemannZeta (routeCTaylorPolePoint n) *
          ((2 * Real.pi : ℂ) * u) ^ (2 * n - 1) := by
  rw [bettinConreyGZeroOddResidue]
  rw [show ((2 * n : ℕ) : ℂ) = (2 : ℂ) * (n : ℂ) by norm_num,
    riemannZeta_two_mul_nat (Nat.ne_zero_of_lt hn)]
  rw [pow_succ]
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsub : 2 * n - 1 + 1 = 2 * n := by omega
  field_simp [hpi]
  rw [show ((Real.pi : ℂ) * 2 * u) ^ (2 * n - 1) =
      (Real.pi : ℂ) ^ (2 * n - 1) *
        (2 : ℂ) ^ (2 * n - 1) * u ^ (2 * n - 1) by
          rw [mul_pow, mul_pow]]
  have hpiPow : (Real.pi : ℂ) * (Real.pi : ℂ) ^ (2 * n - 1) =
      (Real.pi : ℂ) ^ (2 * n) := by
    rw [mul_comm, ← pow_succ, hsub]
  rw [← hpiPow]
  ring

/-- The source contour has normalization `1/(π i)` rather than
`1/(2π i)`, so a crossed residue contributes twice the preceding value. -/
theorem two_mul_bettinConreyGZeroOddResidue
    (u : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    2 * bettinConreyGZeroOddResidue u n =
      2 * (-1 : ℂ) ^ n * (((bernoulli (2 * n) : ℚ) : ℂ)) /
          (Nat.factorial (2 * n) : ℂ) *
        riemannZeta (routeCTaylorPolePoint n) *
          ((2 * Real.pi : ℂ) * u) ^ (2 * n - 1) := by
  rw [bettinConreyGZeroOddResidue_eq_bernoulli u n hn]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues
