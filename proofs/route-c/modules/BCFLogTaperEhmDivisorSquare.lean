import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Square summability of Ehm's divisor coefficients

Ehm's Fourier coefficient calculation produces the sequence
`Nat.divisors.card / n`.  This module proves its square summability without
using an asymptotic estimate for the divisor summatory function.

For two divisors `d,e ∣ n`, put

`g = gcd d e`, `a = d/g`, `b = e/g`, and `c = n/lcm d e`.

Then `g*a*b*c = n`, and the map `(n,d,e) ↦ (g,a,b,c)` is injective.  Thus the
series of squared divisor counts is dominated by the fourfold product of the
convergent reciprocal-square series.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmDivisorSquare

open scoped BigOperators

private abbrev DivisorPairSigma :=
  Σ n : ℕ+, ({d : ℕ // d ∈ n.val.divisors} × {e : ℕ // e ∈ n.val.divisors})

private abbrev FourPNat := (ℕ+ × ℕ+) × (ℕ+ × ℕ+)

private def divisorPairToFour : DivisorPairSigma → FourPNat := fun x =>
  let n := x.1.val
  let d := x.2.1.val
  let e := x.2.2.val
  let g := Nat.gcd d e
  let l := Nat.lcm d e
  ((⟨g, Nat.gcd_pos_of_pos_left e
        (Nat.pos_of_mem_divisors x.2.1.property)⟩,
    ⟨d / g, Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_mem_divisors x.2.1.property)
          (Nat.gcd_dvd_left d e))
        (Nat.gcd_pos_of_pos_left e
          (Nat.pos_of_mem_divisors x.2.1.property))⟩),
   (⟨e / g, Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_mem_divisors x.2.2.property)
          (Nat.gcd_dvd_right d e))
        (Nat.gcd_pos_of_pos_left e
          (Nat.pos_of_mem_divisors x.2.1.property))⟩,
    ⟨n / l, Nat.div_pos
        (Nat.le_of_dvd x.1.property
          (Nat.lcm_dvd (Nat.dvd_of_mem_divisors x.2.1.property)
            (Nat.dvd_of_mem_divisors x.2.2.property)))
        (Nat.lcm_pos (Nat.pos_of_mem_divisors x.2.1.property)
          (Nat.pos_of_mem_divisors x.2.2.property))⟩))

private theorem summable_inv_sq_pnat :
    Summable (fun n : ℕ+ => (1 : ℝ) / (n : ℝ) ^ 2) := by
  simpa using
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).subtype
      (fun n : ℕ => 0 < n)

private theorem summable_fourWeight :
    Summable (fun x : FourPNat =>
      ((1 : ℝ) / (x.1.1 : ℝ) ^ 2) * ((1 : ℝ) / (x.1.2 : ℝ) ^ 2) *
      (((1 : ℝ) / (x.2.1 : ℝ) ^ 2) * ((1 : ℝ) / (x.2.2 : ℝ) ^ 2))) := by
  have hpair : Summable (fun x : ℕ+ × ℕ+ =>
      ((1 : ℝ) / (x.1 : ℝ) ^ 2) * ((1 : ℝ) / (x.2 : ℝ) ^ 2)) :=
    summable_inv_sq_pnat.mul_of_nonneg summable_inv_sq_pnat
      (fun _ => by positivity) (fun _ => by positivity)
  exact hpair.mul_of_nonneg hpair (fun _ => by positivity) (fun _ => by positivity)

private theorem gcd_div_div_mul_eq_lcm (d e : ℕ) (hd : 0 < d) :
    Nat.gcd d e * (d / Nat.gcd d e) * (e / Nat.gcd d e) = Nat.lcm d e := by
  let g := Nat.gcd d e
  have hg : 0 < g := Nat.gcd_pos_of_pos_left e hd
  apply Nat.eq_of_mul_eq_mul_left hg
  calc
    g * (g * (d / g) * (e / g)) =
        (g * (d / g)) * (g * (e / g)) := by ring
    _ = d * e := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d e),
        Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)]
    _ = g * Nat.lcm d e := (Nat.gcd_mul_lcm d e).symm

private theorem divisorPairToFour_product (x : DivisorPairSigma) :
    (divisorPairToFour x).1.1.val * (divisorPairToFour x).1.2.val *
      (divisorPairToFour x).2.1.val * (divisorPairToFour x).2.2.val = x.1.val := by
  let n := x.1.val
  let d := x.2.1.val
  let e := x.2.2.val
  let g := Nat.gcd d e
  let l := Nat.lcm d e
  have hd : 0 < d := Nat.pos_of_mem_divisors x.2.1.property
  have hl_dvd_n : l ∣ n :=
    Nat.lcm_dvd (Nat.dvd_of_mem_divisors x.2.1.property)
      (Nat.dvd_of_mem_divisors x.2.2.property)
  change g * (d / g) * (e / g) * (n / l) = n
  rw [gcd_div_div_mul_eq_lcm d e hd]
  exact Nat.mul_div_cancel' hl_dvd_n

private theorem divisorPairToFour_injective : Function.Injective divisorPairToFour := by
  rintro ⟨n, d, e⟩ ⟨n', d', e'⟩ h
  have hnval : n.val = n'.val := by
    rw [← divisorPairToFour_product ⟨n, d, e⟩,
      ← divisorPairToFour_product ⟨n', d', e'⟩, h]
  have hn : n = n' := PNat.coe_injective hnval
  subst n'
  have hg : (divisorPairToFour ⟨n, d, e⟩).1.1.val =
      (divisorPairToFour ⟨n, d', e'⟩).1.1.val := congrArg (fun z => z.1.1.val) h
  have ha : (divisorPairToFour ⟨n, d, e⟩).1.2.val =
      (divisorPairToFour ⟨n, d', e'⟩).1.2.val := congrArg (fun z => z.1.2.val) h
  have hb : (divisorPairToFour ⟨n, d, e⟩).2.1.val =
      (divisorPairToFour ⟨n, d', e'⟩).2.1.val := congrArg (fun z => z.2.1.val) h
  dsimp [divisorPairToFour] at hg ha hb
  have hdval : d.val = d'.val := by
    calc
      d.val = Nat.gcd d.val e.val * (d.val / Nat.gcd d.val e.val) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_left d.val e.val)).symm
      _ = Nat.gcd d'.val e'.val * (d'.val / Nat.gcd d'.val e'.val) :=
        congrArg₂ (· * ·) hg ha
      _ = d'.val := Nat.mul_div_cancel' (Nat.gcd_dvd_left d'.val e'.val)
  have heval : e.val = e'.val := by
    calc
      e.val = Nat.gcd d.val e.val * (e.val / Nat.gcd d.val e.val) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_right d.val e.val)).symm
      _ = Nat.gcd d'.val e'.val * (e'.val / Nat.gcd d'.val e'.val) :=
        congrArg₂ (· * ·) hg hb
      _ = e'.val := Nat.mul_div_cancel' (Nat.gcd_dvd_right d'.val e'.val)
  have hdsub : d = d' := Subtype.ext hdval
  have hesub : e = e' := Subtype.ext heval
  subst d'
  subst e'
  rfl

private theorem fourWeight_divisorPairToFour (x : DivisorPairSigma) :
    ((1 : ℝ) / ((divisorPairToFour x).1.1 : ℝ) ^ 2) *
        ((1 : ℝ) / ((divisorPairToFour x).1.2 : ℝ) ^ 2) *
        (((1 : ℝ) / ((divisorPairToFour x).2.1 : ℝ) ^ 2) *
          ((1 : ℝ) / ((divisorPairToFour x).2.2 : ℝ) ^ 2)) =
      (1 : ℝ) / (x.1 : ℝ) ^ 2 := by
  have hprod := congrArg (fun z : ℕ => (z : ℝ)) (divisorPairToFour_product x)
  simp only [Nat.cast_mul] at hprod
  have h1 : ((divisorPairToFour x).1.1 : ℝ) ≠ 0 := by positivity
  have h2 : ((divisorPairToFour x).1.2 : ℝ) ≠ 0 := by positivity
  have h3 : ((divisorPairToFour x).2.1 : ℝ) ≠ 0 := by positivity
  have h4 : ((divisorPairToFour x).2.2 : ℝ) ≠ 0 := by positivity
  have hn : (x.1 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [hprod]

private theorem summable_divisorPairSigma_inv_sq :
    Summable (fun x : DivisorPairSigma => (1 : ℝ) / (x.1 : ℝ) ^ 2) := by
  have h := summable_fourWeight.comp_injective divisorPairToFour_injective
  exact h.congr (fun x => fourWeight_divisorPairToFour x)

/-- The positive-index version of square summability for the divisor-count
Fourier coefficients. -/
theorem divisorFunctionSquareSummable_pnat :
    Summable (fun n : ℕ+ =>
      ((n.val.divisors.card : ℝ) ^ 2) / (n : ℝ) ^ 2) := by
  let f : DivisorPairSigma → ℝ := fun x => (1 : ℝ) / (x.1 : ℝ) ^ 2
  have hf : Summable f := summable_divisorPairSigma_inv_sq
  have hout := ((summable_sigma_of_nonneg (f := f) (fun _ => by positivity)).mp hf).2
  simpa [f, tsum_fintype, div_eq_mul_inv, pow_two] using hout

/-- A natural-indexed form of the same theorem.  The shift is essential:
the analytic series starts at `m = 1`, whereas a raw natural-number
denominator has a spurious zero index. -/
theorem divisorFunctionSquareSummable :
    Summable (fun m : ℕ =>
      ((m + 1).divisors.card : ℝ) ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2) := by
  have h := (Equiv.pnatEquivNat.symm.summable_iff).2
    divisorFunctionSquareSummable_pnat
  simpa only [Function.comp_def, Equiv.pnatEquivNat_symm_apply,
    Nat.succPNat_coe, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using h

end RH.Criteria.NymanBeurling.BCFLogTaperEhmDivisorSquare
