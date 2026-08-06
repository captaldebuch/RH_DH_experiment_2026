/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15BettinChandeeLedger
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A quantitative dyadic divisor-square bound

This file supplies the classical average estimate required by the H15
Bettin--Chandee coefficient ledger.  The proof is elementary.  A pair of
divisors `d,e ∣ n` is injected into the four positive factors

`gcd d e`, `d / gcd d e`, `e / gcd d e`, `n / lcm d e`.

Counting the last factor after the first three produces three harmonic sums,
and hence the expected `X * (1 + log X)^3` bound rather than a pointwise
divisor estimate.
-/

open scoped BigOperators

namespace NBMellinTools.NB12

private abbrev H15DivisorPairSigma (R : ℕ) :=
  Σ n : {n : ℕ // n ∈ h15BettinChandeeNatBlock R},
    ({d : ℕ // d ∈ n.val.divisors} × {e : ℕ // e ∈ n.val.divisors})

private abbrev H15FourPNat := (ℕ+ × ℕ+) × (ℕ+ × ℕ+)

private def h15DivisorPairToFour {R : ℕ} :
    H15DivisorPairSigma R → H15FourPNat := fun x =>
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
        (Nat.le_of_dvd (Nat.pos_of_ne_zero
            (Nat.ne_zero_of_mem_divisors x.2.1.property))
          (Nat.lcm_dvd (Nat.dvd_of_mem_divisors x.2.1.property)
            (Nat.dvd_of_mem_divisors x.2.2.property)))
        (Nat.lcm_pos (Nat.pos_of_mem_divisors x.2.1.property)
          (Nat.pos_of_mem_divisors x.2.2.property))⟩))

private theorem h15_gcd_div_div_mul_eq_lcm
    (d e : ℕ) (hd : 0 < d) :
    Nat.gcd d e * (d / Nat.gcd d e) * (e / Nat.gcd d e) =
      Nat.lcm d e := by
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

private theorem h15DivisorPairToFour_product {R : ℕ}
    (x : H15DivisorPairSigma R) :
    (h15DivisorPairToFour x).1.1.val *
      (h15DivisorPairToFour x).1.2.val *
      (h15DivisorPairToFour x).2.1.val *
      (h15DivisorPairToFour x).2.2.val = x.1.val := by
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
  rw [h15_gcd_div_div_mul_eq_lcm d e hd]
  exact Nat.mul_div_cancel' hl_dvd_n

private theorem h15DivisorPairToFour_injective {R : ℕ} :
    Function.Injective (h15DivisorPairToFour (R := R)) := by
  rintro ⟨n, d, e⟩ ⟨n', d', e'⟩ h
  have hnval : n.val = n'.val := by
    rw [← h15DivisorPairToFour_product ⟨n, d, e⟩,
      ← h15DivisorPairToFour_product ⟨n', d', e'⟩, h]
  have hn : n = n' := Subtype.ext hnval
  subst n'
  have hg : (h15DivisorPairToFour ⟨n, d, e⟩).1.1.val =
      (h15DivisorPairToFour ⟨n, d', e'⟩).1.1.val :=
    congrArg (fun z => z.1.1.val) h
  have ha : (h15DivisorPairToFour ⟨n, d, e⟩).1.2.val =
      (h15DivisorPairToFour ⟨n, d', e'⟩).1.2.val :=
    congrArg (fun z => z.1.2.val) h
  have hb : (h15DivisorPairToFour ⟨n, d, e⟩).2.1.val =
      (h15DivisorPairToFour ⟨n, d', e'⟩).2.1.val :=
    congrArg (fun z => z.2.1.val) h
  dsimp [h15DivisorPairToFour] at hg ha hb
  have hdval : d.val = d'.val := by
    calc
      d.val = Nat.gcd d.val e.val * (d.val / Nat.gcd d.val e.val) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_left d.val e.val)).symm
      _ = Nat.gcd d'.val e'.val *
          (d'.val / Nat.gcd d'.val e'.val) := congrArg₂ (· * ·) hg ha
      _ = d'.val :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left d'.val e'.val)
  have heval : e.val = e'.val := by
    calc
      e.val = Nat.gcd d.val e.val * (e.val / Nat.gcd d.val e.val) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_right d.val e.val)).symm
      _ = Nat.gcd d'.val e'.val *
          (e'.val / Nat.gcd d'.val e'.val) := congrArg₂ (· * ·) hg hb
      _ = e'.val :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right d'.val e'.val)
  exact Sigma.ext rfl (heq_of_eq (Prod.ext
    (Subtype.ext hdval) (Subtype.ext heval)))

private abbrev H15BoundedFourProduct (X : ℕ) :=
  {z : H15FourPNat // z.1.1.val * z.1.2.val * z.2.1.val * z.2.2.val ≤ X}

private def h15DivisorPairToBoundedFour {R : ℕ} :
    H15DivisorPairSigma R → H15BoundedFourProduct (2 * R) := fun x =>
  ⟨h15DivisorPairToFour x, by
    rw [h15DivisorPairToFour_product]
    exact (Finset.mem_Ico.mp x.1.property).2.le⟩

private theorem h15DivisorPairToBoundedFour_injective {R : ℕ} :
    Function.Injective (h15DivisorPairToBoundedFour (R := R)) := by
  intro x y h
  apply h15DivisorPairToFour_injective
  exact congrArg Subtype.val h

private abbrev H15SmallNat (X : ℕ) :=
  {n : ℕ // n ∈ Finset.Icc 1 X}

private abbrev H15TripleFiber (X : ℕ) :=
  Σ g : H15SmallNat X,
    Σ a : H15SmallNat X,
      Σ b : H15SmallNat X, Fin (X / (g.val * a.val * b.val))

private def h15BoundedFourToTripleFiber {X : ℕ} :
    H15BoundedFourProduct X → H15TripleFiber X := fun z => by
  let g := z.1.1.1.val
  let a := z.1.1.2.val
  let b := z.1.2.1.val
  let c := z.1.2.2.val
  let p := g * a * b
  have hg_le : g ≤ X := by
    exact (Nat.le_mul_of_pos_right g z.1.1.2.pos).trans
      ((Nat.le_mul_of_pos_right (g * a) z.1.2.1.pos).trans
        ((Nat.le_mul_of_pos_right (g * a * b) z.1.2.2.pos).trans z.2))
  have ha_le : a ≤ X := by
    have hga : a ≤ g * a := by
      rw [Nat.mul_comm]
      exact Nat.le_mul_of_pos_right a z.1.1.1.pos
    exact hga.trans
      ((Nat.le_mul_of_pos_right (g * a) z.1.2.1.pos).trans
        ((Nat.le_mul_of_pos_right (g * a * b) z.1.2.2.pos).trans z.2))
  have hb_le : b ≤ X := by
    have hgb : b ≤ g * b := by
      rw [Nat.mul_comm]
      exact Nat.le_mul_of_pos_right b z.1.1.1.pos
    have hgab : g * b ≤ g * a * b := by
      rw [Nat.mul_assoc, Nat.mul_comm a b, ← Nat.mul_assoc]
      exact Nat.le_mul_of_pos_right (g * b) z.1.1.2.pos
    exact hgb.trans (hgab.trans
      ((Nat.le_mul_of_pos_right (g * a * b) z.1.2.2.pos).trans z.2))
  have hc_le : c ≤ X / p := by
    exact (Nat.le_div_iff_mul_le (by positivity)).2 (by
      simpa [p, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using z.2)
  have hcpos : 0 < c := z.1.2.2.pos
  have hc_lt : c - 1 < X / p := by omega
  let cf : Fin (X / p) := ⟨c - 1, hc_lt⟩
  refine ⟨⟨g, Finset.mem_Icc.mpr ⟨z.1.1.1.pos, hg_le⟩⟩,
    ⟨⟨a, Finset.mem_Icc.mpr ⟨z.1.1.2.pos, ha_le⟩⟩,
      ⟨⟨b, Finset.mem_Icc.mpr ⟨z.1.2.1.pos, hb_le⟩⟩, ?_⟩⟩⟩
  simpa [p] using cf

private theorem h15BoundedFourToTripleFiber_injective {X : ℕ} :
    Function.Injective (h15BoundedFourToTripleFiber (X := X)) := by
  intro z z' h
  have hg := congrArg (fun w => w.1.val) h
  have ha := congrArg (fun w => w.2.1.val) h
  have hb := congrArg (fun w => w.2.2.1.val) h
  have hc := congrArg (fun w => w.2.2.2.val) h
  dsimp [h15BoundedFourToTripleFiber] at hg ha hb hc
  have hcval : z.1.2.2.val = z'.1.2.2.val := by
    have hzpos := z.1.2.2.pos
    have hzpos' := z'.1.2.2.pos
    omega
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext <;> exact PNat.coe_injective (by assumption)
  · apply Prod.ext
    · exact PNat.coe_injective hb
    · exact PNat.coe_injective hcval

private theorem h15_card_tripleFiber_formula (X : ℕ) :
    Nat.card (H15TripleFiber X) =
      ∑ g : H15SmallNat X, ∑ a : H15SmallNat X,
        ∑ b : H15SmallNat X, X / (g.val * a.val * b.val) := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_sigma, Fintype.card_fin]

private theorem h15_card_divisorPairSigma_formula (R : ℕ) :
    Nat.card (H15DivisorPairSigma R) =
      ∑ n ∈ h15BettinChandeeNatBlock R, n.divisors.card ^ 2 := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_coe, pow_two]
  exact (h15BettinChandeeNatBlock R).sum_attach
    (fun n => n.divisors.card * n.divisors.card)

private def h15DivisorPairToTripleFiber {R : ℕ} :
    H15DivisorPairSigma R → H15TripleFiber (2 * R) :=
  h15BoundedFourToTripleFiber ∘ h15DivisorPairToBoundedFour

private theorem h15DivisorPairToTripleFiber_injective {R : ℕ} :
    Function.Injective (h15DivisorPairToTripleFiber (R := R)) :=
  h15BoundedFourToTripleFiber_injective.comp
    h15DivisorPairToBoundedFour_injective

private theorem h15_card_divisorPairSigma_le_tripleFiber (R : ℕ) :
    Nat.card (H15DivisorPairSigma R) ≤
      Nat.card (H15TripleFiber (2 * R)) :=
  Nat.card_le_card_of_injective _ h15DivisorPairToTripleFiber_injective

private theorem h15_sum_inv_smallNat_eq_harmonic (X : ℕ) :
    (∑ k : H15SmallNat X, ((k.val : ℝ)⁻¹)) =
      (harmonic X : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact (Finset.Icc 1 X).sum_attach
    (fun k : ℕ => ((k : ℝ)⁻¹))

private theorem h15_cast_card_tripleFiber_le (X : ℕ) :
    (Nat.card (H15TripleFiber X) : ℝ) ≤
      (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 3 := by
  rw [h15_card_tripleFiber_formula]
  push_cast
  calc
    (∑ g : H15SmallNat X, ∑ a : H15SmallNat X,
        ∑ b : H15SmallNat X,
          ((X / (g.val * a.val * b.val) : ℕ) : ℝ)) ≤
      ∑ g : H15SmallNat X, ∑ a : H15SmallNat X,
        ∑ b : H15SmallNat X,
          (X : ℝ) * (g.val : ℝ)⁻¹ *
            (a.val : ℝ)⁻¹ * (b.val : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro g _
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      calc
        ((X / (g.val * a.val * b.val) : ℕ) : ℝ) ≤
            (X : ℝ) / ((g.val * a.val * b.val : ℕ) : ℝ) :=
          Nat.cast_div_le
        _ = (X : ℝ) * (g.val : ℝ)⁻¹ *
            (a.val : ℝ)⁻¹ * (b.val : ℝ)⁻¹ := by
          push_cast
          rw [div_eq_mul_inv, mul_inv_rev, mul_inv_rev]
          ring
    _ = (X : ℝ) *
        (∑ k : H15SmallNat X, ((k.val : ℝ)⁻¹)) ^ 3 := by
      let H : ℝ := ∑ k : H15SmallNat X, ((k.val : ℝ)⁻¹)
      have hinner (g : H15SmallNat X) :
          (∑ a : H15SmallNat X,
            (X : ℝ) * (g.val : ℝ)⁻¹ * (a.val : ℝ)⁻¹) =
            ((X : ℝ) * (g.val : ℝ)⁻¹) * H := by
        simp only [H, Finset.mul_sum]
      calc
        (∑ g : H15SmallNat X, ∑ a : H15SmallNat X,
          ∑ b : H15SmallNat X,
            (X : ℝ) * (g.val : ℝ)⁻¹ *
              (a.val : ℝ)⁻¹ * (b.val : ℝ)⁻¹) =
            (∑ g : H15SmallNat X, ∑ a : H15SmallNat X,
              (X : ℝ) * (g.val : ℝ)⁻¹ * (a.val : ℝ)⁻¹) * H := by
                simp only [H, ← Finset.sum_mul, ← Finset.mul_sum]
        _ = (∑ g : H15SmallNat X,
              ((X : ℝ) * (g.val : ℝ)⁻¹) * H) * H := by
                congr 1
                apply Finset.sum_congr rfl
                intro g _
                exact hinner g
        _ = (((X : ℝ) * H) * H) * H := by
                rw [← Finset.sum_mul]
                congr 2
                simp only [H, Finset.mul_sum]
        _ = (X : ℝ) * H ^ 3 := by ring
    _ = (X : ℝ) * (harmonic X : ℝ) ^ 3 := by
      rw [h15_sum_inv_smallNat_eq_harmonic]
    _ ≤ (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
      have hharm : 0 ≤ (harmonic X : ℝ) := by
        rw [← h15_sum_inv_smallNat_eq_harmonic]
        positivity
      exact pow_le_pow_left₀ hharm (harmonic_le_one_add_log X) 3

/-- Elementary dyadic summatory bound for the square of the divisor count. -/
theorem sum_divisorsCard_sq_h15BettinChandeeNatBlock_le
    (R : ℕ) :
    (∑ r ∈ h15BettinChandeeNatBlock R,
        (r.divisors.card : ℝ) ^ 2) ≤
      (2 * (R : ℝ)) * (1 + Real.log (2 * (R : ℝ))) ^ 3 := by
  calc
    (∑ r ∈ h15BettinChandeeNatBlock R,
        (r.divisors.card : ℝ) ^ 2) =
        (Nat.card (H15DivisorPairSigma R) : ℝ) := by
          rw [h15_card_divisorPairSigma_formula]
          push_cast
          rfl
    _ ≤ (Nat.card (H15TripleFiber (2 * R)) : ℝ) := by
          exact_mod_cast h15_card_divisorPairSigma_le_tripleFiber R
    _ ≤ ((2 * R : ℕ) : ℝ) *
          (1 + Real.log ((2 * R : ℕ) : ℝ)) ^ 3 :=
        h15_cast_card_tripleFiber_le (2 * R)
    _ = (2 * (R : ℝ)) * (1 + Real.log (2 * (R : ℝ))) ^ 3 := by
          push_cast
          rfl

private theorem h15_divisor_frequency_sq_eq_div_cube
    (r : ℕ) :
    ((r.divisors.card : ℝ) / (r : ℝ) ^ (3 / 2 : ℝ)) ^ 2 =
      (r.divisors.card : ℝ) ^ 2 / (r : ℝ) ^ 3 := by
  rw [div_pow]
  congr 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (Nat.cast_nonneg r)]
  norm_num [Real.rpow_natCast]

/-- The classical divisor-square package required by the H15 dyadic ledger,
with the explicit constant `2`. -/
noncomputable def h15DivisorSquareDyadicBound :
    H15DivisorSquareDyadicBound where
  constant := 2
  constant_nonneg := by norm_num
  bound R hR := by
    rw [h15BettinChandeeFrequencyMass_eq_divisorSquare]
    simp_rw [h15_divisor_frequency_sq_eq_div_cube]
    calc
      (∑ r ∈ h15BettinChandeeNatBlock R,
          (r.divisors.card : ℝ) ^ 2 / (r : ℝ) ^ 3) ≤
        ∑ r ∈ h15BettinChandeeNatBlock R,
          (r.divisors.card : ℝ) ^ 2 / (R : ℝ) ^ 3 := by
            apply Finset.sum_le_sum
            intro r hrmem
            apply div_le_div_of_nonneg_left (sq_nonneg _)
              (by positivity)
            exact pow_le_pow_left₀ (Nat.cast_nonneg R)
              (by exact_mod_cast (Finset.mem_Ico.mp hrmem).1) 3
      _ = (∑ r ∈ h15BettinChandeeNatBlock R,
            (r.divisors.card : ℝ) ^ 2) / (R : ℝ) ^ 3 := by
          rw [Finset.sum_div]
      _ ≤ ((2 * (R : ℝ)) *
            (1 + Real.log (2 * (R : ℝ))) ^ 3) / (R : ℝ) ^ 3 := by
          exact div_le_div_of_nonneg_right
            (sum_divisorsCard_sq_h15BettinChandeeNatBlock_le R)
            (by positivity)
      _ = 2 * (1 + Real.log (2 * (R : ℝ))) ^ 3 /
            (R : ℝ) ^ 2 := by
          have hR0 : (R : ℝ) ≠ 0 := by positivity
          field_simp

end NBMellinTools.NB12
