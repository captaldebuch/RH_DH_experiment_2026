import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRationalSineEndpoint

/-!
# Route B5: finite Fourier transform at the Estermann endpoint

This file develops the purely finite Fourier calculation left after the
rational Hurwitz endpoint.  Its first target is the DFT of the cotangent
residue function.  No analytic continuation or infinite series occurs here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannFiniteFourier

open AddChar Complex ZMod
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperRationalSineEndpoint
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The cotangent function on residues, with its removable zero residue set
to zero. -/
noncomputable def residueCotangent
    {q : ℕ} [NeZero q] (r : ZMod q) : ℂ :=
  if r = 0 then 0 else (cotangentTermV r.val q : ℂ)

@[simp] theorem residueCotangent_zero
    {q : ℕ} [NeZero q] : residueCotangent (0 : ZMod q) = 0 := by
  simp [residueCotangent]

/-- On the canonical nonzero natural representatives, `residueCotangent`
is the original real cotangent term. -/
theorem residueCotangent_natCast_Ioc
    {q : ℕ} [NeZero q] (r : ℕ)
    (hr : r ∈ Finset.Ioc 0 (q - 1)) :
    residueCotangent (r : ZMod q) = (cotangentTermV r q : ℂ) := by
  simp only [Finset.mem_Ioc] at hr
  have hrq : r < q := by omega
  have hrne : (r : ZMod q) ≠ 0 := by
    intro h
    have hval := congrArg (ZMod.val : ZMod q → ℕ) h
    rw [ZMod.val_natCast_of_lt hrq] at hval
    simp only [ZMod.val_zero] at hval
    omega
  unfold residueCotangent
  rw [if_neg hrne, ZMod.val_natCast_of_lt hrq]

/-- Replace a complete residue sum whose zero term vanishes by the canonical
natural representatives `1, ..., q-1`. -/
theorem sum_zmod_eq_sum_Ioc_of_zero
    {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (hzero : f 0 = 0) :
    (∑ r : ZMod q, f r) =
      ∑ r ∈ Finset.Ioc 0 (q - 1), f (r : ZMod q) := by
  have hfin :
      (∑ r : ZMod q, f r) =
        ∑ n : Fin q, f (ZMod.finEquiv q n) := by
    apply Fintype.sum_equiv (ZMod.finEquiv q).symm
    intro r
    simp
  rw [hfin]
  have hcanonical (n : Fin q) :
      ZMod.finEquiv q n = (n : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
        apply ZMod.val_injective (q + 1)
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt n.isLt]
        rfl
  simp_rw [hcanonical]
  change (∑ n : Fin q, f ((n : ℕ) : ZMod q)) = _
  have hRange :
      (∑ n : Fin q, f ((n : ℕ) : ZMod q)) =
        ∑ n ∈ Finset.range q, f (n : ZMod q) :=
    Fin.sum_univ_eq_sum_range (fun n : ℕ => f (n : ZMod q)) q
  rw [hRange]
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hset : Finset.range q =
      insert 0 (Finset.Ioc 0 (q - 1)) := by
    ext r
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hzeroNot : 0 ∉ Finset.Ioc 0 (q - 1) := by simp
  have hzero' : f ((0 : ℕ) : ZMod q) = 0 := by simpa using hzero
  rw [hset, Finset.sum_insert hzeroNot, hzero', zero_add]

/-- The real part of a negative-frequency standard character. -/
theorem stdAddChar_neg_nat_mul_re
    {q : ℕ} [NeZero q] (j : ZMod q) (r : ℕ) :
    (ZMod.stdAddChar (-((r : ZMod q) * j))).re =
      rationalCosinePeriodicTerm j.val q r := by
  rw [AddChar.map_neg_eq_inv]
  rw [show (r : ZMod q) * j = j * (r : ZMod q) by ring]
  rw [Complex.inv_re]
  have hnorm :
      Complex.normSq (ZMod.stdAddChar (j * (r : ZMod q))) = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.normSq_coe _
  rw [hnorm, div_one]
  have h := rationalCosinePeriodicTerm_eq_stdAddChar_re j.val q r
  rw [ZMod.natCast_zmod_val] at h
  exact h.symm

/-- The imaginary part of a negative-frequency standard character. -/
theorem stdAddChar_neg_nat_mul_im
    {q : ℕ} [NeZero q] (j : ZMod q) (r : ℕ) :
    (ZMod.stdAddChar (-((r : ZMod q) * j))).im =
      -rationalSinePeriodicTerm j r := by
  rw [AddChar.map_neg_eq_inv]
  rw [show (r : ZMod q) * j = j * (r : ZMod q) by ring]
  rw [Complex.inv_im]
  have hnorm :
      Complex.normSq (ZMod.stdAddChar (j * (r : ZMod q))) = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.normSq_coe _
  rw [hnorm, div_one]
  exact congrArg Neg.neg
    (rationalSinePeriodicTerm_eq_stdAddChar_im j r).symm

/-- Cosine is unchanged by reflection inside a period. -/
theorem rationalCosinePeriodicTerm_reflect
    {q : ℕ} [NeZero q] (k : ℕ) (hq : 0 < q)
    (r : ℕ) (hr : r ∈ Finset.Ioc 0 (q - 1)) :
    rationalCosinePeriodicTerm k q (q - r) =
      rationalCosinePeriodicTerm k q r := by
  simp only [Finset.mem_Ioc] at hr
  have hrq : r ≤ q := by omega
  unfold rationalCosinePeriodicTerm
  have hcast : ((q - r : ℕ) : ℝ) = (q : ℝ) - r :=
    Nat.cast_sub hrq
  have harg :
      2 * Real.pi * ((k : ℝ) / q) * ((q : ℝ) - r) =
        k * (2 * Real.pi) -
          2 * Real.pi * ((k : ℝ) / q) * r := by
    have hqR : (q : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hcast, harg, Real.cos_nat_mul_two_pi_sub]

/-- Cotangent changes sign under reflection inside a period. -/
theorem cotangentTermV_reflect
    {q : ℕ} (hq : 0 < q)
    (r : ℕ) (hr : r ∈ Finset.Ioc 0 (q - 1)) :
    cotangentTermV (q - r) q = -cotangentTermV r q := by
  simp only [Finset.mem_Ioc] at hr
  have hrq : r ≤ q := by omega
  have hqR : (q : ℝ) ≠ 0 := by positivity
  unfold cotangentTermV
  have hcast : ((q - r : ℕ) : ℝ) = (q : ℝ) - r :=
    Nat.cast_sub hrq
  have harg :
      Real.pi * ((q : ℝ) - r) / q =
        Real.pi - Real.pi * (r : ℝ) / q := by
    field_simp
  rw [hcast, harg, Real.cos_pi_sub, Real.sin_pi_sub]
  ring

/-- The cosine--cotangent part of the finite DFT vanishes by reflection. -/
theorem sum_cosine_mul_cotangent_eq_zero
    {q : ℕ} [NeZero q] (k : ℕ) :
    (∑ r ∈ Finset.Ioc 0 (q - 1),
      rationalCosinePeriodicTerm k q r * cotangentTermV r q) = 0 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let S : ℝ := ∑ r ∈ Finset.Ioc 0 (q - 1),
    rationalCosinePeriodicTerm k q r * cotangentTermV r q
  have hreflect : S = -S := by
    unfold S
    calc
      (∑ r ∈ Finset.Ioc 0 (q - 1),
          rationalCosinePeriodicTerm k q r * cotangentTermV r q) =
          ∑ r ∈ Finset.Ioc 0 (q - 1),
            rationalCosinePeriodicTerm k q (q - r) *
              cotangentTermV (q - r) q := by
            apply Finset.sum_nbij' (i := fun r => q - r)
              (j := fun r => q - r)
            · intro r hr
              simp only [Finset.mem_Ioc] at hr ⊢
              omega
            · intro r hr
              simp only [Finset.mem_Ioc] at hr ⊢
              omega
            · intro r hr
              simp only [Finset.mem_Ioc] at hr
              omega
            · intro r hr
              simp only [Finset.mem_Ioc] at hr
              omega
            · intro r hr
              simp only [Finset.mem_Ioc] at hr
              congr 2 <;> omega
      _ = ∑ r ∈ Finset.Ioc 0 (q - 1),
            -(rationalCosinePeriodicTerm k q r *
              cotangentTermV r q) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [rationalCosinePeriodicTerm_reflect k hq r hr,
              cotangentTermV_reflect hq r hr]
            ring
      _ = -S := by simp [S]
  linarith

/-- The complete DFT of the cotangent residue function.  This is the finite
Fourier form of the sine--cotangent identity proved in the endpoint module. -/
theorem dft_residueCotangent
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    ZMod.dft (residueCotangent (q := q)) j =
      -Complex.I * ((q : ℝ) - 2 * (j.val : ℝ)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [sum_zmod_eq_sum_Ioc_of_zero
    (fun r : ZMod q => ZMod.stdAddChar (-(r * j)) * residueCotangent r)]
  · have hres := residueCotangent_natCast_Ioc (q := q)
    have hsumres :
        (∑ r ∈ Finset.Ioc 0 (q - 1),
          ZMod.stdAddChar (-((r : ZMod q) * j)) *
            residueCotangent (r : ZMod q)) =
          ∑ r ∈ Finset.Ioc 0 (q - 1),
            ZMod.stdAddChar (-((r : ZMod q) * j)) *
              (cotangentTermV r q : ℂ) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hres r hr]
    rw [hsumres]
    apply Complex.ext
    · rw [Complex.re_sum]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, Complex.neg_re, Complex.I_re, neg_zero,
        zero_mul]
      simp_rw [stdAddChar_neg_nat_mul_re]
      simpa using
        sum_cosine_mul_cotangent_eq_zero (q := q) j.val
    · rw [Complex.im_sum]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, Complex.neg_im, Complex.I_im, neg_one_mul,
        Complex.neg_re, Complex.I_re]
      simp_rw [stdAddChar_neg_nat_mul_im]
      have hsine := rationalSineCotangentFiniteIdentity.value_eq j hj
      simpa using congrArg Neg.neg hsine
  · simp

/-- The residue cotangent is odd. -/
theorem residueCotangent_neg
    {q : ℕ} [NeZero q] (r : ZMod q) :
    residueCotangent (-r) = -residueCotangent r := by
  by_cases hr : r = 0
  · subst r
    simp
  have hnr : -r ≠ 0 := neg_ne_zero.mpr hr
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hr0 : 0 < r.val := ZMod.val_pos.mpr hr
  have hrmem : r.val ∈ Finset.Ioc 0 (q - 1) := by
    simp only [Finset.mem_Ioc]
    have hrq := r.val_lt
    exact ⟨hr0, by omega⟩
  letI : NeZero r := ⟨hr⟩
  unfold residueCotangent
  rw [if_neg hnr, if_neg hr, ZMod.val_neg_of_ne_zero]
  norm_cast
  exact_mod_cast cotangentTermV_reflect hq r.val hrmem

/-- The cotangent DFT at zero vanishes. -/
theorem dft_residueCotangent_zero
    {q : ℕ} [NeZero q] :
    ZMod.dft (residueCotangent (q := q)) 0 = 0 := by
  rw [ZMod.dft_apply_zero]
  rw [sum_zmod_eq_sum_Ioc_of_zero residueCotangent residueCotangent_zero]
  have hsum :
      (∑ r ∈ Finset.Ioc 0 (q - 1),
        residueCotangent (r : ZMod q)) =
        ∑ r ∈ Finset.Ioc 0 (q - 1),
          (cotangentTermV r q : ℂ) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact residueCotangent_natCast_Ioc r hr
  rw [hsum]
  have hcos := sum_cosine_mul_cotangent_eq_zero (q := q) 0
  simp [rationalCosinePeriodicTerm] at hcos
  norm_cast at hcos ⊢

/-- The cotangent DFT expressed uniformly in terms of the periodic Bernoulli
value, including the exceptional zero residue. -/
theorem dft_residueCotangent_eq_bernoulli
    {q : ℕ} [NeZero q] (j : ZMod q) :
    ZMod.dft (residueCotangent (q := q)) j =
      (-2 * Complex.I * (q : ℂ)) * periodicBernoulliOneValue j -
        Complex.I * (q : ℂ) * (if j = 0 then 1 else 0) := by
  by_cases hj : j = 0
  · subst j
    rw [dft_residueCotangent_zero]
    simp [periodicBernoulliOneValue]
    ring
  · rw [dft_residueCotangent j hj]
    simp [periodicBernoulliOneValue, hj]
    have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
    field_simp [hq]
    norm_num
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val]
    exact Complex.ofReal_natCast j.val

/-- The DFT of the periodic first Bernoulli value.  It is the exact finite
cotangent transform needed by the Estermann value at zero. -/
theorem dft_periodicBernoulliOneValue
    {q : ℕ} [NeZero q] (j : ZMod q) :
    ZMod.dft (periodicBernoulliOneValue (q := q)) j =
      -(1 : ℂ) / 2 - Complex.I / 2 * residueCotangent j := by
  have hdouble := congrFun
    (ZMod.dft_dft (residueCotangent (q := q))) j
  rw [ZMod.dft_apply] at hdouble
  simp only [smul_eq_mul] at hdouble
  simp_rw [dft_residueCotangent_eq_bernoulli] at hdouble
  have hdelta :
      (∑ x : ZMod q,
        ZMod.stdAddChar (-(x * j)) *
          (if x = 0 then (1 : ℂ) else 0)) = 1 := by
    simp
  have hB :
      (∑ x : ZMod q,
        ZMod.stdAddChar (-(x * j)) *
          periodicBernoulliOneValue x) =
        ZMod.dft (periodicBernoulliOneValue (q := q)) j := by
    rw [ZMod.dft_apply]
    simp only [smul_eq_mul]
  have hcalc :
      (-2 * Complex.I * (q : ℂ)) *
          ZMod.dft (periodicBernoulliOneValue (q := q)) j -
        Complex.I * (q : ℂ) =
          (q : ℂ) * residueCotangent (-j) := by
    calc
      (-2 * Complex.I * (q : ℂ)) *
            ZMod.dft (periodicBernoulliOneValue (q := q)) j -
          Complex.I * (q : ℂ) =
          (-2 * Complex.I * (q : ℂ)) *
              (∑ x : ZMod q,
                ZMod.stdAddChar (-(x * j)) *
                  periodicBernoulliOneValue x) -
            Complex.I * (q : ℂ) *
              (∑ x : ZMod q,
                ZMod.stdAddChar (-(x * j)) *
                  (if x = 0 then (1 : ℂ) else 0)) := by
            rw [hB, hdelta]
            ring
      _ = ∑ x : ZMod q,
            ZMod.stdAddChar (-(x * j)) *
              ((-2 * Complex.I * (q : ℂ)) *
                  periodicBernoulliOneValue x -
                Complex.I * (q : ℂ) *
                  (if x = 0 then (1 : ℂ) else 0)) := by
            rw [Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = (q : ℂ) * residueCotangent (-j) := hdouble
  rw [residueCotangent_neg] at hcalc
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hcalc' :
      -2 * Complex.I *
          ZMod.dft (periodicBernoulliOneValue (q := q)) j -
        Complex.I = -residueCotangent j := by
    apply mul_left_cancel₀ hq
    rw [← hcalc]
    ring
  have hsolve :
      -2 * Complex.I *
          ZMod.dft (periodicBernoulliOneValue (q := q)) j =
        Complex.I - residueCotangent j := by
    linear_combination hcalc'
  calc
    ZMod.dft (periodicBernoulliOneValue (q := q)) j =
        Complex.I / 2 *
          (-2 * Complex.I *
            ZMod.dft (periodicBernoulliOneValue (q := q)) j) := by
          field_simp
          ring_nf
          simp [Complex.I_sq]
    _ = Complex.I / 2 *
          (Complex.I - residueCotangent j) := by rw [hsolve]
    _ = -(1 : ℂ) / 2 - Complex.I / 2 * residueCotangent j := by
          field_simp
          ring_nf
          simp [Complex.I_sq]
          ring

/-- The inner Bernoulli transform in the continued Estermann value. -/
theorem sum_estermannResiduePhase_mul_bernoulli
    (a : ℕ) {q : ℕ} [NeZero q] (j : ZMod q) :
    (∑ k : ZMod q,
      estermannResiduePhase a j k * periodicBernoulliOneValue k) =
      -(1 : ℂ) / 2 + Complex.I / 2 *
        residueCotangent ((a : ZMod q) * j) := by
  let t : ZMod q := (a : ZMod q) * j
  have hdft := dft_periodicBernoulliOneValue (q := q) (-t)
  rw [residueCotangent_neg] at hdft
  calc
    (∑ k : ZMod q,
        estermannResiduePhase a j k * periodicBernoulliOneValue k) =
        ZMod.dft (periodicBernoulliOneValue (q := q)) (-t) := by
      rw [ZMod.dft_apply]
      simp only [smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k _
      unfold estermannResiduePhase t
      congr 1
      apply congrArg ZMod.stdAddChar
      ring
    _ = -(1 : ℂ) / 2 + Complex.I / 2 * residueCotangent t := by
      rw [hdft]
      ring
    _ = _ := rfl

/-- Multiplication by a reduced numerator preserves the total periodic
Bernoulli mass. -/
theorem sum_periodicBernoulliOneValue_unitMul
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    (∑ r : ZMod q,
      periodicBernoulliOneValue ((a : ZMod q) * r)) = -(1 : ℂ) / 2 := by
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a hcop
  have hreindex :
      (∑ r : ZMod q,
        periodicBernoulliOneValue (u.val * r)) =
        ∑ r : ZMod q, periodicBernoulliOneValue r := by
    exact Fintype.sum_equiv u.mulLeft _ _ (fun r => rfl)
  have hzero := dft_periodicBernoulliOneValue (q := q) (0 : ZMod q)
  rw [ZMod.dft_apply_zero, residueCotangent_zero] at hzero
  simpa [u, ZMod.coe_unitOfCoprime] using hreindex.trans hzero

/-- On a canonical nonzero residue, multiplication inside the periodic
Bernoulli value is the ordinary fractional part. -/
theorem periodicBernoulliOneValue_mul_natCast
    (a : ℕ) {q r : ℕ} [NeZero q]
    (hcop : Nat.Coprime a q) (hr : r ∈ Finset.Ioc 0 (q - 1)) :
    periodicBernoulliOneValue ((a : ZMod q) * (r : ZMod q)) =
      (1 : ℂ) / 2 -
        ((Int.fract (((a * r : ℕ) : ℝ) / (q : ℝ)) : ℝ) : ℂ) := by
  simp only [Finset.mem_Ioc] at hr
  have hrq : r < q := by omega
  have har : (a : ZMod q) * (r : ZMod q) ≠ 0 := by
    intro h
    have haunit : IsUnit (a : ZMod q) :=
      (ZMod.isUnit_iff_coprime a q).mpr hcop
    have hrzero : (r : ZMod q) = 0 :=
      (haunit.mul_right_eq_zero.mp h)
    have hval := congrArg (ZMod.val : ZMod q → ℕ) hrzero
    rw [ZMod.val_natCast_of_lt hrq] at hval
    simp only [ZMod.val_zero] at hval
    omega
  simp only [periodicBernoulliOneValue, if_neg har]
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hval : ((a : ZMod q) * (r : ZMod q)).val = (a * r) % q := by
    rw [← Nat.cast_mul, ZMod.val_natCast]
  rw [hval]
  simp only [Complex.ofReal_div, Complex.ofReal_natCast]

/-- The cotangent/Bernoulli pairing after multiplication by a reduced
numerator is exactly the negative Vasyunin sum. -/
theorem sum_residueCotangent_mul_bernoulli_unitMul
    (a q : ℕ) [NeZero q] (hcop : Nat.Coprime a q) :
    (∑ r : ZMod q,
      residueCotangent r *
        periodicBernoulliOneValue ((a : ZMod q) * r)) =
      -(cotangentSumVFormula a q : ℂ) := by
  rw [sum_zmod_eq_sum_Ioc_of_zero
    (fun r : ZMod q => residueCotangent r *
      periodicBernoulliOneValue ((a : ZMod q) * r))]
  · have hrewrite :
        (∑ r ∈ Finset.Ioc 0 (q - 1),
          residueCotangent (r : ZMod q) *
            periodicBernoulliOneValue
              ((a : ZMod q) * (r : ZMod q))) =
          ∑ r ∈ Finset.Ioc 0 (q - 1),
            (cotangentTermV r q : ℂ) *
              ((1 : ℂ) / 2 -
                ((Int.fract (((a * r : ℕ) : ℝ) / (q : ℝ)) : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [residueCotangent_natCast_Ioc r hr,
        periodicBernoulliOneValue_mul_natCast a hcop hr]
    rw [hrewrite]
    have hcot := dft_residueCotangent_zero (q := q)
    rw [ZMod.dft_apply_zero,
      sum_zmod_eq_sum_Ioc_of_zero residueCotangent residueCotangent_zero]
      at hcot
    have hcot' :
        (∑ r ∈ Finset.Ioc 0 (q - 1),
          (cotangentTermV r q : ℂ)) = 0 := by
      calc
        (∑ r ∈ Finset.Ioc 0 (q - 1),
            (cotangentTermV r q : ℂ)) =
            ∑ r ∈ Finset.Ioc 0 (q - 1),
              residueCotangent (r : ZMod q) := by
                apply Finset.sum_congr rfl
                intro r hr
                rw [residueCotangent_natCast_Ioc r hr]
        _ = 0 := hcot
    unfold cotangentSumVFormula
    rw [show Finset.Ico 1 q = Finset.Ioc 0 (q - 1) by
      ext r
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega]
    calc
      (∑ r ∈ Finset.Ioc 0 (q - 1),
          (cotangentTermV r q : ℂ) *
            ((1 : ℂ) / 2 -
              ((Int.fract (((a * r : ℕ) : ℝ) / (q : ℝ)) : ℝ) : ℂ))) =
          (1 : ℂ) / 2 *
              (∑ r ∈ Finset.Ioc 0 (q - 1),
                (cotangentTermV r q : ℂ)) -
            ∑ r ∈ Finset.Ioc 0 (q - 1),
              ((Int.fract (((a * r : ℕ) : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
                (cotangentTermV r q : ℂ) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro r _
            ring
      _ = -(∑ r ∈ Finset.Ioc 0 (q - 1),
              ((Int.fract (((a * r : ℕ) : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
                (cotangentTermV r q : ℂ)) := by rw [hcot']; ring
      _ = _ := by
            push_cast
            simp only [mul_comm]
  · simp

/-- The remaining finite Estermann--Vasyunin identity is unconditional. -/
noncomputable def estermannBernoulliCotangentIdentity :
    EstermannBernoulliCotangentIdentity where
  value_eq := by
    intro a q ha hq hcop
    letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
    let u : (ZMod q)ˣ := ZMod.unitOfCoprime a hcop
    let F : ZMod q → ℂ := fun j =>
      (-(1 : ℂ) / 2 + Complex.I / 2 *
          residueCotangent
            ((inverseResidue a q : ZMod q) * j)) *
        periodicBernoulliOneValue j
    have hfinite : inverseEstermannBernoulliFiniteValue a q =
        ∑ j : ZMod q, F j := by
      unfold inverseEstermannBernoulliFiniteValue
        estermannBernoulliFiniteValue F
      simp_rw [sum_estermannResiduePhase_mul_bernoulli]
    have hinv (r : ZMod q) :
        (inverseResidue a q : ZMod q) * ((a : ZMod q) * r) = r := by
      have hia :
          (inverseResidue a q : ZMod q) * (a : ZMod q) = 1 := by
        simpa only [Nat.cast_mul] using
          inverseResidue_mul_mod_eq_one a q hcop
      rw [← mul_assoc, hia, one_mul]
    have hreindex :
        (∑ j : ZMod q, F j) =
          ∑ r : ZMod q,
            (-(1 : ℂ) / 2 + Complex.I / 2 * residueCotangent r) *
              periodicBernoulliOneValue ((a : ZMod q) * r) := by
      symm
      calc
        (∑ r : ZMod q,
            (-(1 : ℂ) / 2 + Complex.I / 2 * residueCotangent r) *
              periodicBernoulliOneValue ((a : ZMod q) * r)) =
            ∑ r : ZMod q, F (u.val * r) := by
              apply Finset.sum_congr rfl
              intro r _
              simp only [F, u, ZMod.coe_unitOfCoprime]
              rw [hinv]
        _ = ∑ j : ZMod q, F j :=
          Fintype.sum_equiv u.mulLeft _ _ (fun r => rfl)
    rw [hfinite, hreindex]
    rw [show (∑ r : ZMod q,
        (-(1 : ℂ) / 2 + Complex.I / 2 * residueCotangent r) *
          periodicBernoulliOneValue ((a : ZMod q) * r)) =
        -(1 : ℂ) / 2 *
            (∑ r : ZMod q,
              periodicBernoulliOneValue ((a : ZMod q) * r)) +
          Complex.I / 2 *
            (∑ r : ZMod q,
              residueCotangent r *
                periodicBernoulliOneValue ((a : ZMod q) * r)) by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring]
    rw [sum_periodicBernoulliOneValue_unitMul a q hcop,
      sum_residueCotangent_mul_bernoulli_unitMul a q hcop]
    ring

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannFiniteFourier
