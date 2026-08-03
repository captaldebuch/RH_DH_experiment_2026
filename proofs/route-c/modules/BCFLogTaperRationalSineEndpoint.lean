import RiemannHypothesis.Criteria.NymanBeurling.BBLSPhiOne
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
import RiemannHypothesis.Criteria.NymanBeurling.MobiusSummatoryClassical

/-!
# The rational sine endpoint: analytic compatibility

This file proves the analytic part of the missing `sinZeta(a,1)` endpoint.
An ordered evaluation of the conditionally convergent harmonic sine series is
transported to Mathlib's entire `sinZeta` by the already proved real
Dirichlet--Abelian boundary theorem.

Thus no hidden continuity assertion remains: the only input below is the
ordered value of the elementary real series.  A later finite trigonometric
calculation can construct that input.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRationalSineEndpoint

open Complex Filter HurwitzZeta Topology ZMod
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannAtZeroBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.MobiusSummatory
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The real boundary coefficient of the harmonic sine series.  The value at
zero is harmlessly zero under Lean's division convention. -/
noncomputable def rationalSineBoundaryTerm (x : ℝ) (n : ℕ) : ℝ :=
  Real.sin (2 * Real.pi * x * n) / (n : ℝ)

@[simp] theorem rationalSineBoundaryTerm_zero (x : ℝ) :
    rationalSineBoundaryTerm x 0 = 0 := by
  simp [rationalSineBoundaryTerm]

/-- The remaining ordered Fourier-series statement, separated from analytic
continuation. -/
structure RationalSineHarmonicSeriesFormula where
  tendsto_value : ∀ {q : ℕ} [NeZero q] (j : ZMod q), j ≠ 0 →
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
        rationalSineBoundaryTerm ((j.val : ℝ) / q) n)
      atTop
      (𝓝 (Real.pi * (1 / 2 - (j.val : ℝ) / q)))

/-- The unweighted periodic sine coefficient. -/
noncomputable def rationalSinePeriodicTerm
    {q : ℕ} [NeZero q] (j : ZMod q) (n : ℕ) : ℝ :=
  Real.sin (2 * Real.pi * ((j.val : ℝ) / q) * n)

/-- The real sine coefficient is the imaginary part of the standard additive
character. -/
theorem rationalSinePeriodicTerm_eq_stdAddChar_im
    {q : ℕ} [NeZero q] (j : ZMod q) (n : ℕ) :
    rationalSinePeriodicTerm j n =
      (ZMod.stdAddChar (j * (n : ZMod q))).im := by
  have hphase := congrArg Complex.im
    (estermannAdditivePhase_eq_stdAddChar j.val q n)
  have hcast : ((j.val * n : ℕ) : ZMod q) = j * (n : ZMod q) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hcast] at hphase
  rw [← hphase]
  simp [rationalSinePeriodicTerm, estermannAdditivePhase,
    Complex.exp_im]
  ring_nf

/-- Periodicity with modulus `q`. -/
theorem rationalSinePeriodicTerm_periodic
    {q : ℕ} [NeZero q] (j : ZMod q) (n : ℕ) :
    rationalSinePeriodicTerm j (n + q) =
      rationalSinePeriodicTerm j n := by
  simp only [rationalSinePeriodicTerm_eq_stdAddChar_im]
  congr 2
  simp [Nat.cast_add]

/-- The periodic sine coefficient vanishes at both ends of a full period. -/
@[simp] theorem rationalSinePeriodicTerm_zero
    {q : ℕ} [NeZero q] (j : ZMod q) :
    rationalSinePeriodicTerm j 0 = 0 := by
  simp [rationalSinePeriodicTerm]

@[simp] theorem rationalSinePeriodicTerm_modulus
    {q : ℕ} [NeZero q] (j : ZMod q) :
    rationalSinePeriodicTerm j q = 0 := by
  simpa using rationalSinePeriodicTerm_periodic j 0

/-- A nontrivial standard additive character sums to zero over the canonical
natural representatives of `ZMod q`. -/
theorem stdAddChar_mul_nat_range_sum_eq_zero
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    (∑ n ∈ Finset.range q,
      ZMod.stdAddChar (j * (n : ZMod q))) = 0 := by
  have hchar : (∑ z : ZMod q, ZMod.stdAddChar (z * j)) = 0 := by
    simpa [hj] using AddChar.sum_mulShift (ψ := ZMod.stdAddChar) j
      (ZMod.isPrimitive_stdAddChar q)
  have hfin :
      (∑ n : Fin q, ZMod.stdAddChar
        ((ZMod.finEquiv q n) * j)) = 0 := by
    calc
      (∑ n : Fin q, ZMod.stdAddChar ((ZMod.finEquiv q n) * j)) =
          ∑ z : ZMod q, ZMod.stdAddChar (z * j) := by
            apply Fintype.sum_equiv (ZMod.finEquiv q)
            intro n
            rfl
      _ = 0 := hchar
  have hfinCast (n : Fin q) :
      ZMod.finEquiv q n = (n : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
        apply ZMod.val_injective (q + 1)
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt n.isLt]
        rfl
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ n : Fin q, ZMod.stdAddChar (j * (n : ZMod q))) =
        ∑ n : Fin q, ZMod.stdAddChar ((ZMod.finEquiv q n) * j) := by
          apply Finset.sum_congr rfl
          intro n _
          apply congrArg ZMod.stdAddChar
          rw [hfinCast n, mul_comm]
    _ = 0 := hfin

/-- A nontrivial rational sine coefficient has mean zero over one period. -/
theorem rationalSinePeriodicTerm_meanzero
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    (∑ n ∈ Finset.Ioc 0 q, rationalSinePeriodicTerm j n) = 0 := by
  have hrangeChar :
      (∑ n ∈ Finset.range q,
        ZMod.stdAddChar (j * (n : ZMod q))) = 0 := by
    exact stdAddChar_mul_nat_range_sum_eq_zero j hj
  have hrangeSine :
      (∑ n ∈ Finset.range q, rationalSinePeriodicTerm j n) = 0 := by
    calc
      (∑ n ∈ Finset.range q, rationalSinePeriodicTerm j n) =
          ∑ n ∈ Finset.range q,
            (ZMod.stdAddChar (j * (n : ZMod q))).im := by
              apply Finset.sum_congr rfl
              intro n _
              exact rationalSinePeriodicTerm_eq_stdAddChar_im j n
      _ = (∑ n ∈ Finset.range q,
            ZMod.stdAddChar (j * (n : ZMod q))).im := by
              rw [Complex.im_sum]
      _ = 0 := by rw [hrangeChar]; rfl
  have hIoc :
      (∑ n ∈ Finset.Ioc 0 q, rationalSinePeriodicTerm j n) =
        ∑ n ∈ Finset.range q, rationalSinePeriodicTerm j n := by
    have hins : Finset.range (q + 1) =
        insert 0 (Finset.Ioc 0 q) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
      omega
    have hzeroNot : 0 ∉ Finset.Ioc 0 q := by simp
    have hleft :
        (∑ n ∈ Finset.range (q + 1), rationalSinePeriodicTerm j n) =
          ∑ n ∈ Finset.Ioc 0 q, rationalSinePeriodicTerm j n := by
      rw [hins, Finset.sum_insert hzeroNot,
        rationalSinePeriodicTerm_zero, zero_add]
    have hright :
        (∑ n ∈ Finset.range (q + 1), rationalSinePeriodicTerm j n) =
          ∑ n ∈ Finset.range q, rationalSinePeriodicTerm j n := by
      rw [Finset.sum_range_succ, rationalSinePeriodicTerm_modulus, add_zero]
    exact hleft.symm.trans hright
  rw [hIoc, hrangeSine]

/-- The cosine companion to `rationalSinePeriodicTerm`. -/
noncomputable def rationalCosinePeriodicTerm
    (k q n : ℕ) : ℝ :=
  Real.cos (2 * Real.pi * ((k : ℝ) / q) * n)

/-- The real cosine coefficient is the real part of the standard additive
character. -/
theorem rationalCosinePeriodicTerm_eq_stdAddChar_re
    (k q n : ℕ) [NeZero q] :
    rationalCosinePeriodicTerm k q n =
      (ZMod.stdAddChar ((k : ZMod q) * (n : ZMod q))).re := by
  have hphase := congrArg Complex.re
    (estermannAdditivePhase_eq_stdAddChar k q n)
  have hcast : ((k * n : ℕ) : ZMod q) =
      (k : ZMod q) * (n : ZMod q) := by push_cast; rfl
  rw [hcast] at hphase
  rw [← hphase]
  simp [rationalCosinePeriodicTerm, estermannAdditivePhase,
    Complex.exp_re]
  ring_nf

/-- Every nonzero cosine frequency below the modulus has sum `-1` over the
nonzero residue representatives. -/
theorem sum_rationalCosinePeriodicTerm_Ioc_eq_neg_one
    {q k : ℕ} [NeZero q] (hk0 : 0 < k) (hkq : k < q) :
    (∑ r ∈ Finset.Ioc 0 (q - 1),
      rationalCosinePeriodicTerm k q r) = -1 := by
  have hj : (k : ZMod q) ≠ 0 := by
    intro hj0
    have hval := congrArg ZMod.val hj0
    rw [ZMod.val_natCast_of_lt hkq] at hval
    simp only [ZMod.val_zero] at hval
    omega
  have hchar := stdAddChar_mul_nat_range_sum_eq_zero
    (j := (k : ZMod q)) hj
  have hrange :
      (∑ r ∈ Finset.range q,
        rationalCosinePeriodicTerm k q r) = 0 := by
    calc
      (∑ r ∈ Finset.range q,
          rationalCosinePeriodicTerm k q r) =
        ∑ r ∈ Finset.range q,
          (ZMod.stdAddChar
            ((k : ZMod q) * (r : ZMod q))).re := by
              apply Finset.sum_congr rfl
              intro r _
              exact rationalCosinePeriodicTerm_eq_stdAddChar_re k q r
      _ = (∑ r ∈ Finset.range q,
          ZMod.stdAddChar
            ((k : ZMod q) * (r : ZMod q))).re := by
              rw [Complex.re_sum]
      _ = 0 := by rw [hchar]; rfl
  have hq : 0 < q := hk0.trans hkq
  have hset : Finset.range q =
      insert 0 (Finset.Ioc 0 (q - 1)) := by
    ext r
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hzeroNot : 0 ∉ Finset.Ioc 0 (q - 1) := by simp
  rw [hset, Finset.sum_insert hzeroNot] at hrange
  have hzero : rationalCosinePeriodicTerm k q 0 = 1 := by
    simp [rationalCosinePeriodicTerm]
  rw [hzero] at hrange
  linarith

/-- The finite cosine kernel appearing in the elementary sine--cotangent
identity. -/
noncomputable def dirichletCosineKernel (m : ℕ) (x : ℝ) : ℝ :=
  1 + Real.cos (2 * (m : ℝ) * x) +
    2 * ∑ k ∈ Finset.Ico 1 m,
      Real.cos (2 * (k : ℝ) * x)

/-- Pointwise Dirichlet-kernel identity. -/
theorem sin_two_nat_mul_cot_eq_dirichletCosineKernel
    (m : ℕ) (hm : 0 < m) (x : ℝ) (hx : Real.sin x ≠ 0) :
    Real.sin (2 * (m : ℝ) * x) *
        (Real.cos x / Real.sin x) =
      dirichletCosineKernel m x := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  induction n with
  | zero =>
      simp [dirichletCosineKernel, Real.sin_two_mul,
        Real.cos_two_mul]
      field_simp
  | succ n ih =>
      have hsum :
          (∑ k ∈ Finset.Ico 1 (n + 2),
              Real.cos (2 * (k : ℝ) * x)) =
            (∑ k ∈ Finset.Ico 1 (n + 1),
              Real.cos (2 * (k : ℝ) * x)) +
              Real.cos (2 * ((n + 1 : ℕ) : ℝ) * x) := by
        rw [Finset.sum_Ico_succ_top (by omega)]
      have hangle :
          2 * ((n + 2 : ℕ) : ℝ) * x =
            2 * ((n + 1 : ℕ) : ℝ) * x + 2 * x := by
        push_cast
        ring
      have hstep :
          Real.sin (2 * ((n + 2 : ℕ) : ℝ) * x) *
              (Real.cos x / Real.sin x) =
            Real.sin (2 * ((n + 1 : ℕ) : ℝ) * x) *
                (Real.cos x / Real.sin x) +
              Real.cos (2 * ((n + 2 : ℕ) : ℝ) * x) +
              Real.cos (2 * ((n + 1 : ℕ) : ℝ) * x) := by
        rw [hangle, Real.sin_add, Real.cos_add,
          Real.sin_two_mul, Real.cos_two_mul]
        field_simp
        have hcosSq : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
          nlinarith [Real.sin_sq_add_cos_sq x]
        rw [hcosSq]
        ring_nf
        rw [hcosSq]
        ring
      rw [hstep, ih (Nat.succ_pos n)]
      unfold dirichletCosineKernel
      rw [hsum]
      ring

/-- Reflection of a rational sine coefficient inside one nontrivial
period. -/
theorem rationalSinePeriodicTerm_reflect
    {q : ℕ} [NeZero q] (j : ZMod q) (hq : 0 < q)
    (r : ℕ) (hr : r ∈ Finset.Ioc 0 (q - 1)) :
    rationalSinePeriodicTerm j (q - r) =
      -rationalSinePeriodicTerm j r := by
  simp only [Finset.mem_Ioc] at hr
  have hrq : r ≤ q := by omega
  have hqR : (q : ℝ) ≠ 0 := by positivity
  unfold rationalSinePeriodicTerm
  have hcast : ((q - r : ℕ) : ℝ) = (q : ℝ) - r := by
    exact Nat.cast_sub hrq
  have harg :
      2 * Real.pi * ((j.val : ℝ) / q) * ((q : ℝ) - r) =
        j.val * (2 * Real.pi) -
          2 * Real.pi * ((j.val : ℝ) / q) * r := by
    field_simp
  rw [hcast, harg, Real.sin_nat_mul_two_pi_sub]

/-- The sole finite trigonometric identity needed to evaluate all rational
harmonic sine series.  It is the classical Dirichlet-kernel identity

`sum_{r=1}^{q-1} sin(2*pi*j*r/q) cot(pi*r/q) = q - 2*j`.

Unlike the original Hurwitz endpoint, this package contains no infinite
series or analytic continuation. -/
structure RationalSineCotangentFiniteIdentity where
  value_eq : ∀ {q : ℕ} [NeZero q] (j : ZMod q), j ≠ 0 →
    (∑ r ∈ Finset.Ioc 0 (q - 1),
      rationalSinePeriodicTerm j r * cotangentTermV r q) =
        (q : ℝ) - 2 * (j.val : ℝ)

/-- The sum of the finite Dirichlet cosine kernel over the nonzero residue
representatives. -/
theorem sum_dirichletCosineKernel_Ioc
    {q m : ℕ} [NeZero q] (hm0 : 0 < m) (hmq : m < q) :
    (∑ r ∈ Finset.Ioc 0 (q - 1),
      dirichletCosineKernel m
        (Real.pi * (r : ℝ) / (q : ℝ))) =
      (q : ℝ) - 2 * (m : ℝ) := by
  let S := Finset.Ioc 0 (q - 1)
  let T := Finset.Ico 1 m
  have hcardS : S.card = q - 1 := by
    simp [S]
  have hmain :
      (∑ r ∈ S, rationalCosinePeriodicTerm m q r) = -1 :=
    sum_rationalCosinePeriodicTerm_Ioc_eq_neg_one hm0 hmq
  have hinner :
      (∑ k ∈ T, ∑ r ∈ S, rationalCosinePeriodicTerm k q r) =
        -((m - 1 : ℕ) : ℝ) := by
    calc
      (∑ k ∈ T, ∑ r ∈ S, rationalCosinePeriodicTerm k q r) =
          ∑ k ∈ T, (-1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [T, Finset.mem_Ico] at hk
            exact sum_rationalCosinePeriodicTerm_Ioc_eq_neg_one
              hk.1 (hk.2.trans hmq)
      _ = -((m - 1 : ℕ) : ℝ) := by simp [T]
  have hcos (k r : ℕ) :
      Real.cos (2 * (k : ℝ) *
          (Real.pi * (r : ℝ) / (q : ℝ))) =
        rationalCosinePeriodicTerm k q r := by
    unfold rationalCosinePeriodicTerm
    congr 1
    ring
  have htail :
      (∑ r ∈ Finset.Ioc 0 (q - 1),
          2 * ∑ k ∈ Finset.Ico 1 m,
            rationalCosinePeriodicTerm k q r) =
        2 * (-((m - 1 : ℕ) : ℝ)) := by
    calc
      (∑ r ∈ Finset.Ioc 0 (q - 1),
          2 * ∑ k ∈ Finset.Ico 1 m,
            rationalCosinePeriodicTerm k q r) =
          2 * ∑ r ∈ Finset.Ioc 0 (q - 1),
            ∑ k ∈ Finset.Ico 1 m,
              rationalCosinePeriodicTerm k q r := by
                rw [Finset.mul_sum]
      _ = 2 * ∑ k ∈ Finset.Ico 1 m,
            ∑ r ∈ Finset.Ioc 0 (q - 1),
              rationalCosinePeriodicTerm k q r := by
                congr 1
                exact Finset.sum_comm
      _ = 2 * (-((m - 1 : ℕ) : ℝ)) := by
            rw [show (∑ k ∈ Finset.Ico 1 m,
                ∑ r ∈ Finset.Ioc 0 (q - 1),
                  rationalCosinePeriodicTerm k q r) =
                -((m - 1 : ℕ) : ℝ) by simpa [S, T] using hinner]
  simp_rw [dirichletCosineKernel, hcos]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_const, nsmul_eq_mul, hcardS, hmain]
  rw [htail]
  rw [Nat.cast_sub (by omega : 1 ≤ q),
    Nat.cast_sub (by omega : 1 ≤ m)]
  norm_num
  ring

/-- The finite sine--cotangent identity, proved by the elementary
Dirichlet-kernel calculation above. -/
noncomputable def rationalSineCotangentFiniteIdentity :
    RationalSineCotangentFiniteIdentity where
  value_eq := by
    intro q _ j hj
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hjVal : j.val ≠ 0 := by
      intro hval
      apply hj
      apply ZMod.val_injective q
      simp [hval]
    have hj0 : 0 < j.val := Nat.pos_of_ne_zero hjVal
    have hjq : j.val < q := j.val_lt
    have hpoint : ∀ r ∈ Finset.Ioc 0 (q - 1),
        rationalSinePeriodicTerm j r * cotangentTermV r q =
          dirichletCosineKernel j.val
            (Real.pi * (r : ℝ) / (q : ℝ)) := by
      intro r hr
      simp only [Finset.mem_Ioc] at hr
      have hr0 : 0 < r := hr.1
      have hrq : r < q := by omega
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hx0 : 0 < Real.pi * (r : ℝ) / (q : ℝ) := by positivity
      have hxpi : Real.pi * (r : ℝ) / (q : ℝ) < Real.pi := by
        rw [div_lt_iff₀ hqR]
        exact mul_lt_mul_of_pos_left (by exact_mod_cast hrq) Real.pi_pos
      have hxsin :
          Real.sin (Real.pi * (r : ℝ) / (q : ℝ)) ≠ 0 :=
        ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx0 hxpi)
      have hkernel := sin_two_nat_mul_cot_eq_dirichletCosineKernel
        j.val hj0 (Real.pi * (r : ℝ) / (q : ℝ)) hxsin
      rw [← hkernel]
      unfold rationalSinePeriodicTerm cotangentTermV
      congr 2
      ring
    calc
      (∑ r ∈ Finset.Ioc 0 (q - 1),
          rationalSinePeriodicTerm j r * cotangentTermV r q) =
          ∑ r ∈ Finset.Ioc 0 (q - 1),
            dirichletCosineKernel j.val
              (Real.pi * (r : ℝ) / (q : ℝ)) := by
                apply Finset.sum_congr rfl
                exact hpoint
      _ = (q : ℝ) - 2 * (j.val : ℝ) :=
        sum_dirichletCosineKernel_Ioc hj0 hjq

/-- The finite sine--cotangent identity evaluates the digamma form furnished
by periodic Abel summation. -/
theorem rationalSine_digamma_value_of_finiteCotangent
    (HC : RationalSineCotangentFiniteIdentity)
    {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) :
    (1 / (q : ℝ)) * ∑ r ∈ Finset.Ioc 0 q,
        rationalSinePeriodicTerm j r *
          bblsDigammaShift ((r : ℝ) / q) =
      Real.pi * (1 / 2 - (j.val : ℝ) / q) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hsplitq : Finset.Ioc 0 q =
      insert q (Finset.Ioc 0 (q - 1)) := by
    ext r
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  have hqnotmem : q ∉ Finset.Ioc 0 (q - 1) := by
    simp only [Finset.mem_Ioc]
    omega
  rw [hsplitq, Finset.sum_insert hqnotmem,
    rationalSinePeriodicTerm_modulus, zero_mul, zero_add]
  let S : ℝ := ∑ r ∈ Finset.Ioc 0 (q - 1),
    rationalSinePeriodicTerm j r *
      bblsDigammaShift ((r : ℝ) / q)
  have hreindex : S = ∑ r ∈ Finset.Ioc 0 (q - 1),
      (-rationalSinePeriodicTerm j r) *
        bblsDigammaShift (1 - (r : ℝ) / q) := by
    unfold S
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
      have hrmem := hr
      simp only [Finset.mem_Ioc] at hr
      have hrq : r ≤ q := by omega
      have hsine := rationalSinePeriodicTerm_reflect j hq r hrmem
      have harg : ((q - r : ℕ) : ℝ) / q =
          1 - (r : ℝ) / q := by
        push_cast [Nat.cast_sub hrq]
        field_simp
      rw [hsine, harg]
      ring
  have hdouble : 2 * S = ∑ r ∈ Finset.Ioc 0 (q - 1),
      rationalSinePeriodicTerm j r *
        (Real.pi * Real.cot (Real.pi * ((r : ℝ) / q))) := by
    have htwo : 2 * S = S + S := by ring
    rw [htwo]
    nth_rewrite 2 [hreindex]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_Ioc] at hr
    have hr0 : (0 : ℝ) < (r : ℝ) / q := by
      exact div_pos (by exact_mod_cast hr.1) hqR
    have hr1 : (r : ℝ) / q < 1 := by
      rw [div_lt_one hqR]
      exact_mod_cast (show r < q by omega)
    have hrefl := bblsDigammaShift_reflection hr0 hr1
    calc
      rationalSinePeriodicTerm j r *
            bblsDigammaShift ((r : ℝ) / q) +
          (-rationalSinePeriodicTerm j r) *
            bblsDigammaShift (1 - (r : ℝ) / q) =
        rationalSinePeriodicTerm j r *
          (bblsDigammaShift ((r : ℝ) / q) -
            bblsDigammaShift (1 - (r : ℝ) / q)) := by ring
      _ = rationalSinePeriodicTerm j r *
          (Real.pi * Real.cot (Real.pi * ((r : ℝ) / q))) := by
            rw [hrefl]
  have hcot : ∀ r : ℕ,
      Real.cot (Real.pi * ((r : ℝ) / q)) =
        cotangentTermV r q := by
    intro r
    unfold cotangentTermV
    rw [Real.cot_eq_cos_div_sin]
    congr 2 <;> ring
  have h2S : 2 * S =
      Real.pi * ((q : ℝ) - 2 * (j.val : ℝ)) := by
    calc
      2 * S = Real.pi * ∑ r ∈ Finset.Ioc 0 (q - 1),
          rationalSinePeriodicTerm j r * cotangentTermV r q := by
            rw [hdouble, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r _
            rw [hcot r]
            ring
      _ = Real.pi * ((q : ℝ) - 2 * (j.val : ℝ)) := by
            rw [HC.value_eq j hj]
  have hS : S =
      Real.pi * ((q : ℝ) - 2 * (j.val : ℝ)) / 2 := by
    linarith
  change (1 / (q : ℝ)) * S = _
  rw [hS]
  field_simp

/-- The finite sine--cotangent identity constructs the ordered harmonic
series package. -/
noncomputable def rationalSineHarmonicSeriesFormula_of_finiteCotangent
    (HC : RationalSineCotangentFiniteIdentity) :
    RationalSineHarmonicSeriesFormula where
  tendsto_value := by
    intro q _ j hj
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have h := bbls_tendsto_sum_div_of_periodic_meanzero
      (fun n : ℕ => rationalSinePeriodicTerm j n) q hq
      (rationalSinePeriodicTerm_periodic j)
      (rationalSinePeriodicTerm_meanzero j hj)
    rw [rationalSine_digamma_value_of_finiteCotangent HC j hj] at h
    simpa [rationalSineBoundaryTerm, rationalSinePeriodicTerm] using h

/-- The unconditional ordered rational harmonic sine-series formula. -/
noncomputable def rationalSineHarmonicSeriesFormula :
    RationalSineHarmonicSeriesFormula :=
  rationalSineHarmonicSeriesFormula_of_finiteCotangent
    rationalSineCotangentFiniteIdentity

/-- In the absolutely convergent half-plane, the real sine Dirichlet series
is the real part of `sinZeta`. -/
theorem hasSum_rationalSineBoundary_displaced
    (x d : ℝ) (hd : 0 < d) :
    HasSum
      (fun n : ℕ => rationalSineBoundaryTerm x n * (n : ℝ) ^ (-d))
      (HurwitzZeta.sinZeta x (((1 + d : ℝ) : ℂ))).re := by
  have hs : 1 < ((((1 + d : ℝ) : ℂ))).re := by
    simp
    linarith
  have hcomplex := Complex.hasSum_re
    (HurwitzZeta.hasSum_nat_sinZeta x hs)
  refine hcomplex.congr_fun ?_
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [rationalSineBoundaryTerm]
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [show (((1 + d : ℝ) : ℂ)) = ((1 + d : ℝ) : ℂ) from rfl]
    have hpow : (n : ℂ) ^ (((1 + d : ℝ) : ℂ)) =
        (((n : ℝ) ^ (1 + d) : ℝ) : ℂ) := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast]
      exact (Complex.ofReal_cpow (Nat.cast_nonneg n) (1 + d)).symm
    rw [hpow]
    rw [← Complex.ofReal_div]
    simp only [Complex.ofReal_re]
    unfold rationalSineBoundaryTerm
    rw [Real.rpow_add hnR, Real.rpow_one, Real.rpow_neg (le_of_lt hnR)]
    field_simp

/-- Values on the positive side of the boundary are real. -/
theorem sinZeta_real_on_one_add_pos (x d : ℝ) (hd : 0 < d) :
    (HurwitzZeta.sinZeta x (((1 + d : ℝ) : ℂ))).im = 0 := by
  have hs : 1 < ((((1 + d : ℝ) : ℂ))).re := by
    simp
    linarith
  have him := Complex.hasSum_im (HurwitzZeta.hasSum_nat_sinZeta x hs)
  have hzero : HasSum
      (fun _n : ℕ => (0 : ℝ)) 0 := hasSum_zero
  exact him.unique (hzero.congr_fun fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hpow : (n : ℂ) ^ (((1 + d : ℝ) : ℂ)) =
          (((n : ℝ) ^ (1 + d) : ℝ) : ℂ) := by
        rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast]
        exact (Complex.ofReal_cpow (Nat.cast_nonneg n) (1 + d)).symm
      rw [hpow]
      rw [← Complex.ofReal_div]
      exact Complex.ofReal_im _)

/-- The ordered harmonic-sine evaluation gives the genuine analytic
`sinZeta` endpoint.  This is the reusable Dirichlet--Abelian compatibility
theorem missing from Mathlib's current Hurwitz-value file. -/
noncomputable def rationalSineZetaOneFormula_of_harmonicSeries
    (H : RationalSineHarmonicSeriesFormula) :
    RationalSineZetaOneFormula where
  value_eq := by
    intro q _ j hj
    let x : ℝ := (j.val : ℝ) / q
    let ell : ℝ := Real.pi * (1 / 2 - (j.val : ℝ) / q)
    let F : ℝ → ℝ := fun d =>
      (HurwitzZeta.sinZeta x (((1 + d : ℝ) : ℂ))).re
    have hpartial : Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
          rationalSineBoundaryTerm x n) atTop (𝓝 ell) := by
      simpa [x, ell] using H.tendsto_value j hj
    have habel : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 ell) :=
      dirichlet_abelian_tendsto_of_partial_sum_tendsto
        (rationalSineBoundaryTerm x) F
        (rationalSineBoundaryTerm_zero x) hpartial
        (fun d hd => hasSum_rationalSineBoundary_displaced x d hd)
    have hcontinuous : Tendsto F (𝓝[>] (0 : ℝ))
        (𝓝 (HurwitzZeta.sinZeta x 1).re) := by
      have hfull : Tendsto F (𝓝 (0 : ℝ))
          (𝓝 (HurwitzZeta.sinZeta x 1).re) := by
        have harg : Tendsto (fun d : ℝ => (((1 + d : ℝ) : ℂ)))
            (𝓝 0) (𝓝 1) :=
          by simpa using
            (show ContinuousAt (fun d : ℝ => (((1 + d : ℝ) : ℂ))) 0 by
              fun_prop).tendsto
        have hsin : Tendsto (HurwitzZeta.sinZeta x) (𝓝 1)
            (𝓝 (HurwitzZeta.sinZeta x 1)) :=
          (HurwitzZeta.differentiableAt_sinZeta x 1).continuousAt
        have hcomp := hsin.comp harg
        simpa [F] using
          Complex.continuous_re.continuousAt.tendsto.comp hcomp
      exact tendsto_nhdsWithin_of_tendsto_nhds hfull
    have hre : (HurwitzZeta.sinZeta x 1).re = ell :=
      tendsto_nhds_unique hcontinuous habel
    have himWithin : Tendsto
        (fun d : ℝ => (HurwitzZeta.sinZeta x
          (((1 + d : ℝ) : ℂ))).im)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with d hd
      exact (sinZeta_real_on_one_add_pos x d hd).symm
    have himContinuous : Tendsto
        (fun d : ℝ => (HurwitzZeta.sinZeta x
          (((1 + d : ℝ) : ℂ))).im)
        (𝓝[>] (0 : ℝ)) (𝓝 (HurwitzZeta.sinZeta x 1).im) := by
      have hfull : Tendsto
          (fun d : ℝ => (HurwitzZeta.sinZeta x
            (((1 + d : ℝ) : ℂ))).im)
          (𝓝 (0 : ℝ)) (𝓝 (HurwitzZeta.sinZeta x 1).im) := by
        have harg : Tendsto (fun d : ℝ => (((1 + d : ℝ) : ℂ)))
            (𝓝 0) (𝓝 1) :=
          by simpa using
            (show ContinuousAt (fun d : ℝ => (((1 + d : ℝ) : ℂ))) 0 by
              fun_prop).tendsto
        have hsin : Tendsto (HurwitzZeta.sinZeta x) (𝓝 1)
            (𝓝 (HurwitzZeta.sinZeta x 1)) :=
          (HurwitzZeta.differentiableAt_sinZeta x 1).continuousAt
        have hcomp := hsin.comp harg
        simpa using Complex.continuous_im.continuousAt.tendsto.comp hcomp
      exact tendsto_nhdsWithin_of_tendsto_nhds hfull
    have him : (HurwitzZeta.sinZeta x 1).im = 0 :=
      tendsto_nhds_unique himContinuous himWithin
    have hrhs :
        (Real.pi : ℂ) * ((1 : ℂ) / 2 - (j.val : ℂ) / (q : ℂ)) =
          (ell : ℂ) := by
      simp only [ell, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
        Complex.ofReal_natCast]
    rw [ZMod.toAddCircle_apply]
    rw [hrhs]
    change HurwitzZeta.sinZeta x 1 = (ell : ℂ)
    apply Complex.ext
    · simpa using hre
    · simpa using him

/-- The unconditional rational value of `sinZeta` at `s = 1`. -/
noncomputable def rationalSineZetaOneFormula :
    RationalSineZetaOneFormula :=
  rationalSineZetaOneFormula_of_harmonicSeries
    rationalSineHarmonicSeriesFormula

end RH.Criteria.NymanBeurling.BCFLogTaperRationalSineEndpoint
