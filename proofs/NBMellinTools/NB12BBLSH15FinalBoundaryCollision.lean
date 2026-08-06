/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FinalBoundaryFourier
import NBMellinTools.NB12BBLSH15BoundaryDensity

/-!
# NB12zs: residue collisions on the correction-coupled final boundary

The normalized final boundary lies in two intervals of length `L*q` and all
its points are multiples of `L`.  When `L` is coprime to `q`, reduction
modulo `q` is injective on each endpoint interval.  Hence every folded
residue fiber contains at most two points.

This file turns that finite geometry into the sharp coefficient `ℓ²` bound
needed by the Fourier representation from Step 4v-k.  For odd moduli it then
gives an exact Parseval mean-square estimate.  It does not promote a
frequency average to the fixed-frequency signed decay required by H15.
-/

open scoped BigOperators Topology ArithmeticFunction.Moebius ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Injectivity on one endpoint interval -/

/-- Reduction modulo `q` is injective on the multiples of `L` in any
half-open interval of length at most `L*q`, provided `L` and `q` are
coprime. -/
theorem injOn_natCast_h15MultiplesInInterval
    {a b L q : ℕ} (hL : 0 < L)
    (hLq : Nat.Coprime L q) (hab : b ≤ a + L * q) :
    Set.InjOn (fun u : ℕ => (u : ZMod q))
      (h15MultiplesInInterval a b L : Set ℕ) := by
  intro u hu v hv huv
  have hu' := Finset.mem_filter.mp hu
  have hv' := Finset.mem_filter.mp hv
  have huRange := Finset.mem_Ico.mp hu'.1
  have hvRange := Finset.mem_Ico.mp hv'.1
  rcases hu'.2 with ⟨u', rfl⟩
  rcases hv'.2 with ⟨v', rfl⟩
  have hmod : L * u' ≡ L * v' [MOD q] :=
    (ZMod.natCast_eq_natCast_iff (L * u') (L * v') q).mp huv
  have hcop : Nat.gcd q L = 1 := by
    simpa [Nat.gcd_comm] using hLq.gcd_eq_one
  have hmod' : u' ≡ v' [MOD q] :=
    Nat.ModEq.cancel_left_of_coprime hcop hmod
  apply congrArg (fun n => L * n)
  apply hmod'.eq_of_abs_lt
  by_cases huv' : u' ≤ v'
  · have hmul : L * v' < L * (u' + q) := by
      calc
        L * v' < b := hvRange.2
        _ ≤ a + L * q := hab
        _ ≤ L * u' + L * q := Nat.add_le_add_right huRange.1 _
        _ = L * (u' + q) := by rw [Nat.mul_add]
    have hvlt : v' < u' + q := (Nat.mul_lt_mul_left hL).mp hmul
    rw [abs_of_nonneg (by omega)]
    exact_mod_cast (show v' - u' < q by omega)
  · have hvu' : v' ≤ u' := by omega
    have hmul : L * u' < L * (v' + q) := by
      calc
        L * u' < b := huRange.2
        _ ≤ a + L * q := hab
        _ ≤ L * v' + L * q := Nat.add_le_add_right hvRange.1 _
        _ = L * (v' + q) := by rw [Nat.mul_add]
    have hult : u' < v' + q := (Nat.mul_lt_mul_left hL).mp hmul
    rw [abs_of_nonpos (by omega)]
    have hdiff :
        -((v' : ℤ) - (u' : ℤ)) = ((u' - v' : ℕ) : ℤ) := by
      omega
    rw [hdiff]
    exact_mod_cast (show u' - v' < q by omega)

/-- A fixed residue occurs at most once in one short multiple interval. -/
theorem card_filter_h15MultiplesInInterval_natCast_le_one
    {a b L q : ℕ} (hL : 0 < L)
    (hLq : Nat.Coprime L q) (hab : b ≤ a + L * q)
    (x : ZMod q) :
    ((h15MultiplesInInterval a b L).filter
      (fun u : ℕ => (u : ZMod q) = x)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu v hv
  have hu' := Finset.mem_filter.mp hu
  have hv' := Finset.mem_filter.mp hv
  exact injOn_natCast_h15MultiplesInInterval hL hLq hab
    hu'.1 hv'.1 (hu'.2.trans hv'.2.symm)

/-! ## The two-endpoint collision bound -/

/-- Every folded final-boundary residue fiber has cardinality at most two:
at most one point comes from each endpoint interval. -/
theorem card_h15NormalizedBoundaryResidueFiber_le_two
    {U L q : ℕ} (hL : 0 < L) (hq : 0 < q)
    (hLq : Nat.Coprime L q) (x : ZMod q) :
    ((h15NormalizedSuperperiodBoundarySupport U L q).filter
      (fun u : ℕ => (u : ZMod q) = x)).card ≤ 2 := by
  let leftFiber :=
    (h15MultiplesInInterval U (U + L * q) L).filter
      (fun u : ℕ => (u : ZMod q) = x)
  let rightFiber :=
    (h15MultiplesInInterval (2 * U - L * q) (2 * U) L).filter
      (fun u : ℕ => (u : ZMod q) = x)
  calc
    ((h15NormalizedSuperperiodBoundarySupport U L q).filter
        (fun u : ℕ => (u : ZMod q) = x)).card ≤
        (leftFiber ∪ rightFiber).card := by
      apply Finset.card_le_card
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      have huMajorant :=
        h15NormalizedSuperperiodBoundarySupport_subset_densityMajorant
          U L q (Nat.mul_pos hL hq) hu'.1
      rw [h15NormalizedBoundaryEndpointMajorant,
        Finset.mem_union] at huMajorant
      rw [Finset.mem_union]
      rcases huMajorant with huLeft | huRight
      · exact Or.inl (Finset.mem_filter.mpr ⟨huLeft, hu'.2⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨huRight, hu'.2⟩)
    _ ≤ leftFiber.card + rightFiber.card := Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      (card_filter_h15MultiplesInInterval_natCast_le_one
        hL hLq (by omega) x)
      (card_filter_h15MultiplesInInterval_natCast_le_one
        hL hLq (by omega) x)
    _ = 2 := by omega

/-! ## Coefficient `ℓ²` mass -/

/-- Pointwise squared mass of the complete piecewise correction weight on
the exact final boundary. -/
noncomputable def h15NormalizedBoundaryPointL2Mass
    (N g U L q d : ℕ) : ℝ :=
  ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
    (h15NormalizedProgressionCoupledBoundaryPointWeight
      N g U L q d u) ^ 2

/-- A folded coefficient is the complex embedding of the corresponding real
fiber sum. -/
theorem h15NormalizedBoundaryResidueCoefficient_eq_ofReal_sum
    (N g U L q d : ℕ) [NeZero q] (x : ZMod q) :
    h15NormalizedBoundaryResidueCoefficient N g U L q d x =
      ((∑ u ∈ (h15NormalizedSuperperiodBoundarySupport U L q).filter
          (fun u : ℕ => (u : ZMod q) = x),
        h15NormalizedProgressionCoupledBoundaryPointWeight
          N g U L q d u : ℝ) : ℂ) := by
  unfold h15NormalizedBoundaryResidueCoefficient
  push_cast
  rfl

/-- Sharp two-endpoint coefficient bound.  No sign is removed before the
fiber sum; Cauchy--Schwarz is applied only after exact residue folding. -/
theorem h15NormalizedBoundaryResidueL2Mass_le_two_mul_pointL2Mass
    (N g U L q d : ℕ) [NeZero q]
    (hL : 0 < L) (hq : 0 < q) (hLq : Nat.Coprime L q) :
    h15NormalizedBoundaryResidueL2Mass N g U L q d ≤
      2 * h15NormalizedBoundaryPointL2Mass N g U L q d := by
  classical
  unfold h15NormalizedBoundaryResidueL2Mass
    h15NormalizedBoundaryPointL2Mass
  calc
    (∑ x : ZMod q,
        Complex.normSq
          (h15NormalizedBoundaryResidueCoefficient N g U L q d x)) ≤
        ∑ x : ZMod q,
          2 * ∑ u ∈
              (h15NormalizedSuperperiodBoundarySupport U L q).filter
                (fun u : ℕ => (u : ZMod q) = x),
            (h15NormalizedProgressionCoupledBoundaryPointWeight
              N g U L q d u) ^ 2 := by
      apply Finset.sum_le_sum
      intro x _hx
      rw [h15NormalizedBoundaryResidueCoefficient_eq_ofReal_sum,
        Complex.normSq_ofReal]
      calc
        (∑ u ∈
            (h15NormalizedSuperperiodBoundarySupport U L q).filter
              (fun u : ℕ => (u : ZMod q) = x),
          h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L q d u) *
              (∑ u ∈
                (h15NormalizedSuperperiodBoundarySupport U L q).filter
                  (fun u : ℕ => (u : ZMod q) = x),
                h15NormalizedProgressionCoupledBoundaryPointWeight
                  N g U L q d u) ≤
            (((h15NormalizedSuperperiodBoundarySupport U L q).filter
              (fun u : ℕ => (u : ZMod q) = x)).card : ℝ) *
              ∑ u ∈
                (h15NormalizedSuperperiodBoundarySupport U L q).filter
                  (fun u : ℕ => (u : ZMod q) = x),
                (h15NormalizedProgressionCoupledBoundaryPointWeight
                  N g U L q d u) ^ 2 :=
          by
            simpa only [sq] using
              (sq_sum_le_card_mul_sum_sq
                (s := (h15NormalizedSuperperiodBoundarySupport U L q).filter
                  (fun u : ℕ => (u : ZMod q) = x))
                (f := fun u =>
                  h15NormalizedProgressionCoupledBoundaryPointWeight
                    N g U L q d u))
        _ ≤ 2 * ∑ u ∈
              (h15NormalizedSuperperiodBoundarySupport U L q).filter
                (fun u : ℕ => (u : ZMod q) = x),
              (h15NormalizedProgressionCoupledBoundaryPointWeight
                N g U L q d u) ^ 2 := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast
              card_h15NormalizedBoundaryResidueFiber_le_two hL hq hLq x
          · positivity
    _ = 2 * ∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
          (h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L q d u) ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise
        (h15NormalizedSuperperiodBoundarySupport U L q)
        (fun u : ℕ => (u : ZMod q))
        (fun u =>
          (h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L q d u) ^ 2)

/-- Odd-modulus consequence: the exact doubled-character Parseval identity
and the two-endpoint collision theorem cost only the factor `2*q`. -/
theorem h15NormalizedBoundaryFourierMeanSquare_le_of_odd
    (N g U L q d : ℕ) [NeZero q]
    (hL : 0 < L) (hq : 0 < q) (hLq : Nat.Coprime L q)
    (hqOdd : Odd q) :
    h15NormalizedBoundaryFourierMeanSquare N g U L q d ≤
      2 * (q : ℝ) * h15NormalizedBoundaryPointL2Mass N g U L q d := by
  rw [h15NormalizedBoundaryFourierMeanSquare_eq_of_odd
    N g U L q d hqOdd]
  calc
    (q : ℝ) * h15NormalizedBoundaryResidueL2Mass N g U L q d ≤
        (q : ℝ) * (2 * h15NormalizedBoundaryPointL2Mass N g U L q d) := by
      gcongr
      exact h15NormalizedBoundaryResidueL2Mass_le_two_mul_pointL2Mass
        N g U L q d hL hq hLq
    _ = 2 * (q : ℝ) * h15NormalizedBoundaryPointL2Mass N g U L q d := by
      ring

/-! ## Explicit endpoint scale and the fixed-frequency stop test -/

/-- Both pieces of the coupled endpoint coefficient obey the same inverse
square envelope.  The proof keeps the terminal first-Abel increment on the
complete-period sector and uses the original smooth weight only on the
incomplete sector. -/
theorem abs_h15NormalizedProgressionCoupledBoundaryPointWeight_le
    {N g U L q d u : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hq : 0 < q)
    (hu : u ∈ h15NormalizedSuperperiodBoundarySupport U L q) :
    |h15NormalizedProgressionCoupledBoundaryPointWeight
      N g U L q d u| ≤ (1 / (U : ℝ)) ^ 2 := by
  unfold h15NormalizedProgressionCoupledBoundaryPointWeight
  split_ifs with huComplete
  · rw [h15NormalizedCompletePeriodProgressionSupport,
      Finset.mem_biUnion] at huComplete
    rcases huComplete with ⟨k, hk, huk⟩
    rw [natDiv_eq_periodIndex_of_mem_h15NormalizedProgressionQPeriod huk,
      abs_mul]
    calc
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          |h15NormalizedProgressionAbelTerminalWeight N g k q| ≤
          1 * (1 / (U : ℝ)) ^ 2 := by
        apply mul_le_mul
        · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
        · exact abs_h15NormalizedProgressionAbelTerminalWeight_le
            hN hg hU hq hk
        · exact abs_nonneg _
        · norm_num
      _ = (1 / (U : ℝ)) ^ 2 := one_mul _
  · exact abs_h15NormalizedProgressionSmoothWeight_le_of_mem
      hN hg hU (Finset.mem_sdiff.mp hu).1

/-- Explicit pointwise mass bound from the sharp density count and the
common inverse-square envelope. -/
theorem h15NormalizedBoundaryPointL2Mass_le
    {N g U L q d : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hU : 0 < U) (hL : 0 < L) (hq : 0 < q) :
    h15NormalizedBoundaryPointL2Mass N g U L q d ≤
      (2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 := by
  unfold h15NormalizedBoundaryPointL2Mass
  calc
    (∑ u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
        (h15NormalizedProgressionCoupledBoundaryPointWeight
          N g U L q d u) ^ 2) ≤
        ∑ _u ∈ h15NormalizedSuperperiodBoundarySupport U L q,
          (1 / (U : ℝ)) ^ 4 := by
      apply Finset.sum_le_sum
      intro u hu
      calc
        (h15NormalizedProgressionCoupledBoundaryPointWeight
            N g U L q d u) ^ 2 =
            |h15NormalizedProgressionCoupledBoundaryPointWeight
              N g U L q d u| ^ 2 := by rw [sq_abs]
        _ ≤ ((1 / (U : ℝ)) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _)
            (abs_h15NormalizedProgressionCoupledBoundaryPointWeight_le
              hN hg hU hq hu) 2
        _ = (1 / (U : ℝ)) ^ 4 := by ring
    _ = (((h15NormalizedSuperperiodBoundarySupport U L q).card : ℕ) : ℝ) *
        (1 / (U : ℝ)) ^ 4 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_h15NormalizedSuperperiodBoundarySupport_le_density
        U L q hL hq

/-- Explicit odd-modulus frequency mean square. -/
theorem h15NormalizedBoundaryFourierMeanSquare_le_explicit_of_odd
    (N g U L q d : ℕ) [NeZero q]
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hL : 0 < L) (hq : 0 < q) (hLq : Nat.Coprime L q)
    (hqOdd : Odd q) :
    h15NormalizedBoundaryFourierMeanSquare N g U L q d ≤
      (4 * q * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 := by
  calc
    h15NormalizedBoundaryFourierMeanSquare N g U L q d ≤
        2 * (q : ℝ) * h15NormalizedBoundaryPointL2Mass N g U L q d :=
      h15NormalizedBoundaryFourierMeanSquare_le_of_odd
        N g U L q d hL hq hLq hqOdd
    _ ≤ 2 * (q : ℝ) *
        ((2 * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 4) := by
      gcongr
      exact h15NormalizedBoundaryPointL2Mass_le hN hg hU hL hq
    _ = (4 * q * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 := by
      ring

/-- One fixed real row is bounded by the full frequency mean square.  This
is the precise point at which averaging over `r` is lost. -/
theorem sq_h15NormalizedProgressionCoupledBoundaryPointRow_le_meanSquare
    (N g r U L q d : ℕ) (hq : 0 < q) :
    (h15NormalizedProgressionCoupledBoundaryPointRow
      N g r U L q d) ^ 2 ≤
      (letI : NeZero q := ⟨hq.ne'⟩
       h15NormalizedBoundaryFourierMeanSquare N g U L q d) := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [h15NormalizedProgressionCoupledBoundaryPointRow_eq_fourierSum_im
    N g r U L q d hq]
  calc
    (h15NormalizedBoundaryFourierSum
        N g U L q d (r : ZMod q)).im ^ 2 ≤
        Complex.normSq
          (h15NormalizedBoundaryFourierSum
            N g U L q d (r : ZMod q)) := by
      rw [Complex.normSq_apply]
      nlinarith [sq_nonneg
        (h15NormalizedBoundaryFourierSum
          N g U L q d (r : ZMod q)).re]
    _ ≤ ∑ r' : ZMod q,
        Complex.normSq
          (h15NormalizedBoundaryFourierSum N g U L q d r') := by
      exact Finset.single_le_sum
        (fun r' _ => Complex.normSq_nonneg
          (h15NormalizedBoundaryFourierSum N g U L q d r'))
        (Finset.mem_univ (r : ZMod q))

/-- Explicit fixed-frequency consequence on odd moduli.  On balanced
`q ≍ U` blocks its square is `O(U⁻²)`, the same power scale as the previous
absolute endpoint bound.  Thus Parseval alone gives no new global exponent. -/
theorem sq_h15NormalizedProgressionCoupledBoundaryPointRow_le_explicit_of_odd
    (N g r U L q d : ℕ)
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hU : 0 < U)
    (hL : 0 < L) (hq : 0 < q) (hLq : Nat.Coprime L q)
    (hqOdd : Odd q) :
    (h15NormalizedProgressionCoupledBoundaryPointRow
      N g r U L q d) ^ 2 ≤
      (4 * q * (q + 1) : ℝ) * (1 / (U : ℝ)) ^ 4 := by
  letI : NeZero q := ⟨hq.ne'⟩
  exact
    (sq_h15NormalizedProgressionCoupledBoundaryPointRow_le_meanSquare
      N g r U L q d hq).trans
      (h15NormalizedBoundaryFourierMeanSquare_le_explicit_of_odd
        N g U L q d hN hg hU hL hq hLq hqOdd)

end NBMellinTools.NB12
