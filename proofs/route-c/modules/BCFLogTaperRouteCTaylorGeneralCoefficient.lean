import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorBaseCoefficient

/-!
# Route C: arbitrary coefficient normalization

This module generalizes the successful degree-two check in two directions.

First, the coefficient of every odd contour residue of `g₀` is identified
with the corresponding Bettin--Conrey auxiliary coefficient `2*b_(2n)`
after multiplication by the outer factor `pi` from the three-term transfer.
This uses the exact zeta values at `1-2n` and `2n`.

Second, the displayed coefficient `a_m*(-1)^m` is split exactly into its
elementary logarithmic part and its finite binomial residue part.  No
asymptotic estimate occurs here.  The remaining collection step is to prove
that expansion of the transported odd monomials produces precisely that
finite binomial part.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorGeneralCoefficient

open Complex
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorBaseCoefficient
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues

/-- Coefficient of `u^(2n-1)` in the contour-derived finite polynomial for
`g₀`. -/
noncomputable def routeCTaylorGZeroOddMonomialCoefficient (n : ℕ) : ℂ :=
  2 * (-1 : ℂ) ^ n * (((bernoulli (2 * n) : ℚ) : ℂ)) /
      (Nat.factorial (2 * n) : ℂ) *
    riemannZeta (routeCTaylorPolePoint n) *
      (2 * Real.pi : ℂ) ^ (2 * n - 1)

/-- The general normalization identity behind the degree-two calculation:
the outer factor `pi` converts the `n`-th contour residue coefficient into
`2*b_(2n)`. -/
theorem pi_mul_routeCTaylorGZeroOddMonomialCoefficient
    (n : ℕ) (hn : 1 ≤ n) :
    (Real.pi : ℂ) * routeCTaylorGZeroOddMonomialCoefficient n =
      2 * bettinConreyCentralTaylorB (2 * n) := by
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  have hk : 2 * n - 1 + 1 = 2 * n := by omega
  have hp : routeCTaylorPolePoint n =
      -((2 * n - 1 : ℕ) : ℂ) := by
    have h := neg_routeCTaylorPolePoint n hn
    linear_combination -h
  unfold routeCTaylorGZeroOddMonomialCoefficient
    bettinConreyCentralTaylorB
  rw [hp, riemannZeta_neg_nat_eq_bernoulli, hk,
    show ((2 * n : ℕ) : ℂ) =
      (2 : ℂ) * (n : ℂ) by norm_num,
    riemannZeta_two_mul_nat hn0]
  have hfac : (Nat.factorial (2 * n) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  field_simp [hfac, hnC]
  rw [mul_pow]
  have hcast : (((2 * n - 1 : ℕ) : ℂ) + 1) =
      (2 : ℂ) * (n : ℂ) := by
    exact_mod_cast hk
  rw [hcast]
  have hodd : Odd (2 * n - 1) := by
    use n - 1
    omega
  rw [hodd.neg_one_pow]
  rw [show (-1 : ℂ) ^ (n + 1) =
      (-1 : ℂ) ^ n * (-1 : ℂ) by rw [pow_succ]]
  have hpow : (Real.pi : ℂ) *
      (Real.pi : ℂ) ^ (2 * n - 1) =
        (Real.pi : ℂ) ^ (2 * n) := by
    rw [mul_comm, ← pow_succ, hk]
  rw [← hpow]
  ring

/-- Compatibility with the named base coefficient. -/
theorem routeCTaylorGZeroOddMonomialCoefficient_one :
    routeCTaylorGZeroOddMonomialCoefficient 1 =
      routeCTaylorGZeroLinearResidueCoefficient := by
  unfold routeCTaylorGZeroOddMonomialCoefficient
    routeCTaylorGZeroLinearResidueCoefficient routeCTaylorPolePoint
  norm_num

/-- Odd auxiliary coefficients above degree one vanish because their
Bernoulli factor vanishes. -/
theorem bettinConreyCentralTaylorB_eq_zero_of_odd
    (m : ℕ) (hodd : Odd m) (hm : 1 < m) :
    bettinConreyCentralTaylorB m = 0 := by
  unfold bettinConreyCentralTaylorB
  rw [bernoulli_eq_zero_of_odd hodd hm]
  simp

/-! ## Negative-binomial extraction of one transported residue -/

/-- Coefficient of `z^m` in `(z/(1+z))^r`.  It is zero before degree `r`
and is the standard negative-binomial coefficient afterwards. -/
noncomputable def routeCTaylorInversePowerCoefficient
    (r m : ℕ) : ℂ :=
  if r ≤ m then
    (-1 : ℂ) ^ (m - r) *
      ((Nat.choose (m - 1) (r - 1) : ℕ) : ℂ)
  else 0

/-- The shifted negative-binomial row sums to the reciprocal power. -/
theorem hasSum_routeCTaylorInversePowerCoefficient_shift
    (r : ℕ) (hr : 1 ≤ r) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum
      (fun k : ℕ =>
        routeCTaylorInversePowerCoefficient r (k + r) *
          z ^ (k + r))
      ((z / (1 + z)) ^ r) := by
  have hgeom := hasSum_choose_mul_geometric_of_norm_lt_one
    (𝕜 := ℂ) (r - 1) (r := -z) (by simpa using hz)
  have hmul := hgeom.mul_left (z ^ r)
  convert hmul using 1
  · funext k
    unfold routeCTaylorInversePowerCoefficient
    simp only [Nat.le_add_left, if_pos]
    have hsub : k + r - r = k := by omega
    have hone : k + r - 1 = k + (r - 1) := by omega
    rw [hsub, hone]
    rw [show (-z) ^ k = (-1 : ℂ) ^ k * z ^ k by
      rw [neg_pow]]
    rw [pow_add]
    ring
  · have hne : 1 + z ≠ 0 := by
      intro h
      have hzneg : z = -1 := by linear_combination h
      rw [hzneg, norm_neg, norm_one] at hz
      norm_num at hz
    rw [Nat.sub_add_cancel hr]
    simp only [sub_neg_eq_add]
    rw [div_pow]
    field_simp [hne]

/-- Full coefficient series for `(z/(1+z))^r`, including its zero prefix. -/
theorem hasSum_routeCTaylorInversePowerCoefficient
    (r : ℕ) (hr : 1 ≤ r) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum
      (fun m : ℕ =>
        routeCTaylorInversePowerCoefficient r m * z ^ m)
      ((z / (1 + z)) ^ r) := by
  have hprefix : ∑ i ∈ Finset.range r,
      routeCTaylorInversePowerCoefficient r i * z ^ i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    unfold routeCTaylorInversePowerCoefficient
    simp only [Finset.mem_range] at hi
    simp [Nat.not_le.mpr hi]
  apply (hasSum_nat_add_iff' r).mp
  simpa [hprefix] using
    hasSum_routeCTaylorInversePowerCoefficient_shift r hr z hz

/-- Coefficient row of one normalized transported odd residue. -/
noncomputable def routeCTaylorOneResidueScalarCoefficient
    (n m : ℕ) : ℂ :=
  let r := 2 * n - 1
  2 * bettinConreyCentralTaylorB (2 * n) *
    ((if m = r then 1 else 0) +
      (if m = r + 1 then 1 else 0) -
        routeCTaylorInversePowerCoefficient r m)

/-- Each normalized odd residue has the claimed coefficient series on the
unit disc.  This is the analytic source of the later finite binomial
convolution. -/
theorem hasSum_routeCTaylorOneResidueScalarCoefficient
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum
      (fun m : ℕ => routeCTaylorOneResidueScalarCoefficient n m * z ^ m)
      (2 * bettinConreyCentralTaylorB (2 * n) *
        ((1 + z) * z ^ (2 * n - 1) -
          (z / (1 + z)) ^ (2 * n - 1))) := by
  let r := 2 * n - 1
  have hr : 1 ≤ r := by
    dsimp [r]
    omega
  have hfirst : HasSum
      (fun m : ℕ => (if m = r then (1 : ℂ) else 0) * z ^ m)
      (z ^ r) := by
    convert hasSum_ite_eq r (z ^ r) using 1
    funext m
    by_cases hm : m = r <;> simp [hm]
  have hsecond : HasSum
      (fun m : ℕ => (if m = r + 1 then (1 : ℂ) else 0) * z ^ m)
      (z ^ (r + 1)) := by
    convert hasSum_ite_eq (r + 1) (z ^ (r + 1)) using 1
    funext m
    by_cases hm : m = r + 1 <;> simp [hm]
  have hinverse := hasSum_routeCTaylorInversePowerCoefficient r hr z hz
  have hcombined := (hfirst.add hsecond).sub hinverse
  have hscaled := hcombined.mul_left
    (2 * bettinConreyCentralTaylorB (2 * n))
  convert hscaled using 1
  · funext m
    unfold routeCTaylorOneResidueScalarCoefficient
    dsimp [r]
    ring
  · dsimp [r]
    rw [pow_succ]
    ring

/-- Elementary logarithmic contribution to the signed scalar Taylor
coefficient in degree `m`. -/
noncomputable def routeCTaylorElementaryScalarCoefficient (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m /
    ((m : ℂ) * ((m + 1 : ℕ) : ℂ))

/-- Finite residue/binomial contribution predicted by the three-term
transport in degree `m`. -/
noncomputable def routeCTaylorResidueBinomialScalarCoefficient
    (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m *
    (2 * bettinConreyCentralTaylorB m +
      2 * ∑ j ∈ Finset.range (m - 1),
        ((Nat.choose (m - 1) j : ℕ) : ℂ) *
          bettinConreyCentralTaylorB (j + 2))

/-- **Arbitrary-degree coefficient split.**  For every degree occurring in
the paper, the elementary and finite residue rows add to the exact native
Taylor coefficient. -/
theorem routeCTaylorScalarCoefficient_eq_elementary_add_residue
    (m : ℕ) (hm : 2 ≤ m) :
    bettinConreyPsiZeroTaylorScalarCoefficient m =
      routeCTaylorElementaryScalarCoefficient m +
        routeCTaylorResidueBinomialScalarCoefficient m := by
  simp only [bettinConreyPsiZeroTaylorScalarCoefficient, hm, if_pos,
    bettinConreyCentralTaylorCoefficient,
    routeCTaylorElementaryScalarCoefficient,
    routeCTaylorResidueBinomialScalarCoefficient]
  ring

/-- The general split specializes to the independently checked degree-two
contour coefficient. -/
theorem routeCTaylorScalarCoefficient_two_from_general :
    bettinConreyPsiZeroTaylorScalarCoefficient 2 =
      routeCTaylorContourBaseCoefficient := by
  exact routeCTaylorContourBaseCoefficient_eq_scalarCoefficient_two.symm

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorGeneralCoefficient
