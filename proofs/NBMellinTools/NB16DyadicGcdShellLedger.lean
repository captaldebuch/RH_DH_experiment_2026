/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib

/-!
# NB16: the dyadic / gcd / frequency-shell ledger of the Nyman--Beurling energy

This file is self-contained: it depends only on `Mathlib`.

It supplies the *measure-theoretic* half of the bridge that
`NB15JointLedgerUnification.IsNymanBeurlingEnergySpecialization` asks for,
namely the exact identity

`∑ over dyadic blocks, gcd strata and frequency shells of the local
 "varying row energy"  =  ∫₀^∞ |χ_{(0,1]}(x) - ∑_{k<N} c_k ρ_k(x)|² dx`.

The route is completely explicit:

1. the squared `L²(0,∞)` error is expanded into its constant, linear and
   quadratic parts (this needs genuine integrability input: each generator
   `ρ_k` is bounded by `1` on `(0,1]` and equals `1/((k+1)x)` on `(1,∞)`);
2. the quadratic part is a Gram sum over pairs of generators, the linear part
   a `χ`-pairing, and the constant part is `|(0,1]| = 1`;
3. all three parts are packaged into one *local energy* attached to a pair of
   generators, so that the total error is a sum of local energies over the
   index set `Fin N × Fin N`;
4. that index set is partitioned by the tag
   `(dyadic scale of j+1, dyadic scale of k+1, gcd (j+1) (k+1),
     gcd (j+1) N, gcd (k+1) N)`,
   i.e. by dyadic block, dyadic block, gcd stratum and frequency shell,
   and the sum is refibred along the tag.

The final statement `logTaperL2Error_eq_dyadicGcdShellLedger` is the exact
identity for the NB8 Möbius log-taper coefficients, and
`isNymanBeurlingEnergySpecialization_ledger` inhabits the specialization
predicate for the ledger family.
-/

open MeasureTheory Set Filter
open scoped BigOperators

namespace NBMellinTools.NB16

/-! ## The Báez--Duarte objects

These are the definitions of the active package (`NB2Mellin`, `BaezDuarteTail`,
`NB8LogTaperTarget`), repeated here so that this file has no dependency
outside `Mathlib`. -/

/-- The characteristic function of `(-∞, 1]`; on `(0,∞)` it is `χ_{(0,1]}`. -/
noncomputable def chi01 (x : ℝ) : ℝ := if x ≤ 1 then 1 else 0

/-- The zero-based Báez--Duarte generator `ρ_k(x) = {1/((k+1)x)}`. -/
noncomputable def rhoBD (k : ℕ) (x : ℝ) : ℝ := Int.fract (1 / ((k + 1 : ℝ) * x))

/-- A finite real linear combination of the generators. -/
noncomputable def bdApprox (N : ℕ) (c : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ k, c k * rhoBD k x

/-- The squared `L²(0,∞)` approximation error. -/
noncomputable def BaezDuarteL2Error (N : ℕ) (c : Fin N → ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), (chi01 x - bdApprox N c x) ^ 2

/-- The NB8 cutoff at stage `n`. -/
def logTaperLength (n : ℕ) : ℕ := n + 2

/-- The NB8 explicit Möbius log-taper coefficients. -/
noncomputable def logTaperCoeffs (n : ℕ) (k : Fin (logTaperLength n)) : ℝ :=
  -((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ) *
    (Real.log (((logTaperLength n : ℕ) : ℝ) / ((k.val + 1 : ℕ) : ℝ)) /
      Real.log ((logTaperLength n : ℕ) : ℝ))

/-- The NB8 log-taper `L²` error. -/
noncomputable def logTaperL2Error (n : ℕ) : ℝ :=
  BaezDuarteL2Error (logTaperLength n) (logTaperCoeffs n)

/-! ## Elementary pointwise facts -/

theorem rhoBD_nonneg (k : ℕ) (x : ℝ) : 0 ≤ rhoBD k x := Int.fract_nonneg _

theorem rhoBD_lt_one (k : ℕ) (x : ℝ) : rhoBD k x < 1 := Int.fract_lt_one _

theorem abs_rhoBD_le_one (k : ℕ) (x : ℝ) : |rhoBD k x| ≤ 1 := by
  rw [abs_of_nonneg (rhoBD_nonneg k x)]
  exact (rhoBD_lt_one k x).le

theorem measurable_rhoBD (k : ℕ) : Measurable (rhoBD k) := by
  unfold rhoBD
  exact measurable_fract.comp (by fun_prop)

theorem measurable_chi01 : Measurable chi01 := by
  unfold chi01
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem abs_chi01_le_one (x : ℝ) : |chi01 x| ≤ 1 := by
  unfold chi01; split_ifs <;> norm_num

theorem chi01_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) : chi01 x = 0 := by
  simp [chi01, not_le_of_gt hx]

/-- Above one every generator is exactly reciprocal. -/
theorem rhoBD_eq_one_div_of_one_lt (k : ℕ) {x : ℝ} (hx : 1 < x) :
    rhoBD k x = 1 / ((k + 1 : ℝ) * x) := by
  unfold rhoBD
  rw [Int.fract]
  have hpos : 0 < 1 / ((k + 1 : ℝ) * x) := by positivity
  have hlt : 1 / ((k + 1 : ℝ) * x) < 1 := by
    rw [div_lt_one (by positivity)]
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    nlinarith
  rw [Int.floor_eq_zero_iff.mpr ⟨le_of_lt hpos, hlt⟩]
  norm_num

/-! ## An integrability criterion on `(0,∞)` -/

theorem integrableOn_Ioi_one_div_sq : IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Ioi 1) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := -2) (c := 1) (by norm_num) (by norm_num)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [mem_Ioi] at hx
  show x ^ (-2 : ℝ) = 1 / x ^ 2
  rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg]
  norm_cast
  rw [one_div]

/-- A measurable function that is bounded on `(0,1]` and `O(x⁻²)` on `(1,∞)` is
integrable on `(0,∞)`. -/
theorem integrableOn_Ioi_of_bdd_of_inv_sq {g : ℝ → ℝ} (hm : Measurable g) (M A : ℝ)
    (h1 : ∀ x ∈ Ioc (0 : ℝ) 1, |g x| ≤ M)
    (h2 : ∀ x ∈ Ioi (1 : ℝ), |g x| ≤ A / x ^ 2) :
    IntegrableOn g (Ioi 0) := by
  -- `(0,∞)` is the disjoint union of the finite-measure piece `(0,1]`, where a
  -- bounded measurable function is integrable, and of `(1,∞)`, where the
  -- comparison function `|A|/x²` is integrable.
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := M) (by simp) hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact h1 x hx
  · have hA : IntegrableOn (fun x : ℝ => |A| * (1 / x ^ 2)) (Ioi 1) :=
      integrableOn_Ioi_one_div_sq.const_mul _
    refine Integrable.mono' hA hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hb := h2 x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    calc ‖g x‖ = |g x| := rfl
      _ ≤ A / x ^ 2 := hb
      _ ≤ |A| * (1 / x ^ 2) := by
          rw [mul_one_div, div_le_div_iff_of_pos_right (by positivity)]
          exact le_abs_self A

/-! ## Integrability of the three building blocks -/

theorem integrableOn_chi01_sq : IntegrableOn (fun x : ℝ => chi01 x ^ 2) (Ioi 0) := by
  refine integrableOn_Ioi_of_bdd_of_inv_sq (measurable_chi01.pow_const 2) 1 0 ?_ ?_
  · intro x _
    unfold chi01; split_ifs <;> norm_num
  · intro x hx
    rw [chi01_eq_zero_of_one_lt hx]
    norm_num

theorem integrableOn_chi01_mul_rhoBD (k : ℕ) :
    IntegrableOn (fun x : ℝ => chi01 x * rhoBD k x) (Ioi 0) := by
  refine integrableOn_Ioi_of_bdd_of_inv_sq
    (measurable_chi01.mul (measurable_rhoBD k)) 1 0 ?_ ?_
  · intro x _
    rw [abs_mul]
    calc |chi01 x| * |rhoBD k x| ≤ 1 * 1 :=
          mul_le_mul (abs_chi01_le_one x) (abs_rhoBD_le_one k x) (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  · intro x hx
    rw [chi01_eq_zero_of_one_lt hx]
    norm_num

theorem integrableOn_rhoBD_mul_rhoBD (j k : ℕ) :
    IntegrableOn (fun x : ℝ => rhoBD j x * rhoBD k x) (Ioi 0) := by
  refine integrableOn_Ioi_of_bdd_of_inv_sq
    ((measurable_rhoBD j).mul (measurable_rhoBD k)) 1 1 ?_ ?_
  · intro x _
    rw [abs_mul]
    calc |rhoBD j x| * |rhoBD k x| ≤ 1 * 1 :=
          mul_le_mul (abs_rhoBD_le_one j x) (abs_rhoBD_le_one k x) (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  · -- above `1` the generators are exactly reciprocal, so the product is
    -- `1/((j+1)(k+1)x²) ≤ 1/x²`
    intro x hx
    simp only [mem_Ioi] at hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [rhoBD_eq_one_div_of_one_lt j hx, rhoBD_eq_one_div_of_one_lt k hx]
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [abs_of_nonneg (by positivity)]
    rw [div_mul_div_comm, one_mul]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hjk : (1 : ℝ) ≤ ((j : ℝ) + 1) * ((k : ℝ) + 1) := by nlinarith
    have hxx : (0 : ℝ) < x * x := mul_pos hx0 hx0
    calc x ^ 2 = 1 * (x * x) := by ring
      _ ≤ (((j : ℝ) + 1) * ((k : ℝ) + 1)) * (x * x) := by nlinarith
      _ = ((j : ℝ) + 1) * x * (((k : ℝ) + 1) * x) := by ring

/-! ## The three ledger coefficients -/

/-- The constant part: the mass of `χ_{(0,1]}`. -/
theorem integral_chi01_sq : (∫ x in Ioi (0 : ℝ), chi01 x ^ 2) = 1 := by
  -- `χ² = χ` is the indicator of `(0,1]`, whose Lebesgue measure is `1`.
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [mem_Ioc, mem_Ioi] at hx hx'
    linarith [hx.2]
  have hI1 : IntegrableOn (fun x : ℝ => chi01 x ^ 2) (Ioc 0 1) :=
    integrableOn_chi01_sq.mono_set Ioc_subset_Ioi_self
  have hI2 : IntegrableOn (fun x : ℝ => chi01 x ^ 2) (Ioi 1) :=
    integrableOn_chi01_sq.mono_set (Ioi_subset_Ioi (by norm_num))
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hI1 hI2]
  have h1 : (∫ x in Ioc (0 : ℝ) 1, chi01 x ^ 2) = ∫ _ in Ioc (0 : ℝ) 1, (1 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro x hx
    simp only [mem_Ioc] at hx
    simp [chi01, hx.2]
  have h2 : (∫ x in Ioi (1 : ℝ), chi01 x ^ 2) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero ?_
    intro x hx
    simp only [mem_Ioi] at hx
    simp [chi01, not_le_of_gt hx]
  rw [h1, h2, add_zero]
  simp

/-- The `χ`-pairing of a generator. -/
noncomputable def chiPair (k : ℕ) : ℝ := ∫ x in Ioi (0 : ℝ), chi01 x * rhoBD k x

/-- The Gram coefficient of two generators. -/
noncomputable def gram (j k : ℕ) : ℝ := ∫ x in Ioi (0 : ℝ), rhoBD j x * rhoBD k x

/-! ## The exact quadratic expansion -/

theorem baezDuarteL2Error_eq_expansion (N : ℕ) (c : Fin N → ℝ) :
    BaezDuarteL2Error N c =
      1 - 2 * ∑ k, c k * chiPair k.val +
        ∑ j, ∑ k, c j * c k * gram j.val k.val := by
  classical
  -- Pointwise expansion of the square.
  have hpt : ∀ x : ℝ, (chi01 x - bdApprox N c x) ^ 2 =
      chi01 x ^ 2 - (∑ k, (2 * c k) * (chi01 x * rhoBD k.val x))
        + ∑ j, ∑ k, (c j * c k) * (rhoBD j.val x * rhoBD k.val x) := by
    intro x
    have hsq : (∑ k, c k * rhoBD k.val x) ^ 2 =
        ∑ j, ∑ k, (c j * c k) * (rhoBD j.val x * rhoBD k.val x) := by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have hlin : 2 * chi01 x * (∑ k, c k * rhoBD k.val x) =
        ∑ k, (2 * c k) * (chi01 x * rhoBD k.val x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [bdApprox, sub_sq, hsq, hlin]
  -- Integrability of the three parts.
  have hF1 : IntegrableOn (fun x : ℝ => chi01 x ^ 2) (Ioi 0) := integrableOn_chi01_sq
  have hF2 : IntegrableOn
      (fun x : ℝ => ∑ k, (2 * c k) * (chi01 x * rhoBD k.val x)) (Ioi 0) :=
    integrable_finset_sum _ fun k _ => (integrableOn_chi01_mul_rhoBD k.val).const_mul _
  have hF3 : IntegrableOn
      (fun x : ℝ => ∑ j, ∑ k, (c j * c k) * (rhoBD j.val x * rhoBD k.val x)) (Ioi 0) :=
    integrable_finset_sum _ fun j _ =>
      integrable_finset_sum _ fun k _ =>
        (integrableOn_rhoBD_mul_rhoBD j.val k.val).const_mul _
  unfold BaezDuarteL2Error
  simp_rw [hpt]
  have hF12 : IntegrableOn
      (fun x : ℝ => chi01 x ^ 2 - ∑ k, (2 * c k) * (chi01 x * rhoBD k.val x)) (Ioi 0) :=
    hF1.sub hF2
  rw [integral_add hF12 hF3, integral_sub hF1 hF2, integral_chi01_sq]
  have h2 : (∫ x in Ioi (0 : ℝ), ∑ k, (2 * c k) * (chi01 x * rhoBD k.val x)) =
      2 * ∑ k, c k * chiPair k.val := by
    rw [integral_finset_sum _ fun k _ => (integrableOn_chi01_mul_rhoBD k.val).const_mul _,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [integral_const_mul, chiPair]; ring
  have h3 : (∫ x in Ioi (0 : ℝ), ∑ j, ∑ k, (c j * c k) * (rhoBD j.val x * rhoBD k.val x)) =
      ∑ j, ∑ k, c j * c k * gram j.val k.val := by
    rw [integral_finset_sum _ fun j _ =>
      integrable_finset_sum _ fun k _ => (integrableOn_rhoBD_mul_rhoBD j.val k.val).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finset_sum _ fun k _ => (integrableOn_rhoBD_mul_rhoBD j.val k.val).const_mul _]
    exact Finset.sum_congr rfl fun k _ => by rw [integral_const_mul, gram]
  rw [h2, h3]

/-! ## Local energies -/

/-- The local *varying row energy* attached to a pair of generators.  The
quadratic Gram term is carried by the pair itself, while the linear
`χ`-pairing and the constant mass `1` are shared equally among the `N` pairs
of each row and among all `N²` pairs respectively; summing over all pairs
therefore reproduces the full `L²` error exactly. -/
noncomputable def localEnergy (N : ℕ) (c : Fin N → ℝ) (jk : Fin N × Fin N) : ℝ :=
  c jk.1 * c jk.2 * gram jk.1.val jk.2.val -
      (c jk.1 * chiPair jk.1.val + c jk.2 * chiPair jk.2.val) / (N : ℝ) +
    1 / (N : ℝ) ^ 2

theorem baezDuarteL2Error_eq_sum_localEnergy (N : ℕ) (hN : 0 < N) (c : Fin N → ℝ) :
    BaezDuarteL2Error N c = ∑ jk : Fin N × Fin N, localEnergy N c jk := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  -- each of the `N` rows carries its own `χ`-pairing once, and the constant
  -- mass `1` is shared among the `N²` pairs
  have hproj1 : ∀ f : Fin N → ℝ, ∑ jk : Fin N × Fin N, f jk.1 = (N : ℝ) * ∑ j, f j := by
    intro f; rw [Fintype.sum_prod_type]; simp [Finset.sum_const, Finset.mul_sum]
  have hproj2 : ∀ f : Fin N → ℝ, ∑ jk : Fin N × Fin N, f jk.2 = (N : ℝ) * ∑ j, f j := by
    intro f; rw [Fintype.sum_prod_type]; simp [Finset.sum_const, Finset.mul_sum]
  have hsplit : ∑ jk : Fin N × Fin N, localEnergy N c jk
      = (∑ jk : Fin N × Fin N, c jk.1 * c jk.2 * gram jk.1.val jk.2.val)
        - ((∑ jk : Fin N × Fin N, (c jk.1 * chiPair jk.1.val) / (N : ℝ))
            + ∑ jk : Fin N × Fin N, (c jk.2 * chiPair jk.2.val) / (N : ℝ))
        + ∑ _jk : Fin N × Fin N, (1 / (N : ℝ) ^ 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun jk _ => ?_
    unfold localEnergy
    field_simp
  rw [baezDuarteL2Error_eq_expansion, hsplit,
    hproj1 (fun j => (c j * chiPair j.val) / (N : ℝ)),
    hproj2 (fun j => (c j * chiPair j.val) / (N : ℝ)), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_div]
  field_simp
  push_cast
  ring

/-! ## The dyadic / gcd / frequency-shell tag -/

/-- The ledger tag of a pair of generators: the two dyadic scales, the gcd
stratum, and the frequency shell `(gcd (j+1) N, gcd (k+1) N)` of divisors of
the common cutoff `N`. -/
def ledgerTag (N : ℕ) (jk : Fin N × Fin N) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (Nat.log 2 (jk.1.val + 1), Nat.log 2 (jk.2.val + 1),
    Nat.gcd (jk.1.val + 1) (jk.2.val + 1),
    Nat.gcd (jk.1.val + 1) N, Nat.gcd (jk.2.val + 1) N)

/-- The set of admissible ledger tags: dyadic scales below `log₂ N`, gcd strata
in `[1, N]`, frequency shells made of divisors of `N`. -/
def ledgerTags (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range (Nat.log 2 N + 1)) ×ˢ (Finset.range (Nat.log 2 N + 1)) ×ˢ
    (Finset.Icc 1 N) ×ˢ (Nat.divisors N) ×ˢ (Nat.divisors N)

theorem ledgerTag_mem_ledgerTags (N : ℕ) (hN : 0 < N) (jk : Fin N × Fin N) :
    ledgerTag N jk ∈ ledgerTags N := by
  obtain ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ := jk
  have hjN : j + 1 ≤ N := hj
  have hkN : k + 1 ≤ N := hk
  simp only [ledgerTag, ledgerTags, Finset.mem_product, Finset.mem_range, Finset.mem_Icc,
    Nat.mem_divisors]
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact Nat.lt_succ_of_le (Nat.log_mono_right hjN)
  · exact Nat.lt_succ_of_le (Nat.log_mono_right hkN)
  · exact Nat.succ_le_of_lt (Nat.gcd_pos_of_pos_left _ (Nat.succ_pos j))
  · exact le_trans (Nat.le_of_dvd (Nat.succ_pos j) (Nat.gcd_dvd_left _ _)) hjN
  · exact Nat.gcd_dvd_right _ _
  · exact hN.ne'
  · exact Nat.gcd_dvd_right _ _
  · exact hN.ne'

/-- The energy of one ledger cell. -/
noncomputable def cellEnergy (N : ℕ) (c : Fin N → ℝ) (tag : ℕ × ℕ × ℕ × ℕ × ℕ) : ℝ :=
  ∑ jk ∈ {jk : Fin N × Fin N | ledgerTag N jk = tag}, localEnergy N c jk

/-- **The ledger identity.**  Summing the local varying-row energies over all
dyadic blocks, gcd strata and frequency shells returns the exact `L²(0,∞)`
error of the finite Báez--Duarte approximant. -/
theorem baezDuarteL2Error_eq_ledger_sum (N : ℕ) (hN : 0 < N) (c : Fin N → ℝ) :
    BaezDuarteL2Error N c = ∑ tag ∈ ledgerTags N, cellEnergy N c tag := by
  rw [baezDuarteL2Error_eq_sum_localEnergy N hN c]
  -- the ledger tag maps the index set into the tag set, so refibring along it
  -- is an exact repartition of the sum
  exact (Finset.sum_fiberwise_of_maps_to
    (fun jk _ => ledgerTag_mem_ledgerTags N hN jk) (localEnergy N c)).symm

/-- The ledger identity written out as the five explicit summations over the
two dyadic scales, the gcd stratum and the two frequency-shell divisors. -/
theorem baezDuarteL2Error_eq_ledger_nested_sum (N : ℕ) (hN : 0 < N) (c : Fin N → ℝ) :
    BaezDuarteL2Error N c =
      ∑ a ∈ Finset.range (Nat.log 2 N + 1),
        ∑ b ∈ Finset.range (Nat.log 2 N + 1),
          ∑ d ∈ Finset.Icc 1 N,
            ∑ u ∈ Nat.divisors N,
              ∑ v ∈ Nat.divisors N,
                cellEnergy N c (a, b, d, u, v) := by
  rw [baezDuarteL2Error_eq_ledger_sum N hN c, ledgerTags]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_product]

/-! ## Specialization to the NB8 log-taper family -/

/-- The ledger total for the NB8 log-taper coefficients at stage `n`. -/
noncomputable def logTaperLedgerEnergy (n : ℕ) : ℝ :=
  ∑ tag ∈ ledgerTags (logTaperLength n),
    cellEnergy (logTaperLength n) (logTaperCoeffs n) tag

/-- **The specialization.**  The dyadic/gcd/shell ledger of the NB8 log-taper
family is exactly the certified NB8 log-taper `L²` error. -/
theorem logTaperLedgerEnergy_eq_logTaperL2Error (n : ℕ) :
    logTaperLedgerEnergy n = logTaperL2Error n := by
  have hN : 0 < logTaperLength n := Nat.succ_pos _
  exact (baezDuarteL2Error_eq_ledger_sum (logTaperLength n) hN (logTaperCoeffs n)).symm

/-- The abstract specialization predicate, in the shape used by
`NB15JointLedgerUnification`: a family of energies is an NB energy
specialization when it reproduces the certified log-taper error stagewise. -/
def IsNymanBeurlingEnergySpecialization (energy : ℕ → ℝ) : Prop :=
  ∀ stage : ℕ, energy stage = logTaperL2Error stage

/-- The ledger family inhabits the specialization predicate. -/
theorem isNymanBeurlingEnergySpecialization_ledger :
    IsNymanBeurlingEnergySpecialization logTaperLedgerEnergy :=
  logTaperLedgerEnergy_eq_logTaperL2Error

/-! ## Transport of decay to the Nyman--Beurling criterion

The ledger identity is an exact equality, so any decay statement proved on the
algebraic side transports verbatim to the analytic side.  Nothing below is an
unconditional analytic claim: the decay of the ledger is the input. -/

/-- The finite-approximation form of the Nyman--Beurling criterion. -/
def NymanBeurlingCriterion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ c : Fin N → ℝ, BaezDuarteL2Error N c < ε

theorem baezDuarteL2Error_nonneg (N : ℕ) (c : Fin N → ℝ) : 0 ≤ BaezDuarteL2Error N c := by
  unfold BaezDuarteL2Error
  apply integral_nonneg
  intro x
  positivity

/-- Decay of the dyadic/gcd/shell ledger of the NB8 log-taper family is exactly
decay of the certified log-taper `L²` error, hence gives the criterion. -/
theorem nymanBeurlingCriterion_of_ledgerEnergy_tendsto_zero
    (hdecay : Tendsto logTaperLedgerEnergy atTop (nhds 0)) :
    NymanBeurlingCriterion := by
  intro ε hε
  have hdecay' : Tendsto logTaperL2Error atTop (nhds 0) := by
    refine hdecay.congr ?_
    exact logTaperLedgerEnergy_eq_logTaperL2Error
  obtain ⟨n₀, hn₀⟩ := (eventually_atTop.1 (hdecay'.eventually (Iio_mem_nhds hε)))
  exact ⟨logTaperLength n₀, logTaperCoeffs n₀, hn₀ n₀ le_rfl⟩

end NBMellinTools.NB16
