/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.BaezDuarteTail

/-!
# NB8 (scope file): what is unconditionally true about the Möbius log-taper

`NB8LogTaperTarget.lean` isolates the proposition `LogTaperL2Decay`, i.e.

`lim_{n→∞} ∫_{(0,∞)} (χ_{[0,1]}(x) - ∑_{k<N} c_k(N) ρ_k(x))² dx = 0`,   `N = n+2`,

for the explicit Möbius log-taper coefficients
`c_k(N) = -μ(k+1) log(N/(k+1)) / log N`, where `ρ_k(x) = {1/((k+1)x)}`.
Via the classical Nyman--Beurling/Báez--Duarte theory this statement implies
the Riemann hypothesis (that implication is the content of the missing
`NBMellinTools.NB6GlobalClosure`), so it is not provable by elementary means.

This file develops the part of the programme that *is* unconditional, and pins
down where the RH-strength input has to enter.  It proves:

* integrability: the error integrand is genuinely integrable on `(0,∞)`
  (`integrableOn_sq_bdError`), so none of the statements below is vacuous
  (a non-integrable integrand would make `∫` equal `0` by convention);
* the **Gram expansion** `baezDuarteL2Error_eq_gram`:
  `error = 1 - 2 ∑ c_k m_k + ∑_{j,k} c_j c_k G_{jk}`, together with
  `bdGram_eq`, which splits every Gram entry into a compact piece on `(0,1]`
  plus the exactly computable reciprocal piece `1/((j+1)(k+1))`;
* the moments in closed form, `bdMoment_eq` :
  `m_k = ∫_0^1 ρ_k = (log (k+1) + m_0)/(k+1)` (classically `m_0 = 1 - γ`);
* an exact splitting of the error into its compact part and the reciprocal
  tail, `baezDuarteL2Error_eq_split`;
* the **tail obstruction** `sq_tailScalar_le_baezDuarteL2Error`:
  `(∑ c_k/(k+1))² ≤ error`;
* the **first-moment obstruction** `sq_moment_le_baezDuarteL2Error`:
  `(1 - ∑ c_k m_k)² ≤ error`;
* the **no-finite-stage** theorem `baezDuarteL2Error_pos`: the error is
  *strictly positive* for every finite `N` and every coefficient vector
  whatsoever, so the target is an honest limit; no finite computation can
  certify it and the Nyman--Beurling infimum is never attained;
* the two explicit Möbius-sum statements that `LogTaperL2Decay` therefore
  forces: `logTaper_moebius_tail_tendsto_zero` and
  `logTaper_moebius_moment_tendsto_neg_one`.

The two forced Möbius statements are *necessary* conditions of classical
(Mertens/PNT) strength; they do not come close to being sufficient.  The file
`SCOPE_LogTaperL2Decay.md` records the resulting status report: what remains is
the asymptotic analysis of the Gram quadratic form, which in Mellin--Plancherel
form is exactly the statement that the tapered Möbius Dirichlet polynomial
converges to `-1/ζ` on the critical line, i.e. exactly RH.

The NB8 definitions are repeated here because `NB8LogTaperTarget.lean` cannot be
imported in this repository: its transitive import
`NBMellinTools.NB6GlobalClosure` is not part of this extract.  The definitions
below are copied verbatim from NB8.
-/

open Filter MeasureTheory Set
open scoped BigOperators

namespace NBMellinTools.NB8Scope

open NBMellinTools.NB2

/-! ## The NB8 log-taper data (verbatim copy of `NB8LogTaperTarget.lean`) -/

/-- The total cutoff used at sequence index `n`. -/
def logTaperLength (n : ℕ) : ℕ := n + 2

/-- The explicit real Möbius log-taper coefficients. -/
noncomputable def logTaperCoeffs
    (n : ℕ) (k : Fin (logTaperLength n)) : ℝ :=
  -((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ) *
    (Real.log
        (((logTaperLength n : ℕ) : ℝ) / ((k.val + 1 : ℕ) : ℝ)) /
      Real.log ((logTaperLength n : ℕ) : ℝ))

/-- The exact `L²(0,∞)` error of the explicit log-taper approximant. -/
noncomputable def logTaperL2Error (n : ℕ) : ℝ :=
  BaezDuarteL2Error (logTaperLength n) (logTaperCoeffs n)

/-- The concrete open analytic target for this coefficient family. -/
def LogTaperL2Decay : Prop :=
  Tendsto logTaperL2Error atTop (nhds 0)

/-! ## Elementary bounds on the approximants -/

/-- The reciprocal-tail scalar of a finite approximant: on `(1,∞)` the
approximant is exactly `tailScalar N c / x`. -/
noncomputable def tailScalar (N : ℕ) (c : Fin N → ℝ) : ℝ :=
  ∑ k, c k / (k.val + 1 : ℝ)

theorem measurable_bdApprox (N : ℕ) (c : Fin N → ℝ) :
    Measurable (bdApprox N c) := by
  unfold bdApprox
  exact Finset.measurable_sum _ fun k _ => (measurable_rhoBD k.val).const_mul _

theorem abs_bdApprox_le (N : ℕ) (c : Fin N → ℝ) (x : ℝ) :
    |bdApprox N c x| ≤ ∑ k, |c k| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_of_nonneg (rhoBD_nonneg _ _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (rhoBD_le_one _ _)

theorem abs_bdError_le (N : ℕ) (c : Fin N → ℝ) (x : ℝ) :
    |chi01 x - bdApprox N c x| ≤ 1 + ∑ k, |c k| := by
  have h1 : |chi01 x| ≤ 1 := by
    rw [abs_of_nonneg (chi01_nonneg x)]; exact chi01_le_one x
  exact (abs_sub _ _).trans (add_le_add h1 (abs_bdApprox_le N c x))

/-! ## Integrability and the exact splitting of the error -/

theorem integrableOn_sq_bdError_Ioc (N : ℕ) (c : Fin N → ℝ) :
    IntegrableOn (fun x => (chi01 x - bdApprox N c x) ^ 2) (Ioc (0 : ℝ) 1) := by
  have hmeas : AEStronglyMeasurable
      (fun x => (chi01 x - bdApprox N c x) ^ 2) volume :=
    (((measurable_chi01.sub (measurable_bdApprox N c)).pow_const 2)).aestronglyMeasurable
  refine Measure.integrableOn_of_bounded (M := (1 + ∑ k, |c k|) ^ 2) ?_ hmeas ?_
  · simp
  · filter_upwards with x
    have h := abs_bdError_le N c x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨h1, h2⟩ := abs_le.mp h
    nlinarith

theorem bdError_eq_on_Ioi_one (N : ℕ) (c : Fin N → ℝ) {x : ℝ} (hx : 1 < x) :
    (chi01 x - bdApprox N c x) ^ 2 = (tailScalar N c) ^ 2 * (x ^ (-2 : ℝ)) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  rw [chi_sub_bdApprox_eq_tail_of_one_lt N c hx]
  have hT : (∑ k, c k / (k.val + 1 : ℝ)) = tailScalar N c := rfl
  rw [hT, Real.rpow_neg hx0.le, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num,
    Real.rpow_natCast]
  field_simp

theorem integrableOn_sq_bdError_Ioi_one (N : ℕ) (c : Fin N → ℝ) :
    IntegrableOn (fun x => (chi01 x - bdApprox N c x) ^ 2) (Ioi (1 : ℝ)) := by
  have h : IntegrableOn (fun x : ℝ => (tailScalar N c) ^ 2 * (x ^ (-2 : ℝ))) (Ioi (1:ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  exact (bdError_eq_on_Ioi_one N c hx).symm

theorem integrableOn_sq_bdError (N : ℕ) (c : Fin N → ℝ) :
    IntegrableOn (fun x => (chi01 x - bdApprox N c x) ^ 2) (Ioi (0 : ℝ)) := by
  have hunion : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hunion]
  exact (integrableOn_sq_bdError_Ioc N c).union (integrableOn_sq_bdError_Ioi_one N c)

theorem integral_sq_bdError_Ioi_one (N : ℕ) (c : Fin N → ℝ) :
    ∫ x in Ioi (1:ℝ), (chi01 x - bdApprox N c x) ^ 2 = (tailScalar N c) ^ 2 := by
  have h : ∫ x in Ioi (1:ℝ), (chi01 x - bdApprox N c x) ^ 2
      = ∫ x in Ioi (1:ℝ), (tailScalar N c) ^ 2 * (x ^ (-2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    exact bdError_eq_on_Ioi_one N c hx
  rw [h, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
  norm_num

/-- Exact splitting of the Báez--Duarte error into its compact part and the
square of the reciprocal tail scalar. -/
theorem baezDuarteL2Error_eq_split (N : ℕ) (c : Fin N → ℝ) :
    BaezDuarteL2Error N c
      = (∫ x in Ioc (0:ℝ) 1, (1 - bdApprox N c x) ^ 2) + (tailScalar N c) ^ 2 := by
  have hunion : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  have hdisj : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := by
    simp [Set.disjoint_left]
  unfold BaezDuarteL2Error
  rw [← hunion, setIntegral_union hdisj measurableSet_Ioi
    (integrableOn_sq_bdError_Ioc N c) (integrableOn_sq_bdError_Ioi_one N c),
    integral_sq_bdError_Ioi_one]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
  rw [chi01_of_le_one hx.2]


/-! ## Obstruction 1: the reciprocal tail

Because the error integral contains the whole half line, the single scalar
`tailScalar N c = ∑ c_k/(k+1)` is *exactly* the `L²((1,∞))` part of the error.
Any coefficient family with vanishing error must therefore have vanishing
reciprocal tail. -/

theorem sq_tailScalar_le_baezDuarteL2Error (N : ℕ) (c : Fin N → ℝ) :
    (tailScalar N c) ^ 2 ≤ BaezDuarteL2Error N c := by
  rw [baezDuarteL2Error_eq_split]
  have h : 0 ≤ ∫ x in Ioc (0:ℝ) 1, (1 - bdApprox N c x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  linarith

/-! ## Obstruction 0: no finite stage is ever exact

For every finite `N` and every coefficient vector the error is strictly
positive: on a small interval to the left of `1/N!` all the generators
`ρ_k`, `k < N`, are simultaneously almost `0`, so the approximant cannot be
close to `1` there.  Hence `LogTaperL2Decay` is an honest limit statement; no
finite computation can certify it, and the infimum in the Nyman--Beurling
criterion is never attained. -/

theorem rhoBD_le_of_near_multiple {k K : ℕ} (hdvd : (k + 1) ∣ K) {delta x : ℝ}
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) (hx : 0 < x)
    (h1 : (K : ℝ) < 1 / x) (h2 : 1 / x < (K : ℝ) + delta) :
    rhoBD k x ≤ delta := by
  obtain ⟨q, hq⟩ := hdvd
  have hn : (0 : ℝ) < (k + 1 : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ (k + 1 : ℝ) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hKq : (K : ℝ) = (k + 1 : ℝ) * (q : ℝ) := by exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hq
  have hy : 1 / ((k + 1 : ℝ) * x) = (1 / x) / (k + 1 : ℝ) := by
    field_simp
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hfloor : ⌊(1 / x) / (k + 1 : ℝ)⌋ = (q : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast
      rw [le_div_iff₀ hn]
      nlinarith
    · push_cast
      rw [div_lt_iff₀ hn]
      nlinarith
  have hval : rhoBD k x = (1 / x) / (k + 1 : ℝ) - (q : ℝ) := by
    rw [rhoBD, hy, Int.fract, hfloor]
    push_cast
    ring
  rw [hval, sub_le_iff_le_add, div_le_iff₀ hn]
  nlinarith

theorem abs_bdApprox_le_of_near_multiple (N : ℕ) (c : Fin N → ℝ) {K : ℕ}
    (hdvd : ∀ k : Fin N, (k.val + 1) ∣ K) {delta x : ℝ}
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) (hx : 0 < x)
    (h1 : (K : ℝ) < 1 / x) (h2 : 1 / x < (K : ℝ) + delta) :
    |bdApprox N c x| ≤ (∑ k, |c k|) * delta := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_of_nonneg (rhoBD_nonneg _ _)]
  exact mul_le_mul_of_nonneg_left
    (rhoBD_le_of_near_multiple (hdvd k) hd0 hd1 hx h1 h2) (abs_nonneg _)

theorem baezDuarteL2Error_pos (N : ℕ) (c : Fin N → ℝ) :
    0 < BaezDuarteL2Error N c := by
  classical
  set S : ℝ := ∑ k, |c k| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => abs_nonneg _
  set delta : ℝ := 1 / (2 * (1 + S)) with hdelta
  have hd0 : 0 < delta := by rw [hdelta]; positivity
  have hd1 : delta ≤ 1 := by
    rw [hdelta, div_le_one (by positivity)]
    linarith
  have hSd : S * delta ≤ 1 / 2 := by
    rw [hdelta]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set K : ℕ := Nat.factorial N with hK
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hKpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le zero_lt_one hK1
  have hdvd : ∀ k : Fin N, (k.val + 1) ∣ K :=
    fun k => Nat.dvd_factorial (Nat.succ_pos _) (Nat.succ_le_of_lt k.isLt)
  set a : ℝ := 1 / ((K : ℝ) + delta) with ha
  set b : ℝ := 1 / (K : ℝ) with hb
  have ha0 : 0 < a := by rw [ha]; positivity
  have hab : a < b := by
    rw [ha, hb]
    exact one_div_lt_one_div_of_lt hKpos (by linarith)
  have hb1 : b ≤ 1 := by
    rw [hb, div_le_one hKpos]; exact hK1
  -- pointwise lower bound on the small interval
  have hpt : ∀ x ∈ Ioo a b, (1 : ℝ) / 4 ≤ (chi01 x - bdApprox N c x) ^ 2 := by
    intro x hx
    have hx0 : 0 < x := lt_trans ha0 hx.1
    have hxle : x ≤ 1 := le_trans hx.2.le hb1
    have h1 : (K : ℝ) < 1 / x := by
      have := hx.2
      rw [hb] at this
      calc (K : ℝ) = 1 / (1 / (K : ℝ)) := by field_simp
        _ < 1 / x := one_div_lt_one_div_of_lt hx0 this
    have h2 : 1 / x < (K : ℝ) + delta := by
      have hx1 := hx.1
      rw [ha] at hx1
      have hpos : (0 : ℝ) < (K : ℝ) + delta := by linarith
      calc 1 / x < 1 / (1 / ((K : ℝ) + delta)) := one_div_lt_one_div_of_lt (by positivity) hx1
        _ = (K : ℝ) + delta := by field_simp
    have hbound := abs_bdApprox_le_of_near_multiple N c hdvd hd0 hd1 hx0 h1 h2
    have hhalf : |bdApprox N c x| ≤ 1 / 2 := le_trans hbound hSd
    rw [chi01_of_le_one hxle]
    have := abs_le.mp hhalf
    nlinarith [this.1, this.2]
  have hsub : Ioo a b ⊆ Ioi (0 : ℝ) := fun x hx => lt_trans ha0 hx.1
  have hintIoi := integrableOn_sq_bdError N c
  have hintJ : IntegrableOn (fun x => (chi01 x - bdApprox N c x) ^ 2) (Ioo a b) :=
    hintIoi.mono_set hsub
  have hconst : ∫ _ in Ioo a b, (1 : ℝ) / 4 = (b - a) * (1 / 4) := by
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hab.le]
  have hstep1 : (b - a) * (1 / 4) ≤ ∫ x in Ioo a b, (chi01 x - bdApprox N c x) ^ 2 := by
    rw [← hconst]
    exact setIntegral_mono_on (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)) hintJ measurableSet_Ioo hpt
  have hstep2 : ∫ x in Ioo a b, (chi01 x - bdApprox N c x) ^ 2 ≤ BaezDuarteL2Error N c := by
    refine setIntegral_mono_set hintIoi (ae_of_all _ fun x => sq_nonneg _) ?_
    exact HasSubset.Subset.eventuallyLE hsub
  have hpos : 0 < (b - a) * (1 / 4) := by
    have : 0 < b - a := by linarith
    positivity
  linarith


/-! ## Obstruction 2: the first moment on `(0,1)`

Cauchy--Schwarz on the unit interval (which has measure one) turns the error
into a bound for the *linear* functional `c ↦ ∑ c_k m_k`, where
`m_k = ∫_0^1 ρ_k` is the first moment of the `k`-th generator.  The moments are
computed in closed form below: `m_k = (log (k+1) + m_0)/(k+1)`, with
`m_0 = ∫_0^1 {1/x} dx = 1 - γ` (Euler's constant; the identification of `m_0`
with `1 - γ` is classical and is not needed here). -/

/-- The first moment of the `k`-th Báez--Duarte generator on the unit interval. -/
noncomputable def bdMoment (k : ℕ) : ℝ := ∫ x in Ioc (0:ℝ) 1, rhoBD k x

theorem integrableOn_Ioc01_of_bounded {f : ℝ → ℝ} (hm : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : IntegrableOn f (Ioc (0:ℝ) 1) := by
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hm.aestronglyMeasurable ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

theorem integrableOn_rhoBD_Ioc01 (k : ℕ) : IntegrableOn (rhoBD k) (Ioc (0:ℝ) 1) :=
  integrableOn_Ioc01_of_bounded (measurable_rhoBD k) (C := 1) fun x => by
    rw [abs_of_nonneg (rhoBD_nonneg k x)]; exact rhoBD_le_one k x

theorem integrableOn_bdApprox_Ioc01 (N : ℕ) (c : Fin N → ℝ) :
    IntegrableOn (bdApprox N c) (Ioc (0:ℝ) 1) :=
  integrableOn_Ioc01_of_bounded (measurable_bdApprox N c) (abs_bdApprox_le N c)

theorem integral_bdApprox_Ioc01 (N : ℕ) (c : Fin N → ℝ) :
    ∫ x in Ioc (0:ℝ) 1, bdApprox N c x = ∑ k, c k * bdMoment k.val := by
  unfold bdApprox
  rw [integral_finset_sum _ fun k _ => (integrableOn_rhoBD_Ioc01 k.val).const_mul _]
  exact Finset.sum_congr rfl fun k _ => by rw [integral_const_mul]; rfl

/-- Cauchy--Schwarz on the unit interval. -/
theorem sq_setIntegral_le_setIntegral_sq {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioc (0:ℝ) 1))
    (hf2 : IntegrableOn (fun x => f x ^ 2) (Ioc (0:ℝ) 1)) :
    (∫ x in Ioc (0:ℝ) 1, f x) ^ 2 ≤ ∫ x in Ioc (0:ℝ) 1, f x ^ 2 := by
  set m : ℝ := ∫ x in Ioc (0:ℝ) 1, f x with hm
  have hvol : ∫ _x in Ioc (0:ℝ) 1, (1:ℝ) = 1 := by simp
  have hconstint : IntegrableOn (fun _ : ℝ => m ^ 2 * (1:ℝ)) (Ioc (0:ℝ) 1) :=
    integrableOn_const (by simp)
  have hsubint : IntegrableOn (fun x => f x ^ 2 - (2 * m) * f x) (Ioc (0:ℝ) 1) :=
    hf2.sub (hf.const_mul (2 * m))
  have hexp : ∫ x in Ioc (0:ℝ) 1, (f x - m) ^ 2
      = (∫ x in Ioc (0:ℝ) 1, f x ^ 2) - m ^ 2 := by
    have hpt : ∀ x ∈ Ioc (0:ℝ) 1, (f x - m) ^ 2 = (f x ^ 2 - (2 * m) * f x) + m ^ 2 * 1 := by
      intro x _; ring
    rw [setIntegral_congr_fun measurableSet_Ioc hpt,
      integral_add hsubint hconstint, integral_sub hf2 (hf.const_mul (2 * m)),
      integral_const_mul, integral_const_mul, hvol, ← hm]
    ring
  have hnn : 0 ≤ ∫ x in Ioc (0:ℝ) 1, (f x - m) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  linarith [hexp ▸ hnn]

/-- The first-moment obstruction: the error controls how far the linear
functional `∑ c_k m_k` is from `1`. -/
theorem sq_moment_le_baezDuarteL2Error (N : ℕ) (c : Fin N → ℝ) :
    (1 - ∑ k, c k * bdMoment k.val) ^ 2 ≤ BaezDuarteL2Error N c := by
  have hone : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioc (0:ℝ) 1) := integrableOn_const (by simp)
  have hf : IntegrableOn (fun x => 1 - bdApprox N c x) (Ioc (0:ℝ) 1) :=
    hone.sub (integrableOn_bdApprox_Ioc01 N c)
  have hf2 : IntegrableOn (fun x => (1 - bdApprox N c x) ^ 2) (Ioc (0:ℝ) 1) := by
    have := integrableOn_sq_bdError_Ioc N c
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioc
    rw [chi01_of_le_one hx.2]
  have hlin : ∫ x in Ioc (0:ℝ) 1, (1 - bdApprox N c x)
      = 1 - ∑ k, c k * bdMoment k.val := by
    rw [integral_sub hone (integrableOn_bdApprox_Ioc01 N c),
      integral_bdApprox_Ioc01]
    simp
  have hCS := sq_setIntegral_le_setIntegral_sq hf hf2
  rw [hlin] at hCS
  rw [baezDuarteL2Error_eq_split]
  nlinarith [sq_nonneg (tailScalar N c)]


/-! ### The generator moments in closed form -/

/-- The auxiliary profile `f t = {1/t}`; every generator is a dilate of it. -/
noncomputable def fractInv (t : ℝ) : ℝ := Int.fract (1 / t)

theorem rhoBD_eq_fractInv (k : ℕ) (x : ℝ) : rhoBD k x = fractInv ((k + 1 : ℝ) * x) := rfl

theorem intervalIntegrable_fractInv (a b : ℝ) :
    IntervalIntegrable fractInv volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := 1) ?_ ?_ ?_
  · rw [Set.uIoc]; exact measure_Ioc_lt_top.ne
  · exact (measurable_const.div measurable_id).fract.aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, fractInv, abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le

theorem integral_fractInv_one_to (n : ℕ) :
    ∫ t in (1:ℝ)..((n : ℝ) + 1), fractInv t = Real.log ((n : ℝ) + 1) := by
  have hge : (1:ℝ) ≤ (n : ℝ) + 1 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hcongr : ∫ t in (1:ℝ)..((n : ℝ) + 1), fractInv t
      = ∫ t in (1:ℝ)..((n : ℝ) + 1), 1 / t := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
    have h1 : 1 < t := by
      rcases Set.mem_uIoc.mp ht with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · linarith
    have hpos : 0 < 1 / t := by positivity
    have hlt : 1 / t < 1 := by
      rw [div_lt_one (by linarith)]; exact h1
    rw [fractInv, Int.fract_eq_self.mpr ⟨hpos.le, hlt⟩]
  rw [hcongr, integral_one_div, div_one]
  intro hmem
  rw [Set.mem_uIcc] at hmem
  rcases hmem with ⟨h, _⟩ | ⟨_, h⟩ <;> linarith

/-- Closed form for the generator moments: `m_k = (log (k+1) + m_0)/(k+1)`.
Classically `m_0 = ∫_0^1 {1/x} dx = 1 - γ`. -/
theorem bdMoment_eq (k : ℕ) :
    bdMoment k = (Real.log ((k : ℝ) + 1) + bdMoment 0) / ((k : ℝ) + 1) := by
  have hn : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have h0 : bdMoment 0 = ∫ t in (0:ℝ)..1, fractInv t := by
    rw [bdMoment, ← intervalIntegral.integral_of_le zero_le_one]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [rhoBD_eq_fractInv]
    norm_num
  have hmain : bdMoment k = ∫ x in (0:ℝ)..1, fractInv (((k : ℝ) + 1) * x) := by
    rw [bdMoment, ← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_congr (fun x _ => rhoBD_eq_fractInv k x)
  rw [hmain, intervalIntegral.integral_comp_mul_left (c := (k : ℝ) + 1) _ (ne_of_gt hn),
    mul_zero, mul_one,
    ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_fractInv 0 1) (intervalIntegrable_fractInv 1 ((k : ℝ) + 1)),
    integral_fractInv_one_to k, ← h0, smul_eq_mul]
  field_simp
  ring


/-! ## What `LogTaperL2Decay` forces: two explicit Möbius statements -/

theorem tendsto_zero_of_sq_le {f g : ℕ → ℝ} (h : ∀ n, (f n) ^ 2 ≤ g n)
    (hg : Tendsto g atTop (nhds 0)) : Tendsto f atTop (nhds 0) := by
  have hsq : Tendsto (fun n => (f n) ^ 2) atTop (nhds 0) :=
    squeeze_zero (fun n => sq_nonneg _) h hg
  have habs : Tendsto (fun n => |f n|) atTop (nhds 0) := by
    have hc : Tendsto (fun n => Real.sqrt ((f n) ^ 2)) atTop (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Real.sqrt_sq_eq_abs] using hc
  exact tendsto_zero_iff_abs_tendsto_zero _ |>.2 habs

/-- The log-taper coefficient as a function of a plain natural index. -/
noncomputable def logTaperCoeffNat (n k : ℕ) : ℝ :=
  -((ArithmeticFunction.moebius (k + 1) : ℤ) : ℝ) *
    (Real.log (((logTaperLength n : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) /
      Real.log ((logTaperLength n : ℕ) : ℝ))

theorem logTaperCoeffs_eq_nat (n : ℕ) (k : Fin (logTaperLength n)) :
    logTaperCoeffs n k = logTaperCoeffNat n k.val := rfl

/-- The Möbius sum measuring the reciprocal tail of the log-taper approximant:
`(1/log N) ∑_{m ≤ N} μ(m) log(N/m)/m` with `N = n + 2`. -/
noncomputable def moebiusLogTaperTail (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (logTaperLength n),
      ((ArithmeticFunction.moebius (k + 1) : ℤ) : ℝ)
        * Real.log (((logTaperLength n : ℕ) : ℝ) / ((k : ℝ) + 1)) / ((k : ℝ) + 1))
    / Real.log ((logTaperLength n : ℕ) : ℝ)

theorem tailScalar_logTaper (n : ℕ) :
    tailScalar (logTaperLength n) (logTaperCoeffs n) = -moebiusLogTaperTail n := by
  have hFin : (∑ k : Fin (logTaperLength n), logTaperCoeffs n k / ((k.val : ℝ) + 1))
      = ∑ m ∈ Finset.range (logTaperLength n), logTaperCoeffNat n m / ((m : ℝ) + 1) :=
    Fin.sum_univ_eq_sum_range (fun m : ℕ => logTaperCoeffNat n m / ((m : ℝ) + 1)) _
  rw [moebiusLogTaperTail, Finset.sum_div, ← Finset.sum_neg_distrib, tailScalar, hFin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [logTaperCoeffNat]
  push_cast
  ring

/-- The Möbius sum measuring the first moment of the log-taper approximant. -/
noncomputable def moebiusLogTaperMoment (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (logTaperLength n),
      ((ArithmeticFunction.moebius (k + 1) : ℤ) : ℝ)
        * Real.log (((logTaperLength n : ℕ) : ℝ) / ((k : ℝ) + 1))
        * (Real.log ((k : ℝ) + 1) + bdMoment 0) / ((k : ℝ) + 1))
    / Real.log ((logTaperLength n : ℕ) : ℝ)

theorem moment_logTaper (n : ℕ) :
    (∑ k, logTaperCoeffs n k * bdMoment k.val) = -moebiusLogTaperMoment n := by
  have hFin : (∑ k : Fin (logTaperLength n), logTaperCoeffs n k * bdMoment k.val)
      = ∑ m ∈ Finset.range (logTaperLength n), logTaperCoeffNat n m * bdMoment m :=
    Fin.sum_univ_eq_sum_range (fun m : ℕ => logTaperCoeffNat n m * bdMoment m) _
  rw [moebiusLogTaperMoment, Finset.sum_div, ← Finset.sum_neg_distrib, hFin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [logTaperCoeffNat, bdMoment_eq k]
  push_cast
  ring

/-- **Necessary condition 1** (reciprocal tail).  If the explicit Möbius
log-taper family has vanishing `L²` error, then
`(1/log N) ∑_{m ≤ N} μ(m) log(N/m)/m → 0`.  This is a prime-number-theorem
strength statement about the Möbius function; it is a *consequence* of
`LogTaperL2Decay`, not a substitute for it. -/
theorem logTaper_moebius_tail_tendsto_zero (hdecay : LogTaperL2Decay) :
    Tendsto moebiusLogTaperTail atTop (nhds 0) := by
  refine tendsto_zero_of_sq_le (g := logTaperL2Error) (fun n => ?_) hdecay
  have h := sq_tailScalar_le_baezDuarteL2Error (logTaperLength n) (logTaperCoeffs n)
  rw [tailScalar_logTaper] at h
  simpa [logTaperL2Error, neg_pow] using h

/-- **Necessary condition 2** (first moment).  If the explicit Möbius log-taper
family has vanishing `L²` error, then
`(1/log N) ∑_{m ≤ N} μ(m) log(N/m)(log m + m₀)/m → -1`, where
`m₀ = ∫_0^1 {1/x} dx = 1 - γ`. -/
theorem logTaper_moebius_moment_tendsto_neg_one (hdecay : LogTaperL2Decay) :
    Tendsto moebiusLogTaperMoment atTop (nhds (-1)) := by
  have key : Tendsto (fun n => 1 + moebiusLogTaperMoment n) atTop (nhds 0) := by
    refine tendsto_zero_of_sq_le (g := logTaperL2Error) (fun n => ?_) hdecay
    have h := sq_moment_le_baezDuarteL2Error (logTaperLength n) (logTaperCoeffs n)
    rw [moment_logTaper] at h
    simpa [logTaperL2Error, sub_neg_eq_add] using h
  have := key.sub_const 1
  simpa using this

/-! ## The (unconditional) forward interface

Only the *easy* direction is available unconditionally: a vanishing log-taper
error gives the finite-approximation Nyman--Beurling criterion.  The step from
that criterion to `RiemannHypothesis` is the classical Nyman--Beurling theorem,
supplied in the full package by `NBMellinTools.NB6GlobalClosure` (a file absent
from this repository). -/

theorem nymanBeurlingCriterion_of_logTaperL2Decay (hdecay : LogTaperL2Decay) :
    NymanBeurlingCriterion := by
  intro eps heps
  have heventually : ∀ᶠ n : ℕ in atTop, logTaperL2Error n < eps :=
    hdecay.eventually (Iio_mem_nhds heps)
  obtain ⟨n₀, hn₀⟩ := (eventually_atTop.1 heventually)
  exact ⟨logTaperLength n₀, logTaperCoeffs n₀, hn₀ n₀ le_rfl⟩


/-! ## The full Gram expansion

Steps 1--3 of the programme: expand `‖χ - ∑ c_k ρ_k‖²` into
`1 - 2 ∑ c_k m_k + ∑_{j,k} c_j c_k G_{jk}`, with `G_{jk} = ⟨ρ_j, ρ_k⟩`.
The Gram entries split as a compact piece plus the exactly computable
reciprocal piece `1/((j+1)(k+1))`.  This is the point where the analytic
difficulty is concentrated: the asymptotic behaviour, as `N → ∞`, of the
quadratic form built from the compact pieces
`∫_0^1 {1/((j+1)x)}{1/((k+1)x)} dx` (Vasyunin/cotangent sums) is exactly what
RH controls. -/

theorem integrableOn_Ioi_of_bounds {f : ℝ → ℝ} (hm : Measurable f) {C D : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hD : ∀ x, 1 < x → |f x| ≤ D * x ^ (-2 : ℝ)) :
    IntegrableOn f (Ioi (0:ℝ)) := by
  have h1 : IntegrableOn f (Ioc (0:ℝ) 1) := integrableOn_Ioc01_of_bounded hm hC
  have h2 : IntegrableOn f (Ioi (1:ℝ)) := by
    have hg : IntegrableOn (fun x : ℝ => D * x ^ (-2 : ℝ)) (Ioi (1:ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul D
    refine Integrable.mono' hg hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa [Real.norm_eq_abs] using hD x hx
  have hunion : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hunion]
  exact h1.union h2

theorem Ioc01_subset_Ioi_zero : Ioc (0:ℝ) 1 ⊆ Ioi 0 := fun _ hx => hx.1

theorem Ioi_one_subset_Ioi_zero : Ioi (1:ℝ) ⊆ Ioi 0 := fun _ hx =>
  mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hx))

theorem integral_Ioi_split {f : ℝ → ℝ} (h1 : IntegrableOn f (Ioc (0:ℝ) 1))
    (h2 : IntegrableOn f (Ioi (1:ℝ))) :
    ∫ x in Ioi (0:ℝ), f x = (∫ x in Ioc (0:ℝ) 1, f x) + ∫ x in Ioi (1:ℝ), f x := by
  have hunion : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  have hdisj : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := by simp [Set.disjoint_left]
  rw [← hunion, setIntegral_union hdisj measurableSet_Ioi h1 h2]

/-- The Gram matrix of the Báez--Duarte generators. -/
noncomputable def bdGram (j k : ℕ) : ℝ := ∫ x in Ioi (0:ℝ), rhoBD j x * rhoBD k x

theorem rhoBD_mul_le_inv_sq (j k : ℕ) {x : ℝ} (hx : 1 < x) :
    rhoBD j x * rhoBD k x = (1 / (((j : ℝ) + 1) * ((k : ℝ) + 1))) * x ^ (-2 : ℝ) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  rw [rhoBD_eq_one_div_of_one_lt j hx, rhoBD_eq_one_div_of_one_lt k hx,
    Real.rpow_neg hx0.le, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hk : (0:ℝ) < (k : ℝ) + 1 := by positivity
  field_simp

theorem integrableOn_rhoBD_mul (j k : ℕ) :
    IntegrableOn (fun x => rhoBD j x * rhoBD k x) (Ioi (0:ℝ)) := by
  refine integrableOn_Ioi_of_bounds ((measurable_rhoBD j).mul (measurable_rhoBD k))
    (C := 1) (D := 1) (fun x => ?_) (fun x hx => ?_)
  · rw [abs_mul, abs_of_nonneg (rhoBD_nonneg _ _), abs_of_nonneg (rhoBD_nonneg _ _)]
    exact mul_le_one₀ (rhoBD_le_one _ _) (rhoBD_nonneg _ _) (rhoBD_le_one _ _)
  · have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [rhoBD_mul_le_inv_sq j k hx, one_mul]
    have hj : (1:ℝ) ≤ (j : ℝ) + 1 := by
      have : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hk : (1:ℝ) ≤ (k : ℝ) + 1 := by
      have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hpow : (0:ℝ) < x ^ (-2 : ℝ) := Real.rpow_pos_of_pos hx0 _
    rw [abs_of_nonneg (by positivity)]
    have hle : 1 / (((j : ℝ) + 1) * ((k : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    nlinarith

/-- Splitting of the Gram entries: a compact piece on `(0,1]` plus the exact
reciprocal piece `1/((j+1)(k+1))`. -/
theorem bdGram_eq (j k : ℕ) :
    bdGram j k = (∫ x in Ioc (0:ℝ) 1, rhoBD j x * rhoBD k x)
      + 1 / (((j : ℝ) + 1) * ((k : ℝ) + 1)) := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hk : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hIoi := (integrableOn_rhoBD_mul j k)
  rw [bdGram, integral_Ioi_split (hIoi.mono_set Ioc01_subset_Ioi_zero)
      (hIoi.mono_set Ioi_one_subset_Ioi_zero)]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => rhoBD_mul_le_inv_sq j k hx),
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
  norm_num

theorem integral_sq_chi01 : ∫ x in Ioi (0:ℝ), (chi01 x) ^ 2 = 1 := by
  have hint : IntegrableOn (fun x => (chi01 x) ^ 2) (Ioi (0:ℝ)) := by
    refine integrableOn_Ioi_of_bounds (measurable_chi01.pow_const 2) (C := 1) (D := 0)
      (fun x => ?_) (fun x hx => ?_)
    · rw [abs_of_nonneg (sq_nonneg _)]
      have h0 := chi01_nonneg x
      have h1 := chi01_le_one x
      nlinarith
    · rw [chi01_of_one_lt hx]
      norm_num
  rw [integral_Ioi_split (hint.mono_set Ioc01_subset_Ioi_zero)
      (hint.mono_set Ioi_one_subset_Ioi_zero)]
  have h1 : ∫ x in Ioc (0:ℝ) 1, (chi01 x) ^ 2 = 1 := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun x hx => by rw [chi01_of_le_one hx.2]; norm_num : ∀ x ∈ Ioc (0:ℝ) 1, (chi01 x) ^ 2 = 1)]
    simp
  have h2 : ∫ x in Ioi (1:ℝ), (chi01 x) ^ 2 = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => by rw [chi01_of_one_lt hx]; norm_num : ∀ x ∈ Ioi (1:ℝ), (chi01 x) ^ 2 = 0)]
    simp
  rw [h1, h2, add_zero]

theorem integrableOn_chi01_mul_bdApprox (N : ℕ) (c : Fin N → ℝ) :
    IntegrableOn (fun x => chi01 x * bdApprox N c x) (Ioi (0:ℝ)) := by
  refine integrableOn_Ioi_of_bounds (measurable_chi01.mul (measurable_bdApprox N c))
    (C := ∑ k, |c k|) (D := 0) (fun x => ?_) (fun x hx => ?_)
  · rw [abs_mul, abs_of_nonneg (chi01_nonneg x)]
    have hS : 0 ≤ ∑ k, |c k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    calc chi01 x * |bdApprox N c x| ≤ 1 * |bdApprox N c x| :=
          mul_le_mul_of_nonneg_right (chi01_le_one x) (abs_nonneg _)
      _ ≤ ∑ k, |c k| := by rw [one_mul]; exact abs_bdApprox_le N c x
  · rw [chi01_of_one_lt hx]
    norm_num

theorem integral_chi01_mul_bdApprox (N : ℕ) (c : Fin N → ℝ) :
    ∫ x in Ioi (0:ℝ), chi01 x * bdApprox N c x = ∑ k, c k * bdMoment k.val := by
  have hint := integrableOn_chi01_mul_bdApprox N c
  rw [integral_Ioi_split (hint.mono_set Ioc01_subset_Ioi_zero)
      (hint.mono_set Ioi_one_subset_Ioi_zero)]
  have h1 : ∫ x in Ioc (0:ℝ) 1, chi01 x * bdApprox N c x
      = ∑ k, c k * bdMoment k.val := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun x hx => by rw [chi01_of_le_one hx.2, one_mul] :
        ∀ x ∈ Ioc (0:ℝ) 1, chi01 x * bdApprox N c x = bdApprox N c x)]
    exact integral_bdApprox_Ioc01 N c
  have h2 : ∫ x in Ioi (1:ℝ), chi01 x * bdApprox N c x = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => by rw [chi01_of_one_lt hx, zero_mul] :
        ∀ x ∈ Ioi (1:ℝ), chi01 x * bdApprox N c x = 0)]
    simp
  rw [h1, h2, add_zero]

theorem integral_sq_bdApprox (N : ℕ) (c : Fin N → ℝ) :
    ∫ x in Ioi (0:ℝ), (bdApprox N c x) ^ 2
      = ∑ j, ∑ k, c j * c k * bdGram j.val k.val := by
  have hpt : ∀ x : ℝ, (bdApprox N c x) ^ 2
      = ∑ j, ∑ k, (c j * c k) * (rhoBD j.val x * rhoBD k.val x) := by
    intro x
    rw [sq, bdApprox, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x)]
  rw [integral_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun k _ => (integrableOn_rhoBD_mul j.val k.val).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finset_sum _ fun k _ => (integrableOn_rhoBD_mul j.val k.val).const_mul _]
  exact Finset.sum_congr rfl fun k _ => by rw [integral_const_mul]; rfl

/-- **The Gram expansion of the Báez--Duarte error.**  This is the exact
finite-dimensional quadratic form whose infimum over `c` is `d_N²`. -/
theorem baezDuarteL2Error_eq_gram (N : ℕ) (c : Fin N → ℝ) :
    BaezDuarteL2Error N c
      = 1 - 2 * (∑ k, c k * bdMoment k.val)
        + ∑ j, ∑ k, c j * c k * bdGram j.val k.val := by
  have hchi : IntegrableOn (fun x => (chi01 x) ^ 2) (Ioi (0:ℝ)) := by
    refine integrableOn_Ioi_of_bounds (measurable_chi01.pow_const 2) (C := 1) (D := 0)
      (fun x => ?_) (fun x hx => ?_)
    · rw [abs_of_nonneg (sq_nonneg _)]
      have h0 := chi01_nonneg x
      have h1 := chi01_le_one x
      nlinarith
    · rw [chi01_of_one_lt hx]; norm_num
  have hcross : IntegrableOn (fun x => 2 * (chi01 x * bdApprox N c x)) (Ioi (0:ℝ)) :=
    (integrableOn_chi01_mul_bdApprox N c).const_mul 2
  have hsq : IntegrableOn (fun x => (bdApprox N c x) ^ 2) (Ioi (0:ℝ)) := by
    have hS : 0 ≤ ∑ k, |c k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    refine integrableOn_Ioi_of_bounds ((measurable_bdApprox N c).pow_const 2)
      (C := (∑ k, |c k|) ^ 2) (D := (tailScalar N c) ^ 2) (fun x => ?_) (fun x hx => ?_)
    · rw [abs_of_nonneg (sq_nonneg _)]
      have := abs_bdApprox_le N c x
      have habs : |bdApprox N c x| ^ 2 = (bdApprox N c x) ^ 2 := sq_abs _
      nlinarith [abs_nonneg (bdApprox N c x)]
    · have hx0 : 0 < x := lt_trans zero_lt_one hx
      rw [bdApprox_eq_tail_of_one_lt N c hx]
      have hT : (∑ k, c k / (k.val + 1 : ℝ)) = tailScalar N c := rfl
      rw [hT, Real.rpow_neg hx0.le, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
        abs_of_nonneg (by positivity)]
      field_simp
      exact le_rfl
  have hdiff : IntegrableOn
      (fun x => (chi01 x) ^ 2 - 2 * (chi01 x * bdApprox N c x)) (Ioi (0:ℝ)) :=
    hchi.sub hcross
  have hexp : ∀ x : ℝ, (chi01 x - bdApprox N c x) ^ 2
      = ((chi01 x) ^ 2 - 2 * (chi01 x * bdApprox N c x)) + (bdApprox N c x) ^ 2 := by
    intro x; ring
  unfold BaezDuarteL2Error
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hexp x),
    integral_add hdiff hsq, integral_sub hchi hcross,
    integral_const_mul, integral_sq_chi01, integral_chi01_mul_bdApprox,
    integral_sq_bdApprox]

end NBMellinTools.NB8Scope

