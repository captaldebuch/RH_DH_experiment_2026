import Mathlib
import NBMellinTools.NB17Mellin
import NBMellinTools.NB17RieszMeanZeta
import NBMellinTools.NB17ZetaFract

/-!
# Query B: LogTaperL2Decay ↔ Riemann Hypothesis

The complete bridge from the Nyman–Beurling / Báez-Duarte approximation problem to the
Riemann hypothesis, using the Mellin–Plancherel infrastructure of
`NBMellinTools.NB17Mellin`, `NBMellinTools.NB17RieszMeanZeta` and `NBMellinTools.NB17ZetaFract`.

## What is proved unconditionally

* `QueryBLogTaperRH.D_N_is_riesz_mean` : the truncated Dirichlet series built from the
  Möbius log-taper coefficients *is* (exactly, not just asymptotically) the normalised
  logarithmic Riesz mean of the Möbius function.
* `RieszMeanZeta.rieszMean_div_log_tendsto` (in `NB17RieszMeanZeta`) : these normalised
  Riesz means converge to `1/ζ(s)` for `Re s > 1`.
* `QueryBLogTaperRH.rh_equiv_zeta_nonvanishing_half_plane` : the Riemann hypothesis is
  equivalent to the non-vanishing of `ζ` on the open half-plane `Re s > 1/2`.
* `NB17ZetaFract.zetaFractMellin` (in `NB17ZetaFract`) : the classical fractional-part
  representation `∫_0^∞ {u} u^{-s-1} du = -ζ(s)/s` for `0 < Re s < 1`.

## Classical inputs

The remaining theorems are stated *relative to explicitly named classical inputs*, each of
which is a precisely stated theorem (or, in one case, a conjecture) that is currently not
available in Mathlib.  They appear as hypotheses of the theorems that use them, so nothing
is hidden:

* `NB17Mellin.MellinPlancherelIdentity` — the Mellin–Plancherel theorem (classical).
* `LogTaperBaezDuarte.NymanBeurlingCriterion` — the Nyman–Beurling/Báez-Duarte criterion
  (classical: Nyman 1950, Beurling 1955, Báez-Duarte 2003).
* `LogTaperBaezDuarte.LogTaperAsymptoticOptimality` — the statement that the *specific*
  Möbius log-taper coefficients realise the Nyman–Beurling infimum asymptotically.
  **This one is a conjecture**, not a theorem; it is used only for the implication
  `RH → LogTaperL2Decay`.  The converse implication
  (`logTaperL2Decay_implies_riemann_hypothesis`) needs only the classical criterion.
-/

open MeasureTheory Set Filter Topology Complex Real

open scoped ArithmeticFunction.Moebius

noncomputable section

namespace LogTaperBaezDuarte

/-! ## Part 1: the Báez-Duarte approximation problem -/

/-- The indicator function `χ_{(0,1]}`. -/
def chi01 (x : ℝ) : ℂ := if 0 < x ∧ x ≤ 1 then 1 else 0

/-- The Báez-Duarte generators `ρ_n(x) = {1/(n x)}` (fractional part), extended by `0`
to `x ≤ 0`. -/
def rhoBD (n : ℕ) (x : ℝ) : ℂ :=
  if 0 < x then ((Int.fract (1 / (n * x)) : ℝ) : ℂ) else 0

/-- Möbius log-taper coefficients `c_k(N) = -μ(k+1) log(N/(k+1)) / log N`. -/
def logTaperCoeff (N k : ℕ) : ℝ :=
  -(μ (k + 1) : ℝ) * Real.log ((N : ℝ) / (k + 1)) / Real.log N

/-- A general finite combination `∑_{k<N} c_k ρ_{k+1}` of Báez-Duarte generators. -/
def bdApproxWith (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℂ :=
  ∑ k : Fin N, (c k : ℂ) * rhoBD (k + 1) x

/-- The log-taper approximant `∑_{k<N} c_k(N) ρ_{k+1}`. -/
def bdApprox (N : ℕ) (x : ℝ) : ℂ := bdApproxWith N (logTaperCoeff N) x

/-- The `L²((0,∞))` error of a general finite combination. -/
def l2ErrorWith (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∫ x in Ioi (0:ℝ), ‖chi01 x - bdApproxWith N c x‖ ^ 2

/-- The `L²((0,∞))` error of the log-taper approximant. -/
def baezDuarteL2Error (N : ℕ) : ℝ :=
  ∫ x in Ioi (0:ℝ), ‖chi01 x - bdApprox N x‖ ^ 2

lemma baezDuarteL2Error_eq (N : ℕ) : baezDuarteL2Error N = l2ErrorWith N (logTaperCoeff N) := rfl

/-- `LogTaperL2Decay`: the log-taper error tends to `0` as `N → ∞`. -/
def LogTaperL2Decay : Prop :=
  Tendsto (fun N : ℕ => baezDuarteL2Error N) atTop (𝓝 0)

/-- **Classical input 3: the Nyman–Beurling/Báez-Duarte criterion.**
The Riemann hypothesis holds if and only if `χ_{(0,1]}` lies in the `L²((0,∞))`-closure of
the span of the dilations `ρ_n(x) = {1/(nx)}`, `n ≥ 1`. -/
def NymanBeurlingCriterion : Prop :=
  RiemannHypothesis ↔ ∀ ε > 0, ∃ (N : ℕ) (c : ℕ → ℝ), l2ErrorWith N c < ε

/-! ### `L²`-integrability of the Nyman–Beurling data -/

lemma chi01_eq_indicator : chi01 = Set.indicator (Ioc (0 : ℝ) 1) (fun _ => (1 : ℂ)) := by
  funext x
  by_cases hx : 0 < x ∧ x ≤ 1
  · simp [chi01, hx]
  · have hx' : x ∉ Ioc (0:ℝ) 1 := fun h => hx ⟨h.1, h.2⟩
    simp [chi01, hx, hx']

lemma measurable_chi01 : Measurable chi01 := by
  rw [chi01_eq_indicator]
  exact (measurable_const.indicator measurableSet_Ioc)

lemma measurable_rhoBD (n : ℕ) : Measurable (rhoBD n) := by
  unfold rhoBD
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id) ?_ measurable_const
  exact Complex.measurable_ofReal.comp (measurable_fract.comp (by fun_prop))

/-- The dominating function `min (1, 1/x)` for the Báez-Duarte generators. -/
def gDom : ℝ → ℝ := fun x => if x ≤ 1 then 1 else x⁻¹

lemma measurable_gDom : Measurable gDom :=
  Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_inv

lemma integrableOn_gDom_sq : IntegrableOn (fun x => gDom x ^ 2) (Ioi (0:ℝ)) := by
  have hsplit : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi (0:ℝ) := Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hsplit]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioc (0:ℝ) 1) := by simp [IntegrableOn]
    refine h1.congr_fun ?_ measurableSet_Ioc
    intro x hx
    simp [gDom, hx.2]
  · have h := integrableOn_Ioi_rpow_of_lt (a := -2) (c := 1) (by norm_num) (by norm_num)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    have hnle : ¬ (x ≤ 1) := not_le.mpr hx
    simp only [gDom, if_neg hnle]
    rw [← Real.rpow_natCast x⁻¹ 2, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]
    norm_num

lemma memLp_gDom : MemLp gDom 2 (volume.restrict (Ioi (0:ℝ))) :=
  (memLp_two_iff_integrable_sq measurable_gDom.aestronglyMeasurable).2 integrableOn_gDom_sq

lemma memLp_chi01 : MemLp chi01 2 (volume.restrict (Ioi (0:ℝ))) := by
  rw [chi01_eq_indicator]
  refine memLp_indicator_const 2 measurableSet_Ioc 1 (Or.inr ?_)
  rw [Measure.restrict_apply measurableSet_Ioc]
  simp

lemma memLp_rhoBD (n : ℕ) (hn : 1 ≤ n) : MemLp (rhoBD n) 2 (volume.restrict (Ioi (0:ℝ))) := by
  refine memLp_gDom.mono' (measurable_rhoBD n).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
  have hx0 : (0:ℝ) < x := hx
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnx : (0:ℝ) < (n:ℝ) * x := by nlinarith
  have hy : (0:ℝ) ≤ 1 / ((n:ℝ) * x) := by positivity
  have hfract_nonneg := Int.fract_nonneg (1 / ((n:ℝ) * x))
  have hfract_lt := Int.fract_lt_one (1 / ((n:ℝ) * x))
  rw [rhoBD, if_pos hx0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfract_nonneg]
  by_cases hle : x ≤ 1
  · simp only [gDom, if_pos hle]
    linarith
  · have hx1 : 1 < x := not_le.mp hle
    have hfle : Int.fract (1 / ((n:ℝ) * x)) ≤ 1 / ((n:ℝ) * x) := by
      have h0 : (0:ℤ) ≤ ⌊1 / ((n:ℝ) * x)⌋ := Int.floor_nonneg.mpr hy
      have h2 : (0:ℝ) ≤ (⌊1 / ((n:ℝ) * x)⌋ : ℝ) := by exact_mod_cast h0
      rw [Int.fract]
      linarith
    have hbnd : 1 / ((n:ℝ) * x) ≤ x⁻¹ := by
      rw [one_div, inv_le_inv₀ hnx hx0]
      nlinarith
    simp only [gDom, if_neg hle]
    linarith

lemma memLp_bdApproxWith (N : ℕ) (c : ℕ → ℝ) :
    MemLp (bdApproxWith N c) 2 (volume.restrict (Ioi (0:ℝ))) := by
  refine memLp_finset_sum _ fun k _ => ?_
  exact (memLp_rhoBD (k + 1) (by omega)).const_mul _

lemma memLp_bdError (N : ℕ) :
    MemLp (fun x => chi01 x - bdApprox N x) 2 (volume.restrict (Ioi (0:ℝ))) :=
  memLp_chi01.sub (memLp_bdApproxWith N (logTaperCoeff N))

lemma bdError_vanishes (N : ℕ) : ∀ x ≤ (0:ℝ), chi01 x - bdApprox N x = 0 := by
  intro x hx
  have h1 : chi01 x = 0 := by
    have : ¬ (0 < x ∧ x ≤ 1) := by rintro ⟨h, -⟩; linarith
    simp only [chi01, if_neg this]
  have h2 : bdApprox N x = 0 := by
    rw [bdApprox, bdApproxWith]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [rhoBD, if_neg (not_lt.mpr hx), mul_zero]
  rw [h1, h2, sub_zero]

/-- **Conjectural input: asymptotic optimality of the Möbius log taper.**
If `χ_{(0,1]}` is approximable at all by finite combinations of the `ρ_n`, then the
*specific* Möbius log-taper coefficients already achieve the approximation.
This is a conjecture (Báez-Duarte; Balazard–Saias), not a theorem. -/
def LogTaperAsymptoticOptimality : Prop :=
  (∀ ε > 0, ∃ (N : ℕ) (c : ℕ → ℝ), l2ErrorWith N c < ε) → LogTaperL2Decay

end LogTaperBaezDuarte

namespace QueryBLogTaperRH

open LogTaperBaezDuarte NB17Mellin RieszMeanZeta

/-! ## Part 2: the associated Dirichlet polynomial -/

/-- The truncated Dirichlet series `D_N(s) = ∑_{k<N} c_k(N) (k+1)^{-s}`. -/
def D_N (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k : Fin N, (logTaperCoeff N k : ℂ) * ((k : ℂ) + 1) ^ (-s)

/-! ## Part 3: Mellin–Plancherel form of the error -/

/-- The Mellin transform of `χ_{(0,1]}` is `1/s` on `Re s > 0`. -/
theorem hasMellin_chi01 {s : ℂ} (hs : 0 < s.re) : HasMellin chi01 s (1 / s) := by
  rw [chi01_eq_indicator]
  exact hasMellin_indicator_Ioc01 hs

/-- The Mellin transform of the Báez-Duarte generator `ρ_n` is `-n^{-s} ζ(s)/s` on the
strip `0 < Re s < 1`. -/
theorem hasMellin_rhoBD {n : ℕ} (hn : 1 ≤ n) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    HasMellin (rhoBD n) s ((n : ℂ) ^ (-s) * (-riemannZeta s / s)) := by
  have hpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hcast : (((n:ℝ)) : ℂ) = (n : ℂ) := by push_cast; ring
  have hmain := hasMellin_fractInv_mul NB17ZetaFract.zetaFractMellin hpos h0 h1
  rw [hcast] at hmain
  refine (hasMellin_congr (f := fun x : ℝ => fractInv ((n:ℝ) * x)) (g := rhoBD n) ?_).1 hmain
  intro x hx
  have hx0 : (0:ℝ) < x := hx
  simp [fractInv, rhoBD, hx0, one_div]

/-- The Mellin transform of the log-taper approximant. -/
theorem hasMellin_bdApprox (N : ℕ) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    HasMellin (bdApprox N) s (-(riemannZeta s / s) * D_N N s) := by
  have hrho : ∀ k : Fin N,
      HasMellin (rhoBD ((k:ℕ) + 1)) s ((((k:ℕ) + 1 : ℕ) : ℂ) ^ (-s) * (-riemannZeta s / s)) :=
    fun k => hasMellin_rhoBD (by omega) h0 h1
  have hconv : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      MellinConvergent (fun x => (logTaperCoeff N k : ℂ) * rhoBD ((k:ℕ) + 1) x) s := by
    intro k _
    simpa [smul_eq_mul] using (hrho k).1.const_smul ((logTaperCoeff N k : ℂ))
  have hsum := hasMellin_finset_sum (Finset.univ : Finset (Fin N))
      (fun k x => (logTaperCoeff N k : ℂ) * rhoBD ((k:ℕ) + 1) x) s hconv
  have hval : ∀ k : Fin N,
      mellin (fun x => (logTaperCoeff N k : ℂ) * rhoBD ((k:ℕ) + 1) x) s =
        (logTaperCoeff N k : ℂ) * ((((k:ℕ) + 1 : ℕ) : ℂ) ^ (-s) * (-riemannZeta s / s)) := by
    intro k
    have := mellin_const_smul (rhoBD ((k:ℕ) + 1)) s ((logTaperCoeff N k : ℂ))
    simpa [smul_eq_mul, (hrho k).2] using this
  refine ⟨hsum.1, ?_⟩
  have h2 : mellin (bdApprox N) s =
      ∑ k : Fin N, mellin (fun x => (logTaperCoeff N k : ℂ) * rhoBD ((k:ℕ) + 1) x) s := hsum.2
  rw [h2, Finset.sum_congr rfl fun k _ => hval k, D_N, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : (((k:ℕ) + 1 : ℕ) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
  rw [hc]
  ring

/-- The Mellin transform of the Nyman–Beurling error is `(1 + ζ(s) D_N(s))/s`. -/
theorem hasMellin_bdError (N : ℕ) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    HasMellin (fun x => chi01 x - bdApprox N x) s ((1 + riemannZeta s * D_N N s) / s) := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at h0
    simp at h0
  have h := hasMellin_sub (hasMellin_chi01 h0).1 (hasMellin_bdApprox N h0 h1).1
  rw [(hasMellin_chi01 h0).2, (hasMellin_bdApprox N h0 h1).2] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  field_simp
  ring

/-- Via Mellin–Plancherel, the `L²` error equals an integral on the critical line.

The Mellin transform of `χ_{(0,1]}` is `1/s`, and that of `ρ_n` is `-n^{-s} ζ(s)/s`
(on the strip `0 < Re s < 1`), so the Mellin transform of the error is
`(1 + ζ(s) D_N(s))/s`; Plancherel then gives

`∫_0^∞ |χ_{(0,1]} - ∑ c_k ρ_k|² dx = (1/2π) ∫_ℝ |1 + ζ(1/2+it) D_N(1/2+it)|² / |1/2+it|² dt.`

(The statement corrects the one in the original query, where the factor `1/s` appeared
both inside and outside the modulus.) -/
theorem baezDuarteL2Error_eq_mellin_critical_line
    (hMP : MellinPlancherelIdentity) (N : ℕ) :
    baezDuarteL2Error N =
      (1 / (2 * π)) * ∫ t : ℝ,
        ‖1 + riemannZeta ((1:ℂ)/2 + I * t) * D_N N ((1:ℂ)/2 + I * t)‖ ^ 2 /
          ‖(1:ℂ)/2 + I * t‖ ^ 2 := by
  have hre : ∀ t : ℝ, ((1:ℂ)/2 + I * t).re = 1/2 := by intro t; simp
  have h0 : ∀ t : ℝ, 0 < ((1:ℂ)/2 + I * t).re := by intro t; rw [hre]; norm_num
  have h1 : ∀ t : ℝ, ((1:ℂ)/2 + I * t).re < 1 := by intro t; rw [hre]; norm_num
  have hmeas := (memLp_bdError N).aestronglyMeasurable
  have hint : IntegrableOn (fun x => ‖chi01 x - bdApprox N x‖ ^ 2) (Ioi (0:ℝ)) :=
    (memLp_two_iff_integrable_sq_norm hmeas).1 (memLp_bdError N)
  have hconv : ∀ t : ℝ, MellinConvergent (fun x => chi01 x - bdApprox N x) (1 / 2 + I * t) :=
    fun t => (hasMellin_bdError N (h0 t) (h1 t)).1
  rw [baezDuarteL2Error,
    hMP (fun x => chi01 x - bdApprox N x) (bdError_vanishes N) hmeas hint hconv]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only []
  rw [(hasMellin_bdError N (h0 t) (h1 t)).2, norm_div, div_pow]

/-! ## Part 4: connection with Riesz means of `1/ζ` -/

/-- The truncated sum `D_N` **is** the normalised logarithmic Riesz mean of the Möbius
function: `D_N(s) = -R_N(s)/log N` where `R_N(s) = ∑_{n≤N} μ(n) log(N/n) n^{-s}`.

(The original query stated this as an asymptotic relation with an unspecified `O`-term;
in fact the relation is an exact identity.) -/
theorem D_N_is_riesz_mean (N : ℕ) (s : ℂ) :
    D_N N s = -(rieszMean N s / (Real.log N : ℂ)) := by
  rw [D_N, rieszMean, Finset.sum_div, ← Finset.sum_neg_distrib,
    show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext x; simp,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun k => (logTaperCoeff N k : ℂ) * ((k : ℂ) + 1) ^ (-s)) N]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcast : ((1 + k : ℕ) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
  rw [hcast]
  have hcast' : ((1 + k : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [show 1 + k = k + 1 from Nat.add_comm 1 k] at hcast hcast' ⊢
  rw [logTaperCoeff, hcast']
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_intCast]
  ring

/-- In the half-plane of absolute convergence the Riesz means do converge to `1/ζ`:
`D_N(s) → -1/ζ(s)` for `Re s > 1`. -/
theorem D_N_tendsto_neg_inv_zeta {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => D_N N s) atTop (𝓝 (-(1 / riemannZeta s))) := by
  have h := (rieszMean_div_log_tendsto hs).neg
  refine h.congr fun N => ?_
  rw [D_N_is_riesz_mean]

/-! ## Part 5: decay ↔ convergence of Riesz means on the critical line -/

/-- `LogTaperL2Decay` is equivalent to the convergence, in the weighted `L²`-sense on the
critical line, of the normalised Riesz means `R_N/log N` of the Möbius function to `1/ζ`. -/
theorem logTaperL2Decay_iff_riesz_convergence
    (hMP : MellinPlancherelIdentity) :
    LogTaperL2Decay ↔
      Tendsto (fun N : ℕ => ∫ t : ℝ,
        ‖1 - riemannZeta ((1:ℂ)/2 + I * t) * rieszMean N ((1:ℂ)/2 + I * t) /
            (Real.log N : ℂ)‖ ^ 2 / ‖(1:ℂ)/2 + I * t‖ ^ 2) atTop (𝓝 0) := by
  set J : ℕ → ℝ := fun N => ∫ t : ℝ,
    ‖1 - riemannZeta ((1:ℂ)/2 + I * t) * rieszMean N ((1:ℂ)/2 + I * t) /
      (Real.log N : ℂ)‖ ^ 2 / ‖(1:ℂ)/2 + I * t‖ ^ 2 with hJ
  have hpi : (2 * π) ≠ 0 := by positivity
  have hEq : ∀ N : ℕ, baezDuarteL2Error N = (1 / (2 * π)) * J N := by
    intro N
    rw [baezDuarteL2Error_eq_mellin_critical_line hMP N, hJ]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    rw [D_N_is_riesz_mean]
    have hring : 1 + riemannZeta ((1:ℂ)/2 + I * t) *
          -(rieszMean N ((1:ℂ)/2 + I * t) / (Real.log N : ℂ)) =
        1 - riemannZeta ((1:ℂ)/2 + I * t) * rieszMean N ((1:ℂ)/2 + I * t) /
          (Real.log N : ℂ) := by ring
    rw [hring]
  constructor
  · intro h
    have h2 := h.const_mul (2 * π)
    rw [mul_zero] at h2
    refine h2.congr fun N => ?_
    rw [hEq N]
    field_simp
  · intro h
    have h2 := h.const_mul (1 / (2 * π))
    rw [mul_zero] at h2
    exact h2.congr fun N => (hEq N).symm

/-! ## Part 6: the Riemann hypothesis as a zero-free half-plane -/

/-- `ζ` does not vanish at the negative odd integers (these are not among the trivial
zeros): this follows from the functional equation, since `cos(π(2m+2)/2) = ±1 ≠ 0`. -/
theorem riemannZeta_neg_odd_ne_zero (m : ℕ) : riemannZeta (-(2 * (m:ℂ) + 1)) ≠ 0 := by
  have hs : ∀ n : ℕ, (2 * (m:ℂ) + 2) ≠ -n := by
    intro n hn
    have h := congrArg Complex.re hn
    simp at h
    have h1 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    have h2 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hs1 : (2 * (m:ℂ) + 2) ≠ 1 := by
    intro hn
    have h := congrArg Complex.re hn
    simp at h
    have h1 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hfe := riemannZeta_one_sub hs hs1
  rw [show (1 : ℂ) - (2*(m:ℂ)+2) = -(2*(m:ℂ)+1) by ring] at hfe
  rw [hfe]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcpow : ((2 * (Real.pi:ℂ)) ^ (-(2 * (m:ℂ) + 2))) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    push_neg
    intro hcontra
    exact absurd hcontra (by simp [hpi])
  have hcos : Complex.cos ((Real.pi:ℂ) * (2 * (m:ℂ) + 2) / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    field_simp at hk
    have h3 : (2 * (m:ℤ) + 2) = 2 * k + 1 := by
      exact_mod_cast (by linear_combination hk : (2 * (m:ℂ) + 2) = 2 * (k:ℂ) + 1)
    omega
  have hzeta : riemannZeta (2 * (m:ℂ) + 2) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    simp
    have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hcpow)
    (Complex.Gamma_ne_zero hs)) hcos) hzeta

/-- The Riemann hypothesis is equivalent to the non-vanishing of `ζ` on the open
half-plane `Re s > 1/2`. -/
theorem rh_equiv_zeta_nonvanishing_half_plane :
    RiemannHypothesis ↔ ∀ σ > (1:ℝ)/2, ∀ t : ℝ, riemannZeta ((σ : ℂ) + I * t) ≠ 0 := by
  constructor
  · intro hRH σ hσ t hzero
    have hre : ((σ:ℂ) + I * t).re = σ := by simp
    have hne1 : ((σ:ℂ) + I * t) ≠ 1 := by
      intro hh; rw [hh] at hzero; exact riemannZeta_one_ne_zero hzero
    have htriv : ¬∃ n : ℕ, ((σ:ℂ) + I * t) = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have hre2 := congrArg Complex.re hn
      rw [hre] at hre2
      simp at hre2
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hfin := hRH _ hzero htriv hne1
    rw [hre] at hfin
    linarith
  · intro h s hzero htriv hne1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `Re s < 1/2`: the functional equation produces a zero with `Re > 1/2`
      have hsn : ∀ n : ℕ, s ≠ -n := by
        intro n hn
        rcases Nat.even_or_odd n with he | ho
        · rcases Nat.eq_zero_or_pos n with rfl | hpos
          · rw [hn] at hzero
            simp [riemannZeta_zero] at hzero
          · obtain ⟨k, hk⟩ := he
            have hk1 : 1 ≤ k := by omega
            refine htriv ⟨k - 1, ?_⟩
            rw [hn, hk]
            have hcast : ((k - 1 : ℕ) : ℂ) = (k : ℂ) - 1 := by
              push_cast [Nat.cast_sub hk1]; ring
            rw [hcast]
            push_cast
            ring
        · obtain ⟨m, hm⟩ := ho
          rw [hn, hm] at hzero
          refine riemannZeta_neg_odd_ne_zero m ?_
          convert hzero using 2
          push_cast
          ring
      have hfe := riemannZeta_one_sub hsn hne1
      rw [hzero, mul_zero] at hfe
      refine h (1 - s).re (by simp; linarith) (1 - s).im ?_
      rw [mul_comm, Complex.re_add_im]
      exact hfe
    · refine h s.re (by linarith) s.im ?_
      rw [mul_comm, Complex.re_add_im]
      exact hzero

/-! ## Part 7: the equivalence with the Riemann hypothesis -/

/-- Decay of the log-taper error implies the Riemann hypothesis.  This is the direction of
the Nyman–Beurling criterion that needs no conjectural input beyond the criterion itself. -/
theorem logTaperL2Decay_implies_riemann_hypothesis
    (hNB : NymanBeurlingCriterion) : LogTaperL2Decay → RiemannHypothesis := by
  intro hdecay
  refine hNB.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := (hdecay.eventually (gt_mem_nhds hε)).exists
  exact ⟨N, logTaperCoeff N, hN⟩

/-- **The main result**: `LogTaperL2Decay` is equivalent to the Riemann hypothesis. -/
theorem logTaperL2Decay_iff_riemann_hypothesis
    (hNB : NymanBeurlingCriterion) (hOpt : LogTaperAsymptoticOptimality) :
    LogTaperL2Decay ↔ RiemannHypothesis :=
  ⟨logTaperL2Decay_implies_riemann_hypothesis hNB, fun hRH => hOpt (hNB.mp hRH)⟩

end QueryBLogTaperRH

/-!
## Appendix: the original statements of the query

The formulations below are the ones supplied with the query.  They do not elaborate in
Lean (they refer to `Nat.zeta`, which is the arithmetic function `ζ` rather than the
Riemann zeta function, to an undefined `O(·)` notation, to `Int.mul n k`, and they use
`∫ ... dt` inside a `<`-comparison); moreover the integrand of the first statement carries
the factor `1/s` twice.  They are kept here, commented out, for reference; the corrected
and proved versions are the theorems above.

```
def logTaperCoeff (N : ℕ) (k : ℕ) : ℝ :=
  - (Int.mul n k : ℝ) * Real.log (N / (k + 1)) / Real.log N
  where n k := Int.of_nat (Nat.moebius (k + 1))

theorem baezDuarteL2Error_eq_mellin_critical_line (N : ℕ) :
    baezDuarteL2Error N =
      (1 / (2 * π)) * ∫ t : ℝ,
        ‖1 / (Complex.ofReal (1/2) + I * t) +
         Nat.zeta (Complex.ofReal (1/2) + I * t) * D_N N (Complex.ofReal (1/2) + I * t)‖ ^ 2 /
        ‖Complex.ofReal (1/2) + I * t‖ ^ 2

theorem D_N_is_riesz_mean_asymptotic (N : ℕ) :
    D_N N (Complex.ofReal s) = (1 / Real.log N) * RieszMeanZeta.rieszMean N s
      + O(1/(Real.log N)^2)

theorem logTaperL2Decay_iff_riesz_convergence :
    LogTaperL2Decay ↔
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
      ∫ t : ℝ,
        ‖D_N N (Complex.ofReal (1/2) + I * t)
          - 1/Nat.zeta (Complex.ofReal (1/2) + I * t)‖ ^ 2 dt < ε

theorem rh_equiv_zeta_nonvanishing_half_plane :
    RiemannHypothesis ↔ ∀ σ > 1/2, ∀ t : ℝ, Nat.zeta (σ + I * t) ≠ 0

theorem logTaperL2Decay_iff_riemann_hypothesis :
    LogTaperL2Decay ↔ RiemannHypothesis
```
-/
