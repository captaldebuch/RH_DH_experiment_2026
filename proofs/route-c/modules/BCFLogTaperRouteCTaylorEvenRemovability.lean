import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorLocalSubtraction

/-!
# Route C: removability at the negative even integers

Between consecutive odd Taylor poles, the sine denominator also vanishes at
a negative even integer.  These points contribute no residue: the trivial
zero of the Riemann zeta function supplies exactly the same linear factor.

This file constructs the two analytic factors and proves that their quotient
is a genuine local analytic extension of the literal meromorphic integrand.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorEvenRemovability

open Complex Filter Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues

/-- The `n`-th negative even integer, starting with `-2`. -/
def routeCTaylorEvenPoint (n : ℕ) : ℂ :=
  -2 * ((n + 1 : ℕ) : ℂ)

theorem routeCTaylorEvenPoint_ne_one (n : ℕ) :
    routeCTaylorEvenPoint n ≠ 1 := by
  unfold routeCTaylorEvenPoint
  intro h
  have hre : -(2 : ℝ) * ((n + 1 : ℕ) : ℝ) = 1 := by
    simpa using congrArg Complex.re h
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  linarith

theorem riemannZeta_routeCTaylorEvenPoint (n : ℕ) :
    riemannZeta (routeCTaylorEvenPoint n) = 0 := by
  simpa [routeCTaylorEvenPoint] using
    riemannZeta_neg_two_mul_nat_add_one n

theorem sin_pi_mul_routeCTaylorEvenPoint (n : ℕ) :
    Complex.sin ((Real.pi : ℂ) * routeCTaylorEvenPoint n) = 0 := by
  rw [show (Real.pi : ℂ) * routeCTaylorEvenPoint n =
      -(((2 * (n + 1) : ℕ) : ℂ) * (Real.pi : ℂ)) by
        unfold routeCTaylorEvenPoint
        push_cast
        ring]
  rw [Complex.sin_neg, Complex.sin_nat_mul_pi]
  simp

theorem cos_pi_mul_routeCTaylorEvenPoint (n : ℕ) :
    Complex.cos ((Real.pi : ℂ) * routeCTaylorEvenPoint n) = 1 := by
  rw [show (Real.pi : ℂ) * routeCTaylorEvenPoint n =
      -(((n + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ))) by
        unfold routeCTaylorEvenPoint
        push_cast
        ring]
  rw [Complex.cos_neg, Complex.cos_nat_mul_two_pi]

/-- A local analytic factorization of a function with a zero at `p`. -/
structure RouteCTaylorLocalLinearFactor (f : ℂ → ℂ) (p : ℂ) where
  quotient : ℂ → ℂ
  analyticAt_quotient : AnalyticAt ℂ quotient p
  factorization : ∀ s : ℂ, f s = (s - p) * quotient s

/-- Analytic division by the known trivial zero of zeta at `-2(n+1)`. -/
noncomputable def routeCTaylorEvenZetaFactor (n : ℕ) :
    RouteCTaylorLocalLinearFactor riemannZeta
      (routeCTaylorEvenPoint n) := by
  let p := routeCTaylorEvenPoint n
  have hζ : AnalyticAt ℂ riemannZeta p := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [compl_singleton_mem_nhds_iff.mpr
      (routeCTaylorEvenPoint_ne_one n)] with s hs
    exact differentiableAt_riemannZeta hs
  let M : ℂ → ℂ := fun w => riemannZeta (p + w)
  have hM : AnalyticAt ℂ M 0 := by
    have hadd : AnalyticAt ℂ (fun w : ℂ => p + w) 0 := by fun_prop
    have hζ' : AnalyticAt ℂ riemannZeta (p + (0 : ℂ)) := by
      simpa using hζ
    exact hζ'.comp (f := fun w : ℂ => p + w) hadd
  let hex := hM.exists_eq_sum_add_pow_mul 1
  let T : ℂ → ℂ := Classical.choose hex
  have hT : AnalyticAt ℂ T 0 := (Classical.choose_spec hex).1
  have hEq := (Classical.choose_spec hex).2
  let Q : ℂ → ℂ := fun s => T (s - p)
  have hQ : AnalyticAt ℂ Q p := by
    have hsub : AnalyticAt ℂ (fun s : ℂ => s - p) p := by fun_prop
    have hT' : AnalyticAt ℂ T (p - p) := by simpa using hT
    exact hT'.comp (f := fun s : ℂ => s - p) hsub
  refine {
    quotient := Q
    analyticAt_quotient := hQ
    factorization := ?_ }
  intro s
  have hs := hEq (s - p)
  have hpzero : riemannZeta p = 0 := by
    simpa [p] using riemannZeta_routeCTaylorEvenPoint n
  simpa [M, Q, hpzero, Finset.sum_range_succ,
    iteratedDeriv_zero] using hs

/-- Analytic division by the corresponding zero of `sin(πs)`. -/
noncomputable def routeCTaylorEvenSineFactor (n : ℕ) :
    RouteCTaylorLocalLinearFactor
      (fun s : ℂ => Complex.sin ((Real.pi : ℂ) * s))
      (routeCTaylorEvenPoint n) := by
  let p := routeCTaylorEvenPoint n
  let F : ℂ → ℂ := fun s => Complex.sin ((Real.pi : ℂ) * s)
  have hF : AnalyticAt ℂ F p := by
    unfold F
    fun_prop
  let M : ℂ → ℂ := fun w => F (p + w)
  have hM : AnalyticAt ℂ M 0 := by
    have hadd : AnalyticAt ℂ (fun w : ℂ => p + w) 0 := by fun_prop
    have hF' : AnalyticAt ℂ F (p + (0 : ℂ)) := by simpa using hF
    exact hF'.comp (f := fun w : ℂ => p + w) hadd
  let hex := hM.exists_eq_sum_add_pow_mul 1
  let T : ℂ → ℂ := Classical.choose hex
  have hT : AnalyticAt ℂ T 0 := (Classical.choose_spec hex).1
  have hEq := (Classical.choose_spec hex).2
  let Q : ℂ → ℂ := fun s => T (s - p)
  have hQ : AnalyticAt ℂ Q p := by
    have hsub : AnalyticAt ℂ (fun s : ℂ => s - p) p := by fun_prop
    have hT' : AnalyticAt ℂ T (p - p) := by simpa using hT
    exact hT'.comp (f := fun s : ℂ => s - p) hsub
  refine {
    quotient := Q
    analyticAt_quotient := hQ
    factorization := ?_ }
  intro s
  have hs := hEq (s - p)
  have hpzero : F p = 0 := by
    simpa [F, p] using sin_pi_mul_routeCTaylorEvenPoint n
  simpa [M, Q, hpzero, Finset.sum_range_succ,
    iteratedDeriv_zero] using hs

/-- The sine quotient is nonzero at a negative even integer: its value is
the derivative `π cos(πp)=π`. -/
theorem routeCTaylorEvenSineFactor_ne_zero (n : ℕ) :
    (routeCTaylorEvenSineFactor n).quotient
      (routeCTaylorEvenPoint n) ≠ 0 := by
  let p := routeCTaylorEvenPoint n
  let S := routeCTaylorEvenSineFactor n
  have hderiv : HasDerivAt
      (fun s : ℂ => Complex.sin ((Real.pi : ℂ) * s))
      (Real.pi : ℂ) p := by
    have hinner : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) * s)
        (Real.pi : ℂ) p := by
      simpa using (hasDerivAt_id p).const_mul (Real.pi : ℂ)
    have hsin := (Complex.hasDerivAt_sin
      ((Real.pi : ℂ) * p)).comp p hinner
    have hcos : Complex.cos ((Real.pi : ℂ) * p) = 1 := by
      simpa [p] using cos_pi_mul_routeCTaylorEvenPoint n
    rw [hcos] at hsin
    simpa using hsin
  have hQderiv := S.analyticAt_quotient.differentiableAt.hasDerivAt
  have hprod := (hasDerivAt_id p).sub_const p |>.mul hQderiv
  have hprod' : HasDerivAt
      (fun s : ℂ => Complex.sin ((Real.pi : ℂ) * s))
      (S.quotient p) p := by
    convert hprod using 1
    · funext s
      simpa [p] using S.factorization s
    · simp
  have heq : S.quotient p = (Real.pi : ℂ) :=
    (hderiv.unique hprod').symm
  rw [heq]
  exact ofReal_ne_zero.mpr Real.pi_ne_zero

/-- The literal integrand has a genuine analytic extension across every
negative even integer. -/
structure RouteCTaylorEvenRemovableExtension (u : ℂ) (n : ℕ) where
  regularized : ℂ → ℂ
  analyticAt_regularized : AnalyticAt ℂ regularized
    (routeCTaylorEvenPoint n)
  agrees_punctured :
    bettinConreyGZeroMeromorphicIntegrand u =ᶠ[𝓝[≠]
      routeCTaylorEvenPoint n] regularized

noncomputable def routeCTaylorEvenRemovableExtension
    (u : ℂ) (hu : u ≠ 0) (n : ℕ) :
    RouteCTaylorEvenRemovableExtension u n := by
  let p := routeCTaylorEvenPoint n
  let Z := routeCTaylorEvenZetaFactor n
  let S := routeCTaylorEvenSineFactor n
  let R : ℂ → ℂ := fun s =>
    Z.quotient s * riemannZeta (1 - s) / S.quotient s * u ^ (-s)
  have hright : AnalyticAt ℂ (fun s : ℂ => riemannZeta (1 - s)) p := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have hp0 : p ≠ 0 := by
      intro hp
      have hre : -(2 : ℝ) * ((n + 1 : ℕ) : ℝ) = 0 := by
        simpa [p, routeCTaylorEvenPoint] using congrArg Complex.re hp
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      linarith
    filter_upwards [eventually_ne_nhds hp0] with s hs
    have harg : 1 - s ≠ 1 := by
      intro h
      apply hs
      linear_combination -h
    exact (differentiableAt_riemannZeta harg).comp s (by fun_prop)
  have hpow : AnalyticAt ℂ (fun s : ℂ => u ^ (-s)) p := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [] with s
    exact differentiableAt_id.neg.const_cpow (Or.inl hu)
  have hS0 : S.quotient p ≠ 0 := by
    simpa [S, p] using routeCTaylorEvenSineFactor_ne_zero n
  have hR : AnalyticAt ℂ R p := by
    unfold R
    exact ((Z.analyticAt_quotient.mul hright).div
      S.analyticAt_quotient hS0).mul hpow
  refine {
    regularized := R
    analyticAt_regularized := hR
    agrees_punctured := ?_ }
  have hSevent : ∀ᶠ s in 𝓝 p, S.quotient s ≠ 0 :=
    S.analyticAt_quotient.continuousAt.eventually_ne hS0
  filter_upwards [hSevent.filter_mono inf_le_left,
    self_mem_nhdsWithin] with s hSs hsp
  have hsp' : s ≠ p := by simpa using hsp
  have hspEven : s ≠ routeCTaylorEvenPoint n := by
    simpa [p] using hsp'
  unfold bettinConreyGZeroMeromorphicIntegrand R
  rw [Z.factorization, S.factorization]
  field_simp [hspEven, hSs]
  rw [show (s - routeCTaylorEvenPoint n) * Z.quotient s *
        riemannZeta (1 - s) * u ^ (-s) =
      (s - routeCTaylorEvenPoint n) *
        (Z.quotient s * riemannZeta (1 - s) * u ^ (-s)) by ring]
  exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hspEven)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorEvenRemovability
