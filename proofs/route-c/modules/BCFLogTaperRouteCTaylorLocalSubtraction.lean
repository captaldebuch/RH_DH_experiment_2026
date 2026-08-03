import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFinitePoleGeometry
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelTwoPole

/-!
# Route C: holomorphic subtraction at one odd Taylor pole

A punctured residue limit is not by itself a removable-singularity theorem.
Here the sine denominator is factored analytically at each negative odd
integer.  Dividing the analytic zeta-power numerator by the resulting
nonvanishing factor reduces the pole subtraction to an ordinary first-order
Taylor quotient.

The output is a local analytic remainder whose punctured-neighborhood
decomposition has exactly the residue computed in the preceding module.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorLocalSubtraction

open Complex Filter Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelTwoPole
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues

/-- An entire quotient which factors the sine denominator at one negative
odd Taylor pole. -/
structure RouteCTaylorSineFactor (n : ℕ) where
  quotient : ℂ → ℂ
  differentiable_quotient : Differentiable ℂ quotient
  quotient_at_pole : quotient (routeCTaylorPolePoint n) = -(Real.pi : ℂ)
  factorization : ∀ s : ℂ,
    Complex.sin ((Real.pi : ℂ) * s) =
      (s - routeCTaylorPolePoint n) * quotient s

/-- The exact analytic sine factor at `p_n=1-2n`.  The second-order Taylor
quotient is used so that the value `Q_n(p_n)=-π` is visible definitionally in
the constructed factor. -/
noncomputable def routeCTaylorSineFactor
    (n : ℕ) (hn : 1 ≤ n) : RouteCTaylorSineFactor n := by
  let p := routeCTaylorPolePoint n
  let H : ℂ → ℂ := fun w => Complex.sin ((Real.pi : ℂ) * (p + w))
  have hH : Differentiable ℂ H := by
    intro w
    unfold H
    fun_prop
  have hH0 : H 0 = 0 := by
    simpa [H, p] using sin_pi_mul_routeCTaylorPolePoint n hn
  have hHderiv : deriv H 0 = -(Real.pi : ℂ) := by
    have hinner : HasDerivAt
        (fun w : ℂ => (Real.pi : ℂ) * (p + w))
        (Real.pi : ℂ) 0 := by
      convert ((hasDerivAt_const (x := (0 : ℂ)) (c := p)).add
        (hasDerivAt_id (x := (0 : ℂ)))).const_mul
          (Real.pi : ℂ) using 1 <;> ring
    have hsin := (Complex.hasDerivAt_sin
      ((Real.pi : ℂ) * (p + 0))).comp 0 hinner
    have hcos : Complex.cos ((Real.pi : ℂ) * (p + 0)) = -1 := by
      simpa [p] using cos_pi_mul_routeCTaylorPolePoint n hn
    rw [hcos] at hsin
    simpa [H] using hsin.deriv
  let hex := exists_differentiableOn_secondOrderQuotient
    Set.univ isOpen_univ H hH.differentiableOn (Set.mem_univ 0)
  let R : ℂ → ℂ := Classical.choose hex
  have hR : DifferentiableOn ℂ R Set.univ :=
    (Classical.choose_spec hex).1
  have hEq : ∀ z : ℂ,
      H z = H 0 + z * deriv H 0 + z ^ 2 * R z :=
    (Classical.choose_spec hex).2
  let Q : ℂ → ℂ := fun s =>
    -(Real.pi : ℂ) + (s - p) * R (s - p)
  have hQ : Differentiable ℂ Q := by
    intro s
    unfold Q
    have hRglobal : Differentiable ℂ R := differentiableOn_univ.mp hR
    have hRcomp : DifferentiableAt ℂ (fun z : ℂ => R (z - p)) s :=
      (hRglobal (s - p)).comp s (by fun_prop)
    exact (differentiableAt_const (c := -(Real.pi : ℂ))).add
      ((differentiableAt_id.sub_const p).mul hRcomp)
  refine {
    quotient := Q
    differentiable_quotient := hQ
    quotient_at_pole := by simp [Q, p]
    factorization := ?_ }
  intro s
  have heq := hEq (s - p)
  rw [hH0, hHderiv] at heq
  change Complex.sin ((Real.pi : ℂ) * s) = (s - p) * Q s
  rw [show Complex.sin ((Real.pi : ℂ) * s) = H (s - p) by
    unfold H
    congr 1
    ring]
  rw [heq]
  unfold Q
  ring

/-- The numerator left after removing the sine denominator. -/
noncomputable def routeCTaylorOddPoleNumerator (u s : ℂ) : ℂ :=
  riemannZeta s * riemannZeta (1 - s) * u ^ (-s)

/-- The zeta-power numerator is analytic at every negative odd Taylor pole
for nonzero `u`. -/
theorem analyticAt_routeCTaylorOddPoleNumerator
    (u : ℂ) (hu : u ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    AnalyticAt ℂ (routeCTaylorOddPoleNumerator u)
      (routeCTaylorPolePoint n) := by
  let p := routeCTaylorPolePoint n
  have hp1 : p ≠ 1 := routeCTaylorPolePoint_ne_one n hn
  have hleft : AnalyticAt ℂ riemannZeta p := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [compl_singleton_mem_nhds_iff.mpr hp1] with s hs
    exact differentiableAt_riemannZeta hs
  have hright : AnalyticAt ℂ (fun s : ℂ => riemannZeta (1 - s)) p := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have hp0 : p ≠ 0 := by
      intro hp
      have htwo : (2 * n : ℂ) = 1 := by
        dsimp [p, routeCTaylorPolePoint] at hp
        linear_combination -hp
      have htwoNat : 2 * n = 1 := by exact_mod_cast htwo
      omega
    filter_upwards [eventually_ne_nhds hp0]
      with s hs
    have harg : 1 - s ≠ 1 := by
      intro h
      apply hs
      linear_combination -h
    exact (differentiableAt_riemannZeta harg).comp s (by fun_prop)
  have hpow : AnalyticAt ℂ (fun s : ℂ => u ^ (-s)) p := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [] with s
    exact differentiableAt_id.neg.const_cpow (Or.inl hu)
  exact (hleft.mul hright).mul hpow

/-- Local holomorphic principal-part subtraction at one crossed odd pole. -/
structure RouteCTaylorOddPoleSubtraction
    (u : ℂ) (n : ℕ) where
  regularized : ℂ → ℂ
  analyticAt_regularized : AnalyticAt ℂ regularized
    (routeCTaylorPolePoint n)
  decomposition :
    bettinConreyGZeroMeromorphicIntegrand u =ᶠ[
      𝓝[≠] routeCTaylorPolePoint n]
      (fun s => regularized s +
        bettinConreyGZeroOddResidue u n *
          (s - routeCTaylorPolePoint n)⁻¹)

/-- Construct the genuine analytic remainder from the sine factor and the
first-order Taylor quotient of the analytic numerator divided by it. -/
noncomputable def routeCTaylorOddPoleSubtraction
    (u : ℂ) (hu : u ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    RouteCTaylorOddPoleSubtraction u n := by
  let p := routeCTaylorPolePoint n
  let S := routeCTaylorSineFactor n hn
  let A : ℂ → ℂ := routeCTaylorOddPoleNumerator u
  let B : ℂ → ℂ := fun s => A s / S.quotient s
  have hA : AnalyticAt ℂ A p :=
    analyticAt_routeCTaylorOddPoleNumerator u hu n hn
  have hQ : AnalyticAt ℂ S.quotient p := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    exact Eventually.of_forall S.differentiable_quotient
  have hQ0 : S.quotient p ≠ 0 := by
    rw [S.quotient_at_pole]
    exact neg_ne_zero.mpr (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hB : AnalyticAt ℂ B p := hA.div hQ hQ0
  have hBp : B p = bettinConreyGZeroOddResidue u n := by
    unfold B A routeCTaylorOddPoleNumerator
    rw [S.quotient_at_pole, one_sub_routeCTaylorPolePoint,
      neg_routeCTaylorPolePoint n hn, cpow_natCast]
    unfold bettinConreyGZeroOddResidue
    field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring
  let M : ℂ → ℂ := fun w => B (p + w)
  have hM : AnalyticAt ℂ M 0 := by
    unfold M
    have hadd : AnalyticAt ℂ (fun w : ℂ => p + w) 0 := by fun_prop
    have hBat : AnalyticAt ℂ B (p + (0 : ℂ)) := by simpa using hB
    exact hBat.comp (f := fun w : ℂ => p + w) hadd
  let hex := hM.exists_eq_sum_add_pow_mul 1
  let T : ℂ → ℂ := Classical.choose hex
  have hT : AnalyticAt ℂ T 0 := (Classical.choose_spec hex).1
  have hEq := (Classical.choose_spec hex).2
  let R : ℂ → ℂ := fun s => T (s - p)
  have hR : AnalyticAt ℂ R p := by
    unfold R
    have hsub : AnalyticAt ℂ (fun s : ℂ => s - p) p := by fun_prop
    have hT' : AnalyticAt ℂ T (p - p) := by simpa using hT
    exact hT'.comp (f := fun s : ℂ => s - p) hsub
  have hEq' : ∀ s : ℂ, B s = B p + (s - p) * R s := by
    intro s
    have hs := hEq (s - p)
    simpa [M, R, Finset.sum_range_succ, iteratedDeriv_zero] using hs
  refine {
    regularized := R
    analyticAt_regularized := hR
    decomposition := ?_ }
  have hQevent : ∀ᶠ s in 𝓝 p, S.quotient s ≠ 0 :=
    hQ.continuousAt.preimage_mem_nhds
      (compl_singleton_mem_nhds_iff.mpr hQ0)
  filter_upwards [hQevent.filter_mono inf_le_left,
    self_mem_nhdsWithin] with s hQs hsp
  have hsp' : s ≠ p := by simpa using hsp
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    rw [S.factorization]
    exact mul_ne_zero (sub_ne_zero.mpr hsp') hQs
  unfold bettinConreyGZeroMeromorphicIntegrand
  have hBdecomp := hEq' s
  rw [hBp] at hBdecomp
  calc
    riemannZeta s * riemannZeta (1 - s) /
          Complex.sin ((Real.pi : ℂ) * s) * u ^ (-s) =
        B s / (s - p) := by
      rw [S.factorization]
      dsimp only [p]
      unfold B A routeCTaylorOddPoleNumerator
      field_simp [hsp', hQs]
    _ = (bettinConreyGZeroOddResidue u n + (s - p) * R s) /
          (s - p) := by rw [hBdecomp]
    _ = R s + bettinConreyGZeroOddResidue u n * (s - p)⁻¹ := by
      rw [add_div, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hsp')]
      simp only [div_eq_mul_inv, add_comm]

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorLocalSubtraction
