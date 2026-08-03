import Mathlib.Analysis.Analytic.Order
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReflectionWeight
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannGaussianSubtraction

/-!
# Route C: the genuine Abel two-pole rectangle

The Gaussian contour package has an entire pole-removed numerator.  The
reflected Abel weight does not: `Gamma (1-s)` has further poles at
`s = 2, 3, ...`.  They are outside the only strip needed here.  This module
therefore performs the subtraction on the open half-plane `re s < 2` and
uses the localized rectangle theorem.

No decay assumption, RH hypothesis, or external analytic axiom occurs in
this construction.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelTwoPole

open Complex Filter Set Topology MeasureTheory
open scoped Interval Real Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannTwoPoleRectangle
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannGaussianSubtraction
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelReflectionWeight

/-- The maximal half-plane containing the contour rectangle but no further
pole of `Gamma (1-s)`. -/
def abelTwoPoleHalfPlane : Set ℂ := {s : ℂ | s.re < 2}

theorem isOpen_abelTwoPoleHalfPlane : IsOpen abelTwoPoleHalfPlane := by
  exact isOpen_lt continuous_re continuous_const

/-- The numerator after simultaneously removing the reflected Estermann
double pole at zero and the Gamma pole at one.  The Gamma recurrence gives
`(1-s) Gamma (1-s) = Gamma (2-s)`, so this numerator is holomorphic on
`re s < 2`. -/
noncomputable def bettinConreyAbelPoleNumerator
    (x : ℝ) (a q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  Complex.Gamma (2 - s) * (x : ℂ) ^ (s - 1) *
    estermannPoleRemovedNumerator a q (1 - s)

theorem differentiableOn_bettinConreyAbelPoleNumerator
    (x : ℝ) (hx : 0 < x) (a q : ℕ) [NeZero q] :
    DifferentiableOn ℂ (bettinConreyAbelPoleNumerator x a q)
      abelTwoPoleHalfPlane := by
  intro s hs
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hgammaAt : DifferentiableAt ℂ Complex.Gamma (2 - s) := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have hre := congrArg Complex.re hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    change s.re < 2 at hs
    norm_num at hre
    linarith
  have hgamma : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (2 - z)) s := by
    have hinner : DifferentiableAt ℂ (fun z : ℂ => 2 - z) s := by fun_prop
    simpa using (hgammaAt.comp (f := fun z : ℂ => 2 - z) s hinner)
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ (z - 1)) s :=
    (differentiableAt_id.sub_const 1).const_cpow (Or.inl hx0)
  have hP : DifferentiableAt ℂ
      (fun z : ℂ => estermannPoleRemovedNumerator a q (1 - z)) s := by
    exact (differentiable_estermannPoleRemovedNumerator a q (1 - s)).comp s (by
      fun_prop)
  exact ((hgamma.mul hpow).mul hP).differentiableWithinAt

/-- Exact quotient formula for the normalized reflected integrand. -/
theorem normalizedWeightedIntegrand_eq_abelPoleNumerator_div
    (x : ℝ) (hx : 0 < x) (a q : ℕ) [NeZero q] {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    estermannWeightedIntegrand a q
        (bettinConreyNormalizedAbelReflectionWeight x) s =
      bettinConreyAbelPoleNumerator x a q s / (s ^ 2 * (s - 1)) := by
  have hsub : 1 - s ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  have hgamma := Complex.Gamma_add_one (1 - s) (sub_ne_zero.mpr hs1.symm)
  have hgamma' : Complex.Gamma (2 - s) =
      (1 - s) * Complex.Gamma (1 - s) := by
    convert hgamma using 1 <;> ring
  unfold estermannWeightedIntegrand
    bettinConreyNormalizedAbelReflectionWeight
    bettinConreyRawAbelReflectionWeight bettinConreyAbelPoleNumerator
  rw [estermannPoleRemovedNumerator_eq a q hsub, hgamma']
  apply (eq_div_iff
    (mul_ne_zero (pow_ne_zero 2 hs0) (sub_ne_zero.mpr hs1))).2
  ring

/-- A second-order Taylor quotient which remains differentiable throughout
an open domain, assuming only domain-local differentiability of the input. -/
theorem exists_differentiableOn_secondOrderQuotient
    (U : Set ℂ) (hU : IsOpen U) (N : ℂ → ℂ)
    (hN : DifferentiableOn ℂ N U) (h0 : (0 : ℂ) ∈ U) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧ ∀ z : ℂ,
      N z = N 0 + z * deriv N 0 + z ^ 2 * F z := by
  have hAnalyticOn : AnalyticOnNhd ℂ N U :=
    (Complex.analyticOnNhd_iff_differentiableOn hU).2 hN
  have hAnalytic : AnalyticAt ℂ N 0 := hAnalyticOn 0 h0
  rcases hAnalytic.exists_eq_sum_add_pow_mul 2 with ⟨F, hFa, hEq⟩
  have hEq' : ∀ z : ℂ,
      N z = N 0 + z * deriv N 0 + z ^ 2 * F z := by
    intro z
    simpa [Finset.sum_range_succ, iteratedDeriv_zero,
      iteratedDeriv_one, add_assoc] using hEq z
  have hFdiff : DifferentiableOn ℂ F U := by
    intro z hzU
    by_cases hz : z = 0
    · subst z
      exact hFa.differentiableAt.differentiableWithinAt
    · let Q : ℂ → ℂ := fun w =>
        (N w - N 0 - w * deriv N 0) / w ^ 2
      have hNz : DifferentiableAt ℂ N z :=
        hN.differentiableAt (hU.mem_nhds hzU)
      have hQ : DifferentiableAt ℂ Q z := by
        unfold Q
        exact ((hNz.sub (differentiableAt_const (c := N 0))).sub
          (differentiableAt_id.mul_const (deriv N 0))).div
            (differentiableAt_id.pow 2) (pow_ne_zero 2 hz)
      have hFQ : F =ᶠ[𝓝 z] Q := by
        filter_upwards [eventually_ne_nhds hz] with w hw
        have heq := hEq' w
        unfold Q
        rw [eq_div_iff (pow_ne_zero 2 hw), heq]
        ring
      exact (hQ.congr_of_eventuallyEq hFQ).differentiableWithinAt
  exact ⟨F, hFdiff, hEq'⟩

/-- First-order Taylor division at one, again preserving differentiability
on the chosen open domain. -/
theorem exists_differentiableOn_firstOrderQuotientAtOne
    (U : Set ℂ) (hU : IsOpen U) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F U) (h1 : (1 : ℂ) ∈ U) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ ∀ z : ℂ,
      F z = F 1 + (z - 1) * G z := by
  have hAnalyticOn : AnalyticOnNhd ℂ F U :=
    (Complex.analyticOnNhd_iff_differentiableOn hU).2 hF
  have hFone : AnalyticAt ℂ F 1 := hAnalyticOn 1 h1
  let M : ℂ → ℂ := fun u => F (1 + u)
  have hM : AnalyticAt ℂ M 0 := by
    unfold M
    have hadd : AnalyticAt ℂ (fun u : ℂ => 1 + u) 0 := by fun_prop
    have hFone' : AnalyticAt ℂ F (1 + (0 : ℂ)) := by
      simpa using hFone
    simpa using (hFone'.comp (f := fun u : ℂ => 1 + u) hadd)
  rcases hM.exists_eq_sum_add_pow_mul 1 with ⟨R, hRa, hEq⟩
  have hEq' : ∀ u : ℂ, M u = M 0 + u * R u := by
    intro u
    simpa [Finset.sum_range_succ, iteratedDeriv_zero] using hEq u
  let G : ℂ → ℂ := fun z => R (z - 1)
  have hGdiff : DifferentiableOn ℂ G U := by
    intro z hzU
    by_cases hz : z = 1
    · subst z
      have hinner : DifferentiableAt ℂ (fun z : ℂ => z - 1) 1 := by fun_prop
      have hRzero : DifferentiableAt ℂ R (1 - (1 : ℂ)) := by
        simpa using hRa.differentiableAt
      exact (hRzero.comp (f := fun z : ℂ => z - 1) 1 hinner).differentiableWithinAt
    · let Q : ℂ → ℂ := fun w => (F w - F 1) / (w - 1)
      have hFz : DifferentiableAt ℂ F z :=
        hF.differentiableAt (hU.mem_nhds hzU)
      have hQ : DifferentiableAt ℂ Q z := by
        unfold Q
        exact (hFz.sub (differentiableAt_const (c := F 1))).div
          (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hz)
      have hGQ : G =ᶠ[𝓝 z] Q := by
        filter_upwards [eventually_ne_nhds hz] with w hw
        have heq := hEq' (w - 1)
        have heq' : F w = F 1 + (w - 1) * R (w - 1) := by
          simpa [M] using heq
        unfold G Q
        rw [eq_div_iff (sub_ne_zero.mpr hw)]
        have heq'' : F w = (w - 1) * R (w - 1) + F 1 := by
          simpa [add_comm] using heq'
        have hdiff : F w - F 1 = (w - 1) * R (w - 1) :=
          sub_eq_iff_eq_add.mpr heq''
        calc
          R (w - 1) * (w - 1) = (w - 1) * R (w - 1) := mul_comm _ _
          _ = F w - F 1 := hdiff.symm
      exact (hQ.congr_of_eventuallyEq hGQ).differentiableWithinAt
  refine ⟨G, hGdiff, ?_⟩
  intro z
  have heq := hEq' (z - 1)
  simpa [M, G] using heq

/-- The genuine pole-subtraction data for the reflected Abel integrand.  Its
regularized remainder is only asserted holomorphic on `re s < 2`, exactly as
required by the finite rectangle. -/
theorem exists_bettinConreyAbelTwoPoleSubtraction
    (x : ℝ) (hx : 0 < x) (a q : ℕ) [NeZero q] :
    ∃ H : TwoPoleRectangleSubtractionData
        (estermannWeightedIntegrand a q
          (bettinConreyNormalizedAbelReflectionWeight x)),
      DifferentiableOn ℂ H.regularized abelTwoPoleHalfPlane ∧
      H.doubleCoefficient =
        estermannWeightedDoublePoleCoefficient a q
          (bettinConreyNormalizedAbelReflectionWeight x) ∧
      H.residueAtZero =
        estermannWeightedResidueCoefficient a q
          (bettinConreyNormalizedAbelReflectionWeight x) ∧
      H.residueAtOne = estermannHurwitzContinuation a q 0 := by
  let N : ℂ → ℂ := bettinConreyAbelPoleNumerator x a q
  have hN : DifferentiableOn ℂ N abelTwoPoleHalfPlane :=
    differentiableOn_bettinConreyAbelPoleNumerator x hx a q
  have h0 : (0 : ℂ) ∈ abelTwoPoleHalfPlane := by
    norm_num [abelTwoPoleHalfPlane]
  have h1 : (1 : ℂ) ∈ abelTwoPoleHalfPlane := by
    norm_num [abelTwoPoleHalfPlane]
  rcases exists_differentiableOn_secondOrderQuotient
      abelTwoPoleHalfPlane isOpen_abelTwoPoleHalfPlane N hN h0 with
    ⟨F, hF, hNexp⟩
  rcases exists_differentiableOn_firstOrderQuotientAtOne
      abelTwoPoleHalfPlane isOpen_abelTwoPoleHalfPlane F hF h1 with
    ⟨G, hG, hFexp⟩
  have hFone : F 1 = N 1 - N 0 - deriv N 0 := by
    have h := hNexp 1
    norm_num at h
    linear_combination -h
  let H : TwoPoleRectangleSubtractionData
      (estermannWeightedIntegrand a q
        (bettinConreyNormalizedAbelReflectionWeight x)) := {
    regularized := G
    doubleCoefficient := -N 0
    residueAtZero := -(N 0 + deriv N 0)
    residueAtOne := N 1
    decomposition s hs0 hs1 := by
      rw [normalizedWeightedIntegrand_eq_abelPoleNumerator_div
        x hx a q hs0 hs1]
      change N s / (s ^ 2 * (s - 1)) = _
      rw [hNexp s, hFexp s, hFone]
      field_simp [hs0, hs1, sub_ne_zero.mpr hs1]
      ring
  }
  have hdouble : H.doubleCoefficient =
      estermannWeightedDoublePoleCoefficient a q
        (bettinConreyNormalizedAbelReflectionWeight x) := by
    change -N 0 = _
    unfold N bettinConreyAbelPoleNumerator
    have hGamma2 : Complex.Gamma (2 : ℂ) = 1 := by
      simpa using Complex.Gamma_nat_eq_factorial 1
    simp only [sub_zero]
    rw [hGamma2, one_mul, estermannPoleRemovedNumerator_one]
    simp [Complex.Gamma_one, Complex.cpow_neg_one,
      estermannWeightedDoublePoleCoefficient,
      normalizedAbelReflectionWeight_zero]
  have hres0 : H.residueAtZero =
      estermannWeightedResidueCoefficient a q
        (bettinConreyNormalizedAbelReflectionWeight x) := by
    let R : ℂ → ℂ := fun s =>
      s * H.regularized s + H.residueAtZero +
        s * H.residueAtOne / (s - 1)
    have hGreg : DifferentiableAt ℂ H.regularized 0 :=
      hG.differentiableAt (isOpen_abelTwoPoleHalfPlane.mem_nhds h0)
    have hR : ContinuousAt R 0 := by
      unfold R
      exact ((continuousAt_id.mul hGreg.continuousAt).add
        continuousAt_const).add
          ((continuousAt_id.mul continuousAt_const).div
            (continuousAt_id.sub continuousAt_const) (by norm_num))
    have hRt : Tendsto R (𝓝[≠] (0 : ℂ)) (𝓝 H.residueAtZero) := by
      convert hR.tendsto.mono_left inf_le_left using 1 <;> simp [R]
    have hleft : Tendsto
        (fun s : ℂ => s *
          (estermannWeightedIntegrand a q
              (bettinConreyNormalizedAbelReflectionWeight x) s -
            H.doubleCoefficient / s ^ 2))
        (𝓝[≠] (0 : ℂ)) (𝓝 H.residueAtZero) := by
      apply hRt.congr'
      filter_upwards [self_mem_nhdsWithin,
        (eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)).filter_mono inf_le_left]
          with s hs0 hs1
      have hs0' : s ≠ 0 := by simpa using hs0
      rw [H.decomposition s hs0' hs1]
      unfold R
      field_simp [hs0', hs1]
      ring
    rw [hdouble] at hleft
    have hright := estermannWeightedIntegrand_residue_limit a q
      (bettinConreyNormalizedAbelReflectionWeight x)
      (differentiableAt_normalizedAbelReflectionWeight_zero x hx)
    exact tendsto_nhds_unique hleft hright
  have hres1 : H.residueAtOne = estermannHurwitzContinuation a q 0 := by
    change N 1 = _
    unfold N bettinConreyAbelPoleNumerator
    norm_num [Complex.Gamma_one]
    have hzero : (0 : ℂ) ≠ 1 := by norm_num
    rw [estermannPoleRemovedNumerator_eq a q hzero]
    norm_num
  exact ⟨H, hG, hdouble, hres0, hres1⟩

/-- Exact finite two-pole rectangle identity on the canonical strip
`-1/2 ≤ re s ≤ 3/2`. -/
theorem bettinConreyAbel_twoPoleRectangle
    (x : ℝ) (hx : 0 < x) (a q : ℕ) [NeZero q] (T : ℝ) (hT : 0 < T) :
    rectangularBoundaryIntegral
        (estermannWeightedIntegrand a q
          (bettinConreyNormalizedAbelReflectionWeight x))
        (symmetricLowerCorner (-1 / 2 : ℝ) T)
        (symmetricUpperCorner (3 / 2 : ℝ) T) =
      2 * Real.pi * I *
        (estermannWeightedResidueCoefficient a q
            (bettinConreyNormalizedAbelReflectionWeight x) +
          estermannHurwitzContinuation a q 0) := by
  rcases exists_bettinConreyAbelTwoPoleSubtraction x hx a q with
    ⟨H, hreg, hdouble, hres0, hres1⟩
  have hrect : DifferentiableOn ℂ H.regularized
      ([[-1 / 2, 3 / 2]] ×ℂ [[-T, T]]) := by
    apply hreg.mono
    intro s hs
    change s.re < 2
    have hsre := hs.1.2
    norm_num at hsre ⊢
    linarith
  rw [H.boundary_eq_of_differentiableOn
    (-1 / 2 : ℝ) (3 / 2 : ℝ) T (by norm_num) (by norm_num) hT hrect,
    hres0, hres1]

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelTwoPole
