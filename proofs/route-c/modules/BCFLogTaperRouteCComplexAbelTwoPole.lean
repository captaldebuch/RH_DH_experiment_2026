import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelLeftLine

/-!
# Route C: the complex Abel two-pole rectangle

The positive-real Abel rectangle extends to every nonzero complex damping
parameter.  The principal-power factor is entire in the contour variable,
so the same local pole subtraction applies on `Re(s)<2`.  This module proves
that statement and records the exact finite boundary identity.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelTwoPole

open Complex Filter Set Topology MeasureTheory
open scoped Interval Real Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannGaussianSubtraction
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannHurwitz
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannTwoPoleRectangle
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelComplexDamping
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelTwoPole

/-- Pole-removed numerator for complex Abel damping. -/
noncomputable def bettinConreyComplexAbelPoleNumerator
    (u : ℂ) (a q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  Complex.Gamma (2 - s) * u ^ (s - 1) *
    estermannPoleRemovedNumerator a q (1 - s)

theorem differentiableOn_bettinConreyComplexAbelPoleNumerator
    {u : ℂ} (hu : u ≠ 0) (a q : ℕ) [NeZero q] :
    DifferentiableOn ℂ (bettinConreyComplexAbelPoleNumerator u a q)
      abelTwoPoleHalfPlane := by
  intro s hs
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
  have hpow : DifferentiableAt ℂ (fun z : ℂ => u ^ (z - 1)) s :=
    (differentiableAt_id.sub_const 1).const_cpow (Or.inl hu)
  have hP : DifferentiableAt ℂ
      (fun z : ℂ => estermannPoleRemovedNumerator a q (1 - z)) s := by
    exact (differentiable_estermannPoleRemovedNumerator a q (1 - s)).comp s
      (by fun_prop)
  exact ((hgamma.mul hpow).mul hP).differentiableWithinAt

/-- Exact quotient representation away from the two poles. -/
theorem complexWeightedIntegrand_eq_abelPoleNumerator_div
    (u : ℂ) (a q : ℕ) [NeZero q] {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    estermannWeightedIntegrand a q
        (bettinConreyComplexAbelReflectionWeight u) s =
      bettinConreyComplexAbelPoleNumerator u a q s /
        (s ^ 2 * (s - 1)) := by
  have hsub : 1 - s ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  have hgamma := Complex.Gamma_add_one (1 - s)
    (sub_ne_zero.mpr hs1.symm)
  have hgamma' : Complex.Gamma (2 - s) =
      (1 - s) * Complex.Gamma (1 - s) := by
    convert hgamma using 1 <;> ring
  unfold estermannWeightedIntegrand
    bettinConreyComplexAbelReflectionWeight
    bettinConreyComplexAbelPoleNumerator
  rw [estermannPoleRemovedNumerator_eq a q hsub, hgamma']
  apply (eq_div_iff
    (mul_ne_zero (pow_ne_zero 2 hs0) (sub_ne_zero.mpr hs1))).2
  ring

/-- The complete two-pole subtraction data for a nonzero complex damping
parameter. -/
theorem exists_bettinConreyComplexAbelTwoPoleSubtraction
    {u : ℂ} (hu : u ≠ 0) (a q : ℕ) [NeZero q] :
    ∃ H : TwoPoleRectangleSubtractionData
        (estermannWeightedIntegrand a q
          (bettinConreyComplexAbelReflectionWeight u)),
      DifferentiableOn ℂ H.regularized abelTwoPoleHalfPlane ∧
      H.doubleCoefficient =
        estermannWeightedDoublePoleCoefficient a q
          (bettinConreyComplexAbelReflectionWeight u) ∧
      H.residueAtZero =
        estermannWeightedResidueCoefficient a q
          (bettinConreyComplexAbelReflectionWeight u) ∧
      H.residueAtOne = estermannHurwitzContinuation a q 0 := by
  let N : ℂ → ℂ := bettinConreyComplexAbelPoleNumerator u a q
  have hN : DifferentiableOn ℂ N abelTwoPoleHalfPlane :=
    differentiableOn_bettinConreyComplexAbelPoleNumerator hu a q
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
        (bettinConreyComplexAbelReflectionWeight u)) := {
    regularized := G
    doubleCoefficient := -N 0
    residueAtZero := -(N 0 + deriv N 0)
    residueAtOne := N 1
    decomposition s hs0 hs1 := by
      rw [complexWeightedIntegrand_eq_abelPoleNumerator_div
        u a q hs0 hs1]
      change N s / (s ^ 2 * (s - 1)) = _
      rw [hNexp s, hFexp s, hFone]
      field_simp [hs0, hs1, sub_ne_zero.mpr hs1]
      ring
  }
  have hdouble : H.doubleCoefficient =
      estermannWeightedDoublePoleCoefficient a q
        (bettinConreyComplexAbelReflectionWeight u) := by
    change -N 0 = _
    unfold N bettinConreyComplexAbelPoleNumerator
    have hGamma2 : Complex.Gamma (2 : ℂ) = 1 := by
      simpa using Complex.Gamma_nat_eq_factorial 1
    simp only [sub_zero, zero_sub]
    rw [hGamma2, one_mul, Complex.cpow_neg_one,
      estermannPoleRemovedNumerator_one]
    simp [estermannWeightedDoublePoleCoefficient,
      complexAbelReflectionWeight_zero]
  have hres0 : H.residueAtZero =
      estermannWeightedResidueCoefficient a q
        (bettinConreyComplexAbelReflectionWeight u) := by
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
              (bettinConreyComplexAbelReflectionWeight u) s -
            H.doubleCoefficient / s ^ 2))
        (𝓝[≠] (0 : ℂ)) (𝓝 H.residueAtZero) := by
      apply hRt.congr'
      filter_upwards [self_mem_nhdsWithin,
        (eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)).filter_mono
          inf_le_left] with s hs0 hs1
      have hs0' : s ≠ 0 := by simpa using hs0
      rw [H.decomposition s hs0' hs1]
      unfold R
      field_simp [hs0', hs1]
      ring
    rw [hdouble] at hleft
    have hright := estermannWeightedIntegrand_residue_limit a q
      (bettinConreyComplexAbelReflectionWeight u)
      (differentiableAt_complexAbelReflectionWeight_zero hu)
    exact tendsto_nhds_unique hleft hright
  have hres1 : H.residueAtOne = estermannHurwitzContinuation a q 0 := by
    change N 1 = _
    unfold N bettinConreyComplexAbelPoleNumerator
    norm_num [Complex.Gamma_one]
    have hzero : (0 : ℂ) ≠ 1 := by norm_num
    rw [estermannPoleRemovedNumerator_eq a q hzero]
    norm_num
  exact ⟨H, hG, hdouble, hres0, hres1⟩

/-- Exact finite complex Abel rectangle across the two Estermann poles. -/
theorem bettinConreyComplexAbel_twoPoleRectangle
    {u : ℂ} (hu : u ≠ 0) (a q : ℕ) [NeZero q]
    (T : ℝ) (hT : 0 < T) :
    rectangularBoundaryIntegral
        (estermannWeightedIntegrand a q
          (bettinConreyComplexAbelReflectionWeight u))
        (symmetricLowerCorner (-1 / 2 : ℝ) T)
        (symmetricUpperCorner (3 / 2 : ℝ) T) =
      2 * Real.pi * I *
        (estermannWeightedResidueCoefficient a q
            (bettinConreyComplexAbelReflectionWeight u) +
          estermannHurwitzContinuation a q 0) := by
  rcases exists_bettinConreyComplexAbelTwoPoleSubtraction hu a q with
    ⟨H, hreg, _hdouble, hres0, hres1⟩
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

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexAbelTwoPole
