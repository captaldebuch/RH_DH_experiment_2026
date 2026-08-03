import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge

/-!
# Research reductions for the uniform Ehm boundary

This module records two unconditional reductions of the remaining H15
boundary problem.

First, the incomplete divisor coefficient is completed by the omitted
divisors `d > N`.  This rewrites the finite hyperbolic boundary as a full
von Mangoldt--`R₁` transform minus one signed complementary-divisor sum.
No absolute values are introduced in this identity.

Second, eventual control at every sufficiently large hyperbolic cutoff is
shown to be stronger than necessary.  It suffices to have bounded cutoffs
cofinally in `J` for each fixed `N`: convergence of the finite hyperbolic
expressions then passes the same bound to the limit.  This is a strictly
weaker analytic target, but remains an open RH-strength cancellation
estimate for the concrete Ehm kernel.  Consistently with Ehm, Section 8.1
(arXiv:2405.06349), estimation of this Möbius inversion error is treated as
a major challenge rather than as a consequence of the preceding identities.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch

open scoped BigOperators Topology ArithmeticFunction
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryTail
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbola
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral

/-- The portion of the full log-taper divisor sum omitted by the finite
Dirichlet polynomial cutoff `d ≤ N`. -/
noncomputable def ehmLogTaperMissingDivisorCoeff (N j : ℕ) : ℝ :=
  ∑ d ∈ j.divisors,
    if N < d then dirichletCoeff N d else 0

/-- The retained and omitted divisor coefficients partition the full
log-taper divisor convolution exactly. -/
theorem ehmLogTaperDivisorCoeff_add_missing (N j : ℕ) :
    ehmLogTaperDivisorCoeff N j +
        ehmLogTaperMissingDivisorCoeff N j =
      ∑ d ∈ j.divisors, dirichletCoeff N d := by
  classical
  unfold ehmLogTaperDivisorCoeff ehmLogTaperMissingDivisorCoeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d ≤ N
  · simp [hd, Nat.not_lt_of_ge hd]
  · have hNd : N < d := Nat.lt_of_not_ge hd
    simp [hd, hNd]

/-- The full (untruncated) log-taper divisor convolution is the von
Mangoldt coefficient for every `j ≥ 2`.  Unlike the retained-coefficient
formula, this statement has no hypothesis `j ≤ N`. -/
theorem ehmFullLogTaperDivisorCoeff_eq_vonMangoldt_div_log
    (N j : ℕ) (hN : 2 ≤ N) (hj : 2 ≤ j) :
    (∑ d ∈ j.divisors, dirichletCoeff N d) =
      ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) := by
  unfold dirichletCoeff
  simp_rw [weight_of_two_le hN]
  have hmu :
      (∑ d ∈ j.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = 0 := by
    calc
      (∑ d ∈ j.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) =
          (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
              ArithmeticFunction ℝ) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) j :=
        (ArithmeticFunction.coe_mul_zeta_apply
          (f := ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
            ArithmeticFunction ℝ))).symm
      _ = (1 : ArithmeticFunction ℝ) j := by
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
      _ = 0 := by simp [show j ≠ 1 by omega]
  have hmulog := ArithmeticFunction.sum_moebius_mul_log_eq (n := j)
  have hmulog' :
      (∑ d ∈ j.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          Real.log (d : ℝ)) = -ArithmeticFunction.vonMangoldt j := by
    simpa only [ArithmeticFunction.log_apply] using hmulog
  calc
    (∑ d ∈ j.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (1 - Real.log (d : ℝ) / Real.log (N : ℝ))) =
        (∑ d ∈ j.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) -
          (∑ d ∈ j.divisors,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              Real.log (d : ℝ)) / Real.log (N : ℝ) := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := by rw [hmu, hmulog']; ring

/-- Above the polynomial cutoff, the incomplete divisor coefficient is a
full von Mangoldt coefficient minus the signed omitted-divisor coefficient. -/
theorem ehmLogTaperDivisorCoeff_eq_vonMangoldt_sub_missing
    (N j : ℕ) (hN : 2 ≤ N) (hj : 2 ≤ j) :
    ehmLogTaperDivisorCoeff N j =
      ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) -
        ehmLogTaperMissingDivisorCoeff N j := by
  have hpartition := ehmLogTaperDivisorCoeff_add_missing N j
  rw [ehmFullLogTaperDivisorCoeff_eq_vonMangoldt_div_log N j hN hj]
    at hpartition
  linarith

/-- The full finite von Mangoldt transform through hyperbolic height `J`. -/
noncomputable def ehmFiniteFullVonMangoldtTransform
    (R1 : ℝ → ℝ) (N J : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 J,
    ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) *
      R1 ((j : ℝ) * x)

/-- The signed complementary-divisor part supported on `N < j ≤ J`. -/
noncomputable def ehmFiniteMissingDivisorTail
    (R1 : ℝ → ℝ) (N J : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (N + 1) J,
    ehmLogTaperMissingDivisorCoeff N j * R1 ((j : ℝ) * x)

/-- Exact completion of the finite boundary and incomplete tail.  The
right-hand side retains the sign between the full von Mangoldt transform
and the omitted-divisor correction. -/
theorem ehmBoundary_add_incompleteTail_eq_fullVonMangoldt_sub_missing
    (R1 : ℝ → ℝ) (N J : ℕ) (x : ℝ)
    (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteVonMangoldtBoundary R1 N x +
        ehmFiniteIncompleteDivisorTail R1 N J x =
      ehmFiniteFullVonMangoldtTransform R1 N J x -
        ehmFiniteMissingDivisorTail R1 N J x := by
  classical
  have hwhole :
      Finset.Icc 2 J =
        Finset.Icc 2 N ∪ Finset.Icc (N + 1) J := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdis :
      Disjoint (Finset.Icc 2 N) (Finset.Icc (N + 1) J) := by
    apply Finset.disjoint_left.mpr
    intro j hjN hjTail
    have hjN' := (Finset.mem_Icc.mp hjN).2
    have hjTail' := (Finset.mem_Icc.mp hjTail).1
    omega
  unfold ehmFiniteVonMangoldtBoundary
    ehmFiniteIncompleteDivisorTail
    ehmFiniteFullVonMangoldtTransform
    ehmFiniteMissingDivisorTail
  rw [hwhole, Finset.sum_union hdis]
  have htail :
      (∑ j ∈ Finset.Icc (N + 1) J,
          ehmLogTaperDivisorCoeff N j * R1 ((j : ℝ) * x)) =
        (∑ j ∈ Finset.Icc (N + 1) J,
          ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) *
            R1 ((j : ℝ) * x)) -
        ∑ j ∈ Finset.Icc (N + 1) J,
          ehmLogTaperMissingDivisorCoeff N j * R1 ((j : ℝ) * x) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlo : N + 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [ehmLogTaperDivisorCoeff_eq_vonMangoldt_sub_missing
      N j hN (by omega)]
    ring
  rw [htail]
  ring

/-- Outer BCF sum of the full finite von Mangoldt transform. -/
noncomputable def ehmFiniteFullVonMangoldtTransformOuter
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) *
    ehmFiniteFullVonMangoldtTransform R1 N J (1 / (m : ℝ))

/-- Outer BCF sum of the complementary-divisor tail. -/
noncomputable def ehmFiniteMissingDivisorTailOuter
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) *
    ehmFiniteMissingDivisorTail R1 N J (1 / (m : ℝ))

/-- Outer version of the full-von-Mangoldt-minus-complement identity. -/
theorem ehmBoundaryOuter_add_incompleteTailOuter_eq_fullOuter_sub_missingOuter
    (R1 : ℝ → ℝ) (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteVonMangoldtBoundaryOuter R1 N +
        ehmFiniteIncompleteDivisorTailOuter R1 N J =
      ehmFiniteFullVonMangoldtTransformOuter R1 N J -
        ehmFiniteMissingDivisorTailOuter R1 N J := by
  classical
  unfold ehmFiniteVonMangoldtBoundaryOuter
    ehmFiniteIncompleteDivisorTailOuter
    ehmFiniteFullVonMangoldtTransformOuter
    ehmFiniteMissingDivisorTailOuter
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have hinner :=
    ehmBoundary_add_incompleteTail_eq_fullVonMangoldt_sub_missing
      R1 N J (1 / (m : ℝ)) hN hNJ
  rw [show dirichletCoeff N m / (m : ℝ) *
          ehmFiniteVonMangoldtBoundary R1 N (1 / (m : ℝ)) +
        dirichletCoeff N m / (m : ℝ) *
          ehmFiniteIncompleteDivisorTail R1 N J (1 / (m : ℝ)) =
        dirichletCoeff N m / (m : ℝ) *
          (ehmFiniteVonMangoldtBoundary R1 N (1 / (m : ℝ)) +
            ehmFiniteIncompleteDivisorTail R1 N J (1 / (m : ℝ))) by ring,
      hinner]
  ring

/-- The finite coupled boundary target in completed-divisor variables. -/
theorem ehmFiniteCoupledBoundaryExpression_eq_fullOuter_sub_missing_add_remainder
    (R1 : ℝ → ℝ) (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteCoupledBoundaryExpression R1 N J =
      ehmFiniteFullVonMangoldtTransformOuter R1 N J -
        ehmFiniteMissingDivisorTailOuter R1 N J +
          ehmCoupledRemainder N := by
  unfold ehmFiniteCoupledBoundaryExpression
  rw [ehmBoundaryOuter_add_incompleteTailOuter_eq_fullOuter_sub_missingOuter
    R1 N J hN hNJ]

/-- A convergent real sequence which is bounded by `r` at arbitrarily late
indices has a limit bounded by `r`. -/
theorem abs_limit_le_of_tendsto_of_frequently_abs_le
    {f : ℕ → ℝ} {L r : ℝ}
    (hlim : Tendsto f atTop (𝓝 L))
    (hfreq : ∃ᶠ J : ℕ in atTop, |f J| ≤ r) :
    |L| ≤ r := by
  by_contra hnot
  have hrL : r < |L| := lt_of_not_ge hnot
  have hevent : ∀ᶠ J : ℕ in atTop, r < |f J| :=
    hlim.abs.eventually (Ioi_mem_nhds hrL)
  rcases (hfreq.and_eventually hevent).exists with ⟨J, hJle, hJlt⟩
  exact (not_lt_of_ge hJle) hJlt

/-- A weaker uniform-boundary target: for each `N`, bounded finite
expressions need only occur at arbitrarily late hyperbolic cutoffs.  It does
not require all sufficiently large cutoffs to be good. -/
structure EhmCofinalCoupledBoundaryControl (R1 : ℝ → ℝ) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  cofinal_bound : ∀ N : ℕ, 2 ≤ N → ∀ J₀ : ℕ,
    ∃ J : ℕ, max N J₀ ≤ J ∧
      |ehmFiniteCoupledBoundaryExpression R1 N J| ≤
        C / (Real.log (N : ℝ)) ^ α

/-- The same cofinal research target in completed-divisor variables.  The
full von Mangoldt transform, omitted-divisor correction, and moment
remainder deliberately remain under one absolute value. -/
structure EhmCompletedDivisorCofinalControl (R1 : ℝ → ℝ) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  cofinal_bound : ∀ N : ℕ, 2 ≤ N → ∀ J₀ : ℕ,
    ∃ J : ℕ, max N J₀ ≤ J ∧
      |ehmFiniteFullVonMangoldtTransformOuter R1 N J -
          ehmFiniteMissingDivisorTailOuter R1 N J +
            ehmCoupledRemainder N| ≤
        C / (Real.log (N : ℝ)) ^ α

/-- The completed-divisor formulation gives cofinal control of the
original finite boundary expression by the exact identity above. -/
def EhmCompletedDivisorCofinalControl.toCofinal
    {R1 : ℝ → ℝ} (H : EhmCompletedDivisorCofinalControl R1) :
    EhmCofinalCoupledBoundaryControl R1 where
  C := H.C
  C_pos := H.C_pos
  α := H.α
  α_pos := H.α_pos
  cofinal_bound N hN J₀ := by
    rcases H.cofinal_bound N hN J₀ with ⟨J, hJ, hbound⟩
    refine ⟨J, hJ, ?_⟩
    rw [ehmFiniteCoupledBoundaryExpression_eq_fullOuter_sub_missing_add_remainder
      R1 N J hN (le_trans (Nat.le_max_left N J₀) hJ)]
    exact hbound

/-- Eventual uniform boundary control implies the weaker cofinal control. -/
def EhmUniformCoupledBoundaryControl.toCofinal
    {R1 : ℝ → ℝ} (H : EhmUniformCoupledBoundaryControl R1) :
    EhmCofinalCoupledBoundaryControl R1 where
  C := H.C
  C_pos := H.C_pos
  α := H.α
  α_pos := H.α_pos
  cofinal_bound N hN J₀ := by
    refine ⟨max (H.cutoff N) J₀, ?_, ?_⟩
    · exact max_le_max (H.cutoff_ge N) le_rfl
    · exact H.bound N hN (max (H.cutoff N) J₀) (Nat.le_max_left _ _)

/-- Cofinal control is already sufficient: pointwise convergence in `J`
passes the bound to the exact Ehm coupled expression. -/
noncomputable def ehmCoupledCancellation_of_cofinalBoundary
    (H : EhmKernelPackage)
    (HS : EhmR1SeriesBridge H.S1 H.R1)
    (HB : EhmCofinalCoupledBoundaryControl H.R1) :
    EhmCoupledCancellationEstimate H where
  C := HB.C
  C_pos := HB.C_pos
  α := HB.α
  α_pos := HB.α_pos
  bound N hN := by
    apply abs_limit_le_of_tendsto_of_frequently_abs_le
      (ehmFiniteCoupledBoundaryExpression_tendsto HS N hN)
    rw [frequently_atTop]
    intro J₀
    rcases HB.cofinal_bound N hN J₀ with ⟨J, hJ, hbound⟩
    exact ⟨J, (Nat.le_max_right N J₀).trans hJ, hbound⟩

/-- Concrete cofinal target for the proved Ehm autocorrelation kernel. -/
abbrev EhmAutocorrelationCofinalCoupledBoundaryControl :=
  EhmCofinalCoupledBoundaryControl ehmR1

/-- The cofinal boundary criterion and the autocorrelation series bridge
give the project-wide H15 estimate. -/
noncomputable def coupledLogTaperCancellation_of_ehmCofinalBoundary
    (HS : EhmAutocorrelationR1SeriesBridge)
    (HB : EhmAutocorrelationCofinalCoupledBoundaryControl) :
    CoupledLogTaperCancellationEstimate := by
  let HK : EhmKernelPackage :=
    ehmS1PointwiseKernelPackageProved.toEhmKernelPackage
  exact coupledLogTaperCancellation_of_ehm HK
    (ehmCoupledCancellation_of_cofinalBoundary HK HS HB)

/-- Consequently the same weaker target is sufficient for spectral
vanishing.  This theorem is a reduction, not a construction of `HB`. -/
noncomputable def spectralVanishing_of_ehmCofinalBoundary
    (HS : EhmAutocorrelationR1SeriesBridge)
    (HB : EhmAutocorrelationCofinalCoupledBoundaryControl) :
    SpectralVanishingEstimate :=
  spectralVanishingEstimate_of_coupledLogTaperCancellation
    (coupledLogTaperCancellation_of_ehmCofinalBoundary HS HB)

/-- The weaker positive-rational series bridge is already enough to pass
cofinal boundary control to the exact Ehm cancellation estimate. -/
noncomputable def ehmCoupledCancellation_of_cofinalBoundary_rational
    (H : EhmKernelPackage)
    (HS : EhmR1RationalSeriesBridge H.S1 H.R1)
    (HB : EhmCofinalCoupledBoundaryControl H.R1) :
    EhmCoupledCancellationEstimate H where
  C := HB.C
  C_pos := HB.C_pos
  α := HB.α
  α_pos := HB.α_pos
  bound N hN := by
    apply abs_limit_le_of_tendsto_of_frequently_abs_le
      (ehmFiniteCoupledBoundaryExpression_tendsto_of_rational HS N hN)
    rw [frequently_atTop]
    intro J₀
    rcases HB.cofinal_bound N hN J₀ with ⟨J, hJ, hbound⟩
    exact ⟨J, (Nat.le_max_right N J₀).trans hJ, hbound⟩

/-- Concrete rational-scale and cofinal-boundary closure of H15. -/
noncomputable def coupledLogTaperCancellation_of_ehmCofinalBoundary_rational
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HB : EhmAutocorrelationCofinalCoupledBoundaryControl) :
    CoupledLogTaperCancellationEstimate := by
  let HK : EhmKernelPackage :=
    ehmS1PointwiseKernelPackageProved.toEhmKernelPackage
  exact coupledLogTaperCancellation_of_ehm HK
    (ehmCoupledCancellation_of_cofinalBoundary_rational HK HS HB)

/-- The smallest formal target currently exposed by the Ehm hyperbolic
route: rational series identification plus cofinally bounded completed
divisor sums imply spectral vanishing. -/
noncomputable def spectralVanishing_of_ehmCofinalBoundary_rational
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HB : EhmAutocorrelationCofinalCoupledBoundaryControl) :
    SpectralVanishingEstimate :=
  spectralVanishingEstimate_of_coupledLogTaperCancellation
    (coupledLogTaperCancellation_of_ehmCofinalBoundary_rational HS HB)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryResearch
