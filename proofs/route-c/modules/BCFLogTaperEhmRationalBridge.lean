import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary

/-!
# Rational-scale Ehm series bridge

The BCF/Ehm inversion error only samples `S₁` and `R₁` at positive rational
scales `d/m`.  This module weakens the all-real series interface accordingly
and proves that the rational interface already suffices for the hyperbolic
limit and the uniform-boundary closure of H15.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbola
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral

/-- The exact `R₁` series identity only at the positive rational scales used
by the finite BCF problem. -/
structure EhmR1RationalSeriesBridge (S1 R1 : ℝ → ℝ) where
  hasSum_ratio : ∀ d m : ℕ, 0 < d → 0 < m →
    HasSum
      (fun q : ℕ =>
        R1 (((q + 1 : ℕ) : ℝ) * ((d : ℝ) / (m : ℝ))))
      (S1 ((d : ℝ) / (m : ℝ)))

/-- The all-positive-real bridge restricts to the rational bridge. -/
def EhmR1SeriesBridge.toRational
    {S1 R1 : ℝ → ℝ} (H : EhmR1SeriesBridge S1 R1) :
    EhmR1RationalSeriesBridge S1 R1 where
  hasSum_ratio d m hd hm := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    exact H.hasSum_series ((d : ℝ) / (m : ℝ))
      (div_pos (by exact_mod_cast hd) hmR)

/-- Rational-only identification of the convergent series with `S1`. -/
structure EhmR1RationalSeriesValueIdentity (S1 R1 : ℝ → ℝ) where
  value : ∀ d m : ℕ, 0 < d → 0 < m →
    S1 ((d : ℝ) / (m : ℝ)) =
      ∑' q : ℕ,
        R1 (((q + 1 : ℕ) : ℝ) * ((d : ℝ) / (m : ℝ)))

/-- Quadratic decay plus the rational value identity gives precisely the
series bridge needed by H15. -/
noncomputable def EhmR1RationalSeriesBridge.of_decay_and_value
    {S1 R1 : ℝ → ℝ}
    (HD : EhmR1QuadraticDecay R1)
    (HV : EhmR1RationalSeriesValueIdentity S1 R1) :
    EhmR1RationalSeriesBridge S1 R1 where
  hasSum_ratio d m hd hm := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hx : 0 < (d : ℝ) / (m : ℝ) :=
      div_pos (by exact_mod_cast hd) hmR
    rw [HV.value d m hd hm]
    exact (HD.summable_series ((d : ℝ) / (m : ℝ)) hx).hasSum

/-- Concrete rational bridge for Ehm's autocorrelation and elementary
`R₁`. -/
abbrev EhmAutocorrelationR1RationalSeriesBridge :=
  EhmR1RationalSeriesBridge ehmS1Autocorrelation ehmR1

private theorem sum_Icc_one_eq_sum_range_shift
    (f : ℕ → ℝ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, f k) =
      ∑ q ∈ Finset.range K, f (q + 1) := by
  apply Finset.sum_bij (fun k _ => k - 1)
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    simp only [Finset.mem_range]
    omega
  · intro a ha b hb hab
    have ha1 := (Finset.mem_Icc.mp ha).1
    have hb1 := (Finset.mem_Icc.mp hb).1
    omega
  · intro q hq
    simp only [Finset.mem_range] at hq
    refine ⟨q + 1, Finset.mem_Icc.mpr ?_, ?_⟩
    · omega
    · simp
  · intro k hk
    have hk1 := (Finset.mem_Icc.mp hk).1
    rw [Nat.sub_add_cancel hk1]

/-- Convergence of ordinary partial sums at a positive rational scale. -/
theorem ehmR1PartialSeries_ratio_tendsto
    {S1 R1 : ℝ → ℝ} (H : EhmR1RationalSeriesBridge S1 R1)
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    Tendsto
      (fun K : ℕ =>
        ehmR1PartialSeries R1 K ((d : ℝ) / (m : ℝ)))
      atTop (𝓝 (S1 ((d : ℝ) / (m : ℝ)))) := by
  have hseries := (H.hasSum_ratio d m hd hm).tendsto_sum_nat
  apply Tendsto.congr _ hseries
  intro K
  exact (sum_Icc_one_eq_sum_range_shift
    (fun k : ℕ => R1 ((k : ℝ) * ((d : ℝ) / (m : ℝ)))) K).symm

/-- The rational bridge suffices for the inner hyperbolic limit at `x=1/m`.
No identity at irrational scales is needed. -/
theorem ehmFiniteS1HyperbolicSum_reciprocal_tendsto
    {S1 R1 : ℝ → ℝ} (H : EhmR1RationalSeriesBridge S1 R1)
    (N m : ℕ) (hm : 0 < m) :
    Tendsto
      (fun J : ℕ =>
        ehmFiniteS1HyperbolicSum R1 N J (1 / (m : ℝ)))
      atTop
      (𝓝 (∑ d ∈ Finset.Icc 1 N,
        dirichletCoeff N d * S1 ((d : ℝ) / (m : ℝ)))) := by
  classical
  unfold ehmFiniteS1HyperbolicSum
  apply tendsto_finsetSum
  intro d hdmem
  have hd : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdmem).1
  have hpartial := ehmR1PartialSeries_ratio_tendsto H d m hd hm
  have hdiv := Nat.tendsto_div_const_atTop (Nat.ne_of_gt hd)
  have hlimit := (hpartial.comp hdiv).const_mul (dirichletCoeff N d)
  apply Tendsto.congr _ hlimit
  intro J
  simpa [div_eq_mul_inv, mul_assoc] using
    (ehmFiniteHyperbolicRow_eq_partialSeries R1
      (dirichletCoeff N d) (1 / (m : ℝ)) d J hd).symm

/-- The rational series identity already carries the finite hyperbolic outer
sum to Ehm's complete inversion error. -/
theorem ehmFiniteHyperbolicInversionError_tendsto_of_rational
    {S1 R1 : ℝ → ℝ} (H : EhmR1RationalSeriesBridge S1 R1)
    (N : ℕ) :
    Tendsto (fun J : ℕ => ehmFiniteHyperbolicInversionError R1 N J)
      atTop (𝓝 (ehmInversionError S1 R1 N)) := by
  classical
  unfold ehmFiniteHyperbolicInversionError ehmInversionError
  apply tendsto_finsetSum
  intro m hmmem
  have hm : 0 < m :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hmmem).1
  have hinner := ehmFiniteS1HyperbolicSum_reciprocal_tendsto H N m hm
  have hlimit := (hinner.sub_const (R1 (1 / (m : ℝ)))).const_mul
    (dirichletCoeff N m / (m : ℝ))
  exact hlimit

/-- Fixed-`N` convergence of the coupled boundary expression using only the
rational series bridge. -/
theorem ehmFiniteCoupledBoundaryExpression_tendsto_of_rational
    {S1 R1 : ℝ → ℝ} (H : EhmR1RationalSeriesBridge S1 R1)
    (N : ℕ) (hN : 2 ≤ N) :
    Tendsto (fun J : ℕ => ehmFiniteCoupledBoundaryExpression R1 N J)
      atTop
      (𝓝 (ehmInversionError S1 R1 N + ehmCoupledRemainder N)) := by
  have hlimit :=
    (ehmFiniteHyperbolicInversionError_tendsto_of_rational H N).add_const
      (ehmCoupledRemainder N)
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop N] with J hNJ
  exact (ehmFiniteCoupledBoundaryExpression_eq_hyperbolic_add_remainder
    R1 N J hN hNJ).symm

/-- Uniform coupled boundary control plus only the rational bridge gives the
exact Ehm cancellation package. -/
noncomputable def ehmCoupledCancellation_of_uniformBoundary_rational
    (HK : EhmKernelPackage)
    (HS : EhmR1RationalSeriesBridge HK.S1 HK.R1)
    (HB : EhmUniformCoupledBoundaryControl HK.R1) :
    EhmCoupledCancellationEstimate HK where
  C := HB.C
  C_pos := HB.C_pos
  α := HB.α
  α_pos := HB.α_pos
  bound N hN := by
    have hlimit :=
      (ehmFiniteCoupledBoundaryExpression_tendsto_of_rational HS N hN).abs
    apply le_of_tendsto hlimit
    filter_upwards [eventually_ge_atTop (HB.cutoff N)] with J hJ
    exact HB.bound N hN J hJ

/-- Concrete rational-scale closure of the project-wide H15 estimate. -/
noncomputable def coupledLogTaperCancellation_of_ehmUniformBoundary_rational
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HB : EhmAutocorrelationUniformCoupledBoundaryControl) :
    CoupledLogTaperCancellationEstimate := by
  let HK : EhmKernelPackage :=
    ehmS1PointwiseKernelPackageProved.toEhmKernelPackage
  exact coupledLogTaperCancellation_of_ehm HK
    (ehmCoupledCancellation_of_uniformBoundary_rational HK HS HB)

/-- The rational bridge and the uniform boundary estimate therefore suffice
for spectral vanishing. -/
noncomputable def spectralVanishing_of_ehmUniformBoundary_rational
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (HB : EhmAutocorrelationUniformCoupledBoundaryControl) :
    SpectralVanishingEstimate :=
  spectralVanishingEstimate_of_coupledLogTaperCancellation
    (coupledLogTaperCancellation_of_ehmUniformBoundary_rational HS HB)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
