import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmHyperbolicKernelNormalForm

/-!
# Fourier and endpoint-resonance audit for the Ehm reciprocal kernel

This file performs the algebraic part of WP3.  It lifts the exact
smooth--Bernoulli--endpoint decomposition of `ehmR1` through the collapsed
finite `q`-kernel, identifies the integer endpoint with the divisibility
condition `m ∣ d*q`, and reconstructs the complete coupled Type-I/II target
at the explicit conductor `D(X)=(X+1)^8`.

No Fourier estimate or cancellation theorem is asserted.  In particular,
the smooth, Bernoulli, endpoint, main, and linear terms are kept coupled.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAlternativeRoutes
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoupledNearCoreTarget
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbolicKernelNormalForm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit
open RH.Criteria.NymanBeurling.QuadraticInteraction
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## Linearity and exact decomposition of one reciprocal row -/

theorem ehmDyadicReciprocalQKernel_add
    (R S : ℝ → ℝ) (J m d : ℕ) :
    ehmDyadicReciprocalQKernel (R + S) J m d =
      ehmDyadicReciprocalQKernel R J m d +
        ehmDyadicReciprocalQKernel S J m d := by
  unfold ehmDyadicReciprocalQKernel ehmR1PartialSeries
  simp_rw [Pi.add_apply, Finset.sum_add_distrib]

theorem ehmDyadicReciprocalQKernel_neg
    (R : ℝ → ℝ) (J m d : ℕ) :
    ehmDyadicReciprocalQKernel (-R) J m d =
      -ehmDyadicReciprocalQKernel R J m d := by
  unfold ehmDyadicReciprocalQKernel ehmR1PartialSeries
  simp_rw [Pi.neg_apply, Finset.sum_neg_distrib]

/-- The exact pointwise Ehm decomposition lifted through the entire finite
hyperbolic row. -/
theorem ehmDyadicReciprocalQKernel_eq_routePieces
    (J m d : ℕ) :
    ehmDyadicReciprocalQKernel ehmR1 J m d =
      ehmDyadicReciprocalQKernel ehmR1SmoothPart J m d -
        ehmDyadicReciprocalQKernel ehmR1BernoulliSawtoothPart J m d +
        ehmDyadicReciprocalQKernel ehmR1IntegerEndpointPart J m d := by
  have hfun : ehmR1 =
      ehmR1SmoothPart + (-ehmR1BernoulliSawtoothPart) +
        ehmR1IntegerEndpointPart := by
    funext x
    simpa [Pi.neg_apply] using ehmR1_eq_smooth_sub_bernoulli_add_endpoint x
  rw [hfun, ehmDyadicReciprocalQKernel_add,
    ehmDyadicReciprocalQKernel_add, ehmDyadicReciprocalQKernel_neg]
  ring

/-! ## Exact finite Vaaler phase rows -/

/-- The actual Fourier phase produced by the Ehm kernel.  It is reciprocal
in the Möbius variable `m`, with numerator `h*q*d`. -/
noncomputable def ehmVaalerRationalPhase
    (h : ℤ) (q d m : ℕ) : ℂ :=
  vaalerFourierPhase h ((q : ℝ) * ((d : ℝ) / (m : ℝ)))

/-- The weighted phase row which occurs because the Bernoulli term in `R₁`
is divided by its argument. -/
noncomputable def ehmVaalerWeightedPhaseRow
    (h : ℤ) (J m d : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (J / d),
    ehmVaalerRationalPhase h q d m /
      (((q : ℝ) * ((d : ℝ) / (m : ℝ)) : ℝ) : ℂ)

/-- The complete finite Fourier approximant after interchanging the finite
`q` and Vaaler-frequency sums. -/
noncomputable def ehmVaalerBernoulliKernelApprox
    (V : VaalerSawtoothPackage) (H J m d : ℕ) : ℂ :=
  ∑ h ∈ V.frequencies H,
    V.coefficient H h * ehmVaalerWeightedPhaseRow h J m d

/-- The error row accompanying the finite Vaaler approximant. -/
noncomputable def ehmVaalerBernoulliKernelError
    (V : VaalerSawtoothPackage) (H J m d : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (J / d),
    vaalerSawtoothError V H ((q : ℝ) * ((d : ℝ) / (m : ℝ))) /
      (((q : ℝ) * ((d : ℝ) / (m : ℝ)) : ℝ) : ℂ)

/-- The phase really is `exp(2*pi*i*h*q*d/m)`; in particular it is not a
Kloosterman inverse in `d` or `q`. -/
theorem ehmVaalerRationalPhase_eq_exp
    (h : ℤ) (q d m : ℕ) :
    ehmVaalerRationalPhase h q d m =
      Complex.exp
        (((2 * Real.pi * (h : ℝ) *
          (((q * d : ℕ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  unfold ehmVaalerRationalPhase vaalerFourierPhase
  congr 2
  push_cast
  ring

/-- The zero Fourier frequency is exactly the nonoscillatory reciprocal
weight row. -/
theorem ehmVaalerWeightedPhaseRow_zero (J m d : ℕ) :
    ehmVaalerWeightedPhaseRow 0 J m d =
      ∑ q ∈ Finset.Icc 1 (J / d),
        1 / (((q : ℝ) * ((d : ℝ) / (m : ℝ)) : ℝ) : ℂ) := by
  unfold ehmVaalerWeightedPhaseRow ehmVaalerRationalPhase
    vaalerFourierPhase
  apply Finset.sum_congr rfl
  intro q _
  simp

/-- Exact Vaaler expansion of one Bernoulli reciprocal row.  The equality
retains both the weighted Fourier modes and the complete error row. -/
theorem ehmDyadicBernoulliQKernel_eq_vaaler
    (V : VaalerSawtoothPackage) (H J m d : ℕ) :
    ((ehmDyadicReciprocalQKernel ehmR1BernoulliSawtoothPart
      J m d : ℝ) : ℂ) =
      ehmVaalerBernoulliKernelApprox V H J m d +
        ehmVaalerBernoulliKernelError V H J m d := by
  let x : ℕ → ℝ := fun q ↦ (q : ℝ) * ((d : ℝ) / (m : ℝ))
  have hcast :
      ((ehmDyadicReciprocalQKernel ehmR1BernoulliSawtoothPart
        J m d : ℝ) : ℂ) =
        ∑ q ∈ Finset.Icc 1 (J / d),
          (bernoulliB1 (x q) : ℂ) / (x q : ℂ) := by
    unfold ehmDyadicReciprocalQKernel ehmR1PartialSeries
      ehmR1BernoulliSawtoothPart
    push_cast
    apply Finset.sum_congr rfl
    intro q _
    simp [x]
  rw [hcast]
  calc
    (∑ q ∈ Finset.Icc 1 (J / d),
        (bernoulliB1 (x q) : ℂ) / (x q : ℂ)) =
      ∑ q ∈ Finset.Icc 1 (J / d),
        (vaalerSawtoothApprox V H (x q) +
          vaalerSawtoothError V H (x q)) / (x q : ℂ) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [vaalerSawtooth_decomposition]
    _ = (∑ q ∈ Finset.Icc 1 (J / d),
          vaalerSawtoothApprox V H (x q) / (x q : ℂ)) +
        ehmVaalerBernoulliKernelError V H J m d := by
      simp_rw [add_div, Finset.sum_add_distrib]
      rfl
    _ = ehmVaalerBernoulliKernelApprox V H J m d +
        ehmVaalerBernoulliKernelError V H J m d := by
      congr 1
      unfold ehmVaalerBernoulliKernelApprox
        ehmVaalerWeightedPhaseRow ehmVaalerRationalPhase
      simp_rw [vaalerSawtoothApprox, V.finite_fourier]
      simp_rw [Finset.sum_div]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring

/-! ## The exact endpoint resonance -/

/-- A positive natural ratio has zero fractional part exactly at the
divisibility resonance. -/
theorem fract_natRatio_eq_zero_iff_dvd
    (n m : ℕ) (hm : 0 < m) :
    Int.fract ((n : ℝ) / (m : ℝ)) = 0 ↔ m ∣ n := by
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [div_eq_zero_iff]
  simp only [hmR, or_false]
  norm_cast
  exact Nat.dvd_iff_mod_eq_zero.symm

/-- Closed form of the endpoint correction at a positive natural ratio. -/
theorem ehmR1IntegerEndpointPart_natRatio
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ehmR1IntegerEndpointPart ((n : ℝ) / (m : ℝ)) =
      if m ∣ n then (m : ℝ) / (2 * (n : ℝ)) else 0 := by
  by_cases hdiv : m ∣ n
  · have hfract : Int.fract ((n : ℝ) / (m : ℝ)) = 0 :=
      (fract_natRatio_eq_zero_iff_dvd n m hm).2 hdiv
    simp only [ehmR1IntegerEndpointPart, hfract, if_true, hdiv]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp [hnR, hmR]
  · have hfract : Int.fract ((n : ℝ) / (m : ℝ)) ≠ 0 := by
      simpa [fract_natRatio_eq_zero_iff_dvd n m hm] using hdiv
    simp [ehmR1IntegerEndpointPart, hfract, hdiv]

/-- In the collapsed Ehm row, the integer endpoint is supported precisely
on `m ∣ d*q`. -/
theorem ehmR1IntegerEndpointPart_dq_div_m
    (d q m : ℕ) (hd : 0 < d) (hq : 0 < q) (hm : 0 < m) :
    ehmR1IntegerEndpointPart (((d * q : ℕ) : ℝ) / (m : ℝ)) =
      if m ∣ d * q then
        (m : ℝ) / (2 * ((d * q : ℕ) : ℝ))
      else 0 := by
  exact ehmR1IntegerEndpointPart_natRatio (d * q) m
    (Nat.mul_pos hd hq) hm

/-! ## Reconstruction in fixed-conductor Type-I/II coordinates -/

/-- The `R1`-dependent coupled expression in collapsed Type-I/II
coordinates, before the linear remainder is inserted. -/
noncomputable def ehmDyadicKernelNormalCoupledPart
    (R1 : ℝ → ℝ) (X D J U : ℕ) : ℝ :=
  ehmDyadicFullMainJointSum R1 X J +
    ehmDyadicNearKernelTypeI R1 X D J U +
    ehmDyadicNearKernelTypeII R1 X D J U

/-- The new kernel normal form is exactly the previously audited coupled
kernel part. -/
theorem ehmDyadicCoupledKernelPart_eq_kernelNormal
    (R1 : ℝ → ℝ) (X D J U : ℕ) (hU : U ≤ 2 * X) :
    ehmDyadicCoupledKernelPart R1 X D J =
      ehmDyadicKernelNormalCoupledPart R1 X D J U := by
  unfold ehmDyadicCoupledKernelPart ehmDyadicKernelNormalCoupledPart
  rw [ehmDyadicNearComplementaryJointSum_eq_neg_mobiusBilinear,
    sub_neg_eq_add,
    ehmDyadicNearMobiusBilinearJointSum_eq_typeI_add_typeII R1 X D J U hU,
    ehmDyadicNearTypeI_eq_kernelTypeI,
    ehmDyadicNearTypeII_eq_kernelTypeII]
  ring

/-- Full exact route decomposition at the polynomial conductor.  This is the
starting point for a future Vaaler expansion and resonance calculation. -/
theorem ehmDyadicExplicitCutoffCoupledNearCore_eq_routeKernelPieces
    (X J U : ℕ) (hU : U ≤ 2 * X) :
    ehmDyadicExplicitCoupledNearCore ehmR1 X
        (ehmExplicitFarCutoff X) J =
      (ehmDyadicKernelNormalCoupledPart ehmR1SmoothPart X
          (ehmExplicitFarCutoff X) J U +
        ∑ N ∈ ehmDyadicNBlock X, ehmCoupledRemainder N) -
      ehmDyadicKernelNormalCoupledPart ehmR1BernoulliSawtoothPart X
        (ehmExplicitFarCutoff X) J U +
      ehmDyadicKernelNormalCoupledPart ehmR1IntegerEndpointPart X
        (ehmExplicitFarCutoff X) J U := by
  rw [ehmDyadicExplicitCoupledNearCore_eq_reciprocalRoutePieces]
  rw [ehmDyadicCoupledKernelPart_eq_kernelNormal _ _ _ _ U hU,
    ehmDyadicCoupledKernelPart_eq_kernelNormal _ _ _ _ U hU,
    ehmDyadicCoupledKernelPart_eq_kernelNormal _ _ _ _ U hU]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
