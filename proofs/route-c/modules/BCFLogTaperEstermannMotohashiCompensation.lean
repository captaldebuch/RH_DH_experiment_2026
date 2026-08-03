import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiFourierRecovery

/-!
# BT1-C3: arithmetic and spectral compensation tests

BT1-C2 proved that a radial Schwartz selector normalized at `u = q²` has
first weighted seminorm at least `q²`.  This file pursues both possible
responses to that loss.

* **Option A:** put the actual H15 arithmetic amplitude into the selector.
  The outer completion contributes `q⁻¹`, and the separated interior
  coefficient contributes a second `q⁻¹`.  These exactly compensate the
  forced `q²` first-seminorm cost.  The remaining question is uniform control
  of the fully reduced signed coefficient and of higher seminorms.
* **Option B:** retain the polynomial loss in the trace theorem.  An abstract
  quadratic seed cost combined with a cubic spectral gain yields a reciprocal
  majorant and hence convergence to zero.  A merely quadratic gain leaves the
  normalized majorant equal to one.

The results are quantitative transfer statements.  They do not assume or
prove the missing signed H15 cancellation estimate.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiCompensation

open Complex Filter Real SchwartzMap Topology
open scoped BigOperators Topology
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15NumeratorCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloostermanCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannModulusSeparation
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiCuspInvariance
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiFourierRecovery
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSeed
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries

/-! ## Option A: the complete arithmetic amplitude -/

/-- Insert a complex arithmetic amplitude directly into the radial Schwartz
selector. -/
noncomputable def h15MotohashiWeightedRadialSelector
    (a : ℕ → ℂ) (q : ℕ) : SchwartzMap ℝ ℂ :=
  a q • h15MotohashiRadialSchwartzSelector q

@[simp]
theorem h15MotohashiWeightedRadialSelector_sample
    (a : ℕ → ℂ) (q : ℕ) :
    h15MotohashiWeightedRadialSelector a q
        (h15MotohashiRadialSample q) = a q := by
  simp [h15MotohashiWeightedRadialSelector]

/-- The seminorm of the weighted mode is exactly the norm of its arithmetic
amplitude times the seminorm of the unit selector. -/
theorem h15MotohashiWeightedRadialSelector_seminorm
    (a : ℕ → ℂ) (q : ℕ) :
    (SchwartzMap.seminorm ℂ 1 0)
        (h15MotohashiWeightedRadialSelector a q) =
      ‖a q‖ * (SchwartzMap.seminorm ℂ 1 0)
        (h15MotohashiRadialSchwartzSelector q) := by
  exact map_smul_eq_mul _ _ _

/-- Necessary arithmetic compensation: the weighted mode still pays
`q² * ‖a q‖` in the first Schwartz seminorm. -/
theorem h15Motohashi_weightedAmplitude_cost_le_seminorm
    (a : ℕ → ℂ) (q : ℕ) :
    (q : ℝ) ^ 2 * ‖a q‖ ≤
      (SchwartzMap.seminorm ℂ 1 0)
        (h15MotohashiWeightedRadialSelector a q) := by
  rw [h15MotohashiWeightedRadialSelector_seminorm]
  nlinarith [h15MotohashiRadialSchwartzSelector_first_seminorm_lower q,
    norm_nonneg (a q)]

/-- The corresponding necessary bound for every polynomially weighted
Schwartz seminorm. -/
theorem h15Motohashi_weightedAmplitude_pow_cost_le_seminorm
    (a : ℕ → ℂ) (q k : ℕ) :
    (q : ℝ) ^ (2 * k) * ‖a q‖ ≤
      (SchwartzMap.seminorm ℂ k 0)
        (h15MotohashiWeightedRadialSelector a q) := by
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℂ
    (h15MotohashiWeightedRadialSelector a q) k
    (h15MotohashiRadialSample q)
  rw [h15MotohashiWeightedRadialSelector_sample] at h
  simpa [h15MotohashiRadialSample, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (q : ℝ)), ← pow_mul] using h

/-- The concrete fixed-width selector also has the matching quadratic upper
bound.  Thus its first seminorm has exactly quadratic order in the radial
sample; the C2 lower bound was not an artifact of a loose estimate. -/
theorem h15MotohashiRadialSchwartzSelector_first_seminorm_upper
    (q : ℕ) :
    (SchwartzMap.seminorm ℂ 1 0)
        (h15MotohashiRadialSchwartzSelector q) ≤ (q : ℝ) ^ 2 + 1 := by
  apply SchwartzMap.seminorm_le_bound' ℂ 1 0 _ (by positivity)
  intro x
  rw [pow_one, iteratedDeriv_zero]
  change |x| * ‖h15MotohashiRadialSelector q x‖ ≤ (q : ℝ) ^ 2 + 1
  by_cases hx : dist x (h15MotohashiRadialSample q) < 1 / 3
  · have hb0 : 0 ≤ h15MotohashiRadialBump q x :=
      (h15MotohashiRadialBump q).nonneg' x
    have hb1 : h15MotohashiRadialBump q x ≤ 1 :=
      (h15MotohashiRadialBump q).le_one
    have hnorm : ‖h15MotohashiRadialSelector q x‖ ≤ 1 := by
      simpa [h15MotohashiRadialSelector, abs_of_nonneg hb0] using hb1
    have habs : |x| ≤ (q : ℝ) ^ 2 + 1 / 3 := by
      calc
        |x| = |(x - h15MotohashiRadialSample q) +
            h15MotohashiRadialSample q| := by ring_nf
        _ ≤ |x - h15MotohashiRadialSample q| +
            |h15MotohashiRadialSample q| := by
          simpa [Real.norm_eq_abs] using
            norm_add_le (x - h15MotohashiRadialSample q)
              (h15MotohashiRadialSample q)
        _ ≤ (q : ℝ) ^ 2 + 1 / 3 := by
          have hx' : |x - h15MotohashiRadialSample q| < 1 / 3 := by
            simpa [Real.dist_eq] using hx
          rw [h15MotohashiRadialSample] at hx'
          rw [h15MotohashiRadialSample,
            abs_of_nonneg (sq_nonneg (q : ℝ))]
          linarith
    have hmul := mul_le_mul_of_nonneg_left hnorm (abs_nonneg x)
    nlinarith
  · have hz : h15MotohashiRadialSelector q x = 0 := by
      unfold h15MotohashiRadialSelector
      norm_cast
      apply ContDiffBump.zero_of_le_dist
      simpa [h15MotohashiRadialBump] using le_of_not_gt hx
    rw [hz, norm_zero, mul_zero]
    positivity

/-- Matching upper bound for an arbitrary arithmetic amplitude. -/
theorem h15MotohashiWeightedRadialSelector_seminorm_upper
    (a : ℕ → ℂ) (q : ℕ) :
    (SchwartzMap.seminorm ℂ 1 0)
        (h15MotohashiWeightedRadialSelector a q) ≤
      ‖a q‖ * ((q : ℝ) ^ 2 + 1) := by
  rw [h15MotohashiWeightedRadialSelector_seminorm]
  exact mul_le_mul_of_nonneg_left
    (h15MotohashiRadialSchwartzSelector_first_seminorm_upper q)
    (norm_nonneg (a q))

/-- The H15 pre-Kloosterman coefficient with its outer explicit `q⁻¹`
factor removed.  A second inverse-modulus factor remains inside the completed
numerator weight. -/
noncomputable def h15MotohashiReducedPreKloostermanCoefficient
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) : ℂ :=
  estermannDivisorCoeff n *
      inverseCoordinateFourierCoefficient
        (h15UnitNumeratorWeight N g q) m *
    ((2 * Real.pi : ℂ) * h15MotohashiSignedKernel sign η c q n)

/-- Exact extraction of the outer inverse-modulus factor. -/
theorem h15MotohashiPreKloostermanCoefficient_eq_inv_modulus_mul_reduced
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) :
    h15MotohashiPreKloostermanCoefficient N g q sign η c n m =
      (q : ℂ)⁻¹ *
        h15MotohashiReducedPreKloostermanCoefficient
          N g q sign η c n m := by
  unfold h15MotohashiPreKloostermanCoefficient
    h15MotohashiReducedPreKloostermanCoefficient
  ring

/-- The forced quadratic selector cost and the outer `q⁻¹` amplitude combine
to a linear cost before the second inverse-modulus factor is extracted. -/
theorem h15Motohashi_quadraticCost_mul_preCoefficient_norm
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) :
    (q : ℝ) ^ 2 *
        ‖h15MotohashiPreKloostermanCoefficient
          N g q sign η c n m‖ =
      (q : ℝ) *
        ‖h15MotohashiReducedPreKloostermanCoefficient
          N g q sign η c n m‖ := by
  rw [h15MotohashiPreKloostermanCoefficient_eq_inv_modulus_mul_reduced,
    norm_mul, norm_inv]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  rw [Complex.norm_natCast]
  field_simp

/-- Intermediate Option-A lower bound before extracting the inverse-modulus
factor already present in the completed numerator coefficient. -/
theorem h15Motohashi_reducedCoefficient_linearCost_le_modeSeminorm
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) :
    (q : ℝ) *
        ‖h15MotohashiReducedPreKloostermanCoefficient
          N g q sign η c n m‖ ≤
      (SchwartzMap.seminorm ℂ 1 0)
        (h15MotohashiPreKloostermanCoefficient
            N g q sign η c n m •
          h15MotohashiRadialSchwartzSelector q) := by
  rw [← h15Motohashi_quadraticCost_mul_preCoefficient_norm]
  rw [map_smul_eq_mul]
  nlinarith [h15MotohashiRadialSchwartzSelector_first_seminorm_lower q,
    norm_nonneg
      (h15MotohashiPreKloostermanCoefficient N g q sign η c n m)]

/-- Remove both inverse-modulus factors from the H15 pre-Kloosterman
coefficient.  All remaining dependence on `q` is arithmetic: the tapered
Dirichlet coefficient, the separated inverse-coordinate transform, and the
Mellin kernel. -/
noncomputable def h15MotohashiFullyReducedPreKloostermanCoefficient
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) : ℂ :=
  estermannDivisorCoeff n *
      (dirichletCoeff N (g * q) : ℂ) *
      inverseCoordinateFourierCoefficient
        (h15SeparatedUnitNumeratorWeight N g q) m *
    ((2 * Real.pi : ℂ) * h15MotohashiSignedKernel sign η c q n)

/-- **Exact double inverse-modulus factorization.** -/
theorem h15MotohashiPreKloostermanCoefficient_eq_inv_sq_mul_fullyReduced
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) :
    h15MotohashiPreKloostermanCoefficient N g q sign η c n m =
      (q : ℂ)⁻¹ ^ 2 *
        h15MotohashiFullyReducedPreKloostermanCoefficient
          N g q sign η c n m := by
  rw [h15MotohashiPreKloostermanCoefficient_eq_inv_modulus_mul_reduced]
  unfold h15MotohashiReducedPreKloostermanCoefficient
  rw [inverseCoordinateFourierCoefficient_h15UnitWeight_eq]
  unfold h15ModulusScalar
    h15MotohashiFullyReducedPreKloostermanCoefficient
  push_cast
  ring

/-- The two arithmetic inverse-modulus factors exactly cancel the forced
quadratic radial cost in norm. -/
theorem h15Motohashi_quadraticCost_mul_preCoefficient_norm_eq_fullyReduced
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) :
    (q : ℝ) ^ 2 *
        ‖h15MotohashiPreKloostermanCoefficient
          N g q sign η c n m‖ =
      ‖h15MotohashiFullyReducedPreKloostermanCoefficient
          N g q sign η c n m‖ := by
  rw [h15MotohashiPreKloostermanCoefficient_eq_inv_sq_mul_fullyReduced,
    norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  field_simp

/-- For the seminorm of polynomial weight `k+1`, the double arithmetic
inverse-modulus factor leaves the residual cost `(q²)^k`.  Thus Option A
fully resolves the first weighted seminorm (`k=0`) but higher Motohashi
seminorms still require either further arithmetic decay or Option-B spectral
gain. -/
theorem h15Motohashi_higherWeightCost_mul_preCoefficient_norm
    (N g q k : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) :
    ((q : ℝ) ^ 2) ^ (k + 1) *
        ‖h15MotohashiPreKloostermanCoefficient
          N g q sign η c n m‖ =
      ((q : ℝ) ^ 2) ^ k *
        ‖h15MotohashiFullyReducedPreKloostermanCoefficient
          N g q sign η c n m‖ := by
  rw [pow_succ, mul_assoc,
    h15Motohashi_quadraticCost_mul_preCoefficient_norm_eq_fullyReduced]

/-- Necessary higher-seminorm budget for one genuine H15 mode. -/
theorem h15Motohashi_higherWeightFullyReducedCost_le_modeSeminorm
    (N g q k : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) :
    ((q : ℝ) ^ 2) ^ k *
        ‖h15MotohashiFullyReducedPreKloostermanCoefficient
          N g q sign η c n m‖ ≤
      (SchwartzMap.seminorm ℂ (k + 1) 0)
        (h15MotohashiPreKloostermanCoefficient
            N g q sign η c n m •
          h15MotohashiRadialSchwartzSelector q) := by
  rw [← h15Motohashi_higherWeightCost_mul_preCoefficient_norm]
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℂ
    (h15MotohashiPreKloostermanCoefficient N g q sign η c n m •
      h15MotohashiRadialSchwartzSelector q) (k + 1)
    (h15MotohashiRadialSample q)
  have hsample :
      (h15MotohashiPreKloostermanCoefficient N g q sign η c n m •
          h15MotohashiRadialSchwartzSelector q)
          (h15MotohashiRadialSample q) =
        h15MotohashiPreKloostermanCoefficient
          N g q sign η c n m := by simp
  rw [hsample] at h
  simpa [h15MotohashiRadialSample, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (q : ℝ))] using h

/-- **Option-A first-seminorm success.**  For each genuine H15 mode, the
fully reduced coefficient—not a polynomial modulus factor—is the necessary
lower bound after arithmetic compensation. -/
theorem h15Motohashi_fullyReducedCoefficient_norm_le_modeSeminorm
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) :
    ‖h15MotohashiFullyReducedPreKloostermanCoefficient
        N g q sign η c n m‖ ≤
      (SchwartzMap.seminorm ℂ 1 0)
        (h15MotohashiPreKloostermanCoefficient
            N g q sign η c n m •
          h15MotohashiRadialSchwartzSelector q) := by
  rw [← h15Motohashi_quadraticCost_mul_preCoefficient_norm_eq_fullyReduced]
  rw [map_smul_eq_mul]
  nlinarith [h15MotohashiRadialSchwartzSelector_first_seminorm_lower q,
    norm_nonneg
      (h15MotohashiPreKloostermanCoefficient N g q sign η c n m)]

/-- The converse estimate is uniform in the modulus: after both arithmetic
`q⁻¹` factors are retained, the concrete first seminorm is at most twice the
norm of the fully reduced coefficient. -/
theorem h15Motohashi_modeSeminorm_le_two_mul_fullyReducedCoefficient_norm
    (N g q : ℕ) [NeZero q] (sign : H15MotohashiSign)
    (η c : ℝ) (n : ℕ) (m : ZMod q) :
    (SchwartzMap.seminorm ℂ 1 0)
        (h15MotohashiPreKloostermanCoefficient
            N g q sign η c n m •
          h15MotohashiRadialSchwartzSelector q) ≤
      2 * ‖h15MotohashiFullyReducedPreKloostermanCoefficient
        N g q sign η c n m‖ := by
  rw [map_smul_eq_mul]
  have hupper :=
    h15MotohashiRadialSchwartzSelector_first_seminorm_upper q
  have hnorm : 0 ≤
      ‖h15MotohashiPreKloostermanCoefficient
        N g q sign η c n m‖ := norm_nonneg _
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqone : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqpos
  have hqsq : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  calc
    ‖h15MotohashiPreKloostermanCoefficient
          N g q sign η c n m‖ *
        (SchwartzMap.seminorm ℂ 1 0)
          (h15MotohashiRadialSchwartzSelector q) ≤
      ‖h15MotohashiPreKloostermanCoefficient
          N g q sign η c n m‖ * ((q : ℝ) ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left hupper hnorm
    _ ≤ 2 * ((q : ℝ) ^ 2 *
        ‖h15MotohashiPreKloostermanCoefficient
          N g q sign η c n m‖) := by
      rw [show 2 * ((q : ℝ) ^ 2 *
          ‖h15MotohashiPreKloostermanCoefficient
            N g q sign η c n m‖) =
          ‖h15MotohashiPreKloostermanCoefficient
            N g q sign η c n m‖ * (2 * (q : ℝ) ^ 2) by ring]
      exact mul_le_mul_of_nonneg_left (by nlinarith) hnorm
    _ = 2 * ‖h15MotohashiFullyReducedPreKloostermanCoefficient
          N g q sign η c n m‖ := by
      rw [h15Motohashi_quadraticCost_mul_preCoefficient_norm_eq_fullyReduced]

/-! ## Option B: explicit polynomial trace loss -/

/-- The normalized majorant produced when a quadratic seed loss is met by
only a quadratic spectral gain. -/
noncomputable def h15QuadraticLossAfterQuadraticGain (N : ℕ) : ℝ :=
  (N : ℝ) ^ 2 / (N : ℝ) ^ 2

/-- The normalized majorant produced when the same loss is met by a cubic
spectral gain. -/
noncomputable def h15QuadraticLossAfterCubicGain (N : ℕ) : ℝ :=
  (N : ℝ) ^ 2 / (N : ℝ) ^ 3

theorem h15QuadraticLossAfterQuadraticGain_eq_one
    (N : ℕ) (hN : 0 < N) :
    h15QuadraticLossAfterQuadraticGain N = 1 := by
  unfold h15QuadraticLossAfterQuadraticGain
  field_simp [Nat.cast_ne_zero.mpr hN.ne']

theorem h15QuadraticLossAfterCubicGain_eq_inv
    (N : ℕ) (hN : 0 < N) :
    h15QuadraticLossAfterCubicGain N = (N : ℝ)⁻¹ := by
  unfold h15QuadraticLossAfterCubicGain
  field_simp [Nat.cast_ne_zero.mpr hN.ne']

/-- A quadratic gain is critical: its normalized upper-bound profile tends
to one, not zero.  This does not prove that the underlying signed expression
fails to decay; it proves that this majorant alone cannot establish decay. -/
theorem h15QuadraticLossAfterQuadraticGain_tendsto_one :
    Tendsto h15QuadraticLossAfterQuadraticGain atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (h15QuadraticLossAfterQuadraticGain_eq_one N hN).symm

/-- A cubic gain crosses the threshold and makes the quadratic loss decay. -/
theorem h15QuadraticLossAfterCubicGain_tendsto_zero :
    Tendsto h15QuadraticLossAfterCubicGain atTop (nhds 0) := by
  apply tendsto_inv_atTop_nhds_zero_nat.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (h15QuadraticLossAfterCubicGain_eq_inv N hN).symm

/-- Proof-carrying version of Option B.  The seed may have quadratic growth,
but the signed spectral estimate is required to gain three powers. -/
structure H15MotohashiCubicTraceCompensation where
  seedCost : ℕ → ℝ
  signedOutput : ℕ → ℝ
  Cseed : ℝ
  Ctrace : ℝ
  Cseed_nonneg : 0 ≤ Cseed
  Ctrace_nonneg : 0 ≤ Ctrace
  seedCost_nonneg : ∀ N, 0 ≤ seedCost N
  seedCost_bound : ∀ N,
    seedCost N ≤ Cseed * ((N + 1 : ℕ) : ℝ) ^ 2
  signed_trace_bound : ∀ N,
    |signedOutput N| ≤
      Ctrace * seedCost N / ((N + 1 : ℕ) : ℝ) ^ 3

/-- Cubic spectral gain turns any quadratically bounded seed cost into a
reciprocal signed-output bound. -/
theorem H15MotohashiCubicTraceCompensation.output_abs_le
    (H : H15MotohashiCubicTraceCompensation) (N : ℕ) :
    |H.signedOutput N| ≤ H.Ctrace * H.Cseed / ((N + 1 : ℕ) : ℝ) := by
  have hden : 0 ≤ ((N + 1 : ℕ) : ℝ) ^ 3 := by positivity
  calc
    |H.signedOutput N| ≤
        H.Ctrace * H.seedCost N / ((N + 1 : ℕ) : ℝ) ^ 3 :=
      H.signed_trace_bound N
    _ ≤ H.Ctrace *
          (H.Cseed * ((N + 1 : ℕ) : ℝ) ^ 2) /
            ((N + 1 : ℕ) : ℝ) ^ 3 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (H.seedCost_bound N) H.Ctrace_nonneg) hden
    _ = H.Ctrace * H.Cseed / ((N + 1 : ℕ) : ℝ) := by
      have hN : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp

/-- **Option-B success criterion.**  A genuine trace estimate with one power
more gain than the quadratic seminorm loss forces the signed output to
vanish. -/
theorem H15MotohashiCubicTraceCompensation.tendsto_zero
    (H : H15MotohashiCubicTraceCompensation) :
    Tendsto H.signedOutput atTop (nhds 0) := by
  apply squeeze_zero_norm
  · intro N
    simpa [Real.norm_eq_abs] using H.output_abs_le N
  · simpa using (tendsto_add_atTop_iff_nat (α := ℝ) 1).2
      (tendsto_const_div_atTop_nhds_zero_nat (H.Ctrace * H.Cseed))

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiCompensation
