import Beurling.Main

/-!
# The analytic extension of a Hardy-space function to the unit disc

An element `f` of `L²(𝕋)` has Fourier coefficients bounded by `‖f‖`, so the power series
`∑ₙ f̂(n) zⁿ` (`n ≥ 0`) has radius of convergence at least `1` and defines an analytic function on
the open unit disc.  For `f ∈ H²` this is the usual analytic function of which `f` is the
boundary value; in particular, an inner function in the sense of `Beurling.IsInner` has an
analytic extension to the disc.
-/

open MeasureTheory Complex Submodule Filter Topology

noncomputable section

namespace Beurling

/-- The nonnegative Fourier coefficients of an element of `L²(𝕋)`, i.e. the Taylor coefficients
of its analytic extension to the disc. -/
def discCoeff (f : L2C) : ℕ → ℂ := fun n => fourierCoeff (⇑f) (n : ℤ)

/-- The analytic extension of an element of `L²(𝕋)` to the unit disc, given by the power series
with the nonnegative Fourier coefficients as Taylor coefficients. -/
def discExt (f : L2C) : ℂ → ℂ := FormalMultilinearSeries.ofScalarsSum (E := ℂ) (discCoeff f)

lemma norm_discCoeff_le (f : L2C) (n : ℕ) : ‖discCoeff f n‖ ≤ ‖f‖ := by
  rw [discCoeff, fourierCoeff_eq_inner]
  have h1 : ‖(fourierLp 2 (n : ℤ) : L2C)‖ = 1 := by
    simpa using (orthonormal_fourier (T := (1 : ℝ))).1 (n : ℤ)
  calc ‖inner ℂ (fourierLp 2 (n : ℤ)) f‖ ≤ ‖(fourierLp 2 (n : ℤ) : L2C)‖ * ‖f‖ :=
        norm_inner_le_norm _ _
    _ = ‖f‖ := by rw [h1, one_mul]

lemma one_le_radius (f : L2C) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (discCoeff f)).radius := by
  refine FormalMultilinearSeries.le_radius_of_bound _ ‖f‖ (r := 1) fun n => ?_
  simp only [one_pow, mul_one, NNReal.coe_one]
  calc ‖FormalMultilinearSeries.ofScalars ℂ (discCoeff f) n‖
      ≤ ‖discCoeff f n‖ := by
        rw [FormalMultilinearSeries.ofScalars, norm_smul]
        have hle := ContinuousMultilinearMap.norm_mkPiAlgebraFin_le (𝕜 := ℂ) (n := n) (A := ℂ)
        simp only [norm_one, max_self] at hle
        nlinarith [norm_nonneg (discCoeff f n),
          norm_nonneg (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ)]
    _ ≤ ‖f‖ := norm_discCoeff_le f n

/-- The analytic extension is given by its Taylor series. -/
theorem discExt_apply (f : L2C) (z : ℂ) : discExt f z = ∑' n : ℕ, discCoeff f n * z ^ n := by
  rw [discExt, FormalMultilinearSeries.ofScalars_sum_eq]
  simp [smul_eq_mul]

/-- The disc extension of an element of `L²(𝕋)` is analytic on the open unit disc. -/
theorem analyticOnNhd_discExt (f : L2C) : AnalyticOnNhd ℂ (discExt f) (Metric.ball 0 1) := by
  intro z hz
  have hpos : 0 < (FormalMultilinearSeries.ofScalars ℂ (discCoeff f)).radius :=
    lt_of_lt_of_le zero_lt_one (one_le_radius f)
  have hb := (FormalMultilinearSeries.ofScalars ℂ (discCoeff f)).hasFPowerSeriesOnBall hpos
  refine hb.analyticAt_of_mem ?_
  rw [Metric.mem_eball, edist_zero_right]
  refine lt_of_lt_of_le ?_ (one_le_radius f)
  simp only [Metric.mem_ball, dist_zero_right] at hz
  rw [← ENNReal.ofReal_one, ← ofReal_norm_eq_enorm]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z)).mpr hz

end Beurling
