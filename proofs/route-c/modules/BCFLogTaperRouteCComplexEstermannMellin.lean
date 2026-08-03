import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCComplexInverseMellin

/-!
# Route C: complex-damped Estermann Mellin identity

This module lifts the scalar complex inverse-Mellin theorem through the
Estermann divisor series.  It proves absolute summability of the complete
family of vertical rows, exchanges the frequency sum with the integral, and
identifies the result with the complex-damped Lambert series for every
parameter in the open right half-plane.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexEstermannMellin

open Complex Filter MeasureTheory Set Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannSeries
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelMellin
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAbelRightLine
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexInverseMellin

/-- The `n`th Estermann row with a genuinely complex Abel parameter. -/
noncomputable def complexAbelMellinEstermannTerm
    (a q : ℕ) (u : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  let s := estermannVerticalPoint (3 / 2 : ℝ) t
  u ^ (-s) * Complex.Gamma s *
    LSeries.term (estermannCoeff a q) s n

/-- The scalar logarithmic-coordinate integrand is exactly the complex power
integrand after substituting the principal logarithm. -/
theorem complexGammaMellinIntegrand_log_eq_cpow
    {u : ℂ} (hu : u ≠ 0) (t : ℝ) :
    complexGammaMellinIntegrand (Complex.log u) t =
      u ^ (-estermannVerticalPoint (3 / 2 : ℝ) t) *
        Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) := by
  unfold complexGammaMellinIntegrand
  dsimp only
  rw [Complex.cpow_def_of_ne_zero hu]
  congr 2
  ring

/-- Multiplication by a positive real scalar commutes with the principal
complex power. -/
theorem mul_posReal_cpow
    {u : ℂ} (hu : u ≠ 0) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (u * (r : ℂ)) ^ z = u ^ z * (r : ℂ) ^ z := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hu hr0),
    Complex.cpow_def_of_ne_zero hu,
    Complex.cpow_def_of_ne_zero hr0]
  rw [Complex.log_mul_ofReal r hr u hu]
  rw [Complex.ofReal_log hr.le]
  rw [add_mul, Complex.exp_add]
  ring

/-- The exact angular gap for the logarithm of a right-half-plane
parameter. -/
theorem log_mem_complexGammaMellinStrip
    {u : ℂ} (hu : 0 < u.re) :
    Complex.log u ∈ complexGammaMellinStrip := by
  have harg : |Complex.arg u| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hu)
  change |(Complex.log u).im| < Real.pi / 2
  simpa [Complex.log_im] using harg

/-- Uniform row majorization by the scalar complex-Mellin majorant and the
absolutely summable `Re(s)=3/2` Estermann coefficient. -/
theorem norm_complexAbelMellinEstermannTerm_le
    (a q : ℕ) {u : ℂ} (hu : 0 < u.re) (n : ℕ) (t : ℝ) :
    ‖complexAbelMellinEstermannTerm a q u n t‖ ≤
      ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖ *
        complexGammaMellinMajorant (Complex.log u) t := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    norm_num at hu
  have hscalar := norm_complexGammaMellinIntegrand_le
    (Complex.log u) t
  have hterm := norm_estermannTerm_three_halves_add_I_mul a q n t
  unfold complexAbelMellinEstermannTerm
  dsimp only
  rw [← complexGammaMellinIntegrand_log_eq_cpow hu0, norm_mul]
  change
    ‖complexGammaMellinIntegrand (Complex.log u) t‖ *
        ‖LSeries.term (estermannCoeff a q)
          (((3 / 2 : ℝ) : ℂ) + t * Complex.I) n‖ ≤ _
  rw [hterm]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hscalar
      (norm_nonneg (LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n)))

theorem continuous_complexEstermannTerm_vertical
    (a q n : ℕ) :
    Continuous (fun t : ℝ =>
      LSeries.term (estermannCoeff a q)
        (estermannVerticalPoint (3 / 2 : ℝ) t) n) := by
  by_cases hn : n = 0
  · subst n
    simpa only [LSeries.term_zero] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · rw [show (fun t : ℝ => LSeries.term (estermannCoeff a q)
          (estermannVerticalPoint (3 / 2 : ℝ) t) n) =
        (fun t : ℝ => estermannCoeff a q n /
          (n : ℂ) ^ (estermannVerticalPoint (3 / 2 : ℝ) t)) by
      funext t
      rw [LSeries.term_of_ne_zero hn]]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    letI : NeZero (n : ℂ) := ⟨hn0⟩
    apply continuous_const.div
    · exact (continuous_const_cpow (n : ℂ)).comp (by
        unfold estermannVerticalPoint
        fun_prop)
    · intro t
      exact cpow_ne_zero_iff.mpr (Or.inl hn0)

/-- Every complex-damped Estermann row is Bochner integrable. -/
theorem integrable_complexAbelMellinEstermannTerm
    (a q : ℕ) {u : ℂ} (hu : 0 < u.re) (n : ℕ) :
    Integrable (complexAbelMellinEstermannTerm a q u n) := by
  have hstrip := log_mem_complexGammaMellinStrip hu
  change |(Complex.log u).im| < Real.pi / 2 at hstrip
  have hmajor : Integrable (fun t : ℝ =>
      ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖ *
        complexGammaMellinMajorant (Complex.log u) t) :=
    (show Integrable (complexGammaMellinMajorant (Complex.log u)) by
      unfold complexGammaMellinMajorant
      exact (integrable_abelPolynomialExponentialMajorant 1
        (sub_pos.mpr hstrip)).const_mul _).const_mul _
  apply Integrable.mono' hmajor
  · have hu0 : u ≠ 0 := by
      intro h
      subst u
      norm_num at hu
    have hrepr : (complexAbelMellinEstermannTerm a q u n) =
        fun t : ℝ => complexGammaMellinIntegrand (Complex.log u) t *
          LSeries.term (estermannCoeff a q)
            (estermannVerticalPoint (3 / 2 : ℝ) t) n := by
      funext t
      unfold complexAbelMellinEstermannTerm
      dsimp only
      rw [complexGammaMellinIntegrand_log_eq_cpow hu0]
    rw [hrepr]
    exact ((continuous_complexGammaMellinIntegrand (Complex.log u)).mul
      (continuous_complexEstermannTerm_vertical a q n)).aestronglyMeasurable
  · filter_upwards [] with t
    exact norm_complexAbelMellinEstermannTerm_le a q hu n t

/-- The whole family of rowwise `L¹` norms is summable, giving the exact
Tonelli/Fubini input for the complex-damped divisor series. -/
theorem summable_integral_norm_complexAbelMellinEstermannTerm
    (a q : ℕ) {u : ℂ} (hu : 0 < u.re) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖complexAbelMellinEstermannTerm a q u n t‖) := by
  have hstrip := log_mem_complexGammaMellinStrip hu
  change |(Complex.log u).im| < Real.pi / 2 at hstrip
  have hs0 := estermannCoeff_summable a q
    (s := (3 / 2 : ℂ)) (by norm_num)
  rw [LSeriesSummable] at hs0
  have hs : Summable (fun n : ℕ =>
      ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖) := hs0.norm
  let M : ℝ := ∫ t : ℝ,
    complexGammaMellinMajorant (Complex.log u) t
  have hmajorInt : Integrable
      (complexGammaMellinMajorant (Complex.log u)) := by
    unfold complexGammaMellinMajorant
    exact (integrable_abelPolynomialExponentialMajorant 1
      (sub_pos.mpr hstrip)).const_mul _
  have hcomparison : ∀ n : ℕ,
      (∫ t : ℝ, ‖complexAbelMellinEstermannTerm a q u n t‖) ≤
        M * ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖ := by
    intro n
    have hrow := (integrable_complexAbelMellinEstermannTerm
      a q hu n).norm
    have hmaj := hmajorInt.const_mul
      ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖
    have hle :
        (∫ t : ℝ, ‖complexAbelMellinEstermannTerm a q u n t‖) ≤
          ∫ t : ℝ,
            ‖LSeries.term (estermannCoeff a q) (3 / 2 : ℂ) n‖ *
              complexGammaMellinMajorant (Complex.log u) t := by
      apply integral_mono hrow hmaj
      intro t
      exact norm_complexAbelMellinEstermannTerm_le a q hu n t
    rw [integral_const_mul] at hle
    simpa [M, mul_comm] using hle
  exact ((hs.mul_left M).of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _)) hcomparison

/-- Genuine global exchange of the Estermann sum and the vertical integral. -/
theorem tsum_integral_eq_integral_tsum_complexAbelMellinEstermannTerm
    (a q : ℕ) {u : ℂ} (hu : 0 < u.re) :
    (∑' n : ℕ, ∫ t : ℝ,
        complexAbelMellinEstermannTerm a q u n t) =
      ∫ t : ℝ, ∑' n : ℕ,
        complexAbelMellinEstermannTerm a q u n t := by
  exact integral_tsum_of_summable_integral_norm
    (fun n => integrable_complexAbelMellinEstermannTerm a q hu n)
    (summable_integral_norm_complexAbelMellinEstermannTerm a q hu)

/-- The pointwise row sum is the classical Estermann Dirichlet series. -/
theorem tsum_complexAbelMellinEstermannTerm
    (a q : ℕ) (u : ℂ) (t : ℝ) :
    (∑' n : ℕ, complexAbelMellinEstermannTerm a q u n t) =
      u ^ (-estermannVerticalPoint (3 / 2 : ℝ) t) *
        Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) *
        estermannDirichletSeries a q
          (estermannVerticalPoint (3 / 2 : ℝ) t) := by
  unfold complexAbelMellinEstermannTerm estermannDirichletSeries LSeries
  dsimp only
  rw [← tsum_mul_left]

/-- The complex-damped Estermann divisor Lambert series. -/
noncomputable def complexDampedEstermannLambertSeries
    (a q : ℕ) (u : ℂ) : ℂ :=
  ∑' n : ℕ, LSeries.term (estermannCoeff a q) 0 n *
    Complex.exp (-(u * (n : ℂ)))

/-- A positive-real scalar may be absorbed into the complex base without a
branch jump. -/
theorem cpow_mul_natCast
    {u : ℂ} (hu : u ≠ 0) {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    (u * (n : ℂ)) ^ z = u ^ z * (n : ℂ) ^ z := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  simpa using mul_posReal_cpow hu hnpos z

/-- Termwise scalar complex inverse Mellin after absorbing the Dirichlet
frequency into the Abel parameter. -/
theorem integral_complexAbelMellinEstermannTerm
    (a q : ℕ) {u : ℂ} (hu : 0 < u.re) (n : ℕ) :
    (∫ t : ℝ, complexAbelMellinEstermannTerm a q u n t) =
      (2 * Real.pi : ℝ) *
        (LSeries.term (estermannCoeff a q) 0 n *
          Complex.exp (-(u * (n : ℂ)))) := by
  by_cases hn : n = 0
  · subst n
    simp [complexAbelMellinEstermannTerm]
  · have hu0 : u ≠ 0 := by
      intro h
      subst u
      norm_num at hu
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hunRe : 0 < (u * (n : ℂ)).re := by
      simpa [mul_re] using mul_pos hu hnpos
    have hscalar := integral_Gamma_vertical_three_halves_complex hunRe
    have hfun : (fun t : ℝ =>
        complexAbelMellinEstermannTerm a q u n t) =
      fun t : ℝ => estermannCoeff a q n *
        ((u * (n : ℂ)) ^
            (-estermannVerticalPoint (3 / 2 : ℝ) t) *
          Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t)) := by
      funext t
      unfold complexAbelMellinEstermannTerm
      dsimp only
      rw [LSeries.term_of_ne_zero hn]
      let s := estermannVerticalPoint (3 / 2 : ℝ) t
      change u ^ (-s) * Complex.Gamma s *
          (estermannCoeff a q n / (n : ℂ) ^ s) =
        estermannCoeff a q n *
          ((u * (n : ℂ)) ^ (-s) * Complex.Gamma s)
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
      rw [cpow_mul_natCast hu0 hn]
      ring
    rw [hfun, integral_const_mul, hscalar]
    rw [LSeries.term_of_ne_zero hn]
    norm_num
    ring

/-- The full complex Abel--Estermann contour is exactly the complex-damped
Lambert series. -/
theorem complexAbelEstermannMellinIdentity
    (a q : ℕ) {u : ℂ} (hu : 0 < u.re) :
    (∫ t : ℝ,
      u ^ (-estermannVerticalPoint (3 / 2 : ℝ) t) *
        Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) *
        estermannDirichletSeries a q
          (estermannVerticalPoint (3 / 2 : ℝ) t)) =
      (2 * Real.pi : ℝ) *
        complexDampedEstermannLambertSeries a q u := by
  calc
    (∫ t : ℝ,
        u ^ (-estermannVerticalPoint (3 / 2 : ℝ) t) *
          Complex.Gamma (estermannVerticalPoint (3 / 2 : ℝ) t) *
          estermannDirichletSeries a q
            (estermannVerticalPoint (3 / 2 : ℝ) t)) =
      ∫ t : ℝ, ∑' n : ℕ,
        complexAbelMellinEstermannTerm a q u n t := by
          apply integral_congr_ae
          filter_upwards [] with t
          exact (tsum_complexAbelMellinEstermannTerm a q u t).symm
    _ = ∑' n : ℕ, ∫ t : ℝ,
        complexAbelMellinEstermannTerm a q u n t :=
      (tsum_integral_eq_integral_tsum_complexAbelMellinEstermannTerm
        a q hu).symm
    _ = (2 * Real.pi : ℝ) *
        complexDampedEstermannLambertSeries a q u := by
      unfold complexDampedEstermannLambertSeries
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      exact integral_complexAbelMellinEstermannTerm a q hu n

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCComplexEstermannMellin
