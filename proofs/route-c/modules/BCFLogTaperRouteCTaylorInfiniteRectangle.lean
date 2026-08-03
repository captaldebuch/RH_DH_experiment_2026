import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorHorizontalDecay

/-!
# Route C: the infinite-height Taylor rectangle

This module passes the exact finite multi-residue rectangle for the literal
Bettin--Conrey `g₀` integrand to infinite height.  Integrability on both
vertical sides comes from the intrinsic shifted-line majorants, while the
coupled horizontal pair vanishes by the reflected Gamma--zeta estimate.

The resulting identity keeps all normalizations visible:

`right integral = left integral + 2π * (finite residue sum)`.

Since the source definition of `g₀` is `1/π` times the right integral, every
crossed pole contributes exactly twice its residue.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorInfiniteRectangle

open Complex Filter MeasureTheory Topology
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannVoronoi
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCanonicalStrip
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorHorizontalDecay
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorLineMajorant
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorMultiResidueRectangle
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCGammaShiftedLines

/-- The canonical left edge is the `2M`-th shifted Taylor line. -/
theorem routeCTaylorCanonicalLeft_verticalPoint
    (M : ℕ) (t : ℝ) :
    (routeCTaylorCanonicalLeft M : ℂ) + (t : ℂ) * I =
      routeCGammaShiftedPoint (2 * M) t := by
  unfold routeCTaylorCanonicalLeft routeCGammaShiftedPoint
  push_cast
  ring

/-- The canonical right edge is the original central line. -/
theorem routeCTaylorCanonicalRight_verticalPoint (t : ℝ) :
    (routeCTaylorCanonicalRight : ℂ) + (t : ℂ) * I =
      bettinConreyCentralVerticalPoint t := by
  unfold routeCTaylorCanonicalRight bettinConreyCentralVerticalPoint
  push_cast
  ring

/-- Restriction of the meromorphic integrand to the left edge is the literal
shifted-line integrand already controlled by the Taylor majorant. -/
theorem bettinConreyGZeroMeromorphicIntegrand_left_line
    (u : ℂ) (M : ℕ) (t : ℝ) :
    bettinConreyGZeroMeromorphicIntegrand u
        ((routeCTaylorCanonicalLeft M : ℂ) + (t : ℂ) * I) =
      bettinConreyGZeroShiftedVerticalIntegrand u (2 * M) t := by
  rw [routeCTaylorCanonicalLeft_verticalPoint]
  rfl

/-- Restriction to the right edge is the source integrand defining `g₀`. -/
theorem bettinConreyGZeroMeromorphicIntegrand_right_line
    (u : ℂ) (t : ℝ) :
    bettinConreyGZeroMeromorphicIntegrand u
        ((routeCTaylorCanonicalRight : ℂ) + (t : ℂ) * I) =
      bettinConreyGZeroVerticalIntegrand u t := by
  rw [routeCTaylorCanonicalRight_verticalPoint]
  rfl

/-- The left vertical truncations converge to the complete shifted-line
integral. -/
theorem tendsto_bettinConreyGZero_left_vertical
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (hM : 1 ≤ M)
    (theta : ℝ) (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi) :
    Tendsto
      (truncatedVerticalIntegral
        (bettinConreyGZeroMeromorphicIntegrand u)
        (routeCTaylorCanonicalLeft M))
      atTop
      (nhds (∫ t : ℝ,
        bettinConreyGZeroShiftedVerticalIntegrand u (2 * M) t)) := by
  have htwoM : 1 ≤ 2 * M := by omega
  have hint := integrable_bettinConreyGZeroShiftedVerticalIntegrand
    u hu (2 * M) htwoM theta harg htheta
  have hline : Integrable (fun t : ℝ =>
      bettinConreyGZeroMeromorphicIntegrand u
        (estermannVerticalPoint (routeCTaylorCanonicalLeft M) t)) := by
    simpa [estermannVerticalPoint,
      bettinConreyGZeroMeromorphicIntegrand_left_line] using hint
  simpa [estermannVerticalPoint,
    bettinConreyGZeroMeromorphicIntegrand_left_line] using
      (tendsto_truncatedVerticalIntegral_of_integrable
        (bettinConreyGZeroMeromorphicIntegrand u)
        (routeCTaylorCanonicalLeft M) hline)

/-- The right vertical truncations converge to the complete central-line
integral used in the definition of `g₀`. -/
theorem tendsto_bettinConreyGZero_right_vertical
    (u : ℂ) (hu : u ≠ 0)
    (theta : ℝ) (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi) :
    Tendsto
      (truncatedVerticalIntegral
        (bettinConreyGZeroMeromorphicIntegrand u)
        routeCTaylorCanonicalRight)
      atTop
      (nhds (∫ t : ℝ, bettinConreyGZeroVerticalIntegrand u t)) := by
  have hint := integrable_bettinConreyGZeroShiftedVerticalIntegrand
    u hu 1 (by omega) theta harg htheta
  have hcentral : Integrable (bettinConreyGZeroVerticalIntegrand u) := by
    apply hint.congr
    filter_upwards [] with t
    exact bettinConreyGZeroShiftedVerticalIntegrand_one u t
  have hline : Integrable (fun t : ℝ =>
      bettinConreyGZeroMeromorphicIntegrand u
        (estermannVerticalPoint routeCTaylorCanonicalRight t)) := by
    simpa [estermannVerticalPoint,
      bettinConreyGZeroMeromorphicIntegrand_right_line] using hcentral
  simpa [estermannVerticalPoint,
    bettinConreyGZeroMeromorphicIntegrand_right_line] using
      (tendsto_truncatedVerticalIntegral_of_integrable
        (bettinConreyGZeroMeromorphicIntegrand u)
        routeCTaylorCanonicalRight hline)

/-- Infinite-height form of the genuine finite Taylor rectangle. -/
theorem bettinConreyGZero_verticalIntegral_eq_shifted_add_residues
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (hM : 1 ≤ M)
    {theta : ℝ} (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi) :
    (∫ t : ℝ, bettinConreyGZeroVerticalIntegrand u t) =
      (∫ t : ℝ,
        bettinConreyGZeroShiftedVerticalIntegrand u (2 * M) t) +
        2 * Real.pi *
          ∑ n ∈ Finset.Icc 1 M,
            bettinConreyGZeroOddResidue u n := by
  exact verticalLimit_eq_of_rectangularBoundary
    (bettinConreyGZeroMeromorphicIntegrand u)
    (routeCTaylorCanonicalLeft M) routeCTaylorCanonicalRight
    (∑ n ∈ Finset.Icc 1 M, bettinConreyGZeroOddResidue u n)
    (∫ t : ℝ,
      bettinConreyGZeroShiftedVerticalIntegrand u (2 * M) t)
    (∫ t : ℝ, bettinConreyGZeroVerticalIntegrand u t)
    (fun T hT =>
      rectangularBoundaryIntegral_bettinConreyGZero_eq_oddResidues
        u hu M hM hT)
    (tendsto_bettinConreyGZero_left_vertical
      u hu M hM theta harg htheta)
    (tendsto_bettinConreyGZero_right_vertical
      u hu theta harg htheta)
    (bettinConreyGZero_horizontal_pair_vanishes
      u hu M hM harg htheta)

/-- Source-normalized contour shift.  The factor `1/π` in `g₀` turns the
residue-theorem factor `2π` into the coefficient `2`. -/
theorem bettinConreyGZero_eq_shiftedIntegral_add_residues
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (hM : 1 ≤ M)
    {theta : ℝ} (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi) :
    bettinConreyGZero u =
      (1 / (Real.pi : ℂ)) *
        (∫ t : ℝ,
          bettinConreyGZeroShiftedVerticalIntegrand u (2 * M) t) +
        2 * ∑ n ∈ Finset.Icc 1 M,
          bettinConreyGZeroOddResidue u n := by
  rw [bettinConreyGZero]
  rw [bettinConreyGZero_verticalIntegral_eq_shifted_add_residues
    u hu M hM harg htheta]
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-! ## The literal finite Taylor polynomial -/

/-- The finite Bernoulli--zeta polynomial printed in the contour proof of
Bettin--Conrey's central Taylor theorem. -/
noncomputable def bettinConreyGZeroFiniteTaylorPolynomial
    (u : ℂ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M,
    2 * (-1 : ℂ) ^ n * (((bernoulli (2 * n) : ℚ) : ℂ)) /
        (Nat.factorial (2 * n) : ℂ) *
      riemannZeta (routeCTaylorPolePoint n) *
        ((2 * Real.pi : ℂ) * u) ^ (2 * n - 1)

/-- The normalized finite residue sum is exactly the displayed
Bernoulli--zeta polynomial, coefficient by coefficient. -/
theorem two_mul_sum_bettinConreyGZeroOddResidue_eq_polynomial
    (u : ℂ) (M : ℕ) :
    2 * ∑ n ∈ Finset.Icc 1 M,
        bettinConreyGZeroOddResidue u n =
      bettinConreyGZeroFiniteTaylorPolynomial u M := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact two_mul_bettinConreyGZeroOddResidue u n
    (Finset.mem_Icc.mp hn).1

/-- The complete left-line integral, including the source factor `1/π`, is
the exact order-`M` Taylor remainder. -/
noncomputable def bettinConreyGZeroFiniteTaylorRemainder
    (u : ℂ) (M : ℕ) : ℂ :=
  (1 / (Real.pi : ℂ)) *
    ∫ t : ℝ,
      bettinConreyGZeroShiftedVerticalIntegrand u (2 * M) t

/-- Exact arbitrary-order finite Taylor expansion of the contour-defined
`g₀`; no big-O notation or limiting argument is hidden in the statement. -/
theorem bettinConreyGZero_eq_finiteTaylorPolynomial_add_remainder
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (hM : 1 ≤ M)
    {theta : ℝ} (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi) :
    bettinConreyGZero u =
      bettinConreyGZeroFiniteTaylorPolynomial u M +
        bettinConreyGZeroFiniteTaylorRemainder u M := by
  rw [bettinConreyGZero_eq_shiftedIntegral_add_residues
    u hu M hM harg htheta]
  rw [two_mul_sum_bettinConreyGZeroOddResidue_eq_polynomial]
  unfold bettinConreyGZeroFiniteTaylorRemainder
  ring

/-- The exact remainder is bounded by the integrable shifted-line
majorant.  Its definition exposes the expected radial factor
`‖u‖^(2M-1/2)` and the intrinsic angular rate `π-theta`. -/
theorem norm_bettinConreyGZeroFiniteTaylorRemainder_le
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (hM : 1 ≤ M)
    (theta : ℝ) (harg : |Complex.arg u| ≤ theta)
    (htheta : theta < Real.pi) :
    ‖bettinConreyGZeroFiniteTaylorRemainder u M‖ ≤
      ‖(1 / (Real.pi : ℂ))‖ *
        ∫ t : ℝ, routeCTaylorLineMajorant u (2 * M) theta t := by
  have htwoM : 1 ≤ 2 * M := by omega
  have hmajor := integrable_routeCTaylorLineMajorant u (2 * M)
    theta htheta
  have hne : ∀ᵐ t : ℝ, t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hintegral :
      ‖∫ t : ℝ,
          bettinConreyGZeroShiftedVerticalIntegrand u (2 * M) t‖ ≤
        ∫ t : ℝ, routeCTaylorLineMajorant u (2 * M) theta t := by
    apply norm_integral_le_of_norm_le hmajor
    filter_upwards [hne] with t ht
    exact norm_bettinConreyGZeroShiftedVerticalIntegrand_le
      u hu (2 * M) htwoM theta t harg ht
  unfold bettinConreyGZeroFiniteTaylorRemainder
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hintegral (norm_nonneg _)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorInfiniteRectangle
