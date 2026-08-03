import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannTwoPoleRectangle

/-!
# Route C: finite simple-pole rectangle geometry

The Taylor shift crosses finitely many negative odd poles.  The project
already contains exact rectangle integrals for one simple pole.  This module
proves finite additivity on the four parametrized edges and packages the
result for an arbitrary finite family of real poles.  It is the geometric
half of the multi-residue shift; the analytic half is the construction of a
holomorphic pole-subtracted remainder.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFinitePoleGeometry

open Complex Set MeasureTheory
open scoped Interval Real BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannTwoPoleRectangle
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues

/-- A rectangular boundary integral commutes with a finite sum whenever
every summand is continuous on each of the four parametrized edges. -/
theorem rectangularBoundaryIntegral_finsetSum
    {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (σL σR T : ℝ)
    (hminus : ∀ i ∈ S, Continuous
      (fun x : ℝ => f i ((x : ℂ) - (T : ℂ) * I)))
    (hplus : ∀ i ∈ S, Continuous
      (fun x : ℝ => f i ((x : ℂ) + (T : ℂ) * I)))
    (hleft : ∀ i ∈ S, Continuous
      (fun y : ℝ => f i ((σL : ℂ) + (y : ℂ) * I)))
    (hright : ∀ i ∈ S, Continuous
      (fun y : ℝ => f i ((σR : ℂ) + (y : ℂ) * I))) :
    rectangularBoundaryIntegral (fun s => ∑ i ∈ S, f i s)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      ∑ i ∈ S, rectangularBoundaryIntegral (f i)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) := by
  unfold rectangularBoundaryIntegral rectangularLowerEdge
    rectangularUpperEdge rectangularRightEdge rectangularLeftEdge
    symmetricLowerCorner symmetricUpperCorner
  simp [Complex.mul_re, Complex.mul_im]
  simp only [← sub_eq_add_neg]
  rw [intervalIntegral.integral_finsetSum
    (fun i hi => (hminus i hi).intervalIntegrable σL σR)]
  rw [intervalIntegral.integral_finsetSum
    (fun i hi => (hplus i hi).intervalIntegrable σL σR)]
  rw [intervalIntegral.integral_finsetSum
    (fun i hi => (hright i hi).intervalIntegrable (-T) T)]
  rw [intervalIntegral.integral_finsetSum
    (fun i hi => (hleft i hi).intervalIntegrable (-T) T)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]

/-- The exact boundary integral of a finite family of simple poles lying
strictly inside the rectangle. -/
theorem rectangularBoundaryIntegral_finset_simplePoles
    {ι : Type*} (S : Finset ι) (p : ι → ℝ) (c : ι → ℂ)
    (σL σR T : ℝ)
    (hL : ∀ i ∈ S, σL < p i)
    (hR : ∀ i ∈ S, p i < σR)
    (hT : 0 < T) :
    rectangularBoundaryIntegral
        (fun s : ℂ => ∑ i ∈ S, c i * (s - (p i : ℂ))⁻¹)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      2 * Real.pi * I * ∑ i ∈ S, c i := by
  let f : ι → ℂ → ℂ := fun i s => c i * (s - (p i : ℂ))⁻¹
  have hminus : ∀ i ∈ S, Continuous
      (fun x : ℝ => f i ((x : ℂ) - (T : ℂ) * I)) := by
    intro i hi
    unfold f
    apply continuous_const.mul
    apply Continuous.inv₀ (by fun_prop)
    intro x hx
    have him := congrArg Complex.im hx
    simp at him
    linarith
  have hplus : ∀ i ∈ S, Continuous
      (fun x : ℝ => f i ((x : ℂ) + (T : ℂ) * I)) := by
    intro i hi
    unfold f
    apply continuous_const.mul
    apply Continuous.inv₀ (by fun_prop)
    intro x hx
    have him := congrArg Complex.im hx
    simp at him
    linarith
  have hleft : ∀ i ∈ S, Continuous
      (fun y : ℝ => f i ((σL : ℂ) + (y : ℂ) * I)) := by
    intro i hi
    unfold f
    apply continuous_const.mul
    apply Continuous.inv₀ (by fun_prop)
    intro y hy
    have hre := congrArg Complex.re hy
    simp at hre
    linarith [hL i hi]
  have hright : ∀ i ∈ S, Continuous
      (fun y : ℝ => f i ((σR : ℂ) + (y : ℂ) * I)) := by
    intro i hi
    unfold f
    apply continuous_const.mul
    apply Continuous.inv₀ (by fun_prop)
    intro y hy
    have hre := congrArg Complex.re hy
    simp at hre
    linarith [hR i hi]
  rw [show rectangularBoundaryIntegral
      (fun s : ℂ => ∑ i ∈ S, c i * (s - (p i : ℂ))⁻¹)
      (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
        ∑ i ∈ S, rectangularBoundaryIntegral (f i)
          (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) by
      exact rectangularBoundaryIntegral_finsetSum S f σL σR T
        hminus hplus hleft hright]
  calc
    (∑ i ∈ S, rectangularBoundaryIntegral (f i)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T)) =
        ∑ i ∈ S, c i * (2 * Real.pi * I) := by
          apply Finset.sum_congr rfl
          intro i hi
          unfold f
          rw [rectangularBoundaryIntegral_const_mul,
            rectangularBoundaryIntegral_simplePole (p i) σL σR T
              (hL i hi) (hR i hi) hT]
    _ = 2 * Real.pi * I * ∑ i ∈ S, c i := by
      rw [← Finset.sum_mul]
      ring

/-- Specialization to the first `M` negative odd Taylor poles. -/
theorem rectangularBoundaryIntegral_routeCTaylorPoles
    (u : ℂ) (M : ℕ) (σL σR T : ℝ)
    (hL : ∀ n ∈ Finset.Icc 1 M,
      σL < (routeCTaylorPolePoint n).re)
    (hR : ∀ n ∈ Finset.Icc 1 M,
      (routeCTaylorPolePoint n).re < σR)
    (hT : 0 < T) :
    rectangularBoundaryIntegral
        (fun s : ℂ => ∑ n ∈ Finset.Icc 1 M,
          bettinConreyGZeroOddResidue u n *
            (s - routeCTaylorPolePoint n)⁻¹)
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      2 * Real.pi * I *
        ∑ n ∈ Finset.Icc 1 M,
          bettinConreyGZeroOddResidue u n := by
  simpa [routeCTaylorPolePoint] using
    (rectangularBoundaryIntegral_finset_simplePoles
      (Finset.Icc 1 M)
      (fun n => (routeCTaylorPolePoint n).re)
      (bettinConreyGZeroOddResidue u) σL σR T hL hR hT)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFinitePoleGeometry
