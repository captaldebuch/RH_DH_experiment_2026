import Beurling.Basic

/-!
# Uniqueness theorem for Fourier coefficients of `L¹` functions on the circle

The main result of this file, `Beurling.ae_eq_zero_of_fourierCoeff_eq_zero`, states that an
integrable function on the circle all of whose Fourier coefficients vanish is zero almost
everywhere.  Mathlib contains the corresponding statement for `L²` functions (as a consequence of
the fact that the characters form a Hilbert basis), but not the `L¹` version, which is what is
needed to prove that the wandering vector of a shift-invariant subspace is an inner function.

The proof is the classical one: the characters span a dense subspace of `C(𝕋, ℂ)` by
Stone–Weierstrass, so the (continuous) functional `φ ↦ ∫ φ w` vanishes on all continuous
functions; testing against continuous approximations of indicators of closed sets shows that the
integral of `w` over every closed set vanishes, whence `w = 0` a.e.
-/

open MeasureTheory Complex Submodule Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Beurling

/-- The pairing `φ ↦ ∫ φ w` of continuous functions against a fixed integrable function,
as a continuous linear functional. -/
def integralPairing {w : Circ → ℂ} (hw : Integrable w mu) : C(Circ, ℂ) →L[ℂ] ℂ := by
  refine LinearMap.mkContinuous
    { toFun := fun φ => ∫ x, φ x * w x ∂mu
      map_add' := ?_
      map_smul' := ?_ } (∫ x, ‖w x‖ ∂mu) ?_
  · intro φ ψ
    simp only [ContinuousMap.add_apply, add_mul]
    exact integral_add (hw.bdd_mul (φ.continuous.aestronglyMeasurable)
        (.of_forall fun x => φ.norm_coe_le_norm x))
      (hw.bdd_mul (ψ.continuous.aestronglyMeasurable)
        (.of_forall fun x => ψ.norm_coe_le_norm x))
  · intro c φ
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul c _
  · intro φ
    have hint : Integrable (fun x => φ x * w x) mu :=
      hw.bdd_mul (φ.continuous.aestronglyMeasurable)
        (.of_forall fun x => φ.norm_coe_le_norm x)
    calc ‖∫ x, φ x * w x ∂mu‖ ≤ ∫ x, ‖φ x * w x‖ ∂mu := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖φ‖ * ‖w x‖ ∂mu := by
          refine integral_mono hint.norm ((hw.norm).const_mul _) fun x => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (norm_nonneg _)
      _ = ‖φ‖ * ∫ x, ‖w x‖ ∂mu := integral_const_mul _ _
      _ = (∫ x, ‖w x‖ ∂mu) * ‖φ‖ := mul_comm _ _

lemma integralPairing_apply {w : Circ → ℂ} (hw : Integrable w mu) (φ : C(Circ, ℂ)) :
    integralPairing hw φ = ∫ x, φ x * w x ∂mu := rfl

/-- If all Fourier coefficients of an integrable function vanish, then the integral of the
function against any continuous function vanishes. -/
lemma integral_continuous_mul_eq_zero_of_fourierCoeff_eq_zero {w : Circ → ℂ}
    (hw : Integrable w mu) (h : ∀ n : ℤ, fourierCoeff w n = 0) (φ : C(Circ, ℂ)) :
    ∫ x, φ x * w x ∂mu = 0 := by
  have hker : (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) ≤
      LinearMap.ker (integralPairing hw).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    have : ∫ x, fourier n x * w x ∂mu = 0 := by
      have := h (-n)
      simpa [fourierCoeff, smul_eq_mul] using this
    simpa [LinearMap.mem_ker, integralPairing_apply] using this
  have hclosed : IsClosed ((LinearMap.ker (integralPairing hw).toLinearMap : Submodule ℂ _) :
      Set C(Circ, ℂ)) := (integralPairing hw).isClosed_ker
  have htop : (⊤ : Submodule ℂ C(Circ, ℂ)) ≤ LinearMap.ker (integralPairing hw).toLinearMap := by
    rw [← span_fourier_closure_eq_top]
    exact Submodule.topologicalClosure_minimal _ hker hclosed
  have : φ ∈ LinearMap.ker (integralPairing hw).toLinearMap := htop Submodule.mem_top
  simpa [LinearMap.mem_ker, integralPairing_apply] using this

/-- **Uniqueness theorem for Fourier coefficients**: an integrable function on the circle whose
Fourier coefficients all vanish is zero almost everywhere. -/
theorem ae_eq_zero_of_fourierCoeff_eq_zero {w : Circ → ℂ} (hw : Integrable w mu)
    (h : ∀ n : ℤ, fourierCoeff w n = 0) : w =ᵐ[mu] 0 := by
  refine ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hw fun F hF => ?_
  -- continuous approximations of the indicator of `F`
  set fseq := hF.apprSeq with hfseq
  have hbound : ∀ n x, ((fseq n x : ℝ≥0) : ℝ) ≤ 1 := fun n x => by
    exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hF n x
  have hnonneg : ∀ n x, (0 : ℝ) ≤ ((fseq n x : ℝ≥0) : ℝ) := fun n x => (fseq n x).coe_nonneg
  -- the corresponding complex-valued continuous functions
  set φ : ℕ → C(Circ, ℂ) := fun n =>
    ⟨fun x => ((fseq n x : ℝ≥0) : ℝ), by
      exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (fseq n).continuous)⟩
    with hφ
  have hzero : ∀ n, ∫ x, (φ n) x * w x ∂mu = 0 := fun n =>
    integral_continuous_mul_eq_zero_of_fourierCoeff_eq_zero hw h (φ n)
  -- pointwise convergence to the indicator
  have hptw : ∀ x, Tendsto (fun n => (φ n) x * w x) atTop (𝓝 (F.indicator (fun _ => (1 : ℂ)) x
      * w x)) := by
    intro x
    have := (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hF)) x
    have h2 : Tendsto (fun n => ((fseq n x : ℝ≥0) : ℂ)) atTop
        (𝓝 ((F.indicator (fun _ => (1 : ℝ≥0)) x : ℝ≥0) : ℂ)) := by
      exact (Complex.continuous_ofReal.comp NNReal.continuous_coe).continuousAt.tendsto.comp this
    have h3 : ((F.indicator (fun _ => (1 : ℝ≥0)) x : ℝ≥0) : ℂ) =
        F.indicator (fun _ => (1 : ℂ)) x := by
      by_cases hx : x ∈ F <;> simp [hx]
    rw [← h3]
    exact h2.mul_const _
  -- dominated convergence
  have hlim : Tendsto (fun n => ∫ x, (φ n) x * w x ∂mu) atTop
      (𝓝 (∫ x, F.indicator (fun _ => (1 : ℂ)) x * w x ∂mu)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖w x‖)
      (fun n => ((φ n).continuous.aestronglyMeasurable).mul hw.aestronglyMeasurable)
      hw.norm ?_ (.of_forall hptw)
    intro n
    filter_upwards with x
    rw [norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    have hnorm : ‖(φ n) x‖ = ((fseq n x : ℝ≥0) : ℝ) := by
      simp [hφ, Complex.norm_real, abs_of_nonneg (hnonneg n x)]
    rw [hnorm]
    exact hbound n x
  have : ∫ x, F.indicator (fun _ => (1 : ℂ)) x * w x ∂mu = 0 := by
    refine tendsto_nhds_unique hlim ?_
    simp only [hzero]
    exact tendsto_const_nhds
  rw [← this, ← integral_indicator hF.measurableSet]
  refine integral_congr_ae (.of_forall fun x => ?_)
  by_cases hx : x ∈ F <;> simp [hx, Set.indicator_of_mem, Set.indicator_of_notMem]

end Beurling
