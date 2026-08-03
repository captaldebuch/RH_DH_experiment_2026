import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorEvenRemovability
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCFiniteAnalyticPatch
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFinitePoleGeometry

/-!
# Route C: the finite pole-subtracted Taylor remainder

The genuine meromorphic integrand is centered by subtracting the first `M`
negative odd principal parts.  This file constructs a local analytic
replacement at every negative odd pole and every intervening negative even
point, then packages the choices for the generic finite analytic patcher.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFiniteRemainder

open Complex Filter Set Topology
open scoped Interval Real BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorLocalSubtraction
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorEvenRemovability
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCFiniteAnalyticPatch
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift

noncomputable def routeCTaylorOddPrincipalTerm
    (u : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  bettinConreyGZeroOddResidue u n *
    (s - routeCTaylorPolePoint n)⁻¹

noncomputable def routeCTaylorOddPrincipalSum
    (u : ℂ) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M, routeCTaylorOddPrincipalTerm u n s

/-- The literal integrand after subtracting the first `M` odd principal
parts.  Its values at the exceptional points will subsequently be patched. -/
noncomputable def routeCTaylorFiniteRemainder
    (u : ℂ) (M : ℕ) (s : ℂ) : ℂ :=
  bettinConreyGZeroMeromorphicIntegrand u s -
    routeCTaylorOddPrincipalSum u M s

noncomputable def routeCTaylorOddExceptionalPoints (M : ℕ) : Finset ℂ :=
  (Finset.Icc 1 M).image routeCTaylorPolePoint

noncomputable def routeCTaylorEvenExceptionalPoints (M : ℕ) : Finset ℂ :=
  (Finset.range M).image routeCTaylorEvenPoint

noncomputable def routeCTaylorExceptionalPoints (M : ℕ) : Finset ℂ :=
  routeCTaylorOddExceptionalPoints M ∪
    routeCTaylorEvenExceptionalPoints M

theorem routeCTaylorPolePoint_injective :
    Function.Injective routeCTaylorPolePoint := by
  intro n m h
  have hcast : (n : ℂ) = (m : ℂ) := by
    unfold routeCTaylorPolePoint at h
    linear_combination -h / 2
  exact_mod_cast hcast

theorem routeCTaylorEvenPoint_ne_routeCTaylorPolePoint
    (j n : ℕ) :
    routeCTaylorEvenPoint j ≠ routeCTaylorPolePoint n := by
  intro h
  have hre : -(2 : ℝ) * ((j + 1 : ℕ) : ℝ) =
      1 - 2 * (n : ℝ) := by
    simpa [routeCTaylorEvenPoint, routeCTaylorPolePoint] using
      congrArg Complex.re h
  have hint : -(2 : ℤ) * (j + 1) = 1 - 2 * n := by
    exact_mod_cast hre
  omega

theorem analyticAt_routeCTaylorOddPrincipalTerm_of_ne
    (u : ℂ) {n m : ℕ} (hnm : n ≠ m) :
    AnalyticAt ℂ (routeCTaylorOddPrincipalTerm u m)
      (routeCTaylorPolePoint n) := by
  have hp : routeCTaylorPolePoint n - routeCTaylorPolePoint m ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hnm (routeCTaylorPolePoint_injective h)
  unfold routeCTaylorOddPrincipalTerm
  exact analyticAt_const.mul
    ((analyticAt_id.sub analyticAt_const).inv hp)

theorem analyticAt_routeCTaylorOddPrincipalTerm_even
    (u : ℂ) (j m : ℕ) :
    AnalyticAt ℂ (routeCTaylorOddPrincipalTerm u m)
      (routeCTaylorEvenPoint j) := by
  have hp : routeCTaylorEvenPoint j - routeCTaylorPolePoint m ≠ 0 :=
    sub_ne_zero.mpr (routeCTaylorEvenPoint_ne_routeCTaylorPolePoint j m)
  unfold routeCTaylorOddPrincipalTerm
  exact analyticAt_const.mul
    ((analyticAt_id.sub analyticAt_const).inv hp)

/-- Local analytic remainder at one of the crossed negative odd poles. -/
noncomputable def routeCTaylorFiniteRemainderOddLocal
    (u : ℂ) (hu : u ≠ 0) (M n : ℕ)
    (hn : n ∈ Finset.Icc 1 M) :
    LocalAnalyticReplacement (routeCTaylorFiniteRemainder u M)
      (routeCTaylorPolePoint n) := by
  let P := routeCTaylorOddPoleSubtraction u hu n (Finset.mem_Icc.mp hn).1
  let R : ℂ → ℂ := fun s =>
    P.regularized s -
      ∑ m ∈ (Finset.Icc 1 M).erase n,
        routeCTaylorOddPrincipalTerm u m s
  have hsum : AnalyticAt ℂ
      (fun s : ℂ => ∑ m ∈ (Finset.Icc 1 M).erase n,
        routeCTaylorOddPrincipalTerm u m s)
      (routeCTaylorPolePoint n) := by
    have h := Finset.analyticAt_sum (𝕜 := ℂ)
      ((Finset.Icc 1 M).erase n)
      (fun m hm => analyticAt_routeCTaylorOddPrincipalTerm_of_ne u
        (Finset.mem_erase.mp hm).1.symm)
    apply h.congr
    filter_upwards [] with s
    simp
  have hR : AnalyticAt ℂ R (routeCTaylorPolePoint n) :=
    P.analyticAt_regularized.sub hsum
  refine {
    replacement := R
    analyticAt_replacement := hR
    agrees_punctured := ?_ }
  filter_upwards [P.decomposition] with s hs
  have hsplit := Finset.sum_erase_add (Finset.Icc 1 M)
    (fun m => routeCTaylorOddPrincipalTerm u m s) hn
  change bettinConreyGZeroMeromorphicIntegrand u s =
    P.regularized s + routeCTaylorOddPrincipalTerm u n s at hs
  unfold routeCTaylorFiniteRemainder routeCTaylorOddPrincipalSum R
  rw [hs]
  rw [← hsplit]
  ring

/-- Local analytic remainder at one intervening negative even point. -/
noncomputable def routeCTaylorFiniteRemainderEvenLocal
    (u : ℂ) (hu : u ≠ 0) (M j : ℕ) :
    LocalAnalyticReplacement (routeCTaylorFiniteRemainder u M)
      (routeCTaylorEvenPoint j) := by
  let E := routeCTaylorEvenRemovableExtension u hu j
  let R : ℂ → ℂ := fun s =>
    E.regularized s - routeCTaylorOddPrincipalSum u M s
  have hsum : AnalyticAt ℂ (routeCTaylorOddPrincipalSum u M)
      (routeCTaylorEvenPoint j) := by
    unfold routeCTaylorOddPrincipalSum
    have h := Finset.analyticAt_sum (𝕜 := ℂ) (Finset.Icc 1 M)
      (fun m _hm => analyticAt_routeCTaylorOddPrincipalTerm_even u j m)
    apply h.congr
    filter_upwards [] with s
    simp
  have hR : AnalyticAt ℂ R (routeCTaylorEvenPoint j) :=
    E.analyticAt_regularized.sub hsum
  refine {
    replacement := R
    analyticAt_replacement := hR
    agrees_punctured := ?_ }
  filter_upwards [E.agrees_punctured] with s hs
  unfold routeCTaylorFiniteRemainder R
  rw [hs]

/-- Every point in the finite exceptional set has a genuine analytic local
replacement for the pole-subtracted remainder. -/
theorem exists_routeCTaylorFiniteRemainder_localReplacement
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (p : ℂ)
    (hp : p ∈ routeCTaylorExceptionalPoints M) :
    Nonempty (LocalAnalyticReplacement
      (routeCTaylorFiniteRemainder u M) p) := by
  rw [routeCTaylorExceptionalPoints, Finset.mem_union] at hp
  rcases hp with hpOdd | hpEven
  · rw [routeCTaylorOddExceptionalPoints, Finset.mem_image] at hpOdd
    rcases hpOdd with ⟨n, hn, rfl⟩
    exact ⟨routeCTaylorFiniteRemainderOddLocal u hu M n hn⟩
  · rw [routeCTaylorEvenExceptionalPoints, Finset.mem_image] at hpEven
    rcases hpEven with ⟨j, hj, rfl⟩
    exact ⟨routeCTaylorFiniteRemainderEvenLocal u hu M j⟩

/-- Canonical local data used by `finiteAnalyticPatch`. -/
noncomputable def routeCTaylorFiniteRemainderLocalData
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) :
    ∀ p : ℂ, p ∈ routeCTaylorExceptionalPoints M →
      LocalAnalyticReplacement (routeCTaylorFiniteRemainder u M) p :=
  fun p hp => Classical.choice
    (show Nonempty (LocalAnalyticReplacement
      (routeCTaylorFiniteRemainder u M) p) from
        exists_routeCTaylorFiniteRemainder_localReplacement u hu M p hp)

/-- The globally patched finite remainder. -/
noncomputable def routeCTaylorPatchedFiniteRemainder
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) : ℂ → ℂ :=
  finiteAnalyticPatch (routeCTaylorFiniteRemainder u M)
    (routeCTaylorExceptionalPoints M)
    (routeCTaylorFiniteRemainderLocalData u hu M)

/-- Once regular points of a region are known to be analytic, the local odd
and even constructions assemble into differentiability on the whole region. -/
theorem differentiableOn_routeCTaylorPatchedFiniteRemainder
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (U : Set ℂ)
    (hoff : ∀ z ∈ U, z ∉ routeCTaylorExceptionalPoints M →
      AnalyticAt ℂ (routeCTaylorFiniteRemainder u M) z) :
    DifferentiableOn ℂ
      (routeCTaylorPatchedFiniteRemainder u hu M) U := by
  exact differentiableOn_finiteAnalyticPatch
    (routeCTaylorFiniteRemainder u M)
    (routeCTaylorExceptionalPoints M)
    (routeCTaylorFiniteRemainderLocalData u hu M) U hoff

/-- Cauchy--Goursat for the fully patched finite remainder.  All residue
geometry has disappeared into the explicit finite principal-part sum. -/
theorem rectangularBoundaryIntegral_routeCTaylorPatchedFiniteRemainder_eq_zero
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (σL σR T : ℝ)
    (hoff : ∀ z ∈
        ([[σL, σR]] ×ℂ [[-T, T]]),
      z ∉ routeCTaylorExceptionalPoints M →
        AnalyticAt ℂ (routeCTaylorFiniteRemainder u M) z) :
    rectangularBoundaryIntegral
        (routeCTaylorPatchedFiniteRemainder u hu M)
        (symmetricLowerCorner σL T)
        (symmetricUpperCorner σR T) = 0 := by
  apply rectangularBoundaryIntegral_eq_zero
  simpa [symmetricLowerCorner, symmetricUpperCorner,
    Complex.mul_re, Complex.mul_im] using
    differentiableOn_routeCTaylorPatchedFiniteRemainder
      u hu M ([[σL, σR]] ×ℂ [[-T, T]]) hoff

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFiniteRemainder
