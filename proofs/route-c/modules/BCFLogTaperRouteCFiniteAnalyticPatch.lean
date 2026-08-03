import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# A finite analytic patch for removable singularities

This module packages the sheaf-like gluing step needed by the Route C
finite contour shift.  If a function is analytic away from a finite set and
has a specified analytic replacement near every exceptional point, changing
only its values at those points produces one function analytic on the whole
region.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCFiniteAnalyticPatch

open Complex Filter Set Topology

/-- Local analytic data which fills one puncture of `f`. -/
structure LocalAnalyticReplacement (f : ℂ → ℂ) (p : ℂ) where
  replacement : ℂ → ℂ
  analyticAt_replacement : AnalyticAt ℂ replacement p
  agrees_punctured : f =ᶠ[𝓝[≠] p] replacement

/-- Replace the value at each point of a finite exceptional set by the value
of its chosen local analytic continuation. -/
noncomputable def finiteAnalyticPatch
    (f : ℂ → ℂ) (S : Finset ℂ)
    (repl : ∀ p : ℂ, p ∈ S → LocalAnalyticReplacement f p) : ℂ → ℂ :=
  fun z => if hz : z ∈ S then (repl z hz).replacement z else f z

theorem finiteAnalyticPatch_of_notMem
    (f : ℂ → ℂ) (S : Finset ℂ)
    (repl : ∀ p : ℂ, p ∈ S → LocalAnalyticReplacement f p)
    {z : ℂ} (hz : z ∉ S) :
    finiteAnalyticPatch f S repl z = f z := by
  simp [finiteAnalyticPatch, hz]

theorem finiteAnalyticPatch_of_mem
    (f : ℂ → ℂ) (S : Finset ℂ)
    (repl : ∀ p : ℂ, p ∈ S → LocalAnalyticReplacement f p)
    {z : ℂ} (hz : z ∈ S) :
    finiteAnalyticPatch f S repl z = (repl z hz).replacement z := by
  simp [finiteAnalyticPatch, hz]

/-- At an exceptional point, the finite patch agrees in a full neighborhood
with the corresponding local analytic replacement. -/
theorem finiteAnalyticPatch_eventuallyEq_local
    (f : ℂ → ℂ) (S : Finset ℂ)
    (repl : ∀ p : ℂ, p ∈ S → LocalAnalyticReplacement f p)
    {p : ℂ} (hp : p ∈ S) :
    finiteAnalyticPatch f S repl =ᶠ[𝓝 p]
      (repl p hp).replacement := by
  have hagree := (repl p hp).agrees_punctured
  change {z | f z = (repl p hp).replacement z} ∈ 𝓝[≠] p at hagree
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hagree
  rcases hagree with ⟨V, hV, hVsub⟩
  have hAvoid : ((S.erase p : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 p :=
    (S.erase p).isClosed.compl_mem_nhds (by simp)
  filter_upwards [hV, hAvoid] with z hzV hzAvoid
  by_cases hzp : z = p
  · subst z
    simpa [finiteAnalyticPatch, hp]
  · have hzS : z ∉ S := by
      intro hzS
      exact hzAvoid (Finset.mem_erase.mpr ⟨hzp, hzS⟩)
    rw [finiteAnalyticPatch_of_notMem f S repl hzS]
    exact hVsub ⟨hzV, by simpa⟩

/-- Away from the exceptional set, the finite patch agrees with the original
function in a full neighborhood. -/
theorem finiteAnalyticPatch_eventuallyEq_of_notMem
    (f : ℂ → ℂ) (S : Finset ℂ)
    (repl : ∀ p : ℂ, p ∈ S → LocalAnalyticReplacement f p)
    {z : ℂ} (hz : z ∉ S) :
    finiteAnalyticPatch f S repl =ᶠ[𝓝 z] f := by
  have hAvoid : ((S : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 z :=
    S.isClosed.compl_mem_nhds hz
  filter_upwards [hAvoid] with w hw
  exact finiteAnalyticPatch_of_notMem f S repl hw

/-- The patched function is analytic at every point of a region on which
the original function is analytic away from the finite exceptional set. -/
theorem analyticAt_finiteAnalyticPatch
    (f : ℂ → ℂ) (S : Finset ℂ)
    (repl : ∀ p : ℂ, p ∈ S → LocalAnalyticReplacement f p)
    (U : Set ℂ)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z)
    {z : ℂ} (hzU : z ∈ U) :
    AnalyticAt ℂ (finiteAnalyticPatch f S repl) z := by
  by_cases hzS : z ∈ S
  · exact (repl z hzS).analyticAt_replacement.congr
      (finiteAnalyticPatch_eventuallyEq_local f S repl hzS).symm
  · exact (hoff z hzU hzS).congr
      (finiteAnalyticPatch_eventuallyEq_of_notMem f S repl hzS).symm

/-- Region-level differentiability of the finite analytic patch. -/
theorem differentiableOn_finiteAnalyticPatch
    (f : ℂ → ℂ) (S : Finset ℂ)
    (repl : ∀ p : ℂ, p ∈ S → LocalAnalyticReplacement f p)
    (U : Set ℂ)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z) :
    DifferentiableOn ℂ (finiteAnalyticPatch f S repl) U := by
  intro z hz
  exact (analyticAt_finiteAnalyticPatch f S repl U hoff hz).differentiableAt
    |>.differentiableWithinAt

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCFiniteAnalyticPatch
