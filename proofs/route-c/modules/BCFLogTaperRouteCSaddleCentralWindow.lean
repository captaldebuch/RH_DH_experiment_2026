import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegrability
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Route C: central-window decomposition for the saddle integral

Bettin--Conrey first write `u = n(1+w)` and restrict to a fixed window
`|w| <= delta`.  This file formalizes that near/far split exactly and proves
the two local expansions used after the substitution:

* `log (1+w) - (1+w) = -1 - w^2/2 + O(|w|^3/(1-|w|))`;
* `sqrt (1+w) = 1 + w/2 + O(w^2)`.

No asymptotic notation or unproved analytic package occurs here.  The next
quantitative step is to show that the far integral is exponentially small and
then rescale the near integral by `w = t/sqrt n`.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow

open MeasureTheory Set
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegral
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleIntegrability

/-- The integrand in the Bettin--Conrey saddle integral. -/
noncomputable def routeCSaddleIntegrand
    (A : ℂ) (alpha : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  ((Real.rpow u ((n : ℝ) + alpha - 1) * Real.exp (-u) : ℝ) : ℂ) *
    Complex.exp (-A * (Real.sqrt u : ℂ))

theorem routeCSaddleIntegral_eq_integral_integrand
    (A : ℂ) (alpha : ℝ) (n : ℕ) :
    routeCSaddleIntegral A alpha n =
      ∫ u : ℝ in Ioi 0, routeCSaddleIntegrand A alpha n u := by
  rfl

/-- The fixed relative saddle window `u in n*[1-delta,1+delta]`, intersected
with the positive half-line. -/
def routeCSaddleNearSet (delta : ℝ) (n : ℕ) : Set ℝ :=
  Ioi 0 ∩
    Icc ((1 - delta) * (n : ℝ)) ((1 + delta) * (n : ℝ))

/-- The complementary positive-half-line sector. -/
def routeCSaddleFarSet (delta : ℝ) (n : ℕ) : Set ℝ :=
  Ioi 0 \ routeCSaddleNearSet delta n

theorem measurableSet_routeCSaddleNearSet (delta : ℝ) (n : ℕ) :
    MeasurableSet (routeCSaddleNearSet delta n) :=
  measurableSet_Ioi.inter measurableSet_Icc

theorem measurableSet_routeCSaddleFarSet (delta : ℝ) (n : ℕ) :
    MeasurableSet (routeCSaddleFarSet delta n) :=
  measurableSet_Ioi.diff (measurableSet_routeCSaddleNearSet delta n)

theorem routeCSaddleNearSet_subset_Ioi (delta : ℝ) (n : ℕ) :
    routeCSaddleNearSet delta n ⊆ Ioi 0 := by
  intro u hu
  exact hu.1

theorem routeCSaddleFarSet_subset_Ioi (delta : ℝ) (n : ℕ) :
    routeCSaddleFarSet delta n ⊆ Ioi 0 := by
  intro u hu
  exact hu.1

theorem routeCSaddleNearSet_disjoint_farSet (delta : ℝ) (n : ℕ) :
    Disjoint (routeCSaddleNearSet delta n) (routeCSaddleFarSet delta n) := by
  rw [Set.disjoint_left]
  intro u hnear hfar
  exact hfar.2 hnear

theorem routeCSaddleNearSet_union_farSet (delta : ℝ) (n : ℕ) :
    routeCSaddleNearSet delta n ∪ routeCSaddleFarSet delta n = Ioi 0 := by
  apply Set.Subset.antisymm
  · intro u hu
    rcases hu with hnear | hfar
    · exact hnear.1
    · exact hfar.1
  · intro u hu
    by_cases hnear : u ∈ routeCSaddleNearSet delta n
    · exact Or.inl hnear
    · exact Or.inr ⟨hu, hnear⟩

/-- The contribution of the fixed central window. -/
noncomputable def routeCSaddleNearIntegral
    (A : ℂ) (alpha delta : ℝ) (n : ℕ) : ℂ :=
  ∫ u : ℝ in routeCSaddleNearSet delta n,
    routeCSaddleIntegrand A alpha n u

/-- The contribution outside the fixed central window. -/
noncomputable def routeCSaddleFarIntegral
    (A : ℂ) (alpha delta : ℝ) (n : ℕ) : ℂ :=
  ∫ u : ℝ in routeCSaddleFarSet delta n,
    routeCSaddleIntegrand A alpha n u

/-- Exact near/far decomposition of the saddle integral. -/
theorem routeCSaddleIntegral_eq_near_add_far
    (A : ℂ) (alpha delta : ℝ) (n : ℕ)
    (hpos : 0 < (n : ℝ) + alpha) :
    routeCSaddleIntegral A alpha n =
      routeCSaddleNearIntegral A alpha delta n +
        routeCSaddleFarIntegral A alpha delta n := by
  rw [routeCSaddleIntegral_eq_integral_integrand]
  have hglobal : IntegrableOn (routeCSaddleIntegrand A alpha n) (Ioi 0) :=
    integrableOn_routeCSaddleIntegrand A alpha n hpos
  have hnear : IntegrableOn (routeCSaddleIntegrand A alpha n)
      (routeCSaddleNearSet delta n) :=
    hglobal.mono_set (routeCSaddleNearSet_subset_Ioi delta n)
  have hfar : IntegrableOn (routeCSaddleIntegrand A alpha n)
      (routeCSaddleFarSet delta n) :=
    hglobal.mono_set (routeCSaddleFarSet_subset_Ioi delta n)
  rw [← routeCSaddleNearSet_union_farSet delta n,
    setIntegral_union (routeCSaddleNearSet_disjoint_farSet delta n)
      (measurableSet_routeCSaddleFarSet delta n) hnear hfar]
  rfl

/-- The entropy phase after `u = n(1+w)`. -/
noncomputable def routeCSaddleEntropy (w : ℝ) : ℝ :=
  Real.log (1 + w) - (1 + w)

/-- Exact quantitative form of the local entropy expansion used in Lemma 3. -/
theorem abs_routeCSaddleEntropy_add_one_add_half_sq_le
    {w : ℝ} (hw : |w| < 1) :
    |routeCSaddleEntropy w + 1 + w ^ 2 / 2| ≤
      |w| ^ 3 / (1 - |w|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -w) (by simpa) 2
  norm_num [Finset.sum_range_succ] at h
  calc
    |routeCSaddleEntropy w + 1 + w ^ 2 / 2| =
        |-w + w ^ 2 / 2 + Real.log (1 + w)| := by
      congr 1
      rw [routeCSaddleEntropy]
      ring
    _ ≤ |w| ^ 3 / (1 - |w|) := h

/-- An exact rational identity for the first-order square-root remainder. -/
theorem sqrt_one_add_sub_one_sub_half
    {w : ℝ} (hw : -1 < w) :
    Real.sqrt (1 + w) - 1 - w / 2 =
      -(w ^ 2) / (2 * (Real.sqrt (1 + w) + 1) ^ 2) := by
  have harg : 0 ≤ 1 + w := by linarith
  have hsquare : (Real.sqrt (1 + w)) ^ 2 = 1 + w :=
    Real.sq_sqrt harg
  have hden : Real.sqrt (1 + w) + 1 ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The square-root perturbation has a uniform quadratic remainder throughout
the admissible relative window. -/
theorem abs_sqrt_one_add_sub_one_sub_half_le
    {w : ℝ} (hw : -1 < w) :
    |Real.sqrt (1 + w) - 1 - w / 2| ≤ w ^ 2 / 2 := by
  rw [sqrt_one_add_sub_one_sub_half hw]
  rw [abs_div, abs_neg, abs_pow, sq_abs,
    abs_of_pos (by positivity : 0 < 2 * (Real.sqrt (1 + w) + 1) ^ 2)]
  have hden : 1 ≤ Real.sqrt (1 + w) + 1 := by
    linarith [Real.sqrt_nonneg (1 + w)]
  gcongr
  nlinarith [sq_nonneg (Real.sqrt (1 + w))]

/-- The remaining quantitative stop target at this layer: after the natural
saddle normalization, the far sector must vanish for every fixed
`0 < delta < 1`.  This is a definition, not an asserted theorem. -/
def RouteCSaddleFarTailTarget (A : ℂ) (alpha delta : ℝ) : Prop :=
  0 < delta ∧ delta < 1 ∧
    Filter.Tendsto
      (fun n : ℕ =>
        routeCSaddleFarIntegral A alpha delta n /
          ((Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (A ^ 2 / 8) *
            Complex.exp (-A * (Real.sqrt n : ℂ)) *
            Complex.exp (-(n : ℝ)) *
            ((Real.rpow n ((n : ℝ) + alpha - 1 / 2) : ℝ) : ℂ)))
      Filter.atTop (nhds 0)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow
