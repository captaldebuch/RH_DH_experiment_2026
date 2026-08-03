import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Route C: entropy gap outside the saddle window

For `v > 0`, the real saddle rate

`Phi(v) = log v - v + 1`

has its unique maximum `0` at `v = 1`.  This file proves, without asymptotic
notation, that outside the fixed window `[1-delta, 1+delta]` the rate is at
most `-c_delta` for an explicit positive constant `c_delta`.  Consequently
the principal exponential factor is bounded by `exp (-n*c_delta)` throughout
the far sector.

This is the real-variable localization input in Bettin--Conrey Lemma 3.  It
does not yet integrate the polynomial and complex square-root perturbations;
that weighted tail estimate is the next step.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarEntropy

open Set
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleCentralWindow

/-- The saddle rate, normalized to vanish at its maximum `v = 1`. -/
noncomputable def routeCSaddleRate (v : ℝ) : ℝ :=
  Real.log v - v + 1

theorem hasDerivAt_routeCSaddleRate {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt routeCSaddleRate (v⁻¹ - 1) v := by
  change HasDerivAt (fun x => Real.log x - x + 1) (v⁻¹ - 1) v
  convert ((Real.hasDerivAt_log hv).sub (hasDerivAt_id v)).const_add 1 using 1
  funext x
  simp only [Pi.sub_apply, id_eq]
  ring

theorem routeCSaddleRate_monotoneOn_left :
    MonotoneOn routeCSaddleRate (Ioc 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 1)
  · simpa [routeCSaddleRate] using
      ((Real.continuousOn_log.mono fun x hx => ne_of_gt hx.1).sub
        continuousOn_id).add continuousOn_const
  · intro x hx
    have hx' : x ∈ Ioc (0 : ℝ) 1 := interior_subset hx
    exact (hasDerivAt_routeCSaddleRate (ne_of_gt hx'.1)).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Ioc (0 : ℝ) 1 := interior_subset hx
    rw [sub_nonneg]
    exact (one_le_inv₀ hx'.1).2 hx'.2

theorem routeCSaddleRate_antitoneOn_right :
    AntitoneOn routeCSaddleRate (Ici 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1)
  · simpa [routeCSaddleRate] using
      ((Real.continuousOn_log.mono fun x hx => by
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx)).sub continuousOn_id).add
          continuousOn_const
  · intro x hx
    have hx' : x ∈ Ici (1 : ℝ) := interior_subset hx
    exact (hasDerivAt_routeCSaddleRate
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hx'))).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Ici (1 : ℝ) := interior_subset hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx'
    rw [sub_nonpos]
    exact (inv_le_one₀ hxpos).2 hx'

/-- Explicit entropy loss outside a relative window. -/
noncomputable def routeCSaddleEntropyGap (delta : ℝ) : ℝ :=
  min (-(routeCSaddleRate (1 - delta)))
    (-(routeCSaddleRate (1 + delta)))

theorem routeCSaddleEntropyGap_pos
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1) :
    0 < routeCSaddleEntropyGap delta := by
  rw [routeCSaddleEntropyGap, lt_min_iff]
  constructor
  · have hp : 0 < 1 - delta := by linarith
    have hne : 1 - delta ≠ 1 := by linarith
    have h := Real.log_lt_sub_one_of_pos hp hne
    simp only [routeCSaddleRate]
    linarith
  · have hp : 0 < 1 + delta := by linarith
    have hne : 1 + delta ≠ 1 := by linarith
    have h := Real.log_lt_sub_one_of_pos hp hne
    simp only [routeCSaddleRate]
    linarith

/-- Uniform negative rate outside the fixed saddle window. -/
theorem routeCSaddleRate_le_neg_entropyGap
    {delta v : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1)
    (hv : 0 < v) (hfar : v ≤ 1 - delta ∨ 1 + delta ≤ v) :
    routeCSaddleRate v ≤ -(routeCSaddleEntropyGap delta) := by
  rcases hfar with hleft | hright
  · have hv_mem : v ∈ Ioc (0 : ℝ) 1 :=
      ⟨hv, hleft.trans (by linarith)⟩
    have hend_mem : 1 - delta ∈ Ioc (0 : ℝ) 1 := by
      constructor <;> linarith
    calc
      routeCSaddleRate v ≤ routeCSaddleRate (1 - delta) :=
        routeCSaddleRate_monotoneOn_left hv_mem hend_mem hleft
      _ = -(-(routeCSaddleRate (1 - delta))) := by ring
      _ ≤ -(routeCSaddleEntropyGap delta) :=
        neg_le_neg (min_le_left _ _)
  · have hstart_mem : 1 + delta ∈ Ici (1 : ℝ) := by
      simp only [mem_Ici]
      linarith
    have hv_mem : v ∈ Ici (1 : ℝ) := hstart_mem.trans hright
    calc
      routeCSaddleRate v ≤ routeCSaddleRate (1 + delta) :=
        routeCSaddleRate_antitoneOn_right hstart_mem hv_mem hright
      _ = -(-(routeCSaddleRate (1 + delta))) := by ring
      _ ≤ -(routeCSaddleEntropyGap delta) :=
        neg_le_neg (min_le_right _ _)

theorem routeCSaddleRate_one_add (w : ℝ) :
    routeCSaddleRate (1 + w) = routeCSaddleEntropy w + 1 := by
  rw [routeCSaddleRate, routeCSaddleEntropy]

/-- Membership in the original `u`-variable far set becomes the expected
alternative after division by the positive saddle location `n`. -/
theorem div_natCast_mem_far_alternative
    {delta u : ℝ} {n : ℕ} (hn : 0 < n)
    (hu : u ∈ routeCSaddleFarSet delta n) :
    u / (n : ℝ) ≤ 1 - delta ∨ 1 + delta ≤ u / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  by_cases hleft : u / (n : ℝ) ≤ 1 - delta
  · exact Or.inl hleft
  · right
    by_contra hright
    have hleft' : 1 - delta < u / (n : ℝ) := lt_of_not_ge hleft
    have hright' : u / (n : ℝ) < 1 + delta := lt_of_not_ge hright
    apply hu.2
    constructor
    · exact hu.1
    · constructor
      · exact le_of_lt ((lt_div_iff₀ hnR).mp hleft')
      · exact le_of_lt ((div_lt_iff₀ hnR).mp hright')

theorem routeCSaddleFar_rate_le_neg_entropyGap
    {delta u : ℝ} {n : ℕ} (hn : 0 < n)
    (hd0 : 0 < delta) (hd1 : delta < 1)
    (hu : u ∈ routeCSaddleFarSet delta n) :
    routeCSaddleRate (u / (n : ℝ)) ≤
      -(routeCSaddleEntropyGap delta) := by
  apply routeCSaddleRate_le_neg_entropyGap hd0 hd1
  · exact div_pos hu.1 (by exact_mod_cast hn)
  · exact div_natCast_mem_far_alternative hn hu

/-- Exponential suppression of the principal rate throughout the far sector. -/
theorem exp_natCast_mul_routeCSaddleFar_rate_le
    {delta u : ℝ} {n : ℕ} (hn : 0 < n)
    (hd0 : 0 < delta) (hd1 : delta < 1)
    (hu : u ∈ routeCSaddleFarSet delta n) :
    Real.exp ((n : ℝ) * routeCSaddleRate (u / (n : ℝ))) ≤
      Real.exp (-((n : ℝ) * routeCSaddleEntropyGap delta)) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left
    (routeCSaddleFar_rate_le_neg_entropyGap hn hd0 hd1 hu)
    (Nat.cast_nonneg n)
  nlinarith

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCSaddleFarEntropy
