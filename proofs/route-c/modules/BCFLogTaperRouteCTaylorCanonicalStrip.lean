import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFiniteRemainder

/-!
# Route C: exceptional points in the canonical Taylor strip

The finite contour moves from `Re(s)=-1/2` to
`Re(s)=1/2-2M`.  This file proves that every zero of `sin(πs)` in that
closed strip is one of the negative odd/even points already equipped with a
local analytic replacement.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCanonicalStrip

open Complex Filter Set Topology
open scoped Interval Real BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorEvenRemovability
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFiniteRemainder
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift

noncomputable def routeCTaylorCanonicalLeft (M : ℕ) : ℝ :=
  1 / 2 - 2 * M

noncomputable def routeCTaylorCanonicalRight : ℝ :=
  -1 / 2

def routeCTaylorCanonicalClosedStrip (M : ℕ) : Set ℂ :=
  {s | routeCTaylorCanonicalLeft M ≤ s.re ∧
    s.re ≤ routeCTaylorCanonicalRight}

/-- The half-integer boundaries isolate exactly the first `2M-1` negative
integers.  Splitting their positive absolute values by parity identifies the
odd poles and even removable points. -/
theorem routeCTaylor_sine_zero_mem_exceptional
    (M : ℕ) (hM : 1 ≤ M) {s : ℂ}
    (hsStrip : s ∈ routeCTaylorCanonicalClosedStrip M)
    (hsin : Complex.sin ((Real.pi : ℂ) * s) = 0) :
    s ∈ routeCTaylorExceptionalPoints M := by
  rcases Complex.sin_eq_zero_iff.mp hsin with ⟨k, hk⟩
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsK : s = (k : ℂ) := by
    apply (mul_left_cancel₀ hpi)
    calc
      (Real.pi : ℂ) * s = (k : ℂ) * (Real.pi : ℂ) := hk
      _ = (Real.pi : ℂ) * (k : ℂ) := by ring
  have hkUpperR : (k : ℝ) < 0 := by
    have hu := hsStrip.2
    rw [hsK] at hu
    simp [routeCTaylorCanonicalRight] at hu
    linarith
  have hkUpper : k < 0 := by exact_mod_cast hkUpperR
  have hkLowerR : -(2 : ℝ) * M < (k : ℝ) := by
    have hl := hsStrip.1
    rw [hsK] at hl
    simp [routeCTaylorCanonicalLeft] at hl
    linarith
  have hkLower : -(2 : ℤ) * M < k := by exact_mod_cast hkLowerR
  let r : ℕ := (-k).toNat
  have hnegNonneg : 0 ≤ -k := by omega
  have hrInt : (r : ℤ) = -k := by
    simpa [r] using Int.toNat_of_nonneg hnegNonneg
  have hrComplex : (r : ℂ) = -(k : ℂ) := by exact_mod_cast hrInt
  have hrPos : 1 ≤ r := by omega
  have hrUpper : r ≤ 2 * M - 1 := by omega
  rcases Nat.even_or_odd' r with ⟨a, ha | ha⟩
  · have haPos : 1 ≤ a := by omega
    let j := a - 1
    have hj : j ∈ Finset.range M := by
      rw [Finset.mem_range]
      dsimp [j]
      omega
    have hpoint : routeCTaylorEvenPoint j = s := by
      rw [hsK]
      have hjSucc : j + 1 = a := by
        dsimp [j]
        omega
      unfold routeCTaylorEvenPoint
      rw [hjSucc]
      rw [ha] at hrComplex
      push_cast at hrComplex ⊢
      linear_combination -hrComplex
    rw [routeCTaylorExceptionalPoints, Finset.mem_union]
    exact Or.inr (by
      rw [routeCTaylorEvenExceptionalPoints, Finset.mem_image]
      exact ⟨j, hj, hpoint⟩)
  · let n := a + 1
    have hn : n ∈ Finset.Icc 1 M := by
      rw [Finset.mem_Icc]
      dsimp [n]
      omega
    have hpoint : routeCTaylorPolePoint n = s := by
      rw [hsK]
      unfold routeCTaylorPolePoint
      dsimp [n]
      rw [ha] at hrComplex
      push_cast at hrComplex ⊢
      linear_combination -hrComplex
    rw [routeCTaylorExceptionalPoints, Finset.mem_union]
    exact Or.inl (by
      rw [routeCTaylorOddExceptionalPoints, Finset.mem_image]
      exact ⟨n, hn, hpoint⟩)

/-- Away from `0`, `1`, and the sine lattice, the literal Mellin integrand
is analytic. -/
theorem analyticAt_bettinConreyGZeroMeromorphicIntegrand_of_regular
    (u : ℂ) (hu : u ≠ 0) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0) :
    AnalyticAt ℂ (bettinConreyGZeroMeromorphicIntegrand u) s := by
  have hleft : AnalyticAt ℂ riemannZeta s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [eventually_ne_nhds hs1] with z hz
    exact differentiableAt_riemannZeta hz
  have hright : AnalyticAt ℂ (fun z : ℂ => riemannZeta (1 - z)) s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [eventually_ne_nhds hs0] with z hz
    have harg : 1 - z ≠ 1 := by
      intro h
      apply hz
      linear_combination -h
    exact (differentiableAt_riemannZeta harg).comp z (by fun_prop)
  have hsine : AnalyticAt ℂ
      (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z)) s := by
    fun_prop
  have hpow : AnalyticAt ℂ (fun z : ℂ => u ^ (-z)) s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [] with z
    exact differentiableAt_id.neg.const_cpow (Or.inl hu)
  unfold bettinConreyGZeroMeromorphicIntegrand
  exact ((hleft.mul hright).div hsine hsin).mul hpow

/-- At a point outside the enumerated odd poles, the finite principal-part
sum is analytic. -/
theorem analyticAt_routeCTaylorOddPrincipalSum_of_notMem
    (u : ℂ) (M : ℕ) {s : ℂ}
    (hs : s ∉ routeCTaylorOddExceptionalPoints M) :
    AnalyticAt ℂ (routeCTaylorOddPrincipalSum u M) s := by
  have hsum := Finset.analyticAt_sum (𝕜 := ℂ)
    (f := fun n => routeCTaylorOddPrincipalTerm u n) (Finset.Icc 1 M)
    (fun n hn => by
      have hne : s ≠ routeCTaylorPolePoint n := by
        intro h
        apply hs
        rw [routeCTaylorOddExceptionalPoints, Finset.mem_image]
        exact ⟨n, hn, h.symm⟩
      unfold routeCTaylorOddPrincipalTerm
      exact analyticAt_const.mul
        ((analyticAt_id.sub analyticAt_const).inv
          (sub_ne_zero.mpr hne)))
  unfold routeCTaylorOddPrincipalSum
  apply hsum.congr
  filter_upwards [] with z
  simp

/-- The unpatched finite remainder is analytic at every regular point of the
canonical strip. -/
theorem analyticAt_routeCTaylorFiniteRemainder_on_canonicalStrip
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (hM : 1 ≤ M) {s : ℂ}
    (hsStrip : s ∈ routeCTaylorCanonicalClosedStrip M)
    (hsExc : s ∉ routeCTaylorExceptionalPoints M) :
    AnalyticAt ℂ (routeCTaylorFiniteRemainder u M) s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    have hu := hsStrip.2
    norm_num [routeCTaylorCanonicalRight] at hu
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    have hu := hsStrip.2
    norm_num [routeCTaylorCanonicalRight] at hu
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    intro h
    exact hsExc (routeCTaylor_sine_zero_mem_exceptional M hM hsStrip h)
  have hmain :=
    analyticAt_bettinConreyGZeroMeromorphicIntegrand_of_regular
      u hu hs0 hs1 hsin
  have hsOdd : s ∉ routeCTaylorOddExceptionalPoints M := by
    intro h
    apply hsExc
    rw [routeCTaylorExceptionalPoints, Finset.mem_union]
    exact Or.inl h
  have hprincipal :=
    analyticAt_routeCTaylorOddPrincipalSum_of_notMem u M hsOdd
  unfold routeCTaylorFiniteRemainder
  exact hmain.sub hprincipal

/-- The regular-point premise of the finite patcher is unconditional on the
canonical half-integer rectangle. -/
theorem rectangularBoundaryIntegral_routeCTaylorCanonicalPatched_eq_zero
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (hM : 1 ≤ M) (T : ℝ) :
    rectangularBoundaryIntegral
        (routeCTaylorPatchedFiniteRemainder u hu M)
        (symmetricLowerCorner (routeCTaylorCanonicalLeft M) T)
        (symmetricUpperCorner routeCTaylorCanonicalRight T) = 0 := by
  apply
    rectangularBoundaryIntegral_routeCTaylorPatchedFiniteRemainder_eq_zero
  intro z hzRect hzExc
  apply analyticAt_routeCTaylorFiniteRemainder_on_canonicalStrip
    u hu M hM _ hzExc
  have hLR : routeCTaylorCanonicalLeft M ≤
      routeCTaylorCanonicalRight := by
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    unfold routeCTaylorCanonicalLeft routeCTaylorCanonicalRight
    linarith
  have hzRe := hzRect.1
  rw [uIcc_of_le hLR] at hzRe
  exact hzRe

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCanonicalStrip
