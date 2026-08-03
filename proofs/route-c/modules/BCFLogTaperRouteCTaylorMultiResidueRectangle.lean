import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCanonicalStrip

/-!
# Route C: the complete finite multi-residue rectangle identity

The analytic remainder has already been patched and shown to have zero
boundary integral on the canonical rectangle.  Here we prove that no patch
point lies on its four edges, replace the patched function by the literal
finite remainder there, and add back the exact finite principal-part sum.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorMultiResidueRectangle

open Complex Filter Set Topology
open scoped Interval Real BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannContourShift
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannTwoPoleRectangle
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFinitePoleGeometry
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCFiniteAnalyticPatch
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorResidues
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorEvenRemovability
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFiniteRemainder
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCanonicalStrip

/-- Every exceptional point is a real integer. -/
theorem routeCTaylorExceptionalPoints_exists_intCast
    {M : ℕ} {p : ℂ} (hp : p ∈ routeCTaylorExceptionalPoints M) :
    ∃ k : ℤ, p = (k : ℂ) := by
  rw [routeCTaylorExceptionalPoints, Finset.mem_union] at hp
  rcases hp with hpOdd | hpEven
  · rw [routeCTaylorOddExceptionalPoints, Finset.mem_image] at hpOdd
    rcases hpOdd with ⟨n, _hn, rfl⟩
    refine ⟨1 - 2 * (n : ℤ), ?_⟩
    unfold routeCTaylorPolePoint
    push_cast
    ring
  · rw [routeCTaylorEvenExceptionalPoints, Finset.mem_image] at hpEven
    rcases hpEven with ⟨j, _hj, rfl⟩
    refine ⟨-2 * ((j : ℤ) + 1), ?_⟩
    unfold routeCTaylorEvenPoint
    push_cast
    ring

theorem routeCTaylorCanonicalLeft_ne_intCast (M : ℕ) (k : ℤ) :
    (routeCTaylorCanonicalLeft M : ℂ) ≠ (k : ℂ) := by
  intro h
  have hre : routeCTaylorCanonicalLeft M = (k : ℝ) := by
    simpa using congrArg Complex.re h
  have hreal : (1 : ℝ) = 4 * M + 2 * k := by
    unfold routeCTaylorCanonicalLeft at hre
    linarith
  have hint : (1 : ℤ) = 4 * M + 2 * k := by exact_mod_cast hreal
  omega

theorem routeCTaylorCanonicalRight_ne_intCast (k : ℤ) :
    (routeCTaylorCanonicalRight : ℂ) ≠ (k : ℂ) := by
  intro h
  have hre : routeCTaylorCanonicalRight = (k : ℝ) := by
    simpa using congrArg Complex.re h
  have hreal : (1 : ℝ) = -2 * k := by
    unfold routeCTaylorCanonicalRight at hre
    linarith
  have hint : (1 : ℤ) = -2 * k := by exact_mod_cast hreal
  omega

theorem routeCTaylor_lower_horizontal_not_exceptional
    (M : ℕ) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    (x : ℂ) - (T : ℂ) * I ∉ routeCTaylorExceptionalPoints M := by
  intro hp
  rcases routeCTaylorExceptionalPoints_exists_intCast hp with ⟨k, hk⟩
  have him := congrArg Complex.im hk
  simp at him
  linarith

theorem routeCTaylor_upper_horizontal_not_exceptional
    (M : ℕ) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    (x : ℂ) + (T : ℂ) * I ∉ routeCTaylorExceptionalPoints M := by
  intro hp
  rcases routeCTaylorExceptionalPoints_exists_intCast hp with ⟨k, hk⟩
  have him := congrArg Complex.im hk
  simp at him
  linarith

theorem routeCTaylor_left_vertical_not_exceptional
    (M : ℕ) (y : ℝ) :
    (routeCTaylorCanonicalLeft M : ℂ) + (y : ℂ) * I ∉
      routeCTaylorExceptionalPoints M := by
  intro hp
  rcases routeCTaylorExceptionalPoints_exists_intCast hp with ⟨k, hk⟩
  apply routeCTaylorCanonicalLeft_ne_intCast M k
  apply Complex.ext
  · simpa using congrArg Complex.re hk
  · simp

theorem routeCTaylor_right_vertical_not_exceptional
    (M : ℕ) (y : ℝ) :
    (routeCTaylorCanonicalRight : ℂ) + (y : ℂ) * I ∉
      routeCTaylorExceptionalPoints M := by
  intro hp
  rcases routeCTaylorExceptionalPoints_exists_intCast hp with ⟨k, hk⟩
  apply routeCTaylorCanonicalRight_ne_intCast k
  apply Complex.ext
  · simpa using congrArg Complex.re hk
  · simp

/-- Congruence of the four parametrized edges. -/
theorem rectangularBoundaryIntegral_congr_symmetric
    (f g : ℂ → ℂ) (σL σR T : ℝ)
    (hminus : ∀ x : ℝ,
      f ((x : ℂ) - (T : ℂ) * I) =
        g ((x : ℂ) - (T : ℂ) * I))
    (hplus : ∀ x : ℝ,
      f ((x : ℂ) + (T : ℂ) * I) =
        g ((x : ℂ) + (T : ℂ) * I))
    (hleft : ∀ y : ℝ,
      f ((σL : ℂ) + (y : ℂ) * I) =
        g ((σL : ℂ) + (y : ℂ) * I))
    (hright : ∀ y : ℝ,
      f ((σR : ℂ) + (y : ℂ) * I) =
        g ((σR : ℂ) + (y : ℂ) * I)) :
    rectangularBoundaryIntegral f
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) =
      rectangularBoundaryIntegral g
        (symmetricLowerCorner σL T) (symmetricUpperCorner σR T) := by
  unfold rectangularBoundaryIntegral rectangularLowerEdge
    rectangularUpperEdge rectangularRightEdge rectangularLeftEdge
    symmetricLowerCorner symmetricUpperCorner
  simp [Complex.mul_re, Complex.mul_im]
  simp only [← sub_eq_add_neg]
  rw [intervalIntegral.integral_congr (fun x _ => hminus x)]
  rw [intervalIntegral.integral_congr (fun x _ => hplus x)]
  rw [intervalIntegral.integral_congr (fun y _ => hright y)]
  rw [intervalIntegral.integral_congr (fun y _ => hleft y)]

/-- The patch changes no value on a nonzero-height canonical boundary. -/
theorem rectangularBoundaryIntegral_patched_eq_finiteRemainder
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) {T : ℝ} (hT : 0 < T) :
    rectangularBoundaryIntegral
        (routeCTaylorPatchedFiniteRemainder u hu M)
        (symmetricLowerCorner (routeCTaylorCanonicalLeft M) T)
        (symmetricUpperCorner routeCTaylorCanonicalRight T) =
      rectangularBoundaryIntegral
        (routeCTaylorFiniteRemainder u M)
        (symmetricLowerCorner (routeCTaylorCanonicalLeft M) T)
        (symmetricUpperCorner routeCTaylorCanonicalRight T) := by
  apply rectangularBoundaryIntegral_congr_symmetric
  · intro x
    exact finiteAnalyticPatch_of_notMem _ _ _
      (routeCTaylor_lower_horizontal_not_exceptional M hT x)
  · intro x
    exact finiteAnalyticPatch_of_notMem _ _ _
      (routeCTaylor_upper_horizontal_not_exceptional M hT x)
  · intro y
    exact finiteAnalyticPatch_of_notMem _ _ _
      (routeCTaylor_left_vertical_not_exceptional M y)
  · intro y
    exact finiteAnalyticPatch_of_notMem _ _ _
      (routeCTaylor_right_vertical_not_exceptional M y)

/-- The literal, unpatched finite remainder has zero canonical boundary
integral. -/
theorem rectangularBoundaryIntegral_routeCTaylorFiniteRemainder_eq_zero
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (hM : 1 ≤ M)
    {T : ℝ} (hT : 0 < T) :
    rectangularBoundaryIntegral (routeCTaylorFiniteRemainder u M)
        (symmetricLowerCorner (routeCTaylorCanonicalLeft M) T)
        (symmetricUpperCorner routeCTaylorCanonicalRight T) = 0 := by
  rw [← rectangularBoundaryIntegral_patched_eq_finiteRemainder
    u hu M hT]
  exact rectangularBoundaryIntegral_routeCTaylorCanonicalPatched_eq_zero
    u hu M hM T

/-- A sine zero of `πs` forces `s` itself to be an integer. -/
theorem exists_intCast_of_sin_pi_mul_eq_zero {s : ℂ}
    (h : Complex.sin ((Real.pi : ℂ) * s) = 0) :
    ∃ k : ℤ, s = (k : ℂ) := by
  rcases Complex.sin_eq_zero_iff.mp h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr Real.pi_ne_zero
  apply (mul_left_cancel₀ hpi)
  calc
    (Real.pi : ℂ) * s = (k : ℂ) * (Real.pi : ℂ) := hk
    _ = (Real.pi : ℂ) * (k : ℂ) := by ring

theorem sin_pi_mul_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
  intro h
  rcases exists_intCast_of_sin_pi_mul_eq_zero h with ⟨k, hk⟩
  apply hs
  rw [hk]
  simp

/-- A convenient regular-point lemma for the literal finite remainder. -/
theorem analyticAt_routeCTaylorFiniteRemainder_of_regular
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0)
    (hsExc : s ∉ routeCTaylorExceptionalPoints M) :
    AnalyticAt ℂ (routeCTaylorFiniteRemainder u M) s := by
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

theorem continuous_routeCTaylorFiniteRemainder_lower
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) {T : ℝ} (hT : 0 < T) :
    Continuous (fun x : ℝ => routeCTaylorFiniteRemainder u M
      ((x : ℂ) - (T : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro x
  let s : ℂ := (x : ℂ) - (T : ℂ) * I
  have him : s.im ≠ 0 := by
    dsimp [s]
    simp
    linarith
  have ha := analyticAt_routeCTaylorFiniteRemainder_of_regular
    u hu M (by intro h; apply him; rw [h]; simp)
      (by intro h; apply him; rw [h]; simp)
      (sin_pi_mul_ne_zero_of_im_ne_zero him)
      (routeCTaylor_lower_horizontal_not_exceptional M hT x)
  have hinner : ContinuousAt
      (fun t : ℝ => (t : ℂ) - (T : ℂ) * I) x := by fun_prop
  simpa [s] using ha.continuousAt.comp
    (f := fun t : ℝ => (t : ℂ) - (T : ℂ) * I) hinner

theorem continuous_routeCTaylorFiniteRemainder_upper
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) {T : ℝ} (hT : 0 < T) :
    Continuous (fun x : ℝ => routeCTaylorFiniteRemainder u M
      ((x : ℂ) + (T : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro x
  let s : ℂ := (x : ℂ) + (T : ℂ) * I
  have him : s.im ≠ 0 := by
    dsimp [s]
    simp
    linarith
  have ha := analyticAt_routeCTaylorFiniteRemainder_of_regular
    u hu M (by intro h; apply him; rw [h]; simp)
      (by intro h; apply him; rw [h]; simp)
      (sin_pi_mul_ne_zero_of_im_ne_zero him)
      (routeCTaylor_upper_horizontal_not_exceptional M hT x)
  have hinner : ContinuousAt
      (fun t : ℝ => (t : ℂ) + (T : ℂ) * I) x := by fun_prop
  simpa [s] using ha.continuousAt.comp
    (f := fun t : ℝ => (t : ℂ) + (T : ℂ) * I) hinner

theorem continuous_routeCTaylorFiniteRemainder_left
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) :
    Continuous (fun y : ℝ => routeCTaylorFiniteRemainder u M
      ((routeCTaylorCanonicalLeft M : ℂ) + (y : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  let s : ℂ := (routeCTaylorCanonicalLeft M : ℂ) + (y : ℂ) * I
  have hsInt : ∀ k : ℤ, s ≠ (k : ℂ) := by
    intro k h
    apply routeCTaylorCanonicalLeft_ne_intCast M k
    apply Complex.ext
    · simpa [s] using congrArg Complex.re h
    · simp
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    intro h
    rcases exists_intCast_of_sin_pi_mul_eq_zero h with ⟨k, hk⟩
    exact hsInt k hk
  have ha := analyticAt_routeCTaylorFiniteRemainder_of_regular
    u hu M (by simpa using hsInt 0) (by simpa using hsInt 1) hsin
      (routeCTaylor_left_vertical_not_exceptional M y)
  have hinner : ContinuousAt
      (fun t : ℝ =>
        (routeCTaylorCanonicalLeft M : ℂ) + (t : ℂ) * I) y := by
    fun_prop
  simpa [s] using ha.continuousAt.comp
    (f := fun t : ℝ =>
      (routeCTaylorCanonicalLeft M : ℂ) + (t : ℂ) * I) hinner

theorem continuous_routeCTaylorFiniteRemainder_right
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) :
    Continuous (fun y : ℝ => routeCTaylorFiniteRemainder u M
      ((routeCTaylorCanonicalRight : ℂ) + (y : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  let s : ℂ := (routeCTaylorCanonicalRight : ℂ) + (y : ℂ) * I
  have hsInt : ∀ k : ℤ, s ≠ (k : ℂ) := by
    intro k h
    apply routeCTaylorCanonicalRight_ne_intCast k
    apply Complex.ext
    · simpa [s] using congrArg Complex.re h
    · simp
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    intro h
    rcases exists_intCast_of_sin_pi_mul_eq_zero h with ⟨k, hk⟩
    exact hsInt k hk
  have ha := analyticAt_routeCTaylorFiniteRemainder_of_regular
    u hu M (by simpa using hsInt 0) (by simpa using hsInt 1) hsin
      (routeCTaylor_right_vertical_not_exceptional M y)
  have hinner : ContinuousAt
      (fun t : ℝ =>
        (routeCTaylorCanonicalRight : ℂ) + (t : ℂ) * I) y := by
    fun_prop
  simpa [s] using ha.continuousAt.comp
    (f := fun t : ℝ =>
      (routeCTaylorCanonicalRight : ℂ) + (t : ℂ) * I) hinner

theorem continuous_routeCTaylorOddPrincipalSum_lower
    (u : ℂ) (M : ℕ) {T : ℝ} (hT : 0 < T) :
    Continuous (fun x : ℝ => routeCTaylorOddPrincipalSum u M
      ((x : ℂ) - (T : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hnot := routeCTaylor_lower_horizontal_not_exceptional M hT x
  have hodd : (x : ℂ) - (T : ℂ) * I ∉
      routeCTaylorOddExceptionalPoints M := by
    intro h
    apply hnot
    rw [routeCTaylorExceptionalPoints, Finset.mem_union]
    exact Or.inl h
  have hinner : ContinuousAt
      (fun t : ℝ => (t : ℂ) - (T : ℂ) * I) x := by fun_prop
  exact (analyticAt_routeCTaylorOddPrincipalSum_of_notMem u M hodd).continuousAt.comp
    (f := fun t : ℝ => (t : ℂ) - (T : ℂ) * I) hinner

theorem continuous_routeCTaylorOddPrincipalSum_upper
    (u : ℂ) (M : ℕ) {T : ℝ} (hT : 0 < T) :
    Continuous (fun x : ℝ => routeCTaylorOddPrincipalSum u M
      ((x : ℂ) + (T : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hnot := routeCTaylor_upper_horizontal_not_exceptional M hT x
  have hodd : (x : ℂ) + (T : ℂ) * I ∉
      routeCTaylorOddExceptionalPoints M := by
    intro h
    apply hnot
    rw [routeCTaylorExceptionalPoints, Finset.mem_union]
    exact Or.inl h
  have hinner : ContinuousAt
      (fun t : ℝ => (t : ℂ) + (T : ℂ) * I) x := by fun_prop
  exact (analyticAt_routeCTaylorOddPrincipalSum_of_notMem u M hodd).continuousAt.comp
    (f := fun t : ℝ => (t : ℂ) + (T : ℂ) * I) hinner

theorem continuous_routeCTaylorOddPrincipalSum_left
    (u : ℂ) (M : ℕ) :
    Continuous (fun y : ℝ => routeCTaylorOddPrincipalSum u M
      ((routeCTaylorCanonicalLeft M : ℂ) + (y : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hnot := routeCTaylor_left_vertical_not_exceptional M y
  have hodd : (routeCTaylorCanonicalLeft M : ℂ) + (y : ℂ) * I ∉
      routeCTaylorOddExceptionalPoints M := by
    intro h
    apply hnot
    rw [routeCTaylorExceptionalPoints, Finset.mem_union]
    exact Or.inl h
  have hinner : ContinuousAt
      (fun t : ℝ =>
        (routeCTaylorCanonicalLeft M : ℂ) + (t : ℂ) * I) y := by
    fun_prop
  exact (analyticAt_routeCTaylorOddPrincipalSum_of_notMem u M hodd).continuousAt.comp
    (f := fun t : ℝ =>
      (routeCTaylorCanonicalLeft M : ℂ) + (t : ℂ) * I) hinner

theorem continuous_routeCTaylorOddPrincipalSum_right
    (u : ℂ) (M : ℕ) :
    Continuous (fun y : ℝ => routeCTaylorOddPrincipalSum u M
      ((routeCTaylorCanonicalRight : ℂ) + (y : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hnot := routeCTaylor_right_vertical_not_exceptional M y
  have hodd : (routeCTaylorCanonicalRight : ℂ) + (y : ℂ) * I ∉
      routeCTaylorOddExceptionalPoints M := by
    intro h
    apply hnot
    rw [routeCTaylorExceptionalPoints, Finset.mem_union]
    exact Or.inl h
  have hinner : ContinuousAt
      (fun t : ℝ =>
        (routeCTaylorCanonicalRight : ℂ) + (t : ℂ) * I) y := by
    fun_prop
  exact (analyticAt_routeCTaylorOddPrincipalSum_of_notMem u M hodd).continuousAt.comp
    (f := fun t : ℝ =>
      (routeCTaylorCanonicalRight : ℂ) + (t : ℂ) * I) hinner

/-- The complete unconditional finite contour shift for the literal central
Mellin integrand. -/
theorem rectangularBoundaryIntegral_bettinConreyGZero_eq_oddResidues
    (u : ℂ) (hu : u ≠ 0) (M : ℕ) (hM : 1 ≤ M)
    {T : ℝ} (hT : 0 < T) :
    rectangularBoundaryIntegral
        (bettinConreyGZeroMeromorphicIntegrand u)
        (symmetricLowerCorner (routeCTaylorCanonicalLeft M) T)
        (symmetricUpperCorner routeCTaylorCanonicalRight T) =
      2 * Real.pi * I *
        ∑ n ∈ Finset.Icc 1 M,
          bettinConreyGZeroOddResidue u n := by
  let R := routeCTaylorFiniteRemainder u M
  let P := routeCTaylorOddPrincipalSum u M
  have hdec : rectangularBoundaryIntegral
      (bettinConreyGZeroMeromorphicIntegrand u)
      (symmetricLowerCorner (routeCTaylorCanonicalLeft M) T)
      (symmetricUpperCorner routeCTaylorCanonicalRight T) =
    rectangularBoundaryIntegral (fun s => R s + P s)
      (symmetricLowerCorner (routeCTaylorCanonicalLeft M) T)
      (symmetricUpperCorner routeCTaylorCanonicalRight T) := by
    apply rectangularBoundaryIntegral_congr_symmetric
    all_goals intro z
    all_goals unfold R P routeCTaylorFiniteRemainder
    all_goals ring
  have hadd : rectangularBoundaryIntegral (fun s => R s + P s)
      (symmetricLowerCorner (routeCTaylorCanonicalLeft M) T)
      (symmetricUpperCorner routeCTaylorCanonicalRight T) =
    rectangularBoundaryIntegral R
        (symmetricLowerCorner (routeCTaylorCanonicalLeft M) T)
        (symmetricUpperCorner routeCTaylorCanonicalRight T) +
      rectangularBoundaryIntegral P
        (symmetricLowerCorner (routeCTaylorCanonicalLeft M) T)
        (symmetricUpperCorner routeCTaylorCanonicalRight T) := by
    apply rectangularBoundaryIntegral_add_symmetric
    · exact continuous_routeCTaylorFiniteRemainder_lower u hu M hT
    · exact continuous_routeCTaylorOddPrincipalSum_lower u M hT
    · exact continuous_routeCTaylorFiniteRemainder_upper u hu M hT
    · exact continuous_routeCTaylorOddPrincipalSum_upper u M hT
    · exact continuous_routeCTaylorFiniteRemainder_left u hu M
    · exact continuous_routeCTaylorOddPrincipalSum_left u M
    · exact continuous_routeCTaylorFiniteRemainder_right u hu M
    · exact continuous_routeCTaylorOddPrincipalSum_right u M
  have hRzero : rectangularBoundaryIntegral R
      (symmetricLowerCorner (routeCTaylorCanonicalLeft M) T)
      (symmetricUpperCorner routeCTaylorCanonicalRight T) = 0 := by
    exact rectangularBoundaryIntegral_routeCTaylorFiniteRemainder_eq_zero
      u hu M hM hT
  have hL : ∀ n ∈ Finset.Icc 1 M,
      routeCTaylorCanonicalLeft M < (routeCTaylorPolePoint n).re := by
    intro n hn
    have hnle : n ≤ M := (Finset.mem_Icc.mp hn).2
    have hnleR : (n : ℝ) ≤ M := by exact_mod_cast hnle
    simp [routeCTaylorCanonicalLeft, routeCTaylorPolePoint]
    linarith
  have hRight : ∀ n ∈ Finset.Icc 1 M,
      (routeCTaylorPolePoint n).re < routeCTaylorCanonicalRight := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    simp [routeCTaylorCanonicalRight, routeCTaylorPolePoint]
    linarith
  have hP : rectangularBoundaryIntegral P
      (symmetricLowerCorner (routeCTaylorCanonicalLeft M) T)
      (symmetricUpperCorner routeCTaylorCanonicalRight T) =
      2 * Real.pi * I *
        ∑ n ∈ Finset.Icc 1 M,
          bettinConreyGZeroOddResidue u n := by
    simpa [P, routeCTaylorOddPrincipalSum,
      routeCTaylorOddPrincipalTerm] using
      rectangularBoundaryIntegral_routeCTaylorPoles u M
        (routeCTaylorCanonicalLeft M) routeCTaylorCanonicalRight T
        hL hRight hT
  rw [hdec, hadd, hRzero, hP, zero_add]

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorMultiResidueRectangle
