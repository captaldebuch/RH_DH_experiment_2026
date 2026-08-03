import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryTail

/-!
# Finite hyperbolic reindexing of the Ehm log taper

This module groups the finite region `d * k ≤ J` by the product `j = d*k`.
The result is an exact divisor-coefficient identity.  It neither passes to an
infinite series nor estimates the incomplete-divisor range `j > N`.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbola

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBoundaryTail

/-- The finite hyperbolic truncation of the inner Ehm `R₁` series. -/
noncomputable def ehmFiniteS1HyperbolicSum
    (R1 : ℝ → ℝ) (N J : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 J,
    if d * k ≤ J then
      dirichletCoeff N d * R1 (((d * k : ℕ) : ℝ) * x)
    else 0

/-- The same finite sum after grouping by `j = d*k`. -/
noncomputable def ehmFiniteDivisorGroupedSum
    (R1 : ℝ → ℝ) (N J : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 J,
    ehmLogTaperDivisorCoeff N j * R1 ((j : ℝ) * x)

/-- The completely evaluated portion `2 ≤ j ≤ N` of the grouped sum. -/
noncomputable def ehmFiniteVonMangoldtBoundary
    (R1 : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 N,
    ArithmeticFunction.vonMangoldt j / Real.log (N : ℝ) *
      R1 ((j : ℝ) * x)

/-- The finite incomplete-divisor range `N < j ≤ J`.  This remains signed
and is not replaced by a sum of absolute values. -/
noncomputable def ehmFiniteIncompleteDivisorTail
    (R1 : ℝ → ℝ) (N J : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (N + 1) J,
    ehmLogTaperDivisorCoeff N j * R1 ((j : ℝ) * x)

/-- Multiplication by a positive `d` bijects the hyperbolic row with the
multiples of `d` in `[1,J]`. -/
private theorem hyperbolicRow_eq_divisibleRow
    (f : ℕ → ℝ) (d J : ℕ) (hd : 0 < d) :
    (∑ k ∈ Finset.Icc 1 J, if d * k ≤ J then f (d * k) else 0) =
      ∑ j ∈ Finset.Icc 1 J, if d ∣ j then f j else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ => d * k)
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkIcc, hdkJ⟩
    rcases Finset.mem_Icc.mp hkIcc with ⟨hk1, _⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hd (lt_of_lt_of_le Nat.zero_lt_one hk1), hdkJ⟩,
      dvd_mul_right d k⟩
  · intro a _ b _ hab
    exact Nat.mul_left_cancel hd hab
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjIcc, hdj⟩
    rcases Finset.mem_Icc.mp hjIcc with ⟨hj1, hjJ⟩
    refine ⟨j / d, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      have hdjpos : 0 < j / d :=
        Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hj1) hdj) hd
      have hquotJ : j / d ≤ J := (Nat.div_le_self j d).trans hjJ
      constructor
      · exact Finset.mem_Icc.mpr ⟨hdjpos, hquotJ⟩
      · rw [Nat.mul_div_cancel' hdj]
        exact hjJ
    · exact Nat.mul_div_cancel' hdj
  · intro k _
    rfl

/-- For positive `j`, restricting divisors to `d ≤ N` is the same as
restricting positive indices in `[1,N]` to divisors of `j`. -/
private theorem positiveDivisors_filter_eq (N j : ℕ) (hj : 0 < j) :
    (Finset.Icc 1 N).filter (fun d => d ∣ j) =
      j.divisors.filter (fun d => d ≤ N) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd1, hdN⟩, hdj⟩
    exact ⟨⟨hdj, Nat.ne_of_gt hj⟩, hdN⟩
  · rintro ⟨⟨hdj, _⟩, hdN⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdj hj, hdN⟩, hdj⟩

/-- Exact finite hyperbolic reindexing.  The coefficient of `R₁(jx)` is the
incomplete divisor sum `A_N(j)`. -/
theorem ehmFiniteS1HyperbolicSum_eq_divisorGrouped
    (R1 : ℝ → ℝ) (N J : ℕ) (x : ℝ) :
    ehmFiniteS1HyperbolicSum R1 N J x =
      ehmFiniteDivisorGroupedSum R1 N J x := by
  classical
  unfold ehmFiniteS1HyperbolicSum ehmFiniteDivisorGroupedSum
  calc
    (∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 J,
        if d * k ≤ J then
          dirichletCoeff N d * R1 (((d * k : ℕ) : ℝ) * x)
        else 0) =
        ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 J,
          if d ∣ j then
            dirichletCoeff N d * R1 ((j : ℝ) * x)
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hdmem
      have hd : 0 < d :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdmem).1
      exact hyperbolicRow_eq_divisibleRow
        (fun j => dirichletCoeff N d * R1 ((j : ℝ) * x)) d J hd
    _ = ∑ j ∈ Finset.Icc 1 J, ∑ d ∈ Finset.Icc 1 N,
          if d ∣ j then
            dirichletCoeff N d * R1 ((j : ℝ) * x)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.Icc 1 J,
        ehmLogTaperDivisorCoeff N j * R1 ((j : ℝ) * x) := by
      apply Finset.sum_congr rfl
      intro j hjmem
      have hj : 0 < j :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hjmem).1
      calc
        (∑ d ∈ Finset.Icc 1 N,
            if d ∣ j then
              dirichletCoeff N d * R1 ((j : ℝ) * x)
            else 0) =
            ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ j),
              dirichletCoeff N d * R1 ((j : ℝ) * x) := by
          rw [Finset.sum_filter]
        _ = ∑ d ∈ j.divisors.filter (fun d => d ≤ N),
              dirichletCoeff N d * R1 ((j : ℝ) * x) := by
          rw [positiveDivisors_filter_eq N j hj]
        _ = ehmLogTaperDivisorCoeff N j * R1 ((j : ℝ) * x) := by
          unfold ehmLogTaperDivisorCoeff
          rw [Finset.sum_mul, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro d _
          split <;> simp_all

/-- The corresponding finite defect is therefore the grouped divisor sum
minus the initial `R₁(x)` term. -/
theorem ehmFiniteS1HyperbolicSum_sub_R1_eq_divisorGrouped_sub_R1
    (R1 : ℝ → ℝ) (N J : ℕ) (x : ℝ) :
    ehmFiniteS1HyperbolicSum R1 N J x - R1 x =
      ehmFiniteDivisorGroupedSum R1 N J x - R1 x := by
  rw [ehmFiniteS1HyperbolicSum_eq_divisorGrouped]

/-- For `N ≤ J`, the grouped defect is exactly a finite von Mangoldt
boundary plus the still-incomplete divisor tail `N < j ≤ J`. -/
theorem ehmFiniteDivisorGroupedSum_sub_R1_eq_boundary_add_tail
    (R1 : ℝ → ℝ) (N J : ℕ) (x : ℝ)
    (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteDivisorGroupedSum R1 N J x - R1 x =
      ehmFiniteVonMangoldtBoundary R1 N x +
        ehmFiniteIncompleteDivisorTail R1 N J x := by
  classical
  let F : ℕ → ℝ := fun j =>
    ehmLogTaperDivisorCoeff N j * R1 ((j : ℝ) * x)
  have hfirst : Finset.Icc 1 N = {1} ∪ Finset.Icc 2 N := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hwhole :
      Finset.Icc 1 J = Finset.Icc 1 N ∪ Finset.Icc (N + 1) J := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisFirst : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 N) := by
    apply Finset.disjoint_left.mpr
    intro j hj1 hj2
    simp only [Finset.mem_singleton] at hj1
    rw [hj1] at hj2
    have := (Finset.mem_Icc.mp hj2).1
    omega
  have hdisWhole :
      Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) J) := by
    apply Finset.disjoint_left.mpr
    intro j hjN hjTail
    have hjN' := (Finset.mem_Icc.mp hjN).2
    have hjTail' := (Finset.mem_Icc.mp hjTail).1
    omega
  have hsplit :
      (∑ j ∈ Finset.Icc 1 J, F j) =
        F 1 + (∑ j ∈ Finset.Icc 2 N, F j) +
          ∑ j ∈ Finset.Icc (N + 1) J, F j := by
    rw [hwhole, Finset.sum_union hdisWhole, hfirst,
      Finset.sum_union hdisFirst]
    simp
  have hboundary :
      (∑ j ∈ Finset.Icc 2 N, F j) =
        ehmFiniteVonMangoldtBoundary R1 N x := by
    unfold ehmFiniteVonMangoldtBoundary
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [F]
    rw [ehmLogTaperDivisorCoeff_eq_vonMangoldt_div_log N j hN
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2]
  unfold ehmFiniteDivisorGroupedSum ehmFiniteIncompleteDivisorTail
  change (∑ j ∈ Finset.Icc 1 J, F j) - R1 x = _
  rw [hsplit, hboundary]
  have hFone : F 1 = R1 x := by
    dsimp [F]
    rw [ehmLogTaperDivisorCoeff_one N hN]
    norm_num
  rw [hFone]
  ring

/-- Combined finite form: the hyperbolic truncation minus `R₁(x)` is the
explicit boundary plus the incomplete-divisor tail. -/
theorem ehmFiniteS1HyperbolicSum_sub_R1_eq_boundary_add_tail
    (R1 : ℝ → ℝ) (N J : ℕ) (x : ℝ)
    (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteS1HyperbolicSum R1 N J x - R1 x =
      ehmFiniteVonMangoldtBoundary R1 N x +
        ehmFiniteIncompleteDivisorTail R1 N J x := by
  rw [ehmFiniteS1HyperbolicSum_sub_R1_eq_divisorGrouped_sub_R1,
    ehmFiniteDivisorGroupedSum_sub_R1_eq_boundary_add_tail R1 N J x hN hNJ]

/-- The finite hyperbolic truncation inserted into Ehm's outer BCF sum. -/
noncomputable def ehmFiniteHyperbolicInversionError
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) *
    (ehmFiniteS1HyperbolicSum R1 N J (1 / (m : ℝ)) -
      R1 (1 / (m : ℝ)))

/-- Outer sum of the explicit finite von Mangoldt boundary. -/
noncomputable def ehmFiniteVonMangoldtBoundaryOuter
    (R1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) *
    ehmFiniteVonMangoldtBoundary R1 N (1 / (m : ℝ))

/-- Outer sum of the signed incomplete-divisor range `N < j ≤ J`. -/
noncomputable def ehmFiniteIncompleteDivisorTailOuter
    (R1 : ℝ → ℝ) (N J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, dirichletCoeff N m / (m : ℝ) *
    ehmFiniteIncompleteDivisorTail R1 N J (1 / (m : ℝ))

/-- Exact outer hyperbolic decomposition.  No absolute value is introduced,
so cancellation between the finite boundary and incomplete tail is retained. -/
theorem ehmFiniteHyperbolicInversionError_eq_boundaryOuter_add_tailOuter
    (R1 : ℝ → ℝ) (N J : ℕ) (hN : 2 ≤ N) (hNJ : N ≤ J) :
    ehmFiniteHyperbolicInversionError R1 N J =
      ehmFiniteVonMangoldtBoundaryOuter R1 N +
        ehmFiniteIncompleteDivisorTailOuter R1 N J := by
  classical
  unfold ehmFiniteHyperbolicInversionError
    ehmFiniteVonMangoldtBoundaryOuter
    ehmFiniteIncompleteDivisorTailOuter
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [ehmFiniteS1HyperbolicSum_sub_R1_eq_boundary_add_tail
    R1 N J (1 / (m : ℝ)) hN hNJ]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbola
