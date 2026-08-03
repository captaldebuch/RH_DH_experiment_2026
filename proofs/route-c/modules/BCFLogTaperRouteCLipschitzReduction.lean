import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCCentralLipschitz

/-!
# Route C: reduction of global regularity to one primitive pair

This module removes all remaining finite H15 aggregation from the
central-parameter regularity problem.  A polynomial Lipschitz estimate for
each primitive `(g,a,b)` period pair, uniform on the common half-disk, is
lifted through the complete fixed-cutoff sum.  The three finite indices cost
exactly three additional powers of `N+2`.

The result is deliberately unsigned: this is regularity in the auxiliary
central parameter, not the final signed H15 cancellation.  The next analytic
target is the primitive-pair estimate, whose finite Hurwitz representation is
already explicit.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCLipschitzReduction

open Complex Filter Set Topology
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCUniformCentralWindow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralLipschitz

/-- Away from the removable point, the completed aggregate minus its central
value is exactly the finite sum of the primitive period-pair increments.  The
dual cotangent term cancels identically. -/
theorem routeCCentralAnalyticExtension_sub_target_eq_pair_sum
    (H : AuliBettinConreyRationalReciprocityPackage)
    (N : ℕ) {z : ℂ} (hz : z ≠ 0) :
    routeCCentralAnalyticExtension H N z -
        routeCCentralFinitePartTarget N =
      ∑ g ∈ Finset.Icc 1 N,
        ∑ a ∈ Finset.Icc 1 (N / g),
          ∑ b ∈ Finset.Icc 1 (N / g),
            (routeCInteriorRenormalizedPeriodPair H z N g a b -
              routeCInteriorCentralPeriodPairC N g a b) := by
  rw [routeCCentralAnalyticExtension_of_ne H N hz]
  have htarget : routeCCentralFinitePartTarget N =
      (routeCInteriorCentralPeriodAggregate N : ℂ) +
        (routeCInteriorCentralDualAggregate N : ℂ) := by
    unfold routeCCentralFinitePartTarget
    rw [routeCInteriorCentralCotangent_sub_finitePart]
    push_cast
    rfl
  rw [htarget]
  unfold routeCInteriorRenormalizedPeriodDualAggregate
  rw [← routeCInteriorCentralPeriodAggregateC_eq_ofReal]
  unfold routeCInteriorRenormalizedPeriodAggregate
    routeCInteriorCentralPeriodAggregateC
  simp only [Finset.sum_sub_distrib]
  ring

/-- The exact local quantitative target after removing the finite H15
aggregation. -/
structure RouteCInteriorPairPolynomialControl
    (H : AuliBettinConreyRationalReciprocityPackage) where
  exponent : ℕ
  bound : ∀ (N g a b : ℕ) (z : ℂ),
    g ∈ Finset.Icc 1 N →
    a ∈ Finset.Icc 1 (N / g) →
    b ∈ Finset.Icc 1 (N / g) →
    z ≠ 0 → ‖z‖ ≤ 1 / 2 →
    ‖routeCInteriorRenormalizedPeriodPair H z N g a b -
        routeCInteriorCentralPeriodPairC N g a b‖ ≤
      ((N : ℝ) + 2) ^ exponent * ‖z‖

/-- A constant sum over any interval `Icc 1 M`, with `M ≤ N`, costs at most
one factor of `N+2`. -/
theorem sum_Icc_one_le_mul_cutoff
    (N M : ℕ) (hMN : M ≤ N) (c : ℝ) (hc : 0 ≤ c) :
    (∑ _j ∈ Finset.Icc 1 M, c) ≤ ((N : ℝ) + 2) * c := by
  rw [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hc
  norm_cast
  rw [Nat.card_Icc]
  omega

/-- The nested primitive H15 box has unsigned constant mass at most
`(N+2)^3`. -/
theorem triple_Icc_constant_sum_le
    (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (∑ g ∈ Finset.Icc 1 N,
      ∑ _a ∈ Finset.Icc 1 (N / g),
        ∑ _b ∈ Finset.Icc 1 (N / g), c) ≤
      ((N : ℝ) + 2) ^ 3 * c := by
  have hbase : 0 ≤ (N : ℝ) + 2 := by positivity
  calc
    (∑ g ∈ Finset.Icc 1 N,
      ∑ a ∈ Finset.Icc 1 (N / g),
        ∑ _b ∈ Finset.Icc 1 (N / g), c) ≤
        ∑ g ∈ Finset.Icc 1 N,
          ∑ _a ∈ Finset.Icc 1 (N / g), ((N : ℝ) + 2) * c := by
            apply Finset.sum_le_sum
            intro g _hg
            apply Finset.sum_le_sum
            intro _a _ha
            exact sum_Icc_one_le_mul_cutoff N (N / g)
              (Nat.div_le_self N g) c hc
    _ ≤ ∑ _g ∈ Finset.Icc 1 N,
        ((N : ℝ) + 2) * (((N : ℝ) + 2) * c) := by
          apply Finset.sum_le_sum
          intro g _hg
          exact sum_Icc_one_le_mul_cutoff N (N / g)
            (Nat.div_le_self N g) (((N : ℝ) + 2) * c)
              (mul_nonneg hbase hc)
    _ ≤ ((N : ℝ) + 2) *
        (((N : ℝ) + 2) * (((N : ℝ) + 2) * c)) := by
          exact sum_Icc_one_le_mul_cutoff N N le_rfl
            (((N : ℝ) + 2) * (((N : ℝ) + 2) * c))
              (mul_nonneg hbase (mul_nonneg hbase hc))
    _ = ((N : ℝ) + 2) ^ 3 * c := by ring

/-- Triangle inequality through all three primitive indices. -/
theorem norm_triple_pair_sum_le
    (H : AuliBettinConreyRationalReciprocityPackage)
    (N : ℕ) (z : ℂ) :
    ‖∑ g ∈ Finset.Icc 1 N,
      ∑ a ∈ Finset.Icc 1 (N / g),
        ∑ b ∈ Finset.Icc 1 (N / g),
          (routeCInteriorRenormalizedPeriodPair H z N g a b -
            routeCInteriorCentralPeriodPairC N g a b)‖ ≤
      ∑ g ∈ Finset.Icc 1 N,
        ∑ a ∈ Finset.Icc 1 (N / g),
          ∑ b ∈ Finset.Icc 1 (N / g),
            ‖routeCInteriorRenormalizedPeriodPair H z N g a b -
              routeCInteriorCentralPeriodPairC N g a b‖ := by
  calc
    ‖∑ g ∈ Finset.Icc 1 N,
      ∑ a ∈ Finset.Icc 1 (N / g),
        ∑ b ∈ Finset.Icc 1 (N / g),
          (routeCInteriorRenormalizedPeriodPair H z N g a b -
            routeCInteriorCentralPeriodPairC N g a b)‖ ≤
        ∑ g ∈ Finset.Icc 1 N,
          ‖∑ a ∈ Finset.Icc 1 (N / g),
            ∑ b ∈ Finset.Icc 1 (N / g),
              (routeCInteriorRenormalizedPeriodPair H z N g a b -
                routeCInteriorCentralPeriodPairC N g a b)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ g ∈ Finset.Icc 1 N,
        ∑ a ∈ Finset.Icc 1 (N / g),
          ‖∑ b ∈ Finset.Icc 1 (N / g),
            (routeCInteriorRenormalizedPeriodPair H z N g a b -
              routeCInteriorCentralPeriodPairC N g a b)‖ := by
        apply Finset.sum_le_sum
        intro g _hg
        exact norm_sum_le _ _
    _ ≤ ∑ g ∈ Finset.Icc 1 N,
        ∑ a ∈ Finset.Icc 1 (N / g),
          ∑ b ∈ Finset.Icc 1 (N / g),
            ‖routeCInteriorRenormalizedPeriodPair H z N g a b -
              routeCInteriorCentralPeriodPairC N g a b‖ := by
        apply Finset.sum_le_sum
        intro g _hg
        apply Finset.sum_le_sum
        intro a _ha
        exact norm_sum_le _ _

/-- A polynomial primitive-pair estimate gives the canonical global
half-disk control with an explicit three-power combinatorial loss. -/
noncomputable def RouteCInteriorPairPolynomialControl.toGlobalControl
    {H : AuliBettinConreyRationalReciprocityPackage}
    (P : RouteCInteriorPairPolynomialControl H) :
    RouteCPolynomialHalfDiskControl H where
  exponent := P.exponent + 3
  bound := by
    intro N z hzhalf
    by_cases hz : z = 0
    · subst z
      simp
    · rw [routeCCentralAnalyticExtension_sub_target_eq_pair_sum H N hz]
      have htriangle := norm_triple_pair_sum_le H N z
      have hterm :
          (∑ g ∈ Finset.Icc 1 N,
            ∑ a ∈ Finset.Icc 1 (N / g),
              ∑ b ∈ Finset.Icc 1 (N / g),
                ‖routeCInteriorRenormalizedPeriodPair H z N g a b -
                  routeCInteriorCentralPeriodPairC N g a b‖) ≤
            ∑ g ∈ Finset.Icc 1 N,
              ∑ a ∈ Finset.Icc 1 (N / g),
                ∑ _b ∈ Finset.Icc 1 (N / g),
                  ((N : ℝ) + 2) ^ P.exponent * ‖z‖ := by
        apply Finset.sum_le_sum
        intro g hg
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        exact P.bound N g a b z hg ha hb hz hzhalf
      have hbox := triple_Icc_constant_sum_le N
        (((N : ℝ) + 2) ^ P.exponent * ‖z‖)
        (mul_nonneg (pow_nonneg (by positivity) _) (norm_nonneg z))
      calc
        ‖∑ g ∈ Finset.Icc 1 N,
          ∑ a ∈ Finset.Icc 1 (N / g),
            ∑ b ∈ Finset.Icc 1 (N / g),
              (routeCInteriorRenormalizedPeriodPair H z N g a b -
                routeCInteriorCentralPeriodPairC N g a b)‖ ≤
            ∑ g ∈ Finset.Icc 1 N,
              ∑ a ∈ Finset.Icc 1 (N / g),
                ∑ b ∈ Finset.Icc 1 (N / g),
                  ‖routeCInteriorRenormalizedPeriodPair H z N g a b -
                    routeCInteriorCentralPeriodPairC N g a b‖ := htriangle
        _ ≤ ∑ g ∈ Finset.Icc 1 N,
              ∑ a ∈ Finset.Icc 1 (N / g),
                ∑ _b ∈ Finset.Icc 1 (N / g),
                  ((N : ℝ) + 2) ^ P.exponent * ‖z‖ := hterm
        _ ≤ ((N : ℝ) + 2) ^ 3 *
              (((N : ℝ) + 2) ^ P.exponent * ‖z‖) := hbox
        _ = ((N : ℝ) + 2) ^ (P.exponent + 3) * ‖z‖ := by
          rw [pow_add]
          ring

/-- Therefore primitive-pair control also produces the explicit polynomial
central window. -/
noncomputable def RouteCInteriorPairPolynomialControl.toPolynomialWindowCertificate
    {H : AuliBettinConreyRationalReciprocityPackage}
    (P : RouteCInteriorPairPolynomialControl H) :
    RouteCPolynomialWindowCertificate P.toGlobalControl.toCentralWindowData :=
  P.toGlobalControl.toPolynomialWindowCertificate

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCLipschitzReduction
