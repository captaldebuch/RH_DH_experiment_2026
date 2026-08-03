import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmSignedTransferAudit

/-!
# Rectangular Abel transfer for the coupled Ehm kernel

This file supplies the finite two-dimensional summation-by-parts theorem
needed by the direct signed Ehm route.  It is deliberately independent of
the particular arithmetic coefficient and kernel.

For a coefficient array `a` and a *complete* scalar kernel `K`, let

```text
A(d,m) = sum_{i <= d} sum_{j <= m} a(i,j).
```

The exact identity below writes `sum a(d,m) K(d,m)` as the corner value,
the two oriented edge variations, and the mixed interior variation, all
weighted by `A`.  The resulting inequality is

```text
|sum a K| <= B * rectangularVariation K D M
```

whenever every rectangular prefix has absolute value at most `B`.

The kernel is not split into main and correction pieces.  Thus an H15
application may instantiate `K` with their already recombined expression,
retaining any exact cancellation between them.  This theorem does **not**
prove the required Möbius discrepancy bound `B -> 0`; that is the remaining
signed analytic input.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularAbel

open scoped BigOperators

/-! ## Prefixes and finite differences -/

/-- Prefix of one row through the column indexed by `m`. -/
noncomputable def rowPrefix (a : ℕ → ℕ → ℝ) (d m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), a d j

/-- Rectangular prefix through `(d,m)`, with both endpoints included. -/
noncomputable def rectangularPrefix (a : ℕ → ℕ → ℝ) (d m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (m + 1), a i j

/-- Forward difference in the first coordinate. -/
noncomputable def firstForwardDifference (K : ℕ → ℕ → ℝ) (d m : ℕ) : ℝ :=
  K d m - K (d + 1) m

/-- Forward difference in the second coordinate. -/
noncomputable def secondForwardDifference (K : ℕ → ℕ → ℝ) (d m : ℕ) : ℝ :=
  K d m - K d (m + 1)

/-- Mixed forward difference with the sign dictated by rectangular Abel
summation. -/
noncomputable def mixedForwardDifference (K : ℕ → ℕ → ℝ) (d m : ℕ) : ℝ :=
  K d m - K d (m + 1) - K (d + 1) m + K (d + 1) (m + 1)

/-- Total rectangular variation, including the corner and both boundary
edges.  Omitting any of these terms would make the transfer theorem false. -/
noncomputable def rectangularVariation
    (K : ℕ → ℕ → ℝ) (D M : ℕ) : ℝ :=
  |K D M| +
    (∑ d ∈ Finset.range D, |firstForwardDifference K d M|) +
    (∑ m ∈ Finset.range M, |secondForwardDifference K D m|) +
    ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
      |mixedForwardDifference K d m|

/-- The localized Abel cost.  Unlike a discrepancy supremum times total
variation, this keeps every signed rectangular prefix paired with the kernel
difference at the same coordinate.  It is therefore the sharpest bound
available from the exact rectangular Abel identity using only the triangle
inequality on its individual summands. -/
noncomputable def rectangularWeightedTransferCost
    (a K : ℕ → ℕ → ℝ) (D M : ℕ) : ℝ :=
  |rectangularPrefix a D M * K D M| +
    (∑ d ∈ Finset.range D,
      |rectangularPrefix a d M * firstForwardDifference K d M|) +
    (∑ m ∈ Finset.range M,
      |rectangularPrefix a D m * secondForwardDifference K D m|) +
    ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
      |rectangularPrefix a d m * mixedForwardDifference K d m|

theorem rectangularVariation_nonneg
    (K : ℕ → ℕ → ℝ) (D M : ℕ) :
    0 ≤ rectangularVariation K D M := by
  unfold rectangularVariation
  positivity

/-- A deliberately coarse but completely general variation estimate.  If a
kernel is bounded by `H` on the rectangle and its one-step collar, then its
rectangular variation is at most the number of signed corner contributions
times `H`.

This estimate is useful as a quantitative stop test.  It does not exploit
smoothness or cancellation of finite differences. -/
theorem rectangularVariation_le_of_abs_le
    (K : ℕ → ℕ → ℝ) (D M : ℕ) (H : ℝ)
    (hK : ∀ d ≤ D + 1, ∀ m ≤ M + 1, |K d m| ≤ H) :
    rectangularVariation K D M ≤
      H * ((2 * D + 1 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) := by
  have hcorner : |K D M| ≤ H := hK D (by omega) M (by omega)
  have hfirst :
      (∑ d ∈ Finset.range D, |firstForwardDifference K d M|) ≤
        (D : ℝ) * (2 * H) := by
    calc
      (∑ d ∈ Finset.range D, |firstForwardDifference K d M|) ≤
          ∑ _d ∈ Finset.range D, 2 * H := by
            apply Finset.sum_le_sum
            intro d hd
            have hdlt : d < D := Finset.mem_range.mp hd
            unfold firstForwardDifference
            calc
              |K d M - K (d + 1) M| ≤ |K d M| + |K (d + 1) M| :=
                abs_sub _ _
              _ ≤ H + H := by
                gcongr
                · exact hK d (by omega) M (by omega)
                · exact hK (d + 1) (by omega) M (by omega)
              _ = 2 * H := by ring
      _ = (D : ℝ) * (2 * H) := by simp
  have hsecond :
      (∑ m ∈ Finset.range M, |secondForwardDifference K D m|) ≤
        (M : ℝ) * (2 * H) := by
    calc
      (∑ m ∈ Finset.range M, |secondForwardDifference K D m|) ≤
          ∑ _m ∈ Finset.range M, 2 * H := by
            apply Finset.sum_le_sum
            intro m hm
            have hmlt : m < M := Finset.mem_range.mp hm
            unfold secondForwardDifference
            calc
              |K D m - K D (m + 1)| ≤ |K D m| + |K D (m + 1)| :=
                abs_sub _ _
              _ ≤ H + H := by
                gcongr
                · exact hK D (by omega) m (by omega)
                · exact hK D (by omega) (m + 1) (by omega)
              _ = 2 * H := by ring
      _ = (M : ℝ) * (2 * H) := by simp
  have hmixed :
      (∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
        |mixedForwardDifference K d m|) ≤
        (D : ℝ) * (M : ℝ) * (4 * H) := by
    calc
      (∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
          |mixedForwardDifference K d m|) ≤
          ∑ _d ∈ Finset.range D, ∑ _m ∈ Finset.range M, 4 * H := by
            apply Finset.sum_le_sum
            intro d hd
            have hdlt : d < D := Finset.mem_range.mp hd
            apply Finset.sum_le_sum
            intro m hm
            have hmlt : m < M := Finset.mem_range.mp hm
            unfold mixedForwardDifference
            calc
              |K d m - K d (m + 1) - K (d + 1) m +
                  K (d + 1) (m + 1)| ≤
                  |K d m| + |K d (m + 1)| + |K (d + 1) m| +
                    |K (d + 1) (m + 1)| := by
                    calc
                      |K d m - K d (m + 1) - K (d + 1) m +
                          K (d + 1) (m + 1)| ≤
                          |K d m - K d (m + 1) - K (d + 1) m| +
                            |K (d + 1) (m + 1)| := abs_add_le _ _
                      _ ≤ (|K d m - K d (m + 1)| + |K (d + 1) m|) +
                            |K (d + 1) (m + 1)| := by
                              gcongr
                              exact abs_sub _ _
                      _ ≤ ((|K d m| + |K d (m + 1)|) + |K (d + 1) m|) +
                            |K (d + 1) (m + 1)| := by
                              gcongr
                              exact abs_sub _ _
                  _ ≤ H + H + H + H := by
                    gcongr
                    · exact hK d (by omega) m (by omega)
                    · exact hK d (by omega) (m + 1) (by omega)
                    · exact hK (d + 1) (by omega) m (by omega)
                    · exact hK (d + 1) (by omega) (m + 1) (by omega)
                  _ = 4 * H := by ring
      _ = (D : ℝ) * (M : ℝ) * (4 * H) := by simp; ring
  unfold rectangularVariation
  calc
    |K D M| +
        (∑ d ∈ Finset.range D, |firstForwardDifference K d M|) +
        (∑ m ∈ Finset.range M, |secondForwardDifference K D m|) +
        ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
          |mixedForwardDifference K d m| ≤
      H + (D : ℝ) * (2 * H) + (M : ℝ) * (2 * H) +
        (D : ℝ) * (M : ℝ) * (4 * H) := by gcongr
    _ = H * ((2 * D + 1 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) := by
      push_cast
      ring

/-! ## One- and two-dimensional Abel identities -/

/-- One-dimensional summation by parts in inclusive-prefix form. -/
theorem sum_range_succ_mul_eq_endpoint_add_prefix
    (a K : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), a i * K i) =
      (∑ i ∈ Finset.range (N + 1), a i) * K N +
        ∑ i ∈ Finset.range N,
          (∑ j ∈ Finset.range (i + 1), a j) * (K i - K (i + 1)) := by
  have h := Finset.sum_range_by_parts K a (N + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at h
  calc
    (∑ i ∈ Finset.range (N + 1), a i * K i) =
        ∑ i ∈ Finset.range (N + 1), K i * a i := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = K N * (∑ i ∈ Finset.range (N + 1), a i) -
        ∑ i ∈ Finset.range N,
          (K (i + 1) - K i) * (∑ j ∈ Finset.range (i + 1), a j) := h
    _ = (∑ i ∈ Finset.range (N + 1), a i) * K N +
        ∑ i ∈ Finset.range N,
          (∑ j ∈ Finset.range (i + 1), a j) * (K i - K (i + 1)) := by
          rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
          congr 1
          · ring
          apply Finset.sum_congr rfl
          intro i _
          ring

private theorem sum_rowPrefix_eq_rectangularPrefix
    (a : ℕ → ℕ → ℝ) (d m : ℕ) :
    (∑ i ∈ Finset.range (d + 1), rowPrefix a i m) =
      rectangularPrefix a d m := by
  rfl

/-- Exact two-dimensional Abel transform on the inclusive rectangle
`[0,D] x [0,M]`.

The four displayed contributions are respectively the corner, the first
edge, the second edge, and the mixed interior variation. -/
theorem rectangularAbel_identity
    (a K : ℕ → ℕ → ℝ) (D M : ℕ) :
    (∑ d ∈ Finset.range (D + 1),
      ∑ m ∈ Finset.range (M + 1), a d m * K d m) =
      rectangularPrefix a D M * K D M +
        (∑ d ∈ Finset.range D,
          rectangularPrefix a d M * firstForwardDifference K d M) +
        (∑ m ∈ Finset.range M,
          rectangularPrefix a D m * secondForwardDifference K D m) +
        ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
          rectangularPrefix a d m * mixedForwardDifference K d m := by
  have hrow : ∀ d : ℕ,
      (∑ m ∈ Finset.range (M + 1), a d m * K d m) =
        rowPrefix a d M * K d M +
          ∑ m ∈ Finset.range M,
            rowPrefix a d m * secondForwardDifference K d m := by
    intro d
    simpa [rowPrefix, secondForwardDifference] using
      (sum_range_succ_mul_eq_endpoint_add_prefix
        (fun m => a d m) (fun m => K d m) M)
  rw [Finset.sum_congr rfl (fun d _ => hrow d), Finset.sum_add_distrib]
  have hedgeD := sum_range_succ_mul_eq_endpoint_add_prefix
    (fun d => rowPrefix a d M) (fun d => K d M) D
  simp only [sum_rowPrefix_eq_rectangularPrefix] at hedgeD
  have hm : ∀ m : ℕ,
      (∑ d ∈ Finset.range (D + 1),
        rowPrefix a d m * secondForwardDifference K d m) =
        rectangularPrefix a D m * secondForwardDifference K D m +
          ∑ d ∈ Finset.range D,
            rectangularPrefix a d m * mixedForwardDifference K d m := by
    intro m
    have h := sum_range_succ_mul_eq_endpoint_add_prefix
      (fun d => rowPrefix a d m)
      (fun d => secondForwardDifference K d m) D
    simp only [sum_rowPrefix_eq_rectangularPrefix] at h
    rw [h]
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    unfold secondForwardDifference mixedForwardDifference
    ring
  have hrest :
      (∑ d ∈ Finset.range (D + 1), ∑ m ∈ Finset.range M,
        rowPrefix a d m * secondForwardDifference K d m) =
        (∑ m ∈ Finset.range M,
          rectangularPrefix a D m * secondForwardDifference K D m) +
          ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
            rectangularPrefix a d m * mixedForwardDifference K d m := by
    calc
      (∑ d ∈ Finset.range (D + 1), ∑ m ∈ Finset.range M,
          rowPrefix a d m * secondForwardDifference K d m) =
          ∑ m ∈ Finset.range M, ∑ d ∈ Finset.range (D + 1),
            rowPrefix a d m * secondForwardDifference K d m := by
              rw [Finset.sum_comm]
      _ = ∑ m ∈ Finset.range M,
          (rectangularPrefix a D m * secondForwardDifference K D m +
            ∑ d ∈ Finset.range D,
              rectangularPrefix a d m * mixedForwardDifference K d m) := by
            apply Finset.sum_congr rfl
            intro m _
            exact hm m
      _ = (∑ m ∈ Finset.range M,
          rectangularPrefix a D m * secondForwardDifference K D m) +
          ∑ m ∈ Finset.range M, ∑ d ∈ Finset.range D,
            rectangularPrefix a d m * mixedForwardDifference K d m := by
              rw [Finset.sum_add_distrib]
      _ = (∑ m ∈ Finset.range M,
          rectangularPrefix a D m * secondForwardDifference K D m) +
          ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
            rectangularPrefix a d m * mixedForwardDifference K d m := by
              rw [Finset.sum_comm]
  rw [hedgeD, hrest]
  simp only [firstForwardDifference]
  ring

/-- Exact signed transfer to the localized Abel cost. -/
theorem abs_rectangularSum_le_weightedTransferCost
    (a K : ℕ → ℕ → ℝ) (D M : ℕ) :
    |∑ d ∈ Finset.range (D + 1),
      ∑ m ∈ Finset.range (M + 1), a d m * K d m| ≤
        rectangularWeightedTransferCost a K D M := by
  rw [rectangularAbel_identity]
  unfold rectangularWeightedTransferCost
  calc
    |rectangularPrefix a D M * K D M +
        (∑ d ∈ Finset.range D,
          rectangularPrefix a d M * firstForwardDifference K d M) +
        (∑ m ∈ Finset.range M,
          rectangularPrefix a D m * secondForwardDifference K D m) +
        ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
          rectangularPrefix a d m * mixedForwardDifference K d m| ≤
      |rectangularPrefix a D M * K D M| +
        |∑ d ∈ Finset.range D,
          rectangularPrefix a d M * firstForwardDifference K d M| +
        |∑ m ∈ Finset.range M,
          rectangularPrefix a D m * secondForwardDifference K D m| +
        |∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
          rectangularPrefix a d m * mixedForwardDifference K d m| := by
      calc
        |((rectangularPrefix a D M * K D M +
            ∑ d ∈ Finset.range D,
              rectangularPrefix a d M * firstForwardDifference K d M) +
            ∑ m ∈ Finset.range M,
              rectangularPrefix a D m * secondForwardDifference K D m) +
            ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
              rectangularPrefix a d m * mixedForwardDifference K d m| ≤
          |(rectangularPrefix a D M * K D M +
            ∑ d ∈ Finset.range D,
              rectangularPrefix a d M * firstForwardDifference K d M) +
            ∑ m ∈ Finset.range M,
              rectangularPrefix a D m * secondForwardDifference K D m| +
          |∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
              rectangularPrefix a d m * mixedForwardDifference K d m| :=
            abs_add_le _ _
        _ ≤ (|rectangularPrefix a D M * K D M +
              ∑ d ∈ Finset.range D,
                rectangularPrefix a d M * firstForwardDifference K d M| +
            |∑ m ∈ Finset.range M,
                rectangularPrefix a D m * secondForwardDifference K D m|) +
            |∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
                rectangularPrefix a d m * mixedForwardDifference K d m| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ ((|rectangularPrefix a D M * K D M| +
              |∑ d ∈ Finset.range D,
                rectangularPrefix a d M * firstForwardDifference K d M|) +
            |∑ m ∈ Finset.range M,
                rectangularPrefix a D m * secondForwardDifference K D m|) +
            |∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
                rectangularPrefix a d m * mixedForwardDifference K d m| := by
              gcongr
              exact abs_add_le _ _
    _ ≤ |rectangularPrefix a D M * K D M| +
        (∑ d ∈ Finset.range D,
          |rectangularPrefix a d M * firstForwardDifference K d M|) +
        (∑ m ∈ Finset.range M,
          |rectangularPrefix a D m * secondForwardDifference K D m|) +
        ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
          |rectangularPrefix a d m * mixedForwardDifference K d m| := by
      gcongr
      · exact Finset.abs_sum_le_sum_abs _ _
      · exact Finset.abs_sum_le_sum_abs _ _
      · calc
          |∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
              rectangularPrefix a d m * mixedForwardDifference K d m| ≤
            ∑ d ∈ Finset.range D,
              |∑ m ∈ Finset.range M,
                rectangularPrefix a d m * mixedForwardDifference K d m| :=
                  Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
              |rectangularPrefix a d m * mixedForwardDifference K d m| := by
                gcongr with d hd
                exact Finset.abs_sum_le_sum_abs _ _

/-! ## Discrepancy times variation -/

private theorem abs_biSum_mul_le
    {ι : Type*}
    (s : Finset ι) (A L : ι → ℝ) (B : ℝ)
    (hA : ∀ i ∈ s, |A i| ≤ B) :
    |∑ i ∈ s, A i * L i| ≤ B * ∑ i ∈ s, |L i| := by
  calc
    |∑ i ∈ s, A i * L i| ≤ ∑ i ∈ s, |A i * L i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, B * |L i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hA i hi) (abs_nonneg _)
    _ = B * ∑ i ∈ s, |L i| := by rw [Finset.mul_sum]

private theorem abs_rectangular_biSum_mul_le
    (A L : ℕ → ℕ → ℝ) (B : ℝ) (D M : ℕ)
    (hA : ∀ d ∈ Finset.range D, ∀ m ∈ Finset.range M,
      |A d m| ≤ B) :
    |∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M, A d m * L d m| ≤
      B * ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M, |L d m| := by
  calc
    |∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M, A d m * L d m| ≤
        ∑ d ∈ Finset.range D,
          |∑ m ∈ Finset.range M, A d m * L d m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.range D, B * ∑ m ∈ Finset.range M, |L d m| := by
      apply Finset.sum_le_sum
      intro d hd
      exact abs_biSum_mul_le (Finset.range M) (A d) (L d) B
        (hA d hd)
    _ = B * ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M, |L d m| := by
      rw [Finset.mul_sum]

/-- The reusable signed rectangular transfer estimate.

The hypothesis is a bound for the *signed rectangular prefixes* of `a`,
not a termwise absolute estimate.  The conclusion charges it against the
variation of the already recombined kernel `K`, including the two edges and
the corner. -/
theorem abs_rectangularSum_le_discrepancy_mul_variation
    (a K : ℕ → ℕ → ℝ) (D M : ℕ) (B : ℝ)
    (hprefix : ∀ d ≤ D, ∀ m ≤ M, |rectangularPrefix a d m| ≤ B) :
    |∑ d ∈ Finset.range (D + 1),
      ∑ m ∈ Finset.range (M + 1), a d m * K d m| ≤
        B * rectangularVariation K D M := by
  rw [rectangularAbel_identity]
  have hcorner : |rectangularPrefix a D M * K D M| ≤ B * |K D M| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hprefix D le_rfl M le_rfl) (abs_nonneg _)
  have hedgeD :
      |∑ d ∈ Finset.range D,
          rectangularPrefix a d M * firstForwardDifference K d M| ≤
        B * ∑ d ∈ Finset.range D, |firstForwardDifference K d M| := by
    apply abs_biSum_mul_le (Finset.range D)
        (fun d => rectangularPrefix a d M)
        (fun d => firstForwardDifference K d M) B
    intro d hd
    exact hprefix d (Nat.le_of_lt (Finset.mem_range.mp hd)) M le_rfl
  have hedgeM :
      |∑ m ∈ Finset.range M,
          rectangularPrefix a D m * secondForwardDifference K D m| ≤
        B * ∑ m ∈ Finset.range M, |secondForwardDifference K D m| := by
    apply abs_biSum_mul_le (Finset.range M)
        (fun m => rectangularPrefix a D m)
        (fun m => secondForwardDifference K D m) B
    intro m hm
    exact hprefix D le_rfl m (Nat.le_of_lt (Finset.mem_range.mp hm))
  have hinterior :
      |∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
          rectangularPrefix a d m * mixedForwardDifference K d m| ≤
        B * ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
          |mixedForwardDifference K d m| := by
    apply abs_rectangular_biSum_mul_le
      (rectangularPrefix a) (mixedForwardDifference K) B D M
    intro d hd m hm
    exact hprefix d (Nat.le_of_lt (Finset.mem_range.mp hd))
      m (Nat.le_of_lt (Finset.mem_range.mp hm))
  calc
    |rectangularPrefix a D M * K D M +
        (∑ d ∈ Finset.range D,
          rectangularPrefix a d M * firstForwardDifference K d M) +
        (∑ m ∈ Finset.range M,
          rectangularPrefix a D m * secondForwardDifference K D m) +
        ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
          rectangularPrefix a d m * mixedForwardDifference K d m| ≤
      |rectangularPrefix a D M * K D M| +
        |∑ d ∈ Finset.range D,
          rectangularPrefix a d M * firstForwardDifference K d M| +
        |∑ m ∈ Finset.range M,
          rectangularPrefix a D m * secondForwardDifference K D m| +
        |∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
          rectangularPrefix a d m * mixedForwardDifference K d m| := by
        calc
          |(rectangularPrefix a D M * K D M +
              ∑ d ∈ Finset.range D,
                rectangularPrefix a d M * firstForwardDifference K d M) +
              (∑ m ∈ Finset.range M,
                rectangularPrefix a D m * secondForwardDifference K D m) +
              ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
                rectangularPrefix a d m * mixedForwardDifference K d m| ≤
            |(rectangularPrefix a D M * K D M +
              ∑ d ∈ Finset.range D,
                rectangularPrefix a d M * firstForwardDifference K d M) +
              (∑ m ∈ Finset.range M,
                rectangularPrefix a D m * secondForwardDifference K D m)| +
              |∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
                rectangularPrefix a d m * mixedForwardDifference K d m| :=
                  abs_add_le _ _
          _ ≤ (|rectangularPrefix a D M * K D M +
                ∑ d ∈ Finset.range D,
                  rectangularPrefix a d M * firstForwardDifference K d M| +
              |∑ m ∈ Finset.range M,
                rectangularPrefix a D m * secondForwardDifference K D m|) +
              |∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
                rectangularPrefix a d m * mixedForwardDifference K d m| := by
                  gcongr
                  exact abs_add_le _ _
          _ ≤ ((|rectangularPrefix a D M * K D M| +
                |∑ d ∈ Finset.range D,
                  rectangularPrefix a d M * firstForwardDifference K d M|) +
              |∑ m ∈ Finset.range M,
                rectangularPrefix a D m * secondForwardDifference K D m|) +
              |∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
                rectangularPrefix a d m * mixedForwardDifference K d m| := by
                  gcongr
                  exact abs_add_le _ _
    _ ≤ B * |K D M| +
        B * (∑ d ∈ Finset.range D, |firstForwardDifference K d M|) +
        B * (∑ m ∈ Finset.range M, |secondForwardDifference K D m|) +
        B * ∑ d ∈ Finset.range D, ∑ m ∈ Finset.range M,
          |mixedForwardDifference K d m| := by
        gcongr
    _ = B * rectangularVariation K D M := by
      unfold rectangularVariation
      ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmRectangularAbel
