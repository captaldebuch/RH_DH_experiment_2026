import RiemannHypothesis.Criteria.NymanBeurling.QuadraticInteraction

/-!
# Retired cellwise interface for the H15 Farey correlation debt

The original `FareyCellMobiusCorrelationEstimate` allowed an arbitrary weight
`w : ℕ → ℝ`, which is inconsistent with a logarithmic saving: a one-point
weight defeats any fixed saving as the ambient cutoff grows.  The geometric
weight class below does not repair that issue, because it still contains a
one-point weight after rescaling its envelope constant.

This file is retained as an exploratory record of finite Farey bookkeeping;
it is not the official H15 input and is not used by `FinalAssembly`.  The
corrected research target is `H15CenteredAggregateEstimate`, which bounds the
specific coupled cutoff-Möbius aggregate without independent cellwise weight
quantifiers.  No Chowla/DFI estimate is asserted here.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling
open RH.Criteria.NymanBeurling.CutoffMobiusKernels

/-! ## 1. Structured weights -/

/-- A simple, kernel-friendly weight class: a nonnegative amplitude controls a
geometrically decaying envelope.  The geometric envelope is stronger than a
bounded-variation condition, but is explicit and gives a uniform finite
`ℓ¹` bound without importing an analytic estimate. -/
def FareyCellWeightClass (w : ℕ → ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, |w m| ≤ A * ((1 / 2 : ℝ) ^ m)

theorem fareyCellWeightClass_l1_bound {w : ℕ → ℝ}
    (hw : FareyCellWeightClass w) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ M : ℕ, fareyCellWeightL1 M w ≤ C₀ := by
  rcases hw with ⟨A, hA, hdecay⟩
  refine ⟨A, hA, ?_⟩
  intro M
  unfold fareyCellWeightL1
  have hsum :
      (∑ m ∈ Finset.Icc 1 M, ((1 / 2 : ℝ) ^ m)) ≤ 1 := by
    by_cases hM : M = 0
    · simp [hM]
    · have hMpos : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
      have hgeom := geom_sum_Ico (x := (1 / 2 : ℝ)) (by norm_num)
        (m := 1) (n := M + 1) (by omega)
      have hIcc : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
        ext m
        simp
      rw [hIcc, hgeom]
      norm_num
      have hp : 0 ≤ ((1 / 2 : ℝ) ^ (M + 1)) :=
        pow_nonneg (by norm_num) _
      field_simp
      nlinarith
  calc
    ∑ x ∈ Finset.Icc 1 M, |w x|
        ≤ ∑ x ∈ Finset.Icc 1 M, A * ((1 / 2 : ℝ) ^ x) :=
      Finset.sum_le_sum (fun x hx => hdecay x)
    _ = A * (∑ x ∈ Finset.Icc 1 M, ((1 / 2 : ℝ) ^ x)) := by
      rw [Finset.mul_sum]
    _ ≤ A * 1 := by
      exact mul_le_mul_of_nonneg_left hsum hA
    _ = A := by ring

/-! ## 2. Finite Farey cells -/

/-- Two reduced fractions are Farey neighbours when their cross determinant has
absolute value one.  This is the arithmetic relation used by a future Farey
decomposition; no ordering convention is built into the definition. -/
def FareyNeighbor (a b c d : ℕ) : Prop :=
  |(a : ℤ) * d - (b : ℤ) * c| = 1

/-- The finite cell indexed by the mediant numerator/denominator sum `m`. -/
def fareyCellPairs (N m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 N).product (Finset.Icc 1 N) |>.filter (fun p =>
    p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ p.1 + p.2 = m)

theorem mem_fareyCellPairs_iff {N m : ℕ} {p : ℕ × ℕ} :
    p ∈ fareyCellPairs N m ↔
      p.1 ∈ Finset.Icc 1 N ∧ p.2 ∈ Finset.Icc 1 N ∧
        p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ p.1 + p.2 = m := by
  simp [fareyCellPairs, and_assoc, and_left_comm, and_comm]

theorem fareyCellPairs_disjoint {N m₁ m₂ : ℕ} {p : ℕ × ℕ}
    (hp₁ : p ∈ fareyCellPairs N m₁)
    (hp₂ : p ∈ fareyCellPairs N m₂) : m₁ = m₂ := by
  have h₁ := (mem_fareyCellPairs_iff.mp hp₁).2.2.2.2
  have h₂ := (mem_fareyCellPairs_iff.mp hp₂).2.2.2.2
  omega

theorem fareyCellPairs_cover {N : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N))
    (hlt : p.1 < p.2) (hcop : Nat.Coprime p.1 p.2) :
    p ∈ fareyCellPairs N (p.1 + p.2) := by
  have hp' := Finset.mem_product.mp hp
  exact mem_fareyCellPairs_iff.mpr ⟨hp'.1, hp'.2, hlt, hcop, rfl⟩

/-- Summing over all reduced ordered pairs with `h < k` is exactly the sum of
the corresponding mediant cells.  This is the finite mass-preservation
identity needed before inserting any analytic correlation estimate. -/
theorem fareyCellPairs_sum_partition (N : ℕ) (F : ℕ × ℕ → ℝ) :
    (∑ p ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N) |>.filter
        (fun p => p.1 < p.2 ∧ Nat.Coprime p.1 p.2), F p) =
      ∑ m ∈ Finset.Icc 2 (2 * N), ∑ p ∈ fareyCellPairs N m, F p := by
  let s : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 N).product (Finset.Icc 1 N) |>.filter
      (fun p => p.1 < p.2 ∧ Nat.Coprime p.1 p.2)
  let t : Finset ℕ := Finset.Icc 2 (2 * N)
  let g : ℕ × ℕ → ℕ := fun p => p.1 + p.2
  have hmap : ∀ p ∈ s, g p ∈ t := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprod := Finset.mem_product.mp hp'.1
    rcases hprod with ⟨hp1, hp2⟩
    simp only [g, t, Finset.mem_Icc] at hp1 hp2 ⊢
    constructor
    · omega
    · omega
  have hfiber := Finset.sum_fiberwise_of_maps_to (s := s) (t := t) hmap F
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro m hm
  apply congrArg (fun u : Finset (ℕ × ℕ) => ∑ p ∈ u, F p)
  ext p
  simp [s, fareyCellPairs, g, and_assoc, and_left_comm, and_comm]

/-! ## 3. Retired restricted correlation hypothesis -/

/-- An exploratory cellwise interface retained for its finite bookkeeping.
It is not a viable H15 hypothesis: `FareyCellWeightClass` admits point masses,
so a fixed logarithmic saving cannot hold uniformly over this class. -/
structure FareyCellMobiusCorrelationEstimate_Restricted where
  C_correlation : ℝ
  C_correlation_nonneg : 0 ≤ C_correlation
  correlation_bound :
    ∀ N g a q r s M : ℕ,
      ∀ w : ℕ → ℝ,
        g ∈ Finset.Icc 1 N →
          a ∈ Finset.Icc 1 (N / g) →
            q ∈ Finset.Icc 1 (N / g) →
              Nat.Coprime a q →
                r < a →
                  s < q →
                    M ∈ Finset.Icc 1 (N / g) →
                      FareyCellWeightClass w →
                        |fareyCellMobiusCorrelationSum a q r s M w| ≤
                          fareyCellLogSavingMajorant C_correlation N M w

/-! ## 4. Reusable decomposition and bridge -/

/-- Exact Farey-cell bookkeeping for the restricted interface.  Its fields are
structural decomposition and mass obligations, not the correlation estimate
itself. -/
structure FareyCellGcdSliceErrorDecomposition_Restricted
    (Hcorr : FareyCellMobiusCorrelationEstimate_Restricted)
    (mainTerm : ℕ → ℝ) where
  cellWeight : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ
  cellWeight_class :
    ∀ N g a q r s M : ℕ, FareyCellWeightClass (cellWeight N g a q r s M)
  errorMajorant : ℕ → ℕ → ℝ
  C_error : ℝ
  C_error_nonneg : 0 ≤ C_error
  errorMajorant_nonneg : ∀ N g : ℕ, 0 ≤ errorMajorant N g
  farey_cell_decomposition :
    ∀ N g : ℕ, g ∈ Finset.Icc 1 N →
      quadraticInteractionOffDiagonalGcdSlice N g - mainTerm g =
        fareyCellParameterSum N g (fun a q r s M =>
          fareyCellMobiusCorrelationSum a q r s M
            (cellWeight N g a q r s M))
  farey_cell_majorant_bound :
    ∀ N g : ℕ, g ∈ Finset.Icc 1 N →
      fareyCellParameterSum N g (fun a q r s M =>
        fareyCellLogSavingMajorant Hcorr.C_correlation N M
          (cellWeight N g a q r s M)) ≤ errorMajorant N g
  error_mass_bound :
    ∀ N : ℕ,
      (∑ g ∈ Finset.Icc 1 N, errorMajorant N g) ≤
        C_error / Real.log (N + 2 : ℝ)

theorem abs_fareyCellParameterSum_le_majorant
    (Hcorr : FareyCellMobiusCorrelationEstimate_Restricted)
    {mainTerm : ℕ → ℝ}
    (D : FareyCellGcdSliceErrorDecomposition_Restricted Hcorr mainTerm)
    (N g : ℕ) (hg : g ∈ Finset.Icc 1 N) :
    |fareyCellParameterSum N g (fun a q r s M =>
        fareyCellMobiusCorrelationSum a q r s M
          (D.cellWeight N g a q r s M))| ≤
      fareyCellParameterSum N g (fun a q r s M =>
        fareyCellLogSavingMajorant Hcorr.C_correlation N M
          (D.cellWeight N g a q r s M)) := by
  unfold fareyCellParameterSum
  let A := Finset.Icc 1 (N / g)
  have hcell : ∀ (a q r s M : ℕ),
      a ∈ A → q ∈ A.filter (fun q => Nat.Coprime a q) →
        r ∈ Finset.range a → s ∈ Finset.range q → M ∈ A →
      |fareyCellMobiusCorrelationSum a q r s M
          (D.cellWeight N g a q r s M)| ≤
        fareyCellLogSavingMajorant Hcorr.C_correlation N M
          (D.cellWeight N g a q r s M) := by
    intro a q r s M ha hq hr hs hM
    have hq' := Finset.mem_filter.mp hq
    exact Hcorr.correlation_bound N g a q r s M
      (D.cellWeight N g a q r s M) hg ha hq'.1 hq'.2
      (Finset.mem_range.mp hr) (Finset.mem_range.mp hs) hM
      (D.cellWeight_class N g a q r s M)
  calc
    |∑ a ∈ A, ∑ q ∈ A.filter (fun q => Nat.Coprime a q),
        ∑ r ∈ Finset.range a, ∑ s ∈ Finset.range q,
          ∑ M ∈ A, fareyCellMobiusCorrelationSum a q r s M
            (D.cellWeight N g a q r s M)|
        ≤ ∑ a ∈ A, |∑ q ∈ A.filter (fun q => Nat.Coprime a q),
            ∑ r ∈ Finset.range a, ∑ s ∈ Finset.range q,
              ∑ M ∈ A, fareyCellMobiusCorrelationSum a q r s M
                (D.cellWeight N g a q r s M)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, ∑ q ∈ A.filter (fun q => Nat.Coprime a q),
          |∑ r ∈ Finset.range a, ∑ s ∈ Finset.range q,
            ∑ M ∈ A, fareyCellMobiusCorrelationSum a q r s M
              (D.cellWeight N g a q r s M)| := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, ∑ q ∈ A.filter (fun q => Nat.Coprime a q),
          ∑ r ∈ Finset.range a, |∑ s ∈ Finset.range q,
            ∑ M ∈ A, fareyCellMobiusCorrelationSum a q r s M
              (D.cellWeight N g a q r s M)| := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, ∑ q ∈ A.filter (fun q => Nat.Coprime a q),
          ∑ r ∈ Finset.range a, ∑ s ∈ Finset.range q, |∑ M ∈ A,
            fareyCellMobiusCorrelationSum a q r s M
              (D.cellWeight N g a q r s M)| := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, ∑ q ∈ A.filter (fun q => Nat.Coprime a q),
          ∑ r ∈ Finset.range a, ∑ s ∈ Finset.range q, ∑ M ∈ A,
            |fareyCellMobiusCorrelationSum a q r s M
              (D.cellWeight N g a q r s M)| := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, ∑ q ∈ A.filter (fun q => Nat.Coprime a q),
          ∑ r ∈ Finset.range a, ∑ s ∈ Finset.range q, ∑ M ∈ A,
            fareyCellLogSavingMajorant Hcorr.C_correlation N M
              (D.cellWeight N g a q r s M) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro M hM
      exact hcell a q r s M ha hq hr hs hM

noncomputable def quadraticInteractionGcdSliceErrorEstimate_of_weightRestrictedCorrelation
    (Hcorr : FareyCellMobiusCorrelationEstimate_Restricted)
    (mainTerm : ℕ → ℝ)
    (D : FareyCellGcdSliceErrorDecomposition_Restricted Hcorr mainTerm) :
    QuadraticInteractionGcdSliceErrorEstimate mainTerm := by
  refine
    { errorMajorant := D.errorMajorant
      C_error := D.C_error
      C_error_nonneg := D.C_error_nonneg
      errorMajorant_nonneg := D.errorMajorant_nonneg
      slice_error_bound := ?_
      error_mass_bound := D.error_mass_bound }
  intro N g hg
  rw [D.farey_cell_decomposition N g hg]
  exact (abs_fareyCellParameterSum_le_majorant Hcorr D N g hg).trans
    (D.farey_cell_majorant_bound N g hg)

/-- The restricted Farey-cell package reaches the existing H15 estimate once
the independent BBLS main-term package, the exact cell bookkeeping, and the
already-separated smooth/residue bounds are supplied.  These extra arguments
are intentional: a binary correlation estimate alone cannot manufacture the
Farey decomposition or the other analytic sub-estimates. -/
noncomputable def quadraticInteractionEstimates_of_weightRestrictedCorrelation
    (Hcorr : FareyCellMobiusCorrelationEstimate_Restricted)
    (HBBLS : BBLS_EstermannContourPackage)
    (D : FareyCellGcdSliceErrorDecomposition_Restricted Hcorr HBBLS.mainTerm)
    (C_loggamma C_residue : ℝ)
    (C_pos :
      0 < C_loggamma +
        (quadraticInteractionDiagonalEstimate_zero.C_diagonal + D.C_error +
          HBBLS.C_main) + C_residue)
    (loggamma_bound :
      ∀ N : ℕ,
        |explicitQuadraticLogGammaComponent N| ≤ C_loggamma /
          Real.log (N + 2 : ℝ))
    (residue_bound :
      ∀ N : ℕ,
        |explicitCutoffResidueComponent N| ≤ C_residue /
          Real.log (N + 2 : ℝ)) :
    QuadraticInteractionEstimates :=
  quadraticInteractionEstimates_of_analytic_subEstimates
    (quadraticInteractionAnalyticSubEstimates_of_BBLS_and_gcdError HBBLS
      (quadraticInteractionGcdSliceErrorEstimate_of_weightRestrictedCorrelation
        Hcorr HBBLS.mainTerm D))
    C_loggamma C_residue C_pos loggamma_bound residue_bound

end RH.Criteria.NymanBeurling.QuadraticInteraction
