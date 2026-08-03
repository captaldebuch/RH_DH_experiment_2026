import RiemannHypothesis.Criteria.NymanBeurling.QuadraticInteraction
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPeriodReduction

/-!
# H15 forward spine: Vaaler → exponential sums → DFI/Kloosterman

This module is deliberately a forward-facing interface, not an attempted
proof of the remaining quadratic estimate.  The existing
`FareyCellMobiusCorrelationEstimate` is the arithmetic endpoint already
identified for H15.  Here we record the two earlier stages that a future
analytic argument must supply:

* a Vaaler-type finite Fourier approximation to the Dedekind sawtooth
  `bernoulliB1`; and
* Type-I/Type-II exponential-sum estimates, including the Kloosterman-fraction
  form appearing after the Vaaler expansion.

The exact Farey-cell decomposition and weight bookkeeping remain the existing
`FareyCellGcdSliceErrorDecomposition` field.  Consequently the final bridge in
this file is purely structural and has no hidden analytic claim.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Criteria.NymanBeurling.CutoffMobiusKernels

/-! ## Explicit phase notation used by the exponential-sum stage -/

noncomputable def h15ExponentialPhase (α : ℝ) (n : ℕ) : ℂ :=
  Complex.exp ((((2 * Real.pi * α * (n : ℝ)) : ℝ) : ℂ) * Complex.I)

noncomputable def h15WeightedExponentialSum
    (M : ℕ) (α : ℝ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M, w n * h15ExponentialPhase α n

noncomputable def h15KloostermanFractionPhase
    (A m n : ℕ) : ℂ :=
  Complex.exp ((((2 * Real.pi * (A : ℝ) /
      ((m : ℝ) * (n : ℝ))) : ℝ) : ℂ) * Complex.I)

noncomputable def h15BilinearKloostermanFractionSum
    (M₁ M₂ A : ℕ) (u v : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M₁, ∑ n ∈ Finset.Icc 1 M₂,
    u m * v n * h15KloostermanFractionPhase A m n

theorem h15KloostermanFractionPhase_norm (A m n : ℕ) :
    ‖h15KloostermanFractionPhase A m n‖ = 1 := by
  unfold h15KloostermanFractionPhase
  exact Complex.norm_exp_ofReal_mul_I _

/-!
The reciprocal-phase layer is first split exactly by `gcd m n`.  This is
finite bookkeeping, not a cancellation estimate; the latter remains an
explicit analytic input below.  The split is useful because any DFI estimate
can now be stated stratum-by-stratum without silently assuming coprimality.
-/
noncomputable def h15BilinearKloostermanFractionGcdSlice
    (M₁ M₂ A g : ℕ) (u v : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M₁, ∑ n ∈ Finset.Icc 1 M₂,
    if Nat.gcd m n = g then
      u m * v n * h15KloostermanFractionPhase A m n
    else 0

theorem h15BilinearKloostermanFractionSum_eq_gcdSlice_sum
    (M₁ M₂ A : ℕ) (u v : ℕ → ℂ) :
    h15BilinearKloostermanFractionSum M₁ M₂ A u v =
      ∑ g ∈ Finset.Icc 1 (min M₁ M₂),
        h15BilinearKloostermanFractionGcdSlice M₁ M₂ A g u v := by
  classical
  unfold h15BilinearKloostermanFractionSum
    h15BilinearKloostermanFractionGcdSlice
  symm
  calc
    (∑ g ∈ Finset.Icc 1 (min M₁ M₂),
        ∑ m ∈ Finset.Icc 1 M₁, ∑ n ∈ Finset.Icc 1 M₂,
          if Nat.gcd m n = g then
            u m * v n * h15KloostermanFractionPhase A m n else 0) =
        ∑ m ∈ Finset.Icc 1 M₁, ∑ g ∈ Finset.Icc 1 (min M₁ M₂),
          ∑ n ∈ Finset.Icc 1 M₂,
            if Nat.gcd m n = g then
              u m * v n * h15KloostermanFractionPhase A m n else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.Icc 1 M₁, ∑ n ∈ Finset.Icc 1 M₂,
          ∑ g ∈ Finset.Icc 1 (min M₁ M₂),
            if Nat.gcd m n = g then
              u m * v n * h15KloostermanFractionPhase A m n else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.Icc 1 M₁, ∑ n ∈ Finset.Icc 1 M₂,
          u m * v n * h15KloostermanFractionPhase A m n := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hgcd_mem : Nat.gcd m n ∈ Finset.Icc 1 (min M₁ M₂) := by
        apply Finset.mem_Icc.mpr
        constructor
        · exact Nat.gcd_pos_of_pos_left n hmpos
        · exact le_min
            ((Nat.gcd_le_left n hmpos).trans (Finset.mem_Icc.mp hm).2)
            ((Nat.gcd_le_right m hnpos).trans (Finset.mem_Icc.mp hn).2)
      rw [Finset.sum_eq_single (Nat.gcd m n)]
      · simp
      · intro b hb hbg
        have hne : Nat.gcd m n ≠ b := Ne.symm hbg
        simp [hne]
      · intro hnot
        exact (hnot hgcd_mem).elim

/-! ## The W₁/bracket interface -/

/-
The first Fourier mode is the positive mode `m = 1` in the already proved
BBLS partial-sum decomposition.  The bracket is defined as the remaining
partial-sum limit.  Thus the following identity is exact; no convergence or
rearrangement assumption is introduced here.
-/
noncomputable def h15WOneComponent (N : ℕ) : ℝ :=
  cutoffMobiusBernoulliMode N 1

noncomputable def h15WOneBracket (N : ℕ) : ℝ :=
  cutoffMobiusBernoulliCorrelationValue N - h15WOneComponent N

theorem h15WOne_plus_bracket_eq_correlation (N : ℕ) :
    h15WOneComponent N + h15WOneBracket N =
      cutoffMobiusBernoulliCorrelationValue N := by
  unfold h15WOneBracket
  ring

/-
The diagnostics in `experiments/phase15_mode_split_bracket.py` show that the
safe split is asymmetric: `W₁ - 1` is controlled at the visible `1/log`
scale, while the paired logarithmic/bracket/linear term is the candidate
`1/log²` remainder.  We freeze those rates as separate fields rather than
claiming the stronger old centered `1/log²` interface.
-/
structure H15WOneBracketEstimate
    (_H : MobiusSummatory.ClassicalMertensDecay) where
  C_w1 : ℝ
  C_bracket : ℝ
  C_w1_nonneg : 0 ≤ C_w1
  C_bracket_nonneg : 0 ≤ C_bracket
  w1_minus_one_bound :
    ∀ N : ℕ,
      |h15WOneComponent N - 1| ≤ C_w1 / Real.log (N + 2 : ℝ)
  bracket_bound :
    ∀ N : ℕ,
      |explicitQuadraticLogRatioComponent N + h15WOneBracket N +
          2 * (explicitLinearMobiusSum N + 1)| ≤
        C_bracket / Real.log (N + 2 : ℝ) ^ 2

structure H15CenteredOLogEstimate where
  C_centered : ℝ
  C_centered_nonneg : 0 ≤ C_centered
  centered_bound :
    ∀ N : ℕ,
      |explicitQuadraticLogRatioComponent N +
          cutoffMobiusBernoulliCorrelationValue N - 1 +
            2 * (explicitLinearMobiusSum N + 1)| ≤
        C_centered / Real.log (N + 2 : ℝ)

noncomputable def h15CenteredOLogEstimate_of_w1Bracket
    (W : H15WOneBracketEstimate H) : H15CenteredOLogEstimate := by
  let logTwo := Real.log (2 : ℝ)
  refine
    { C_centered := W.C_w1 + W.C_bracket / logTwo
      C_centered_nonneg := add_nonneg W.C_w1_nonneg
        (div_nonneg W.C_bracket_nonneg (Real.log_pos (by norm_num)).le)
      centered_bound := ?_ }
  intro N
  have hlogTwo : 0 < logTwo := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log (N + 2 : ℝ) :=
    Real.log_pos (by norm_cast; omega)
  have hmono : logTwo ≤ Real.log (N + 2 : ℝ) := by
    exact Real.log_le_log (by norm_num) (by norm_cast; omega)
  have hbracket :
      W.C_bracket / Real.log (N + 2 : ℝ) ^ 2 ≤
        (W.C_bracket / logTwo) / Real.log (N + 2 : ℝ) := by
    calc
      W.C_bracket / Real.log (N + 2 : ℝ) ^ 2 =
          (W.C_bracket / Real.log (N + 2 : ℝ)) /
            Real.log (N + 2 : ℝ) := by ring
      _ ≤ (W.C_bracket / logTwo) /
            Real.log (N + 2 : ℝ) := by
        exact div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_left W.C_bracket_nonneg hlogTwo hmono)
          hlogN.le
  have hsplit :
      explicitQuadraticLogRatioComponent N +
          cutoffMobiusBernoulliCorrelationValue N - 1 +
            2 * (explicitLinearMobiusSum N + 1) =
        (h15WOneComponent N - 1) +
          (explicitQuadraticLogRatioComponent N + h15WOneBracket N +
            2 * (explicitLinearMobiusSum N + 1)) := by
    rw [← h15WOne_plus_bracket_eq_correlation]
    ring
  rw [hsplit]
  calc
    |h15WOneComponent N - 1 +
          (explicitQuadraticLogRatioComponent N + h15WOneBracket N +
            2 * (explicitLinearMobiusSum N + 1))|
        ≤ |h15WOneComponent N - 1| +
            |explicitQuadraticLogRatioComponent N + h15WOneBracket N +
              2 * (explicitLinearMobiusSum N + 1)| :=
          abs_add_le _ _
    _ ≤ W.C_w1 / Real.log (N + 2 : ℝ) +
          W.C_bracket / Real.log (N + 2 : ℝ) ^ 2 := by
          exact add_le_add (W.w1_minus_one_bound N) (W.bracket_bound N)
    _ ≤ W.C_w1 / Real.log (N + 2 : ℝ) +
          (W.C_bracket / logTwo) / Real.log (N + 2 : ℝ) := by
          exact add_le_add (le_refl _) hbracket
    _ = (W.C_w1 + W.C_bracket / logTwo) /
          Real.log (N + 2 : ℝ) := by ring

/-! ## Reciprocal phases and the DFI stop-gates -/

/-- A concrete, normalized gcd-stratum majorant for reciprocal phases. -/
structure H15ReciprocalPhaseGcdCancellation where
  majorant : ℕ → ℕ → ℕ → ℕ → ℝ
  majorant_nonneg :
    ∀ M₁ M₂ A g : ℕ, 0 ≤ majorant M₁ M₂ A g
  gcd_slice_bound :
    ∀ (M₁ M₂ A g : ℕ) (u v : ℕ → ℂ),
      (∀ m : ℕ, ‖u m‖ ≤ 1) → (∀ n : ℕ, ‖v n‖ ≤ 1) →
      ‖h15BilinearKloostermanFractionGcdSlice M₁ M₂ A g u v‖ ≤
        majorant M₁ M₂ A g

/-- The expert DFI/Weil input is left as a named proposition until its exact
weight class, dyadic ranges, and saving are selected from the theorem to be
formalized.  The phase and its gcd decomposition above are fully concrete. -/
structure H15KloostermanDFIInput where
  estimate : Prop
  estimate_holds : estimate

/-! ## The Vaaler stage -/

/--
A content-bearing Vaaler package for the project’s Dedekind-sawtooth
convention.  `finite_fourier_expansion` is kept as a proposition-valued field
because the exact coefficient normalization (and the endpoint convention at
integers) must be fixed from the chosen Vaaler theorem before formalization.
The sandwich and nonnegativity fields are the statements used by the later
error bookkeeping.
-/
structure H15VaalerSawtoothPackage where
  approximant : ℕ → ℝ → ℝ
  errorMajorant : ℕ → ℝ → ℝ
  errorMajorant_nonneg : ∀ J : ℕ, ∀ x : ℝ, 0 ≤ errorMajorant J x
  uniform_error :
    ∀ J : ℕ, ∀ x : ℝ,
      |bernoulliB1 x - approximant J x| ≤ errorMajorant J x
  finite_fourier_expansion : Prop
  finite_fourier_expansion_holds : finite_fourier_expansion

structure H15ThreeLayerBernoulliPairPackage
    (H : MobiusSummatory.ClassicalMertensDecay) where
  vaaler : H15VaalerSawtoothPackage
  reciprocalPhase : H15ReciprocalPhaseGcdCancellation
  dfi : H15KloostermanDFIInput
  w1Bracket : H15WOneBracketEstimate H

noncomputable def h15ThreeLayer_uniform_O_log
    (S : H15ThreeLayerBernoulliPairPackage H) :
    H15CenteredOLogEstimate :=
  h15CenteredOLogEstimate_of_w1Bracket S.w1Bracket

/-! ## The exponential-sum stage -/

/--
The exponential-sum obligations exposed by the Vaaler expansion.  The three
fields are intentionally propositions rather than guessed universal
inequalities: their admissible smooth weights, dyadic ranges, and savings must
be frozen from the DFI/Kloosterman theorem actually selected.  Their intended
objects are `h15WeightedExponentialSum` (Type I) and
`h15BilinearKloostermanFractionSum` (Type II/Kloosterman fractions).
-/
structure H15ExponentialSumPackage where
  typeI_estimate : Prop
  typeI_estimate_holds : typeI_estimate
  typeII_estimate : Prop
  typeII_estimate_holds : typeII_estimate
  kloosterman_fraction_estimate : Prop
  kloosterman_fraction_estimate_holds : kloosterman_fraction_estimate

/-! ## Assembly into the existing Farey-cell endpoint -/

/--
The forward-spine package.  `mainTerm` is the same BBLS main term used by
`QuadraticInteractionGcdSliceErrorEstimate`.  The Vaaler and exponential
packages document the analytic route; `decomposition` is the exact finite
Farey-cell reduction and mass bookkeeping that turns its output into the
existing gcd-slice error interface.
-/
structure H15VaalerExponentialDFIPackage
    (H : MobiusSummatory.ClassicalMertensDecay)
    (mainTerm : ℕ → ℝ) where
  vaaler : H15VaalerSawtoothPackage
  exponentialSums : H15ExponentialSumPackage
  fareyCorrelation : FareyCellMobiusCorrelationEstimate
  decomposition :
    FareyCellGcdSliceErrorDecomposition fareyCorrelation mainTerm

/-- The DFI/Farey reduction discharges the abstract H15 gcd-slice error field. -/
noncomputable def quadraticInteractionGcdSliceErrorEstimate_of_forward_spine
    {H : MobiusSummatory.ClassicalMertensDecay} {mainTerm : ℕ → ℝ}
    (S : H15VaalerExponentialDFIPackage H mainTerm) :
    QuadraticInteractionGcdSliceErrorEstimate mainTerm :=
  quadraticInteractionGcdSliceErrorEstimate_of_fareyCellCorrelation
    S.fareyCorrelation mainTerm S.decomposition

/--
With the BBLS main-term package, the forward spine reaches the already-proved
analytic-subestimate assembly.  The only non-mechanical content remains in
the Vaaler, exponential-sum, and Farey decomposition fields above.
-/
noncomputable def quadraticInteractionAnalyticSubEstimates_of_forward_spine
    {H : MobiusSummatory.ClassicalMertensDecay}
    (B : BBLS_EstermannContourPackage)
    (S : H15VaalerExponentialDFIPackage H B.mainTerm) :
    QuadraticInteractionAnalyticSubEstimates := by
  exact quadraticInteractionAnalyticSubEstimates_of_BBLS_and_gcdError B
    (quadraticInteractionGcdSliceErrorEstimate_of_forward_spine S)

end RH.Criteria.NymanBeurling.QuadraticInteraction
