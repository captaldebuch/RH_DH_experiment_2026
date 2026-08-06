/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB6GlobalClosure

/-!
# NB7: a concrete approximation-sequence interface

The Nyman--Beurling criterion is existential at every positive tolerance.
Analytic constructions, including any future H15 construction, are usually
more naturally stated as one sequence of finite coefficient vectors whose
`L²` errors tend to zero.  This file proves that such data supply the exact
criterion used by NB4--NB6 and hence Mathlib's global Riemann hypothesis.

No instance of the structure below is asserted here.  Constructing one is the
remaining RH-strength problem.
-/

open Filter Set

namespace NBMellinTools.NB7

open NBMellinTools.NB2

/-- A sequence of finite Báez--Duarte approximants with certified vanishing
`L²(0,∞)` error. -/
structure BaezDuarteApproximationSequence where
  /-- Length of the `n`-th finite approximant. -/
  length : ℕ → ℕ
  /-- Coefficients of the `n`-th finite approximant. -/
  coeffs : ∀ n : ℕ, Fin (length n) → ℝ
  /-- The exact project error tends to zero. -/
  error_tendsto_zero :
    Tendsto
      (fun n : ℕ => BaezDuarteL2Error (length n) (coeffs n))
      atTop (nhds 0)

/-- A certified approximation sequence supplies the finite-approximation
Nyman--Beurling criterion. -/
theorem nymanBeurlingCriterion_of_approximationSequence
    (hseq : BaezDuarteApproximationSequence) :
    NymanBeurlingCriterion := by
  intro ε hε
  have heventually :
      ∀ᶠ n : ℕ in atTop,
        BaezDuarteL2Error (hseq.length n) (hseq.coeffs n) < ε :=
    hseq.error_tendsto_zero.eventually (Iio_mem_nhds hε)
  obtain ⟨n₀, hn₀⟩ := (eventually_atTop.1 heventually)
  exact ⟨hseq.length n₀, hseq.coeffs n₀, hn₀ n₀ le_rfl⟩

/-- Conversely, the tolerance-by-tolerance criterion can be organized into a
single vanishing-error sequence.  This is a choice/diagonalization lemma, not
an analytic estimate. -/
theorem nonempty_approximationSequence_of_nymanBeurlingCriterion
    (hcriterion : NymanBeurlingCriterion) :
    Nonempty BaezDuarteApproximationSequence := by
  classical
  have hchoice : ∀ n : ℕ,
      ∃ N : ℕ, ∃ coeffs : Fin N → ℝ,
        BaezDuarteL2Error N coeffs < 1 / ((n : ℝ) + 1) := by
    intro n
    exact hcriterion (1 / ((n : ℝ) + 1)) (by positivity)
  choose length coeffs hbound using hchoice
  refine ⟨{
    length := length
    coeffs := coeffs
    error_tendsto_zero := ?_
  }⟩
  exact squeeze_zero
    (fun n => baezDuarteL2Error_nonneg (length n) (coeffs n))
    (fun n => le_of_lt (hbound n))
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The active Nyman--Beurling criterion is exactly equivalent to the existence
of one certified vanishing-error approximation sequence. -/
theorem nymanBeurlingCriterion_iff_nonempty_approximationSequence :
    NymanBeurlingCriterion ↔ Nonempty BaezDuarteApproximationSequence := by
  constructor
  · exact nonempty_approximationSequence_of_nymanBeurlingCriterion
  · rintro ⟨hseq⟩
    exact nymanBeurlingCriterion_of_approximationSequence hseq

/-- The complete verified implication from concrete vanishing-error data to
Mathlib's global Riemann hypothesis. -/
theorem riemannHypothesis_of_approximationSequence
    (hseq : BaezDuarteApproximationSequence) :
    RiemannHypothesis :=
  NBMellinTools.NB6.riemannHypothesis_of_nymanBeurlingCriterion
    (nymanBeurlingCriterion_of_approximationSequence hseq)

end NBMellinTools.NB7
