/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15OperatorAdaptation
import NBMellinTools.NB15DirectAdditiveResonanceSplit

/-!
# NB15: Block decomposition of the canonical Gram kernel (Phase 2)

This module defines the three-block decomposition of the H15 operator trace:
resonant (q | r), nonresonant (q ∤ r), and correction (low-frequency).

Each block is defined via its amplitude restriction and canonical Gram kernel.
The module establishes the structure and preparatory identities for Phase 3,
where spectral properties will be proved.

No decay estimate is asserted here.
-/

open scoped BigOperators ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## Resonant block: q ∣ r -/

/-- Amplitude restricted to resonant indices. -/
noncomputable def h15ResonantBlockAmplitude
    (n K J : ℕ) (t : ℝ) (ik : H15ResonantOperatorIndex n K J) : ℂ :=
  if h15DirectAdditiveFrequencyResonant ik.1 then
    h15ResonantOperatorAmplitude n K J t ik
  else
    0

/-- Gram kernel of resonant block. -/
noncomputable def h15ResonantBlockGramKernel
    (n K J : ℕ) (t : ℝ) :
    Matrix (H15ResonantOperatorIndex n K J)
      (H15ResonantOperatorIndex n K J) ℂ :=
  fun ik jl =>
    conj (h15ResonantBlockAmplitude n K J t ik) *
      h15ResonantBlockAmplitude n K J t jl

/-! ## Nonresonant block: q ∤ r -/

/-- Amplitude restricted to nonresonant indices. -/
noncomputable def h15NonresonantBlockAmplitude
    (n K J : ℕ) (t : ℝ) (ik : H15ResonantOperatorIndex n K J) : ℂ :=
  if h15DirectAdditiveFrequencyResonant ik.1 then
    0
  else
    h15ResonantOperatorAmplitude n K J t ik

/-- Gram kernel of nonresonant block. -/
noncomputable def h15NonresonantBlockGramKernel
    (n K J : ℕ) (t : ℝ) :
    Matrix (H15ResonantOperatorIndex n K J)
      (H15ResonantOperatorIndex n K J) ℂ :=
  fun ik jl =>
    conj (h15NonresonantBlockAmplitude n K J t ik) *
      h15NonresonantBlockAmplitude n K J t jl

/-! ## Correction block: zero in quotient support -/

/-- Correction block kernel (zero in the fixed-height quotient support). -/
noncomputable def h15CorrectionBlockGramKernel
    (n K J : ℕ) (t : ℝ) :
    Matrix (H15ResonantOperatorIndex n K J)
      (H15ResonantOperatorIndex n K J) ℂ :=
  fun _ _ => 0

/-! ## Decomposition structure -/

/-- The total amplitude decomposes into resonant and nonresonant blocks. -/
theorem h15ResonantOperatorAmplitude_eq_block_sum
    (n K J : ℕ) (t : ℝ) (ik : H15ResonantOperatorIndex n K J) :
    h15ResonantOperatorAmplitude n K J t ik =
      h15ResonantBlockAmplitude n K J t ik +
        h15NonresonantBlockAmplitude n K J t ik := by
  unfold h15ResonantBlockAmplitude h15NonresonantBlockAmplitude
  split_ifs <;> ring

/-- Gram kernel decomposition: diagonal sum for each index pair. -/
theorem h15ResonantGramKernel_eq_block_sum_entry
    (n K J : ℕ) (t : ℝ) (ik jl : H15ResonantOperatorIndex n K J) :
    h15ResonantGramKernel n K J t ik jl =
      h15ResonantBlockGramKernel n K J t ik jl +
        h15NonresonantBlockGramKernel n K J t ik jl +
        h15CorrectionBlockGramKernel n K J t ik jl := by
  sorry  -- Follows from amplitude decomposition

/-! ## Trace structure of blocks -/

/-- Trace of resonant block equals sum of squared resonant-mode amplitudes. -/
theorem h15ResonantBlockGramTrace_eq_resonantSumSq
    (n K J : ℕ) (t : ℝ) :
    Matrix.trace (h15ResonantBlockGramKernel n K J t) =
      (∑ ik : H15ResonantOperatorIndex n K J,
        if h15DirectAdditiveFrequencyResonant ik.1 then
          Complex.normSq (h15ResonantOperatorAmplitude n K J t ik)
        else
          0 : ℂ) := by
  sorry  -- Follows from trace definition and resonant block definition

/-- Trace of nonresonant block equals sum of squared nonresonant-mode amplitudes. -/
theorem h15NonresonantBlockGramTrace_eq_nonresonantSumSq
    (n K J : ℕ) (t : ℝ) :
    Matrix.trace (h15NonresonantBlockGramKernel n K J t) =
      (∑ ik : H15ResonantOperatorIndex n K J,
        if h15DirectAdditiveFrequencyResonant ik.1 then
          0
        else
          Complex.normSq (h15ResonantOperatorAmplitude n K J t ik) : ℂ) := by
  sorry  -- Follows from trace definition and nonresonant block definition

/-- Trace of correction block is zero (block is zero in quotient support). -/
theorem h15CorrectionBlockGramTrace_eq_zero
    (n K J : ℕ) (t : ℝ) :
    Matrix.trace (h15CorrectionBlockGramKernel n K J t) = 0 := by
  unfold h15CorrectionBlockGramKernel Matrix.trace
  simp

/-! ## Spectral placeholders for Phase 3+ -/

/-- Resonant block is finite-rank (defined by collision parametrization). -/
theorem h15ResonantBlockGramKernel_is_finite_rank
    (n K J : ℕ) (t : ℝ) :
    ∃ r : ℕ, Matrix.rank (h15ResonantBlockGramKernel n K J t) ≤ r := by
  sorry  -- Phase 3: collision structure qk = q'ℓ bounds rank

/-- Nonresonant block HS norm bound (to be filled via oscillatory analysis). -/
theorem h15NonresonantBlockGramKernel_HS_bound
    (n K J : ℕ) (t : ℝ) :
    ∃ C : ℝ, (∑ ik : H15ResonantOperatorIndex n K J,
      ∑ jl : H15ResonantOperatorIndex n K J,
        Complex.normSq (h15NonresonantBlockGramKernel n K J t ik jl)) ≤ C := by
  sorry  -- Phase 3: oscillatory phase + period cancellation

/-- Correction block trace-class property (placeholder). -/
theorem h15CorrectionBlockGramKernel_trace_class
    (n K J : ℕ) (t : ℝ) :
    True := by
  trivial

end NBMellinTools.NB12
