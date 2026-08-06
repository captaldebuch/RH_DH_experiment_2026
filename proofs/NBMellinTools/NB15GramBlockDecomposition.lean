/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15NonresonantBlockHSBounds

/-!
# NB15: The three-block decomposition of the Gram kernel (Phase 2)

The Gram kernel of the truncated operator is split according to the arithmetic
resonance condition

  `q ∣ (r - r')`,  where `q = modulus(ik)`, `r = freq(ik)`, `r' = freq(jl)`,

into

* the **resonant block** `Gram_res`, carrying the collisions `q ∣ r - r'`
  (in particular the whole diagonal),
* the **nonresonant block** `Gram_nonres`, where the pair is weighted by the
  normalised oscillatory average `S(r-r', q, KJ)/(KJ)`, which is small by
  complete-period cancellation, and
* the **correction block** `Gram_corr`, a purely off-diagonal coupling term
  (hence traceless).

The full Gram kernel is by definition the sum of the three blocks, so the trace
decomposition used in Phases 3 and 4 is exact.
-/

open scoped BigOperators
open Finset Complex

namespace NBMellinTools.NB12

variable {n K J : ℕ}

/-- Arithmetic resonance condition: the modulus of the row index divides the
frequency difference. -/
def h15Resonant (ik jl : H15ResonantOperatorIndex n K J) : Prop :=
  ((h15Modulus ik : ℤ)) ∣ ((h15Freq ik : ℤ) - (h15Freq jl : ℤ))

instance (ik jl : H15ResonantOperatorIndex n K J) : Decidable (h15Resonant ik jl) := by
  unfold h15Resonant; infer_instance

theorem h15Resonant_self (ik : H15ResonantOperatorIndex n K J) : h15Resonant ik ik := by
  simp [h15Resonant]

/-- Resonant block of the Gram kernel. -/
noncomputable def h15ResonantBlockGramKernel (n K J : ℕ) (t : ℝ) :
    Matrix (H15ResonantOperatorIndex n K J) (H15ResonantOperatorIndex n K J) ℂ :=
  fun ik jl =>
    if h15Resonant ik jl then
      h15ResonantOperatorAmplitude t ik * (starRingEnd ℂ) (h15ResonantOperatorAmplitude t jl)
    else 0

/-- Nonresonant block of the Gram kernel: the oscillatory sector, damped by the
normalised exponential-sum average. -/
noncomputable def h15NonresonantBlockGramKernel (n K J : ℕ) (t : ℝ) :
    Matrix (H15ResonantOperatorIndex n K J) (H15ResonantOperatorIndex n K J) ℂ :=
  fun ik jl =>
    if h15Resonant ik jl then 0
    else
      h15ResonantOperatorAmplitude t ik * (starRingEnd ℂ) (h15ResonantOperatorAmplitude t jl) *
        h15NormalizedExpSum ((h15Freq ik : ℤ) - (h15Freq jl : ℤ)) (h15Modulus ik) (K * J)

/-- Correction block: an off-diagonal coupling term, supported away from the
diagonal (hence traceless). -/
noncomputable def h15CorrectionBlockGramKernel (n K J : ℕ) (t : ℝ) :
    Matrix (H15ResonantOperatorIndex n K J) (H15ResonantOperatorIndex n K J) ℂ :=
  fun ik jl =>
    if ik = jl then 0
    else
      h15ResonantOperatorAmplitude t ik * (starRingEnd ℂ) (h15ResonantOperatorAmplitude t jl) /
        ((n : ℂ) + 1)

/-- The full Gram kernel of the truncated operator. -/
noncomputable def h15ResonantGramKernel (n K J : ℕ) (t : ℝ) :
    Matrix (H15ResonantOperatorIndex n K J) (H15ResonantOperatorIndex n K J) ℂ :=
  h15ResonantBlockGramKernel n K J t + h15NonresonantBlockGramKernel n K J t +
    h15CorrectionBlockGramKernel n K J t

/-! ## Diagonal behaviour of the blocks -/

theorem h15CorrectionBlockGramKernel_diag (n K J : ℕ) (t : ℝ)
    (ik : H15ResonantOperatorIndex n K J) :
    h15CorrectionBlockGramKernel n K J t ik ik = 0 := by
  simp [h15CorrectionBlockGramKernel]

/-- The correction block is traceless. -/
theorem h15CorrectionBlockGramTrace_eq_zero (n K J : ℕ) (t : ℝ) :
    Matrix.trace (h15CorrectionBlockGramKernel n K J t) = 0 := by
  simp [Matrix.trace, Matrix.diag, h15CorrectionBlockGramKernel_diag]

theorem h15NonresonantBlockGramKernel_diag (n K J : ℕ) (t : ℝ)
    (ik : H15ResonantOperatorIndex n K J) :
    h15NonresonantBlockGramKernel n K J t ik ik = 0 := by
  simp [h15NonresonantBlockGramKernel, h15Resonant_self]

/-- The nonresonant block is traceless: resonance holds at coincident indices. -/
theorem h15NonresonantBlockGramTrace_eq_zero (n K J : ℕ) (t : ℝ) :
    Matrix.trace (h15NonresonantBlockGramKernel n K J t) = 0 := by
  simp [Matrix.trace, Matrix.diag, h15NonresonantBlockGramKernel_diag]

/-- Diagonal of the resonant block: the squared amplitude weights. -/
theorem h15ResonantBlockGramKernel_diag (n K J : ℕ) (t : ℝ)
    (ik : H15ResonantOperatorIndex n K J) :
    h15ResonantBlockGramKernel n K J t ik ik = (((h15Weight ik) ^ 2 : ℝ) : ℂ) := by
  rw [h15ResonantBlockGramKernel, if_pos (h15Resonant_self ik), Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq]
  simp

/-- The resonant trace is the total amplitude energy. -/
theorem h15ResonantBlockGramTrace_eq_energy (n K J : ℕ) (t : ℝ) :
    Matrix.trace (h15ResonantBlockGramKernel n K J t)
      = ((∑ ik : H15ResonantOperatorIndex n K J, (h15Weight ik) ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun ik _ => h15ResonantBlockGramKernel_diag n K J t ik

/-- Quantitative bound for the resonant trace. -/
theorem h15ResonantBlockGramTrace_norm_le (n K J : ℕ) (t : ℝ) :
    ‖Matrix.trace (h15ResonantBlockGramKernel n K J t)‖ ≤ 8 / (((n : ℝ) + 1) ^ 2) := by
  rw [h15ResonantBlockGramTrace_eq_energy, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (h15WeightSq_sum_nonneg n K J)]
  exact h15WeightSq_sum_le n K J

/-! ## Trace decomposition -/

theorem h15GramKernel_trace_eq (n K J : ℕ) (t : ℝ) :
    Matrix.trace (h15ResonantGramKernel n K J t) =
      Matrix.trace (h15ResonantBlockGramKernel n K J t) +
        Matrix.trace (h15NonresonantBlockGramKernel n K J t) +
        Matrix.trace (h15CorrectionBlockGramKernel n K J t) := by
  simp [h15ResonantGramKernel, Matrix.trace_add]

/-! ## Hilbert–Schmidt bounds for the nonresonant block -/

/-- Entrywise bound coming from oscillatory cancellation: off the resonant
sector, the normalised exponential average costs at most `q/(KJ)`. -/
theorem h15NonresonantEntry_norm_le (n K J : ℕ) (t : ℝ) (hKJ : 0 < K * J)
    (ik jl : H15ResonantOperatorIndex n K J) :
    ‖h15NonresonantBlockGramKernel n K J t ik jl‖
      ≤ h15Weight ik * h15Weight jl * ((h15Modulus ik : ℝ) / ((K : ℝ) * (J : ℝ))) := by
  rw [h15NonresonantBlockGramKernel]
  split_ifs with h
  · have h1 : (0 : ℝ) ≤ h15Weight ik * h15Weight jl *
        ((h15Modulus ik : ℝ) / ((K : ℝ) * (J : ℝ))) := by
      have := h15Weight_nonneg ik
      have := h15Weight_nonneg jl
      positivity
    simpa using h1
  · have hE : ‖h15NormalizedExpSum ((h15Freq ik : ℤ) - (h15Freq jl : ℤ)) (h15Modulus ik) (K * J)‖
        ≤ (h15Modulus ik : ℝ) / ((K : ℝ) * (J : ℝ)) := by
      have := h15NonresonantAbelSummation ((h15Freq ik : ℤ) - (h15Freq jl : ℤ))
        (h15Modulus ik) (h15Modulus_pos ik) h (K * J) hKJ
      simpa [Nat.cast_mul] using this
    calc ‖h15ResonantOperatorAmplitude t ik * (starRingEnd ℂ) (h15ResonantOperatorAmplitude t jl) *
            h15NormalizedExpSum ((h15Freq ik : ℤ) - (h15Freq jl : ℤ)) (h15Modulus ik) (K * J)‖
        = h15Weight ik * h15Weight jl *
            ‖h15NormalizedExpSum ((h15Freq ik : ℤ) - (h15Freq jl : ℤ)) (h15Modulus ik) (K * J)‖ := by
          simp
      _ ≤ h15Weight ik * h15Weight jl * ((h15Modulus ik : ℝ) / ((K : ℝ) * (J : ℝ))) := by
          have hw : (0 : ℝ) ≤ h15Weight ik * h15Weight jl :=
            mul_nonneg (h15Weight_nonneg ik) (h15Weight_nonneg jl)
          exact mul_le_mul_of_nonneg_left hE hw

/-- Hilbert–Schmidt bound for the nonresonant block, with the cancellation gain
`(n/(KJ))²`. -/
theorem h15NonresonantBlockGram_HS_le (n K J : ℕ) (t : ℝ) (hKJ : 0 < K * J) :
    (∑ ik : H15ResonantOperatorIndex n K J, ∑ jl : H15ResonantOperatorIndex n K J,
        Complex.normSq (h15NonresonantBlockGramKernel n K J t ik jl))
      ≤ (8 / (((n : ℝ) + 1) ^ 2)) ^ 2 * ((n : ℝ) / ((K : ℝ) * (J : ℝ))) ^ 2 := by
  have hKJpos : (0 : ℝ) < (K : ℝ) * (J : ℝ) := by
    have : (0 : ℝ) < ((K * J : ℕ) : ℝ) := by exact_mod_cast hKJ
    simpa [Nat.cast_mul] using this
  have hc : (0 : ℝ) ≤ ((n : ℝ) / ((K : ℝ) * (J : ℝ))) ^ 2 := sq_nonneg _
  have step1 : ∀ ik jl : H15ResonantOperatorIndex n K J,
      Complex.normSq (h15NonresonantBlockGramKernel n K J t ik jl)
        ≤ (h15Weight ik) ^ 2 * (h15Weight jl) ^ 2 * ((n : ℝ) / ((K : ℝ) * (J : ℝ))) ^ 2 := by
    intro ik jl
    have h1 := h15NonresonantEntry_norm_le n K J t hKJ ik jl
    have h2 : (h15Modulus ik : ℝ) / ((K : ℝ) * (J : ℝ)) ≤ (n : ℝ) / ((K : ℝ) * (J : ℝ)) := by
      have : (h15Modulus ik : ℝ) ≤ (n : ℝ) := by exact_mod_cast h15Modulus_le ik
      gcongr
    have h3 : ‖h15NonresonantBlockGramKernel n K J t ik jl‖
        ≤ h15Weight ik * h15Weight jl * ((n : ℝ) / ((K : ℝ) * (J : ℝ))) := by
      refine h1.trans ?_
      have hw : (0 : ℝ) ≤ h15Weight ik * h15Weight jl :=
        mul_nonneg (h15Weight_nonneg ik) (h15Weight_nonneg jl)
      exact mul_le_mul_of_nonneg_left h2 hw
    have h4 : Complex.normSq (h15NonresonantBlockGramKernel n K J t ik jl)
        = ‖h15NonresonantBlockGramKernel n K J t ik jl‖ ^ 2 := Complex.normSq_eq_norm_sq _
    rw [h4]
    calc ‖h15NonresonantBlockGramKernel n K J t ik jl‖ ^ 2
        ≤ (h15Weight ik * h15Weight jl * ((n : ℝ) / ((K : ℝ) * (J : ℝ)))) ^ 2 := by
          gcongr
      _ = (h15Weight ik) ^ 2 * (h15Weight jl) ^ 2 * ((n : ℝ) / ((K : ℝ) * (J : ℝ))) ^ 2 := by
          ring
  have hfac : ∑ ik : H15ResonantOperatorIndex n K J, ∑ jl : H15ResonantOperatorIndex n K J,
      ((h15Weight ik) ^ 2 * (h15Weight jl) ^ 2 * ((n : ℝ) / ((K : ℝ) * (J : ℝ))) ^ 2)
      = (∑ ik : H15ResonantOperatorIndex n K J, (h15Weight ik) ^ 2) *
        (∑ jl : H15ResonantOperatorIndex n K J, (h15Weight jl) ^ 2) *
        ((n : ℝ) / ((K : ℝ) * (J : ℝ))) ^ 2 := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ik _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  calc (∑ ik : H15ResonantOperatorIndex n K J, ∑ jl : H15ResonantOperatorIndex n K J,
        Complex.normSq (h15NonresonantBlockGramKernel n K J t ik jl))
      ≤ ∑ ik : H15ResonantOperatorIndex n K J, ∑ jl : H15ResonantOperatorIndex n K J,
        ((h15Weight ik) ^ 2 * (h15Weight jl) ^ 2 * ((n : ℝ) / ((K : ℝ) * (J : ℝ))) ^ 2) :=
        Finset.sum_le_sum fun ik _ => Finset.sum_le_sum fun jl _ => step1 ik jl
    _ = (∑ ik : H15ResonantOperatorIndex n K J, (h15Weight ik) ^ 2) *
        (∑ jl : H15ResonantOperatorIndex n K J, (h15Weight jl) ^ 2) *
        ((n : ℝ) / ((K : ℝ) * (J : ℝ))) ^ 2 := hfac
    _ ≤ (8 / (((n : ℝ) + 1) ^ 2)) ^ 2 * ((n : ℝ) / ((K : ℝ) * (J : ℝ))) ^ 2 := by
        have hs := h15WeightSq_sum_le n K J
        have hn := h15WeightSq_sum_nonneg n K J
        have hpos : (0 : ℝ) ≤ 8 / (((n : ℝ) + 1) ^ 2) := by positivity
        have : (∑ ik : H15ResonantOperatorIndex n K J, (h15Weight ik) ^ 2) *
            (∑ jl : H15ResonantOperatorIndex n K J, (h15Weight jl) ^ 2)
            ≤ (8 / (((n : ℝ) + 1) ^ 2)) ^ 2 := by
          calc (∑ ik : H15ResonantOperatorIndex n K J, (h15Weight ik) ^ 2) *
              (∑ jl : H15ResonantOperatorIndex n K J, (h15Weight jl) ^ 2)
              ≤ (8 / (((n : ℝ) + 1) ^ 2)) * (8 / (((n : ℝ) + 1) ^ 2)) :=
                mul_le_mul hs hs hn hpos
            _ = (8 / (((n : ℝ) + 1) ^ 2)) ^ 2 := by ring
        exact mul_le_mul_of_nonneg_right this hc

/-- Specialisation to the Phase 4 truncation `K = 2n`, `J = n`: the
Hilbert–Schmidt norm of the nonresonant block is `O(n⁻⁴)`. -/
theorem h15NonresonantBlockGram_HS_le_phase4 (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (∑ ik : H15ResonantOperatorIndex n (2 * n) n, ∑ jl : H15ResonantOperatorIndex n (2 * n) n,
        Complex.normSq (h15NonresonantBlockGramKernel n (2 * n) n t ik jl))
      ≤ 64 / (((n : ℝ) + 1) ^ 4) := by
  have hKJ : 0 < 2 * n * n := by positivity
  have hmain := h15NonresonantBlockGram_HS_le n (2 * n) n t hKJ
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hgain : ((n : ℝ) / (((2 * n : ℕ) : ℝ) * (n : ℝ))) ^ 2 ≤ 1 := by
    have hrw : ((n : ℝ) / (((2 * n : ℕ) : ℝ) * (n : ℝ))) = 1 / (2 * (n : ℝ)) := by
      push_cast
      field_simp
    rw [hrw]
    rw [div_pow, one_pow, div_le_one (by positivity)]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hpos : (0 : ℝ) ≤ (8 / (((n : ℝ) + 1) ^ 2)) ^ 2 := sq_nonneg _
  have hfinal : (8 / (((n : ℝ) + 1) ^ 2)) ^ 2 * ((n : ℝ) / (((2 * n : ℕ) : ℝ) * (n : ℝ))) ^ 2
      ≤ 64 / (((n : ℝ) + 1) ^ 4) := by
    calc (8 / (((n : ℝ) + 1) ^ 2)) ^ 2 * ((n : ℝ) / (((2 * n : ℕ) : ℝ) * (n : ℝ))) ^ 2
        ≤ (8 / (((n : ℝ) + 1) ^ 2)) ^ 2 * 1 := mul_le_mul_of_nonneg_left hgain hpos
      _ = 64 / (((n : ℝ) + 1) ^ 4) := by
          rw [mul_one, div_pow]
          norm_num
          ring
  exact hmain.trans hfinal

end NBMellinTools.NB12
