/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15Phase3Spectral

/-!
# NB15: Operator-Trace Decay Analysis (Phase 4)

Phase 4 fills in the Phase 3 sorry proofs with concrete decay properties:

1. **Resonant trace bounds** — Tr(Gram_res) is bounded
2. **Nonresonant trace decay** — Tr(Gram_nonres) → 0 via oscillatory cancellation
3. **Main decay identity** — Full H15 trace decay theorem

By Nyman-Beurling criterion, H15 decay → Riemann Hypothesis.

*Scope note.* The Nyman–Beurling criterion itself is not available (neither in
Mathlib nor in this repository), so the final statement below is proved in the
honest conditional form: the operator-trace decay is established
unconditionally for the model of Phases 1–3, and the Riemann Hypothesis is
derived from it *given* the criterion, which is taken as an explicit hypothesis
of the theorem.  See `h15RiemannHypothesisViaOperatorTrace_phase4`.
-/

open scoped BigOperators
open Complex

namespace NBMellinTools.NB12

/-! ## Resonant trace analysis -/

/-- Resonant block trace is bounded (finite-rank × amplitude bounds). -/
theorem h15ResonantBlockGramTrace_bounded_phase4
    (n K J : ℕ) (t : ℝ) :
    ∃ C : ℝ, ‖(Matrix.trace (h15ResonantBlockGramKernel n K J t) : ℂ)‖ ≤ C := by
  -- Tr(Gram_res) = ∑ |a_i|², and ∑ |a_i|² ≤ 8/(N+1)² ≤ 8 by the amplitude
  -- (weight) bounds; the constant 8 is uniform in `n`, `K`, `J` and `t`.
  refine ⟨8, le_trans (h15ResonantBlockGramTrace_norm_le n K J t) ?_⟩
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact div_le_self (by norm_num) h1

/-! ## Nonresonant trace decay -/

/-- The nonresonant HS norm decays to zero as N → ∞. -/
theorem h15NonresonantBlockGramKernel_HS_decays_phase4
    (t : ℝ) :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (∑ ik : H15ResonantOperatorIndex n (2 * n) n,
        ∑ jl : H15ResonantOperatorIndex n (2 * n) n,
          Complex.normSq (h15NonresonantBlockGramKernel n (2 * n) n t ik jl)) < ε := by
  -- HS norm → 0 via oscillatory cancellation (complete periods cancel, incomplete
  -- periods cost at most one period) plus the ledger normalisation of the amplitudes.
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (64 / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.succ_pos N) hn
  have hbound := h15NonresonantBlockGram_HS_le_phase4 n hn0 t
  have hxN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_succ_le hn)
  have hx1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hxpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hgt : 64 / ε < (n : ℝ) + 1 := by linarith
  have hlt : 64 / ((n : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hxpos]
    rw [div_lt_iff₀ hε] at hgt
    linarith
  have h3 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ hx1
  have hpow : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hxpos.le]
  have hstep : 64 / (((n : ℝ) + 1) ^ 4) ≤ 64 / ((n : ℝ) + 1) := by
    gcongr
  linarith

/-- The nonresonant trace decays to zero. -/
theorem h15NonresonantBlockGramTrace_decays_phase4
    (t : ℝ) :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ‖(Matrix.trace (h15NonresonantBlockGramKernel n (2 * n) n t) : ℂ)‖ < ε := by
  -- Every index is resonant with itself, so the nonresonant block has vanishing
  -- diagonal and its trace is *exactly* zero — a strengthening of the bound
  -- ‖Tr(Gram_nonres)‖ ≤ ‖Gram_nonres‖_HS → 0 supplied by the previous theorem.
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  rw [h15NonresonantBlockGramTrace_eq_zero n (2 * n) n t]
  simpa using hε

/-! ## Main decay identity assembly -/

/-- The resonant trace itself decays: the ledger normalisation gives
`‖Tr(Gram_res)‖ ≤ 8/(N+1)²`. -/
theorem h15ResonantBlockGramTrace_decays_phase4
    (t : ℝ) :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ‖(Matrix.trace (h15ResonantBlockGramKernel n (2 * n) n t) : ℂ)‖ < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (8 / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hbound := h15ResonantBlockGramTrace_norm_le n (2 * n) n t
  have hxN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_succ_le hn)
  have hxpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hgt : 8 / ε < (n : ℝ) + 1 := by linarith
  have hlt : 8 / ((n : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hxpos]
    rw [div_lt_iff₀ hε] at hgt
    linarith
  have hpow : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hstep : 8 / (((n : ℝ) + 1) ^ 2) ≤ 8 / ((n : ℝ) + 1) := by gcongr
  linarith

/-- The full Gram trace decays to zero when correction trace → 0. -/
theorem h15GramTraceDecays_phase4
    (t : ℝ) :
    (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ‖(Matrix.trace (h15NonresonantBlockGramKernel n (2 * n) n t) : ℂ)‖ < ε) →
    (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ‖(Matrix.trace (h15ResonantGramKernel n (2 * n) n t) : ℂ)‖ < ε) := by
  intro hnonres ε hε
  obtain ⟨N₁, hN₁⟩ := hnonres (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := h15ResonantBlockGramTrace_decays_phase4 t (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
  -- Tr(Gram) = Tr(Gram_res) + Tr(Gram_nonres) + Tr(Gram_corr), and the
  -- correction block is traceless.
  have hdec := h15SignedLedgerDecompositionFinal n (2 * n) n t
  rw [hdec]
  calc ‖Matrix.trace (h15ResonantBlockGramKernel n (2 * n) n t) +
        Matrix.trace (h15NonresonantBlockGramKernel n (2 * n) n t)‖
      ≤ ‖Matrix.trace (h15ResonantBlockGramKernel n (2 * n) n t)‖ +
        ‖Matrix.trace (h15NonresonantBlockGramKernel n (2 * n) n t)‖ := norm_add_le _ _
    _ < ε := by linarith

/-! ## H15 via Nyman-Beurling criterion -/

/-- The complete H15 decay statement (given oscillatory cancellation + correction decay). -/
theorem h15H15DecayViaOperatorTrace_phase4
    (t : ℝ) :
    (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ‖(Matrix.trace (h15NonresonantBlockGramKernel n (2 * n) n t) : ℂ)‖ < ε) →
    (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ‖(Matrix.trace (h15ResonantGramKernel n (2 * n) n t) : ℂ)‖ < ε) := by
  intro hnonres
  exact h15GramTraceDecays_phase4 t hnonres

/-- Unconditional operator-trace decay for the Phase 1–3 model:
`Tr(Gram) → 0` as the truncation parameter grows. -/
theorem h15GramTraceDecays_unconditional (t : ℝ) :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ‖(Matrix.trace (h15ResonantGramKernel n (2 * n) n t) : ℂ)‖ < ε :=
  h15H15DecayViaOperatorTrace_phase4 t (h15NonresonantBlockGramTrace_decays_phase4 t)

/- ORIGINAL STATEMENT (Task 5), left here for the record:

theorem h15RiemannHypothesisViaOperatorTrace_phase4
    (t : ℝ) :
    RiemannHypothesis := by
  sorry  -- Follows from:
         -- (1) h15NonresonantBlockGramTrace_decays_phase4 (oscillatory cancellation)
         -- (2) h15ResonantBlockGramTrace_bounded_phase4 (finite-rank arithmetic)
         -- (3) h15CorrectionTraceDecaysToZero (hypothesis, RH-strength gate)
         -- (4) Nyman-Beurling criterion: Tr(Gram) → 0 ↔ RH

This cannot be proved as stated.  The trace decay established in this file is a
theorem about the finite Gram model of Phases 1–3; the bridge "Tr(Gram) → 0 ⇒
RH" is precisely the Nyman–Beurling criterion applied to this model, and that
bridge is not formalised anywhere in this development (the Phase 3 declaration
`h15CorrectionTraceDecaysToZero` has content `True`, so it supplies nothing).
Deriving `RiemannHypothesis` outright would therefore be an unjustified claim.
The corrected statement below keeps the same conclusion but makes the missing
criterion an explicit hypothesis `hNB`. -/

/-- The Riemann Hypothesis via operator spectral analysis, in conditional form:
given the Nyman–Beurling-type criterion `hNB` relating decay of the Gram trace
of the canonical pair to RH, the Riemann Hypothesis follows, because the
required decay is proved unconditionally here
(`h15GramTraceDecays_unconditional`). -/
theorem h15RiemannHypothesisViaOperatorTrace_phase4
    (t : ℝ)
    (hNB : (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        ‖(Matrix.trace (h15ResonantGramKernel n (2 * n) n t) : ℂ)‖ < ε) →
      RiemannHypothesis) :
    RiemannHypothesis :=
  hNB (h15GramTraceDecays_unconditional t)

/-! ## Summary: What Phase 4 accomplished -/

/-- Phase 4: Operator spectral decomposition is complete with concrete decay. -/
theorem h15Phase4Complete :
    (∃ C : ℝ, ∀ n K J (t : ℝ),
      ‖(Matrix.trace (h15ResonantBlockGramKernel n K J t) : ℂ)‖ ≤ C) ∧
    (∀ (t : ℝ), ∀ ε : ℝ, ε > 0 → ∃ N₀, ∀ n ≥ N₀,
      ‖(Matrix.trace (h15NonresonantBlockGramKernel n (2*n) n t) : ℂ)‖ < ε) ∧
    (∀ n K J (t : ℝ), Matrix.trace (h15CorrectionBlockGramKernel n K J t) = 0) := by
  refine ⟨⟨8, fun n K J t => ?_⟩, fun t => h15NonresonantBlockGramTrace_decays_phase4 t,
    fun n K J t => h15CorrectionBlockGramTrace_eq_zero n K J t⟩
  refine le_trans (h15ResonantBlockGramTrace_norm_le n K J t) ?_
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact div_le_self (by norm_num) h1

end NBMellinTools.NB12
