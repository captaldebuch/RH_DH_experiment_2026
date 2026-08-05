/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB15DirectAdditiveResonantFixedHeight
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# NB15: canonical finite operator attached to the resonant H15 block

This module is the Phase 1 stop test for the proposed operator route.  It
does not import the five `RequestProject` modules named in the integration
brief: those modules are absent from the supplied Aristotle archives.
Instead it constructs the operator directly from the already certified H15
fixed-height amplitude.

There are two distinct facts which must not be conflated.

* The Gram kernel is canonical once the H15 amplitude has been fixed, and
  composing it with the fixed all-ones test matrix recovers the complete
  quadratic energy exactly.
* The ordinary trace of the Gram kernel sees only its diagonal.  The same is
  true after projecting the kernel to equal physical frequencies.  Hence a
  bare assertion that the H15 expression is `Matrix.trace T` has no content:
  the observable multiplying the kernel is an essential part of the data.

No estimate, Hilbert--Schmidt decay, or correction decay is asserted here.
-/

open scoped BigOperators ComplexConjugate
open Complex

namespace NBMellinTools.NB12

/-! ## The genuine finite H15 index and amplitude -/

/-- The active finite quotient support, used as the operator's index type. -/
abbrev H15ResonantOperatorIndex (n K J : ℕ) :=
  ↥(h15DirectAdditiveResonantQuotientPairSupport n K J)

/-- The literal fixed-height H15 amplitude on the active support.  This
definition retains the signed Möbius/log-taper row weight, Gaussian damping,
orientation, inverse residue and physical frequency already present in the
certified arithmetic expression. -/
noncomputable def h15ResonantOperatorAmplitude
    (n K J : ℕ) (t : ℝ) (ik : H15ResonantOperatorIndex n K J) : ℂ :=
  h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
    (h15ContourDamping n)
    (ik.1.1, h15DirectAdditiveResonantPhysicalFrequency ik.1) t

/-- Summing the operator amplitude over its finite index is exactly the
previously certified fixed-height quotient aggregate. -/
theorem sum_h15ResonantOperatorAmplitude_eq_fixedHeightAggregate
    (n K J : ℕ) (t : ℝ) :
    (∑ ik : H15ResonantOperatorIndex n K J,
      h15ResonantOperatorAmplitude n K J t ik) =
        h15BettinChandeeResonantQuotientFixedHeightAggregate n K J t := by
  classical
  unfold h15BettinChandeeResonantQuotientFixedHeightAggregate
    h15ResonantOperatorAmplitude
  simpa only [Finset.univ_eq_attach] using
    (Finset.sum_attach
      (h15DirectAdditiveResonantQuotientPairSupport n K J)
      (fun ik =>
        h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
          (h15ContourDamping n)
          (ik.1, h15DirectAdditiveResonantPhysicalFrequency ik) t))

/-! ## Canonical Gram and collision kernels -/

/-- The canonical Gram kernel of the genuine H15 amplitudes. -/
noncomputable def h15ResonantGramKernel
    (n K J : ℕ) (t : ℝ) :
    Matrix (H15ResonantOperatorIndex n K J)
      (H15ResonantOperatorIndex n K J) ℂ :=
  fun ik jl =>
    conj (h15ResonantOperatorAmplitude n K J t ik) *
      h15ResonantOperatorAmplitude n K J t jl

/-- Pointwise specialization makes the Gram kernel unique.  This is the
non-vacuous uniqueness statement used here: uniqueness is relative to the
already certified H15 amplitude, not relative to the value of a trace. -/
theorem h15ResonantGramKernel_unique
    (n K J : ℕ) (t : ℝ)
    (M : Matrix (H15ResonantOperatorIndex n K J)
      (H15ResonantOperatorIndex n K J) ℂ)
    (hM : ∀ ik jl,
      M ik jl =
        conj (h15ResonantOperatorAmplitude n K J t ik) *
          h15ResonantOperatorAmplitude n K J t jl) :
    M = h15ResonantGramKernel n K J t := by
  funext ik jl
  exact hM ik jl

/-- The physical-frequency collision projection of the Gram kernel. -/
noncomputable def h15ResonantCollisionKernel
    (n K J : ℕ) (t : ℝ) :
    Matrix (H15ResonantOperatorIndex n K J)
      (H15ResonantOperatorIndex n K J) ℂ :=
  fun ik jl =>
    if h15DirectAdditiveResonantPhysicalFrequency ik.1 =
        h15DirectAdditiveResonantPhysicalFrequency jl.1 then
      h15ResonantGramKernel n K J t ik jl
    else 0

/-- Collision projection does not change the diagonal. -/
theorem h15ResonantCollisionKernel_diag
    (n K J : ℕ) (t : ℝ) (ik : H15ResonantOperatorIndex n K J) :
    h15ResonantCollisionKernel n K J t ik ik =
      h15ResonantGramKernel n K J t ik ik := by
  simp [h15ResonantCollisionKernel]

/-! ## What the ordinary trace does and does not see -/

/-- The ordinary trace of the Gram kernel is only the diagonal squared
mass. -/
theorem trace_h15ResonantGramKernel
    (n K J : ℕ) (t : ℝ) :
    Matrix.trace (h15ResonantGramKernel n K J t) =
      ∑ ik : H15ResonantOperatorIndex n K J,
        (Complex.normSq (h15ResonantOperatorAmplitude n K J t ik) : ℂ) := by
  classical
  unfold Matrix.trace Matrix.diag h15ResonantGramKernel
  apply Finset.sum_congr rfl
  intro ik _
  rw [Complex.normSq_eq_conj_mul_self]

/-- In the notation of the certified fixed-height ledger, the real part of
the ordinary Gram trace is exactly the previously defined diagonal sector. -/
theorem trace_h15ResonantGramKernel_re_eq_diagonal
    (n K J : ℕ) (t : ℝ) :
    (Matrix.trace (h15ResonantGramKernel n K J t)).re =
      h15BettinChandeeResonantQuotientDiagonal n K J t := by
  classical
  rw [trace_h15ResonantGramKernel]
  rw [Complex.re_sum]
  simp only [ofReal_re]
  unfold h15BettinChandeeResonantQuotientDiagonal
    h15ResonantOperatorAmplitude
  simpa only [Finset.univ_eq_attach] using
    (Finset.sum_attach
      (h15DirectAdditiveResonantQuotientPairSupport n K J)
      (fun ik =>
        Complex.normSq
          (h15DirectAdditiveFixedHeightSummand (NB8.logTaperLength n)
            (h15ContourDamping n)
            (ik.1, h15DirectAdditiveResonantPhysicalFrequency ik) t)))

/-- Projecting to equal physical frequencies still leaves the ordinary
trace unchanged.  Thus the collision cross terms are not an ordinary trace
of the projected Gram matrix. -/
theorem trace_h15ResonantCollisionKernel_eq_trace_gram
    (n K J : ℕ) (t : ℝ) :
    Matrix.trace (h15ResonantCollisionKernel n K J t) =
      Matrix.trace (h15ResonantGramKernel n K J t) := by
  classical
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro ik _
  exact h15ResonantCollisionKernel_diag n K J t ik

/-- Consequently the ordinary trace of the collision-projected kernel is
also exactly the diagonal sector and contains no collision cross term. -/
theorem trace_h15ResonantCollisionKernel_re_eq_diagonal
    (n K J : ℕ) (t : ℝ) :
    (Matrix.trace (h15ResonantCollisionKernel n K J t)).re =
      h15BettinChandeeResonantQuotientDiagonal n K J t := by
  rw [trace_h15ResonantCollisionKernel_eq_trace_gram,
    trace_h15ResonantGramKernel_re_eq_diagonal]

/-! ## The correct trace observable -/

/-- The fixed all-ones test matrix.  It is independent of all H15
coefficients. -/
def h15AllOnesTestMatrix (ι : Type*) : Matrix ι ι ℂ :=
  fun _ _ => 1

/-- Composing any finite kernel with the fixed all-ones matrix turns its
complete entry sum into a trace. -/
theorem trace_h15AllOnesTestMatrix_mul
    {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) :
    Matrix.trace (h15AllOnesTestMatrix ι * M) =
      ∑ i : ι, ∑ j : ι, M j i := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, h15AllOnesTestMatrix]

/-- The canonical H15 Gram kernel, observed by the fixed all-ones matrix,
recovers the complete fixed-height quadratic energy exactly.  In particular
all equal- and unequal-frequency cross terms are retained. -/
theorem trace_allOnes_mul_h15ResonantGramKernel_eq_fixedHeightEnergy
    (n K J : ℕ) (t : ℝ) :
    Matrix.trace
        (h15AllOnesTestMatrix (H15ResonantOperatorIndex n K J) *
          h15ResonantGramKernel n K J t) =
      (Complex.normSq
        (h15BettinChandeeResonantQuotientFixedHeightAggregate n K J t) : ℂ) := by
  classical
  rw [trace_h15AllOnesTestMatrix_mul]
  unfold h15ResonantGramKernel
  calc
    (∑ i : H15ResonantOperatorIndex n K J,
        ∑ j : H15ResonantOperatorIndex n K J,
          conj (h15ResonantOperatorAmplitude n K J t j) *
            h15ResonantOperatorAmplitude n K J t i) =
        (∑ j : H15ResonantOperatorIndex n K J,
          conj (h15ResonantOperatorAmplitude n K J t j)) *
        (∑ i : H15ResonantOperatorIndex n K J,
          h15ResonantOperatorAmplitude n K J t i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
    _ = conj (∑ j : H15ResonantOperatorIndex n K J,
          h15ResonantOperatorAmplitude n K J t j) *
        (∑ i : H15ResonantOperatorIndex n K J,
          h15ResonantOperatorAmplitude n K J t i) := by
            rw [map_sum]
    _ = (Complex.normSq
        (∑ ik : H15ResonantOperatorIndex n K J,
          h15ResonantOperatorAmplitude n K J t ik) : ℂ) := by
            rw [Complex.normSq_eq_conj_mul_self]
    _ = _ := by
      rw [sum_h15ResonantOperatorAmplitude_eq_fixedHeightAggregate]

/-! ## The trace-vacuity stop test -/

/-- A concrete off-diagonal matrix with zero trace. -/
def h15TraceVacuityWitness : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 0, 0]

/-- The witness has the same trace as the zero matrix. -/
theorem trace_h15TraceVacuityWitness_eq_trace_zero :
    Matrix.trace h15TraceVacuityWitness =
      Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [h15TraceVacuityWitness, Matrix.trace_fin_two]

/-- Nevertheless the witness is not the zero matrix.  Therefore a trace
value alone cannot identify an H15 kernel. -/
theorem h15TraceVacuityWitness_ne_zero :
    h15TraceVacuityWitness ≠ (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [h15TraceVacuityWitness] at h01

end NBMellinTools.NB12
