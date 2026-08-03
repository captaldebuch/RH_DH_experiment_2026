import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTVariation

/-!
# Accumulating the reciprocal Taylor error in the MSTT route

The low-row module bounds the Taylor error for one frequency and one product
coordinate.  This module performs the two finite outer summations and replaces
the exact remainder by the elementary uniform block envelope

`|h*n| * H^(K+1) / X^(K+2)`.

It does not assert that the resulting expression tends to zero.  Choosing the
cutoffs and proving decay of the explicit finite envelope is precisely Gate 2.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTTaylorAccumulation

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmReciprocalTaylor

/-- Symmetric nonzero Vaaler frequencies retained at height `Q`. -/
noncomputable def ehmMSTTNonzeroFrequencyRange (Q : ℕ) : Finset ℤ :=
  (Finset.Icc (-(Q : ℤ)) (Q : ℤ)).erase 0

/-- The complete signed Taylor-error contribution on one MSTT block, before
taking norms. -/
noncomputable def ehmMSTTLowProductTaylorErrorSum
    (Q N D J Y X H K : ℕ) : ℂ :=
  ∑ h ∈ ehmMSTTNonzeroFrequencyRange Q,
    ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
      ehmMSTTLowProductTaylorErrorColumn h N D n X H K

/-- The corresponding sum of the exact unsigned column majorants. -/
noncomputable def ehmMSTTLowProductTaylorErrorMass
    (Q N D J Y X H K : ℕ) : ℝ :=
  ∑ h ∈ ehmMSTTNonzeroFrequencyRange Q,
    ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
      ehmMSTTLowProductTaylorErrorMajorant h N D n X H K

/-- Triangle inequality is postponed until after the signed Taylor-error
columns have been assembled, and then bounded by their explicit majorants. -/
theorem norm_ehmMSTTLowProductTaylorErrorSum_le_mass
    (Q N D J Y X H K : ℕ) (hX : 1 ≤ X) :
    ‖ehmMSTTLowProductTaylorErrorSum Q N D J Y X H K‖ ≤
      ehmMSTTLowProductTaylorErrorMass Q N D J Y X H K := by
  classical
  unfold ehmMSTTLowProductTaylorErrorSum
    ehmMSTTLowProductTaylorErrorMass
  calc
    ‖∑ h ∈ ehmMSTTNonzeroFrequencyRange Q,
        ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
          ehmMSTTLowProductTaylorErrorColumn h N D n X H K‖ ≤
      ∑ h ∈ ehmMSTTNonzeroFrequencyRange Q,
        ‖∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
          ehmMSTTLowProductTaylorErrorColumn h N D n X H K‖ :=
        norm_sum_le _ _
    _ ≤ ∑ h ∈ ehmMSTTNonzeroFrequencyRange Q,
        ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
          ‖ehmMSTTLowProductTaylorErrorColumn h N D n X H K‖ := by
      apply Finset.sum_le_sum
      intro h _
      exact norm_sum_le _ _
    _ ≤ ∑ h ∈ ehmMSTTNonzeroFrequencyRange Q,
        ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
          ehmMSTTLowProductTaylorErrorMajorant h N D n X H K := by
      apply Finset.sum_le_sum
      intro h _
      apply Finset.sum_le_sum
      intro n _
      exact norm_ehmMSTTLowProductTaylorErrorColumn_le
        h N D n X H K hX

/-- The unsigned mass of a fixed product weight on one outer block. -/
noncomputable def ehmMSTTLowProductWeightL1Mass
    (N D n X H : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc X (X + H),
    ‖ehmMSTTLowProductWeight N D n m‖

/-- Uniform Taylor factor for frequency `h` and product coordinate `n` on a
block of length `H` based at `X`. -/
noncomputable def ehmMSTTReciprocalTaylorBlockFactor
    (h : ℤ) (n X H K : ℕ) : ℝ :=
  2 * Real.pi *
    (|((h : ℝ) * (n : ℝ))| * (H : ℝ) ^ (K + 1) /
      (X : ℝ) ^ (K + 2))

/-- The exact column majorant is bounded by weight mass times the uniform
Taylor factor. -/
theorem ehmMSTTLowProductTaylorErrorMajorant_le_blockFactor
    (h : ℤ) (N D n X H K : ℕ) (hX : 1 ≤ X) :
    ehmMSTTLowProductTaylorErrorMajorant h N D n X H K ≤
      ehmMSTTLowProductWeightL1Mass N D n X H *
        ehmMSTTReciprocalTaylorBlockFactor h n X H K := by
  classical
  unfold ehmMSTTLowProductTaylorErrorMajorant
    ehmMSTTLowProductWeightL1Mass
    ehmMSTTReciprocalTaylorBlockFactor
  calc
    (∑ m ∈ Finset.Ioc X (X + H),
        ‖(((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          ehmMSTTLowProductWeight N D n m))‖ *
            (2 * Real.pi *
              |reciprocalTaylorRemainder
                ((h : ℝ) * (n : ℝ)) (X : ℝ) K
                  ((m : ℝ) - (X : ℝ))|)) ≤
      ∑ m ∈ Finset.Ioc X (X + H),
        ‖ehmMSTTLowProductWeight N D n m‖ *
          (2 * Real.pi *
            (|((h : ℝ) * (n : ℝ))| * (H : ℝ) ^ (K + 1) /
              (X : ℝ) ^ (K + 2))) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmX : X < m := (Finset.mem_Ioc.mp hm).1
      have hmXH : m ≤ X + H := (Finset.mem_Ioc.mp hm).2
      have hrem := abs_reciprocalTaylorRemainder_le
        ((h : ℝ) * (n : ℝ)) (X : ℝ)
        ((m : ℝ) - (X : ℝ)) (H : ℝ) K
        (by exact_mod_cast (show 0 < X by omega))
        (sub_nonneg.mpr (by exact_mod_cast (show X ≤ m by omega)))
        (sub_le_iff_le_add.mpr
          (by exact_mod_cast (show m ≤ H + X by simpa [add_comm] using hmXH)))
      rw [norm_mul]
      have hmu :
          ‖((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
      have hweight : 0 ≤ ‖ehmMSTTLowProductWeight N D n m‖ := norm_nonneg _
      have hphase : 0 ≤ 2 * Real.pi := by positivity
      have hpref :
          ‖((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ))‖ *
              ‖ehmMSTTLowProductWeight N D n m‖ ≤
            ‖ehmMSTTLowProductWeight N D n m‖ := by
        simpa using mul_le_mul_of_nonneg_right hmu hweight
      calc
        ‖((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ))‖ *
              ‖ehmMSTTLowProductWeight N D n m‖ *
              (2 * Real.pi *
                |reciprocalTaylorRemainder
                  ((h : ℝ) * (n : ℝ)) (X : ℝ) K
                    ((m : ℝ) - (X : ℝ))|) ≤
            ‖ehmMSTTLowProductWeight N D n m‖ *
              (2 * Real.pi *
                |reciprocalTaylorRemainder
                  ((h : ℝ) * (n : ℝ)) (X : ℝ) K
                    ((m : ℝ) - (X : ℝ))|) := by
          exact mul_le_mul_of_nonneg_right hpref
            (mul_nonneg hphase (abs_nonneg _))
        _ ≤ ‖ehmMSTTLowProductWeight N D n m‖ *
              (2 * Real.pi *
                (|((h : ℝ) * (n : ℝ))| * (H : ℝ) ^ (K + 1) /
                  (X : ℝ) ^ (K + 2))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrem hphase) hweight
    _ = (∑ m ∈ Finset.Ioc X (X + H),
          ‖ehmMSTTLowProductWeight N D n m‖) *
        (2 * Real.pi *
          (|((h : ℝ) * (n : ℝ))| * (H : ℝ) ^ (K + 1) /
            (X : ℝ) ^ (K + 2))) := by
      rw [Finset.sum_mul]

/-- Fully explicit Gate-2 envelope after summing all retained frequencies
and product coordinates. -/
noncomputable def ehmMSTTLowProductTaylorBlockEnvelope
    (Q N D J Y X H K : ℕ) : ℝ :=
  ∑ h ∈ ehmMSTTNonzeroFrequencyRange Q,
    ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
      ehmMSTTLowProductWeightL1Mass N D n X H *
        ehmMSTTReciprocalTaylorBlockFactor h n X H K

theorem ehmMSTTLowProductTaylorErrorMass_le_blockEnvelope
    (Q N D J Y X H K : ℕ) (hX : 1 ≤ X) :
    ehmMSTTLowProductTaylorErrorMass Q N D J Y X H K ≤
      ehmMSTTLowProductTaylorBlockEnvelope Q N D J Y X H K := by
  unfold ehmMSTTLowProductTaylorErrorMass
    ehmMSTTLowProductTaylorBlockEnvelope
  apply Finset.sum_le_sum
  intro h _
  apply Finset.sum_le_sum
  intro n _
  exact ehmMSTTLowProductTaylorErrorMajorant_le_blockFactor
    h N D n X H K hX

/-- The signed accumulated Taylor error is controlled by the single explicit
Gate-2 envelope. -/
theorem norm_ehmMSTTLowProductTaylorErrorSum_le_blockEnvelope
    (Q N D J Y X H K : ℕ) (hX : 1 ≤ X) :
    ‖ehmMSTTLowProductTaylorErrorSum Q N D J Y X H K‖ ≤
      ehmMSTTLowProductTaylorBlockEnvelope Q N D J Y X H K :=
  (norm_ehmMSTTLowProductTaylorErrorSum_le_mass
      Q N D J Y X H K hX).trans
    (ehmMSTTLowProductTaylorErrorMass_le_blockEnvelope
      Q N D J Y X H K hX)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTTaylorAccumulation
