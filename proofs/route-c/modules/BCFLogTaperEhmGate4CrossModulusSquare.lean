import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmGate4DispersionHierarchy

/-!
# Gate 4: exact signed cross-modulus square

This module expands the complete primitive high-product mode square before
any absolute-value estimate is applied.  Both the `g = 1` main sector and the
`g ≥ 2` primitive sector are included, as are all nonzero Vaaler frequencies.

The final identity shows where the retained correction occurs in the square
of the coupled residual.  It is a separate correction--mode cross term; it is
not definitionally one of the off-diagonal modulus kernels.  Any asymptotic
matching between those terms is therefore a new analytic theorem.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4CrossModulusSquare

open scoped BigOperators ComplexConjugate
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Strategy
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHighProductResidues
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTSectorCoupling
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-- A primitive modulus is the pair `(g,q)`, represented as a sigma type so
that Mathlib's finite sigma-sum API applies directly. -/
abbrev PrimitiveModulus := Σ _g : ℕ, ℕ

/-- Every primitive modulus in the complete high-product row.  The range
`g = 1` is the main sector; `g ≥ 2` is the off-diagonal gcd sector. -/
def highProductPrimitiveModuli (X : ℕ) : Finset PrimitiveModulus :=
  (Finset.Icc 1 (2 * X)).sigma
    (fun g ↦ Finset.Icc 1 ((2 * X) / g))

/-- One fully signed residue atom, including the outer Möbius factor. -/
noncomputable def highProductPrimitiveSignedAtom
    (h : ℤ) (X D J Y : ℕ) (p : PrimitiveModulus) (a : ℕ) : ℂ :=
  ((((ArithmeticFunction.moebius (p.1 * p.2) : ℤ) : ℝ) : ℂ) *
    highProductPrimitiveSummand h X D J Y p.1 p.2 a)

/-- The complete reduced-residue contribution at one primitive modulus. -/
noncomputable def highProductPrimitiveSignedModulusTerm
    (h : ℤ) (X D J Y : ℕ) (p : PrimitiveModulus) : ℂ :=
  ∑ a ∈ ehmReducedResidues p.2,
    highProductPrimitiveSignedAtom h X D J Y p a

/-- The complete signed primitive row at one Fourier frequency. -/
noncomputable def highProductCompletePrimitiveRow
    (h : ℤ) (X D J Y : ℕ) : ℂ :=
  ∑ p ∈ highProductPrimitiveModuli X,
    highProductPrimitiveSignedModulusTerm h X D J Y p

/-- The signed modulus term is the outer Möbius factor times the primitive
residue row already isolated in Stage 1. -/
theorem highProductPrimitiveSignedModulusTerm_eq
    (h : ℤ) (X D J Y : ℕ) (p : PrimitiveModulus) :
    highProductPrimitiveSignedModulusTerm h X D J Y p =
      ((((ArithmeticFunction.moebius (p.1 * p.2) : ℤ) : ℝ) : ℂ) *
        highProductPrimitiveGcdStratum h X D J Y p.1 p.2) := by
  unfold highProductPrimitiveSignedModulusTerm
    highProductPrimitiveSignedAtom highProductPrimitiveGcdStratum
  rw [Finset.mul_sum]

/-- Sigma-sum expansion of the complete primitive row. -/
theorem highProductCompletePrimitiveRow_eq_nested
    (h : ℤ) (X D J Y : ℕ) :
    highProductCompletePrimitiveRow h X D J Y =
      ∑ g ∈ Finset.Icc 1 (2 * X),
        ∑ q ∈ Finset.Icc 1 ((2 * X) / g),
          ((((ArithmeticFunction.moebius (g * q) : ℤ) : ℝ) : ℂ) *
            highProductPrimitiveGcdStratum h X D J Y g q) := by
  unfold highProductCompletePrimitiveRow highProductPrimitiveModuli
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro q _
  exact highProductPrimitiveSignedModulusTerm_eq h X D J Y ⟨g, q⟩

/-- For positive dyadic scale, the complete row is exactly the `g = 1`
main row plus the `g ≥ 2` primitive off-diagonal row. -/
theorem highProductCompletePrimitiveRow_eq_main_add_offDiagonal
    (h : ℤ) (X D J Y : ℕ) (hX : 1 ≤ X) :
    highProductCompletePrimitiveRow h X D J Y =
      (∑ q ∈ Finset.Icc 1 (2 * X),
        ((((ArithmeticFunction.moebius q : ℤ) : ℝ) : ℂ) *
          highProductPrimitiveGcdStratum h X D J Y 1 q)) +
      ∑ g ∈ Finset.Icc 2 (2 * X),
        ∑ q ∈ Finset.Icc 1 ((2 * X) / g),
          ((((ArithmeticFunction.moebius (g * q) : ℤ) : ℝ) : ℂ) *
            highProductPrimitiveGcdStratum h X D J Y g q) := by
  let F : ℕ → ℂ := fun g ↦
    ∑ q ∈ Finset.Icc 1 ((2 * X) / g),
      ((((ArithmeticFunction.moebius (g * q) : ℤ) : ℝ) : ℂ) *
        highProductPrimitiveGcdStratum h X D J Y g q)
  have hsplit : Finset.Icc 1 (2 * X) =
      insert 1 (Finset.Icc 2 (2 * X)) := by
    ext g
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  calc
    highProductCompletePrimitiveRow h X D J Y =
        ∑ g ∈ Finset.Icc 1 (2 * X), F g := by
      rw [highProductCompletePrimitiveRow_eq_nested]
    _ = F 1 + ∑ g ∈ Finset.Icc 2 (2 * X), F g := by
      rw [hsplit, Finset.sum_insert (by simp)]
    _ = _ := by simp [F]

/-- Complete Vaaler-weighted primitive modes. -/
noncomputable def highProductCompletePrimitiveModes
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h * highProductCompletePrimitiveRow h X D J Y

/-- The flattened complete modes coincide with the existing Stage-1
main/off-diagonal decomposition. -/
theorem highProductCompletePrimitiveModes_eq_main_add_offDiagonal
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) (hX : 1 ≤ X) :
    highProductCompletePrimitiveModes V Q X D J Y =
      highProductPrimitiveMainModes V Q X D J Y +
        highProductPrimitiveOffDiagonalModes V Q X D J Y := by
  unfold highProductCompletePrimitiveModes
    highProductPrimitiveMainModes highProductPrimitiveOffDiagonalModes
  simp_rw [highProductCompletePrimitiveRow_eq_main_add_offDiagonal
    _ _ _ _ _ hX, mul_add]
  rw [Finset.sum_add_distrib]

/-! ## Residue and phase kernels -/

/-- The cross kernel between two primitive moduli at possibly distinct
Fourier frequencies, expanded over both reduced-residue variables. -/
noncomputable def highProductPrimitiveResidueCrossKernel
    (h k : ℤ) (X D J Y : ℕ)
    (p r : PrimitiveModulus) : ℂ :=
  ∑ a ∈ ehmReducedResidues p.2,
    ∑ b ∈ ehmReducedResidues r.2,
      starRingEnd ℂ (highProductPrimitiveSignedAtom h X D J Y p a) *
        highProductPrimitiveSignedAtom k X D J Y r b

/-- Multiplying two modulus rows gives exactly the residue-pair kernel. -/
theorem star_modulusTerm_mul_modulusTerm_eq_residueCrossKernel
    (h k : ℤ) (X D J Y : ℕ) (p r : PrimitiveModulus) :
    starRingEnd ℂ (highProductPrimitiveSignedModulusTerm h X D J Y p) *
        highProductPrimitiveSignedModulusTerm k X D J Y r =
      highProductPrimitiveResidueCrossKernel h k X D J Y p r := by
  unfold highProductPrimitiveSignedModulusTerm
    highProductPrimitiveResidueCrossKernel
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

/-- The phase in one residue-pair kernel is the linear rational difference
`k*b/r - h*a/q`.  No modular inverse occurs in this finite expansion. -/
theorem star_rationalPhase_mul_rationalPhase
    (h k : ℤ) (a q b r : ℕ) :
    starRingEnd ℂ (ehmVaalerRationalPhase h a 1 q) *
        ehmVaalerRationalPhase k b 1 r =
      Complex.exp
        (((2 * Real.pi *
          ((k : ℝ) * ((b : ℝ) / (r : ℝ)) -
            (h : ℝ) * ((a : ℝ) / (q : ℝ))) : ℝ) : ℂ) * Complex.I) := by
  unfold ehmVaalerRationalPhase vaalerFourierPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-! ## Complete weighted square -/

/-- One Vaaler-frequency/modulus term in the complete primitive modes. -/
noncomputable def highProductPrimitiveWeightedModulusTerm
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ)
    (h : ℤ) (p : PrimitiveModulus) : ℂ :=
  V.coefficient Q h *
    highProductPrimitiveSignedModulusTerm h X D J Y p

/-- Cross terms with the same primitive modulus, retaining every pair of
Vaaler frequencies. -/
noncomputable def highProductPrimitiveCrossModulusDiagonal
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    ∑ p ∈ highProductPrimitiveModuli X,
      ∑ k ∈ (V.frequencies Q).erase 0,
        starRingEnd ℂ
            (highProductPrimitiveWeightedModulusTerm V Q X D J Y h p) *
          highProductPrimitiveWeightedModulusTerm V Q X D J Y k p

/-- Cross terms between distinct primitive moduli.  This is the exact
off-diagonal object that a signed dispersion or automorphic estimate must
evaluate. -/
noncomputable def highProductPrimitiveCrossModulusOffDiagonal
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    ∑ p ∈ highProductPrimitiveModuli X,
      ∑ k ∈ (V.frequencies Q).erase 0,
        ∑ r ∈ (highProductPrimitiveModuli X).erase p,
          starRingEnd ℂ
              (highProductPrimitiveWeightedModulusTerm V Q X D J Y h p) *
            highProductPrimitiveWeightedModulusTerm V Q X D J Y k r

private theorem normSq_sum_sum_eq_cross
    {α β : Type*}
    (s : Finset α) (t : Finset β) (f : α → β → ℂ) :
    (Complex.normSq (∑ i ∈ s, ∑ j ∈ t, f i j) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ s, ∑ l ∈ t,
        starRingEnd ℂ (f i j) * f k l := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]

/-- Exact diagonal/off-diagonal expansion of the complete signed
cross-modulus square. -/
theorem highProductCompletePrimitiveModes_normSq_eq_diagonal_add_offDiagonal
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) :
    (Complex.normSq
        (highProductCompletePrimitiveModes V Q X D J Y) : ℂ) =
      highProductPrimitiveCrossModulusDiagonal V Q X D J Y +
        highProductPrimitiveCrossModulusOffDiagonal V Q X D J Y := by
  classical
  unfold highProductCompletePrimitiveModes
    highProductCompletePrimitiveRow
  simp_rw [Finset.mul_sum]
  rw [normSq_sum_sum_eq_cross]
  unfold highProductPrimitiveCrossModulusDiagonal
    highProductPrimitiveCrossModulusOffDiagonal
  simp_rw [highProductPrimitiveWeightedModulusTerm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact (Finset.add_sum_erase (highProductPrimitiveModuli X)
    (fun r ↦
      starRingEnd ℂ
          (V.coefficient Q h *
            highProductPrimitiveSignedModulusTerm h X D J Y p) *
        (V.coefficient Q k *
          highProductPrimitiveSignedModulusTerm k X D J Y r)) hp).symm

/-- Real form of the complete signed-square expansion. -/
theorem highProductCompletePrimitiveModes_normSq_eq_re_diagonal_add_offDiagonal
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) :
    Complex.normSq (highProductCompletePrimitiveModes V Q X D J Y) =
      (highProductPrimitiveCrossModulusDiagonal V Q X D J Y).re +
        (highProductPrimitiveCrossModulusOffDiagonal V Q X D J Y).re := by
  have h := congrArg Complex.re
    (highProductCompletePrimitiveModes_normSq_eq_diagonal_add_offDiagonal
      V Q X D J Y)
  simpa using h

/-! ## Where the retained correction occurs -/

/-- The canonical correction-coupled core is correction minus the complete
primitive modes. -/
theorem highProductCanonicalPrimitiveCoupledCore_eq_correction_sub_modes
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) (hX : 1 ≤ X) :
    highProductCanonicalPrimitiveCoupledCore V Q X J U Y =
      (ehmMSTTHighSectorRetainedCorrection X
        (ehmExplicitFarCutoff X) J U Y : ℂ) -
      highProductCompletePrimitiveModes V Q X
        (ehmExplicitFarCutoff X) J Y := by
  unfold highProductCanonicalPrimitiveCoupledCore
  rw [highProductCompletePrimitiveModes_eq_main_add_offDiagonal
    V Q X (ehmExplicitFarCutoff X) J Y hX]
  ring

/-- Exact square of the correction-coupled residual.  The retained
correction contributes its own square and the separate
`-2 * correction * Re(modes)` term. -/
theorem highProductCanonicalPrimitiveCoupledCore_normSq
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) (hX : 1 ≤ X) :
    Complex.normSq (highProductCanonicalPrimitiveCoupledCore V Q X J U Y) =
      (ehmMSTTHighSectorRetainedCorrection X
        (ehmExplicitFarCutoff X) J U Y) ^ 2 +
      Complex.normSq (highProductCompletePrimitiveModes V Q X
        (ehmExplicitFarCutoff X) J Y) -
      2 * ehmMSTTHighSectorRetainedCorrection X
        (ehmExplicitFarCutoff X) J U Y *
        (highProductCompletePrimitiveModes V Q X
          (ehmExplicitFarCutoff X) J Y).re := by
  rw [highProductCanonicalPrimitiveCoupledCore_eq_correction_sub_modes
    V Q X J U Y hX]
  rw [Complex.normSq_sub]
  simp only [Complex.normSq_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im, zero_mul, sub_zero]
  ring

/-- Final audit identity: the complete residual square contains the
cross-modulus off-diagonal kernel, but the retained correction remains in a
distinct correction--mode cross term. -/
theorem highProductCanonicalPrimitiveCoupledCore_normSq_crossModulus
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) (hX : 1 ≤ X) :
    Complex.normSq (highProductCanonicalPrimitiveCoupledCore V Q X J U Y) =
      (ehmMSTTHighSectorRetainedCorrection X
        (ehmExplicitFarCutoff X) J U Y) ^ 2 +
      (highProductPrimitiveCrossModulusDiagonal V Q X
        (ehmExplicitFarCutoff X) J Y).re +
      (highProductPrimitiveCrossModulusOffDiagonal V Q X
        (ehmExplicitFarCutoff X) J Y).re -
      2 * ehmMSTTHighSectorRetainedCorrection X
        (ehmExplicitFarCutoff X) J U Y *
        (highProductCompletePrimitiveModes V Q X
          (ehmExplicitFarCutoff X) J Y).re := by
  rw [highProductCanonicalPrimitiveCoupledCore_normSq V Q X J U Y hX]
  rw [highProductCompletePrimitiveModes_normSq_eq_re_diagonal_add_offDiagonal]
  ring

/-- The exact main term that the distinct-modulus kernel would have to
reproduce in order to make the coupled residual small.  It is not the
retained correction alone: it also contains the mode/correction cross term
and the same-modulus diagonal. -/
noncomputable def highProductRequiredOffDiagonalBalance
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) : ℝ :=
  2 * ehmMSTTHighSectorRetainedCorrection X
      (ehmExplicitFarCutoff X) J U Y *
      (highProductCompletePrimitiveModes V Q X
        (ehmExplicitFarCutoff X) J Y).re -
    (ehmMSTTHighSectorRetainedCorrection X
      (ehmExplicitFarCutoff X) J U Y) ^ 2 -
    (highProductPrimitiveCrossModulusDiagonal V Q X
      (ehmExplicitFarCutoff X) J Y).re

/-- Exact obstruction identity.  The error in matching the off-diagonal
kernel to its required correction balance is precisely the squared norm of
the original correction-coupled Gate-4 core. -/
theorem offDiagonal_sub_requiredBalance_eq_core_normSq
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) (hX : 1 ≤ X) :
    (highProductPrimitiveCrossModulusOffDiagonal V Q X
        (ehmExplicitFarCutoff X) J Y).re -
      highProductRequiredOffDiagonalBalance V Q X J U Y =
        Complex.normSq
          (highProductCanonicalPrimitiveCoupledCore V Q X J U Y) := by
  rw [highProductCanonicalPrimitiveCoupledCore_normSq_crossModulus
    V Q X J U Y hX]
  unfold highProductRequiredOffDiagonalBalance
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4CrossModulusSquare
