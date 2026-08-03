/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEDegenerateCollisionPhaseCompression

/-!
# NB12zzzaZ: diagonal and second-harmonic degenerate ledgers

The equal/opposite phase compression is lifted through the complete signed
quotient-fiber sum.  Each atom retains its endpoint coefficient, collected
Laurent-pair coefficient, Archimedean orientation factors, hyperbolic
normalization, and quotient support.

For the actual H15 common superperiod the frequency-level quotient
dispersion is exactly the sum of:

* a frequency-independent collision diagonal; and
* a doubled-frequency signed residual.

No absolute value or analytic estimate is used.
-/

open AddChar Complex ZMod
open scoped BigOperators ComplexConjugate

namespace NBMellinTools.NB12

/-! ## Literal atom coefficients -/

noncomputable def h15PostFEDegenerateCollisionRealPrefactor
    (n g U Q : ℕ) (t : ℝ) (p : H15PostFEMissingPairAtomIndex) : ℝ :=
  h15PostFEResidueFiberEndpointMeanCoefficient n g U Q p.1.1 *
    (4 / (2 * h15PairedHyperbolicCoefficient t))

noncomputable def h15PostFEDegenerateCollisionComplexCoefficient
    (n g U Q : ℕ) (t : ℝ) (p : H15PostFEMissingPairAtomIndex) : ℂ :=
  h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t p.2.1 *
    (conj (h15PostFEOrientationArchimedeanFactor p.2.2.1 t) *
      h15PostFEOrientationArchimedeanFactor p.2.2.2 t)

noncomputable def h15PostFEDegenerateCollisionDiagonalAtom
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ)
    (p : H15PostFEMissingPairAtomIndex) : ℝ :=
  h15PostFEDegenerateCollisionRealPrefactor n g U Q t p *
    h15PostFECollidingPhaseDiagonal
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1)
      (h15PostFEDegenerateCollisionComplexCoefficient n g U Q t p)

noncomputable def h15PostFEDegenerateCollisionSecondHarmonicAtom
    (M : ℕ) [NeZero M] (n g U Q r : ℕ) (t : ℝ)
    (p : H15PostFEMissingPairAtomIndex) : ℝ :=
  h15PostFEDegenerateCollisionRealPrefactor n g U Q t p *
    h15PostFECollidingPhaseSecondHarmonic
      (h15PostFELiftedMissingFrequency M p.1)
      (h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1)
      (h15PostFEDegenerateCollisionComplexCoefficient n g U Q t p)
      (ZMod.stdAddChar
        ((r : ZMod M) * h15PostFELiftedMissingFrequency M p.1))

/-- One genuine colliding H15 atom is exactly its diagonal plus its second
harmonic. -/
theorem h15PostFEEndpointPairAtom_eq_collisionDiagonal_add_secondHarmonic
    {n g U Q r : ℕ}
    [NeZero (h15PostFEActualCommonSuperperiod n g U Q)]
    (hQ : 0 < Q) (t : ℝ)
    {p : H15PostFEMissingPairAtomIndex}
    (hp : p ∈ h15PostFEDegenerateCrossModulusCollisionSupport
      (h15PostFEActualCommonSuperperiod n g U Q) n g U Q) :
    h15PostFEEndpointMissingAtom n g U Q r p.1 *
        h15PostFEOrientedPairAtomWithoutFrequency n g U Q r t p.2 =
      h15PostFEDegenerateCollisionDiagonalAtom
          (h15PostFEActualCommonSuperperiod n g U Q) n g U Q t p +
        h15PostFEDegenerateCollisionSecondHarmonicAtom
          (h15PostFEActualCommonSuperperiod n g U Q) n g U Q r t p := by
  let M := h15PostFEActualCommonSuperperiod n g U Q
  letI : NeZero M := ⟨(h15PostFEActualCommonSuperperiod_pos
    n g U Q hQ).ne'⟩
  have hbase := h15PostFEDegenerateCrossModulusCollisionSupport_mem_base hp
  have hpair := (Finset.mem_product.mp hbase.2).1
  have hm := h15PostFEActualMissingPhase_eq_commonSuperperiod hQ hbase.1 r
  have hk := h15PostFEActualPairPhase_eq_commonSuperperiod hQ hpair
    p.2.2.1 p.2.2.2 r
  have hcore :=
    h15PostFECollidingCharacterProduct_eq_diagonal_add_secondHarmonic
      (h15PostFEDegenerateCrossModulusCollisionSupport_collides hp)
      (h15PostFEDegenerateCollisionComplexCoefficient n g U Q t p) r
  have hcoreLit :
      (h15PostFEReducedDoubledAdditivePhase r p.1.2 p.1.1).im *
          (h15PostFEDegenerateCollisionComplexCoefficient n g U Q t p *
            h15PostFECommonPairAdditivePhase p.2.2.1 p.2.2.2 r
              p.2.1.1.1 p.2.1.1.2 p.2.1.2.1 p.2.1.2.2).re =
        h15PostFECollidingPhaseDiagonal
            (h15PostFELiftedMissingFrequency M p.1)
            (h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1)
            (h15PostFEDegenerateCollisionComplexCoefficient n g U Q t p) +
          h15PostFECollidingPhaseSecondHarmonic
            (h15PostFELiftedMissingFrequency M p.1)
            (h15PostFELiftedPairFrequency M p.2.2.1 p.2.2.2 p.2.1)
            (h15PostFEDegenerateCollisionComplexCoefficient n g U Q t p)
            (ZMod.stdAddChar
              ((r : ZMod M) * h15PostFELiftedMissingFrequency M p.1)) := by
    rw [hm, hk]
    exact hcore
  have hc :
      h15PostFEOrderedPairCollectedScalarWithoutFrequency n g U Q t p.2.1 *
          (conj (h15PostFEOrientationArchimedeanFactor p.2.2.1 t) *
            h15PostFEOrientationArchimedeanFactor p.2.2.2 t *
            h15PostFECommonPairAdditivePhase p.2.2.1 p.2.2.2 r
              p.2.1.1.1 p.2.1.1.2 p.2.1.2.1 p.2.1.2.2) =
        h15PostFEDegenerateCollisionComplexCoefficient n g U Q t p *
          h15PostFECommonPairAdditivePhase p.2.2.1 p.2.2.2 r
            p.2.1.1.1 p.2.1.1.2 p.2.1.2.1 p.2.1.2.2 := by
    unfold h15PostFEDegenerateCollisionComplexCoefficient
    ring
  unfold h15PostFEEndpointMissingAtom h15PostFEJointMissingAtom
    h15PostFEOrientedPairAtomWithoutFrequency
    h15PostFEDegenerateCollisionDiagonalAtom
    h15PostFEDegenerateCollisionSecondHarmonicAtom
    h15PostFEDegenerateCollisionRealPrefactor
  rw [hc]
  rw [show
      h15PostFEResidueFiberEndpointMeanCoefficient n g U Q p.1.1 *
          (h15PostFEReducedDoubledAdditivePhase r p.1.2 p.1.1).im *
          ((4 / (2 * h15PairedHyperbolicCoefficient t)) *
            (h15PostFEDegenerateCollisionComplexCoefficient n g U Q t p *
              h15PostFECommonPairAdditivePhase p.2.2.1 p.2.2.2 r
                p.2.1.1.1 p.2.1.1.2 p.2.1.2.1 p.2.1.2.2).re) =
        (h15PostFEResidueFiberEndpointMeanCoefficient n g U Q p.1.1 *
          (4 / (2 * h15PairedHyperbolicCoefficient t))) *
          ((h15PostFEReducedDoubledAdditivePhase r p.1.2 p.1.1).im *
            (h15PostFEDegenerateCollisionComplexCoefficient n g U Q t p *
              h15PostFECommonPairAdditivePhase p.2.2.1 p.2.2.2 r
                p.2.1.1.1 p.2.1.1.2 p.2.1.2.1 p.2.1.2.2).re) by ring]
  rw [hcoreLit]
  ring

/-! ## Quotient-fiber collection -/

noncomputable def h15PostFEDegenerateQuotientFrequencyDiagonalFiber
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (h15PostFEDegenerateCrossModulusCollisionSupport
      M n g U Q).filter
      (fun p => h15PostFEMissingPairDegenerateQuotient p = k),
    h15PostFEDegenerateCollisionDiagonalAtom M n g U Q t p

noncomputable def h15PostFEDegenerateQuotientFrequencySecondHarmonicFiber
    (M : ℕ) [NeZero M] (n g U Q r : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (h15PostFEDegenerateCrossModulusCollisionSupport
      M n g U Q).filter
      (fun p => h15PostFEMissingPairDegenerateQuotient p = k),
    h15PostFEDegenerateCollisionSecondHarmonicAtom M n g U Q r t p

theorem h15PostFEDegenerateQuotientFrequencyFiber_eq_diagonal_add_secondHarmonic
    {n g U Q r : ℕ}
    [NeZero (h15PostFEActualCommonSuperperiod n g U Q)]
    (hQ : 0 < Q) (t : ℝ) (k : ℕ) :
    h15PostFEDegenerateQuotientFrequencyFiberCorrelation
        (h15PostFEActualCommonSuperperiod n g U Q) n g U Q r t k =
      h15PostFEDegenerateQuotientFrequencyDiagonalFiber
          (h15PostFEActualCommonSuperperiod n g U Q) n g U Q t k +
        h15PostFEDegenerateQuotientFrequencySecondHarmonicFiber
          (h15PostFEActualCommonSuperperiod n g U Q) n g U Q r t k := by
  let M := h15PostFEActualCommonSuperperiod n g U Q
  letI : NeZero M := ⟨(h15PostFEActualCommonSuperperiod_pos
    n g U Q hQ).ne'⟩
  unfold h15PostFEDegenerateQuotientFrequencyFiberCorrelation
    h15PostFEDegenerateQuotientFrequencyDiagonalFiber
    h15PostFEDegenerateQuotientFrequencySecondHarmonicFiber
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  exact h15PostFEEndpointPairAtom_eq_collisionDiagonal_add_secondHarmonic
    hQ t (Finset.mem_filter.mp hp).1

/-! ## Complete frequency-level quotient dispersion -/

noncomputable def h15PostFEDegenerateCollisionDiagonalDispersion
    (M : ℕ) [NeZero M] (n g U Q : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ h15PostFEDegenerateQuotientSupport M n g U Q,
    h15PostFEDegenerateQuotientFrequencyDiagonalFiber M n g U Q t k

noncomputable def h15PostFEDegenerateCollisionSecondHarmonicDispersion
    (M : ℕ) [NeZero M] (n g U Q r : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ h15PostFEDegenerateQuotientSupport M n g U Q,
    h15PostFEDegenerateQuotientFrequencySecondHarmonicFiber
      M n g U Q r t k

/-- Exact collision-shell compression of the complete quotient dispersion. -/
theorem h15PostFEDegenerateFrequencyQuotientDispersion_eq_diagonal_add_secondHarmonic
    {n g U Q r : ℕ}
    [NeZero (h15PostFEActualCommonSuperperiod n g U Q)]
    (hQ : 0 < Q) (t : ℝ) :
    h15PostFEDegenerateFrequencyQuotientDispersion
        (h15PostFEActualCommonSuperperiod n g U Q) n g U Q r t =
      h15PostFEDegenerateCollisionDiagonalDispersion
          (h15PostFEActualCommonSuperperiod n g U Q) n g U Q t +
        h15PostFEDegenerateCollisionSecondHarmonicDispersion
          (h15PostFEActualCommonSuperperiod n g U Q) n g U Q r t := by
  let M := h15PostFEActualCommonSuperperiod n g U Q
  letI : NeZero M := ⟨(h15PostFEActualCommonSuperperiod_pos
    n g U Q hQ).ne'⟩
  unfold h15PostFEDegenerateFrequencyQuotientDispersion
    h15PostFEDegenerateCollisionDiagonalDispersion
    h15PostFEDegenerateCollisionSecondHarmonicDispersion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  exact h15PostFEDegenerateQuotientFrequencyFiber_eq_diagonal_add_secondHarmonic
    hQ t k

end NBMellinTools.NB12
