import Mathlib.Analysis.Fourier.ZMod
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmGate4Strategy

/-!
# Gate 4: exact finite Parseval identity in primitive coordinates

This module identifies each primitive `(g,q)` row from the exact Gate-4
reindexing with an additive Fourier transform on `ZMod q`.  It proves the
full-period Parseval identity without analytic assumptions.

The right-hand side is `q` times the squared `ℓ²` norm of the transformed
residue coefficients.  Thus Parseval alone does not give decay in `g` or `q`:
such decay must come from a new bound on those coefficient energies or from
signed cancellation between distinct `(g,q)` rows.  No such bound is asserted
here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Parseval

open scoped BigOperators ComplexConjugate Topology
open AddChar Filter Finset ZMod
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Strategy
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHighProductResidues

/-! ## Finite additive Parseval -/

private lemma star_stdAddChar {q : ℕ} [NeZero q] (x : ZMod q) :
    starRingEnd ℂ (stdAddChar x) = stdAddChar (-x) := by
  change ((starRingEnd ℂ).compAddChar stdAddChar) x = _
  rw [AddChar.starComp_eq_inv (by
    rw [ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne q))]
  simp

private lemma star_phase_mul_phase {q : ℕ} [NeZero q]
    (h a b : ZMod q) :
    starRingEnd ℂ (stdAddChar (h * a)) * stdAddChar (h * b) =
      stdAddChar (h * (b - a)) := by
  rw [star_stdAddChar, ← map_add_eq_mul]
  congr 1
  ring

/-- Full-period Parseval for the positive-sign additive Fourier convention.
The normalization is the counting-measure normalization: the frequency energy
is `q` times the coefficient energy. -/
theorem additiveFourier_parseval {q : ℕ} [NeZero q] (c : ZMod q → ℂ) :
    ∑ h : ZMod q,
        Complex.normSq (∑ a : ZMod q, c a * stdAddChar (h * a)) =
      (q : ℝ) * ∑ a : ZMod q, Complex.normSq (c a) := by
  classical
  apply Complex.ofReal_injective
  push_cast
  change (∑ h : ZMod q,
      (Complex.normSq (∑ a : ZMod q, c a * stdAddChar (h * a)) : ℂ)) =
    (q : ℂ) * ∑ a : ZMod q, (Complex.normSq (c a) : ℂ)
  simp_rw [Complex.normSq_eq_conj_mul_self]
  simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ h : ZMod q, ∑ a : ZMod q, ∑ b : ZMod q,
        starRingEnd ℂ (c a) * starRingEnd ℂ (stdAddChar (h * a)) *
          (c b * stdAddChar (h * b))) =
      ∑ a : ZMod q, ∑ b : ZMod q,
        starRingEnd ℂ (c a) * c b *
          ∑ h : ZMod q, stdAddChar (h * (b - a)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      calc
        starRingEnd ℂ (c a) * starRingEnd ℂ (stdAddChar (h * a)) *
            (c b * stdAddChar (h * b)) =
          starRingEnd ℂ (c a) * c b *
            (starRingEnd ℂ (stdAddChar (h * a)) *
              stdAddChar (h * b)) := by ring
        _ = _ := by rw [star_phase_mul_phase]
    _ = ∑ a : ZMod q, (q : ℂ) * (starRingEnd ℂ (c a) * c a) := by
      simp_rw [AddChar.sum_mulShift (ψ := stdAddChar) _
        (ZMod.isPrimitive_stdAddChar q)]
      push_cast
      simp only [sub_eq_zero, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, ZMod.card]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-! ## The primitive Gate-4 coefficients as a `ZMod` Fourier transform -/

/-- Extension by zero of the primitive residue coefficient to every class in
`ZMod q`. -/
noncomputable def highProductPrimitiveCoefficientOnZMod
    (X D J Y g q : ℕ) (a : ZMod q) : ℂ :=
  if Nat.Coprime a.val q then
    (highProductPrimitiveCoefficient X D J Y g q a.val : ℂ)
  else 0

/-- The additive Fourier row attached to the primitive coefficient vector. -/
noncomputable def highProductPrimitiveFourierRow
    (X D J Y g q : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  ∑ a : ZMod q,
    highProductPrimitiveCoefficientOnZMod X D J Y g q a *
      stdAddChar (h * a)

/-- The exact coefficient energy appearing on the Parseval side. -/
noncomputable def highProductPrimitiveCoefficientEnergy
    (X D J Y g q : ℕ) : ℝ :=
  ∑ a ∈ ehmReducedResidues q,
    (highProductPrimitiveCoefficient X D J Y g q a) ^ 2

/-- The explicit Parseval output `F_g(q)`. -/
noncomputable def highProductPrimitiveParsevalEnergy
    (X D J Y g q : ℕ) : ℝ :=
  (q : ℝ) * highProductPrimitiveCoefficientEnergy X D J Y g q

private theorem sum_zmod_coprimeIndicator {q : ℕ} [NeZero q]
    {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    (∑ a : ZMod q, if Nat.Coprime a.val q then F a.val else 0) =
      ∑ a ∈ ehmReducedResidues q, F a := by
  classical
  calc
    _ = ∑ i : Fin q,
        if Nat.Coprime (ZMod.finEquiv q i).val q then
          F (ZMod.finEquiv q i).val else 0 := by
      exact (ZMod.finEquiv q).toEquiv.sum_comp
        (fun a : ZMod q ↦ if Nat.Coprime a.val q then F a.val else 0) |>.symm
    _ = ∑ a ∈ Finset.range q, if Nat.Coprime a q then F a else 0 := by
      have hfin (i : Fin q) : (ZMod.finEquiv q i).val = i.val := by
        rcases q with _ | q
        · exact (NeZero.ne 0 rfl).elim
        · rfl
      simp_rw [hfin]
      exact Fin.sum_univ_eq_sum_range
        (fun a : ℕ ↦ (if Nat.Coprime a q then F a else 0 : M)) q
    _ = _ := by
      simp [ehmReducedResidues, Finset.sum_filter]

/-- The rational phase in a primitive row is literally the standard additive
character modulo `q`. -/
theorem ehmVaalerRationalPhase_eq_stdAddChar
    (q : ℕ) [NeZero q] (h : ℤ) (a : ℕ) :
    ehmVaalerRationalPhase h a 1 q =
      ZMod.stdAddChar ((h : ZMod q) * (a : ZMod q)) := by
  have hcast : (h : ZMod q) * (a : ZMod q) =
      ((h * (a : ℤ) : ℤ) : ZMod q) := by
    push_cast
    rfl
  rw [hcast, ZMod.stdAddChar_coe]
  rw [ehmVaalerRationalPhase_eq_exp]
  congr 1
  push_cast
  field_simp [NeZero.ne q]

/-- Each primitive gcd stratum is exactly the corresponding `ZMod q` Fourier
row evaluated at the residue class of the integer frequency `h`. -/
theorem highProductPrimitiveGcdStratum_eq_fourierRow
    (X D J Y g q : ℕ) [NeZero q] (h : ℤ) :
    highProductPrimitiveGcdStratum h X D J Y g q =
      highProductPrimitiveFourierRow X D J Y g q (h : ZMod q) := by
  classical
  unfold highProductPrimitiveGcdStratum highProductPrimitiveSummand
    highProductPrimitiveFourierRow highProductPrimitiveCoefficientOnZMod
  simp_rw [ite_mul, zero_mul]
  calc
    (∑ a ∈ ehmReducedResidues q,
        (highProductPrimitiveCoefficient X D J Y g q a : ℂ) *
          ehmVaalerRationalPhase h a 1 q) =
      ∑ a ∈ ehmReducedResidues q,
        (highProductPrimitiveCoefficient X D J Y g q a : ℂ) *
          stdAddChar ((h : ZMod q) * (a : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [ehmVaalerRationalPhase_eq_stdAddChar]
    _ = ∑ a : ZMod q,
        if Nat.Coprime a.val q then
          (highProductPrimitiveCoefficient X D J Y g q a.val : ℂ) *
            stdAddChar ((h : ZMod q) * (a.val : ZMod q))
        else 0 := by
      exact (sum_zmod_coprimeIndicator
        (fun a : ℕ ↦
          (highProductPrimitiveCoefficient X D J Y g q a : ℂ) *
            stdAddChar ((h : ZMod q) * (a : ZMod q)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [ZMod.natCast_zmod_val]

private theorem coefficientOnZMod_energy_eq
    (X D J Y g q : ℕ) [NeZero q] :
    (∑ a : ZMod q,
      Complex.normSq (highProductPrimitiveCoefficientOnZMod X D J Y g q a)) =
        highProductPrimitiveCoefficientEnergy X D J Y g q := by
  classical
  unfold highProductPrimitiveCoefficientOnZMod
    highProductPrimitiveCoefficientEnergy
  calc
    (∑ a : ZMod q, Complex.normSq
        (if Nat.Coprime a.val q then
          (highProductPrimitiveCoefficient X D J Y g q a.val : ℂ)
        else 0)) =
      ∑ a : ZMod q, if Nat.Coprime a.val q then
        (highProductPrimitiveCoefficient X D J Y g q a.val) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs
      · rw [Complex.normSq_ofReal]
        ring
      · simp
    _ = _ := sum_zmod_coprimeIndicator
      (fun a : ℕ ↦ (highProductPrimitiveCoefficient X D J Y g q a) ^ 2)

/-- Exact Stage-2 identity for the transformed Gate-4 coefficients. -/
theorem highProductPrimitiveFourierRow_parseval
    (X D J Y g q : ℕ) [NeZero q] :
    (∑ h : ZMod q,
      Complex.normSq (highProductPrimitiveFourierRow X D J Y g q h)) =
        highProductPrimitiveParsevalEnergy X D J Y g q := by
  rw [highProductPrimitiveParsevalEnergy,
    ← coefficientOnZMod_energy_eq]
  exact additiveFourier_parseval
    (highProductPrimitiveCoefficientOnZMod X D J Y g q)

/-- The Parseval output is nonnegative.  This makes explicit that no signed
Möbius cancellation between different moduli survives on the right-hand side
of the one-row identity. -/
theorem highProductPrimitiveParsevalEnergy_nonneg
    (X D J Y g q : ℕ) :
    0 ≤ highProductPrimitiveParsevalEnergy X D J Y g q := by
  unfold highProductPrimitiveParsevalEnergy
    highProductPrimitiveCoefficientEnergy
  positivity

end RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Parseval
