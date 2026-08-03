import Mathlib.Data.Fintype.Units
import Mathlib.Data.ZMod.Units
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmPrimeResidues
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation

/-!
# Residue and inverse-residue forms of the high Ehm product tail

For each fixed reciprocal denominator `m`, this module partitions the exact
high-product row by the ordinary residue `n % m`.  It then separates unit
and nonunit residues and relabels the unit part by inversion in
`(ZMod m)ˣ`.

The inverse relabeling is deliberately literal: both the phase and its
coefficient are evaluated at the inverse residue.  Thus it does not turn
the Ehm tail into a standard Bettin--Chandee form with independent
coefficients.  The nonunit residue form also remains as an exact summand.
No analytic estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmHighProductResidues

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeResidues
open RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation

/-! ## Exact additive residue decomposition -/

/-- The entire paired high-product coefficient carried by one ordinary
residue class modulo `m`. -/
noncomputable def ehmDyadicVaalerHighProductResidueWeight
    (X D J Y m r : ℕ) : ℝ :=
  ∑ n ∈ (ehmDyadicVaalerHighProductRange J Y).filter
      (fun n ↦ n % m = r),
    ehmDyadicVaalerPairedProductCoefficient X D m n / (n : ℝ)

/-- The high-product row reconstructed from ordinary additive residue
classes. -/
noncomputable def ehmDyadicVaalerHighProductResidueForm
    (h : ℤ) (X D J Y m : ℕ) : ℂ :=
  ∑ r ∈ Finset.range m,
    (ehmDyadicVaalerHighProductResidueWeight X D J Y m r : ℂ) *
      ehmVaalerRationalPhase h r 1 m

/-- Exact residue-class partition of the high-product paired row. -/
theorem ehmDyadicVaalerPairedHighProductRow_eq_residueForm
    (h : ℤ) (X D J Y m : ℕ) (hm : m ≠ 0) :
    ehmDyadicVaalerPairedHighProductRow h X D J Y m =
      ehmDyadicVaalerHighProductResidueForm h X D J Y m := by
  classical
  let s : Finset ℕ := ehmDyadicVaalerHighProductRange J Y
  let t : Finset ℕ := Finset.range m
  let g : ℕ → ℕ := fun n ↦ n % m
  let F : ℕ → ℂ := fun n ↦
    ((ehmDyadicVaalerPairedProductCoefficient X D m n /
      (n : ℝ) : ℝ) : ℂ) * ehmVaalerRationalPhase h n 1 m
  have hmap : ∀ n ∈ s, g n ∈ t := by
    intro n _
    simp only [g, t, Finset.mem_range]
    exact Nat.mod_lt n (Nat.pos_of_ne_zero hm)
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to (s := s) (t := t) hmap F
  unfold ehmDyadicVaalerPairedHighProductRow
    ehmDyadicVaalerPairedProductSummand
    ehmDyadicVaalerHighProductResidueForm
  change (∑ n ∈ s, F n) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro r _
  unfold ehmDyadicVaalerHighProductResidueWeight
  change
    (∑ n ∈ s with g n = r, F n) =
      ((∑ n ∈ s with g n = r,
        ehmDyadicVaalerPairedProductCoefficient X D m n /
          (n : ℝ) : ℝ) : ℂ) *
        ehmVaalerRationalPhase h r 1 m
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hnmod : n % m = r := by
    simpa only [g] using (Finset.mem_filter.mp hn).2
  unfold F
  rw [ehmVaalerRationalPhase_mod h n m hm, hnmod]
  norm_cast

/-! ## Unit and nonunit residue sectors -/

/-- Reduced residue classes modulo `m`. -/
def ehmReducedResidues (m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun r ↦ Nat.Coprime r m)

/-- Unit-residue contribution to the high-product row. -/
noncomputable def ehmDyadicVaalerHighProductUnitResidueForm
    (h : ℤ) (X D J Y m : ℕ) : ℂ :=
  ∑ r ∈ ehmReducedResidues m,
    (ehmDyadicVaalerHighProductResidueWeight X D J Y m r : ℂ) *
      ehmVaalerRationalPhase h r 1 m

/-- Nonunit-residue contribution.  This includes all gcd strata that a
Dirichlet-character or modular-inverse expansion omits. -/
noncomputable def ehmDyadicVaalerHighProductNonunitResidueForm
    (h : ℤ) (X D J Y m : ℕ) : ℂ :=
  ∑ r ∈ Finset.range m,
    if Nat.Coprime r m then 0 else
      (ehmDyadicVaalerHighProductResidueWeight X D J Y m r : ℂ) *
        ehmVaalerRationalPhase h r 1 m

theorem ehmDyadicVaalerHighProductResidueForm_eq_unit_add_nonunit
    (h : ℤ) (X D J Y m : ℕ) :
    ehmDyadicVaalerHighProductResidueForm h X D J Y m =
      ehmDyadicVaalerHighProductUnitResidueForm h X D J Y m +
        ehmDyadicVaalerHighProductNonunitResidueForm h X D J Y m := by
  classical
  unfold ehmDyadicVaalerHighProductResidueForm
    ehmDyadicVaalerHighProductUnitResidueForm
    ehmDyadicVaalerHighProductNonunitResidueForm
    ehmReducedResidues
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : Nat.Coprime r m
  · rw [if_pos hr, if_pos hr]
    simp
  · rw [if_neg hr, if_neg hr]
    simp

theorem ehmDyadicVaalerPairedHighProductRow_eq_unit_add_nonunit
    (h : ℤ) (X D J Y m : ℕ) (hm : m ≠ 0) :
    ehmDyadicVaalerPairedHighProductRow h X D J Y m =
      ehmDyadicVaalerHighProductUnitResidueForm h X D J Y m +
        ehmDyadicVaalerHighProductNonunitResidueForm h X D J Y m := by
  rw [ehmDyadicVaalerPairedHighProductRow_eq_residueForm h X D J Y m hm,
    ehmDyadicVaalerHighProductResidueForm_eq_unit_add_nonunit]

/-! ## Literal inverse relabeling of the unit sector -/

private theorem sum_reducedResidues_eq_sum_units
    (m : ℕ) [NeZero m] (F : ℕ → ℂ) :
    (∑ r ∈ ehmReducedResidues m, F r) =
      ∑ u : (ZMod m)ˣ, F (u : ZMod m).val := by
  classical
  apply Finset.sum_bij
    (fun r hr ↦ ZMod.unitOfCoprime r (Finset.mem_filter.mp hr).2)
  · intro r hr
    simp
  · intro a ha b hb hab
    have habZ : (a : ZMod m) = (b : ZMod m) :=
      congrArg Units.val hab
    have habVal := congrArg ZMod.val habZ
    have haLt : a < m := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hbLt : b < m := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt haLt,
      Nat.mod_eq_of_lt hbLt] using habVal
  · intro u _
    let r : ℕ := (u : ZMod m).val
    have hrLt : r < m := ZMod.val_lt (u : ZMod m)
    have hrCoprime : Nat.Coprime r m := ZMod.val_coe_unit_coprime u
    refine ⟨r, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hrLt, hrCoprime⟩, ?_⟩
    apply Units.ext
    exact ZMod.natCast_zmod_val (u : ZMod m)
  · intro r hr
    apply congrArg F
    have hrLt : r < m := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hrLt]

private def unitInverseEquiv (m : ℕ) : (ZMod m)ˣ ≃ (ZMod m)ˣ where
  toFun u := u⁻¹
  invFun u := u⁻¹
  left_inv u := inv_inv u
  right_inv u := inv_inv u

/-- The unit sector after the exact permutation `u ↦ u⁻¹`.  Crucially,
the residue weight is also evaluated at the inverse residue. -/
noncomputable def ehmDyadicVaalerHighProductInverseUnitResidueForm
    (h : ℤ) (X D J Y m : ℕ) (hm : m ≠ 0) : ℂ := by
  classical
  letI : NeZero m := ⟨hm⟩
  exact ∑ u : (ZMod m)ˣ,
    (ehmDyadicVaalerHighProductResidueWeight X D J Y m
      ((u⁻¹ : (ZMod m)ˣ) : ZMod m).val : ℂ) *
        ehmVaalerRationalPhase h
          ((u⁻¹ : (ZMod m)ˣ) : ZMod m).val 1 m

/-- Exact inverse relabeling of the unit sector.  This is the closest
finite Kloosterman-style form available without altering the Ehm phase or
discarding coefficients. -/
theorem ehmDyadicVaalerHighProductUnitResidueForm_eq_inverseRelabeling
    (h : ℤ) (X D J Y m : ℕ) (hm : m ≠ 0) :
    ehmDyadicVaalerHighProductUnitResidueForm h X D J Y m =
      ehmDyadicVaalerHighProductInverseUnitResidueForm
        h X D J Y m hm := by
  classical
  letI : NeZero m := ⟨hm⟩
  unfold ehmDyadicVaalerHighProductUnitResidueForm
    ehmDyadicVaalerHighProductInverseUnitResidueForm
  rw [sum_reducedResidues_eq_sum_units]
  exact (Equiv.sum_comp (unitInverseEquiv m)
    (fun u : (ZMod m)ˣ ↦
      (ehmDyadicVaalerHighProductResidueWeight X D J Y m
        (u : ZMod m).val : ℂ) *
          ehmVaalerRationalPhase h (u : ZMod m).val 1 m)).symm

/-- Full exact high-tail decomposition into an inverse-relabelled unit
sector and the untouched nonunit sector. -/
theorem ehmDyadicVaalerPairedHighProductRow_eq_inverseUnit_add_nonunit
    (h : ℤ) (X D J Y m : ℕ) (hm : m ≠ 0) :
    ehmDyadicVaalerPairedHighProductRow h X D J Y m =
      ehmDyadicVaalerHighProductInverseUnitResidueForm h X D J Y m hm +
        ehmDyadicVaalerHighProductNonunitResidueForm h X D J Y m := by
  rw [ehmDyadicVaalerPairedHighProductRow_eq_unit_add_nonunit
      h X D J Y m hm,
    ehmDyadicVaalerHighProductUnitResidueForm_eq_inverseRelabeling
      h X D J Y m hm]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmHighProductResidues
