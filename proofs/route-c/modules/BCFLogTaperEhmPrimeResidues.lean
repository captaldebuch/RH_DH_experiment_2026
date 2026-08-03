import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmBurgessAudit

/-!
# Additive residue classes in the Ehm Vaaler main row

For a fixed reciprocal denominator `m`, the normalized main row is an
ordinary rational additive-character sum in the von Mangoldt variable.  This
file partitions that row exactly by residue classes modulo `m`.  It is the
finite algebraic entry point for a large-sieve, prime-in-progressions, or
dispersion treatment of the main row.

No prime number theorem in arithmetic progressions and no cancellation
estimate is asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeResidues

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmBurgessAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHarmonicAbel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerNormalizedCharacters

/-! ## Periodicity of the rational phase -/

/-- The rational Vaaler phase is multiplicative under addition of its
integer numerator variable. -/
theorem ehmVaalerRationalPhase_add
    (h : ℤ) (a b d m : ℕ) :
    ehmVaalerRationalPhase h (a + b) d m =
      ehmVaalerRationalPhase h a d m *
        ehmVaalerRationalPhase h b d m := by
  rw [ehmVaalerRationalPhase_eq_exp,
    ehmVaalerRationalPhase_eq_exp,
    ehmVaalerRationalPhase_eq_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Complete resonance classification for a general numerator product
`q*d`. -/
theorem ehmVaalerRationalPhase_eq_one_iff_dvd
    (h : ℤ) (q d m : ℕ) (hm : m ≠ 0) :
    ehmVaalerRationalPhase h q d m = 1 ↔
      (m : ℤ) ∣ h * ((q * d : ℕ) : ℤ) := by
  rw [ehmVaalerRationalPhase_eq_exp]
  rw [show
    (((2 * Real.pi * (h : ℝ) *
      (((q * d : ℕ) : ℝ) / (m : ℝ)) : ℝ) : ℂ) * Complex.I) =
      2 * Real.pi * Complex.I *
        ((h * ((q * d : ℕ) : ℤ) : ℤ) : ℂ) / (m : ℂ) by
    push_cast
    ring]
  exact complex_exp_int_rational_eq_one_iff_dvd
    (h * ((q * d : ℕ) : ℤ)) m hm

/-- The fixed-denominator phase depends only on the numerator modulo `m`. -/
theorem ehmVaalerRationalPhase_mod
    (h : ℤ) (j m : ℕ) (hm : m ≠ 0) :
    ehmVaalerRationalPhase h j 1 m =
      ehmVaalerRationalPhase h (j % m) 1 m := by
  conv_lhs =>
    rw [show j = j % m + m * (j / m) by
      exact (Nat.mod_add_div j m).symm]
  rw [ehmVaalerRationalPhase_add]
  have hres : ehmVaalerRationalPhase h (m * (j / m)) 1 m = 1 := by
    rw [ehmVaalerRationalPhase_eq_one_iff_dvd h (m * (j / m)) 1 m hm]
    refine ⟨h * ((j / m : ℕ) : ℤ), ?_⟩
    push_cast
    ring
  rw [hres, mul_one]

/-! ## Exact residue-class partition -/

/-- The total logarithmic prime weight in one residue class modulo `m`. -/
noncomputable def ehmVaalerMainPrimeResidueWeight
    (J m r : ℕ) : ℝ :=
  ∑ j ∈ (Finset.Icc 2 J).filter (fun j ↦ j % m = r),
    ehmDyadicVaalerMainPrimeWeight j

/-- The fixed-denominator main row reconstructed from its additive residue
classes. -/
noncomputable def ehmVaalerMainPrimeResidueForm
    (h : ℤ) (J m : ℕ) : ℂ :=
  ∑ r ∈ Finset.range m,
    (ehmVaalerMainPrimeResidueWeight J m r : ℂ) *
      ehmVaalerRationalPhase h r 1 m

/-- Exact partition of the additive prime row into residue classes modulo
its reciprocal denominator. -/
theorem ehmVaalerMainAdditivePrimeRow_eq_residueForm
    (h : ℤ) (J m : ℕ) (hm : m ≠ 0) :
    ehmVaalerMainAdditivePrimeRow h J m =
      ehmVaalerMainPrimeResidueForm h J m := by
  classical
  let s : Finset ℕ := Finset.Icc 2 J
  let t : Finset ℕ := Finset.range m
  let g : ℕ → ℕ := fun j ↦ j % m
  let F : ℕ → ℂ := fun j ↦
    (ehmDyadicVaalerMainPrimeWeight j : ℂ) *
      ehmVaalerRationalPhase h j 1 m
  have hmap : ∀ j ∈ s, g j ∈ t := by
    intro j _
    simp only [g, t, Finset.mem_range]
    exact Nat.mod_lt j (Nat.pos_of_ne_zero hm)
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to (s := s) (t := t) hmap F
  unfold ehmVaalerMainAdditivePrimeRow ehmVaalerMainPrimeResidueForm
  change (∑ j ∈ s, F j) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro r hr
  unfold ehmVaalerMainPrimeResidueWeight
  change
    (∑ j ∈ s with g j = r, F j) =
      ((∑ j ∈ s with g j = r,
        ehmDyadicVaalerMainPrimeWeight j : ℝ) : ℂ) *
          ehmVaalerRationalPhase h r 1 m
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjmod : j % m = r := by
    simpa only [g] using (Finset.mem_filter.mp hj).2
  unfold F
  rw [ehmVaalerRationalPhase_mod h j m hm, hjmod]

/-- The complete normalized main form with every fixed-denominator prime
row replaced by its exact residue-class form. -/
theorem ehmDyadicVaalerNormalizedMainPhaseForm_eq_residueForms
    (h : ℤ) (X J : ℕ) :
    ehmDyadicVaalerNormalizedMainPhaseForm h X J =
      ∑ m ∈ Finset.Icc 1 (2 * X),
        (ehmDyadicVaalerMainMobiusWeight X m : ℂ) *
          ehmVaalerMainPrimeResidueForm h J m := by
  classical
  rw [ehmDyadicVaalerNormalizedMainPhaseForm_eq_mobius_additiveRows]
  apply Finset.sum_congr rfl
  intro m hm
  have hmne : m ≠ 0 := by
    have : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    omega
  rw [ehmVaalerMainAdditivePrimeRow_eq_residueForm h J m hmne]

/-! ## Exact centering by the reduced residue classes -/

/-- The reduced-residue additive phase sum.  This is the finite Ramanujan
sum in the normalization used by the Ehm Vaaler phase. -/
noncomputable def ehmVaalerReducedResiduePhaseSum
    (h : ℤ) (m : ℕ) : ℂ :=
  ∑ r ∈ Finset.range m,
    if Nat.Coprime r m then ehmVaalerRationalPhase h r 1 m else 0

/-- A freely chosen per-reduced-class baseline.  Analytically, a
prime-number-theorem input would choose this baseline to match the common
main mass of the coprime residue classes. -/
noncomputable def ehmVaalerMainPrimeResidueBaselineForm
    (h : ℤ) (m : ℕ) (L : ℝ) : ℂ :=
  ∑ r ∈ Finset.range m,
    ((if Nat.Coprime r m then L else 0 : ℝ) : ℂ) *
      ehmVaalerRationalPhase h r 1 m

/-- The exactly centered residue-class form after subtracting the baseline
on reduced residue classes only. -/
noncomputable def ehmVaalerMainPrimeCenteredResidueForm
    (h : ℤ) (J m : ℕ) (L : ℝ) : ℂ :=
  ∑ r ∈ Finset.range m,
    ((ehmVaalerMainPrimeResidueWeight J m r -
      if Nat.Coprime r m then L else 0 : ℝ) : ℂ) *
        ehmVaalerRationalPhase h r 1 m

/-- The uncentered residue form is exactly its centered fluctuation plus the
chosen reduced-residue baseline. -/
theorem ehmVaalerMainPrimeResidueForm_eq_centered_add_baseline
    (h : ℤ) (J m : ℕ) (L : ℝ) :
    ehmVaalerMainPrimeResidueForm h J m =
      ehmVaalerMainPrimeCenteredResidueForm h J m L +
        ehmVaalerMainPrimeResidueBaselineForm h m L := by
  classical
  unfold ehmVaalerMainPrimeResidueForm
    ehmVaalerMainPrimeCenteredResidueForm
    ehmVaalerMainPrimeResidueBaselineForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> push_cast <;> ring

/-- The baseline contribution is the scalar baseline times the finite
Ramanujan phase sum. -/
theorem ehmVaalerMainPrimeResidueBaselineForm_eq_mul_reducedResiduePhaseSum
    (h : ℤ) (m : ℕ) (L : ℝ) :
    ehmVaalerMainPrimeResidueBaselineForm h m L =
      (L : ℂ) * ehmVaalerReducedResiduePhaseSum h m := by
  classical
  unfold ehmVaalerMainPrimeResidueBaselineForm
    ehmVaalerReducedResiduePhaseSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> push_cast <;> ring

/-- Exact centered/Ramanujan decomposition of the complete normalized main
form for any baseline selected separately at each denominator. -/
theorem ehmDyadicVaalerNormalizedMainPhaseForm_eq_centered_add_ramanujan
    (h : ℤ) (X J : ℕ) (L : ℕ → ℝ) :
    ehmDyadicVaalerNormalizedMainPhaseForm h X J =
      ∑ m ∈ Finset.Icc 1 (2 * X),
        (ehmDyadicVaalerMainMobiusWeight X m : ℂ) *
          (ehmVaalerMainPrimeCenteredResidueForm h J m (L m) +
            (L m : ℂ) * ehmVaalerReducedResiduePhaseSum h m) := by
  classical
  rw [ehmDyadicVaalerNormalizedMainPhaseForm_eq_residueForms]
  apply Finset.sum_congr rfl
  intro m _
  rw [ehmVaalerMainPrimeResidueForm_eq_centered_add_baseline,
    ehmVaalerMainPrimeResidueBaselineForm_eq_mul_reducedResiduePhaseSum]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmPrimeResidues
