import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmHighProductResidues
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTSectorCoupling

/-!
# Gate 4: exact high-product residue lift and the honest coupled target

This module lifts the row-level residue decomposition through the complete
nonzero Vaaler-frequency sum and the outer Möbius sum.  It then puts the
result beside the matching high-product smooth and endpoint correction.

The exact finite identity is

`high correction - high modes = high correction - unit modes - nonunit modes`.

No decay estimate is proved here.  In particular, setting the product cutoff
equal to the full summation endpoint would make the high range empty and would
not constitute a Gate-4 estimate.  The final structure below records the
genuine common-cofinal estimate that remains open.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Strategy

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierResonanceAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHighProductResidues
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTNormalizationAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTSectorCoupling
open RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerAnalyticGate
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-! ## One-row decomposition -/

/-- The inverse-unit sector of one high-product row.  Both the residue weight
and the additive phase are evaluated after the same inversion permutation. -/
noncomputable def highProductInverseUnitSector
    (h : ℤ) (X D J Y m : ℕ) (hm : m ≠ 0) : ℂ :=
  ehmDyadicVaalerHighProductInverseUnitResidueForm h X D J Y m hm

/-- The contribution of all nonunit residue classes to one high-product row. -/
noncomputable def highProductNonunitSector
    (h : ℤ) (X D J Y m : ℕ) : ℂ :=
  ehmDyadicVaalerHighProductNonunitResidueForm h X D J Y m

/-- The complete row in inverse-unit plus nonunit coordinates. -/
noncomputable def highProductTail
    (h : ℤ) (X D J Y m : ℕ) (hm : m ≠ 0) : ℂ :=
  highProductInverseUnitSector h X D J Y m hm +
    highProductNonunitSector h X D J Y m

/-- The inverse/nonunit expression is exactly the original paired high row.
This is a relabeling identity, not an estimate. -/
theorem highProductTail_eq_pairedHighProductRow
    (h : ℤ) (X D J Y m : ℕ) (hm : m ≠ 0) :
    highProductTail h X D J Y m hm =
      ehmDyadicVaalerPairedHighProductRow h X D J Y m := by
  unfold highProductTail highProductInverseUnitSector
    highProductNonunitSector
  exact (ehmDyadicVaalerPairedHighProductRow_eq_inverseUnit_add_nonunit
    h X D J Y m hm).symm

/-! ## Exact gcd stratification of the nonunit sector -/

/-- The part of one nonunit row on which `gcd(r,m)` is exactly `g`. -/
noncomputable def highProductNonunitGcdStratum
    (h : ℤ) (X D J Y m g : ℕ) : ℂ :=
  ∑ r ∈ (Finset.range m).filter (fun r ↦
      ¬Nat.Coprime r m ∧ Nat.gcd r m = g),
    (ehmDyadicVaalerHighProductResidueWeight X D J Y m r : ℂ) *
      ehmVaalerRationalPhase h r 1 m

/-- All nontrivial gcd strata.  For `m ≠ 0`, every nonunit residue belongs
to exactly one index `2 ≤ g ≤ m`. -/
noncomputable def highProductNonunitGcdStrata
    (h : ℤ) (X D J Y m : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 2 m,
    highProductNonunitGcdStratum h X D J Y m g

/-- Exact partition of the nonunit sector by its gcd with the modulus. -/
theorem highProductNonunitSector_eq_gcdStrata
    (h : ℤ) (X D J Y m : ℕ) (hm : m ≠ 0) :
    highProductNonunitSector h X D J Y m =
      highProductNonunitGcdStrata h X D J Y m := by
  classical
  let s : Finset ℕ :=
    (Finset.range m).filter (fun r ↦ ¬Nat.Coprime r m)
  let t : Finset ℕ := Finset.Icc 2 m
  let g : ℕ → ℕ := fun r ↦ Nat.gcd r m
  let F : ℕ → ℂ := fun r ↦
    (ehmDyadicVaalerHighProductResidueWeight X D J Y m r : ℂ) *
      ehmVaalerRationalPhase h r 1 m
  have hmap : ∀ r ∈ s, g r ∈ t := by
    intro r hr
    have hnot : ¬Nat.Coprime r m := (Finset.mem_filter.mp hr).2
    have hgne : Nat.gcd r m ≠ 1 := by
      exact fun hg ↦ hnot (Nat.coprime_iff_gcd_eq_one.mpr hg)
    have hgpos : 0 < Nat.gcd r m :=
      Nat.gcd_pos_of_pos_right r (Nat.pos_of_ne_zero hm)
    change Nat.gcd r m ∈ Finset.Icc 2 m
    exact Finset.mem_Icc.mpr
      ⟨by omega, Nat.gcd_le_right r (Nat.pos_of_ne_zero hm)⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to (s := s) (t := t) hmap F
  unfold highProductNonunitSector
    highProductNonunitGcdStrata highProductNonunitGcdStratum
  change (∑ r ∈ Finset.range m,
      if Nat.Coprime r m then 0 else F r) = _
  calc
    (∑ r ∈ Finset.range m,
        if Nat.Coprime r m then 0 else F r) = ∑ r ∈ s, F r := by
      unfold s
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : Nat.Coprime r m <;> simp [hr]
    _ = ∑ a ∈ t, ∑ r ∈ s with g r = a, F r := hfiber.symm
    _ = _ := by
      unfold s t g F
      simp only [Finset.filter_filter]

/-- Dividing a residue and its modulus by their gcd produces a reduced
residue class. -/
theorem highProductGcdReduced_coprime
    (r m : ℕ) (hm : m ≠ 0) :
    Nat.Coprime (r / Nat.gcd r m) (m / Nat.gcd r m) := by
  exact Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_right r (Nat.pos_of_ne_zero hm))

/-- The additive character on a nonunit residue is exactly the character on
the corresponding primitive residue at the reduced modulus.  Thus gcd strata
do not disappear; they recurse to smaller primitive moduli with transformed
coefficients. -/
theorem ehmVaalerRationalPhase_gcd_reduce
    (h : ℤ) (r m : ℕ) (hm : m ≠ 0) :
    ehmVaalerRationalPhase h r 1 m =
      ehmVaalerRationalPhase h (r / Nat.gcd r m) 1
        (m / Nat.gcd r m) := by
  let g := Nat.gcd r m
  have hgpos : 0 < g := by
    exact Nat.gcd_pos_of_pos_right r (Nat.pos_of_ne_zero hm)
  have hgr : g ∣ r := Nat.gcd_dvd_left r m
  have hgm : g ∣ m := Nat.gcd_dvd_right r m
  have hrg : r / g * g = r := Nat.div_mul_cancel hgr
  have hmg : m / g * g = m := Nat.div_mul_cancel hgm
  have hqne : m / g ≠ 0 := by
    intro hq
    apply hm
    rw [← hmg, hq]
    simp
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hqR : (((m / g : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast hqne
  have hrgR : (((r / g : ℕ) : ℝ)) * (g : ℝ) = (r : ℝ) := by
    exact_mod_cast hrg
  have hmgR : (((m / g : ℕ) : ℝ)) * (g : ℝ) = (m : ℝ) := by
    exact_mod_cast hmg
  unfold ehmVaalerRationalPhase
  apply congrArg (vaalerFourierPhase h)
  simp only [Nat.cast_one, one_div]
  change (r : ℝ) * (m : ℝ)⁻¹ =
    (((r / g : ℕ) : ℝ)) * (((m / g : ℕ) : ℝ))⁻¹
  rw [← hrgR, ← hmgR]
  field_simp [hgR, hqR]

/-! ## Canonical primitive coefficient coordinates -/

/-- The high-product residue weight after the canonical substitution
`m = g*q`, `r = g*a`.  All dependencies remain visible in the arguments. -/
noncomputable def highProductPrimitiveCoefficient
    (X D J Y g q a : ℕ) : ℝ :=
  ehmDyadicVaalerHighProductResidueWeight X D J Y (g * q) (g * a)

/-- One primitive additive-character summand. -/
noncomputable def highProductPrimitiveSummand
    (h : ℤ) (X D J Y g q a : ℕ) : ℂ :=
  (highProductPrimitiveCoefficient X D J Y g q a : ℂ) *
    ehmVaalerRationalPhase h a 1 q

/-- The primitive residue row attached to the gcd scale `g` and reduced
modulus `q`. -/
noncomputable def highProductPrimitiveGcdStratum
    (h : ℤ) (X D J Y g q : ℕ) : ℂ :=
  ∑ a ∈ ehmReducedResidues q,
    highProductPrimitiveSummand h X D J Y g q a

/-- Exact coefficient-level reindexing of one nonunit gcd stratum by
`r = g*a`, `m = g*q`, with `(a,q)=1`. -/
theorem highProductNonunitGcdStratum_eq_primitive
    (h : ℤ) (X D J Y g q : ℕ) (hg : 2 ≤ g) (hq : 0 < q) :
    highProductNonunitGcdStratum h X D J Y (g * q) g =
      highProductPrimitiveGcdStratum h X D J Y g q := by
  classical
  unfold highProductNonunitGcdStratum
    highProductPrimitiveGcdStratum highProductPrimitiveSummand
    highProductPrimitiveCoefficient
  apply Finset.sum_bij (fun r _ ↦ r / g)
  · intro r hr
    have hrange := (Finset.mem_filter.mp hr).1
    have hrdata := (Finset.mem_filter.mp hr).2
    have hrgcd : Nat.gcd r (g * q) = g := hrdata.2
    have hrlt : r < g * q := Finset.mem_range.mp hrange
    have hdivlt : r / g < q := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      simpa [mul_comm] using hrlt
    have hmne : g * q ≠ 0 := Nat.mul_ne_zero (by omega) hq.ne'
    have hcop := highProductGcdReduced_coprime r (g * q) hmne
    have hquot : (g * q) / g = q := Nat.mul_div_cancel_left q (by omega)
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdivlt, ?_⟩
    simpa [hrgcd, hquot] using hcop
  · intro r₁ hr₁ r₂ hr₂ heq
    have hgcd₁ : Nat.gcd r₁ (g * q) = g :=
      (Finset.mem_filter.mp hr₁).2.2
    have hgcd₂ : Nat.gcd r₂ (g * q) = g :=
      (Finset.mem_filter.mp hr₂).2.2
    have hdvd₁ : g ∣ r₁ := by
      rw [← hgcd₁]
      exact Nat.gcd_dvd_left r₁ (g * q)
    have hdvd₂ : g ∣ r₂ := by
      rw [← hgcd₂]
      exact Nat.gcd_dvd_left r₂ (g * q)
    calc
      r₁ = r₁ / g * g := (Nat.div_mul_cancel hdvd₁).symm
      _ = r₂ / g * g := by rw [heq]
      _ = r₂ := Nat.div_mul_cancel hdvd₂
  · intro a ha
    have harange := (Finset.mem_filter.mp ha).1
    have hacoprime := (Finset.mem_filter.mp ha).2
    have halt : a < q := Finset.mem_range.mp harange
    let r := g * a
    have hrlt : r < g * q := by
      exact (Nat.mul_lt_mul_left (by omega)).2 halt
    have hrgcd : Nat.gcd r (g * q) = g := by
      unfold r
      rw [Nat.gcd_mul_left, hacoprime.gcd_eq_one, mul_one]
    have hrnot : ¬Nat.Coprime r (g * q) := by
      rw [Nat.coprime_iff_gcd_eq_one, hrgcd]
      omega
    refine ⟨r, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hrlt, hrnot, hrgcd⟩, ?_⟩
    unfold r
    exact Nat.mul_div_cancel_left a (by omega)
  · intro r hr
    have hrgcd : Nat.gcd r (g * q) = g :=
      (Finset.mem_filter.mp hr).2.2
    have hdvd : g ∣ r := by
      rw [← hrgcd]
      exact Nat.gcd_dvd_left r (g * q)
    have hmul : g * (r / g) = r := by
      simpa [mul_comm] using Nat.div_mul_cancel hdvd
    have hmne : g * q ≠ 0 := Nat.mul_ne_zero (by omega) hq.ne'
    have hphase := ehmVaalerRationalPhase_gcd_reduce h r (g * q) hmne
    have hquot : (g * q) / g = q := Nat.mul_div_cancel_left q (by omega)
    rw [hrgcd, hquot] at hphase
    rw [hmul, hphase]

/-- A gcd stratum is empty unless its index divides the modulus. -/
theorem highProductNonunitGcdStratum_eq_zero_of_not_dvd
    (h : ℤ) (X D J Y m g : ℕ) (hgd : ¬g ∣ m) :
    highProductNonunitGcdStratum h X D J Y m g = 0 := by
  classical
  unfold highProductNonunitGcdStratum
  apply Finset.sum_eq_zero
  intro r hr
  have hrgcd : Nat.gcd r m = g := (Finset.mem_filter.mp hr).2.2
  exfalso
  apply hgd
  rw [← hrgcd]
  exact Nat.gcd_dvd_right r m

/-- The gcd-stratum sum may be restricted exactly to divisors of `m`. -/
theorem highProductNonunitGcdStrata_eq_divisorStrata
    (h : ℤ) (X D J Y m : ℕ) :
    highProductNonunitGcdStrata h X D J Y m =
      ∑ g ∈ (Finset.Icc 2 m).filter (fun g ↦ g ∣ m),
        highProductNonunitGcdStratum h X D J Y m g := by
  classical
  unfold highProductNonunitGcdStrata
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hgd : g ∣ m
  · simp [hgd]
  · simp [hgd, highProductNonunitGcdStratum_eq_zero_of_not_dvd
      h X D J Y m g hgd]

/-- Generic finite hyperbolic reindexing from `(m,g)` with `g ∣ m` to
`(g,q)` with `m = g*q`. -/
theorem sum_divisorScale_reindex
    {A : Type*} [AddCommMonoid A] (M : ℕ) (F : ℕ → ℕ → A) :
    (∑ m ∈ Finset.Icc 1 M,
      ∑ g ∈ (Finset.Icc 2 m).filter (fun g ↦ g ∣ m), F m g) =
        ∑ g ∈ Finset.Icc 2 M,
          ∑ q ∈ Finset.Icc 1 (M / g), F (g * q) g := by
  classical
  let s : Finset ℕ := Finset.Icc 1 M
  let t : ℕ → Finset ℕ := fun m ↦
    (Finset.Icc 2 m).filter (fun g ↦ g ∣ m)
  let u : Finset ℕ := Finset.Icc 2 M
  let v : ℕ → Finset ℕ := fun g ↦ Finset.Icc 1 (M / g)
  rw [Finset.sum_sigma' s t F, Finset.sum_sigma' u v
    (fun g q ↦ F (g * q) g)]
  apply Finset.sum_bij (fun p _ ↦ ⟨p.2, p.1 / p.2⟩)
  · intro p hp
    rcases p with ⟨m, g⟩
    have hp' := Finset.mem_sigma.mp hp
    have hm : m ∈ Finset.Icc 1 M := hp'.1
    have hg : g ∈ (Finset.Icc 2 m).filter (fun g ↦ g ∣ m) := hp'.2
    have hgIcc := (Finset.mem_filter.mp hg).1
    have hgdvd := (Finset.mem_filter.mp hg).2
    have hmBounds := Finset.mem_Icc.mp hm
    have hgBounds := Finset.mem_Icc.mp hgIcc
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨hgBounds.1, hgBounds.2.trans hmBounds.2⟩
    · apply Finset.mem_Icc.mpr
      constructor
      · have hgpos : 0 < g := lt_of_lt_of_le (by omega) hgBounds.1
        exact Nat.div_pos hgBounds.2 hgpos
      · exact Nat.div_le_div_right hmBounds.2
  · intro p₁ hp₁ p₂ hp₂ heq
    rcases p₁ with ⟨m₁, g₁⟩
    rcases p₂ with ⟨m₂, g₂⟩
    have hp₁' := Finset.mem_sigma.mp hp₁
    have hp₂' := Finset.mem_sigma.mp hp₂
    have hgdvd₁ := (Finset.mem_filter.mp hp₁'.2).2
    have hgdvd₂ := (Finset.mem_filter.mp hp₂'.2).2
    have hgEq : g₁ = g₂ := congrArg Sigma.fst heq
    have hqEq : m₁ / g₁ = m₂ / g₂ := by
      have := congrArg (fun p : Sigma fun _ : ℕ ↦ ℕ ↦ p.2) heq
      exact this
    subst g₂
    have hmEq : m₁ = m₂ := calc
      m₁ = m₁ / g₁ * g₁ := (Nat.div_mul_cancel hgdvd₁).symm
      _ = m₂ / g₁ * g₁ := by rw [hqEq]
      _ = m₂ := Nat.div_mul_cancel hgdvd₂
    subst m₂
    rfl
  · intro p hp
    rcases p with ⟨g, q⟩
    have hp' : g ∈ u ∧ q ∈ v g := by
      simpa using Finset.mem_sigma.mp hp
    have hg := Finset.mem_Icc.mp hp'.1
    have hq := Finset.mem_Icc.mp hp'.2
    have hgpos : 0 < g := by omega
    have hqpos : 0 < q := by omega
    have hprod : g * q ≤ M := by
      have := (Nat.le_div_iff_mul_le hgpos).1 hq.2
      simpa [mul_comm] using this
    let p' : Sigma fun _ : ℕ ↦ ℕ := ⟨g * q, g⟩
    have hp'mem : p' ∈ s.sigma t := by
      apply Finset.mem_sigma.mpr
      constructor
      · exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hgpos hqpos, hprod⟩
      · apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_Icc.mpr ⟨hg.1, Nat.le_mul_of_pos_right g hqpos⟩
        · exact dvd_mul_right g q
    refine ⟨p', hp'mem, ?_⟩
    simp [p', Nat.mul_div_cancel_left q hgpos]
  · intro p hp
    rcases p with ⟨m, g⟩
    have hp' := Finset.mem_sigma.mp hp
    have hgdvd := (Finset.mem_filter.mp hp'.2).2
    congr 1
    exact (Nat.div_mul_cancel hgdvd).symm.trans (mul_comm _ _)

/-! ## Lift through every nonzero frequency and outer Möbius weight -/

/-- Complete unit-residue contribution on `1 ≤ m ≤ 2X`, including the
outer Möbius factor and every nonzero Vaaler coefficient. -/
noncomputable def highProductUnitModes
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ∑ m ∈ Finset.Icc 1 (2 * X),
        ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          ehmDyadicVaalerHighProductUnitResidueForm h X D J Y m)

/-- Complete nonunit-residue contribution with the same weights and
frequency support as `highProductUnitModes`. -/
noncomputable def highProductNonunitModes
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ∑ m ∈ Finset.Icc 1 (2 * X),
        ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          ehmDyadicVaalerHighProductNonunitResidueForm h X D J Y m)

/-- The nonunit contribution after exposing every gcd stratum, still with
the complete Vaaler-frequency and outer Möbius weights. -/
noncomputable def highProductNonunitGcdStrataModes
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ∑ m ∈ Finset.Icc 1 (2 * X),
        ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          highProductNonunitGcdStrata h X D J Y m)

/-- Exact full weighted lift of the gcd stratification. -/
theorem highProductNonunitModes_eq_gcdStrataModes
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) :
    highProductNonunitModes V Q X D J Y =
      highProductNonunitGcdStrataModes V Q X D J Y := by
  classical
  unfold highProductNonunitModes highProductNonunitGcdStrataModes
  apply Finset.sum_congr rfl
  intro h _
  apply congrArg (fun z : ℂ ↦ V.coefficient Q h * z)
  apply Finset.sum_congr rfl
  intro m hm
  apply congrArg (fun z : ℂ ↦
    ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) * z))
  exact highProductNonunitSector_eq_gcdStrata h X D J Y m
    (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)

/-- The `g = 1` primitive row is exactly the original unit-residue row. -/
theorem ehmDyadicVaalerHighProductUnitResidueForm_eq_primitiveMain
    (h : ℤ) (X D J Y q : ℕ) :
    ehmDyadicVaalerHighProductUnitResidueForm h X D J Y q =
      highProductPrimitiveGcdStratum h X D J Y 1 q := by
  unfold ehmDyadicVaalerHighProductUnitResidueForm
    highProductPrimitiveGcdStratum highProductPrimitiveSummand
    highProductPrimitiveCoefficient
  simp only [one_mul]

/-- The complete primitive main sector `g = 1`. -/
noncomputable def highProductPrimitiveMainModes
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ∑ q ∈ Finset.Icc 1 (2 * X),
        ((((ArithmeticFunction.moebius q : ℤ) : ℝ) : ℂ) *
          highProductPrimitiveGcdStratum h X D J Y 1 q)

/-- The complete primitive off-diagonal sector `g ≥ 2`, reindexed by
`m = g*q`. -/
noncomputable def highProductPrimitiveOffDiagonalModes
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ∑ g ∈ Finset.Icc 2 (2 * X),
        ∑ q ∈ Finset.Icc 1 ((2 * X) / g),
          ((((ArithmeticFunction.moebius (g * q) : ℤ) : ℝ) : ℂ) *
            highProductPrimitiveGcdStratum h X D J Y g q)

/-- Exact identification of the original unit modes with the primitive
`g = 1` sector. -/
theorem highProductUnitModes_eq_primitiveMainModes
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) :
    highProductUnitModes V Q X D J Y =
      highProductPrimitiveMainModes V Q X D J Y := by
  classical
  unfold highProductUnitModes highProductPrimitiveMainModes
  apply Finset.sum_congr rfl
  intro h _
  apply congrArg (fun z : ℂ ↦ V.coefficient Q h * z)
  apply Finset.sum_congr rfl
  intro q _
  rw [ehmDyadicVaalerHighProductUnitResidueForm_eq_primitiveMain]

/-- Exact outer reindexing of all nonunit modes by `m = g*q`, with
`g ≥ 2` and primitive residue classes modulo `q`. -/
theorem highProductNonunitGcdStrataModes_eq_primitiveOffDiagonalModes
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) :
    highProductNonunitGcdStrataModes V Q X D J Y =
      highProductPrimitiveOffDiagonalModes V Q X D J Y := by
  classical
  unfold highProductNonunitGcdStrataModes
    highProductPrimitiveOffDiagonalModes
  apply Finset.sum_congr rfl
  intro h _
  apply congrArg (fun z : ℂ ↦ V.coefficient Q h * z)
  calc
    (∑ m ∈ Finset.Icc 1 (2 * X),
        ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          highProductNonunitGcdStrata h X D J Y m)) =
      ∑ m ∈ Finset.Icc 1 (2 * X),
        ∑ g ∈ (Finset.Icc 2 m).filter (fun g ↦ g ∣ m),
          ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
            highProductNonunitGcdStratum h X D J Y m g) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [highProductNonunitGcdStrata_eq_divisorStrata,
        Finset.mul_sum]
    _ = ∑ g ∈ Finset.Icc 2 (2 * X),
        ∑ q ∈ Finset.Icc 1 ((2 * X) / g),
          ((((ArithmeticFunction.moebius (g * q) : ℤ) : ℝ) : ℂ) *
            highProductNonunitGcdStratum h X D J Y (g * q) g) := by
      exact sum_divisorScale_reindex (2 * X)
        (fun m g ↦
          ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
            highProductNonunitGcdStratum h X D J Y m g))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      have hglo := (Finset.mem_Icc.mp hg).1
      apply Finset.sum_congr rfl
      intro q hq
      have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
      rw [highProductNonunitGcdStratum_eq_primitive
        h X D J Y g q hglo hqpos]

/-- Exact full weighted lift of the unit/nonunit residue partition. -/
theorem ehmDyadicVaalerPairedHighProductModes_eq_unit_add_nonunit
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) :
    ehmDyadicVaalerPairedHighProductModes V Q X D J Y =
      highProductUnitModes V Q X D J Y +
        highProductNonunitModes V Q X D J Y := by
  classical
  unfold ehmDyadicVaalerPairedHighProductModes
    ehmDyadicVaalerPairedHighProductRowsMRange
    highProductUnitModes highProductNonunitModes
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply congrArg (fun z : ℂ ↦ V.coefficient Q h * z)
  apply Finset.sum_congr rfl
  intro m hm
  rw [← mul_add]
  congr 1
  exact ehmDyadicVaalerPairedHighProductRow_eq_unit_add_nonunit
    h X D J Y m (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)

/-- Exact Stage-1 main/off-diagonal decomposition in canonical primitive
coordinates. -/
theorem ehmDyadicVaalerPairedHighProductModes_eq_primitiveMain_add_offDiagonal
    (V : VaalerSawtoothPackage) (Q X D J Y : ℕ) :
    ehmDyadicVaalerPairedHighProductModes V Q X D J Y =
      highProductPrimitiveMainModes V Q X D J Y +
        highProductPrimitiveOffDiagonalModes V Q X D J Y := by
  rw [ehmDyadicVaalerPairedHighProductModes_eq_unit_add_nonunit,
    highProductUnitModes_eq_primitiveMainModes,
    highProductNonunitModes_eq_gcdStrataModes,
    highProductNonunitGcdStrataModes_eq_primitiveOffDiagonalModes]

/-! ## Retain the high correction until after the residue split -/

/-- The genuine Gate-4/5 high-sector expression.  The high smooth and
endpoint correction remains coupled to both residue sectors. -/
noncomputable def highProductResidueCoupledCore
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) : ℂ :=
  (ehmMSTTHighSectorRetainedCorrection X
      (ehmExplicitFarCutoff X) J U Y : ℂ) -
    highProductUnitModes V Q X (ehmExplicitFarCutoff X) J Y -
    highProductNonunitModes V Q X (ehmExplicitFarCutoff X) J Y

/-- The residue-coupled core is exactly the existing high-sector residual.
This is the correct replacement for a separate high-tail bound. -/
theorem highProductResidueCoupledCore_eq_highSectorCoupledResidual
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) :
    highProductResidueCoupledCore V Q X J U Y =
      ehmMSTTHighSectorCoupledResidual V Q X J U Y := by
  unfold highProductResidueCoupledCore
    ehmMSTTHighSectorCoupledResidual
  rw [ehmDyadicVaalerPairedHighProductModes_eq_unit_add_nonunit]
  ring

/-- The same high-sector core with the nonunit contribution displayed as a
sum of primitive-modulus gcd strata. -/
noncomputable def highProductPrimitiveStrataCoupledCore
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) : ℂ :=
  (ehmMSTTHighSectorRetainedCorrection X
      (ehmExplicitFarCutoff X) J U Y : ℂ) -
    highProductUnitModes V Q X (ehmExplicitFarCutoff X) J Y -
    highProductNonunitGcdStrataModes V Q X
      (ehmExplicitFarCutoff X) J Y

/-- Exact replacement of the nonunit sector by its primitive gcd strata in
the fully correction-coupled target. -/
theorem highProductPrimitiveStrataCoupledCore_eq_highSectorCoupledResidual
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) :
    highProductPrimitiveStrataCoupledCore V Q X J U Y =
      ehmMSTTHighSectorCoupledResidual V Q X J U Y := by
  rw [← highProductResidueCoupledCore_eq_highSectorCoupledResidual]
  unfold highProductPrimitiveStrataCoupledCore
    highProductResidueCoupledCore
  rw [highProductNonunitModes_eq_gcdStrataModes]

/-- The correction-coupled high sector in canonical primitive coordinates.
The `g = 1` contribution is isolated from the `g ≥ 2` off-diagonal sum, and
the latter is indexed by `m = g*q`, `r = g*a`, with `(a,q) = 1`. -/
noncomputable def highProductCanonicalPrimitiveCoupledCore
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) : ℂ :=
  (ehmMSTTHighSectorRetainedCorrection X
      (ehmExplicitFarCutoff X) J U Y : ℂ) -
    highProductPrimitiveMainModes V Q X
      (ehmExplicitFarCutoff X) J Y -
    highProductPrimitiveOffDiagonalModes V Q X
      (ehmExplicitFarCutoff X) J Y

/-- Stage 1 closes with an exact identity: the canonical primitive-coordinate
core is the original correction-coupled high-sector residual. -/
theorem highProductCanonicalPrimitiveCoupledCore_eq_highSectorCoupledResidual
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) :
    highProductCanonicalPrimitiveCoupledCore V Q X J U Y =
      ehmMSTTHighSectorCoupledResidual V Q X J U Y := by
  unfold highProductCanonicalPrimitiveCoupledCore
    ehmMSTTHighSectorCoupledResidual
  rw [ehmDyadicVaalerPairedHighProductModes_eq_primitiveMain_add_offDiagonal]
  ring

/-! ## The open analytic statement -/

/-- A standalone, honest formulation of the remaining high-sector estimate.

The cutoff is constrained by `Y ≤ X`, so it cannot trivialize the high range
by taking `Y = J`.  The estimate is normalized by the dyadic block cardinality
and must hold for a cofinal set of secondary cutoffs `J` for every large outer
scale `X`.

This structure is an explicit hypothesis interface.  Constructing an instance
is the unresolved H15/RH-strength problem; no instance is declared here. -/
structure EhmGate4Gate5CoupledCofinalEstimate where
  V : VaalerSawtoothPackage
  degree : ℕ → ℕ → ℕ
  U : ℕ → ℕ
  productCutoff : ℕ → ℕ → ℕ
  productCutoff_le : ∀ X J, productCutoff X J ≤ X
  etaHigh : ℕ → ℝ
  etaHigh_nonneg : ∀ X, 0 ≤ etaHigh X
  etaHigh_tendsto_zero : Tendsto etaHigh atTop (nhds 0)
  cofinal_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |(highProductCanonicalPrimitiveCoupledCore V (degree X J) X J
        (U X) (productCutoff X J)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * etaHigh X

/-- The new residue formulation supplies exactly the high field required by
the sector-coupled H15 gate. -/
theorem EhmGate4Gate5CoupledCofinalEstimate.highSector_bound
    (H : EhmGate4Gate5CoupledCofinalEstimate)
    (X : ℕ) (hX : 2 ≤ X) :
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      |(ehmMSTTHighSectorCoupledResidual H.V (H.degree X J) X J
        (H.U X) (H.productCutoff X J)).re| ≤
          ((ehmDyadicNBlock X).card : ℝ) * H.etaHigh X := by
  refine (H.cofinal_bound X hX).mono ?_
  intro J hJ
  rw [← highProductCanonicalPrimitiveCoupledCore_eq_highSectorCoupledResidual]
  exact hJ

end RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Strategy
