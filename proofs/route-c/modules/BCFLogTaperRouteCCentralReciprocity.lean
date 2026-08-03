import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodRealization

/-!
# Route C: source-normalized central reciprocity

The literal correction in Bettin--Conrey reciprocity is

`a * k^a * ζ(1-a) / (π h)`.

The leading factor `a` cancels the zeta pole, so its central value is
`-1 / (π h)`.  The finite part `(γ - log k) / (π h)` belongs to the
unscaled meromorphic quotient and is not the correction in the source
reciprocity formula.

The resulting exact decomposition has three terms:

* the central period-function side;
* a genuine dual cotangent term `c₀(k/h)`;
* the central value `-1/(πh)` of the scaled correction.

The two H15 orientations are not a direct reciprocity pair: their dual
numerators are `b / (a⁻¹ mod b)` and `a / (b⁻¹ mod a)`.  They are therefore
retained explicitly.  No decay estimate and no period-function package is
asserted here.

Reference: J. S. Auli, A. Bayad, M. Beck, *Reciprocity Theorems for
Bettin--Conrey Sums*, Theorem 1.1, arXiv:1601.06839.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodRealization

/-- The real central Bettin--Conrey value `c₀(h/k)`. -/
noncomputable def bettinConreyCentralValueRe (h k : ℕ) : ℝ :=
  (bettinConreyCentralFiniteSum h k).re

/-- The central value of the scaled Bettin--Conrey correction.  The legacy
name is retained for downstream API stability. -/
noncomputable def bettinConreyCentralFinitePartCorrection
    (h k : ℕ) : ℝ :=
  -1 / (Real.pi * (h : ℝ))

/-- The exact real left-hand side of the central reciprocity relation.  A
future analytic period-function theorem must identify this expression with
the value of `-i ζ(-a) ψₐ(h/k)` at `a = 0`. -/
noncomputable def bettinConreyCentralFinitePartSide
    (h k : ℕ) : ℝ :=
  bettinConreyCentralValueRe h k +
    (k : ℝ) / (h : ℝ) * bettinConreyCentralValueRe k h +
    bettinConreyCentralFinitePartCorrection h k

/-- Proposition-valued interface for the missing analytic identification of
the central period-function value.  No inhabitant is declared. -/
structure BettinConreyCentralFinitePartPackage where
  periodFinitePart : ℕ → ℕ → ℝ
  reciprocity : ∀ h k : ℕ, 0 < h → 0 < k → Nat.Coprime h k →
    bettinConreyCentralFinitePartSide h k = periodFinitePart h k

/-- The real coefficient of one primitive symmetric cotangent pair. -/
noncomputable def routeCCentralPairScale
    (N g a b : ℕ) : ℝ :=
  coprimeSliceCoefficient N g a b *
    (-Real.pi / (2 * (a : ℝ) * (b : ℝ)))

/-- Lift a function of the two inverse numerators through the genuine
primitive interior (`a,b ≥ 2`). -/
noncomputable def routeCInteriorPairLift
    (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ)
    (N g a b : ℕ) : ℝ :=
  if hcop : Nat.Coprime a b then
    if _ha : 2 ≤ a then
      if _hb : 2 ≤ b then
        F N g a b
          (inverseResidueNumerator a b hcop)
          (inverseResidueNumerator b a hcop.symm)
      else 0
    else 0
  else 0

/-- The literal central cotangent contribution of one primitive interior
pair. -/
noncomputable def routeCInteriorCentralCotangentPair
    (N g a b : ℕ) : ℝ :=
  routeCInteriorPairLift
    (fun N g a b h₁ h₂ =>
      -routeCCentralPairScale N g a b *
        (bettinConreyCentralValueRe h₁ b +
          bettinConreyCentralValueRe h₂ a))
    N g a b

/-- The central period-function contribution of one pair, represented by the
exact left-hand side until the analytic package is supplied. -/
noncomputable def routeCInteriorCentralPeriodPair
    (N g a b : ℕ) : ℝ :=
  routeCInteriorPairLift
    (fun N g a b h₁ h₂ =>
      -routeCCentralPairScale N g a b *
        (bettinConreyCentralFinitePartSide h₁ b +
          bettinConreyCentralFinitePartSide h₂ a))
    N g a b

/-- The genuine dual cotangent contribution.  Its arguments are `b/h₁` and
`a/h₂`, not the second H15 orientation. -/
noncomputable def routeCInteriorCentralDualPair
    (N g a b : ℕ) : ℝ :=
  routeCInteriorPairLift
    (fun N g a b h₁ h₂ =>
      routeCCentralPairScale N g a b *
        ((b : ℝ) / (h₁ : ℝ) * bettinConreyCentralValueRe b h₁ +
          (a : ℝ) / (h₂ : ℝ) * bettinConreyCentralValueRe a h₂))
    N g a b

/-- The central values of the two scaled source corrections in one pair. -/
noncomputable def routeCInteriorCentralFinitePartPair
    (N g a b : ℕ) : ℝ :=
  routeCInteriorPairLift
    (fun N g a b h₁ h₂ =>
      routeCCentralPairScale N g a b *
        (bettinConreyCentralFinitePartCorrection h₁ b +
          bettinConreyCentralFinitePartCorrection h₂ a))
    N g a b

/-- Exact pointwise central reciprocity decomposition. -/
theorem routeCInteriorCentralCotangentPair_eq_period_add_dual_add_finitePart
    (N g a b : ℕ) :
    routeCInteriorCentralCotangentPair N g a b =
      routeCInteriorCentralPeriodPair N g a b +
        routeCInteriorCentralDualPair N g a b +
          routeCInteriorCentralFinitePartPair N g a b := by
  classical
  unfold routeCInteriorCentralCotangentPair
    routeCInteriorCentralPeriodPair routeCInteriorCentralDualPair
    routeCInteriorCentralFinitePartPair routeCInteriorPairLift
  split_ifs
  · unfold bettinConreyCentralFinitePartSide
    ring
  all_goals ring

/-- The pole-residue pair already present in the former Route-C split. -/
noncomputable def routeCInteriorCentralPoleResiduePair
    (N g a b : ℕ) : ℝ :=
  if hcop : Nat.Coprime a b then
    if _ha : 2 ≤ a then
      if _hb : 2 ≤ b then
        coprimeSliceCoefficient N g a b *
          (1 / (2 * (a : ℝ) * (b : ℝ)) *
            (1 / (inverseResidueNumerator a b hcop : ℝ) +
              1 / (inverseResidueNumerator b a hcop.symm : ℝ)))
      else 0
    else 0
  else 0

/-- The pole-residue pair is the pair scale multiplied by the two local
residue coefficients `-1/(πh)`. -/
theorem routeCInteriorCentralPoleResiduePair_eq_scaled_residues
    (N g a b : ℕ) :
    routeCInteriorCentralPoleResiduePair N g a b =
      routeCInteriorPairLift
        (fun N g a b h₁ h₂ =>
          routeCCentralPairScale N g a b *
            (-1 / (Real.pi * (h₁ : ℝ)) +
              -1 / (Real.pi * (h₂ : ℝ))))
        N g a b := by
  classical
  unfold routeCInteriorCentralPoleResiduePair routeCInteriorPairLift
  by_cases hcop : Nat.Coprime a b
  · rw [dif_pos hcop, dif_pos hcop]
    by_cases ha : 2 ≤ a
    · rw [dif_pos ha, dif_pos ha]
      by_cases hb : 2 ≤ b
      · rw [dif_pos hb, dif_pos hb]
        have ha0 : (a : ℝ) ≠ 0 := by positivity
        have hb0 : (b : ℝ) ≠ 0 := by positivity
        have hh₁ : 0 < inverseResidueNumerator a b hcop :=
          inverseResidueNumerator_pos a b hcop hb
        have hh₂ : 0 < inverseResidueNumerator b a hcop.symm :=
          inverseResidueNumerator_pos b a hcop.symm ha
        unfold routeCCentralPairScale
        field_simp [Real.pi_ne_zero, ha0, hb0, ne_of_gt hh₁, ne_of_gt hh₂]
        ring
      · rw [dif_neg hb, dif_neg hb]
    · rw [dif_neg ha, dif_neg ha]
  · rw [dif_neg hcop, dif_neg hcop]

/-- Sum a primitive pair contribution over all H15 gcd slices. -/
noncomputable def routeCInteriorPairAggregate
    (F : ℕ → ℕ → ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N,
    ∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g), F N g a b

noncomputable def routeCInteriorCentralCotangentAggregate (N : ℕ) : ℝ :=
  routeCInteriorPairAggregate routeCInteriorCentralCotangentPair N

noncomputable def routeCInteriorCentralPeriodAggregate (N : ℕ) : ℝ :=
  routeCInteriorPairAggregate routeCInteriorCentralPeriodPair N

noncomputable def routeCInteriorCentralDualAggregate (N : ℕ) : ℝ :=
  routeCInteriorPairAggregate routeCInteriorCentralDualPair N

noncomputable def routeCInteriorCentralFinitePartAggregate (N : ℕ) : ℝ :=
  routeCInteriorPairAggregate routeCInteriorCentralFinitePartPair N

noncomputable def routeCInteriorCentralPoleResidueAggregate (N : ℕ) : ℝ :=
  routeCInteriorPairAggregate routeCInteriorCentralPoleResiduePair N

/-- The separately extracted `bettinConreyCentralCorrection` is exactly the
aggregate central value of the scaled source correction. -/
theorem routeCInteriorCentralPoleResidueAggregate_eq_existing
    (N : ℕ) :
    routeCInteriorCentralPoleResidueAggregate N =
      bettinConreyCentralCorrection N := by
  rfl

/-- Exact primitive-interior aggregate decomposition. -/
theorem routeCInteriorCentralCotangentAggregate_eq_period_add_dual_add_finitePart
    (N : ℕ) :
    routeCInteriorCentralCotangentAggregate N =
      routeCInteriorCentralPeriodAggregate N +
        routeCInteriorCentralDualAggregate N +
          routeCInteriorCentralFinitePartAggregate N := by
  unfold routeCInteriorCentralCotangentAggregate
    routeCInteriorCentralPeriodAggregate routeCInteriorCentralDualAggregate
    routeCInteriorCentralFinitePartAggregate routeCInteriorPairAggregate
  simp_rw [routeCInteriorCentralCotangentPair_eq_period_add_dual_add_finitePart]
  simp only [Finset.sum_add_distrib]

/-- After subtracting the source correction's central value, the remaining
interior is exactly period plus genuine dual. -/
theorem routeCInteriorCentralCotangent_sub_finitePart
    (N : ℕ) :
    routeCInteriorCentralCotangentAggregate N -
        routeCInteriorCentralFinitePartAggregate N =
      routeCInteriorCentralPeriodAggregate N +
        routeCInteriorCentralDualAggregate N := by
  rw [routeCInteriorCentralCotangentAggregate_eq_period_add_dual_add_finitePart]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
