import Mathlib
import RiemannHypothesis.Basic.CriticalStrip

/-!
# Báez-Duarte L²(0,∞) Model

The strengthening of the Nyman-Beurling criterion by L. Báez-Duarte.
This reformulates RH as the function χ_{(0,1)} lying in the closure
of the span of fractional-part functions ρ_k(x) = {1/(k x)} in L²(0,∞).
-/

namespace RH.Criteria.NymanBeurling.BaezDuarte

open scoped BigOperators

noncomputable def rhoBD (k : ℕ) (x : ℝ) : ℝ :=
  Int.fract (1 / ((k + 1 : ℝ) * x))

noncomputable def chi01 (x : ℝ) : ℝ :=
  if 0 < x ∧ x ≤ 1 then 1 else 0

noncomputable def bdApprox
    (N : ℕ) (coeffs : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ k, coeffs k * rhoBD k.val x

/-- The L²(0,∞) error from χ_{(0,1]} to a finite Nyman combination. -/
noncomputable def BaezDuarteL2Error
    (N : ℕ) (coeffs : Fin N → ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), (chi01 x - bdApprox N coeffs x) ^ 2

/-- L² error is non-negative: integral of a square. -/
theorem baezDuarteL2Error_nonneg
    (N : ℕ) (coeffs : Fin N → ℝ) :
    0 ≤ BaezDuarteL2Error N coeffs := by
  unfold BaezDuarteL2Error
  apply MeasureTheory.integral_nonneg
  intro x
  positivity

noncomputable def BaezDuarteDistance (N : ℕ) : ℝ :=
  ⨅ coeffs : Fin N → ℝ,
    BaezDuarteL2Error N coeffs

/-- Distance is non-negative: infimum of non-negatives. -/
theorem baezDuarteDistance_nonneg (N : ℕ) : 0 ≤ BaezDuarteDistance N := by
  simp only [BaezDuarteDistance]
  apply le_ciInf
  intro c
  exact baezDuarteL2Error_nonneg N c

def BaezDuarteCriterion : Prop :=
  Filter.Tendsto BaezDuarteDistance Filter.atTop (nhds 0)

-- ---------------------------------------------------------------------------
-- Phase 9A — Monotonicity of BaezDuarteDistance
-- (must precede Phase 10A which uses baezDuarteDistance_antitone)
-- ---------------------------------------------------------------------------

/-- Embedding a Fin N coefficient vector into Fin (N+1) by appending zero
    preserves the L² approximation error: the new ρ_{N+1} basis function
    gets coefficient 0, contributing nothing. -/
theorem bdApprox_embed_zero (N : ℕ) (coeffs : Fin N → ℝ) (x : ℝ) :
    bdApprox (N + 1) (Fin.snoc coeffs 0) x = bdApprox N coeffs x := by
  simp only [bdApprox, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- The L² error is unchanged when we embed N coefficients into N+1 with last = 0. -/
theorem baezDuarteL2Error_embed_zero (N : ℕ) (coeffs : Fin N → ℝ) :
    BaezDuarteL2Error (N + 1) (Fin.snoc coeffs 0) = BaezDuarteL2Error N coeffs := by
  simp only [BaezDuarteL2Error]
  congr 1
  ext x
  congr 1
  congr 1
  exact bdApprox_embed_zero N coeffs x

/-- BaezDuarteDistance is antitone: a larger approximation space gives a smaller infimum. -/
theorem baezDuarteDistance_antitone : Antitone BaezDuarteDistance := by
  apply antitone_nat_of_succ_le
  intro N
  simp only [BaezDuarteDistance]
  apply le_ciInf
  intro coeffs
  have hbdd : BddBelow (Set.range (BaezDuarteL2Error (N + 1))) :=
    ⟨0, by rintro _ ⟨c, rfl⟩; exact baezDuarteL2Error_nonneg _ _⟩
  calc ⨅ c : Fin (N + 1) → ℝ, BaezDuarteL2Error (N + 1) c
      ≤ BaezDuarteL2Error (N + 1) (Fin.snoc coeffs 0) := ciInf_le hbdd _
    _ = BaezDuarteL2Error N coeffs := baezDuarteL2Error_embed_zero N coeffs

-- ---------------------------------------------------------------------------
-- Phase 9G — Conditional fallback: squeeze theorem
-- ---------------------------------------------------------------------------

/-- Squeeze theorem for BaezDuarteDistance: if we have an explicit upper bound
    sequence tending to 0, the distance itself tends to 0. -/
theorem baezDuarteDistance_tendsto_zero_of_energy_bound
    (f : ℕ → ℝ)
    (hf_bound : ∀ N, BaezDuarteDistance N ≤ f N)
    (hf_tendsto : Filter.Tendsto f Filter.atTop (nhds 0)) :
    BaezDuarteCriterion := by
  simp only [BaezDuarteCriterion]
  apply squeeze_zero (fun N => baezDuarteDistance_nonneg N) hf_bound hf_tendsto

-- ---------------------------------------------------------------------------
-- Phase 10A — Axiom ledger: named criterion equivalences
-- ---------------------------------------------------------------------------

/-!
### Criterion hierarchy and proof debt (Phase 10A)

The RH proof debt on the Nyman-Beurling route is concentrated in ONE axiom:

  `nyman_beurling_criterion_iff_RH`

Everything else in this file is proved.  The chain is:

  `nyman_beurling_criterion_iff_RH`   [AXIOM — the Nyman-Beurling theorem]
      ↓
  `nymanBeurlingCriterion_iff_baezDuarteCriterion`  [PROVED — Phase 10A]
      ↓
  `baez_duarte_criterion_implies_RH`  [THEOREM — derived, not axiom]

Honest status: this is a conditional formalization.
`NymanBeurlingCriterion` is RH-equivalent; assuming it is assuming RH.
-/

/-- Classical Nyman-Beurling L² completeness criterion.
    χ_{(0,1]} lies in the L²(0,∞) closure of span{ρ_k : k ≥ 1}.
    Equivalently: for any ε > 0, there exist N and c : Fin N → ℝ with L² error < ε.

    **RH-equivalent** (Nyman 1950, Beurling 1955, Báez-Duarte 2003):
    - Forward (criterion → RH): use the approximation to show all non-trivial zeros
      of ζ lie on the critical line.
    - Backward (RH → criterion): deeper half proved by Báez-Duarte (2003).
    Do NOT assume this criterion without acknowledging it presupposes RH. -/
def NymanBeurlingCriterion : Prop :=
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ c : Fin N → ℝ, BaezDuarteL2Error N c < ε

/-- Phase 10A: NymanBeurlingCriterion ↔ BaezDuarteCriterion (proved, no axiom).
    - → direction: given N₀ and c with error < ε, ciInf_le gives Distance N₀ < ε;
      antitone upgrades to ∀ N ≥ N₀, Distance N < ε (tendsto_zero).
    - ← direction: given Tendsto, obtain N₀ with Distance N₀ = ⨅c, error < ε;
      by_contra + push_neg + le_ciInf derives a contradiction. -/
theorem nymanBeurlingCriterion_iff_baezDuarteCriterion :
    NymanBeurlingCriterion ↔ BaezDuarteCriterion := by
  constructor
  · -- NymanBeurlingCriterion → BaezDuarteCriterion
    intro h
    rw [BaezDuarteCriterion, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, c, hc⟩ := h ε hε
    refine ⟨N₀, fun N hN => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (baezDuarteDistance_nonneg N)]
    calc BaezDuarteDistance N
        ≤ BaezDuarteDistance N₀ := baezDuarteDistance_antitone hN
      _ ≤ BaezDuarteL2Error N₀ c :=
          ciInf_le ⟨0, by rintro _ ⟨c', rfl⟩; exact baezDuarteL2Error_nonneg _ _⟩ c
      _ < ε := hc
  · -- BaezDuarteCriterion → NymanBeurlingCriterion
    intro hcrit ε hε
    rw [BaezDuarteCriterion, Metric.tendsto_atTop] at hcrit
    obtain ⟨N₀, hN₀⟩ := hcrit ε hε
    have hd : BaezDuarteDistance N₀ < ε := by
      have := hN₀ N₀ le_rfl
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (baezDuarteDistance_nonneg N₀)] at this
    simp only [BaezDuarteDistance] at hd
    refine ⟨N₀, ?_⟩
    by_contra hall
    push Not at hall
    linarith [le_ciInf hall]

/-- The exact remaining analytical debt in the forward Nyman--Beurling route
to RH. Keeping it as data makes every RH-producing theorem explicitly
conditional, without adding an axiom to the environment. -/
structure NymanBeurlingRHBridgeDebts where
  /-- Nyman--Beurling completeness rules out zeta zeros off the critical line. -/
  RH_of_nymanBeurlingCriterion :
    NymanBeurlingCriterion → RH.Basic.RiemannHypothesis

/-- The conditional Báez--Duarte-to-RH bridge. The finite-dimensional
criterion conversion is proved above; only the named Nyman--Beurling
analytical debt is supplied by the caller. -/
theorem baez_duarte_criterion_implies_RH
    (debt : NymanBeurlingRHBridgeDebts) (c : BaezDuarteCriterion) :
    RH.Basic.RiemannHypothesis :=
  debt.RH_of_nymanBeurlingCriterion
    (nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr c)

/- The Nyman-Beurling theorem: the completeness criterion is equivalent to RH.
    Source: Nyman (1950) proved → direction; Beurling (1955) strengthened;
    Báez-Duarte (2003) established that integer dilations {ρ_k} suffice.
    
    The axiom `nyman_beurling_criterion_iff_RH` has been removed in Phase NB-A.
    Use `NymanBeurlingRHBridgeDebts` to conditionally bridge to RH instead. -/

-- ---------------------------------------------------------------------------
-- Phase 9F — Named bridge for documentation
-- ---------------------------------------------------------------------------

/-- Assuming NymanBeurlingCriterion (RH-equivalent) gives BaezDuarteCriterion.
    This is the → direction of `nymanBeurlingCriterion_iff_baezDuarteCriterion`.
    Kept as a named theorem; its hypothesis is RH-equivalent. -/
theorem baezDuarteCriterion_of_nyman_beurling_criterion
    (h : NymanBeurlingCriterion) : BaezDuarteCriterion :=
  nymanBeurlingCriterion_iff_baezDuarteCriterion.mp h

-- ---------------------------------------------------------------------------
-- Phase 10C — Certified energy sequences → BaezDuarteCriterion
-- ---------------------------------------------------------------------------

/-- Phase 10C: If we have a sequence E : ℕ → ℝ of certified upper bounds on
    BaezDuarteDistance that tends to 0, then BaezDuarteCriterion holds.
    This is the bridge from the finite computational side (Phase 8E certificates)
    to the asymptotic criterion.

    The finite certificates (N=10/20/50) give specific values of E.
    An infinite sequence with E N → 0 — not constructed here — would close
    the circle without the `nyman_beurling_criterion_iff_RH` axiom.

    The non-negativity of E is not needed explicitly (dropped from 9G signature). -/
theorem baezDuarteCriterion_of_certified_energy_sequence
    (E : ℕ → ℝ)
    (hcert : ∀ N, BaezDuarteDistance N ≤ E N)
    (hE : Filter.Tendsto E Filter.atTop (nhds 0)) :
    BaezDuarteCriterion :=
  baezDuarteDistance_tendsto_zero_of_energy_bound E hcert hE

-- ---------------------------------------------------------------------------
-- Phase 11A — Asymptotic Energy Certificate Target
-- ---------------------------------------------------------------------------

/-- Phase 11A target: A formal structure encoding an infinite sequence
    of upper bounds on the Baez-Duarte distance that asymptotically vanishes.
    Proving the existence of such a structure implies the Riemann Hypothesis
    via `baezDuarteCriterion_of_certified_energy_sequence` and the
    Nyman-Beurling criterion. -/
structure AsymptoticEnergyCertificate where
  E : ℕ → ℝ
  bound : ∀ N, BaezDuarteDistance N ≤ E N
  tends_to_zero : Filter.Tendsto E Filter.atTop (nhds 0)

/-- If we can construct an AsymptoticEnergyCertificate, we satisfy the Baez-Duarte Criterion. -/
theorem baezDuarteCriterion_of_asymptoticEnergyCertificate
    (cert : AsymptoticEnergyCertificate) : BaezDuarteCriterion :=
  baezDuarteCriterion_of_certified_energy_sequence cert.E cert.bound cert.tends_to_zero

end RH.Criteria.NymanBeurling.BaezDuarte
