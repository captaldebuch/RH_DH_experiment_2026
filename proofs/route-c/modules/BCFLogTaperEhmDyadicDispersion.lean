import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal

/-!
# Dyadic mean-value route to double-cofinal Ehm cancellation

The double-cofinal criterion only asks for one good outer cutoff `N` in
every sufficiently late range.  This module turns that existential target
into a mean-value problem suited to dispersion methods.

For each dyadic block `[X,2X]`, suppose that at cofinally many hyperbolic
cutoffs `J` either the first or second moment of the finite Ehm boundaries is
bounded by a null majorant.  Finite averaging first gives a good `N` for each
such `J`.  Since the dyadic block is finite, an infinite pigeonhole argument
then fixes one `N` which is good for cofinally many `J`.  This is exactly the
two-level hypothesis required by `EhmDoubleCofinalBoundaryVanishing`.

The final section states the second-moment target directly in the exact
near/far four-block coordinates.  All signed arithmetic remains inside each
boundary value; the outer square is introduced only after the fully coupled
finite expression has been assembled.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperCofinalEnergy
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDispersionBlocks
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmUniformBoundary

/-! ## Finite and infinite pigeonhole lemmas -/

/-- The inclusive dyadic block of outer cutoffs. -/
def ehmDyadicNBlock (X : ℕ) : Finset ℕ :=
  Finset.Icc X (2 * X)

theorem ehmDyadicNBlock_nonempty (X : ℕ) :
    (ehmDyadicNBlock X).Nonempty := by
  refine ⟨X, ?_⟩
  simp only [ehmDyadicNBlock, Finset.mem_Icc]
  omega

/-- A cardinality-scaled finite mean bound contains one term below the
stated mean.  No sign assumption on `f` is needed. -/
theorem exists_mem_le_of_sum_le_card_mul
    (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℝ) (a : ℝ)
    (havg : ∑ n ∈ s, f n ≤ (s.card : ℝ) * a) :
    ∃ n ∈ s, f n ≤ a := by
  classical
  by_contra h
  push Not at h
  have hstrict : (∑ n ∈ s, a) < ∑ n ∈ s, f n :=
    Finset.sum_lt_sum_of_nonempty hs (fun n hn ↦ h n hn)
  have hconst : (∑ _n ∈ s, a) = (s.card : ℝ) * a := by simp
  rw [hconst] at hstrict
  exact (not_lt_of_ge havg) hstrict

/-- If, cofinally often, some member of a fixed finite set satisfies a
property, then one fixed member satisfies it cofinally often. -/
theorem exists_mem_frequently_of_frequently_exists_mem
    {β : Type*} (l : Filter β) (s : Finset ℕ) (P : ℕ → β → Prop)
    (h : ∃ᶠ y in l, ∃ n ∈ s, P n y) :
    ∃ n ∈ s, ∃ᶠ y in l, P n y := by
  classical
  by_contra hnone
  push Not at hnone
  have eventually_all_finset : ∀ t : Finset ℕ,
      (∀ n ∈ t, ∀ᶠ y in l, ¬P n y) →
        ∀ᶠ y in l, ∀ n ∈ t, ¬P n y := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert n t hn ih =>
        intro hall
        have hn_event : ∀ᶠ y in l, ¬P n y :=
          hall n (Finset.mem_insert_self n t)
        have ht_event : ∀ᶠ y in l, ∀ m ∈ t, ¬P m y :=
          ih (fun m hm ↦ hall m (Finset.mem_insert_of_mem hm))
        filter_upwards [hn_event, ht_event] with y hny hty
        intro m hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hny
        · exact hty m hm
  have hevent : ∀ᶠ y in l, ∀ n ∈ s, ¬P n y :=
    eventually_all_finset s hnone
  apply h
  filter_upwards [hevent] with y hy
  rintro ⟨n, hn, hP⟩
  exact hy n hn hP

/-! ## Fixed-block passage to the exact energy -/

/-- For the proved autocorrelation kernel, the finite Ehm boundary converges
at every fixed positive cutoff to the exact BCF log-taper energy. -/
theorem ehmFiniteCoupledBoundaryExpression_tendsto_energy
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (N : ℕ) (hN : 2 ≤ N) :
    Tendsto
      (fun J : ℕ => ehmFiniteCoupledBoundaryExpression
        BCFLogTaperEhm.ehmR1 N J)
      atTop (nhds (energy N)) := by
  let HK : EhmKernelPackage :=
    ehmS1PointwiseKernelPackageProved.toEhmKernelPackage
  have hlim :=
    ehmFiniteCoupledBoundaryExpression_tendsto_of_rational HS N hN
  have hid : coupledGcdRatioExpression N =
      ehmInversionError ehmS1Autocorrelation BCFLogTaperEhm.ehmR1 N +
        ehmCoupledRemainder N := by
    simpa [HK] using
      (coupledGcdRatioExpression_eq_ehmInversionError_add_remainder HK N hN)
  have heq : energy N =
      ehmInversionError ehmS1Autocorrelation BCFLogTaperEhm.ehmR1 N +
        ehmCoupledRemainder N := by
    calc
      energy N = coupledGcdRatioExpression N := by
        simpa only [coupledGcdRatioExpression] using energy_eq_gcdRatioFormula N
      _ = _ := hid
  simpa only [heq] using hlim

/-- On a fixed dyadic block, the finite second moment in `J` converges to
the exact second moment of the certified energies.  Finiteness of the block
is what makes the limit interchange unconditional. -/
theorem ehmDyadicBoundarySquareSum_tendsto_energySquareSum
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (X : ℕ) (hX : 2 ≤ X) :
    Tendsto
      (fun J : ℕ => ∑ N ∈ ehmDyadicNBlock X,
        (ehmFiniteCoupledBoundaryExpression
          BCFLogTaperEhm.ehmR1 N J) ^ 2)
      atTop
      (nhds (∑ N ∈ ehmDyadicNBlock X, (energy N) ^ 2)) := by
  apply tendsto_finsetSum
  intro N hNmem
  exact (ehmFiniteCoupledBoundaryExpression_tendsto_energy HS N
    (hX.trans (Finset.mem_Icc.mp hNmem).1)).pow 2

/-! ## First-moment averaged boundary target -/

/-- A dyadic first-moment estimate for the complete finite Ehm boundary.
The good truncations `J` need only be cofinal for each block. -/
structure EhmDyadicBoundaryL1Vanishing (R1 : ℝ → ℝ) where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_sum_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ∑ N ∈ ehmDyadicNBlock X,
          |ehmFiniteCoupledBoundaryExpression R1 N J| ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta X

/-- A vanishing dyadic first moment selects one arbitrarily large `N` whose
finite Ehm boundary is small at cofinally many `J`. -/
noncomputable def EhmDyadicBoundaryL1Vanishing.toDoubleCofinal
    {R1 : ℝ → ℝ} (H : EhmDyadicBoundaryL1Vanishing R1) :
    EhmDoubleCofinalBoundaryVanishing R1 where
  cofinally_small ε hε N₀ := by
    have heta_event : ∀ᶠ X : ℕ in atTop, H.eta X < ε :=
      H.eta_tendsto_zero.eventually (Iio_mem_nhds hε)
    have hX_event : ∀ᶠ X : ℕ in atTop, max N₀ 2 ≤ X :=
      eventually_ge_atTop (max N₀ 2)
    rcases (heta_event.and hX_event).exists with ⟨X, heta, hX⟩
    have hX2 : 2 ≤ X := (le_max_right N₀ 2).trans hX
    have hfreq_exists : ∃ᶠ J : ℕ in atTop,
        ∃ N ∈ ehmDyadicNBlock X,
          |ehmFiniteCoupledBoundaryExpression R1 N J| ≤ H.eta X :=
      (H.cofinal_sum_bound X hX2).mono fun J hsum ↦
        exists_mem_le_of_sum_le_card_mul
          (ehmDyadicNBlock X) (ehmDyadicNBlock_nonempty X)
          (fun N ↦ |ehmFiniteCoupledBoundaryExpression R1 N J|)
          (H.eta X) hsum
    rcases exists_mem_frequently_of_frequently_exists_mem
      atTop (ehmDyadicNBlock X)
        (fun N J ↦ |ehmFiniteCoupledBoundaryExpression R1 N J| ≤ H.eta X)
        hfreq_exists with ⟨N, hNmem, hNfreq⟩
    have hXN : X ≤ N := (Finset.mem_Icc.mp hNmem).1
    refine ⟨N, (le_max_left N₀ 2).trans (hX.trans hXN),
      hX2.trans hXN, ?_⟩
    exact hNfreq.mono fun J hJ ↦ hJ.trans_lt heta

/-! ## Second-moment dispersion target -/

/-- The natural dispersion formulation: the dyadic second moment of the
fully coupled finite boundaries has a null root-mean-square majorant. -/
structure EhmDyadicBoundaryL2Vanishing (R1 : ℝ → ℝ) where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_square_sum_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ∑ N ∈ ehmDyadicNBlock X,
          (ehmFiniteCoupledBoundaryExpression R1 N J) ^ 2 ≤
        ((ehmDyadicNBlock X).card : ℝ) * (eta X) ^ 2

/-- Exact dyadic root-mean-square control of the certified BCF energy. -/
structure DyadicLogTaperEnergyL2Vanishing where
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  square_sum_bound : ∀ X : ℕ, 2 ≤ X →
    ∑ N ∈ ehmDyadicNBlock X, (energy N) ^ 2 ≤
      ((ehmDyadicNBlock X).card : ℝ) * (eta X) ^ 2

/-- Cofinal finite-boundary second-moment control passes to the exact energy
second moment by the fixed-block limit theorem. -/
noncomputable def EhmDyadicBoundaryL2Vanishing.toEnergyL2
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicBoundaryL2Vanishing BCFLogTaperEhm.ehmR1) :
    DyadicLogTaperEnergyL2Vanishing where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  square_sum_bound X hX :=
    le_of_tendsto_of_frequently
      (ehmDyadicBoundarySquareSum_tendsto_energySquareSum HS X hX)
      (H.cofinal_square_sum_bound X hX)

/-- A vanishing dyadic energy RMS supplies arbitrarily large cutoffs with
small certified energy. -/
noncomputable def DyadicLogTaperEnergyL2Vanishing.toCofinalEnergy
    (H : DyadicLogTaperEnergyL2Vanishing) :
    CofinalLogTaperEnergyVanishing where
  cofinally_small ε hε N₀ := by
    have heta_event : ∀ᶠ X : ℕ in atTop, H.eta X < ε :=
      H.eta_tendsto_zero.eventually (Iio_mem_nhds hε)
    have hX_event : ∀ᶠ X : ℕ in atTop, max N₀ 2 ≤ X :=
      eventually_ge_atTop (max N₀ 2)
    rcases (heta_event.and hX_event).exists with ⟨X, heta, hX⟩
    have hX2 : 2 ≤ X := (le_max_right N₀ 2).trans hX
    rcases exists_mem_le_of_sum_le_card_mul
      (ehmDyadicNBlock X) (ehmDyadicNBlock_nonempty X)
      (fun N ↦ (energy N) ^ 2) ((H.eta X) ^ 2)
      (H.square_sum_bound X hX2) with ⟨N, hNmem, hNsquare⟩
    have hNeta : energy N ≤ H.eta X := by
      exact (sq_le_sq₀ (energy_nonneg N) (H.eta_nonneg X)).mp hNsquare
    have hXN : X ≤ N := (Finset.mem_Icc.mp hNmem).1
    exact ⟨N, (le_max_left N₀ 2).trans (hX.trans hXN),
      hNeta.trans_lt heta⟩

/-- The exact-energy second-moment formulation closes through the previously
proved cofinal certified-energy criterion. -/
theorem baezDuarteCriterion_of_dyadicLogTaperEnergyL2
    (H : DyadicLogTaperEnergyL2Vanishing) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_cofinalLogTaperEnergy H.toCofinalEnergy

/-- A vanishing root-mean-square boundary estimate implies the same
double-cofinal conclusion, without first applying Cauchy--Schwarz to the
whole block. -/
noncomputable def EhmDyadicBoundaryL2Vanishing.toDoubleCofinal
    {R1 : ℝ → ℝ} (H : EhmDyadicBoundaryL2Vanishing R1) :
    EhmDoubleCofinalBoundaryVanishing R1 where
  cofinally_small ε hε N₀ := by
    have heta_event : ∀ᶠ X : ℕ in atTop, H.eta X < ε :=
      H.eta_tendsto_zero.eventually (Iio_mem_nhds hε)
    have hX_event : ∀ᶠ X : ℕ in atTop, max N₀ 2 ≤ X :=
      eventually_ge_atTop (max N₀ 2)
    rcases (heta_event.and hX_event).exists with ⟨X, heta, hX⟩
    have hX2 : 2 ≤ X := (le_max_right N₀ 2).trans hX
    have hfreq_exists_sq : ∃ᶠ J : ℕ in atTop,
        ∃ N ∈ ehmDyadicNBlock X,
          (ehmFiniteCoupledBoundaryExpression R1 N J) ^ 2 ≤
            (H.eta X) ^ 2 :=
      (H.cofinal_square_sum_bound X hX2).mono fun J hsum ↦
        exists_mem_le_of_sum_le_card_mul
          (ehmDyadicNBlock X) (ehmDyadicNBlock_nonempty X)
          (fun N ↦ (ehmFiniteCoupledBoundaryExpression R1 N J) ^ 2)
          ((H.eta X) ^ 2) hsum
    have hfreq_exists : ∃ᶠ J : ℕ in atTop,
        ∃ N ∈ ehmDyadicNBlock X,
          |ehmFiniteCoupledBoundaryExpression R1 N J| ≤ H.eta X :=
      hfreq_exists_sq.mono fun J hJ ↦ by
        rcases hJ with ⟨N, hN, hsquare⟩
        refine ⟨N, hN, ?_⟩
        apply (sq_le_sq₀ (abs_nonneg _) (H.eta_nonneg X)).mp
        simpa only [sq_abs] using hsquare
    rcases exists_mem_frequently_of_frequently_exists_mem
      atTop (ehmDyadicNBlock X)
        (fun N J ↦ |ehmFiniteCoupledBoundaryExpression R1 N J| ≤ H.eta X)
        hfreq_exists with ⟨N, hNmem, hNfreq⟩
    have hXN : X ≤ N := (Finset.mem_Icc.mp hNmem).1
    refine ⟨N, (le_max_left N₀ 2).trans (hX.trans hXN),
      hX2.trans hXN, ?_⟩
    exact hNfreq.mono fun J hJ ↦ hJ.trans_lt heta

/-! ## Exact near/far block formulation -/

/-- The dyadic second-moment target written in the exact four-block
near/far dispersion coordinates.  The common cutoff condition ensures that
every block identity is valid at the selected `J`. -/
structure EhmDyadicNearFarL2DispersionVanishing (R1 : ℝ → ℝ) where
  D : ℕ → ℕ
  M : ℕ → ℕ
  D_ge : ∀ N, N ≤ D N
  M_le : ∀ N, M N ≤ N
  eta : ℕ → ℝ
  eta_nonneg : ∀ X, 0 ≤ eta X
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  cofinal_square_sum_bound : ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      (∀ N ∈ ehmDyadicNBlock X, D N ≤ J) ∧
      ∑ N ∈ ehmDyadicNBlock X,
          (ehmFiniteNearFarDispersionExpression
            R1 N (D N) J (M N)) ^ 2 ≤
        ((ehmDyadicNBlock X).card : ℝ) * (eta X) ^ 2

/-- The exact four-block identity transports the near/far second moment to
the original finite Ehm boundary second moment. -/
noncomputable def EhmDyadicNearFarL2DispersionVanishing.toBoundaryL2
    {R1 : ℝ → ℝ} (H : EhmDyadicNearFarL2DispersionVanishing R1) :
    EhmDyadicBoundaryL2Vanishing R1 where
  eta := H.eta
  eta_nonneg := H.eta_nonneg
  eta_tendsto_zero := H.eta_tendsto_zero
  cofinal_square_sum_bound X hX :=
    (H.cofinal_square_sum_bound X hX).mono fun J hJ ↦ by
      calc
        (∑ N ∈ ehmDyadicNBlock X,
            (ehmFiniteCoupledBoundaryExpression R1 N J) ^ 2) =
            ∑ N ∈ ehmDyadicNBlock X,
              (ehmFiniteNearFarDispersionExpression
                R1 N (H.D N) J (H.M N)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro N hNmem
          rw [ehmFiniteCoupledBoundaryExpression_eq_nearFarDispersion
            R1 N (H.D N) J (H.M N)
            (hX.trans (Finset.mem_Icc.mp hNmem).1)
            (H.D_ge N) (H.M_le N) (hJ.1 N hNmem)]
        _ ≤ ((ehmDyadicNBlock X).card : ℝ) * (H.eta X) ^ 2 := hJ.2

/-! ## Direct closure theorems -/

theorem baezDuarteCriterion_of_ehmDyadicBoundaryL1
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicBoundaryL1Vanishing BCFLogTaperEhm.ehmR1) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDoubleCofinal HS H.toDoubleCofinal

theorem baezDuarteCriterion_of_ehmDyadicBoundaryL2
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicBoundaryL2Vanishing BCFLogTaperEhm.ehmR1) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDoubleCofinal HS H.toDoubleCofinal

/-- The present main dispersion target: a cofinal dyadic second-moment
estimate for the exact near/far four-block expression suffices for the
Báez--Duarte criterion. -/
theorem baezDuarteCriterion_of_ehmDyadicNearFarL2
    (HS : EhmAutocorrelationR1RationalSeriesBridge)
    (H : EhmDyadicNearFarL2DispersionVanishing BCFLogTaperEhm.ehmR1) :
    BaezDuarteCriterion :=
  baezDuarteCriterion_of_ehmDyadicBoundaryL2 HS H.toBoundaryL2

end RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
