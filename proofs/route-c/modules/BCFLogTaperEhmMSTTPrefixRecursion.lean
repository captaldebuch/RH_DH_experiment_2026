import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTClippedOptimization

/-!
# Recursive dyadic decomposition of the lower MSTT prefix

After the upper block `(X,2X]` has been treated by exact clipped windows,
the Gate-5 low-product modes still contain the prefix `1 <= m <= X`.  This
module gives its exact halving recurrence.  For `S = floor(M/2)`,

`[1,M] = [1,S] union (S,2S] union [2S+1,M]`,

and the final interval has cardinality at most one.  Thus recursive dyadic
blocking loses only one explicit endpoint at each scale.

No estimate for those endpoints or for the sum of scale-dependent MSTT
objectives is asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTPrefixRecursion

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFullVaalerLift
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate5CoupledReconstruction
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTClippedOptimization
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTNormalizationAudit
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTOptimization
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTWindowCover
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmVaalerAnalyticGate
open RH.Criteria.NymanBeurling.QuadraticInteraction

/-! ## Generic finite halving identity -/

/-- The possible odd endpoint left after extracting `(floor(M/2),
2*floor(M/2)]`. -/
def ehmMSTTHalvingEndpointRange (M : ℕ) : Finset ℕ :=
  Finset.Icc (2 * (M / 2) + 1) M

theorem card_ehmMSTTHalvingEndpointRange_le_one (M : ℕ) :
    (ehmMSTTHalvingEndpointRange M).card ≤ 1 := by
  have hmod := Nat.mod_add_div M 2
  have hmodlt : M % 2 < 2 := Nat.mod_lt M (by omega)
  simp only [ehmMSTTHalvingEndpointRange, Nat.card_Icc]
  omega

/-- Exact finite halving of an inclusive prefix, with a one-point parity
remainder instead of an evenness assumption. -/
theorem sum_Icc_one_eq_halved
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, f m) =
      (∑ m ∈ Finset.Icc 1 (M / 2), f m) +
        (∑ m ∈ ehmMSTTDyadicMBlock (M / 2), f m) +
        ∑ m ∈ ehmMSTTHalvingEndpointRange M, f m := by
  have hmod := Nat.mod_add_div M 2
  have hmodlt : M % 2 < 2 := Nat.mod_lt M (by omega)
  have htwo : 2 * (M / 2) ≤ M := by omega
  have hwhole :
      Finset.Icc 1 M =
        Finset.Icc 1 (2 * (M / 2)) ∪
          ehmMSTTHalvingEndpointRange M := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union,
      ehmMSTTHalvingEndpointRange]
    omega
  have hdis :
      Disjoint (Finset.Icc 1 (2 * (M / 2)))
        (ehmMSTTHalvingEndpointRange M) := by
    apply Finset.disjoint_left.mpr
    intro m hmLow hmEnd
    have hmle := (Finset.mem_Icc.mp hmLow).2
    have hmgt := (Finset.mem_Icc.mp hmEnd).1
    omega
  rw [hwhole, Finset.sum_union hdis,
    sum_Icc_one_two_mul_eq_low_add_dyadic]

/-! ## Lift through one row and all Vaaler frequencies -/

/-- Low-product modes supported on the prefix `1 <= m <= M`, while all
arithmetic weights retain their original outer scale `N`. -/
noncomputable def ehmDyadicVaalerPairedLowProductPrefixTo
    (V : VaalerSawtoothPackage)
    (Q N D J Y M : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ehmDyadicVaalerPairedLowProductRowsMRange h N D J Y 1 M

/-- The at-most-one endpoint contribution at a halving step. -/
noncomputable def ehmDyadicVaalerPairedLowProductHalvingEndpoint
    (V : VaalerSawtoothPackage)
    (Q N D J Y M : ℕ) : ℂ :=
  ∑ h ∈ (V.frequencies Q).erase 0,
    V.coefficient Q h *
      ∑ m ∈ ehmMSTTHalvingEndpointRange M,
        ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
          ehmDyadicVaalerPairedLowProductRow h N D J Y m)

theorem ehmDyadicVaalerPairedLowProductRowsMRange_eq_halved
    (h : ℤ) (N D J Y M : ℕ) :
    ehmDyadicVaalerPairedLowProductRowsMRange h N D J Y 1 M =
      ehmDyadicVaalerPairedLowProductRowsMRange
          h N D J Y 1 (M / 2) +
        ehmMSTTLowProductRowsBlock
          h N D J Y (M / 2) (M / 2) +
        ∑ m ∈ ehmMSTTHalvingEndpointRange M,
          ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
            ehmDyadicVaalerPairedLowProductRow h N D J Y m) := by
  simpa [ehmDyadicVaalerPairedLowProductRowsMRange,
    ehmMSTTLowProductRowsBlock, ehmMSTTDyadicMBlock, two_mul] using
      (sum_Icc_one_eq_halved
        (fun m : ℕ =>
          ((((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ) *
            ehmDyadicVaalerPairedLowProductRow h N D J Y m)) M)

/-- Exact recursive step for the complete weighted low-product prefix. -/
theorem ehmDyadicVaalerPairedLowProductPrefixTo_eq_halved
    (V : VaalerSawtoothPackage)
    (Q N D J Y M : ℕ) :
    ehmDyadicVaalerPairedLowProductPrefixTo V Q N D J Y M =
      ehmDyadicVaalerPairedLowProductPrefixTo
          V Q N D J Y (M / 2) +
        ehmMSTTWeightedLowProductModesBlock
          V Q N D J Y (M / 2) (M / 2) +
        ehmDyadicVaalerPairedLowProductHalvingEndpoint
          V Q N D J Y M := by
  classical
  unfold ehmDyadicVaalerPairedLowProductPrefixTo
    ehmMSTTWeightedLowProductModesBlock
    ehmDyadicVaalerPairedLowProductHalvingEndpoint
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [← mul_add, ← mul_add,
    ← ehmDyadicVaalerPairedLowProductRowsMRange_eq_halved]

/-- The prefix used in the first Gate-5 support audit is the specialization
`M=N` of the recursive prefix. -/
theorem ehmDyadicVaalerPairedLowProductPrefix_eq_prefixTo
    (V : VaalerSawtoothPackage) (Q N D J Y : ℕ) :
    ehmDyadicVaalerPairedLowProductPrefix V Q N D J Y =
      ehmDyadicVaalerPairedLowProductPrefixTo V Q N D J Y N := by
  rfl

/-! ## One recursive Gate-5 normal form -/

/-- Gate 5 after one exact halving of its lower low-product prefix. -/
noncomputable def ehmDyadicVaalerGate5FirstRecursiveMSTTCore
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) : ℂ :=
  (ehmDyadicVaalerRetainedCorrection X J U : ℂ) -
    ehmDyadicVaalerPairedLowProductPrefixTo V Q X
      (ehmExplicitFarCutoff X) J Y (X / 2) -
    ehmMSTTWeightedLowProductModesBlock V Q X
      (ehmExplicitFarCutoff X) J Y (X / 2) (X / 2) -
    ehmDyadicVaalerPairedLowProductHalvingEndpoint V Q X
      (ehmExplicitFarCutoff X) J Y X -
    ehmMSTTWeightedLowProductModesBlock V Q X
      (ehmExplicitFarCutoff X) J Y X X -
    ehmDyadicVaalerPairedHighProductModes V Q X
      (ehmExplicitFarCutoff X) J Y -
    ehmDyadicVaalerKernelNormalError V Q X
      (ehmExplicitFarCutoff X) J U

/-- Exact first recursive expansion of the complete Gate-5 core. -/
theorem ehmDyadicVaalerGate5CoupledCore_eq_firstRecursiveMSTTCore
    (V : VaalerSawtoothPackage) (Q X J U Y : ℕ) :
    ehmDyadicVaalerGate5CoupledCore V Q X J U =
      ehmDyadicVaalerGate5FirstRecursiveMSTTCore V Q X J U Y := by
  rw [ehmDyadicVaalerGate5CoupledCore_eq_msttSupportAuditCore]
  unfold ehmDyadicVaalerGate5MSTTSupportAuditCore
    ehmDyadicVaalerGate5FirstRecursiveMSTTCore
  rw [ehmDyadicVaalerPairedLowProductPrefix_eq_prefixTo,
    ehmDyadicVaalerPairedLowProductPrefixTo_eq_halved]
  ring

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTPrefixRecursion
