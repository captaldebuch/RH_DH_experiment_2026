import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannCorrectionBridge

/-!
# Route B8.8: finite weighted lift of Kloosterman completion

The pointwise inverse-coordinate completion is lifted here through an
arbitrary finite family of rows.  Every row may have a different modulus,
frequency, unit weight, and outer complex coefficient.  This is the finite
dependent-type pattern required by the H15 `g,a,b` aggregate.

The theorem remains purely algebraic.  It does not instantiate the row
weights with inverse-Mellin kernels, apply a trace formula, or identify the
aggregate zero mode with the H15 endpoint correction.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEstermannCompletionLift

open AddChar Complex ZMod
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloosterman
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloostermanCompletion

/-- A finite-completion family whose arithmetic data may vary with the row
index.  Positivity of every modulus supplies the local `NeZero` instance
needed by the `ZMod` Fourier theory. -/
structure FiniteKloostermanCompletionFamily (ι : Type*) where
  modulus : ι → ℕ
  modulus_pos : ∀ i, 0 < modulus i
  frequency : ∀ i, ZMod (modulus i)
  unitWeight : ∀ i, (ZMod (modulus i))ˣ → ℂ
  outerCoefficient : ι → ℂ

noncomputable def FiniteKloostermanCompletionFamily.additiveRow
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι) (i : ι) : ℂ := by
  letI : NeZero (F.modulus i) := ⟨Nat.ne_of_gt (F.modulus_pos i)⟩
  exact F.outerCoefficient i *
    ∑ x : (ZMod (F.modulus i))ˣ,
      F.unitWeight i x *
        ZMod.stdAddChar (F.frequency i * (x : ZMod (F.modulus i)))

noncomputable def FiniteKloostermanCompletionFamily.completedRow
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι) (i : ι) : ℂ := by
  letI : NeZero (F.modulus i) := ⟨Nat.ne_of_gt (F.modulus_pos i)⟩
  exact F.outerCoefficient i * (F.modulus i : ℂ)⁻¹ *
    ∑ m : ZMod (F.modulus i),
      inverseCoordinateFourierCoefficient (F.unitWeight i) m *
        kloostermanSum (F.frequency i) m

noncomputable def FiniteKloostermanCompletionFamily.zeroModeRow
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι) (i : ι) : ℂ := by
  letI : NeZero (F.modulus i) := ⟨Nat.ne_of_gt (F.modulus_pos i)⟩
  exact F.outerCoefficient i * (F.modulus i : ℂ)⁻¹ *
    (inverseCoordinateFourierCoefficient (F.unitWeight i) 0 *
      ramanujanSum (F.frequency i))

noncomputable def FiniteKloostermanCompletionFamily.nonzeroModeRow
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι) (i : ι) : ℂ := by
  letI : NeZero (F.modulus i) := ⟨Nat.ne_of_gt (F.modulus_pos i)⟩
  exact F.outerCoefficient i * (F.modulus i : ℂ)⁻¹ *
    ∑ m ∈ (Finset.univ.erase (0 : ZMod (F.modulus i))),
      inverseCoordinateFourierCoefficient (F.unitWeight i) m *
        kloostermanSum (F.frequency i) m

/-- Pointwise completion with the arbitrary outer row coefficient retained. -/
theorem FiniteKloostermanCompletionFamily.additiveRow_eq_completedRow
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι) (i : ι) :
    F.additiveRow i = F.completedRow i := by
  letI : NeZero (F.modulus i) := ⟨Nat.ne_of_gt (F.modulus_pos i)⟩
  unfold additiveRow completedRow
  rw [unitAdditiveSum_eq_kloostermanCompletion]
  ring

/-- The completed row splits exactly into its Ramanujan zero mode and all
nonzero Kloosterman frequencies. -/
theorem FiniteKloostermanCompletionFamily.completedRow_eq_zero_add_nonzero
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι) (i : ι) :
    F.completedRow i = F.zeroModeRow i + F.nonzeroModeRow i := by
  letI : NeZero (F.modulus i) := ⟨Nat.ne_of_gt (F.modulus_pos i)⟩
  unfold completedRow zeroModeRow nonzeroModeRow
  rw [kloostermanCompletion_eq_zeroMode_add_nonzero]
  ring

noncomputable def FiniteKloostermanCompletionFamily.additiveAggregate
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι)
    (rows : Finset ι) : ℂ :=
  ∑ i ∈ rows, F.additiveRow i

noncomputable def FiniteKloostermanCompletionFamily.completedAggregate
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι)
    (rows : Finset ι) : ℂ :=
  ∑ i ∈ rows, F.completedRow i

noncomputable def FiniteKloostermanCompletionFamily.zeroModeAggregate
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι)
    (rows : Finset ι) : ℂ :=
  ∑ i ∈ rows, F.zeroModeRow i

noncomputable def FiniteKloostermanCompletionFamily.nonzeroModeAggregate
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι)
    (rows : Finset ι) : ℂ :=
  ∑ i ∈ rows, F.nonzeroModeRow i

/-- Finite summation over varying moduli introduces no completion remainder. -/
theorem FiniteKloostermanCompletionFamily.additiveAggregate_eq_completed
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι)
    (rows : Finset ι) :
    F.additiveAggregate rows = F.completedAggregate rows := by
  unfold additiveAggregate completedAggregate
  apply Finset.sum_congr rfl
  intro i _
  exact F.additiveRow_eq_completedRow i

/-- The full finite weighted aggregate is exactly the sum of its aggregate
zero mode and aggregate nonzero Kloosterman sector. -/
theorem FiniteKloostermanCompletionFamily.completedAggregate_eq_zero_add_nonzero
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι)
    (rows : Finset ι) :
    F.completedAggregate rows =
      F.zeroModeAggregate rows + F.nonzeroModeAggregate rows := by
  unfold completedAggregate zeroModeAggregate nonzeroModeAggregate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact F.completedRow_eq_zero_add_nonzero i

/-- Combined finite lift from additive rows to the zero/nonzero completed
decomposition. -/
theorem FiniteKloostermanCompletionFamily.additiveAggregate_eq_zero_add_nonzero
    {ι : Type*} (F : FiniteKloostermanCompletionFamily ι)
    (rows : Finset ι) :
    F.additiveAggregate rows =
      F.zeroModeAggregate rows + F.nonzeroModeAggregate rows := by
  rw [F.additiveAggregate_eq_completed rows,
    F.completedAggregate_eq_zero_add_nonzero rows]

end RH.Criteria.NymanBeurling.BCFLogTaperEstermannCompletionLift
