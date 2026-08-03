import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCompletedBlockResidue
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPhysicalCorrection
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmCompensator

/-!
# Genuine H15 contour/trace block modes

The Ehm divisor blocks and the Estermann contour have different natural
coordinates.  This file therefore does not assign contour terms to Ehm blocks
by an arbitrary weight.  Instead it uses the common arithmetic coordinate
which is already present in every exact formula: the gcd slice `g`.

For each dyadic gcd block it records three literal constituents:

* the intrinsic Estermann residue at the contour pole `s = 0`;
* the degenerate completed frequency `m = 0` in the Motohashi seed; and
* the original Gram diagonal `h = k`, whose gcd coordinate is `g = h`.

Their sum is the canonical named mode `Z_k`.  Finite fiberwise reindexing
proves that the sum of the `Z_k` is exactly the corresponding global
residue--zero--diagonal ledger.  The separate normalization defect then tests
whether that ledger reproduces the retained H15 linear correction.  No such
matching is asserted: primal-line, elementary, Eisenstein, and remaining
spectral terms are not silently folded into one of the three named modes.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperH15ContourTraceModes

open Complex
open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperCancellationAnatomy
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCompletedBlockResidue
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15MellinAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannH15NumeratorCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannKloostermanCompletion
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiPhysicalCorrection
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannMotohashiSeed
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## The canonical dyadic gcd partition -/

/-- Dyadic coordinate carried by a positive gcd slice. -/
def h15TraceDyadicGcdIndex (g : ℕ) : ℕ :=
  Nat.log2 g

/-- Dyadic indices met by the genuine finite gcd range `1 ≤ g ≤ N`. -/
def h15TraceDyadicGcdIndices (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).image h15TraceDyadicGcdIndex

/-- The `k`-th fiber of the finite gcd range. -/
def h15TraceDyadicGcdBlock (N k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun g => h15TraceDyadicGcdIndex g = k)

/-- The dyadic gcd fibers reassemble every finite scalar sum exactly. -/
theorem sum_h15TraceDyadicGcdBlocks
    {M : Type*} [AddCommMonoid M]
    (N : ℕ) (f : ℕ → M) :
    (∑ k ∈ h15TraceDyadicGcdIndices N,
      ∑ g ∈ h15TraceDyadicGcdBlock N k, f g) =
        ∑ g ∈ Finset.Icc 1 N, f g := by
  classical
  unfold h15TraceDyadicGcdIndices h15TraceDyadicGcdBlock
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · ext g
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · exact fun h => h.1
    · intro hg
      exact ⟨hg, g, hg, rfl⟩
  · intro g _
    rfl

/-! ## Literal residue, zero, and diagonal slices -/

/-- The intrinsic contour residue in one gcd slice, with the sign appearing
in the extracted Estermann kernel and after projection to the real H15
scalar. -/
noncomputable def h15ContourResidueGcdSlice
    (W : ℂ → ℂ) (N g : ℕ) : ℝ :=
  -(∑ a ∈ Finset.Icc 1 (N / g),
      ∑ b ∈ Finset.Icc 1 (N / g),
        estermannInteriorPairedZeroResidueSummand W N g a b).im

/-- The `m = 0` completed Motohashi orbit in one `(g,q)` row.  Both
functional-equation signs and the proved `π⁻¹` contour normalization are
retained. -/
noncomputable def h15MotohashiZeroOrbitRow
    (N g q : ℕ) [NeZero q] (η c : ℝ) : ℂ :=
  (∑' n : ℕ,
      (h15MotohashiArithmeticSeed N g q .same η c n 0 +
        h15MotohashiArithmeticSeed N g q .opposite η c n 0)) /
    Real.pi

/-- The complete degenerate completed-frequency contribution in one gcd
slice. -/
noncomputable def h15MotohashiZeroGcdSlice
    (N : ℕ) (η c : ℝ) (g : ℕ) : ℝ :=
  (∑ q ∈ Finset.Icc 2 (N / g),
      if hq : 0 < q then
        (@h15MotohashiZeroOrbitRow N g q ⟨Nat.ne_of_gt hq⟩ η c)
      else 0).im

/-- The literal `h = k = g` Gram summand.  On the diagonal the gcd is
exactly `g`, so this uses the same coordinate without a repartition. -/
noncomputable def h15GramDiagonalGcdSlice (N g : ℕ) : ℝ :=
  dirichletCoeff N g * dirichletCoeff N g * baezDuarteGramEntry g g

/-! ## Canonical block modes `Z_k` -/

/-- Intrinsic contour residues localized by their actual gcd coordinate. -/
noncomputable def h15ContourResidueBlockMode
    (W : ℂ → ℂ) (N k : ℕ) : ℝ :=
  ∑ g ∈ h15TraceDyadicGcdBlock N k,
    h15ContourResidueGcdSlice W N g

/-- Completion zero modes localized by their actual gcd coordinate. -/
noncomputable def h15MotohashiZeroBlockMode
    (N : ℕ) (η c : ℝ) (k : ℕ) : ℝ :=
  ∑ g ∈ h15TraceDyadicGcdBlock N k,
    h15MotohashiZeroGcdSlice N η c g

/-- Gram diagonal localized by `g = h = k` in the original quadratic form. -/
noncomputable def h15GramDiagonalBlockMode
    (N k : ℕ) : ℝ :=
  ∑ g ∈ h15TraceDyadicGcdBlock N k,
    h15GramDiagonalGcdSlice N g

/-- The genuine named contour/trace mode
`Z_k = residue_k + zero_k + diagonal_k`. -/
noncomputable def h15ContourTraceBlockMode
    (N : ℕ) (η c : ℝ) (k : ℕ) : ℝ :=
  h15ContourResidueBlockMode (estermannGaussianEvaluationWeight η) N k +
    h15MotohashiZeroBlockMode N η c k +
      h15GramDiagonalBlockMode N k

/-- The three genuine functions can be consumed by the existing completed
block ledger.  This is only a data conversion; it does not identify the gcd
partition with the distinct Ehm divisor partition. -/
noncomputable def h15ContourDerivedModeData
    (N : ℕ) (η c : ℝ) : EhmCompletedBlockContourModes where
  residueMode := h15ContourResidueBlockMode
    (estermannGaussianEvaluationWeight η) N
  zeroMode := h15MotohashiZeroBlockMode N η c
  diagonalMode := h15GramDiagonalBlockMode N

@[simp]
theorem h15ContourDerivedModeData_physicalMode
    (N : ℕ) (η c : ℝ) (k : ℕ) :
    ehmCompletedBlockPhysicalMode (h15ContourDerivedModeData N η c) k =
      h15ContourTraceBlockMode N η c k := by
  rfl

/-! ## Exact global trace normalization -/

/-- Global intrinsic-residue ledger before any comparison with the retained
H15 correction. -/
noncomputable def h15ContourResidueTotal
    (W : ℂ → ℂ) (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N, h15ContourResidueGcdSlice W N g

/-- Global completion-zero ledger. -/
noncomputable def h15MotohashiZeroTotal
    (N : ℕ) (η c : ℝ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N, h15MotohashiZeroGcdSlice N η c g

/-- Global diagonal ledger in the same normalization as the BCF quadratic
form. -/
noncomputable def h15GramDiagonalTotal (N : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 N, h15GramDiagonalGcdSlice N g

/-- Total of the three named physical sectors. -/
noncomputable def h15ContourTraceNamedTotal
    (N : ℕ) (η c : ℝ) : ℝ :=
  h15ContourResidueTotal (estermannGaussianEvaluationWeight η) N +
    h15MotohashiZeroTotal N η c + h15GramDiagonalTotal N

theorem sum_h15ContourResidueBlockMode
    (W : ℂ → ℂ) (N : ℕ) :
    (∑ k ∈ h15TraceDyadicGcdIndices N,
      h15ContourResidueBlockMode W N k) =
        h15ContourResidueTotal W N := by
  exact sum_h15TraceDyadicGcdBlocks N
    (h15ContourResidueGcdSlice W N)

theorem sum_h15MotohashiZeroBlockMode
    (N : ℕ) (η c : ℝ) :
    (∑ k ∈ h15TraceDyadicGcdIndices N,
      h15MotohashiZeroBlockMode N η c k) =
        h15MotohashiZeroTotal N η c := by
  exact sum_h15TraceDyadicGcdBlocks N
    (h15MotohashiZeroGcdSlice N η c)

theorem sum_h15GramDiagonalBlockMode (N : ℕ) :
    (∑ k ∈ h15TraceDyadicGcdIndices N,
      h15GramDiagonalBlockMode N k) =
        h15GramDiagonalTotal N := by
  exact sum_h15TraceDyadicGcdBlocks N (h15GramDiagonalGcdSlice N)

/-- Exact global trace normalization of the three genuine modes.  This is a
reindexing theorem, with no analytic estimate and no correction assumption. -/
theorem sum_h15ContourTraceBlockMode
    (N : ℕ) (η c : ℝ) :
    (∑ k ∈ h15TraceDyadicGcdIndices N,
      h15ContourTraceBlockMode N η c k) =
        h15ContourTraceNamedTotal N η c := by
  unfold h15ContourTraceBlockMode h15ContourTraceNamedTotal
  simp_rw [Finset.sum_add_distrib]
  rw [sum_h15ContourResidueBlockMode,
    sum_h15MotohashiZeroBlockMode, sum_h15GramDiagonalBlockMode]

/-- The diagonal total is definitionally the exact diagonal of the original
BCF Gram quadratic form. -/
theorem h15GramDiagonalTotal_eq_gramDiagonal (N : ℕ) :
    h15GramDiagonalTotal N = gramDiagonal N := by
  rfl

/-- The residue total is exactly the intrinsic-residue part of the physical
contour correction. -/
theorem h15ContourResidueTotal_eq_neg_zeroResidueAggregate_im
    (W : ℂ → ℂ) (N : ℕ) :
    h15ContourResidueTotal W N =
      -(estermannInteriorPairedZeroResidueAggregate W N).im := by
  classical
  unfold h15ContourResidueTotal h15ContourResidueGcdSlice
    estermannInteriorPairedZeroResidueAggregate h15FiniteInteriorAggregate
  rw [Complex.im_sum, Finset.sum_neg_distrib]

/-- The original H15 correction which the signed quadratic sectors must
cancel. -/
noncomputable def h15LinearEndpointCorrection (N : ℕ) : ℝ :=
  2 * gramLinearCorrection N + 1

/-- Exact signed normalization defect.  Its vanishing says that the three
named sectors alone reproduce the negative linear/endpoint correction. -/
noncomputable def h15ContourTraceNormalizationDefect
    (N : ℕ) (η c : ℝ) : ℝ :=
  h15ContourTraceNamedTotal N η c + h15LinearEndpointCorrection N

/-- The global trace normalization question is exactly the vanishing of the
displayed defect.  This theorem deliberately does not claim it vanishes. -/
theorem sum_h15ContourTraceBlockMode_eq_neg_correction_iff
    (N : ℕ) (η c : ℝ) :
    (∑ k ∈ h15TraceDyadicGcdIndices N,
      h15ContourTraceBlockMode N η c k) =
        -h15LinearEndpointCorrection N ↔
      h15ContourTraceNormalizationDefect N η c = 0 := by
  rw [sum_h15ContourTraceBlockMode]
  unfold h15ContourTraceNormalizationDefect
  constructor <;> intro h
  · rw [h]
    ring
  · linarith

/-- Exact missing-sector ledger.  A complete trace formula must supply the
negative of this quantity through the primal-line, elementary, Eisenstein,
and remaining spectral sectors. -/
noncomputable def h15ContourTraceMissingSector
    (N : ℕ) (η c : ℝ) : ℝ :=
  -h15ContourTraceNormalizationDefect N η c

theorem sum_named_add_missingSector_eq_neg_correction
    (N : ℕ) (η c : ℝ) :
    (∑ k ∈ h15TraceDyadicGcdIndices N,
      h15ContourTraceBlockMode N η c k) +
        h15ContourTraceMissingSector N η c =
      -h15LinearEndpointCorrection N := by
  rw [sum_h15ContourTraceBlockMode]
  unfold h15ContourTraceMissingSector h15ContourTraceNormalizationDefect
  ring

/-! ## First-cutoff normalization test -/

/-- At `N = 2`, the sole possible natural numerator in the `q = 2` row has
zero logarithmic-taper coefficient. -/
@[simp]
theorem h15UnitNumeratorWeight_two_one_two
    (x : (ZMod 2)ˣ) :
    @h15UnitNumeratorWeight 2 1 2 inferInstance x = 0 := by
  classical
  unfold h15UnitNumeratorWeight
  norm_num [dirichletCoeff_two_two]

/-- Consequently the completed `m = 0` orbit vanishes in the only possible
interior row at the first nontrivial cutoff. -/
@[simp]
theorem h15MotohashiZeroOrbitRow_two_one_two
    (η c : ℝ) :
    @h15MotohashiZeroOrbitRow 2 1 2 inferInstance η c = 0 := by
  classical
  unfold h15MotohashiZeroOrbitRow h15MotohashiArithmeticSeed
    inverseCoordinateFourierCoefficient
  simp

theorem h15MotohashiZeroTotal_two (η c : ℝ) :
    h15MotohashiZeroTotal 2 η c = 0 := by
  classical
  have h12 : Finset.Icc 1 2 = {1, 2} := by decide
  unfold h15MotohashiZeroTotal h15MotohashiZeroGcdSlice
  rw [h12]
  simp

/-- There is no intrinsic interior residue at `N = 2`: every possible
interior coefficient contains the vanished endpoint coefficient `c_2(2)`. -/
theorem h15ContourResidueTotal_two (W : ℂ → ℂ) :
    h15ContourResidueTotal W 2 = 0 := by
  classical
  have h12 : Finset.Icc 1 2 = {1, 2} := by decide
  unfold h15ContourResidueTotal h15ContourResidueGcdSlice
    estermannInteriorPairedZeroResidueSummand
    estermannInteriorValueCoefficient coprimeSliceCoefficient
  rw [h12]
  simp [h12, dirichletCoeff_two_two]

/-- The exact diagonal ledger at the first nontrivial cutoff is the universal
Gram value `G(1,1)`. -/
theorem h15GramDiagonalTotal_two :
    h15GramDiagonalTotal 2 = baezDuarteGramEntry 1 1 := by
  classical
  have h12 : Finset.Icc 1 2 = {1, 2} := by decide
  unfold h15GramDiagonalTotal h15GramDiagonalGcdSlice
  rw [h12]
  simp [dirichletCoeff_two_one, dirichletCoeff_two_two]

/-- The three named sectors therefore have an exact, parameter-independent
first-cutoff value. -/
theorem h15ContourTraceNamedTotal_two (η c : ℝ) :
    h15ContourTraceNamedTotal 2 η c = baezDuarteGramEntry 1 1 := by
  unfold h15ContourTraceNamedTotal
  rw [h15ContourResidueTotal_two, h15MotohashiZeroTotal_two,
    h15GramDiagonalTotal_two]
  ring

/-- The first-cutoff test is negative: residue, completion-zero, and Gram
diagonal modes by themselves do not reproduce the negative retained
linear/endpoint correction.  Thus a complete trace normalization genuinely
needs the omitted primal/elementary/Eisenstein sectors. -/
theorem h15ContourTraceNamedTotal_two_ne_neg_correction
    (η c : ℝ) :
    h15ContourTraceNamedTotal 2 η c ≠
      -h15LinearEndpointCorrection 2 := by
  rw [h15ContourTraceNamedTotal_two]
  unfold h15LinearEndpointCorrection
  rw [gramLinearCorrection_two]
  intro h
  have hG : 0 ≤ baezDuarteGramEntry 1 1 := by
    have hdiag := gramDiagonal_nonneg 2
    rw [← h15GramDiagonalTotal_eq_gramDiagonal,
      h15GramDiagonalTotal_two] at hdiag
    exact hdiag
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  linarith

/-- Equivalently, the exact global normalization defect is already nonzero
at `N = 2`. -/
theorem h15ContourTraceNormalizationDefect_two_ne_zero
    (η c : ℝ) :
    h15ContourTraceNormalizationDefect 2 η c ≠ 0 := by
  intro hzero
  apply h15ContourTraceNamedTotal_two_ne_neg_correction η c
  unfold h15ContourTraceNormalizationDefect at hzero
  linarith

end RH.Criteria.NymanBeurling.BCFLogTaperH15ContourTraceModes
