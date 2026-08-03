import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperSpectral

/-!
# Exact cancellation anatomy for the BCF logarithmic taper

This module makes explicit a point that is easy to lose in an asymptotic
discussion of the logarithmically tapered BCF energy.  The diagonal Gram
contribution is not itself a small error term: the eventual H15 estimate has
to control its cancellation with the off-diagonal Gram contribution and the
linear correction.

Everything in this file is finite algebra.  In particular, no cancellation
estimate for the Möbius function is assumed or asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperCancellationAnatomy

open scoped BigOperators
open Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The `h = k` part of the finite BCF Gram quadratic form. -/
noncomputable def gramDiagonal (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N,
    dirichletCoeff N h * dirichletCoeff N h * baezDuarteGramEntry h h

/-- The complement of `gramDiagonal` in the exact BCF Gram quadratic form.

It is defined by subtraction on purpose: this records the signed object that
must cancel the diagonal, without silently replacing it by an absolute-value
bound. -/
noncomputable def gramOffDiagonal (N : ℕ) : ℝ :=
  gramQuadraticForm N - gramDiagonal N

/-- The weighted diagonal mass before multiplication by the universal Gram
entry `G(1,1)`. -/
noncomputable def logTaperDiagonalMass (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N,
    dirichletCoeff N h * dirichletCoeff N h * (h : ℝ)⁻¹

/-- The signed part which has to compensate the diagonal contribution. -/
noncomputable def compensatingCorrelation (N : ℕ) : ℝ :=
  gramOffDiagonal N + 2 * gramLinearCorrection N + 1

/-- The diagonal mass is exactly a square-Möbius weighted harmonic sum.  The
signs of `μ` disappear here, so any eventual decay of the full energy cannot
come from diagonal Möbius cancellation. -/
theorem logTaperDiagonalMass_eq_moebius_sq_weight_sq (N : ℕ) :
    logTaperDiagonalMass N =
      ∑ h ∈ Finset.Icc 1 N,
        ((((ArithmeticFunction.moebius h : ℤ) : ℝ) ^ 2) * weight N h ^ 2 *
          (h : ℝ)⁻¹) := by
  unfold logTaperDiagonalMass dirichletCoeff
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- The diagonal mass is nonnegative at every finite cutoff. -/
theorem logTaperDiagonalMass_nonneg (N : ℕ) : 0 ≤ logTaperDiagonalMass N := by
  unfold logTaperDiagonalMass
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg (mul_self_nonneg _) (inv_nonneg.mpr (Nat.cast_nonneg h))

/-- The `h = 1` summand already gives a unit lower bound on the diagonal mass
at every nontrivial BCF cutoff. -/
theorem one_le_logTaperDiagonalMass {N : ℕ} (hN : 2 ≤ N) :
    1 ≤ logTaperDiagonalMass N := by
  have hmem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hcoeff : dirichletCoeff N 1 = 1 := by
    unfold dirichletCoeff
    rw [weight_one hN]
    norm_num
  calc
    (1 : ℝ) =
        dirichletCoeff N 1 * dirichletCoeff N 1 * ((1 : ℕ) : ℝ)⁻¹ := by
      rw [hcoeff]
      norm_num
    _ ≤ logTaperDiagonalMass N := by
      unfold logTaperDiagonalMass
      refine Finset.single_le_sum
        (f := fun h => dirichletCoeff N h * dirichletCoeff N h * (h : ℝ)⁻¹)
        (fun h _ => ?_) hmem
      exact mul_nonneg (mul_self_nonneg _) (inv_nonneg.mpr (Nat.cast_nonneg h))

/-- Exact diagonal/off-diagonal splitting of the quadratic form. -/
theorem gramQuadraticForm_eq_diagonal_add_offDiagonal (N : ℕ) :
    gramQuadraticForm N = gramDiagonal N + gramOffDiagonal N := by
  unfold gramOffDiagonal
  ring

/-- Exact scaling formula for the diagonal Gram contribution.  This is the
finite identity behind the observation that the diagonal is a separate
positive-scale contribution, rather than a term which can simply be required
to decay on its own. -/
theorem gramDiagonal_eq_g11_mul_logTaperDiagonalMass (N : ℕ) :
    gramDiagonal N =
      baezDuarteGramEntry 1 1 * logTaperDiagonalMass N := by
  unfold gramDiagonal logTaperDiagonalMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hhpos : 0 < h :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hh).1
  have hscale : baezDuarteGramEntry h h =
      (h : ℝ)⁻¹ * baezDuarteGramEntry 1 1 := by
    simpa using baezDuarteGramEntry_scale h 1 1 hhpos Nat.one_pos Nat.one_pos
  rw [hscale]
  ring

/-- The diagonal Gram contribution is nonnegative.  The proof is entirely
finite/integral algebra and makes no asymptotic assertion. -/
theorem gramDiagonal_nonneg (N : ℕ) : 0 ≤ gramDiagonal N := by
  rw [gramDiagonal_eq_g11_mul_logTaperDiagonalMass]
  apply mul_nonneg _ (logTaperDiagonalMass_nonneg N)
  unfold baezDuarteGramEntry
  apply MeasureTheory.integral_nonneg
  intro x
  exact mul_self_nonneg _

/-- The universal diagonal Gram entry is strictly positive.  The rational
interval certificate is proved from the explicit `G(1,1)` evaluation. -/
theorem g11_pos : 0 < baezDuarteGramEntry 1 1 := by
  have hbound := G11_interval_axiom
  nlinarith [hbound.1]

/-- The certified `G(1,1)` interval is already strictly above one. -/
theorem one_lt_g11 : 1 < baezDuarteGramEntry 1 1 := by
  have hbound := G11_interval_axiom
  nlinarith [hbound.1]

/-- Every nontrivial log-tapered BCF quadratic form has a strictly positive
diagonal component.  Thus any small total energy must arise through the
signed compensating correlation, not through decay of the diagonal itself. -/
theorem gramDiagonal_pos {N : ℕ} (hN : 2 ≤ N) : 0 < gramDiagonal N := by
  rw [gramDiagonal_eq_g11_mul_logTaperDiagonalMass]
  exact mul_pos g11_pos (lt_of_lt_of_le zero_lt_one (one_le_logTaperDiagonalMass hN))

/-- The diagonal is in fact uniformly larger than one at every nontrivial
cutoff. -/
theorem one_lt_gramDiagonal {N : ℕ} (hN : 2 ≤ N) : 1 < gramDiagonal N := by
  rw [gramDiagonal_eq_g11_mul_logTaperDiagonalMass]
  have hmass := one_le_logTaperDiagonalMass hN
  calc
    (1 : ℝ) < baezDuarteGramEntry 1 1 := one_lt_g11
    _ = baezDuarteGramEntry 1 1 * 1 := (mul_one _).symm
    _ ≤ baezDuarteGramEntry 1 1 * logTaperDiagonalMass N :=
      mul_le_mul_of_nonneg_left hmass g11_pos.le

/-- Closed form of the linear BCF correction.  This is only a finite rewrite;
it does not give a decay estimate for the resulting weighted Möbius sum. -/
theorem gramLinearCorrection_eq_explicit (N : ℕ) :
    gramLinearCorrection N =
      ∑ k ∈ Finset.Icc 1 N,
        dirichletCoeff N k *
          ((Real.log (k : ℝ) + 1 - Real.eulerMascheroniConstant) / (k : ℝ)) := by
  unfold gramLinearCorrection
  apply Finset.sum_congr rfl
  intro k hk
  have hk_one_le : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hk_one_le
  rw [RH.Certificates.innerProductChiRho_formula, hcast]

/-- The entire coupled H15 expression, displayed as diagonal, off-diagonal,
linear, and constant components.  This is an exact equality, not a bound. -/
theorem coupledGcdRatioExpression_eq_diagonal_offDiagonal_linear (N : ℕ) :
    coupledGcdRatioExpression N =
      gramDiagonal N + gramOffDiagonal N + 2 * gramLinearCorrection N + 1 := by
  rw [← spectralEnergy_eq_coupledGcdRatioExpression,
    ← energy_eq_spectralEnergy,
    energy_eq_gramQuadraticForm_add_linearCorrection,
    gramQuadraticForm_eq_diagonal_add_offDiagonal]

/-- The coupled expression is a diagonal term plus its signed compensator. -/
theorem coupledGcdRatioExpression_eq_diagonal_add_compensatingCorrelation (N : ℕ) :
    coupledGcdRatioExpression N =
      gramDiagonal N + compensatingCorrelation N := by
  rw [coupledGcdRatioExpression_eq_diagonal_offDiagonal_linear]
  unfold compensatingCorrelation
  ring

/-- Any genuine H15 estimate forces the off-diagonal-plus-linear compensator
to be eventually negative.  This is a consequence of the positive diagonal
and energy convergence; it does not supply that convergence. -/
theorem compensatingCorrelation_eventually_neg
    (H : CoupledLogTaperCancellationEstimate) :
    ∀ᶠ N in atTop, compensatingCorrelation N < 0 := by
  have hzero := coupledGcdRatioExpression_tendsto_zero H
  have hsmall : ∀ᶠ N in atTop, coupledGcdRatioExpression N < (1 / 2 : ℝ) :=
    hzero.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop (2 : ℕ), hsmall] with N hN henergy
  rw [coupledGcdRatioExpression_eq_diagonal_add_compensatingCorrelation] at henergy
  nlinarith [one_lt_gramDiagonal hN]

/-- The final H15 cancellation estimate is equivalently an estimate for the
sum of the diagonal, off-diagonal, linear, and constant pieces.  This form
prevents an invalid reduction to separate estimates for its components. -/
theorem coupledLogTaper_bound_iff_diagonal_offDiagonal_linear
    (C α : ℝ) (N : ℕ) :
    |coupledGcdRatioExpression N| ≤ C / (Real.log (N : ℝ)) ^ α ↔
      |gramDiagonal N + gramOffDiagonal N + 2 * gramLinearCorrection N + 1|
        ≤ C / (Real.log (N : ℝ)) ^ α := by
  rw [coupledGcdRatioExpression_eq_diagonal_offDiagonal_linear]

/-- Equivalent form of the H15 bound in which the required compensating
correlation is displayed explicitly.  This is a reformulation, not a weaker
route: it says that the off-diagonal-plus-linear expression must approximate
the negative diagonal mass to log-power accuracy. -/
theorem coupledLogTaper_bound_iff_compensatingCorrelation
    (C α : ℝ) (N : ℕ) :
    |coupledGcdRatioExpression N| ≤ C / (Real.log (N : ℝ)) ^ α ↔
      |baezDuarteGramEntry 1 1 * logTaperDiagonalMass N +
          compensatingCorrelation N|
        ≤ C / (Real.log (N : ℝ)) ^ α := by
  rw [coupledGcdRatioExpression_eq_diagonal_add_compensatingCorrelation,
    gramDiagonal_eq_g11_mul_logTaperDiagonalMass]

/-- A research-facing package for the exact compensator estimate.  It is
logically equivalent to `CoupledLogTaperCancellationEstimate` by the
preceding finite identity, and is introduced only to make clear that any
analytic route must preserve the coupling with the diagonal term. -/
structure CompensatingCorrelationEstimate where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ N : ℕ, 2 ≤ N →
    |baezDuarteGramEntry 1 1 * logTaperDiagonalMass N +
        compensatingCorrelation N|
      ≤ C / (Real.log (N : ℝ)) ^ α

/-- The compensator package is exactly sufficient for the already-existing
Route D cancellation interface. -/
def coupledLogTaperCancellation_of_compensatingCorrelation
    (H : CompensatingCorrelationEstimate) : CoupledLogTaperCancellationEstimate where
  C := H.C
  C_pos := H.C_pos
  α := H.α
  α_pos := H.α_pos
  bound N hN :=
    (coupledLogTaper_bound_iff_compensatingCorrelation H.C H.α N).mpr (H.bound N hN)

/-- Conversely, the existing coupled H15 interface supplies the compensator
form with the same constants and exponent. -/
def compensatingCorrelationEstimate_of_coupledLogTaperCancellation
    (H : CoupledLogTaperCancellationEstimate) : CompensatingCorrelationEstimate where
  C := H.C
  C_pos := H.C_pos
  α := H.α
  α_pos := H.α_pos
  bound N hN :=
    (coupledLogTaper_bound_iff_compensatingCorrelation H.C H.α N).mp (H.bound N hN)

end RH.Criteria.NymanBeurling.BCFLogTaperCancellationAnatomy
