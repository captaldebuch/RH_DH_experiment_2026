import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmGate4CrossModulusSquare
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmGate4DispersionHierarchy
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTCenteredGate
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmTypeIIAnalyticGate
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPeriodReduction

/-!
# Feasibility gates for the direct Ehm route

This module performs three audits needed before using one-variable
Möbius--cotangent estimates in the complete Ehm problem.

* It states the integer-parameter specialization of the power-dyadic row
  estimated by Maier--Rassias and splits the H15 Type-I sum into its `q = 1`
  row, its `q ≥ 2` rows, and an explicit row-shape mismatch.
* It normalizes the diagonal Cauchy--Schwarz majorant by the size of the
  dyadic outer block.  This is the exact null-rate test a diagonal-only proof
  must pass.
* It states the smallest correction-preserving cross-modulus balance.  The
  exact complete-square identity proves that this balance supplies the signed
  Gate-4 target.

No analytic estimate is constructed here.  In particular, the
Maier--Rassias theorem is represented by a proof-carrying structure rather
than an axiom, and its mismatch with the H15 rows is not suppressed.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmDirectFeasibility

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmExplicitFarCutoff
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4CrossModulusSquare
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Dispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4DispersionHierarchy
open RH.Criteria.NymanBeurling.BCFLogTaperEhmGate4Strategy
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit
open RH.Criteria.NymanBeurling.QuadraticInteraction
open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## The exact Maier--Rassias row shape -/

/-- Finite partial sums of the endpoint-corrected Maier--Rassias kernel
`g(x) = -2 * sum_{l ≥ 1} B₁(l x) / l`.

At nonintegral arguments this is the familiar summand
`(1 - 2 * fract (l*x)) / l`.  At integral arguments the periodic Bernoulli
function is zero.  This endpoint convention is essential at the rational
arguments used by Maier--Rassias: the raw fractional-part series would have
a nonzero harmonic mean and would diverge.  The paper uses conditional
Fourier convergence, so the kernel is not defined with Lean's absolutely
convergent `tsum`. -/
noncomputable def maierRassiasKernelPartialSum (L : ℕ) (x : ℝ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 L,
    -2 * bernoulliB1 ((l : ℝ) * x) / (l : ℝ)

/-- Proof-carrying realization of the conditionally convergent kernel used
by Maier--Rassias.  Only the rational arguments needed by the finite rows
are requested. -/
structure MaierRassiasKernel where
  g : ℝ → ℝ
  rational_limit : ∀ n k : ℕ, 0 < k →
    Tendsto (fun L ↦ maierRassiasKernelPartialSum L
      ((n : ℝ) / (k : ℝ))) atTop
      (nhds (g ((n : ℝ) / (k : ℝ))))

/-- The power-dyadic Möbius row in Maier--Rassias, Theorem 2.1, specialized
to an integer exponent `D ≥ 2`:

`sum_{k^D ≤ n < 2 k^D} μ(n) g(n/k)`.
-/
noncomputable def maierRassiasPowerDyadicRow
    (g : ℝ → ℝ) (k D : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (k ^ D) (2 * k ^ D),
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
      g ((n : ℝ) / (k : ℝ))

/-- Exact proof interface for the integer-exponent specialization of
Maier--Rassias, Theorem 2.1.  The cited result provides a fixed `z0 > 0`
and, for every positive `eps`, an implicit constant giving the displayed
power saving.  This structure has no instance in the project. -/
structure MaierRassiasPowerSavingEstimate (K : MaierRassiasKernel) where
  z0 : ℝ
  z0_pos : 0 < z0
  bound : ∀ D : ℕ, 2 ≤ D → ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 2 ≤ k →
      |maierRassiasPowerDyadicRow K.g k D| ≤
        C * (k : ℝ) ^ ((D : ℝ) - z0 + eps)

/-! ## What part of the H15 Type-I form has that shape -/

/-- The `q = 1` portion of the Ehm Type-I range. -/
noncomputable def ehmDyadicNearTypeIQOne
    (R1 : ℝ → ℝ) (X D J U : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc (X + 1) D,
    if d ≤ J then
      ((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) / (m : ℝ)) *
        ehmDyadicNearPairAmplitude X m d *
          R1 ((d : ℝ) / (m : ℝ))
    else 0

/-- The remaining `q ≥ 2` portion of the Ehm Type-I range. -/
noncomputable def ehmDyadicNearTypeIQGeTwo
    (R1 : ℝ → ℝ) (X D J U : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc (X + 1) D,
    ∑ q ∈ Finset.Icc 2 J,
      if d * q ≤ J then
        ((((ArithmeticFunction.moebius m : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius d : ℤ) : ℝ)) / (m : ℝ)) *
          ehmDyadicNearPairAmplitude X m d *
            R1 (((d * q : ℕ) : ℝ) / (m : ℝ))
      else 0

private theorem sum_Icc_one_eq_value_add_sum_Icc_two
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) (J : ℕ) (hJ : 1 ≤ J) :
    (∑ q ∈ Finset.Icc 1 J, f q) =
      f 1 + ∑ q ∈ Finset.Icc 2 J, f q := by
  have hset : Finset.Icc 1 J = {1} ∪ Finset.Icc 2 J := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdis : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 J) := by
    simp
  rw [hset, Finset.sum_union hdis]
  simp

/-- Exact separation of the H15 Type-I sum into its single `q = 1` row and
all `q ≥ 2` rows.  A one-row theorem can address at most the first summand. -/
theorem ehmDyadicNearTypeI_eq_qOne_add_qGeTwo
    (R1 : ℝ → ℝ) (X D J U : ℕ) (hJ : 1 ≤ J) :
    ehmDyadicNearTypeI R1 X D J U =
      ehmDyadicNearTypeIQOne R1 X D J U +
        ehmDyadicNearTypeIQGeTwo R1 X D J U := by
  classical
  unfold ehmDyadicNearTypeI ehmDyadicNearMobiusBilinearMRange
    ehmDyadicNearTypeIQOne ehmDyadicNearTypeIQGeTwo
  simp_rw [sum_Icc_one_eq_value_add_sum_Icc_two
    (J := J) (hJ := hJ)]
  simp_rw [Finset.sum_add_distrib]
  simp

/-- The actual inner `q = 1` H15 row at fixed outer variable `m`.  Unlike
the Maier--Rassias row, it has a cutoff-dependent taper-pair amplitude and a
general interval `[X+1,D]`. -/
noncomputable def ehmTypeIQOneInnerRow
    (R1 : ℝ → ℝ) (X D J m : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (X + 1) D,
    if d ≤ J then
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        ehmDyadicNearPairAmplitude X m d *
          R1 ((d : ℝ) / (m : ℝ))
    else 0

/-- Exact outer factorization of the H15 `q = 1` sector. -/
theorem ehmDyadicNearTypeIQOne_eq_outer_rows
    (R1 : ℝ → ℝ) (X D J U : ℕ) :
    ehmDyadicNearTypeIQOne R1 X D J U =
      ∑ m ∈ Finset.Icc 1 U,
        (((ArithmeticFunction.moebius m : ℤ) : ℝ) / (m : ℝ)) *
          ehmTypeIQOneInnerRow R1 X D J m := by
  classical
  unfold ehmDyadicNearTypeIQOne ehmTypeIQOneInnerRow
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d ≤ J
  · simp only [hd, if_true]
    ring
  · simp [hd]

/-- The exact residual between one H15 `q = 1` row and a chosen
Maier--Rassias power-dyadic model row.  It records, rather than hides, the
kernel, interval, and taper mismatches. -/
noncomputable def ehmMaierRassiasRowMismatch
    (R1 g : ℝ → ℝ) (X D J m E : ℕ) : ℝ :=
  ehmTypeIQOneInnerRow R1 X D J m -
    maierRassiasPowerDyadicRow g m E

/-- Exact reconstruction of the complete Type-I range from the model rows,
their explicit mismatches, and the untouched `q ≥ 2` sector. -/
theorem ehmDyadicNearTypeI_eq_maierRassiasModel_add_mismatch_add_qGeTwo
    (R1 g : ℝ → ℝ) (X D J U E : ℕ) (hJ : 1 ≤ J) :
    ehmDyadicNearTypeI R1 X D J U =
      (∑ m ∈ Finset.Icc 1 U,
        (((ArithmeticFunction.moebius m : ℤ) : ℝ) / (m : ℝ)) *
          maierRassiasPowerDyadicRow g m E) +
      (∑ m ∈ Finset.Icc 1 U,
        (((ArithmeticFunction.moebius m : ℤ) : ℝ) / (m : ℝ)) *
          ehmMaierRassiasRowMismatch R1 g X D J m E) +
      ehmDyadicNearTypeIQGeTwo R1 X D J U := by
  rw [ehmDyadicNearTypeI_eq_qOne_add_qGeTwo R1 X D J U hJ,
    ehmDyadicNearTypeIQOne_eq_outer_rows]
  unfold ehmMaierRassiasRowMismatch
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

/-! ## The normalized diagonal stop test -/

/-- The diagonal Cauchy--Schwarz majorant divided by the exact size of the
outer dyadic block. -/
noncomputable def primitiveCoupledNormalizedDiagonalMajorant
    {V : VaalerSawtoothPackage} {Q J U Y : ℕ} (X : ℕ)
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) : ℝ :=
  primitiveCoupledDiagonalMajorant B /
    ((ehmDyadicNBlock X).card : ℝ)

private theorem dyadicBlock_card_pos_real (X : ℕ) :
    0 < ((ehmDyadicNBlock X).card : ℝ) := by
  exact_mod_cast (ehmDyadicNBlock_nonempty X).card_pos

/-- A diagonal proof closes at one scale exactly when its normalized
majorant is below the proposed null rate. -/
theorem normalizedDiagonalMajorant_le_iff
    {V : VaalerSawtoothPackage} {Q J U Y : ℕ} (X : ℕ)
    (B : PrimitiveCoupledBlockDecomposition V Q X J U Y) (eta : ℝ) :
    primitiveCoupledNormalizedDiagonalMajorant X B ≤ eta ↔
      primitiveCoupledDiagonalMajorant B ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta := by
  unfold primitiveCoupledNormalizedDiagonalMajorant
  rw [div_le_iff₀ (dyadicBlock_card_pos_real X)]
  ring_nf

/-- A positive eventual floor for the normalized diagonal majorant rules
out any smaller proposed rate on a cofinal set of secondary cutoffs.  This
is the executable stop condition for a diagonal-only strategy. -/
theorem not_frequently_diagonal_bound_of_eventual_floor
    {V : VaalerSawtoothPackage} {degree : ℕ → ℕ → ℕ}
    {U : ℕ → ℕ} {productCutoff : ℕ → ℕ → ℕ}
    (decomposition : ∀ X J,
      PrimitiveCoupledBlockDecomposition V (degree X J) X J
        (U X) (productCutoff X J))
    (X : ℕ) (delta eta : ℝ) (heta : eta < delta)
    (hfloor : ∀ᶠ J : ℕ in atTop,
      delta ≤ primitiveCoupledNormalizedDiagonalMajorant X
        (decomposition X J)) :
    ¬ ∃ᶠ J : ℕ in atTop,
      primitiveCoupledDiagonalMajorant (decomposition X J) ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta := by
  intro hfreq
  have hnot : ∀ᶠ J : ℕ in atTop,
      ¬ primitiveCoupledDiagonalMajorant (decomposition X J) ≤
        ((ehmDyadicNBlock X).card : ℝ) * eta :=
    hfloor.mono fun J hJ hbound ↦ by
      have heta' : primitiveCoupledNormalizedDiagonalMajorant X
          (decomposition X J) ≤ eta :=
        (normalizedDiagonalMajorant_le_iff X (decomposition X J) eta).2 hbound
      exact (not_le_of_gt heta) (hJ.trans heta')
  exact (not_frequently.mpr hnot) hfreq

/-! ## The minimal correction-preserving cross-modulus theorem -/

/-- The squared cross-modulus balance required after the complete signed
square is expanded.  It retains the same-modulus diagonal and the
correction--mode cross term through `highProductRequiredOffDiagonalBalance`.
-/
def EhmCrossModulusBalanceCofinalBound
    (D : PrimitiveCoupledDispersionData) : Prop :=
  ∀ X : ℕ, 2 ≤ X →
    ∃ᶠ J : ℕ in atTop,
      ehmExplicitFarCutoff X ≤ J ∧
      (highProductPrimitiveCrossModulusOffDiagonal D.V (D.degree X J) X
        (ehmExplicitFarCutoff X) J (D.productCutoff X J)).re -
          highProductRequiredOffDiagonalBalance D.V (D.degree X J) X J
            (D.U X) (D.productCutoff X J) ≤
        (((ehmDyadicNBlock X).card : ℝ) * D.etaHigh X) ^ 2

private theorem abs_re_le_of_normSq_le_sq
    (z : ℂ) (a : ℝ) (ha : 0 ≤ a)
    (h : Complex.normSq z ≤ a ^ 2) : |z.re| ≤ a := by
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hnorm_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  have hnorm_sq : ‖z‖ ^ 2 = Complex.normSq z := by
    rw [Complex.sq_norm]
  have hnorm : ‖z‖ ≤ a := by
    apply (sq_le_sq₀ hnorm_nonneg ha).mp
    rw [hnorm_sq]
    exact h
  exact hre.trans hnorm

/-- The new cross-modulus theorem above is exactly sufficient for the
signed real-part Gate-4 target.  No triangle inequality is taken across
moduli, and the retained correction is not estimated separately. -/
theorem signedRealCofinalBound_of_crossModulusBalance
    {D : PrimitiveCoupledDispersionData}
    (H : EhmCrossModulusBalanceCofinalBound D) :
    D.SignedRealCofinalBound := by
  intro X hX
  refine (H X hX).mono ?_
  intro J hJ
  refine ⟨hJ.1, ?_⟩
  apply abs_re_le_of_normSq_le_sq
  · exact mul_nonneg (Nat.cast_nonneg _) (D.etaHigh_nonneg X)
  · rw [← offDiagonal_sub_requiredBalance_eq_core_normSq
      D.V (D.degree X J) X J (D.U X) (D.productCutoff X J) (by omega)]
    exact hJ.2

/-- Consequently, a proved correction-preserving cross-modulus balance
constructs the existing honest Gate-4 dispersion estimate. -/
noncomputable def PrimitiveCoupledDispersionData.toDispersionEstimateOfCrossModulus
    (D : PrimitiveCoupledDispersionData)
    (H : EhmCrossModulusBalanceCofinalBound D) :
    EhmGate4PrimitiveCoupledDispersionEstimate :=
  D.toDispersionEstimate (signedRealCofinalBound_of_crossModulusBalance H)

end RH.Criteria.NymanBeurling.BCFLogTaperEhmDirectFeasibility
