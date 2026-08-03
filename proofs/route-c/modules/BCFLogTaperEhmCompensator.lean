import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmKernel
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperCancellationAnatomy

/-!
# The Ehm `S₁` form of the BCF compensating correlation

This module combines the exact cancellation anatomy of the BCF logarithmic
taper with Ehm's pointwise `S₁` Gram-kernel interface.  It isolates the final
two-variable signed object

`Σ_m λ_N(m)/m · Σ_n λ_N(n) S₁(n/m)`

together with the one-variable moment correction with which it must remain
coupled.  No asymptotic estimate is asserted.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmCompensator

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperGcd
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral
open RH.Criteria.NymanBeurling.BCFLogTaperCancellationAnatomy
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The finite moment correction which accompanies Ehm's signed `S₁`
quadratic term in the complete BCF energy. -/
noncomputable def ehmS1MomentCorrection (N : ℕ) : ℝ :=
  ehmK * ehmM 0 N * ehmL 0 N + ehmM 0 N * ehmL 1 N / 2 -
      ehmM 1 N * ehmL 0 N / 2 +
    2 * (ehmL 1 N + (1 - Real.eulerMascheroniConstant) * ehmL 0 N) + 1

/-- The diagonal contribution of the `S₁(n/m)` bilinear kernel. -/
noncomputable def ehmS1DiagonalTerm (S1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  S1 1 * logTaperDiagonalMass N

/-- The signed complement of the `S₁` diagonal inside the exact bilinear
term.  It is kept signed and is not replaced by a sum of absolute values. -/
noncomputable def ehmS1OffDiagonalTerm (S1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  ehmS1QuadraticTerm S1 N - ehmS1DiagonalTerm S1 N

/-- The diagonal part of the `S₁` bilinear term, written as the original
double sum with an equality selector. -/
noncomputable def ehmS1DiagonalSum (S1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if m = n then
      dirichletCoeff N m / (m : ℝ) *
        (dirichletCoeff N n * S1 ((n : ℝ) / (m : ℝ)))
    else 0

/-- The actual signed `m ≠ n` portion of Ehm's `S₁` bilinear sum. -/
noncomputable def ehmS1OffDiagonalSum (S1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if m = n then 0
    else
      dirichletCoeff N m / (m : ℝ) *
        (dirichletCoeff N n * S1 ((n : ℝ) / (m : ℝ)))

/-- The same off-diagonal sum with the two indices exchanged inside the
summand.  Keeping this as a separate finite sum makes the later averaging
step transparent and does not assume any reciprocity property of `S1`. -/
noncomputable def ehmS1SwappedOffDiagonalSum (S1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if m = n then 0
    else
      dirichletCoeff N n / (n : ℝ) *
        (dirichletCoeff N m * S1 ((m : ℝ) / (n : ℝ)))

/-- The symmetric-kernel presentation of the signed off-diagonal `S1`
sum.  This is an exact finite average, not an estimate. -/
noncomputable def ehmS1SymmetrizedOffDiagonalSum
    (S1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  (ehmS1OffDiagonalSum S1 N + ehmS1SwappedOffDiagonalSum S1 N) / 2

/-- The symmetric two-ratio kernel which remains after pairing `(m,n)`
with `(n,m)`. -/
noncomputable def ehmS1SymmetricPairKernel
    (S1 : ℝ → ℝ) (m n : ℕ) : ℝ :=
  (S1 ((n : ℝ) / (m : ℝ)) / (m : ℝ) +
    S1 ((m : ℝ) / (n : ℝ)) / (n : ℝ)) / 2

/-- The symmetric-kernel off-diagonal form as one explicit double sum. -/
noncomputable def ehmS1SymmetricKernelOffDiagonalSum
    (S1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if m = n then 0
    else
      dirichletCoeff N m * dirichletCoeff N n *
        ehmS1SymmetricPairKernel S1 m n

/-- Half-kernel contribution from the strict upper triangle. -/
noncomputable def ehmS1SymmetricUpperHalfSum
    (S1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if m < n then
      dirichletCoeff N m * dirichletCoeff N n *
        ehmS1SymmetricPairKernel S1 m n
    else 0

/-- Half-kernel contribution from the strict lower triangle. -/
noncomputable def ehmS1SymmetricLowerHalfSum
    (S1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if n < m then
      dirichletCoeff N m * dirichletCoeff N n *
        ehmS1SymmetricPairKernel S1 m n
    else 0

/-- The complete paired kernel on the strict upper triangle, with no
factor `1/2`. -/
noncomputable def ehmS1UpperTriangleSum
    (S1 : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if m < n then
      dirichletCoeff N m * dirichletCoeff N n *
        (S1 ((n : ℝ) / (m : ℝ)) / (m : ℝ) +
          S1 ((m : ℝ) / (n : ℝ)) / (n : ℝ))
    else 0

/-- Reciprocity-completed upper-triangle kernel.  Its sole `S₁` value is
at `n/m > 1`; the elementary terms must remain coupled to the rest of the
H15 expression. -/
noncomputable def ehmS1OneSidedUpperTriangleSum (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if m < n then
      dirichletCoeff N m * dirichletCoeff N n *
        (2 * ehmS1Autocorrelation ((n : ℝ) / (m : ℝ)) / (m : ℝ) +
          ehmK * (1 / (n : ℝ) - 1 / (m : ℝ)) +
          (1 / 2 : ℝ) * (1 / (n : ℝ) + 1 / (m : ℝ)) *
            Real.log ((n : ℝ) / (m : ℝ)))
    else 0

/-- The balanced-ratio part `1 < n/m < 2` of the one-sided kernel. -/
noncomputable def ehmS1OneSidedBalancedRatioSum (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if m < n ∧ n < 2 * m then
      dirichletCoeff N m * dirichletCoeff N n *
        (2 * ehmS1Autocorrelation ((n : ℝ) / (m : ℝ)) / (m : ℝ) +
          ehmK * (1 / (n : ℝ) - 1 / (m : ℝ)) +
          (1 / 2 : ℝ) * (1 / (n : ℝ) + 1 / (m : ℝ)) *
            Real.log ((n : ℝ) / (m : ℝ)))
    else 0

/-- The far-ratio part `n/m ≥ 2` of the one-sided kernel. -/
noncomputable def ehmS1OneSidedFarRatioSum (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    if m < n ∧ 2 * m ≤ n then
      dirichletCoeff N m * dirichletCoeff N n *
        (2 * ehmS1Autocorrelation ((n : ℝ) / (m : ℝ)) / (m : ℝ) +
          ehmK * (1 / (n : ℝ) - 1 / (m : ℝ)) +
          (1 / 2 : ℝ) * (1 / (n : ℝ) + 1 / (m : ℝ)) *
            Real.log ((n : ℝ) / (m : ℝ)))
    else 0

/-- Exact partition of the one-sided upper triangle at ratio `2`. -/
theorem ehmS1OneSidedUpperTriangleSum_eq_balanced_add_far (N : ℕ) :
    ehmS1OneSidedUpperTriangleSum N =
      ehmS1OneSidedBalancedRatioSum N +
        ehmS1OneSidedFarRatioSum N := by
  classical
  unfold ehmS1OneSidedUpperTriangleSum ehmS1OneSidedBalancedRatioSum
    ehmS1OneSidedFarRatioSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hmn : m < n
  · by_cases hfar : 2 * m ≤ n
    · have hnotbal : ¬n < 2 * m := by omega
      simp [hmn, hfar, hnotbal]
    · have hbal : n < 2 * m := by omega
      simp [hmn, hfar, hbal]
  · simp [hmn]

/-- Symmetry of the paired `S₁` kernel. -/
theorem ehmS1SymmetricPairKernel_comm (S1 : ℝ → ℝ) (m n : ℕ) :
    ehmS1SymmetricPairKernel S1 m n =
      ehmS1SymmetricPairKernel S1 n m := by
  unfold ehmS1SymmetricPairKernel
  ring

/-- Swapping the two indices identifies the lower and upper triangular
half-kernel sums. -/
theorem ehmS1SymmetricLowerHalfSum_eq_upperHalfSum
    (S1 : ℝ → ℝ) (N : ℕ) :
    ehmS1SymmetricLowerHalfSum S1 N =
      ehmS1SymmetricUpperHalfSum S1 N := by
  classical
  unfold ehmS1SymmetricLowerHalfSum ehmS1SymmetricUpperHalfSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  by_cases hmn : m < n
  · simp [hmn, ehmS1SymmetricPairKernel_comm, mul_comm]
  · simp [hmn]

/-- The off-diagonal symmetric double sum is the sum of its two strict
triangles. -/
theorem ehmS1SymmetricKernelOffDiagonalSum_eq_upper_add_lower
    (S1 : ℝ → ℝ) (N : ℕ) :
    ehmS1SymmetricKernelOffDiagonalSum S1 N =
      ehmS1SymmetricUpperHalfSum S1 N +
        ehmS1SymmetricLowerHalfSum S1 N := by
  classical
  unfold ehmS1SymmetricKernelOffDiagonalSum ehmS1SymmetricUpperHalfSum
    ehmS1SymmetricLowerHalfSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases heq : m = n
  · simp [heq]
  · rcases lt_or_gt_of_ne heq with hlt | hgt
    · simp [heq, hlt, Nat.not_lt_of_ge hlt.le]
    · simp [heq, hgt, Nat.not_lt_of_ge hgt.le]

/-- Doubling the upper half-kernel removes its factor `1/2`. -/
theorem two_mul_ehmS1SymmetricUpperHalfSum_eq_upperTriangleSum
    (S1 : ℝ → ℝ) (N : ℕ) :
    2 * ehmS1SymmetricUpperHalfSum S1 N =
      ehmS1UpperTriangleSum S1 N := by
  classical
  unfold ehmS1SymmetricUpperHalfSum ehmS1UpperTriangleSum
    ehmS1SymmetricPairKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hmn : m < n <;> simp [hmn] <;> ring

/-- Exact unordered-pair form of the symmetric off-diagonal kernel. -/
theorem ehmS1SymmetricKernelOffDiagonalSum_eq_upperTriangleSum
    (S1 : ℝ → ℝ) (N : ℕ) :
    ehmS1SymmetricKernelOffDiagonalSum S1 N =
      ehmS1UpperTriangleSum S1 N := by
  rw [ehmS1SymmetricKernelOffDiagonalSum_eq_upper_add_lower,
    ehmS1SymmetricLowerHalfSum_eq_upperHalfSum,
    ← two_mul_ehmS1SymmetricUpperHalfSum_eq_upperTriangleSum]
  ring

/-- Ehm reciprocity converts the paired upper triangle to its exact
one-sided form. -/
theorem ehmS1UpperTriangleSum_eq_oneSided (N : ℕ) :
    ehmS1UpperTriangleSum ehmS1Autocorrelation N =
      ehmS1OneSidedUpperTriangleSum N := by
  classical
  unfold ehmS1UpperTriangleSum ehmS1OneSidedUpperTriangleSum
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m < n
  · have hmpos : 0 < m :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1
    have hnpos : 0 < n :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    simp only [if_pos hmn]
    rw [ehmS1Autocorrelation_pair_reciprocity_rat m n hmpos hnpos]
  · simp [hmn]

/-- Exchanging the two finite indices leaves the off-diagonal sum
unchanged. -/
theorem ehmS1OffDiagonalSum_eq_swapped (S1 : ℝ → ℝ) (N : ℕ) :
    ehmS1OffDiagonalSum S1 N = ehmS1SwappedOffDiagonalSum S1 N := by
  classical
  unfold ehmS1OffDiagonalSum ehmS1SwappedOffDiagonalSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  by_cases hmn : m = n <;> simp [hmn, eq_comm]

/-- Thus the symmetric average is exactly the original signed
off-diagonal sum. -/
theorem ehmS1OffDiagonalSum_eq_symmetrized (S1 : ℝ → ℝ) (N : ℕ) :
    ehmS1OffDiagonalSum S1 N =
      ehmS1SymmetrizedOffDiagonalSum S1 N := by
  rw [ehmS1SymmetrizedOffDiagonalSum,
    ← ehmS1OffDiagonalSum_eq_swapped S1 N]
  ring

/-- Expansion of the symmetric average as a single double sum with the
explicit symmetric pair kernel. -/
theorem ehmS1SymmetrizedOffDiagonalSum_eq_symmetricKernelSum
    (S1 : ℝ → ℝ) (N : ℕ) :
    ehmS1SymmetrizedOffDiagonalSum S1 N =
      ehmS1SymmetricKernelOffDiagonalSum S1 N := by
  classical
  unfold ehmS1SymmetrizedOffDiagonalSum ehmS1OffDiagonalSum
    ehmS1SwappedOffDiagonalSum ehmS1SymmetricKernelOffDiagonalSum
    ehmS1SymmetricPairKernel
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hmn : m = n <;> simp [hmn] <;> ring

/-- Partition the complete `S₁` quadratic term by equality of its two
indices. -/
theorem ehmS1QuadraticTerm_eq_diagonalSum_add_offDiagonalSum
    (S1 : ℝ → ℝ) (N : ℕ) :
    ehmS1QuadraticTerm S1 N =
      ehmS1DiagonalSum S1 N + ehmS1OffDiagonalSum S1 N := by
  classical
  unfold ehmS1QuadraticTerm ehmS1DiagonalSum ehmS1OffDiagonalSum
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hmn : m = n <;> simp [hmn]

/-- The selected diagonal double sum is exactly `S₁(1)` times the
square-Möbius diagonal mass. -/
theorem ehmS1DiagonalSum_eq_diagonalTerm (S1 : ℝ → ℝ) (N : ℕ) :
    ehmS1DiagonalSum S1 N = ehmS1DiagonalTerm S1 N := by
  classical
  unfold ehmS1DiagonalSum ehmS1DiagonalTerm logTaperDiagonalMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hmpos)
  simp [hm, hmne]
  ring

/-- Exact diagonal/off-diagonal splitting of Ehm's `S₁` quadratic term. -/
theorem ehmS1QuadraticTerm_eq_diagonal_add_offDiagonal
    (S1 : ℝ → ℝ) (N : ℕ) :
    ehmS1QuadraticTerm S1 N =
      ehmS1DiagonalTerm S1 N + ehmS1OffDiagonalTerm S1 N := by
  unfold ehmS1OffDiagonalTerm
  ring

/-- The subtraction-based off-diagonal term agrees with the explicit signed
double sum restricted by `m ≠ n`. -/
theorem ehmS1OffDiagonalTerm_eq_offDiagonalSum (S1 : ℝ → ℝ) (N : ℕ) :
    ehmS1OffDiagonalTerm S1 N = ehmS1OffDiagonalSum S1 N := by
  rw [ehmS1OffDiagonalTerm, ehmS1QuadraticTerm_eq_diagonalSum_add_offDiagonalSum,
    ehmS1DiagonalSum_eq_diagonalTerm]
  ring

/-- The pointwise Ehm kernel formula fixes the value of `S₁(1)` exactly. -/
theorem ehmS1_one_eq_g11_sub_ehmK (H : EhmS1PointwiseKernelPackage) :
    H.S1 1 = baezDuarteGramEntry 1 1 - ehmK := by
  have hformula := H.gram_formula 1 1 Nat.one_pos Nat.one_pos
  norm_num at hformula
  linarith

/-- The diagonal `S₁` contribution is an explicit multiple of the same
square-Möbius mass found in the Gram decomposition. -/
theorem ehmS1DiagonalTerm_eq_g11_sub_ehmK_mul_mass
    (H : EhmS1PointwiseKernelPackage) (N : ℕ) :
    ehmS1DiagonalTerm H.S1 N =
      (baezDuarteGramEntry 1 1 - ehmK) * logTaperDiagonalMass N := by
  unfold ehmS1DiagonalTerm
  rw [ehmS1_one_eq_g11_sub_ehmK H]

/-- Exact pointwise-Ehm decomposition of the fully coupled H15 expression.
The theorem is finite algebra once the cited pointwise `S₁` Gram formula is
supplied through `H`. -/
theorem coupledGcdRatioExpression_eq_ehmS1QuadraticTerm_add_momentCorrection
    (H : EhmS1PointwiseKernelPackage) (N : ℕ) :
    coupledGcdRatioExpression N =
      ehmS1QuadraticTerm H.S1 N + ehmS1MomentCorrection N := by
  rw [coupledGcdRatioExpression_eq_gramQuadraticForm,
    gramQuadraticForm_eq_ehmS1QuadraticTerm_add_moments
      H.toEhmPointwiseKernelPackage N,
    gramLinearCorrection_eq_ehmL]
  unfold ehmS1MomentCorrection
  simp only [EhmS1PointwiseKernelPackage.toEhmPointwiseKernelPackage]
  ring

/-- Fully expanded `S₁` target: the signed off-diagonal kernel remains
coupled with its explicit diagonal mass and the one-variable moment
correction. -/
theorem coupledGcdRatioExpression_eq_ehmS1OffDiagonal_add_diagonal_add_correction
    (H : EhmS1PointwiseKernelPackage) (N : ℕ) :
    coupledGcdRatioExpression N =
      ehmS1OffDiagonalTerm H.S1 N +
        (baezDuarteGramEntry 1 1 - ehmK) * logTaperDiagonalMass N +
          ehmS1MomentCorrection N := by
  rw [coupledGcdRatioExpression_eq_ehmS1QuadraticTerm_add_momentCorrection H,
    ehmS1QuadraticTerm_eq_diagonal_add_offDiagonal,
    ehmS1DiagonalTerm_eq_g11_sub_ehmK_mul_mass H]
  ring

/-- Symmetric-kernel form of the exact remaining H15 target.  The two
orientations `S1(n/m)` and `S1(m/n)` are averaged before any estimate is
made, so the signed Möbius coupling is preserved. -/
theorem coupledGcdRatioExpression_eq_ehmS1Symmetrized_add_diagonal_add_correction
    (H : EhmS1PointwiseKernelPackage) (N : ℕ) :
    coupledGcdRatioExpression N =
      ehmS1SymmetrizedOffDiagonalSum H.S1 N +
        (baezDuarteGramEntry 1 1 - ehmK) * logTaperDiagonalMass N +
          ehmS1MomentCorrection N := by
  rw [coupledGcdRatioExpression_eq_ehmS1OffDiagonal_add_diagonal_add_correction H,
    ehmS1OffDiagonalTerm_eq_offDiagonalSum,
    ehmS1OffDiagonalSum_eq_symmetrized]

/-- The symmetric Ehm decomposition with no remaining pointwise-kernel
hypothesis: the kernel is the proved autocorrelation realization. -/
theorem coupledGcdRatioExpression_eq_ehmAutocorrelationSymmetrized
    (N : ℕ) :
    coupledGcdRatioExpression N =
      ehmS1SymmetrizedOffDiagonalSum ehmS1Autocorrelation N +
        (baezDuarteGramEntry 1 1 - ehmK) * logTaperDiagonalMass N +
          ehmS1MomentCorrection N :=
  coupledGcdRatioExpression_eq_ehmS1Symmetrized_add_diagonal_add_correction
    ehmS1PointwiseKernelPackageProved N

/-- Final one-sided upper-triangle form of the exact H15 expression.  This
is the strongest algebraic reduction supplied by reciprocity; it does not
assert decay of the signed sum. -/
theorem coupledGcdRatioExpression_eq_ehmS1OneSidedUpperTriangle
    (N : ℕ) :
    coupledGcdRatioExpression N =
      ehmS1OneSidedUpperTriangleSum N +
        (baezDuarteGramEntry 1 1 - ehmK) * logTaperDiagonalMass N +
          ehmS1MomentCorrection N := by
  rw [coupledGcdRatioExpression_eq_ehmAutocorrelationSymmetrized,
    ehmS1SymmetrizedOffDiagonalSum_eq_symmetricKernelSum,
    ehmS1SymmetricKernelOffDiagonalSum_eq_upperTriangleSum,
    ehmS1UpperTriangleSum_eq_oneSided]

/-- Balanced/far ratio decomposition of the complete H15 expression.  No
absolute values are introduced, so cancellation between the sectors and
the diagonal/moment completion remains available. -/
theorem coupledGcdRatioExpression_eq_ehmS1Balanced_add_far_add_completion
    (N : ℕ) :
    coupledGcdRatioExpression N =
      ehmS1OneSidedBalancedRatioSum N +
        ehmS1OneSidedFarRatioSum N +
        (baezDuarteGramEntry 1 1 - ehmK) * logTaperDiagonalMass N +
          ehmS1MomentCorrection N := by
  rw [coupledGcdRatioExpression_eq_ehmS1OneSidedUpperTriangle,
    ehmS1OneSidedUpperTriangleSum_eq_balanced_add_far]

/-- The balanced-ratio contribution together with the diagonal and moment
completion.  This grouping is diagnostic rather than an assertion that the
far-ratio sum is separately negligible. -/
noncomputable def ehmS1BalancedCoupledCore (N : ℕ) : ℝ :=
  ehmS1OneSidedBalancedRatioSum N +
    (baezDuarteGramEntry 1 1 - ehmK) * logTaperDiagonalMass N +
      ehmS1MomentCorrection N

/-- Exact two-piece research target: a completed balanced core plus the full
reciprocity-completed far-ratio sum.  Cancellation between these pieces is
still allowed and may be essential. -/
theorem coupledGcdRatioExpression_eq_ehmS1BalancedCore_add_far (N : ℕ) :
    coupledGcdRatioExpression N =
      ehmS1BalancedCoupledCore N + ehmS1OneSidedFarRatioSum N := by
  rw [coupledGcdRatioExpression_eq_ehmS1Balanced_add_far_add_completion]
  unfold ehmS1BalancedCoupledCore
  ring

/-- Ehm's exact expression for the compensator itself.  It must approximate
the negative square-Möbius diagonal mass if H15 is to hold. -/
theorem compensatingCorrelation_eq_ehmS1QuadraticTerm_add_correction_sub_diagonal
    (H : EhmS1PointwiseKernelPackage) (N : ℕ) :
    compensatingCorrelation N =
      ehmS1QuadraticTerm H.S1 N + ehmS1MomentCorrection N -
        baezDuarteGramEntry 1 1 * logTaperDiagonalMass N := by
  calc
    compensatingCorrelation N =
        coupledGcdRatioExpression N - gramDiagonal N := by
      rw [coupledGcdRatioExpression_eq_diagonal_add_compensatingCorrelation]
      ring
    _ = _ := by
      rw [coupledGcdRatioExpression_eq_ehmS1QuadraticTerm_add_momentCorrection H,
        gramDiagonal_eq_g11_mul_logTaperDiagonalMass]

/-- Pointwise-Ehm form of the exact H15 bound.  The `S₁` bilinear term and
the moment correction stay inside one absolute value. -/
theorem coupledLogTaper_bound_iff_ehmS1Coupled_bound
    (H : EhmS1PointwiseKernelPackage) (C α : ℝ) (N : ℕ) :
    |coupledGcdRatioExpression N| ≤ C / (Real.log (N : ℝ)) ^ α ↔
      |ehmS1QuadraticTerm H.S1 N + ehmS1MomentCorrection N| ≤
        C / (Real.log (N : ℝ)) ^ α := by
  rw [coupledGcdRatioExpression_eq_ehmS1QuadraticTerm_add_momentCorrection H]

/-- The open research estimate in the direct `S₁` variables.  Constructing
this package is exactly as strong as supplying the original coupled H15
estimate after the pointwise Ehm kernel package is available. -/
structure EhmS1CoupledCancellationEstimate (H : EhmS1PointwiseKernelPackage) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ N : ℕ, 2 ≤ N →
    |ehmS1QuadraticTerm H.S1 N + ehmS1MomentCorrection N| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- The same open estimate written with the exact symmetric off-diagonal
kernel, its explicit positive diagonal, and the finite moment correction.
This is the preferred interface for analytic work on the final gap. -/
structure EhmS1SymmetrizedCoupledCancellationEstimate
    (H : EhmS1PointwiseKernelPackage) where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ N : ℕ, 2 ≤ N →
    |ehmS1SymmetrizedOffDiagonalSum H.S1 N +
        (baezDuarteGramEntry 1 1 - ehmK) * logTaperDiagonalMass N +
          ehmS1MomentCorrection N| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- A symmetric off-diagonal estimate is exactly sufficient for the direct
`S1` cancellation interface. -/
def EhmS1SymmetrizedCoupledCancellationEstimate.toEhmS1Coupled
    (H : EhmS1PointwiseKernelPackage)
    (HE : EhmS1SymmetrizedCoupledCancellationEstimate H) :
    EhmS1CoupledCancellationEstimate H where
  C := HE.C
  C_pos := HE.C_pos
  α := HE.α
  α_pos := HE.α_pos
  bound N hN := by
    rw [← coupledLogTaper_bound_iff_ehmS1Coupled_bound H HE.C HE.α N,
      coupledGcdRatioExpression_eq_ehmS1Symmetrized_add_diagonal_add_correction H]
    exact HE.bound N hN

/-- The sole remaining Ehm-route hypothesis after the pointwise package has
been discharged by the autocorrelation construction. -/
abbrev EhmAutocorrelationCoupledCancellationEstimate :=
  EhmS1SymmetrizedCoupledCancellationEstimate
    ehmS1PointwiseKernelPackageProved

/-- The genuinely open signed estimate in the one-sided upper-triangle
variables exposed by Ehm reciprocity. -/
structure EhmS1OneSidedCoupledCancellationEstimate where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ N : ℕ, 2 ≤ N →
    |ehmS1OneSidedUpperTriangleSum N +
        (baezDuarteGramEntry 1 1 - ehmK) * logTaperDiagonalMass N +
          ehmS1MomentCorrection N| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- The weakest ratio-sector formulation of the open estimate.  It controls
the signed sum of the completed balanced core and the far sector; it does not
require either piece to decay on its own. -/
structure EhmS1RatioSectorCoupledCancellationEstimate where
  C : ℝ
  C_pos : 0 < C
  α : ℝ
  α_pos : 0 < α
  bound : ∀ N : ℕ, 2 ≤ N →
    |ehmS1BalancedCoupledCore N + ehmS1OneSidedFarRatioSum N| ≤
      C / (Real.log (N : ℝ)) ^ α

/-- The coupled ratio-sector target is exactly sufficient for the original
project-wide H15 cancellation interface. -/
noncomputable def EhmS1RatioSectorCoupledCancellationEstimate.toCoupled
    (HE : EhmS1RatioSectorCoupledCancellationEstimate) :
    CoupledLogTaperCancellationEstimate where
  C := HE.C
  C_pos := HE.C_pos
  α := HE.α
  α_pos := HE.α_pos
  bound N hN := by
    rw [coupledGcdRatioExpression_eq_ehmS1BalancedCore_add_far]
    exact HE.bound N hN

/-- The upper-triangle estimate is exactly sufficient for the proved
autocorrelation cancellation interface. -/
noncomputable def EhmS1OneSidedCoupledCancellationEstimate.toAutocorrelation
    (HE : EhmS1OneSidedCoupledCancellationEstimate) :
    EhmAutocorrelationCoupledCancellationEstimate where
  C := HE.C
  C_pos := HE.C_pos
  α := HE.α
  α_pos := HE.α_pos
  bound N hN := by
    change |ehmS1SymmetrizedOffDiagonalSum ehmS1Autocorrelation N +
        (baezDuarteGramEntry 1 1 - ehmK) * logTaperDiagonalMass N +
          ehmS1MomentCorrection N| ≤
      HE.C / (Real.log (N : ℝ)) ^ HE.α
    rw [ehmS1SymmetrizedOffDiagonalSum_eq_symmetricKernelSum,
      ehmS1SymmetricKernelOffDiagonalSum_eq_upperTriangleSum,
      ehmS1UpperTriangleSum_eq_oneSided]
    exact HE.bound N hN

/-- An `S₁`-form estimate supplies the project-wide H15 interface, without
introducing separate absolute-value bounds for its two coupled parts. -/
def coupledLogTaperCancellation_of_ehmS1
    (H : EhmS1PointwiseKernelPackage)
    (HE : EhmS1CoupledCancellationEstimate H) :
    CoupledLogTaperCancellationEstimate where
  C := HE.C
  C_pos := HE.C_pos
  α := HE.α
  α_pos := HE.α_pos
  bound N hN :=
    (coupledLogTaper_bound_iff_ehmS1Coupled_bound H HE.C HE.α N).mpr
      (HE.bound N hN)

/-- The proved autocorrelation reduction turns a bound for the single
remaining signed expression into the project-wide H15 estimate. -/
noncomputable def coupledLogTaperCancellation_of_ehmAutocorrelation
    (HE : EhmAutocorrelationCoupledCancellationEstimate) :
    CoupledLogTaperCancellationEstimate :=
  coupledLogTaperCancellation_of_ehmS1 ehmS1PointwiseKernelPackageProved
    HE.toEhmS1Coupled

/-- A proof of the one-sided signed estimate closes the project-wide H15
cancellation interface. -/
noncomputable def coupledLogTaperCancellation_of_ehmS1OneSided
    (HE : EhmS1OneSidedCoupledCancellationEstimate) :
    CoupledLogTaperCancellationEstimate :=
  coupledLogTaperCancellation_of_ehmAutocorrelation HE.toAutocorrelation

end RH.Criteria.NymanBeurling.BCFLogTaperEhmCompensator
