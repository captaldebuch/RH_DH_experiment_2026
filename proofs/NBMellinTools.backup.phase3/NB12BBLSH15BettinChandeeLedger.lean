/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15FrequencyIntegral

/-!
# NB12za: exact dyadic Bettin--Chandee ledger for the H15 high tail

This file performs the finite arithmetic bookkeeping which comes after the
global high-frequency sum--integral exchange.  It has four purposes.

* Both H15 orientations are written with a common inverse variable and a
  common modulus variable.
* The finite row family and every finite frequency truncation are reassembled
  exactly into dyadic fibers.
* The three separated squared coefficient masses are recorded as an exact
  tensor-product identity.
* The factor `(1 + |theta| A/(MN))^(1/2)` in Bettin--Chandee Theorem 1 is
  included in the exponent audit.  It does not change the lower threshold
  `R > N^(3/4+eta)`, but it removes all frequency decay from the theorem's
  second term once `R >= N^2`.  Consequently the published estimate cannot
  be summed over the entire infinite high tail without a second, ultra-high
  tail argument.

No Bettin--Chandee estimate is postulated here, and no asymptotic H15 decay is
claimed.
-/

open scoped BigOperators Topology LSeries.notation Interval
open Complex Filter MeasureTheory LSeries

namespace NBMellinTools.NB12

open NBMellinTools.NB8

/-! ## Orientation-independent H15 variables -/

/-- Primitive variable which is inverted in the Kloosterman fraction. -/
def h15BettinChandeeInverseVariable {N : ℕ}
    (i : H15LaurentRowIndex N) : ℕ :=
  if h15LaurentOrientation i = 0 then h15LaurentA i else h15LaurentQ i

/-- Primitive modulus in the Kloosterman fraction. -/
def h15BettinChandeeModulusVariable {N : ℕ}
    (i : H15LaurentRowIndex N) : ℕ :=
  if h15LaurentOrientation i = 0 then h15LaurentQ i else h15LaurentA i

theorem h15LaurentOrientation_eq_zero_or_one {N : ℕ}
    (i : H15LaurentRowIndex N) :
    h15LaurentOrientation i = 0 ∨ h15LaurentOrientation i = 1 := by
  have hlt : h15LaurentOrientation i < 2 := i.2.2.2.isLt
  omega

theorem h15BettinChandeeInverseVariable_pos {N : ℕ}
    (i : H15LaurentRowIndex N) :
    0 < h15BettinChandeeInverseVariable i := by
  rcases h15LaurentOrientation_eq_zero_or_one i with h | h <;>
    simp [h15BettinChandeeInverseVariable, h, h15LaurentA, h15LaurentQ]

theorem h15BettinChandeeModulusVariable_pos {N : ℕ}
    (i : H15LaurentRowIndex N) :
    0 < h15BettinChandeeModulusVariable i := by
  rcases h15LaurentOrientation_eq_zero_or_one i with h | h <;>
    simp [h15BettinChandeeModulusVariable, h, h15LaurentA, h15LaurentQ]

/-- On every genuine H15 row, the denominator of the reduced Estermann row
is exactly the orientation-independent modulus variable. -/
theorem h15LaurentRow_denominator_eq_bettinChandeeModulus
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i) :
    (h15LaurentRow i).denominator =
      h15BettinChandeeModulusVariable i := by
  rcases h15LaurentOrientation_eq_zero_or_one i with h | h
  · simpa [h15BettinChandeeModulusVariable, h] using
      h15LaurentRow_denominator_eq_q_of_orientation_zero i hvalid h
  · have hne : h15LaurentOrientation i ≠ 0 := by omega
    have hcop : Nat.Coprime (h15LaurentQ i) (h15LaurentA i) :=
      hvalid.2.2.2.2.symm
    simp [h15LaurentRow_denominator, h15LaurentReducedDenominator,
      h15BettinChandeeModulusVariable, hne, hcop.gcd_eq_one]

/-- The coefficient on the inverted primitive variable. -/
noncomputable def h15BettinChandeeInverseCoefficient
    (N g a : ℕ) : ℝ :=
  h15NaturalLogTaperCoeff N (g * a) / (a : ℝ)

/-- The coefficient on the primitive modulus after the functional equation
has supplied its modulus square. -/
noncomputable def h15BettinChandeeModulusCoefficient
    (N g q : ℕ) : ℝ :=
  h15NaturalLogTaperCoeff N (g * q) * (q : ℝ)

/-- Both H15 orientations have the same separated coefficient formula. -/
theorem h15LaurentRowWeight_mul_denominator_sq_factorization_both
    {N : ℕ} (i : H15LaurentRowIndex N)
    (hvalid : h15LaurentRowValid i) :
    h15LaurentRowWeight i *
        ((h15LaurentRow i).denominator : ℂ) ^ 2 =
      (((Real.pi / (h15LaurentG i : ℝ)) *
        h15BettinChandeeInverseCoefficient N (h15LaurentG i)
          (h15BettinChandeeInverseVariable i) *
        h15BettinChandeeModulusCoefficient N (h15LaurentG i)
          (h15BettinChandeeModulusVariable i) : ℝ) : ℂ) := by
  rcases h15LaurentOrientation_eq_zero_or_one i with h | h
  · simpa [h15BettinChandeeInverseVariable,
      h15BettinChandeeModulusVariable,
      h15BettinChandeeInverseCoefficient,
      h15BettinChandeeModulusCoefficient, h] using
        h15LaurentRowWeight_mul_denominator_sq_factorization
          i hvalid h
  · have hne : h15LaurentOrientation i ≠ 0 := by omega
    rw [h15LaurentRow_denominator_eq_bettinChandeeModulus i hvalid]
    simp only [h15LaurentRowWeight, if_pos hvalid]
    simp [h15BettinChandeeInverseVariable,
      h15BettinChandeeModulusVariable,
      h15BettinChandeeInverseCoefficient,
      h15BettinChandeeModulusCoefficient, hne]
    have hg : ((h15LaurentG i : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by simp [h15LaurentG] : h15LaurentG i ≠ 0)
    have ha : ((h15LaurentA i : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by simp [h15LaurentA] : h15LaurentA i ≠ 0)
    have hq : ((h15LaurentQ i : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by simp [h15LaurentQ] : h15LaurentQ i ≠ 0)
    field_simp [hg, ha, hq]

/-! ## Exact finite dyadic reassembly -/

/-- Five coordinates of one Bettin--Chandee block: gcd slice, inverse
variable scale, modulus scale, frequency scale, and orientation. -/
structure H15BettinChandeeDyadicKey where
  gcdSlice : ℕ
  inverseScale : ℕ
  modulusScale : ℕ
  frequencyScale : ℕ
  orientation : ℕ
  deriving DecidableEq

def h15BettinChandeeDyadicKeyOf
    {N : ℕ} (i : H15LaurentRowIndex N) (r : ℕ) :
    H15BettinChandeeDyadicKey where
  gcdSlice := h15LaurentG i
  inverseScale := Nat.log2 (h15BettinChandeeInverseVariable i)
  modulusScale := Nat.log2 (h15BettinChandeeModulusVariable i)
  frequencyScale := Nat.log2 r
  orientation := h15LaurentOrientation i

/-- Finite row--frequency box used before passing to the already justified
infinite high-frequency limit. -/
def h15BettinChandeeFiniteBox (N K J : ℕ) :
    Finset (H15LaurentRowIndex N × ℕ) :=
  (Finset.univ : Finset (H15LaurentRowIndex N)).product
    (Finset.Ico (K + 1) (K + 1 + J))

def h15BettinChandeeDyadicKeys (N K J : ℕ) :
    Finset H15BettinChandeeDyadicKey :=
  (h15BettinChandeeFiniteBox N K J).image
    (fun ir => h15BettinChandeeDyadicKeyOf ir.1 ir.2)

def h15BettinChandeeDyadicBlock
    (N K J : ℕ) (key : H15BettinChandeeDyadicKey) :
    Finset (H15LaurentRowIndex N × ℕ) :=
  (h15BettinChandeeFiniteBox N K J).filter
    (fun ir => h15BettinChandeeDyadicKeyOf ir.1 ir.2 = key)

theorem mem_h15BettinChandeeDyadicBlock
    {N K J : ℕ} {key : H15BettinChandeeDyadicKey}
    {ir : H15LaurentRowIndex N × ℕ} :
    ir ∈ h15BettinChandeeDyadicBlock N K J key ↔
      ir ∈ h15BettinChandeeFiniteBox N K J ∧
        h15BettinChandeeDyadicKeyOf ir.1 ir.2 = key := by
  simp [h15BettinChandeeDyadicBlock]

/-- Dyadic membership gives all five exact coordinates and the usual
half-open support inequalities. -/
theorem support_of_mem_h15BettinChandeeDyadicBlock
    {N K J : ℕ} {key : H15BettinChandeeDyadicKey}
    {ir : H15LaurentRowIndex N × ℕ}
    (hir : ir ∈ h15BettinChandeeDyadicBlock N K J key) :
    h15LaurentG ir.1 = key.gcdSlice ∧
      h15LaurentOrientation ir.1 = key.orientation ∧
      2 ^ key.inverseScale ≤ h15BettinChandeeInverseVariable ir.1 ∧
      h15BettinChandeeInverseVariable ir.1 < 2 ^ (key.inverseScale + 1) ∧
      2 ^ key.modulusScale ≤ h15BettinChandeeModulusVariable ir.1 ∧
      h15BettinChandeeModulusVariable ir.1 < 2 ^ (key.modulusScale + 1) ∧
      2 ^ key.frequencyScale ≤ ir.2 ∧
      ir.2 < 2 ^ (key.frequencyScale + 1) := by
  have hkey := (mem_h15BettinChandeeDyadicBlock.mp hir).2
  have hg := congrArg H15BettinChandeeDyadicKey.gcdSlice hkey
  have hi := congrArg H15BettinChandeeDyadicKey.inverseScale hkey
  have hq := congrArg H15BettinChandeeDyadicKey.modulusScale hkey
  have hr := congrArg H15BettinChandeeDyadicKey.frequencyScale hkey
  have ho := congrArg H15BettinChandeeDyadicKey.orientation hkey
  have hai0 : h15BettinChandeeInverseVariable ir.1 ≠ 0 :=
    (h15BettinChandeeInverseVariable_pos ir.1).ne'
  have hqi0 : h15BettinChandeeModulusVariable ir.1 ≠ 0 :=
    (h15BettinChandeeModulusVariable_pos ir.1).ne'
  have hirange := (mem_h15BettinChandeeDyadicBlock.mp hir).1
  have hrmem : ir.2 ∈ Finset.Ico (K + 1) (K + 1 + J) := by
    simpa [h15BettinChandeeFiniteBox] using hirange
  have hri0 : ir.2 ≠ 0 := by
    have := (Finset.mem_Ico.mp hrmem).1
    omega
  constructor
  · simpa [h15BettinChandeeDyadicKeyOf] using hg
  constructor
  · simpa [h15BettinChandeeDyadicKeyOf] using ho
  constructor
  · rw [← hi]
    exact Nat.log2_self_le hai0
  constructor
  · rw [← hi]
    exact Nat.lt_log2_self
  constructor
  · rw [← hq]
    exact Nat.log2_self_le hqi0
  constructor
  · rw [← hq]
    exact Nat.lt_log2_self
  constructor
  · rw [← hr]
    exact Nat.log2_self_le hri0
  · rw [← hr]
    exact Nat.lt_log2_self

/-- The dyadic fibers reassemble every finite row--frequency sum exactly. -/
theorem sum_h15BettinChandeeDyadicBlocks
    {R : Type*} [AddCommMonoid R]
    (N K J : ℕ) (f : H15LaurentRowIndex N × ℕ → R) :
    (∑ key ∈ h15BettinChandeeDyadicKeys N K J,
      ∑ ir ∈ h15BettinChandeeDyadicBlock N K J key, f ir) =
        ∑ ir ∈ h15BettinChandeeFiniteBox N K J, f ir := by
  classical
  unfold h15BettinChandeeDyadicKeys h15BettinChandeeDyadicBlock
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · ext ir
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · exact fun h => h.1
    · intro hir
      exact ⟨hir, ir, hir, rfl⟩
  · intro ir _
    rfl

/-! ## The actual finite integrated H15 blocks -/

noncomputable def h15BettinChandeeIntegratedSummand
    (n : ℕ) (T : ℝ)
    (ir : H15LaurentRowIndex (logTaperLength n) × ℕ) : ℂ :=
  h15LaurentRowWeight ir.1 *
    ∫ t : ℝ in -T..T,
      bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
        (h15LaurentRow ir.1).numerator
        (h15LaurentRow ir.1).denominator
        (h15LaurentRow ir.1).coprime ir.2 t

noncomputable def h15BettinChandeeIntegratedDyadicBlock
    (n K J : ℕ) (T : ℝ) (key : H15BettinChandeeDyadicKey) : ℂ :=
  ∑ ir ∈ h15BettinChandeeDyadicBlock (logTaperLength n) K J key,
    h15BettinChandeeIntegratedSummand n T ir

/-- Finite frequency truncation of the exchanged high remainder. -/
noncomputable def h15BettinChandeeFiniteIntegratedHigh
    (n K J : ℕ) (T : ℝ) : ℂ :=
  ∑ ir ∈ h15BettinChandeeFiniteBox (logTaperLength n) K J,
    h15BettinChandeeIntegratedSummand n T ir

theorem h15BettinChandeeFiniteIntegratedHigh_eq_row_sum
    (n K J : ℕ) (T : ℝ) :
    h15BettinChandeeFiniteIntegratedHigh n K J T =
      ∑ i : H15LaurentRowIndex (logTaperLength n),
        h15LaurentRowWeight i *
          ∑ j ∈ Finset.range J,
            ∫ t : ℝ in -T..T,
              bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
                (h15LaurentRow i).numerator
                (h15LaurentRow i).denominator
                (h15LaurentRow i).coprime (j + (K + 1)) t := by
  unfold h15BettinChandeeFiniteIntegratedHigh
    h15BettinChandeeFiniteBox h15BettinChandeeIntegratedSummand
  calc
    (∑ ir ∈
        (Finset.univ : Finset
          (H15LaurentRowIndex (logTaperLength n))).product
            (Finset.Ico (K + 1) (K + 1 + J)),
        h15LaurentRowWeight ir.1 *
          ∫ t : ℝ in -T..T,
            bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
              (h15LaurentRow ir.1).numerator
              (h15LaurentRow ir.1).denominator
              (h15LaurentRow ir.1).coprime ir.2 t) =
      ∑ i : H15LaurentRowIndex (logTaperLength n),
        ∑ r ∈ Finset.Ico (K + 1) (K + 1 + J),
          h15LaurentRowWeight i *
            ∫ t : ℝ in -T..T,
              bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
                (h15LaurentRow i).numerator
                (h15LaurentRow i).denominator
                (h15LaurentRow i).coprime r t := by
          exact Finset.sum_product
            (Finset.univ : Finset
              (H15LaurentRowIndex (logTaperLength n)))
            (Finset.Ico (K + 1) (K + 1 + J)) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Nat.add_comm]

/-- Exact dyadic reassembly of every finite truncation of the genuine
integrated high-frequency H15 sum. -/
theorem sum_h15BettinChandeeIntegratedDyadicBlocks
    (n K J : ℕ) (T : ℝ) :
    (∑ key ∈ h15BettinChandeeDyadicKeys (logTaperLength n) K J,
      h15BettinChandeeIntegratedDyadicBlock n K J T key) =
        h15BettinChandeeFiniteIntegratedHigh n K J T := by
  exact sum_h15BettinChandeeDyadicBlocks
    (logTaperLength n) K J (h15BettinChandeeIntegratedSummand n T)

/-- The interval integrals of the shifted row frequencies form an absolutely
summable complex series. -/
theorem summable_intervalIntegral_bblsActiveThreeHalfFrequencyTerm
    (n : ℕ) (i : H15LaurentRowIndex (logTaperLength n))
    (K : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    Summable (fun j : ℕ =>
      ∫ t : ℝ in -T..T,
        bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
          (h15LaurentRow i).numerator
          (h15LaurentRow i).denominator
          (h15LaurentRow i).coprime (j + (K + 1)) t) := by
  let f : ℕ → ℝ → ℂ := fun j t =>
    bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
      (h15LaurentRow i).numerator
      (h15LaurentRow i).denominator
      (h15LaurentRow i).coprime (j + (K + 1)) t
  have hglobal : Summable (fun j : ℕ => ∫ t : ℝ, ‖f j t‖) :=
    summable_integral_norm_bblsActiveThreeHalfFrequencyTerm
      (h15ContourDamping_pos n)
      (h15LaurentRow i).numerator
      (h15LaurentRow i).denominator
      (h15LaurentRow i).coprime K
  have hnorm : Summable (fun j : ℕ => ‖∫ t : ℝ in -T..T, f j t‖) := by
    apply hglobal.of_nonneg_of_le
    · intro j
      exact norm_nonneg _
    · intro j
      have hf : Integrable (f j) :=
        integrable_bblsActiveThreeHalfFrequencyTerm
          (h15ContourDamping_pos n)
          (h15LaurentRow i).numerator
          (h15LaurentRow i).denominator
          (h15LaurentRow i).coprime (j + (K + 1))
      calc
        ‖∫ t : ℝ in -T..T, f j t‖ ≤
            ∫ t : ℝ in -T..T, ‖f j t‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ = ∫ t : ℝ, ‖f j t‖ ∂(volume.restrict (Set.Ioc (-T) T)) := by
          rw [intervalIntegral.integral_of_le (by linarith)]
        _ ≤ ∫ t : ℝ, ‖f j t‖ :=
          integral_mono_measure Measure.restrict_le_self
            (Filter.Eventually.of_forall fun _ => norm_nonneg _) hf.norm
  rw [← summable_norm_iff]
  simpa only [f] using hnorm

/-- The exact finite dyadic truncations converge to the genuine exchanged
high remainder.  Thus the dyadic ledger is attached to the actual infinite
H15 tail, not to a separate model sum. -/
theorem tendsto_h15BettinChandeeFiniteIntegratedHigh
    (n K : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun J : ℕ => h15BettinChandeeFiniteIntegratedHigh n K J T)
      atTop (nhds (h15ThreeHalfHighFrequencyIntegralRemainder n K T)) := by
  rw [show (fun J : ℕ => h15BettinChandeeFiniteIntegratedHigh n K J T) =
      fun J : ℕ =>
        ∑ i : H15LaurentRowIndex (logTaperLength n),
          h15LaurentRowWeight i *
            ∑ j ∈ Finset.range J,
              ∫ t : ℝ in -T..T,
                bblsActiveThreeHalfFrequencyTerm (h15ContourDamping n)
                  (h15LaurentRow i).numerator
                  (h15LaurentRow i).denominator
                  (h15LaurentRow i).coprime (j + (K + 1)) t by
        funext J
        exact h15BettinChandeeFiniteIntegratedHigh_eq_row_sum n K J T]
  rw [h15ThreeHalfHighFrequencyIntegralRemainder_eq_sum_tsum n K T hT]
  apply tendsto_finsetSum
  intro i _
  exact tendsto_const_nhds.mul
    (summable_intervalIntegral_bblsActiveThreeHalfFrequencyTerm
      n i K T hT).hasSum.tendsto_sum_nat

/-! ## Exact separated squared-mass ledger -/

def h15BettinChandeeNatBlock (X : ℕ) : Finset ℕ :=
  Finset.Ico X (2 * X)

/-- The actual H15 coefficient support inside one dyadic primitive block. -/
def h15BettinChandeeSupportedNatBlock (N g X : ℕ) : Finset ℕ :=
  (h15BettinChandeeNatBlock X).filter (fun x => g * x ≤ N)

theorem mem_h15BettinChandeeSupportedNatBlock
    {N g X x : ℕ} :
    x ∈ h15BettinChandeeSupportedNatBlock N g X ↔
      X ≤ x ∧ x < 2 * X ∧ g * x ≤ N := by
  simp [h15BettinChandeeSupportedNatBlock,
    h15BettinChandeeNatBlock, and_assoc]

/-- On its genuine cutoff support, the Möbius logarithmic taper has modulus
at most one. -/
theorem abs_h15NaturalLogTaperCoeff_le_one
    {N m : ℕ} (hN : 2 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N) :
    |h15NaturalLogTaperCoeff N m| ≤ 1 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hratioOne : (1 : ℝ) ≤ (N : ℝ) / (m : ℝ) :=
    (le_div_iff₀ hmpos).2 (by
      have hmN' : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
      simpa using hmN')
  have hratioPos : 0 < (N : ℝ) / (m : ℝ) := div_pos hNpos hmpos
  have hratioN : (N : ℝ) / (m : ℝ) ≤ (N : ℝ) := by
    apply (div_le_iff₀ hmpos).2
    have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hlogRatioNonneg :
      0 ≤ Real.log ((N : ℝ) / (m : ℝ)) := Real.log_nonneg hratioOne
  have hlogRatioLe :
      Real.log ((N : ℝ) / (m : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hratioPos hratioN
  have htaperNonneg :
      0 ≤ Real.log ((N : ℝ) / (m : ℝ)) / Real.log (N : ℝ) :=
    div_nonneg hlogRatioNonneg hlogN.le
  have htaperLe :
      Real.log ((N : ℝ) / (m : ℝ)) / Real.log (N : ℝ) ≤ 1 :=
    (div_le_one hlogN).2 hlogRatioLe
  have hmu : |(((ArithmeticFunction.moebius m : ℤ) : ℝ))| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
  unfold h15NaturalLogTaperCoeff
  rw [abs_mul, abs_neg, abs_of_nonneg htaperNonneg]
  calc
    |(((ArithmeticFunction.moebius m : ℤ) : ℝ))| *
        (Real.log ((N : ℝ) / (m : ℝ)) / Real.log (N : ℝ)) ≤
      1 * (Real.log ((N : ℝ) / (m : ℝ)) / Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hmu htaperNonneg
    _ ≤ 1 := by simpa using htaperLe

theorem card_h15BettinChandeeSupportedNatBlock_le
    (N g X : ℕ) :
    (h15BettinChandeeSupportedNatBlock N g X).card ≤ X := by
  calc
    (h15BettinChandeeSupportedNatBlock N g X).card ≤
        (h15BettinChandeeNatBlock X).card := by
      unfold h15BettinChandeeSupportedNatBlock
      exact Finset.card_filter_le _ _
    _ = X := by
      simp [h15BettinChandeeNatBlock]
      omega

theorem abs_h15BettinChandeeInverseCoefficient_le
    {N g A a : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hA : 0 < A)
    (ha : a ∈ h15BettinChandeeSupportedNatBlock N g A) :
    |h15BettinChandeeInverseCoefficient N g a| ≤ 1 / (A : ℝ) := by
  have hmem := mem_h15BettinChandeeSupportedNatBlock.mp ha
  have haPos : 0 < a := hA.trans_le hmem.1
  have hgaPos : 1 ≤ g * a := Nat.mul_pos hg haPos
  have htaper := abs_h15NaturalLogTaperCoeff_le_one hN hgaPos hmem.2.2
  unfold h15BettinChandeeInverseCoefficient
  rw [abs_div]
  have haCast : |(a : ℝ)| = (a : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg a)
  rw [haCast]
  calc
    |h15NaturalLogTaperCoeff N (g * a)| / (a : ℝ) ≤
        1 / (a : ℝ) :=
      div_le_div_of_nonneg_right htaper (by positivity)
    _ ≤ 1 / (A : ℝ) := by
      exact one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast hmem.1)

theorem abs_h15BettinChandeeModulusCoefficient_le
    {N g Q q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hq : q ∈ h15BettinChandeeSupportedNatBlock N g Q) :
    |h15BettinChandeeModulusCoefficient N g q| ≤ 2 * (Q : ℝ) := by
  have hmem := mem_h15BettinChandeeSupportedNatBlock.mp hq
  have hqPos : 0 < q := by
    have hQq := hmem.1
    have hqUpper := hmem.2.1
    omega
  have hgqPos : 1 ≤ g * q := Nat.mul_pos hg hqPos
  have htaper := abs_h15NaturalLogTaperCoeff_le_one hN hgqPos hmem.2.2
  unfold h15BettinChandeeModulusCoefficient
  rw [abs_mul]
  have hqCast : |(q : ℝ)| = (q : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg q)
  rw [hqCast]
  calc
    |h15NaturalLogTaperCoeff N (g * q)| * (q : ℝ) ≤
        1 * (q : ℝ) :=
      mul_le_mul_of_nonneg_right htaper (by positivity)
    _ ≤ 2 * (Q : ℝ) := by
      have hqle : (q : ℝ) ≤ 2 * (Q : ℝ) := by
        exact_mod_cast hmem.2.1.le
      simpa using hqle

noncomputable def h15BettinChandeeInverseMass
    (N g A : ℕ) : ℝ :=
  ∑ a ∈ h15BettinChandeeSupportedNatBlock N g A,
    h15BettinChandeeInverseCoefficient N g a ^ 2

noncomputable def h15BettinChandeeModulusMass
    (N g Q : ℕ) : ℝ :=
  ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
    h15BettinChandeeModulusCoefficient N g q ^ 2

/-- Exact elementary `L²` budget for the inverse-variable coefficient. -/
theorem h15BettinChandeeInverseMass_le
    {N g A : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) (hA : 0 < A) :
    h15BettinChandeeInverseMass N g A ≤ 1 / (A : ℝ) := by
  unfold h15BettinChandeeInverseMass
  calc
    (∑ a ∈ h15BettinChandeeSupportedNatBlock N g A,
        h15BettinChandeeInverseCoefficient N g a ^ 2) ≤
      ∑ _a ∈ h15BettinChandeeSupportedNatBlock N g A,
        (1 / (A : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (abs_h15BettinChandeeInverseCoefficient_le hN hg hA ha) 2
    _ = ((h15BettinChandeeSupportedNatBlock N g A).card : ℝ) *
        (1 / (A : ℝ)) ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A : ℝ) * (1 / (A : ℝ)) ^ 2 := by
      gcongr
      exact_mod_cast card_h15BettinChandeeSupportedNatBlock_le N g A
    _ = 1 / (A : ℝ) := by
      have hA0 : (A : ℝ) ≠ 0 := by positivity
      field_simp

/-- Exact elementary `L²` budget for the modulus coefficient. -/
theorem h15BettinChandeeModulusMass_le
    {N g Q : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g) :
    h15BettinChandeeModulusMass N g Q ≤ 4 * (Q : ℝ) ^ 3 := by
  unfold h15BettinChandeeModulusMass
  calc
    (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        h15BettinChandeeModulusCoefficient N g q ^ 2) ≤
      ∑ _q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        (2 * (Q : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (abs_h15BettinChandeeModulusCoefficient_le hN hg hq) 2
    _ = ((h15BettinChandeeSupportedNatBlock N g Q).card : ℝ) *
        (2 * (Q : ℝ)) ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * (2 * (Q : ℝ)) ^ 2 := by
      gcongr
      exact_mod_cast card_h15BettinChandeeSupportedNatBlock_le N g Q
    _ = 4 * (Q : ℝ) ^ 3 := by ring

noncomputable def h15BettinChandeeFrequencyCoefficient (r : ℕ) : ℝ :=
  ‖LSeries.term bblsEstermannDivisorCoeff (3 / 2 : ℂ) r‖

/-- The separated frequency coefficient is exactly the normalized divisor
coefficient `d(r)/r^(3/2)`. -/
theorem h15BettinChandeeFrequencyCoefficient_eq
    {r : ℕ} (hr : 0 < r) :
    h15BettinChandeeFrequencyCoefficient r =
      (r.divisors.card : ℝ) / (r : ℝ) ^ (3 / 2 : ℝ) := by
  unfold h15BettinChandeeFrequencyCoefficient
  rw [LSeries.norm_term_eq]
  simp [hr.ne', bblsEstermannDivisorCoeff_apply]

noncomputable def h15BettinChandeeFrequencyMass (R : ℕ) : ℝ :=
  ∑ r ∈ h15BettinChandeeNatBlock R,
    h15BettinChandeeFrequencyCoefficient r ^ 2

/-- On a positive dyadic block the exact frequency squared mass is the
classical divisor-square sum with denominator `r^3`. -/
theorem h15BettinChandeeFrequencyMass_eq_divisorSquare
    (R : ℕ) :
    h15BettinChandeeFrequencyMass R =
      ∑ r ∈ h15BettinChandeeNatBlock R,
        ((r.divisors.card : ℝ) / (r : ℝ) ^ (3 / 2 : ℝ)) ^ 2 := by
  unfold h15BettinChandeeFrequencyMass
  apply Finset.sum_congr rfl
  intro r hr
  rw [h15BettinChandeeFrequencyCoefficient_eq]
  have hrange := Finset.mem_Ico.mp hr
  omega

/-- Classical divisor-square input in exactly the normalization consumed by
the H15 frequency coefficient.  This is an unconditional analytic-number-
theory estimate, but it is kept as an explicit package until its standard
proof is added to the local Mathlib infrastructure. -/
structure H15DivisorSquareDyadicBound where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound : ∀ R : ℕ, 1 ≤ R →
    h15BettinChandeeFrequencyMass R ≤
      constant * (1 + Real.log (2 * (R : ℝ))) ^ 3 / (R : ℝ) ^ 2

theorem h15BettinChandeeInverseMass_nonneg (N g A : ℕ) :
    0 ≤ h15BettinChandeeInverseMass N g A := by
  unfold h15BettinChandeeInverseMass
  positivity

theorem h15BettinChandeeModulusMass_nonneg (N g Q : ℕ) :
    0 ≤ h15BettinChandeeModulusMass N g Q := by
  unfold h15BettinChandeeModulusMass
  positivity

theorem h15BettinChandeeFrequencyMass_nonneg (R : ℕ) :
    0 ≤ h15BettinChandeeFrequencyMass R := by
  unfold h15BettinChandeeFrequencyMass
  positivity

noncomputable def h15BettinChandeeTensorMass
    (N g A Q R : ℕ) : ℝ :=
  ∑ a ∈ h15BettinChandeeSupportedNatBlock N g A,
    ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
      ∑ r ∈ h15BettinChandeeNatBlock R,
        (h15BettinChandeeInverseCoefficient N g a *
          h15BettinChandeeModulusCoefficient N g q *
          h15BettinChandeeFrequencyCoefficient r) ^ 2

/-- The full three-variable squared coefficient norm is exactly the product
of the three separated squared masses. -/
theorem h15BettinChandeeTensorMass_eq
    (N g A Q R : ℕ) :
    h15BettinChandeeTensorMass N g A Q R =
      h15BettinChandeeInverseMass N g A *
        h15BettinChandeeModulusMass N g Q *
          h15BettinChandeeFrequencyMass R := by
  unfold h15BettinChandeeTensorMass h15BettinChandeeInverseMass
    h15BettinChandeeModulusMass h15BettinChandeeFrequencyMass
  simp_rw [mul_pow]
  calc
    (∑ a ∈ h15BettinChandeeSupportedNatBlock N g A,
      ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
        ∑ r ∈ h15BettinChandeeNatBlock R,
          h15BettinChandeeInverseCoefficient N g a ^ 2 *
            h15BettinChandeeModulusCoefficient N g q ^ 2 *
              h15BettinChandeeFrequencyCoefficient r ^ 2) =
        ∑ a ∈ h15BettinChandeeSupportedNatBlock N g A,
          ∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
            (h15BettinChandeeInverseCoefficient N g a ^ 2 *
              h15BettinChandeeModulusCoefficient N g q ^ 2) *
                (∑ r ∈ h15BettinChandeeNatBlock R,
                  h15BettinChandeeFrequencyCoefficient r ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
    _ = ∑ a ∈ h15BettinChandeeSupportedNatBlock N g A,
          (h15BettinChandeeInverseCoefficient N g a ^ 2 *
            (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
              h15BettinChandeeModulusCoefficient N g q ^ 2)) *
                (∑ r ∈ h15BettinChandeeNatBlock R,
                  h15BettinChandeeFrequencyCoefficient r ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = (∑ a ∈ h15BettinChandeeSupportedNatBlock N g A,
          h15BettinChandeeInverseCoefficient N g a ^ 2) *
        (∑ q ∈ h15BettinChandeeSupportedNatBlock N g Q,
          h15BettinChandeeModulusCoefficient N g q ^ 2) *
        ∑ r ∈ h15BettinChandeeNatBlock R,
          h15BettinChandeeFrequencyCoefficient r ^ 2 := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]

/-- Once the classical divisor-square estimate is supplied, all three exact
H15 coefficient norms have the balanced sizes used in the exponent audit. -/
theorem h15BettinChandeeTensorMass_le
    (H : H15DivisorSquareDyadicBound)
    {N g A Q R : ℕ} (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hA : 0 < A) (hR : 1 ≤ R) :
    h15BettinChandeeTensorMass N g A Q R ≤
      (1 / (A : ℝ)) * (4 * (Q : ℝ) ^ 3) *
        (H.constant * (1 + Real.log (2 * (R : ℝ))) ^ 3 /
          (R : ℝ) ^ 2) := by
  rw [h15BettinChandeeTensorMass_eq]
  have hInv := h15BettinChandeeInverseMass_le hN hg hA
  have hMod := h15BettinChandeeModulusMass_le (Q := Q) hN hg
  have hFreq := H.bound R hR
  exact mul_le_mul
    (mul_le_mul hInv hMod
      (h15BettinChandeeModulusMass_nonneg N g Q)
      (by positivity))
    hFreq
    (h15BettinChandeeFrequencyMass_nonneg R)
    (mul_nonneg (by positivity) (by positivity))

/-! ## Complete exponent audit, including the published phase factor -/

/-- Power contributed by `(1 + R/N^2)^(1/2)` when `R=N^kappa`. -/
noncomputable def h15BettinChandeePhaseLossExponent (kappa : ℝ) : ℝ :=
  max 0 ((kappa - 2) / 2)

noncomputable def h15BettinChandeeFirstCompleteExponent
    (kappa : ℝ) : ℝ :=
  h15BettinChandeeFirstScaledExponent kappa +
    h15BettinChandeePhaseLossExponent kappa

noncomputable def h15BettinChandeeSecondCompleteExponent
    (kappa : ℝ) : ℝ :=
  h15BettinChandeeSecondScaledExponent kappa +
    h15BettinChandeePhaseLossExponent kappa

noncomputable def h15BettinChandeeWorstCompleteExponent
    (kappa : ℝ) : ℝ :=
  max (h15BettinChandeeFirstCompleteExponent kappa)
    (h15BettinChandeeSecondCompleteExponent kappa)

theorem h15BettinChandeePhaseLossExponent_eq_zero
    {kappa : ℝ} (hkappa : kappa ≤ 2) :
    h15BettinChandeePhaseLossExponent kappa = 0 := by
  unfold h15BettinChandeePhaseLossExponent
  rw [max_eq_left]
  linarith

theorem h15BettinChandeePhaseLossExponent_of_two_le
    {kappa : ℝ} (hkappa : 2 ≤ kappa) :
    h15BettinChandeePhaseLossExponent kappa = (kappa - 2) / 2 := by
  unfold h15BettinChandeePhaseLossExponent
  rw [max_eq_right]
  linarith

theorem h15BettinChandeeFirstCompleteExponent_of_two_le
    {kappa : ℝ} (hkappa : 2 ≤ kappa) :
    h15BettinChandeeFirstCompleteExponent kappa =
      -(11 / 20) - (3 / 20) * kappa := by
  rw [h15BettinChandeeFirstCompleteExponent,
    h15BettinChandeeFirstScaledExponent,
    h15BettinChandeePhaseLossExponent_of_two_le hkappa]
  ring

theorem h15BettinChandeeSecondCompleteExponent_of_two_le
    {kappa : ℝ} (hkappa : 2 ≤ kappa) :
    h15BettinChandeeSecondCompleteExponent kappa = -(5 / 8) := by
  rw [h15BettinChandeeSecondCompleteExponent,
    h15BettinChandeeSecondScaledExponent,
    h15BettinChandeePhaseLossExponent_of_two_le hkappa]
  ring

/-- Including the phase factor leaves the lower power-saving threshold
unchanged. -/
theorem h15BettinChandeeWorstCompleteExponent_neg_iff (kappa : ℝ) :
    h15BettinChandeeWorstCompleteExponent kappa < 0 ↔
      3 / 4 < kappa := by
  by_cases hkappa : kappa ≤ 2
  · rw [h15BettinChandeeWorstCompleteExponent,
      h15BettinChandeeFirstCompleteExponent,
      h15BettinChandeeSecondCompleteExponent,
      h15BettinChandeePhaseLossExponent_eq_zero hkappa]
    simp only [add_zero]
    exact h15BettinChandeeWorstScaledExponent_neg_iff kappa
  · have hkappa' : 2 ≤ kappa := le_of_lt (lt_of_not_ge hkappa)
    rw [h15BettinChandeeWorstCompleteExponent, max_lt_iff,
      h15BettinChandeeFirstCompleteExponent_of_two_le hkappa',
      h15BettinChandeeSecondCompleteExponent_of_two_le hkappa']
    constructor
    · intro _
      linarith
    · intro _
      constructor <;> linarith

/-- In the ultra-high regime the second Bettin--Chandee term has no decay in
the frequency scale itself: its `R^(-1/2)` coefficient gain is exactly
cancelled by the square-root phase factor. -/
theorem h15BettinChandeeSecondUltraHighFrequencyExponent_eq_zero :
    -(1 / 2 : ℝ) + 1 / 2 = 0 := by
  norm_num

/-! ## Hybrid ultra-high tail stop test -/

/-- Power predicted by the rowwise absolute tail after summing the H15
arithmetic mass and starting the ultra-high tail at `R=N^lambda`.
The arithmetic mass costs `N^(1/2)` after the three-halves Abel damping,
while the divisor tail gains `R^(-1/2)` (up to logarithms). -/
noncomputable def h15AbsoluteUltraHighExponent (lambda : ℝ) : ℝ :=
  1 / 2 - lambda / 2

theorem h15AbsoluteUltraHighExponent_neg_iff (lambda : ℝ) :
    h15AbsoluteUltraHighExponent lambda < 0 ↔ 1 < lambda := by
  unfold h15AbsoluteUltraHighExponent
  constructor <;> intro h <;> linarith

/-- The convenient cutoff `R=N^3` has a full negative power available for
the absolute ultra-high tail. -/
theorem h15AbsoluteUltraHighExponent_three :
    h15AbsoluteUltraHighExponent 3 = -1 := by
  norm_num [h15AbsoluteUltraHighExponent]

/-- There is a nonempty overlap between the finite Bettin--Chandee window
and the absolute ultra-high tail: every `lambda>2` lies beyond both the
phase transition and the absolute-tail threshold. -/
theorem h15HybridCutoff_exponent_conditions
    {lambda : ℝ} (hlambda : 2 < lambda) :
    2 ≤ lambda ∧ h15AbsoluteUltraHighExponent lambda < 0 := by
  exact ⟨hlambda.le,
    (h15AbsoluteUltraHighExponent_neg_iff lambda).2 (by linarith)⟩

end NBMellinTools.NB12
