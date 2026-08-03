import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmDigammaMultiplication

/-!
# Rational block identities for Ehm's autocorrelation series

This module starts the denominator-block reduction of the coupled rational
closed form.  It keeps exact-integer hits explicit and proves that their
harmonic contribution is precisely the term needed to convert Ehm's centered
fractional-part convention to the BBLS `B₁` convention.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBlocks

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesValue
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDigammaMultiplication
open RH.Criteria.NymanBeurling.BCFLogTaperEhmAutocorrelationNormalization
open RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBridge
open RH.Criteria.NymanBeurling.BCFLogTaperCotangentReduction

/-- Reindex a harmonic sum over multiples of `q` in `[1,qM]`. -/
theorem sum_reciprocal_multiples_eq
    (q M : ℕ) (hq : 0 < q) :
    (∑ k ∈ Finset.Icc 1 (q * M),
      if q ∣ k then 1 / (k : ℝ) else 0) =
        (1 / (q : ℝ)) * (harmonic M : ℝ) := by
  rw [← Finset.sum_filter]
  let emb : ℕ ↪ ℕ :=
    { toFun := fun k => q * k
      inj' := fun _ _ hab => Nat.mul_left_cancel hq hab }
  have hfilter :
      (Finset.Icc 1 (q * M)).filter (fun k : ℕ => q ∣ k) =
        (Finset.Icc 1 M).map emb := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map,
      emb]
    constructor
    · rintro ⟨hk, ⟨l, rfl⟩⟩
      refine ⟨l, ?_, rfl⟩
      constructor
      · have : 0 < l := by
          by_contra hl
          simp only [not_lt] at hl
          have : l = 0 := Nat.eq_zero_of_le_zero hl
          subst l
          simp at hk
        exact this
      · exact Nat.le_of_mul_le_mul_left hk.2 hq
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨Nat.mul_pos hq hl.1, Nat.mul_le_mul_left q hl.2⟩,
        dvd_mul_right q l⟩
  rw [hfilter, Finset.sum_map, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div,
    emb, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change (((q * k : ℕ) : ℝ))⁻¹ =
    (q : ℝ)⁻¹ * (k : ℝ)⁻¹
  push_cast
  rw [mul_inv]

/-- For a coprime rational scale, the weighted exact-integer hits are exactly
the reciprocal multiples of its denominator. -/
theorem sum_reciprocal_fract_hits_eq
    (p q M : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p q) :
    (∑ k ∈ Finset.Icc 1 (q * M),
      if Int.fract ((k : ℝ) * ((p : ℝ) / q)) = 0
      then 1 / (k : ℝ) else 0) =
        (1 / (q : ℝ)) * (harmonic M : ℝ) := by
  rw [show (∑ k ∈ Finset.Icc 1 (q * M),
      if Int.fract ((k : ℝ) * ((p : ℝ) / q)) = 0
      then 1 / (k : ℝ) else 0) =
        ∑ k ∈ Finset.Icc 1 (q * M),
          if q ∣ k then 1 / (k : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro k hk
    have hiff := fract_natCast_mul_div_eq_zero_iff hq hcop.symm k
    by_cases hdiv : q ∣ k
    · have hhit := hiff.mpr hdiv
      simp [hhit, hdiv]
    · have hhit : Int.fract ((k : ℝ) * ((p : ℝ) / q)) ≠ 0 :=
        fun h => hdiv (hiff.mp h)
      simp [hhit, hdiv]]
  exact sum_reciprocal_multiples_eq q M hq

/-- Exact conversion of Ehm's centered fractional harmonic block to the
BBLS `B₁` block.  The discrepancy is supported only at denominator
multiples and is evaluated, not bounded. -/
theorem sum_fract_sub_half_div_eq_bernoulli_sub
    (p q M : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p q) :
    (∑ k ∈ Finset.Icc 1 (q * M),
      (Int.fract ((k : ℝ) * ((p : ℝ) / q)) - 1 / 2) / (k : ℝ)) =
      (∑ k ∈ Finset.Icc 1 (q * M),
        bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) / (k : ℝ)) -
          (harmonic M : ℝ) / (2 * q) := by
  have hpoint : ∀ k : ℕ, 0 < k →
      (Int.fract ((k : ℝ) * ((p : ℝ) / q)) - 1 / 2) / (k : ℝ) =
        bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) / (k : ℝ) -
          (if Int.fract ((k : ℝ) * ((p : ℝ) / q)) = 0
            then 1 / (k : ℝ) else 0) / 2 := by
    intro k hk
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    unfold bernoulliB1
    by_cases hhit : Int.fract ((k : ℝ) * ((p : ℝ) / q)) = 0
    · simp [hhit]
      field_simp [hkR]
    · simp [hhit]
  calc
    _ = (∑ k ∈ Finset.Icc 1 (q * M),
          bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) / (k : ℝ)) -
        (∑ k ∈ Finset.Icc 1 (q * M),
          (if Int.fract ((k : ℝ) * ((p : ℝ) / q)) = 0
            then 1 / (k : ℝ) else 0) / 2) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      exact hpoint k (Finset.mem_Icc.mp hk).1
    _ = _ := by
      rw [← Finset.sum_div,
        sum_reciprocal_fract_hits_eq p q M hq hcop]
      have hBcomm :
          (∑ k ∈ Finset.Icc 1 (q * M),
            bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) / (k : ℝ)) =
          ∑ k ∈ Finset.Icc 1 (q * M),
            bernoulliB1 (((p : ℝ) / q) * (k : ℝ)) / (k : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        ring
      rw [hBcomm]
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp [hqR]

/-- The ceiling defect is the complementary centered sawtooth, including
the exact correction at integer points. -/
theorem natCeil_sub_eq_half_sub_bernoulliB1_sub_indicator
    (x : ℝ) (hx : 0 ≤ x) :
    ((⌈x⌉₊ : ℕ) : ℝ) - x =
      1 / 2 - bernoulliB1 x -
        (if Int.fract x = 0 then 1 / 2 else 0) := by
  have hdecomp : ((⌊x⌋₊ : ℕ) : ℝ) + Int.fract x = x := by
    rw [natCast_floor_eq_intCast_floor hx, Int.floor_add_fract]
  by_cases hfract : Int.fract x = 0
  · have hxFloor : x = ((⌊x⌋₊ : ℕ) : ℝ) := by linarith
    have hceil : ⌈x⌉₊ = ⌊x⌋₊ := by
      rw [hxFloor, Nat.ceil_natCast, Nat.floor_natCast]
    unfold bernoulliB1
    rw [hfract, hceil]
    simp
    linarith
  · have hceil : ⌈x⌉₊ = ⌊x⌋₊ + 1 := by
      apply le_antisymm (Nat.ceil_le_floor_add_one x)
      have hle : ⌊x⌋₊ ≤ ⌈x⌉₊ := Nat.floor_le_ceil x
      apply Nat.add_one_le_iff.mpr
      exact lt_of_le_of_ne hle (fun heq => by
        have hxCeil : x ≤ ((⌈x⌉₊ : ℕ) : ℝ) := Nat.le_ceil x
        have hFloorx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx
        have hxEq : x = ((⌊x⌋₊ : ℕ) : ℝ) := by
          apply le_antisymm
          · simpa [heq] using hxCeil
          · exact hFloorx
        apply hfract
        linarith)
    unfold bernoulliB1
    rw [if_neg hfract, if_neg hfract, hceil]
    push_cast
    linarith

/-- At a positive rational argument the floor in `ehmHarmonic` is ordinary
natural division. -/
theorem ehmHarmonic_nat_mul_ratio_eq
    (p q k : ℕ) :
    ehmHarmonic ((k : ℝ) * ((p : ℝ) / q)) =
      (∑ j ∈ Finset.Icc 1 (k * p / q), 1 / (j : ℝ)) := by
  have harg : (k : ℝ) * ((p : ℝ) / q) =
      ((k * p : ℕ) : ℝ) / (q : ℝ) := by
    push_cast
    ring
  unfold ehmHarmonic
  rw [harg, Nat.floor_div_eq_div]

/-- Pad one floor-harmonic row to the complete `pM` rectangle. -/
theorem ehmHarmonic_ratio_eq_padded_row
    (p q M k : ℕ) (hq : 0 < q) (hk : k ≤ q * M) :
    ehmHarmonic ((k : ℝ) * ((p : ℝ) / q)) =
      ∑ j ∈ Finset.Icc 1 (p * M),
        if j ≤ k * p / q then 1 / (j : ℝ) else 0 := by
  rw [ehmHarmonic_nat_mul_ratio_eq p q k, ← Finset.sum_filter]
  have hupper : k * p / q ≤ p * M := by
    have hmul : k * p ≤ (q * M) * p := Nat.mul_le_mul_right p hk
    calc
      k * p / q ≤ (q * M) * p / q := Nat.div_le_div_right hmul
      _ = p * M := by
        rw [show (q * M) * p = q * (p * M) by ring,
          Nat.mul_div_cancel_left _ hq]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- For a fixed harmonic denominator `j`, the admissible `k` form the
integer interval from the rational ceiling to `qM`. -/
theorem filter_floor_ratio_column_eq_Icc
    (p q M j : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hj : j ∈ Finset.Icc 1 (p * M)) :
    (Finset.Icc 1 (q * M)).filter (fun k : ℕ => j ≤ k * p / q) =
      Finset.Icc
        ⌈(j : ℝ) * ((q : ℝ) / p)⌉₊ (q * M) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
  have hceilpos : 0 < ⌈(j : ℝ) * ((q : ℝ) / p)⌉₊ := by
    rw [Nat.ceil_pos]
    positivity
  have hceilUpper : ⌈(j : ℝ) * ((q : ℝ) / p)⌉₊ ≤ q * M := by
    rw [Nat.ceil_le]
    have hform : (j : ℝ) * ((q : ℝ) / p) =
        ((j : ℝ) * q) / p := by ring
    rw [hform]
    rw [div_le_iff₀ hpR]
    push_cast
    have hjUpper := (Finset.mem_Icc.mp hj).2
    have hnat : j * q ≤ q * M * p := by
      calc
        j * q ≤ (p * M) * q := Nat.mul_le_mul_right q hjUpper
        _ = q * M * p := by ring
    exact_mod_cast hnat
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  have hcond : j ≤ k * p / q ↔
      ⌈(j : ℝ) * ((q : ℝ) / p)⌉₊ ≤ k := by
    rw [Nat.le_div_iff_mul_le hq, Nat.ceil_le]
    have hform : (j : ℝ) * ((q : ℝ) / p) =
        ((j : ℝ) * q) / p := by ring
    rw [hform]
    rw [div_le_iff₀ hpR]
    constructor <;> intro h <;> exact_mod_cast h
  rw [hcond]
  omega

/-- The rational ceiling associated to a column in the complete `pM`
rectangle stays below the opposite side `qM`. -/
theorem natCeil_mul_ratio_le_mul
    (p q M j : ℕ) (hp : 0 < p)
    (hj : j ∈ Finset.Icc 1 (p * M)) :
    ⌈(j : ℝ) * ((q : ℝ) / p)⌉₊ ≤ q * M := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Nat.ceil_le]
  have hform : (j : ℝ) * ((q : ℝ) / p) =
      ((j : ℝ) * q) / p := by ring
  rw [hform, div_le_iff₀ hpR]
  have hjUpper := (Finset.mem_Icc.mp hj).2
  have hnat : j * q ≤ q * M * p := by
    calc
      j * q ≤ (p * M) * q := Nat.mul_le_mul_right q hjUpper
      _ = q * M * p := by ring
  exact_mod_cast hnat

/-- The exact floor-harmonic double count over a complete denominator
block. -/
theorem sum_ehmHarmonic_ratio_block_eq_ceil
    (p q M : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (∑ k ∈ Finset.Icc 1 (q * M),
      ehmHarmonic ((k : ℝ) * ((p : ℝ) / q))) =
      ∑ j ∈ Finset.Icc 1 (p * M),
        (((q * M + 1 -
          ⌈(j : ℝ) * ((q : ℝ) / p)⌉₊ : ℕ) : ℝ) / (j : ℝ)) := by
  calc
    _ = ∑ k ∈ Finset.Icc 1 (q * M),
        ∑ j ∈ Finset.Icc 1 (p * M),
          if j ≤ k * p / q then 1 / (j : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact ehmHarmonic_ratio_eq_padded_row p q M k hq
        (Finset.mem_Icc.mp hk).2
    _ = ∑ j ∈ Finset.Icc 1 (p * M),
        ∑ k ∈ Finset.Icc 1 (q * M),
          if j ≤ k * p / q then 1 / (j : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter,
        filter_floor_ratio_column_eq_Icc p q M j hp hq hj,
        Finset.sum_const]
      rw [Nat.card_Icc]
      simp only [nsmul_eq_mul]
      ring

/-- Rewrite the floor-harmonic block entirely in terms of the periodic BBLS
`B₁` sum and the exact denominator-hit correction. -/
theorem sum_ehmHarmonic_ratio_block_eq_bernoulli
    (p q M : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) :
    (∑ k ∈ Finset.Icc 1 (q * M),
      ehmHarmonic ((k : ℝ) * ((p : ℝ) / q))) =
      (((q * M : ℕ) : ℝ) + 1 / 2) * (harmonic (p * M) : ℝ) -
        (q * M : ℕ) +
        (∑ j ∈ Finset.Icc 1 (p * M),
          bernoulliB1 ((j : ℝ) * ((q : ℝ) / p)) / (j : ℝ)) +
        (harmonic M : ℝ) / (2 * p) := by
  rw [sum_ehmHarmonic_ratio_block_eq_ceil p q M hp hq]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpoint : ∀ j ∈ Finset.Icc 1 (p * M),
      (((q * M + 1 -
          ⌈(j : ℝ) * ((q : ℝ) / p)⌉₊ : ℕ) : ℝ) / (j : ℝ)) =
        ((((q * M : ℕ) : ℝ) + 1 / 2) * (1 / (j : ℝ)) -
          (q : ℝ) / p +
          bernoulliB1 ((j : ℝ) * ((q : ℝ) / p)) / (j : ℝ) +
          (if Int.fract ((j : ℝ) * ((q : ℝ) / p)) = 0
            then 1 / (j : ℝ) else 0) / 2) := by
    intro j hj
    have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hjpos.ne'
    let x : ℝ := (j : ℝ) * ((q : ℝ) / p)
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hceil := natCeil_mul_ratio_le_mul p q M j hp hj
    change ⌈x⌉₊ ≤ q * M at hceil
    have hcast :
        (((q * M + 1 - ⌈x⌉₊ : ℕ) : ℝ)) =
          ((q * M : ℕ) : ℝ) + 1 - (⌈x⌉₊ : ℝ) := by
      rw [Nat.cast_sub (by omega : ⌈x⌉₊ ≤ q * M + 1)]
      push_cast
      ring
    have hdefect :=
      natCeil_sub_eq_half_sub_bernoulliB1_sub_indicator x hx
    dsimp [x] at hcast hdefect ⊢
    rw [hcast]
    by_cases hhit : Int.fract ((j : ℝ) * ((q : ℝ) / p)) = 0
    · simp [hhit] at hdefect ⊢
      field_simp [hjR, hpR] at hdefect ⊢
      nlinarith
    · simp [hhit] at hdefect ⊢
      field_simp [hjR, hpR] at hdefect ⊢
      nlinarith
  calc
    _ = ∑ j ∈ Finset.Icc 1 (p * M),
        ((((q * M : ℕ) : ℝ) + 1 / 2) * (1 / (j : ℝ)) -
          (q : ℝ) / p +
          bernoulliB1 ((j : ℝ) * ((q : ℝ) / p)) / (j : ℝ) +
          (if Int.fract ((j : ℝ) * ((q : ℝ) / p)) = 0
            then 1 / (j : ℝ) else 0) / 2) := by
      apply Finset.sum_congr rfl
      exact hpoint
    _ = _ := by
      have hcard : (Finset.Icc 1 (p * M)).card = p * M := by simp
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul, hcard, ← Finset.sum_div]
      have hharmonic :
          (∑ j ∈ Finset.Icc 1 (p * M), 1 / (j : ℝ)) =
            (harmonic (p * M) : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
      rw [hharmonic]
      rw [sum_reciprocal_fract_hits_eq q p M hp hcop.symm]
      have hBcomm :
          (∑ j ∈ Finset.Icc 1 (p * M),
            bernoulliB1 ((j : ℝ) * ((q : ℝ) / p)) / (j : ℝ)) =
          ∑ j ∈ Finset.Icc 1 (p * M),
            bernoulliB1 (((q : ℝ) / p) * (j : ℝ)) / (j : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        ring
      rw [hBcomm]
      field_simp [hpR]
      push_cast
      ring

/-- The elementary non-periodic part of the rational closed form on the
complete denominator subsequence `N=qM`. -/
noncomputable def ehmR1RationalBlockMain
    (p q M : ℕ) : ℝ :=
  ((q * M : ℕ) : ℝ) *
      (Real.log ((p : ℝ) / q) + Real.eulerMascheroniConstant) +
    Real.log ((Nat.factorial (q * M) : ℕ) : ℝ) -
    (((q * M : ℕ) : ℝ) + 1 / 2) * (harmonic (p * M) : ℝ) +
    (q * M : ℕ)

/-- Exact complete-block reduction of Ehm's coupled rational expression.
The two endpoint-hit harmonic terms cancel identically, leaving the main
Stirling/harmonic piece and two periodic `B₁` sums. -/
theorem ehmR1RationalPartialClosedForm_mul_eq_blockMain_sub_bernoulli
    (p q M : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) :
    ehmR1RationalPartialClosedForm p q (q * M) =
      ehmR1RationalBlockMain p q M -
        (∑ j ∈ Finset.Icc 1 (p * M),
          bernoulliB1 ((j : ℝ) * ((q : ℝ) / p)) / (j : ℝ)) -
        ((q : ℝ) / p) *
          (∑ k ∈ Finset.Icc 1 (q * M),
            bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) / (k : ℝ)) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold ehmR1RationalPartialClosedForm ehmR1RationalBlockMain
  rw [sum_ehmHarmonic_ratio_block_eq_bernoulli p q M hp hq hcop,
    sum_fract_sub_half_div_eq_bernoulli_sub p q M hq hcop]
  field_simp [hpR, hqR]
  push_cast
  ring

/-- Ratio which transfers the proved second-order harmonic remainder from
the `pM` scale to the `qM` coefficient in the rational block main term. -/
noncomputable def ehmRationalHarmonicScaleRatio
    (p q M : ℕ) : ℝ :=
  (((q * M : ℕ) : ℝ) + 1 / 2) /
    (((p * M : ℕ) : ℝ) + 1 / 2)

/-- The rational harmonic scale ratio tends to `q/p`. -/
theorem ehmRationalHarmonicScaleRatio_tendsto
    (p q : ℕ) (hp : 0 < p) :
    Tendsto (ehmRationalHarmonicScaleRatio p q) atTop
      (𝓝 ((q : ℝ) / p)) := by
  have hone : Tendsto (fun M : ℕ => (1 : ℝ) / (M : ℝ)) atTop
      (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hnum : Tendsto (fun M : ℕ =>
      (q : ℝ) + (1 / 2) * (1 / (M : ℝ))) atTop (𝓝 (q : ℝ)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hone)
  have hden : Tendsto (fun M : ℕ =>
      (p : ℝ) + (1 / 2) * (1 / (M : ℝ))) atTop (𝓝 (p : ℝ)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hone)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hdiv := hnum.div hden hpR
  apply hdiv.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  change
    ((q : ℝ) + (1 / 2) * (1 / (M : ℝ))) /
        ((p : ℝ) + (1 / 2) * (1 / (M : ℝ))) =
      (((q * M : ℕ) : ℝ) + 1 / 2) /
        (((p * M : ℕ) : ℝ) + 1 / 2)
  push_cast
  field_simp [hMR]

/-- On positive complete blocks, the logarithmic scale difference is the
constant `log(q/p)`. -/
theorem eventually_log_mul_sub_log_mul_eq
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    ∀ᶠ M : ℕ in atTop,
      Real.log ((q * M : ℕ) : ℝ) -
          Real.log ((p * M : ℕ) : ℝ) =
        Real.log ((q : ℝ) / p) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  rw [Real.log_mul hqR hMR, Real.log_mul hpR hMR,
    Real.log_div hqR hpR]
  ring

/-- The non-periodic rational block has the expected elementary limit. -/
theorem ehmR1RationalBlockMain_tendsto
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    Tendsto (ehmR1RationalBlockMain p q) atTop
      (𝓝 ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant +
        Real.log ((q : ℝ) / p) - (q : ℝ) / p) / 2)) := by
  have hqcofinal : Tendsto (fun M : ℕ => q * M) atTop atTop := by
    simpa [Nat.mul_comm] using tendsto_nat_mul_const_atTop q hq
  have hpcofinal : Tendsto (fun M : ℕ => p * M) atTop atTop := by
    simpa [Nat.mul_comm] using tendsto_nat_mul_const_atTop p hp
  have hstirling := log_stirling_remainder_tendsto_zero.comp hqcofinal
  have hharmonic :=
    ehmHarmonicSecondOrderRemainder_tendsto.comp hpcofinal
  have hratio := ehmRationalHarmonicScaleRatio_tendsto p q hp
  have hscaled := hratio.mul hharmonic
  have hlog : Tendsto (fun M : ℕ =>
      Real.log ((q * M : ℕ) : ℝ) -
        Real.log ((p * M : ℕ) : ℝ)) atTop
      (𝓝 (Real.log ((q : ℝ) / p))) :=
    tendsto_const_nhds.congr'
      (Filter.EventuallyEq.symm
        (eventually_log_mul_sub_log_mul_eq p q hp hq))
  have hconst : Tendsto (fun _ : ℕ =>
      (1 / 2 : ℝ) * Real.log (2 * Real.pi)) atTop
      (𝓝 ((1 / 2 : ℝ) * Real.log (2 * Real.pi))) :=
    tendsto_const_nhds
  have hgamma : Tendsto (fun _ : ℕ =>
      -(Real.eulerMascheroniConstant / 2)) atTop
      (𝓝 (-(Real.eulerMascheroniConstant / 2))) :=
    tendsto_const_nhds
  have hlimit :=
    (((hconst.add hstirling).add (hlog.const_mul (1 / 2))).add hgamma).sub
      hscaled
  have heventual : ∀ᶠ M : ℕ in atTop,
      ehmR1RationalBlockMain p q M =
        (1 / 2) * Real.log (2 * Real.pi) +
          LogStirlingRemainder (q * M) +
          (1 / 2) *
            (Real.log ((q * M : ℕ) : ℝ) -
              Real.log ((p * M : ℕ) : ℝ)) -
          Real.eulerMascheroniConstant / 2 -
          ehmRationalHarmonicScaleRatio p q M *
            ehmHarmonicSecondOrderRemainder (p * M) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    unfold ehmR1RationalBlockMain LogStirlingRemainder
      ehmRationalHarmonicScaleRatio ehmHarmonicSecondOrderRemainder
    rw [ehmHarmonic_nat_eq_HarmonicReal,
      HarmonicReal_eq_mathlib_harmonic]
    push_cast
    rw [Real.log_mul hpR hMR, Real.log_mul hqR hMR,
      Real.log_div hpR hqR]
    field_simp [hpR, hqR, hMR]
    ring
  have hlimit' : Tendsto (fun M : ℕ =>
        (1 / 2) * Real.log (2 * Real.pi) +
          LogStirlingRemainder (q * M) +
          (1 / 2) *
            (Real.log ((q * M : ℕ) : ℝ) -
              Real.log ((p * M : ℕ) : ℝ)) -
          Real.eulerMascheroniConstant / 2 -
          ehmRationalHarmonicScaleRatio p q M *
            ehmHarmonicSecondOrderRemainder (p * M)) atTop
      (𝓝 ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant +
        Real.log ((q : ℝ) / p) - (q : ℝ) / p) / 2)) := by
    convert hlimit using 1
    all_goals ring
  exact hlimit'.congr' (Filter.EventuallyEq.symm heventual)

/-- The first periodic block tends to the `V(q,p)` cotangent value. -/
theorem tendsto_first_rational_bernoulli_block
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun M : ℕ =>
      ∑ j ∈ Finset.Icc 1 (p * M),
        bernoulliB1 ((j : ℝ) * ((q : ℝ) / p)) / (j : ℝ)) atTop
      (𝓝 (Real.pi / (2 * p) * cotangentSumVFormula q p)) := by
  have h := (tendsto_bernoulliB1_sum_div_rat q p hq hp).comp
    (tendsto_nat_mul_const_atTop p hp)
  simpa [Nat.mul_comm] using h

/-- The second periodic block, including its prefactor, tends to the
`V(p,q)` cotangent value with the common denominator `p`. -/
theorem tendsto_second_rational_bernoulli_block
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun M : ℕ =>
      ((q : ℝ) / p) *
        ∑ k ∈ Finset.Icc 1 (q * M),
          bernoulliB1 ((k : ℝ) * ((p : ℝ) / q)) / (k : ℝ)) atTop
      (𝓝 (Real.pi / (2 * p) * cotangentSumVFormula p q)) := by
  have h := (tendsto_bernoulliB1_sum_div_rat p q hp hq).comp
    (tendsto_nat_mul_const_atTop q hq)
  have hscaled := h.const_mul ((q : ℝ) / p)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  convert hscaled using 1
  · funext M
    congr 2
    ring
  · field_simp [hpR, hqR]

/-- On complete denominator blocks, Ehm's finite rational closed form tends
to the Vasyunin value.  The proof is an exact assembly of the elementary
block limit and the two periodic Bernoulli limits; in particular, no
Möbius-cancellation estimate enters here. -/
theorem ehmR1RationalPartialClosedForm_mul_tendsto_vasyunin
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) :
    Tendsto (fun M : ℕ =>
      ehmR1RationalPartialClosedForm p q (q * M)) atTop
      (𝓝 (vasyuninS1RationalKernel q p)) := by
  have hmain := ehmR1RationalBlockMain_tendsto p q hp hq
  have hfirst := tendsto_first_rational_bernoulli_block p q hp hq
  have hsecond := tendsto_second_rational_bernoulli_block p q hp hq
  have hraw := (hmain.sub hfirst).sub hsecond
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hlog :
      Real.log ((p : ℝ) / (q : ℝ)) =
        -Real.log ((q : ℝ) / (p : ℝ)) := by
    rw [show (p : ℝ) / (q : ℝ) =
      ((q : ℝ) / (p : ℝ))⁻¹ from (inv_div _ _).symm,
      Real.log_inv]
  have htarget :
      ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant +
          Real.log ((q : ℝ) / p) - (q : ℝ) / p) / 2 -
          Real.pi / (2 * p) * cotangentSumVFormula q p) -
          Real.pi / (2 * p) * cotangentSumVFormula p q =
        vasyuninS1RationalKernel q p := by
    unfold vasyuninS1RationalKernel vasyuninBEntryFormula ehmK
    rw [hlog]
    field_simp [hpR, hqR]
    ring
  rw [← htarget]
  exact hraw.congr' (Eventually.of_forall fun M =>
    (ehmR1RationalPartialClosedForm_mul_eq_blockMain_sub_bernoulli
      p q M hp hq hcop).symm)

/-- The coprime rational progression theorem obtained by comparing the
complete-block limit with the already proved full-sequence limit. -/
theorem ehmR1RationalPartialClosedForm_tendsto_vasyunin_of_coprime
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) :
    Tendsto (fun N : ℕ => ehmR1RationalPartialClosedForm p q N) atTop
      (𝓝 (vasyuninS1RationalKernel q p)) := by
  have hfull := ehmR1RationalPartialClosedForm_tendsto_tsum p q hp hq
  have hcofinal : Tendsto (fun M : ℕ => q * M) atTop atTop := by
    simpa [Nat.mul_comm] using tendsto_nat_mul_const_atTop q hq
  have hfullBlock := hfull.comp hcofinal
  have hvasyuninBlock :=
    ehmR1RationalPartialClosedForm_mul_tendsto_vasyunin
      p q hp hq hcop
  have hvalue := tendsto_nhds_unique hfullBlock hvasyuninBlock
  rw [hvalue] at hfull
  exact hfull

/-- Unconditional coprime rational progression package. -/
noncomputable def ehmCoprimeRationalProgressionAsymptoticsProved :
    EhmCoprimeRationalProgressionAsymptotics where
  tendsto_value :=
    ehmR1RationalPartialClosedForm_tendsto_vasyunin_of_coprime

/-- Unconditional rational progression package, obtained by exact gcd
descent from the coprime theorem. -/
noncomputable def ehmRationalProgressionAsymptoticsProved :
    EhmRationalProgressionAsymptotics :=
  ehmCoprimeRationalProgressionAsymptoticsProved.toRational

/-- The completed Week-2 bridge: at every positive rational scale, Ehm's
autocorrelation equals the absolutely convergent `R₁` series. -/
noncomputable def ehmAutocorrelationR1RationalSeriesBridgeProved :
    EhmAutocorrelationR1RationalSeriesBridge :=
  ehmAutocorrelationR1RationalSeriesBridge_of_progressions
    ehmRationalProgressionAsymptoticsProved

end RH.Criteria.NymanBeurling.BCFLogTaperEhmRationalBlocks
