import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorGeneralCoefficient

/-!
# Route C: collection of all transported Taylor residues

This module performs the finite parity-aware collection left open by the
arbitrary-coefficient normalization.  Odd Bernoulli rows vanish, the
remaining even indices are reindexed by `j = 2*n - 2`, and the terminal even
row is combined with the separate `2*b_m` contribution.

The final theorem identifies the sum of every contour-derived residue row
with the exact finite binomial contribution in Bettin--Conrey's coefficient
formula.  This is finite algebra and introduces no analytic assumption.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorGeneralCoefficient

open Complex
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow

/-! ## Pointwise form of a transported residue row -/

theorem routeCTaylorOneResidueScalarCoefficient_of_two_mul_lt
    (n m : ℕ) (hn : 1 ≤ n) (hnm : 2 * n < m) :
    routeCTaylorOneResidueScalarCoefficient n m =
      2 * (-1 : ℂ) ^ m *
        ((Nat.choose (m - 1) (2 * n - 2) : ℕ) : ℂ) *
          bettinConreyCentralTaylorB (2 * n) := by
  have hrle : 2 * n - 1 ≤ m := by omega
  have hne1 : m ≠ 2 * n - 1 := by omega
  have hne2 : m ≠ 2 * n - 1 + 1 := by omega
  unfold routeCTaylorOneResidueScalarCoefficient
    routeCTaylorInversePowerCoefficient
  simp only [hne1, hne2, if_false, hrle, if_true, zero_add]
  have hp : (-1 : ℂ) ^ (m - (2 * n - 1)) = -(-1 : ℂ) ^ m := by
    rw [show m - (2 * n - 1) = (m - 2 * n) + 1 by omega, pow_succ]
    have heven : Even (2 * n) := even_two_mul n
    calc
      (-1 : ℂ) ^ (m - 2 * n) * -1 =
          -((-1 : ℂ) ^ (m - 2 * n) * (-1 : ℂ) ^ (2 * n)) := by
            rw [Even.neg_one_pow heven]
            ring
      _ = -(-1 : ℂ) ^ m := by
        rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hnm)]
  rw [hp]
  simp only [show 2 * n - 1 - 1 = 2 * n - 2 by omega]
  ring

theorem routeCTaylorOneResidueScalarCoefficient_of_two_mul_eq
    (n m : ℕ) (hn : 1 ≤ n) (hnm : 2 * n = m) :
    routeCTaylorOneResidueScalarCoefficient n m =
      2 * (m : ℂ) * bettinConreyCentralTaylorB m := by
  subst m
  have hrle : 2 * n - 1 ≤ 2 * n := by omega
  have hne1 : 2 * n ≠ 2 * n - 1 := by omega
  have heq2 : 2 * n = 2 * n - 1 + 1 := by omega
  have hsub : 2 * n - (2 * n - 1) = 1 := by omega
  have hchoose : Nat.choose (2 * n - 1) (2 * n - 1 - 1) = 2 * n - 1 := by
    calc
      Nat.choose (2 * n - 1) (2 * n - 1 - 1) =
          Nat.choose (2 * n - 1) 1 :=
        Nat.choose_symm (by omega : 1 ≤ 2 * n - 1)
      _ = 2 * n - 1 := Nat.choose_one_right _
  unfold routeCTaylorOneResidueScalarCoefficient
    routeCTaylorInversePowerCoefficient
  dsimp only
  rw [if_neg hne1, if_pos heq2, if_pos hrle, hsub, pow_one, hchoose]
  push_cast
  have hcast : (((n * 2 - 1 : ℕ) : ℂ) + 1) = ((n * 2 : ℕ) : ℂ) := by
    exact_mod_cast (show n * 2 - 1 + 1 = n * 2 by omega)
  simp only [Nat.mul_comm n 2] at hcast ⊢
  have htwo : ((2 * n : ℕ) : ℂ) = 2 * (n : ℂ) := by norm_num
  linear_combination
    2 * bettinConreyCentralTaylorB (2 * n) * hcast +
    2 * bettinConreyCentralTaylorB (2 * n) * htwo

theorem routeCTaylorOneResidueScalarCoefficient_of_lt_two_mul
    (n m : ℕ) (hn : 1 ≤ n) (hnm : m < 2 * n) :
    routeCTaylorOneResidueScalarCoefficient n m = 0 := by
  by_cases heq : m = 2 * n - 1
  · unfold routeCTaylorOneResidueScalarCoefficient
      routeCTaylorInversePowerCoefficient
    simp [heq]
  · have hlt : m < 2 * n - 1 := by omega
    have hne2 : m ≠ 2 * n - 1 + 1 := by omega
    have hnle : ¬2 * n - 1 ≤ m := by omega
    unfold routeCTaylorOneResidueScalarCoefficient
      routeCTaylorInversePowerCoefficient
    simp [heq, hne2, hnle]

/-! ## Bernoulli parity and the exact finite reindexing -/

theorem routeCTaylorBinomialRows_filter_even (m : ℕ) :
    (∑ j ∈ Finset.range (m - 1),
        ((Nat.choose (m - 1) j : ℕ) : ℂ) *
          bettinConreyCentralTaylorB (j + 2)) =
      ∑ j ∈ (Finset.range (m - 1)).filter Even,
        ((Nat.choose (m - 1) j : ℕ) : ℂ) *
          bettinConreyCentralTaylorB (j + 2) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases heven : Even j
  · simp [heven]
  · have hoddj : Odd j := Nat.not_even_iff_odd.mp heven
    have hodd : Odd (j + 2) := hoddj.add_even (by norm_num)
    have hgt : 1 < j + 2 := by omega
    rw [bettinConreyCentralTaylorB_eq_zero_of_odd (j + 2) hodd hgt]
    simp [heven]

theorem routeCTaylorEvenBinomialRows_reindex (m : ℕ) :
    (∑ j ∈ (Finset.range (m - 1)).filter Even,
        ((Nat.choose (m - 1) j : ℕ) : ℂ) *
          bettinConreyCentralTaylorB (j + 2)) =
      ∑ n ∈ (Finset.Icc 1 m).filter (fun n => 2 * n ≤ m),
        ((Nat.choose (m - 1) (2 * n - 2) : ℕ) : ℂ) *
          bettinConreyCentralTaylorB (2 * n) := by
  refine Finset.sum_bij'
      (fun j _ => j / 2 + 1)
      (fun n _ => 2 * n - 2) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    rcases hj.2 with ⟨k, hk⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · constructor <;> omega
    · omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · exact ⟨n - 1, by omega⟩
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    rcases hj.2 with ⟨k, hk⟩
    change 2 * (j / 2 + 1) - 2 = j
    subst j
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    change (2 * n - 2) / 2 + 1 = n
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    rcases hj.2 with ⟨k, hk⟩
    change
      (((Nat.choose (m - 1) j : ℕ) : ℂ) *
          bettinConreyCentralTaylorB (j + 2)) =
        (((Nat.choose (m - 1) (2 * (j / 2 + 1) - 2) : ℕ) : ℂ) *
          bettinConreyCentralTaylorB (2 * (j / 2 + 1)))
    subst j
    have hidx : 2 * ((k + k) / 2 + 1) - 2 = k + k := by omega
    have harg : 2 * ((k + k) / 2 + 1) = k + k + 2 := by omega
    rw [hidx, harg]

/-! ## Collection, including the terminal even mode -/

theorem routeCTaylorOneResidueScalarCoefficient_eq_filtered_add_delta
    (n m : ℕ) (hn : 1 ≤ n) :
    routeCTaylorOneResidueScalarCoefficient n m =
      (if 2 * n ≤ m then
        2 * (-1 : ℂ) ^ m *
          ((Nat.choose (m - 1) (2 * n - 2) : ℕ) : ℂ) *
            bettinConreyCentralTaylorB (2 * n)
       else 0) +
      (if 2 * n = m then
        2 * (-1 : ℂ) ^ m * bettinConreyCentralTaylorB m
       else 0) := by
  rcases lt_trichotomy (2 * n) m with hlt | heq | hgt
  · rw [if_pos (Nat.le_of_lt hlt), if_neg (Nat.ne_of_lt hlt)]
    simpa using
      routeCTaylorOneResidueScalarCoefficient_of_two_mul_lt n m hn hlt
  · have hle : 2 * n ≤ m := le_of_eq heq
    rw [if_pos hle, if_pos heq]
    rw [routeCTaylorOneResidueScalarCoefficient_of_two_mul_eq n m hn heq]
    have heven : Even m := ⟨n, by omega⟩
    rw [Even.neg_one_pow heven]
    have hchoose : Nat.choose (m - 1) (2 * n - 2) = m - 1 := by
      subst m
      calc
        Nat.choose (2 * n - 1) (2 * n - 2) =
            Nat.choose (2 * n - 1) 1 := by
          exact Nat.choose_symm (by omega : 1 ≤ 2 * n - 1)
        _ = 2 * n - 1 := Nat.choose_one_right _
    rw [hchoose, heq]
    have hcast : (((m - 1 : ℕ) : ℂ) + 1) = (m : ℂ) := by
      exact_mod_cast (show m - 1 + 1 = m by omega)
    linear_combination
      -2 * bettinConreyCentralTaylorB m * hcast
  · have hnle : ¬2 * n ≤ m := Nat.not_le.mpr hgt
    have hne : 2 * n ≠ m := Nat.ne_of_gt hgt
    rw [if_neg hnle, if_neg hne]
    simpa using
      routeCTaylorOneResidueScalarCoefficient_of_lt_two_mul n m hn hgt

theorem routeCTaylorEndpointDelta_sum (m : ℕ) (hm : 2 ≤ m) :
    (∑ n ∈ Finset.Icc 1 m,
        if 2 * n = m then
          2 * (-1 : ℂ) ^ m * bettinConreyCentralTaylorB m
        else 0) =
      2 * (-1 : ℂ) ^ m * bettinConreyCentralTaylorB m := by
  rcases Nat.even_or_odd m with heven | hodd
  · rcases heven with ⟨k, hk⟩
    have hkm : k ∈ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc]
      omega
    rw [Finset.sum_eq_single_of_mem k hkm]
    · simp only [hk, if_pos (by omega : 2 * k = k + k)]
    · intro n hn hne
      rw [if_neg]
      intro heq
      omega
  · have hb : bettinConreyCentralTaylorB m = 0 :=
      bettinConreyCentralTaylorB_eq_zero_of_odd m hodd hm
    simp [hb]

theorem routeCTaylorFilteredBinomialRows_factor (m : ℕ) :
    (∑ n ∈ Finset.Icc 1 m,
        if 2 * n ≤ m then
          2 * (-1 : ℂ) ^ m *
            ((Nat.choose (m - 1) (2 * n - 2) : ℕ) : ℂ) *
              bettinConreyCentralTaylorB (2 * n)
        else 0) =
      2 * (-1 : ℂ) ^ m *
        (∑ n ∈ (Finset.Icc 1 m).filter (fun n => 2 * n ≤ m),
          ((Nat.choose (m - 1) (2 * n - 2) : ℕ) : ℂ) *
            bettinConreyCentralTaylorB (2 * n)) := by
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hle : 2 * n ≤ m
  · simp only [hle, if_true]
    ring
  · simp [hle]

/-- **Exact collection theorem.**  The sum of all transported odd-residue
coefficient rows is the complete finite binomial residue contribution in
the native Bettin--Conrey Taylor coefficient. -/
theorem sum_routeCTaylorOneResidueScalarCoefficient_eq_residueBinomial
    (m : ℕ) (hm : 2 ≤ m) :
    (∑ n ∈ Finset.Icc 1 m,
        routeCTaylorOneResidueScalarCoefficient n m) =
      routeCTaylorResidueBinomialScalarCoefficient m := by
  calc
    (∑ n ∈ Finset.Icc 1 m,
        routeCTaylorOneResidueScalarCoefficient n m) =
        ∑ n ∈ Finset.Icc 1 m,
          ((if 2 * n ≤ m then
              2 * (-1 : ℂ) ^ m *
                ((Nat.choose (m - 1) (2 * n - 2) : ℕ) : ℂ) *
                  bettinConreyCentralTaylorB (2 * n)
            else 0) +
          (if 2 * n = m then
              2 * (-1 : ℂ) ^ m * bettinConreyCentralTaylorB m
            else 0)) := by
      apply Finset.sum_congr rfl
      intro n hnmem
      have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
      exact
        routeCTaylorOneResidueScalarCoefficient_eq_filtered_add_delta n m hn
    _ =
        (∑ n ∈ Finset.Icc 1 m,
          if 2 * n ≤ m then
            2 * (-1 : ℂ) ^ m *
              ((Nat.choose (m - 1) (2 * n - 2) : ℕ) : ℂ) *
                bettinConreyCentralTaylorB (2 * n)
          else 0) +
        (∑ n ∈ Finset.Icc 1 m,
          if 2 * n = m then
            2 * (-1 : ℂ) ^ m * bettinConreyCentralTaylorB m
          else 0) := by
      rw [Finset.sum_add_distrib]
    _ =
        2 * (-1 : ℂ) ^ m *
          (∑ n ∈ (Finset.Icc 1 m).filter (fun n => 2 * n ≤ m),
            ((Nat.choose (m - 1) (2 * n - 2) : ℕ) : ℂ) *
              bettinConreyCentralTaylorB (2 * n)) +
        2 * (-1 : ℂ) ^ m * bettinConreyCentralTaylorB m := by
      rw [routeCTaylorFilteredBinomialRows_factor m,
        routeCTaylorEndpointDelta_sum m hm]
    _ = routeCTaylorResidueBinomialScalarCoefficient m := by
      rw [← routeCTaylorEvenBinomialRows_reindex m,
        ← routeCTaylorBinomialRows_filter_even m]
      unfold routeCTaylorResidueBinomialScalarCoefficient
      ring

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorGeneralCoefficient
