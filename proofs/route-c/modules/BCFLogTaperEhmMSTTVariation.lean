import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows

/-!
# Variation gate for the MSTT reduction

This module opens the first analytic loss in the low-product MSTT estimate.
It separates the discrete variation of the complete paired Ehm weight into
the main logarithmic-taper variation and one variation for every retained
near divisor.  No asymptotic bound is asserted.

The decomposition matters because a scale-free bound for the unnormalised
variation is not the statement naturally supplied by the definitions: the
outer dyadic cutoff average contains about `N` summands.  The final analytic
gate must therefore record the normalization used by the dyadic mean, or
prove a correspondingly scaled bound.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTVariation

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCutoffAverageMainTerm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDoubleCofinal
open RH.Criteria.NymanBeurling.BCFLogTaperEhmDyadicDispersion
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPairedAdditiveRows
open RH.Criteria.NymanBeurling.BCFLogTaperEhmProductTruncation
open RH.Criteria.NymanBeurling.BCFLogTaperEhmTypeIISplit
open RH.Criteria.NymanBeurling.BCFLogTaperMSTTPolynomialPhase

/-! ## Reusable variation algebra -/

theorem complexWeightVariation_add_le
    (u v : ℕ → ℂ) (A B : ℕ) :
    complexWeightVariation (fun m => u m + v m) A B ≤
      complexWeightVariation u A B + complexWeightVariation v A B := by
  classical
  unfold complexWeightVariation
  calc
    ‖u (B + 1) + v (B + 1)‖ +
        ∑ m ∈ Finset.Icc A B,
          ‖(u m + v m) - (u (m + 1) + v (m + 1))‖ ≤
      (‖u (B + 1)‖ + ‖v (B + 1)‖) +
        ∑ m ∈ Finset.Icc A B,
          (‖u m - u (m + 1)‖ + ‖v m - v (m + 1)‖) := by
      gcongr
      · exact norm_add_le _ _
      · rename_i m hm
        have hsplit :
            (u m + v m) - (u (m + 1) + v (m + 1)) =
              (u m - u (m + 1)) + (v m - v (m + 1)) := by
          ring
        rw [hsplit]
        exact norm_add_le _ _
    _ = (‖u (B + 1)‖ +
          ∑ m ∈ Finset.Icc A B, ‖u m - u (m + 1)‖) +
        (‖v (B + 1)‖ +
          ∑ m ∈ Finset.Icc A B, ‖v m - v (m + 1)‖) := by
      rw [Finset.sum_add_distrib]
      ring

theorem complexWeightVariation_const_mul
    (c : ℂ) (w : ℕ → ℂ) (A B : ℕ) :
    complexWeightVariation (fun m => c * w m) A B =
      ‖c‖ * complexWeightVariation w A B := by
  classical
  unfold complexWeightVariation
  have hdiff : ∀ m : ℕ,
      c * w m - c * w (m + 1) = c * (w m - w (m + 1)) := by
    intro m
    ring
  simp_rw [hdiff, norm_mul]
  rw [← Finset.mul_sum]
  ring

/-- A hard upper cutoff on a discrete weight. -/
noncomputable def complexUpperCutoffWeight
    (T : ℕ) (w : ℕ → ℂ) (m : ℕ) : ℂ :=
  if m ≤ T then w m else 0

/-- Extending the right endpoint by one cannot decrease endpoint-plus-total
variation.  The former endpoint is controlled by the new endpoint and the
one newly exposed difference. -/
theorem complexWeightVariation_mono_right_succ
    (w : ℕ → ℂ) (A B : ℕ) (hAB : A ≤ B) :
    complexWeightVariation w A B ≤
      complexWeightVariation w A (B + 1) := by
  unfold complexWeightVariation
  rw [Finset.sum_Icc_succ_top (by omega)]
  have htriangle :
      ‖w (B + 1)‖ ≤ ‖w (B + 2)‖ + ‖w (B + 1) - w (B + 2)‖ := by
    have hsplit : w (B + 1) =
        (w (B + 1) - w (B + 2)) + w (B + 2) := by ring
    rw [hsplit]
    simpa [add_comm] using
      (norm_add_le (w (B + 1) - w (B + 2)) (w (B + 2)))
  linarith

/-- Clipping a weight to an initial segment does not increase its
endpoint-plus-total variation.  At the clipping point the new jump to zero
is already bounded by the discarded tail variation and its endpoint. -/
theorem complexWeightVariation_upperCutoff_le
    (T : ℕ) (w : ℕ → ℂ) (A B : ℕ) (hAB : A ≤ B) :
    complexWeightVariation (complexUpperCutoffWeight T w) A B ≤
      complexWeightVariation w A B := by
  induction B, hAB using Nat.le_induction with
  | base =>
      by_cases hAT : A ≤ T
      · by_cases hsuccT : A + 1 ≤ T
        · have hAlt : A < T := by omega
          simp [complexWeightVariation, complexUpperCutoffWeight,
            hAT, hsuccT, hAlt]
        · have hTA : T = A := by omega
          subst T
          simp only [complexWeightVariation, Finset.Icc_self,
            Finset.sum_singleton, complexUpperCutoffWeight,
            le_refl, if_pos, Nat.not_succ_le_self]
          have hsplit : w A = (w A - w (A + 1)) + w (A + 1) := by
            ring
          rw [hsplit]
          simpa [add_comm] using
            (norm_add_le (w A - w (A + 1)) (w (A + 1)))
      · have hTA : T < A := by omega
        have hAsucc : ¬ A + 1 ≤ T := by omega
        have hnotAlt : ¬ A < T := by omega
        simp [complexWeightVariation, complexUpperCutoffWeight,
          Nat.not_le.mpr hTA, hAsucc, hnotAlt]
        positivity
  | succ B hAB ih =>
      have hmono := complexWeightVariation_mono_right_succ w A B hAB
      by_cases hTB : T ≤ B
      · have hB1T : ¬ B + 1 ≤ T := by omega
        have hB2T : ¬ B + 2 ≤ T := by omega
        have hcut :
            complexWeightVariation (complexUpperCutoffWeight T w)
                A (B + 1) =
              complexWeightVariation (complexUpperCutoffWeight T w)
                A B := by
          unfold complexWeightVariation
          rw [Finset.sum_Icc_succ_top (by omega)]
          simp [complexUpperCutoffWeight, hB1T, hB2T]
        rw [hcut]
        exact ih.trans hmono
      · have hBT : B < T := by omega
        by_cases hT : T = B + 1
        · subst T
          have hB2 : ¬ B + 2 ≤ B + 1 := by omega
          have hcut :
              complexWeightVariation
                    (complexUpperCutoffWeight (B + 1) w) A (B + 1) =
                complexWeightVariation
                    (complexUpperCutoffWeight (B + 1) w) A B := by
            unfold complexWeightVariation
            rw [Finset.sum_Icc_succ_top (by omega)]
            simp [complexUpperCutoffWeight, hB2]
            ring
          rw [hcut]
          exact ih.trans hmono
        · have hB2T : B + 2 ≤ T := by omega
          unfold complexWeightVariation complexUpperCutoffWeight
          rw [if_pos hB2T]
          have hsum :
              (∑ n ∈ Finset.Icc A (B + 1),
                ‖(if n ≤ T then w n else 0) -
                  if n + 1 ≤ T then w (n + 1) else 0‖) ≤
                ∑ n ∈ Finset.Icc A (B + 1),
                  ‖w n - w (n + 1)‖ := by
            apply Finset.sum_le_sum
            intro n hn
            have hnB : n ≤ B + 1 := (Finset.mem_Icc.mp hn).2
            have hnT : n ≤ T := hnB.trans (by omega)
            have hnsuccT : n + 1 ≤ T := by omega
            simp [hnT, hnsuccT]
          exact add_le_add le_rfl hsum

/-- A nonnegative decreasing real weight has no hidden variation loss:
its endpoint-plus-variation mass telescopes exactly to its left endpoint.
This is the reusable analytic shape needed for the log taper and each
sign-stripped near-divisor amplitude. -/
theorem complexWeightVariation_ofReal_of_antitone
    (u : ℕ → ℝ) (A B : ℕ) (hAB : A ≤ B)
    (hu_nonneg : ∀ m, A ≤ m → 0 ≤ u m) (hu_antitone : Antitone u) :
    complexWeightVariation (fun m => (u m : ℂ)) A B = u A := by
  induction B, hAB using Nat.le_induction with
  | base =>
      unfold complexWeightVariation
      simp only [Finset.Icc_self, Finset.sum_singleton]
      have hdiff :
          ‖(u A : ℂ) - (u (A + 1) : ℂ)‖ = u A - u (A + 1) := by
        rw [← Complex.ofReal_sub]
        exact Complex.norm_of_nonneg
          (sub_nonneg.mpr (hu_antitone (Nat.le_succ _)))
      rw [Complex.norm_of_nonneg (hu_nonneg _ (by omega)), hdiff]
      ring
  | succ B hAB ih =>
      unfold complexWeightVariation at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hdiff :
          ‖(u (B + 1) : ℂ) - (u (B + 1 + 1) : ℂ)‖ =
            u (B + 1) - u (B + 1 + 1) := by
        rw [← Complex.ofReal_sub]
        exact Complex.norm_of_nonneg
          (sub_nonneg.mpr (hu_antitone (Nat.le_succ _)))
      rw [Complex.norm_of_nonneg (hu_nonneg _ (by omega)), hdiff]
      rw [Complex.norm_of_nonneg (hu_nonneg _ (by omega))] at ih
      calc
        u (B + 1 + 1) +
            (∑ x ∈ Finset.Icc A B,
              ‖(u x : ℂ) - (u (x + 1) : ℂ)‖ +
              (u (B + 1) - u (B + 1 + 1))) =
            u (B + 1) +
              ∑ x ∈ Finset.Icc A B,
                ‖(u x : ℂ) - (u (x + 1) : ℂ)‖ := by ring
        _ = u A := ih

theorem complexWeightVariation_sum_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w : ι → ℕ → ℂ) (A B : ℕ) :
    complexWeightVariation (fun m => ∑ i ∈ s, w i m) A B ≤
      ∑ i ∈ s, complexWeightVariation (w i) A B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [complexWeightVariation]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      refine (complexWeightVariation_add_le
        (w i) (fun m => ∑ j ∈ s, w j m) A B).trans ?_
      gcongr

/-! ## Monotonicity of the explicit taper amplitudes -/

/-- For a genuine logarithmic cutoff, the basic taper decreases with its
integer argument. -/
theorem logTaperWeight_antitone
    (N : ℕ) (hN : 2 ≤ N) : Antitone (weight N) := by
  intro a b hab
  rw [weight_of_two_le hN, weight_of_two_le hN]
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogab : Real.log (a : ℝ) ≤ Real.log (b : ℝ) := by
    by_cases ha : a = 0
    · subst a
      simpa using Real.log_natCast_nonneg b
    · exact Real.log_le_log
        (by exact_mod_cast (show 0 < a by omega))
        (by exact_mod_cast hab)
  have hdiv := div_le_div_of_nonneg_right hlogab hlogN.le
  linarith

/-- The taper is nonnegative up to its cutoff. -/
theorem logTaperWeight_nonneg_of_le
    (N m : ℕ) (hN : 2 ≤ N) (hmN : m ≤ N) :
    0 ≤ weight N m := by
  have hmono := logTaperWeight_antitone N hN hmN
  rw [weight_cutoff hN] at hmono
  exact hmono

/-- The outer dyadic average of logarithmic tapers is decreasing in the
MSTT variable. -/
theorem ehmDyadicLogTaperAverage_antitone
    (X : ℕ) (hX : 2 ≤ X) :
    Antitone (ehmDyadicLogTaperAverage X) := by
  classical
  intro a b hab
  unfold ehmDyadicLogTaperAverage
  apply Finset.sum_le_sum
  intro N hNmem
  have hN2 : 2 ≤ N := hX.trans (Finset.mem_Icc.mp hNmem).1
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  by_cases hbN : b ≤ N
  · have haN : a ≤ N := hab.trans hbN
    simp only [hbN, haN, if_true]
    exact div_le_div_of_nonneg_right
      (logTaperWeight_antitone N hN2 hab) hlogN.le
  · simp only [hbN, if_false]
    by_cases haN : a ≤ N
    · simp only [haN, if_true]
      exact div_nonneg (logTaperWeight_nonneg_of_le N a hN2 haN) hlogN.le
    · simp [haN]

/-- The sign-stripped near amplitude is a sum of nonnegative taper products.
This form exposes its monotonicity in the outer variable. -/
theorem ehmDyadicNearPairAmplitude_eq_sum
    (X m d : ℕ) :
    ehmDyadicNearPairAmplitude X m d =
      ∑ N ∈ ehmDyadicNBlock X,
        if m ≤ N then
          if N < d then (-weight N d) * weight N m else 0
        else 0 := by
  classical
  unfold ehmDyadicNearPairAmplitude ehmDyadicNearTaperPairAverage
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro N _
  by_cases hmN : m ≤ N <;> by_cases hNd : N < d
  all_goals simp [hmN, hNd]
  ring

/-- Each sign-stripped near-divisor amplitude decreases with the outer
MSTT variable. -/
theorem ehmDyadicNearPairAmplitude_antitone
    (X d : ℕ) (hX : 2 ≤ X) :
    Antitone (fun m => ehmDyadicNearPairAmplitude X m d) := by
  classical
  intro a b hab
  change ehmDyadicNearPairAmplitude X b d ≤
    ehmDyadicNearPairAmplitude X a d
  rw [ehmDyadicNearPairAmplitude_eq_sum,
    ehmDyadicNearPairAmplitude_eq_sum]
  apply Finset.sum_le_sum
  intro N hNmem
  have hN2 : 2 ≤ N := hX.trans (Finset.mem_Icc.mp hNmem).1
  by_cases hbN : b ≤ N
  · have haN : a ≤ N := hab.trans hbN
    simp only [hbN, haN, if_true]
    by_cases hNd : N < d
    · simp only [hNd, if_true]
      have hneg : 0 ≤ -weight N d := by
        have hmono := logTaperWeight_antitone N hN2 hNd.le
        rw [weight_cutoff hN2] at hmono
        linarith
      exact mul_le_mul_of_nonneg_left
        (logTaperWeight_antitone N hN2 hab) hneg
    · simp [hNd]
  · simp only [hbN, if_false]
    by_cases haN : a ≤ N
    · simp only [haN, if_true]
      by_cases hNd : N < d
      · simp only [hNd, if_true]
        exact mul_nonneg
          (by
            have hmono := logTaperWeight_antitone N hN2 hNd.le
            rw [weight_cutoff hN2] at hmono
            linarith)
          (logTaperWeight_nonneg_of_le N a hN2 haN)
      · simp [hNd]
    · simp [haN]

/-- On a positive block, the main taper's variation telescopes exactly to
its left endpoint. -/
theorem complexWeightVariation_ehmDyadicLogTaperAverage
    (X A B : ℕ) (hX : 2 ≤ X) (hA : 1 ≤ A) (hAB : A ≤ B) :
    complexWeightVariation
        (fun m => (ehmDyadicLogTaperAverage X m : ℂ)) A B =
      ehmDyadicLogTaperAverage X A := by
  apply complexWeightVariation_ofReal_of_antitone _ _ _ hAB
  · intro m hAm
    exact ehmDyadicLogTaperAverage_nonneg X m hX (hA.trans hAm)
  · exact ehmDyadicLogTaperAverage_antitone X hX

/-- The same exact telescoping identity holds for every sign-stripped near
divisor amplitude. -/
theorem complexWeightVariation_ehmDyadicNearPairAmplitude
    (X d A B : ℕ) (hX : 2 ≤ X) (hA : 1 ≤ A) (hAB : A ≤ B) :
    complexWeightVariation
        (fun m => (ehmDyadicNearPairAmplitude X m d : ℂ)) A B =
      ehmDyadicNearPairAmplitude X A d := by
  apply complexWeightVariation_ofReal_of_antitone _ _ _ hAB
  · intro m hAm
    exact ehmDyadicNearPairAmplitude_nonneg X m d hX (hA.trans hAm)
  · exact ehmDyadicNearPairAmplitude_antitone X d hX

/-! ## The exact paired-weight split -/

/-- The main part of one fixed-product MSTT weight. -/
noncomputable def ehmMSTTMainProductWeight
    (N n m : ℕ) : ℂ :=
  ((ehmDyadicLogTaperAverage N m *
    ArithmeticFunction.vonMangoldt n / (n : ℝ) : ℝ) : ℂ)

/-- The contribution of one near divisor to a fixed-product MSTT weight. -/
noncomputable def ehmMSTTNearDivisorProductWeight
    (N n d m : ℕ) : ℂ :=
  if d ∣ n then
    (((((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ehmDyadicNearPairAmplitude N m d) / (n : ℝ) : ℝ) : ℂ)
  else 0

/-- The variation of the main component is its scalar size times the left
endpoint of the decreasing dyadic taper. -/
theorem complexWeightVariation_ehmMSTTMainProductWeight
    (N n A B : ℕ) (hN : 2 ≤ N) (hA : 1 ≤ A) (hAB : A ≤ B) :
    complexWeightVariation (ehmMSTTMainProductWeight N n) A B =
      ‖(((ArithmeticFunction.vonMangoldt n / (n : ℝ) : ℝ) : ℂ))‖ *
        ehmDyadicLogTaperAverage N A := by
  have hfun :
      ehmMSTTMainProductWeight N n =
        fun m =>
          (((ArithmeticFunction.vonMangoldt n / (n : ℝ) : ℝ) : ℂ)) *
            (ehmDyadicLogTaperAverage N m : ℂ) := by
    funext m
    unfold ehmMSTTMainProductWeight
    push_cast
    ring
  rw [hfun, complexWeightVariation_const_mul,
    complexWeightVariation_ehmDyadicLogTaperAverage N A B hN hA hAB]

/-- A signed near-divisor component contributes the scalar norm times the
left endpoint of its sign-stripped decreasing amplitude. -/
theorem complexWeightVariation_ehmMSTTNearDivisorProductWeight
    (N n d A B : ℕ) (hN : 2 ≤ N) (hA : 1 ≤ A) (hAB : A ≤ B) :
    complexWeightVariation
        (ehmMSTTNearDivisorProductWeight N n d) A B =
      if d ∣ n then
        ‖((((ArithmeticFunction.moebius d : ℤ) : ℝ) / (n : ℝ) : ℝ) : ℂ)‖ *
          ehmDyadicNearPairAmplitude N A d
      else 0 := by
  classical
  by_cases hdn : d ∣ n
  · rw [if_pos hdn]
    have hfun :
        ehmMSTTNearDivisorProductWeight N n d =
          fun m =>
            (((((ArithmeticFunction.moebius d : ℤ) : ℝ) /
              (n : ℝ) : ℝ) : ℂ)) *
              (ehmDyadicNearPairAmplitude N m d : ℂ) := by
      funext m
      unfold ehmMSTTNearDivisorProductWeight
      simp only [hdn, if_true]
      push_cast
      ring
    rw [hfun, complexWeightVariation_const_mul,
      complexWeightVariation_ehmDyadicNearPairAmplitude
        N d A B hN hA hAB]
  · rw [if_neg hdn]
    have hzero :
        ehmMSTTNearDivisorProductWeight N n d = fun _ => 0 := by
      funext m
      simp [ehmMSTTNearDivisorProductWeight, hdn]
    rw [hzero]
    simp [complexWeightVariation]

/-- The explicit left-endpoint majorant remaining after the monotone taper
variations have telescoped. -/
noncomputable def ehmMSTTLowProductEndpointVariationMajorant
    (N D n A : ℕ) : ℝ :=
  ‖(((ArithmeticFunction.vonMangoldt n / (n : ℝ) : ℝ) : ℂ))‖ *
      ehmDyadicLogTaperAverage N A +
    ∑ d ∈ Finset.Icc (N + 1) D,
      if d ∣ n then
        ‖((((ArithmeticFunction.moebius d : ℤ) : ℝ) / (n : ℝ) : ℝ) : ℂ)‖ *
          ehmDyadicNearPairAmplitude N A d
      else 0

/-- Below the outer scale there are no retained near divisors: every near
divisor is strictly larger than `N`, hence cannot divide a positive
coordinate `n ≤ N`. -/
theorem ehmMSTTLowProductEndpointVariationMajorant_eq_main_of_le
    (N D n A : ℕ) (hnpos : 1 ≤ n) (hnN : n ≤ N) :
    ehmMSTTLowProductEndpointVariationMajorant N D n A =
      ‖(((ArithmeticFunction.vonMangoldt n / (n : ℝ) : ℝ) : ℂ))‖ *
        ehmDyadicLogTaperAverage N A := by
  classical
  unfold ehmMSTTLowProductEndpointVariationMajorant
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro d hd
  have hNd : N < d := by
    have := (Finset.mem_Icc.mp hd).1
    omega
  have hnd : n < d := hnN.trans_lt hNd
  have hnot : ¬d ∣ n := Nat.not_dvd_of_pos_of_lt (by omega) hnd
  simp [hnot]

/-- The paired weight is exactly its main component plus its signed near
divisor components. -/
theorem ehmMSTTLowProductWeight_eq_main_add_nearDivisors
    (N D n m : ℕ) :
    ehmMSTTLowProductWeight N D n m =
      ehmMSTTMainProductWeight N n m +
        ∑ d ∈ Finset.Icc (N + 1) D,
          ehmMSTTNearDivisorProductWeight N n d m := by
  classical
  unfold ehmMSTTLowProductWeight ehmMSTTMainProductWeight
    ehmMSTTNearDivisorProductWeight
    ehmDyadicVaalerPairedProductCoefficient
    ehmDyadicVaalerNearProductCoefficient
  push_cast
  rw [add_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  by_cases hdn : d ∣ n <;> simp [hdn]

/-- With `n ≤ N`, the whole low-product paired weight—not merely its
variation majorant—has no near-divisor component. -/
theorem ehmMSTTLowProductWeight_eq_main_of_le
    (N D n m : ℕ) (hnpos : 1 ≤ n) (hnN : n ≤ N) :
    ehmMSTTLowProductWeight N D n m =
      ehmMSTTMainProductWeight N n m := by
  rw [ehmMSTTLowProductWeight_eq_main_add_nearDivisors]
  simp only [add_eq_left]
  apply Finset.sum_eq_zero
  intro d hd
  have hNd : N < d := by
    have := (Finset.mem_Icc.mp hd).1
    omega
  have hnd : n < d := hnN.trans_lt hNd
  have hnot : ¬d ∣ n := Nat.not_dvd_of_pos_of_lt (by omega) hnd
  simp [ehmMSTTNearDivisorProductWeight, hnot]

/-- Gate 1 reduced to the variations of the explicit taper components.
This is an inequality before any asymptotic estimate or absolute divisor
bound is inserted. -/
theorem complexWeightVariation_ehmMSTTLowProductWeight_le_components
    (N D n A B : ℕ) :
    complexWeightVariation (ehmMSTTLowProductWeight N D n) A B ≤
      complexWeightVariation (ehmMSTTMainProductWeight N n) A B +
        ∑ d ∈ Finset.Icc (N + 1) D,
          complexWeightVariation
            (ehmMSTTNearDivisorProductWeight N n d) A B := by
  have hfun :
      ehmMSTTLowProductWeight N D n =
        fun m => ehmMSTTMainProductWeight N n m +
          ∑ d ∈ Finset.Icc (N + 1) D,
            ehmMSTTNearDivisorProductWeight N n d m := by
    funext m
    exact ehmMSTTLowProductWeight_eq_main_add_nearDivisors N D n m
  rw [hfun]
  refine (complexWeightVariation_add_le
    (ehmMSTTMainProductWeight N n)
    (fun m => ∑ d ∈ Finset.Icc (N + 1) D,
      ehmMSTTNearDivisorProductWeight N n d m) A B).trans ?_
  gcongr
  exact complexWeightVariation_sum_le (Finset.Icc (N + 1) D)
    (ehmMSTTNearDivisorProductWeight N n) A B

/-- Gate 1 in its first genuinely quantitative form: on a positive block,
the complete paired variation is bounded by one explicit endpoint
majorant.  No uniform-in-scale estimate for that majorant is asserted. -/
theorem complexWeightVariation_ehmMSTTLowProductWeight_le_endpointMajorant
    (N D n A B : ℕ) (hN : 2 ≤ N) (hA : 1 ≤ A) (hAB : A ≤ B) :
    complexWeightVariation (ehmMSTTLowProductWeight N D n) A B ≤
      ehmMSTTLowProductEndpointVariationMajorant N D n A := by
  calc
    complexWeightVariation (ehmMSTTLowProductWeight N D n) A B ≤
        complexWeightVariation (ehmMSTTMainProductWeight N n) A B +
          ∑ d ∈ Finset.Icc (N + 1) D,
            complexWeightVariation
              (ehmMSTTNearDivisorProductWeight N n d) A B :=
      complexWeightVariation_ehmMSTTLowProductWeight_le_components
        N D n A B
    _ = ehmMSTTLowProductEndpointVariationMajorant N D n A := by
      unfold ehmMSTTLowProductEndpointVariationMajorant
      rw [complexWeightVariation_ehmMSTTMainProductWeight
        N n A B hN hA hAB]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      exact complexWeightVariation_ehmMSTTNearDivisorProductWeight
        N n d A B hN hA hAB

/-- The full retained Gate-1 variation mass on one MSTT block. -/
noncomputable def ehmMSTTLowProductVariationMass
    (N D J Y A B : ℕ) : ℝ :=
  ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
    complexWeightVariation (ehmMSTTLowProductWeight N D n) A B

/-- Summing the componentwise Gate-1 reduction over every retained product
coordinate. -/
theorem ehmMSTTLowProductVariationMass_le_components
    (N D J Y A B : ℕ) :
    ehmMSTTLowProductVariationMass N D J Y A B ≤
      ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
        (complexWeightVariation (ehmMSTTMainProductWeight N n) A B +
          ∑ d ∈ Finset.Icc (N + 1) D,
            complexWeightVariation
              (ehmMSTTNearDivisorProductWeight N n d) A B) := by
  unfold ehmMSTTLowProductVariationMass
  apply Finset.sum_le_sum
  intro n _
  exact complexWeightVariation_ehmMSTTLowProductWeight_le_components
    N D n A B

/-- After summing over retained product coordinates, Gate 1 is reduced to
the explicit sum of left-endpoint majorants.  Establishing the required
dyadically normalized uniform bound for this finite expression is the
remaining analytic part of Gate 1. -/
theorem ehmMSTTLowProductVariationMass_le_endpointMajorants
    (N D J Y A B : ℕ) (hN : 2 ≤ N) (hA : 1 ≤ A) (hAB : A ≤ B) :
    ehmMSTTLowProductVariationMass N D J Y A B ≤
      ∑ n ∈ ehmDyadicVaalerLowProductRange J Y,
        ehmMSTTLowProductEndpointVariationMajorant N D n A := by
  unfold ehmMSTTLowProductVariationMass
  apply Finset.sum_le_sum
  intro n _
  exact
    complexWeightVariation_ehmMSTTLowProductWeight_le_endpointMajorant
      N D n A B hN hA hAB

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTVariation
