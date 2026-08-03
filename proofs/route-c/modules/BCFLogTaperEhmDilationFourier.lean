import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmL2Convergence
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Dynamics.Ergodic.AddCircle

/-!
# Fourier coefficients under integer dilation on the circle

This module proves the finite harmonic-analysis identity needed to identify
Ehm's concrete centered-sawtooth partial sums with their divisor-truncated
Fourier synthesis.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmDilationFourier

open MeasureTheory Real AddCircle Filter
open scoped BigOperators ENNReal ComplexConjugate
open RH.Criteria.NymanBeurling.BCFLogTaperEhmFourierBridge
open RH.Criteria.NymanBeurling.BCFLogTaperEhmIntegralSeriesAssembly
open RH.Criteria.NymanBeurling.BCFLogTaperEhmPeriodicL2
open RH.Criteria.NymanBeurling.BCFLogTaperEhmCoefficientConvergence
open RH.Criteria.NymanBeurling.BCFLogTaperEhmL2Convergence

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private theorem nsmul_inv_nat_eq_zero (k : ℕ) (hk : 0 < k) :
    k • ((1 / (k : ℝ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hk0, coe_period]

private theorem fourier_inv_nat_ne_one_of_not_dvd
    (k n : ℕ) (hk : 0 < k) (hkn : ¬k ∣ n) :
    @fourier 1 (-(n : ℤ))
      ((1 / (k : ℝ) : ℝ) : AddCircle (1 : ℝ)) ≠ 1 := by
  intro h
  have hconj := congrArg star h
  have hpos : @fourier 1 (n : ℤ)
      ((1 / (k : ℝ) : ℝ) : AddCircle (1 : ℝ)) = 1 := by
    simpa only [fourier_neg, map_one, starRingEnd_apply, star_star, star_one] using hconj
  rw [fourier_coe_apply] at hpos
  have hexp : Complex.exp
      (2 * Real.pi * Complex.I * (n : ℂ) / (k : ℂ)) = 1 := by
    convert hpos using 2 <;> norm_num
    field_simp
  exact hkn ((Complex.exp_two_pi_mul_I_mul_div_eq_one_iff
    (N := k) (k := n) (Nat.ne_of_gt hk)).mp hexp)

private theorem fourierCoeff_nsmul_eq_zero_of_not_dvd
    (f : AddCircle (1 : ℝ) → ℂ) (k n : ℕ) (hk : 0 < k)
    (hkn : ¬k ∣ n) :
    fourierCoeff (fun x => f (k • x)) (n : ℤ) = 0 := by
  let y : AddCircle (1 : ℝ) := ((1 / (k : ℝ) : ℝ) : AddCircle (1 : ℝ))
  let c : ℂ := fourier (-(n : ℤ)) y
  let F : AddCircle (1 : ℝ) → ℂ := fun x => fourier (-(n : ℤ)) x * f (k • x)
  have hy : k • y = 0 := nsmul_inv_nat_eq_zero k hk
  have hc : c ≠ 1 := fourier_inv_nat_ne_one_of_not_dvd k n hk hkn
  have htranslate (x : AddCircle (1 : ℝ)) : F (x + y) = c * F x := by
    change fourier (-(n : ℤ)) (x + y) * f (k • (x + y)) =
      fourier (-(n : ℤ)) y * (fourier (-(n : ℤ)) x * f (k • x))
    simp only [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul,
      nsmul_add, hy, add_zero]
    ring
  have hint := integral_add_right_eq_self
    (μ := AddCircle.haarAddCircle) F y
  simp_rw [htranslate, integral_const_mul] at hint
  unfold fourierCoeff
  simp only [smul_eq_mul]
  exact eq_zero_of_mul_eq_self_left hc hint

private theorem measurePreserving_nsmul (k : ℕ) (hk : 0 < k) :
    MeasurePreserving (fun x : AddCircle (1 : ℝ) => k • x)
      AddCircle.haarAddCircle AddCircle.haarAddCircle := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk)) with h | h
  · subst k
    simpa only [one_nsmul] using
      (MeasurePreserving.id
        (@AddCircle.haarAddCircle (1 : ℝ) inferInstance))
  · let H := (AddCircle.ergodic_nsmul (T := (1 : ℝ)) h).toMeasurePreserving
    have hv : (volume : Measure (AddCircle (1 : ℝ))) =
        (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
      simpa using
        (@AddCircle.volume_eq_smul_haarAddCircle (1 : ℝ) inferInstance)
    refine ⟨H.measurable, ?_⟩
    calc
      Measure.map (fun x : AddCircle (1 : ℝ) => k • x)
          AddCircle.haarAddCircle =
          Measure.map (fun x : AddCircle (1 : ℝ) => k • x) volume := by rw [hv]
      _ = volume := H.map_eq
      _ = AddCircle.haarAddCircle := hv

private theorem fourierCoeff_nsmul_of_dvd
    (f : AddCircle (1 : ℝ) → ℂ)
    (hf : AEStronglyMeasurable f AddCircle.haarAddCircle)
    (k n : ℕ) (hk : 0 < k) (hkn : k ∣ n) :
    fourierCoeff (fun x => f (k • x)) (n : ℤ) =
      fourierCoeff f (n / k : ℕ) := by
  obtain ⟨r, rfl⟩ := hkn
  have hdiv : k * r / k = r := Nat.mul_div_right r hk
  rw [hdiv]
  let G : AddCircle (1 : ℝ) → ℂ :=
    fun y => fourier (-(r : ℤ)) y * f y
  let p : AddCircle (1 : ℝ) → AddCircle (1 : ℝ) := fun x => k • x
  have hG : AEStronglyMeasurable G AddCircle.haarAddCircle :=
    (map_continuous (fourier (-(r : ℤ)))).aestronglyMeasurable.mul hf
  have hp : MeasurePreserving p AddCircle.haarAddCircle AddCircle.haarAddCircle :=
    measurePreserving_nsmul k hk
  have hmap :
      (∫ y, G y ∂Measure.map p AddCircle.haarAddCircle) =
        ∫ x, G (p x) ∂AddCircle.haarAddCircle :=
    MeasureTheory.integral_map hp.aemeasurable (by simpa [hp.map_eq] using hG)
  rw [hp.map_eq] at hmap
  have hphase (x : AddCircle (1 : ℝ)) :
      fourier (-(↑(k * r) : ℤ)) x = fourier (-(r : ℤ)) (k • x) := by
    simp only [fourier_apply]
    apply congrArg (fun y : AddCircle (1 : ℝ) =>
      ((@toCircle (1 : ℝ) y : Circle) : ℂ))
    calc
      (-(↑(k * r) : ℤ)) • x = -((k * r) • x) := by
        rw [neg_zsmul, natCast_zsmul]
      _ = -(r • (k • x)) := by rw [mul_nsmul]
      _ = (-(r : ℤ)) • (k • x) := by rw [neg_zsmul, natCast_zsmul]
  unfold fourierCoeff
  simp only [smul_eq_mul]
  rw [show (∫ x, fourier (-((k * r : ℕ) : ℤ)) x * f (k • x)
        ∂AddCircle.haarAddCircle) = ∫ x, G (p x) ∂AddCircle.haarAddCircle by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change fourier (-((k * r : ℕ) : ℤ)) x * f (k • x) =
          fourier (-(r : ℤ)) (k • x) * f (k • x)
        rw [hphase x]]
  exact hmap.symm

private theorem ehmCenteredSawtooth_periodic :
    Function.Periodic
      (fun x : ℝ => ((Int.fract x - (1 / 2 : ℝ) : ℝ) : ℂ)) 1 := by
  intro x
  change ((Int.fract (x + 1) - (1 / 2 : ℝ) : ℝ) : ℂ) =
    ((Int.fract x - (1 / 2 : ℝ) : ℝ) : ℂ)
  rw [Int.fract_add_one]

private theorem liftIoc_eq_periodicLift
    {f : ℝ → ℂ} (hf : Function.Periodic f 1) :
    AddCircle.liftIoc (p := (1 : ℝ)) 0 f = hf.lift := by
  funext x
  let y := AddCircle.equivIoc 1 0 x
  have hy : ((y : ℝ) : AddCircle (1 : ℝ)) = x := by
    exact AddCircle.coe_equivIoc
  calc
    AddCircle.liftIoc (p := (1 : ℝ)) 0 f x = f (y : ℝ) := by
      rw [← hy, AddCircle.liftIoc_coe_apply]
      exact y.property
    _ = hf.lift ((y : ℝ) : AddCircle (1 : ℝ)) := (hf.lift_coe _).symm
    _ = hf.lift x := by rw [hy]

private theorem ehmCenteredSawtoothCircle_eq_periodicLift :
    ehmCenteredSawtoothCircle = ehmCenteredSawtooth_periodic.lift := by
  exact liftIoc_eq_periodicLift ehmCenteredSawtooth_periodic

private theorem ehmCenteredSawtoothCircle_real (x : AddCircle (1 : ℝ)) :
    star (ehmCenteredSawtoothCircle x) = ehmCenteredSawtoothCircle x := by
  rw [ehmCenteredSawtoothCircle_eq_periodicLift]
  obtain ⟨y, hy, rfl⟩ := AddCircle.eq_coe_Ioc x
  rw [ehmCenteredSawtooth_periodic.lift_coe]
  simp

private theorem ehmCenteredSawtoothCircle_memLp :
    MemLp ehmCenteredSawtoothCircle 2 AddCircle.haarAddCircle := by
  have hIoc : MemLp
      (fun x : ℝ => ((Int.fract x - (1 / 2 : ℝ) : ℝ) : ℂ)) 2
      (volume.restrict (Set.Ioc 0 (0 + (1 : ℝ)))) := by
    apply MemLp.of_bound
    · exact (by fun_prop : AEStronglyMeasurable
        (fun x : ℝ => ((Int.fract x - (1 / 2 : ℝ) : ℝ) : ℂ))
        (volume.restrict (Set.Ioc 0 (0 + (1 : ℝ)))))
    · filter_upwards with x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;>
        linarith [Int.fract_nonneg x, (Int.fract_lt_one x).le]
  exact hIoc.memLp_liftIoc.haarAddCircle

private theorem ehmCenteredSawtoothCircle_fourierCoeff (m : ℤ) :
    fourierCoeff ehmCenteredSawtoothCircle m =
      if m = 0 then 0 else Complex.I / (2 * Real.pi * (m : ℂ)) := by
  rw [ehmCenteredSawtoothCircle]
  rw [fourierCoeff_liftIoc_eq]
  simpa using ehmCenteredSawtooth_fourierCoeffOn m

private theorem fourierCoeff_neg_of_real
    (f : AddCircle (1 : ℝ) → ℂ)
    (hreal : ∀ x, star (f x) = f x) (n : ℤ) :
    fourierCoeff f (-n) = star (fourierCoeff f n) := by
  unfold fourierCoeff
  change (∫ t : AddCircle (1 : ℝ), fourier (-(-n)) t * f t
      ∂AddCircle.haarAddCircle) =
    conj (∫ t : AddCircle (1 : ℝ), fourier (-n) t * f t
      ∂AddCircle.haarAddCircle)
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [neg_neg, map_mul, hreal x,
      starRingEnd_apply, fourier_neg, star_star]

private theorem fourierCoeff_centered_nsmul_neg
    (k n : ℕ) :
    fourierCoeff (fun x => ehmCenteredSawtoothCircle (k • x)) (-(n : ℤ)) =
      star (fourierCoeff
        (fun x => ehmCenteredSawtoothCircle (k • x)) (n : ℤ)) := by
  apply fourierCoeff_neg_of_real
  intro x
  exact ehmCenteredSawtoothCircle_real (k • x)

private theorem ehmCenteredSawtoothCircle_nsmul_coe (k : ℕ) (x : ℝ) :
    ehmCenteredSawtoothCircle (k • (x : AddCircle (1 : ℝ))) =
      ((Int.fract ((k : ℝ) * x) - (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [ehmCenteredSawtoothCircle_eq_periodicLift]
  rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul,
    ehmCenteredSawtooth_periodic.lift_coe]

private theorem ehmPhi1PartialCircle_eq_row_sum (K : ℕ) :
    ehmPhi1PartialCircle K =
      ∑ k ∈ Finset.Icc 1 K, fun x : AddCircle (1 : ℝ) =>
        ((1 / (k : ℝ) : ℝ) : ℂ) * ehmCenteredSawtoothCircle (k • x) := by
  funext x
  obtain ⟨y, hy, rfl⟩ := AddCircle.eq_coe_Ioc x
  rw [ehmPhi1PartialCircle, AddCircle.liftIoc_coe_apply (by simpa using hy)]
  unfold ehmPhi1Partial ehmCenteredFractionalPart
  simp_rw [Finset.sum_apply, ehmCenteredSawtoothCircle_nsmul_coe]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  field_simp

private theorem card_Icc_dvd_eq_truncatedDivisorCount
    (K n : ℕ) (hn : 0 < n) :
    ((Finset.Icc 1 K).filter fun k => k ∣ n).card =
      ehmTruncatedDivisorCount K n := by
  unfold ehmTruncatedDivisorCount
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rw [Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hk1, hkK⟩, hkn⟩
    exact ⟨⟨hkn, hn.ne'⟩, hkK⟩
  · rintro ⟨⟨hkn, _hn0⟩, hkK⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun hk0 => by
      subst k
      exact hn.ne' (zero_dvd_iff.mp hkn)), hkK⟩, hkn⟩

private theorem weightedRow_integrable (k : ℕ) (hk : 0 < k) :
    Integrable (fun x : AddCircle (1 : ℝ) =>
      ((1 / (k : ℝ) : ℝ) : ℂ) * ehmCenteredSawtoothCircle (k • x))
      AddCircle.haarAddCircle := by
  have hcomp := ehmCenteredSawtoothCircle_memLp.comp_measurePreserving
    (measurePreserving_nsmul k hk)
  have hmul := hcomp.const_mul (((1 / (k : ℝ) : ℝ) : ℂ))
  have hmul' : MemLp (fun x : AddCircle (1 : ℝ) =>
      ((1 / (k : ℝ) : ℝ) : ℂ) * ehmCenteredSawtoothCircle (k • x)) 2
      AddCircle.haarAddCircle := by
    simpa [Function.comp_def] using hmul
  exact hmul'.integrable (by norm_num)

private theorem weightedRow_fourierCoeff_pos
    (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    fourierCoeff (fun x : AddCircle (1 : ℝ) =>
      ((1 / (k : ℝ) : ℝ) : ℂ) * ehmCenteredSawtoothCircle (k • x)) (n : ℤ) =
      if k ∣ n then Complex.I / (2 * Real.pi * (n : ℂ)) else 0 := by
  rw [fourierCoeff.const_mul]
  split_ifs with hkn
  · rw [fourierCoeff_nsmul_of_dvd ehmCenteredSawtoothCircle
      ehmCenteredSawtoothCircle_memLp.1 k n hk hkn]
    have hdiv0 : ((n / k : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.div_pos (Nat.le_of_dvd hn hkn) hk).ne'
    rw [ehmCenteredSawtoothCircle_fourierCoeff, if_neg hdiv0]
    obtain ⟨r, rfl⟩ := hkn
    have hr : 0 < r := Nat.pos_of_mul_pos_left hn
    rw [Nat.mul_div_right r hk]
    push_cast
    field_simp [Real.pi_ne_zero, Nat.ne_of_gt hk, Nat.ne_of_gt hr]
  · rw [fourierCoeff_nsmul_eq_zero_of_not_dvd _ k n hk hkn]
    simp

private theorem weightedRow_fourierCoeff_zero (k : ℕ) (hk : 0 < k) :
    fourierCoeff (fun x : AddCircle (1 : ℝ) =>
      ((1 / (k : ℝ) : ℝ) : ℂ) * ehmCenteredSawtoothCircle (k • x)) 0 = 0 := by
  rw [fourierCoeff.const_mul]
  have hrow := fourierCoeff_nsmul_of_dvd ehmCenteredSawtoothCircle
    ehmCenteredSawtoothCircle_memLp.1 k 0 hk (dvd_zero k)
  rw [show fourierCoeff
      (fun x : AddCircle (1 : ℝ) => ehmCenteredSawtoothCircle (k • x)) 0 =
      fourierCoeff ehmCenteredSawtoothCircle 0 by simpa using hrow]
  simp [ehmCenteredSawtoothCircle_fourierCoeff]

private theorem ehmPhi1PartialCircle_fourierCoeff_pos
    (K n : ℕ) (hn : 0 < n) :
    fourierCoeff (ehmPhi1PartialCircle K) (n : ℤ) =
      Complex.I *
        ((ehmTruncatedDivisorCount K n : ℝ) /
          (2 * Real.pi * (n : ℝ)) : ℂ) := by
  rw [ehmPhi1PartialCircle_eq_row_sum]
  have hsum := fourierCoeff.sum (T := (1 : ℝ))
    (Finset.Icc 1 K)
    (fun k x => ((1 / (k : ℝ) : ℝ) : ℂ) *
      ehmCenteredSawtoothCircle (k • x))
    (fun k hk => weightedRow_integrable k
      (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1))
  rw [congrFun hsum (n : ℤ)]
  simp only [Finset.sum_apply]
  rw [show (∑ k ∈ Finset.Icc 1 K,
      fourierCoeff (fun x : AddCircle (1 : ℝ) =>
        ((1 / (k : ℝ) : ℝ) : ℂ) * ehmCenteredSawtoothCircle (k • x)) (n : ℤ)) =
      ∑ k ∈ Finset.Icc 1 K,
        if k ∣ n then Complex.I / (2 * Real.pi * (n : ℂ)) else 0 by
    apply Finset.sum_congr rfl
    intro k hk
    exact weightedRow_fourierCoeff_pos k n
      (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1) hn]
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, card_Icc_dvd_eq_truncatedDivisorCount K n hn]
  simp only [nsmul_eq_mul]
  push_cast
  field_simp [Real.pi_ne_zero, Nat.ne_of_gt hn]

private theorem ehmPhi1PartialCircle_fourierCoeff_zero (K : ℕ) :
    fourierCoeff (ehmPhi1PartialCircle K) 0 = 0 := by
  rw [ehmPhi1PartialCircle_eq_row_sum]
  have hsum := fourierCoeff.sum (T := (1 : ℝ))
    (Finset.Icc 1 K)
    (fun k x => ((1 / (k : ℝ) : ℝ) : ℂ) *
      ehmCenteredSawtoothCircle (k • x))
    (fun k hk => weightedRow_integrable k
      (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1))
  rw [congrFun hsum 0]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  exact weightedRow_fourierCoeff_zero k
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1)

private theorem ehmPhi1PartialCircle_real (K : ℕ) (x : AddCircle (1 : ℝ)) :
    star (ehmPhi1PartialCircle K x) = ehmPhi1PartialCircle K x := by
  rw [ehmPhi1PartialCircle_eq_row_sum]
  simp only [Finset.sum_apply]
  change (starRingEnd ℂ) (∑ k ∈ Finset.Icc 1 K,
      ((1 / (k : ℝ) : ℝ) : ℂ) * ehmCenteredSawtoothCircle (k • x)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change star (((1 / (k : ℝ) : ℝ) : ℂ) *
      ehmCenteredSawtoothCircle (k • x)) =
    ((1 / (k : ℝ) : ℝ) : ℂ) * ehmCenteredSawtoothCircle (k • x)
  rw [star_mul, ehmCenteredSawtoothCircle_real]
  rw [show star (((1 / (k : ℝ) : ℝ) : ℂ)) =
      (((1 / (k : ℝ) : ℝ) : ℂ)) by
    exact Complex.conj_ofReal _]
  ring

private theorem fourierCoeff_ehmPhi1PartialL2_eq_circle (K : ℕ) (m : ℤ) :
    fourierCoeff (ehmPhi1PartialL2 K) m =
      fourierCoeff (ehmPhi1PartialCircle K) m := by
  exact congrFun (fourierCoeff_congr_ae
    (ehmPhi1PartialCircle_memLp K).coeFn_toLp) m

/-- Exact finite Fourier identification for Ehm's concrete centered-sawtooth
partials.  At frequency `n ≠ 0`, precisely the positive divisors of `|n|`
below the row cutoff contribute. -/
theorem ehmFiniteSawtoothFourierIdentification :
    EhmFiniteSawtoothFourierIdentification where
  coefficient K m := by
    rw [fourierCoeff_ehmPhi1PartialL2_eq_circle]
    cases m with
    | ofNat n =>
        cases n with
        | zero =>
            change fourierCoeff (ehmPhi1PartialCircle K) 0 = 0
            exact ehmPhi1PartialCircle_fourierCoeff_zero K
        | succ n =>
            change fourierCoeff (ehmPhi1PartialCircle K) ((n + 1 : ℕ) : ℤ) =
              Complex.I * (ehmPartialPositiveComplexAmplitude K n : ℂ)
            rw [ehmPhi1PartialCircle_fourierCoeff_pos K (n + 1) (by omega)]
            unfold ehmPartialPositiveComplexAmplitude
            push_cast
            rfl
    | negSucc n =>
        change fourierCoeff (ehmPhi1PartialCircle K) (-((n + 1 : ℕ) : ℤ)) =
          -Complex.I * (ehmPartialPositiveComplexAmplitude K n : ℂ)
        rw [fourierCoeff_neg_of_real (ehmPhi1PartialCircle K)
          (ehmPhi1PartialCircle_real K) ((n + 1 : ℕ) : ℤ)]
        rw [ehmPhi1PartialCircle_fourierCoeff_pos K (n + 1) (by omega)]
        unfold ehmPartialPositiveComplexAmplitude
        let q : ℝ := (ehmTruncatedDivisorCount K (n + 1) : ℝ) /
          (2 * Real.pi * (n + 1 : ℝ))
        have hq :
            (((ehmTruncatedDivisorCount K (n + 1) : ℝ) : ℂ) /
                (2 * (Real.pi : ℂ) * (((n + 1 : ℕ) : ℝ) : ℂ))) = (q : ℂ) := by
          dsimp [q]
          push_cast
          rfl
        rw [hq]
        change star (Complex.I * (q : ℂ)) = -Complex.I * (q : ℂ)
        rw [star_mul]
        rw [show star (q : ℂ) = (q : ℂ) by exact Complex.conj_ofReal q]
        rw [show star Complex.I = -Complex.I by exact Complex.conj_I]
        ring

/-- Week-1 milestone: the concrete finite Ehm sums converge in circle `L²`
to the divisor-coefficient periodic kernel. -/
theorem ehmPhi1L2Convergence :
    Tendsto ehmPhi1PartialL2 atTop (nhds periodicEhmKernelL2) :=
  BCFLogTaperEhmL2Convergence.ehmPhi1L2Convergence
    ehmFiniteSawtoothFourierIdentification

end RH.Criteria.NymanBeurling.BCFLogTaperEhmDilationFourier
