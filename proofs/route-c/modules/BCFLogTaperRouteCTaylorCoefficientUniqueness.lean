import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFiniteTransferSeries
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorDerivativeBridge

/-!
# Route C: coefficient uniqueness from the positive contour germ

The exact finite contour expansion is known only on the positive real germ,
where its remainder is smaller than every prescribed finite Taylor order.
This file proves that such one-sided information nevertheless determines all
coefficients of a holomorphic scalar power series.  Applying that uniqueness
lemma to the native Taylor series and the finite contour model proves the
complete Bettin--Conrey derivative identification.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCoefficientUniqueness

open Complex ENNReal Filter Set Topology Asymptotics
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorAnalytic
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorDerivativeBridge
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorElementaryTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorFiniteTransferSeries
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorGeneralCoefficient
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorRemainderOrder
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorThreeTermTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorTransferredRemainder

/-! ## The finite analytic comparison model -/

noncomputable def routeCTaylorFiniteCandidateCoefficient
    (M m : ℕ) : ℂ :=
  routeCTaylorElementarySeriesCoefficient m +
    ∑ n ∈ Finset.Icc 1 M, routeCTaylorOneResidueScalarCoefficient n m

noncomputable def routeCTaylorFiniteCandidateSeries
    (M : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (routeCTaylorFiniteCandidateCoefficient M)

noncomputable def routeCTaylorFiniteCandidateFunction
    (M : ℕ) (z : ℂ) : ℂ :=
  routeCTaylorElementaryModel z + routeCTaylorFinitePolynomialTransfer z M

theorem hasSum_routeCTaylorFiniteCandidate
    (M : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum
      (fun m => routeCTaylorFiniteCandidateCoefficient M m * z ^ m)
      (routeCTaylorFiniteCandidateFunction M z) := by
  convert (hasSum_routeCTaylorElementarySeries z hz).add
    (hasSum_routeCTaylorFinitePolynomialTransfer z hz M) using 1
  funext m
  unfold routeCTaylorFiniteCandidateCoefficient
  ring

theorem routeCTaylorFiniteCandidateSeries_radius_ge_one (M : ℕ) :
    (1 : ℝ≥0∞) ≤ (routeCTaylorFiniteCandidateSeries M).radius := by
  refine le_of_forall_nnreal_lt fun r hr => ?_
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have hrreal : (r : ℝ) < 1 := by simpa using hr
  have hz : ‖((r : ℝ) : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_of_nonneg r.coe_nonneg] using hrreal
  have hs :=
    (hasSum_routeCTaylorFiniteCandidate M ((r : ℝ) : ℂ) hz).summable.norm
  simpa [routeCTaylorFiniteCandidateSeries,
    FormalMultilinearSeries.ofScalars_norm, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg r.coe_nonneg] using hs

theorem routeCTaylorFiniteCandidate_hasFPowerSeriesAt (M : ℕ) :
    HasFPowerSeriesAt (routeCTaylorFiniteCandidateFunction M)
      (routeCTaylorFiniteCandidateSeries M) 0 := by
  refine ⟨1, {
    r_le := routeCTaylorFiniteCandidateSeries_radius_ge_one M
    r_pos := by norm_num
    hasSum := ?_ }⟩
  intro z hz
  rw [zero_add]
  have hznorm : ‖z‖ < 1 := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right] at hz
    simpa only [ENNReal.ofReal_lt_one] using hz
  exact HasSum.congr_fun
    (hasSum_routeCTaylorFiniteCandidate M z hznorm) fun n => by
      simp [routeCTaylorFiniteCandidateSeries, mul_comm]

/-! ## Positive-ray coefficient uniqueness -/

theorem norm_ofReal_pow_isLittleO_pow {k n : ℕ} (hkn : k < n) :
    (fun x : ℝ => ‖(x : ℂ)‖ ^ n) =o[routeCTaylorPositiveAtZero]
      (fun x : ℝ => (x : ℂ) ^ k) := by
  apply IsLittleO.of_norm_norm
  have hreal : (fun x : ℝ => x ^ n) =o[𝓝 0]
      (fun x : ℝ => x ^ k) := isLittleO_pow_pow hkn
  have hrestrict :=
    hreal.mono (inf_le_left : routeCTaylorPositiveAtZero ≤ 𝓝 0)
  apply hrestrict.congr'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _),
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]

/-- A scalar holomorphic germ that is `o(x^n)` on the positive ray has zero
coefficient in degree `n`.  Strong induction simultaneously removes all
lower modes. -/
theorem ofScalars_coefficient_eq_zero_of_positive_isLittleO
    (c : ℕ → ℂ) (f : ℂ → ℂ)
    (hp : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) 0)
    (n : ℕ)
    (hsmall : (fun x : ℝ => f (x : ℂ)) =o[routeCTaylorPositiveAtZero]
      (fun x : ℝ => (x : ℂ) ^ n)) :
    c n = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have happrox := hp.isBigO_sub_partialSum_pow (n + 1)
      have ht : Tendsto (fun x : ℝ => (x : ℂ))
          routeCTaylorPositiveAtZero (𝓝 0) :=
        (Complex.continuous_ofReal.tendsto 0).mono_left inf_le_left
      have hcomp := happrox.comp_tendsto ht
      have herror :
          (fun x : ℝ =>
            f (x : ℂ) -
              (FormalMultilinearSeries.ofScalars ℂ c).partialSum
                (n + 1) (x : ℂ)) =o[routeCTaylorPositiveAtZero]
            (fun x : ℝ => (x : ℂ) ^ n) := by
        simpa [Function.comp_def] using
          hcomp.trans_isLittleO
            (norm_ofReal_pow_isLittleO_pow (Nat.lt_succ_self n))
      have hpartialRaw := hsmall.sub herror
      have hpartial :
          (fun x : ℝ =>
            (FormalMultilinearSeries.ofScalars ℂ c).partialSum
              (n + 1) (x : ℂ)) =o[routeCTaylorPositiveAtZero]
            (fun x : ℝ => (x : ℂ) ^ n) := by
        refine hpartialRaw.congr' ?_ EventuallyEq.rfl
        filter_upwards with x
        ring
      have hmonomial :
          (fun x : ℝ => c n * (x : ℂ) ^ n) =o[
            routeCTaylorPositiveAtZero] (fun x : ℝ => (x : ℂ) ^ n) := by
        refine hpartial.congr' ?_ EventuallyEq.rfl
        filter_upwards with x
        simp only [FormalMultilinearSeries.partialSum,
          FormalMultilinearSeries.ofScalars_apply_eq]
        rw [Finset.sum_eq_single n]
        · simp
        · intro k hk hkn
          have hkn' : k < n := by
            have hklt : k < n + 1 := Finset.mem_range.mp hk
            omega
          have hsmallk : (fun x : ℝ => f (x : ℂ)) =o[
              routeCTaylorPositiveAtZero] (fun x : ℝ => (x : ℂ) ^ k) :=
            hsmall.trans (by
              apply IsLittleO.of_norm_norm
              apply (norm_ofReal_pow_isLittleO_pow hkn').norm_norm.congr_left
              intro y
              simp [norm_pow])
          rw [ih k hkn' hsmallk]
          simp
        · simp
      by_contra hc
      have hirr :
          (fun x : ℝ => (x : ℂ) ^ n) =o[routeCTaylorPositiveAtZero]
            (fun x : ℝ => (x : ℂ) ^ n) :=
        (isLittleO_const_mul_left_iff hc).mp hmonomial
      have hne : ∀ᶠ x : ℝ in routeCTaylorPositiveAtZero,
          (x : ℂ) ^ n ≠ 0 := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hx.ne')
      letI : NeBot routeCTaylorPositiveAtZero := by
        unfold routeCTaylorPositiveAtZero
        exact nhdsWithin_Ioi_neBot le_rfl
      exact isLittleO_irrefl hne.frequently hirr

/-! ## Comparison with the native central period -/

noncomputable def routeCTaylorFiniteDeltaCoefficient
    (M m : ℕ) : ℂ :=
  iteratedDeriv m bettinConreyPsiZeroTaylorFunction 0 / m.factorial -
    routeCTaylorFiniteCandidateCoefficient M m

noncomputable def routeCTaylorFiniteDeltaFunction
    (M : ℕ) (z : ℂ) : ℂ :=
  bettinConreyPsiZeroTaylorFunction z - routeCTaylorFiniteCandidateFunction M z

theorem routeCTaylorFiniteDelta_hasFPowerSeriesAt (M : ℕ) :
    HasFPowerSeriesAt (routeCTaylorFiniteDeltaFunction M)
      (FormalMultilinearSeries.ofScalars ℂ
        (routeCTaylorFiniteDeltaCoefficient M)) 0 := by
  have h := bettinConreyPsiZeroNativeTaylorSeries_hasFPowerSeriesAt.sub
    (routeCTaylorFiniteCandidate_hasFPowerSeriesAt M)
  change HasFPowerSeriesAt
    (bettinConreyPsiZeroTaylorFunction - routeCTaylorFiniteCandidateFunction M)
    (FormalMultilinearSeries.ofScalars ℂ
      (fun m => iteratedDeriv m bettinConreyPsiZeroTaylorFunction 0 /
        m.factorial - routeCTaylorFiniteCandidateCoefficient M m)) 0
  have heq :
      FormalMultilinearSeries.ofScalars ℂ
          (fun m => iteratedDeriv m bettinConreyPsiZeroTaylorFunction 0 /
            m.factorial - routeCTaylorFiniteCandidateCoefficient M m) =
        bettinConreyPsiZeroNativeTaylorSeries -
          routeCTaylorFiniteCandidateSeries M := by
    rw [bettinConreyPsiZeroNativeTaylorSeries,
      routeCTaylorFiniteCandidateSeries,
      ← FormalMultilinearSeries.ofScalars_sub]
    rfl
  rw [heq]
  exact h

theorem routeCTaylorFiniteDelta_ofReal_isLittleO
    (M : ℕ) (hM : 1 ≤ M) (d : ℕ)
    (hd : (d : ℝ) < routeCTaylorRemainderExponent M) :
    (fun x : ℝ => routeCTaylorFiniteDeltaFunction M (x : ℂ)) =o[
      routeCTaylorPositiveAtZero] (fun x : ℝ => (x : ℂ) ^ d) := by
  have hrem := routeCTaylorFiniteRemainderTransfer_ofReal_isLittleO
    M hM d hd
  apply hrem.congr'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    unfold routeCTaylorFiniteDeltaFunction routeCTaylorFiniteCandidateFunction
    rw [bettinConreyPsiZeroTaylorFunction_ofReal_eq_finiteTransfer x hx M hM,
      routeCTaylorRawElementaryTransfer_ofReal_eq_model x hx]
    ring
  · exact EventuallyEq.rfl

theorem bettinConreyPsiZeroNativeCoefficient_eq_finiteCandidate
    (M : ℕ) (hM : 1 ≤ M) (m : ℕ)
    (hm : (m : ℝ) < routeCTaylorRemainderExponent M) :
    iteratedDeriv m bettinConreyPsiZeroTaylorFunction 0 / m.factorial =
      routeCTaylorFiniteCandidateCoefficient M m := by
  have hzero := ofScalars_coefficient_eq_zero_of_positive_isLittleO
    (routeCTaylorFiniteDeltaCoefficient M)
    (routeCTaylorFiniteDeltaFunction M)
    (routeCTaylorFiniteDelta_hasFPowerSeriesAt M) m
    (routeCTaylorFiniteDelta_ofReal_isLittleO M hM m hm)
  exact sub_eq_zero.mp hzero

theorem routeCTaylorFiniteCandidateCoefficient_one :
    routeCTaylorFiniteCandidateCoefficient 1 1 = 0 := by
  norm_num [routeCTaylorFiniteCandidateCoefficient,
    routeCTaylorElementarySeriesCoefficient,
    routeCTaylorOneResidueScalarCoefficient,
    routeCTaylorInversePowerCoefficient]

theorem routeCTaylorFiniteCandidateCoefficient_self_eq_scalar
    (m : ℕ) (hm : 2 ≤ m) :
    routeCTaylorFiniteCandidateCoefficient m m =
      bettinConreyPsiZeroTaylorScalarCoefficient m := by
  unfold routeCTaylorFiniteCandidateCoefficient
  rw [routeCTaylorElementarySeriesCoefficient_of_two_le m hm,
    sum_routeCTaylorOneResidueScalarCoefficient_eq_residueBinomial m hm,
    routeCTaylorScalarCoefficient_eq_elementary_add_residue m hm]

/-- **Completed classical Taylor coefficient theorem.**  The native
derivative coefficient of the normalized central period is the exact
Bettin--Conrey Bernoulli--zeta coefficient in every degree. -/
theorem bettinConreyPsiZeroTaylorDerivativeIdentification_proved :
    BettinConreyPsiZeroTaylorDerivativeIdentification := by
  intro m
  rcases m with _ | m
  · exact bettinConreyPsiZeroTaylorDerivativeIdentification_zero
  by_cases hm0 : m = 0
  · subst m
    have hnative :=
      bettinConreyPsiZeroNativeCoefficient_eq_finiteCandidate
        1 (by norm_num) 1 (by
          unfold routeCTaylorRemainderExponent
          norm_num)
    rw [hnative, routeCTaylorFiniteCandidateCoefficient_one]
    simp [bettinConreyPsiZeroTaylorScalarCoefficient]
  · have hm2 : 2 ≤ m + 1 := by omega
    have hnative :=
      bettinConreyPsiZeroNativeCoefficient_eq_finiteCandidate
        (m + 1) (by omega) (m + 1) (by
          unfold routeCTaylorRemainderExponent
          norm_num
          have hmR : (1 : ℝ) ≤ m := by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
          linarith)
    rw [hnative,
      routeCTaylorFiniteCandidateCoefficient_self_eq_scalar (m + 1) hm2]

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCTaylorCoefficientUniqueness
