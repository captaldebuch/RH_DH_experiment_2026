import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow

/-!
# Route C: the literal Bettin--Conrey central period function

Bettin--Conrey define the central period function by

`psi_0(z) = -2 (log(2*pi*z)-gamma)/(pi*i*z) - 2*i*g_0(z)`,

where

`g_0(z) = (1/(pi*i)) integral_(-1/2) zeta(s) zeta(1-s) z^(-s) / sin(pi*s) ds`.

After parametrizing the upward vertical line by `s=-1/2+i*t`, the factor
`ds=i dt` changes `1/(pi*i)` into `1/pi`.  The definitions below use that
real-line Bochner integral directly.  They are total Lean definitions; their
analytic properties are stated only with the convergence hypotheses actually
needed.

This file also proves the exact central-specialization passage.  If the
parameter-dependent period function in the already formalized master
reciprocity tends to the literal `psi_0`, then uniqueness of limits identifies
the finite central cotangent side with `(i/2) psi_0`.  No reciprocity theorem,
Taylor theorem, or saddle-point estimate is inserted as an axiom.

References:

* S. Bettin and B. Conrey, *Period functions and cotangent sums*,
  Algebra & Number Theory 7 (2013), Theorem 1 and pp. 6--8.
* S. Bettin and J. B. Conrey, *A reciprocity formula for a cotangent sum*,
  IMRN 2013 (24), 5709--5726.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero

open Complex Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralTaylorRow
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCTransformTail
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCThreeTermDefect

/-- The point `-1/2+i*t` on the upward central Bettin--Conrey contour. -/
noncomputable def bettinConreyCentralVerticalPoint (t : ℝ) : ℂ :=
  -(1 : ℂ) / 2 + (t : ℂ) * I

/-- The source Mellin integrand for `g_0`, after parametrizing its vertical
line but before multiplying by `1/pi`. -/
noncomputable def bettinConreyGZeroVerticalIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  let s := bettinConreyCentralVerticalPoint t
  riemannZeta s * riemannZeta (1 - s) /
      Complex.sin ((Real.pi : ℂ) * s) * z ^ (-s)

/-- Bettin--Conrey's `g_0`.  The source factor `1/(pi*i)` and the line
differential `ds=i dt` combine to the displayed factor `1/pi`. -/
noncomputable def bettinConreyGZero (z : ℂ) : ℂ :=
  (1 / (Real.pi : ℂ)) *
    ∫ t : ℝ, bettinConreyGZeroVerticalIntegrand z t

/-- The literal central period function `psi_0` from Bettin--Conrey
Theorem 1. -/
noncomputable def bettinConreyPsiZero (z : ℂ) : ℂ :=
  -2 *
      (Complex.log ((2 * Real.pi : ℂ) * z) -
        (Real.eulerMascheroniConstant : ℂ)) /
      ((Real.pi : ℂ) * I * z) -
    2 * I * bettinConreyGZero z

/-- The source formula is definitionally recovered with no normalization
change hidden behind rewriting. -/
theorem bettinConreyPsiZero_eq_source_formula (z : ℂ) :
    bettinConreyPsiZero z =
      -2 *
          (Complex.log ((2 * Real.pi : ℂ) * z) -
            (Real.eulerMascheroniConstant : ℂ)) /
          ((Real.pi : ℂ) * I * z) -
        2 * I * bettinConreyGZero z :=
  rfl

/-- The positive rational points used by H15 lie in the right half-plane,
the natural domain of the defining formula. -/
theorem routeCUnitIntervalRatio_re_pos
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    0 < (routeCUnitIntervalRatio h k : ℂ).re := by
  simpa using routeCUnitIntervalRatio_pos h k hh hk

/-- Exact analytic compatibility still required between the
parameter-dependent source period and its central specialization.  This is a
single convergence statement, not a restatement of finite reciprocity. -/
structure BettinConreyPsiZeroCentralSpecialization
    (H : AuliBettinConreyRationalReciprocityPackage) where
  period_tendsto : ∀ x : ℂ, 0 < x.re →
    Tendsto (fun a : ℂ => H.periodFunction a x)
      (𝓝[≠] 0) (𝓝 (bettinConreyPsiZero x))

/-- The zeta multiplier in master reciprocity tends to `i/2` at the central
parameter. -/
theorem tendsto_bettinConreyCentralZetaMultiplier :
    Tendsto (fun a : ℂ => -I * riemannZeta (-a))
      (𝓝[≠] 0) (𝓝 (I / 2)) := by
  have hzeta : Tendsto (fun a : ℂ => riemannZeta (-a))
      (𝓝[≠] 0) (𝓝 (riemannZeta 0)) := by
    have hcont : ContinuousAt (fun a : ℂ => riemannZeta (-a)) 0 :=
      (differentiableAt_riemannZeta (by norm_num)).continuousAt.comp
        (by fun_prop)
    simpa using hcont.tendsto.mono_left
      (inf_le_left : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)
  convert (tendsto_const_nhds.mul hzeta) using 1
  rw [riemannZeta_zero]
  ring_nf

/-- A genuine central specialization of the paper's period function gives
the exact central reciprocity value consumed by the Taylor package. -/
theorem bettinConreyCentralFinitePartSide_eq_psiZero
    (H : AuliBettinConreyRationalReciprocityPackage)
    (S : BettinConreyPsiZeroCentralSpecialization H)
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    (bettinConreyCentralFinitePartSide h k : ℂ) =
      I / 2 * bettinConreyPsiZero (routeCUnitIntervalRatio h k : ℂ) := by
  have hperiod := S.period_tendsto
    (routeCUnitIntervalRatio h k : ℂ)
    (routeCUnitIntervalRatio_re_pos h k hh hk)
  have hproduct := tendsto_bettinConreyCentralZetaMultiplier.mul hperiod
  have hsource : Tendsto
      (fun a : ℂ => auliBettinConreyRenormalizedPeriodSide H a h k)
      (𝓝[≠] 0)
      (𝓝 (I / 2 *
        bettinConreyPsiZero (routeCUnitIntervalRatio h k : ℂ))) := by
    simpa [auliBettinConreyRenormalizedPeriodSide,
      routeCUnitIntervalRatio] using hproduct
  exact tendsto_nhds_unique
    (tendsto_auliBettinConreyRenormalizedPeriodSide_zero
      H h k hh hk hcop)
    hsource

/-- The parameter-dependent three-term relation descends to the literal
central `psi_0` relation at positive rational points.  This is the mechanical
limit passage; the analytic parameter relation remains the cited source
theorem represented by `T`. -/
theorem bettinConreyPsiZero_rational_threeTerm
    (H : AuliBettinConreyRationalReciprocityPackage)
    (S : BettinConreyPsiZeroCentralSpecialization H)
    (T : AuliBettinConreyRationalThreeTermPackage H)
    (h k : ℕ) (hk : 0 < k) (hkh : k < h) :
    bettinConreyPsiZero ((((h - k : ℕ) : ℝ) / (k : ℝ) : ℝ) : ℂ) -
        bettinConreyPsiZero (((h : ℝ) / (k : ℝ) : ℝ) : ℂ) =
      ((k : ℂ) / (h : ℂ)) *
        bettinConreyPsiZero ((((h - k : ℕ) : ℝ) / (h : ℝ) : ℝ) : ℂ) := by
  have hh : 0 < h := Nat.zero_lt_of_lt hkh
  have hsub : 0 < h - k := Nat.sub_pos_of_lt hkh
  have hx₁ : 0 <
      (((((h - k : ℕ) : ℝ) / (k : ℝ) : ℝ) : ℂ)).re := by
    norm_num
    positivity
  have hx₂ : 0 < ((((h : ℝ) / (k : ℝ) : ℝ) : ℂ)).re := by
    norm_num
    positivity
  have hx₃ : 0 <
      (((((h - k : ℕ) : ℝ) / (h : ℝ) : ℝ) : ℂ)).re := by
    norm_num
    positivity
  have hleft := (S.period_tendsto _ hx₁).sub (S.period_tendsto _ hx₂)
  have hbase : ((k : ℂ) / (h : ℂ)) ≠ 0 := by
    exact div_ne_zero (by exact_mod_cast hk.ne') (by exact_mod_cast hh.ne')
  have hfactor : Tendsto
      (fun z : ℂ => routeCPeriodDescentFactor z h k)
      (𝓝[≠] 0) (𝓝 ((k : ℂ) / (h : ℂ))) := by
    have hc : ContinuousAt
        (fun z : ℂ => ((k : ℂ) / (h : ℂ)) ^ (1 + z)) 0 :=
      (continuousAt_const_cpow hbase).comp
        (continuousAt_const.add continuousAt_id)
    simpa [routeCPeriodDescentFactor, hbase] using
      hc.tendsto.mono_left (inf_le_left : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)
  have hright := hfactor.mul (S.period_tendsto _ hx₃)
  have heq :
      (fun z : ℂ =>
          H.periodFunction z
              ((((h - k : ℕ) : ℝ) / (k : ℝ) : ℝ) : ℂ) -
            H.periodFunction z (((h : ℝ) / (k : ℝ) : ℝ) : ℂ)) =ᶠ[𝓝[≠] 0]
        (fun z : ℂ =>
          routeCPeriodDescentFactor z h k *
            H.periodFunction z
              ((((h - k : ℕ) : ℝ) / (h : ℝ) : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact T.threeTerm z h k hz hk hkh
  exact tendsto_nhds_unique (hleft.congr' heq) hright

/-! ## Exact assembly of the remaining local analytic inputs -/

/-- The literal Taylor `HasSum` for the now-fixed source function `psi_0`.
Keeping it separate from coefficient decay records that convergence and the
saddle-point estimate are distinct analytic arguments in the paper. -/
structure BettinConreyPsiZeroTaylorHasSum where
  hasSum : ∀ z : ℂ, ‖z‖ < 1 →
    HasSum
      (fun n : ℕ =>
        bettinConreyCentralTaylorCoefficient (n + 2) * (-z) ^ (n + 2))
      ((Real.pi : ℂ) * I / 2 * (1 + z) *
          bettinConreyPsiZero (1 + z) + 1 + z / 2)

/-- A global root-exponential envelope for the centered coefficients.  The
paper obtains such an envelope from its saddle-point asymptotic; the finite
initial segment is absorbed into `scale`. -/
structure BettinConreyCentralCoefficientRootDecay where
  scale : ℝ
  rate : ℝ
  scale_nonneg : 0 ≤ scale
  rate_pos : 0 < rate
  bound : ∀ m : ℕ, 2 ≤ m →
    ‖bettinConreyCentralCenteredCoefficient m‖ ≤
      scale * routeCRootExponentialMajorant rate m

/-- The form naturally delivered by a coefficient asymptotic: a positive
root-exponential rate and an envelope valid for all sufficiently large
indices. -/
structure BettinConreyCentralCoefficientAsymptoticEnvelope where
  scale : ℝ
  rate : ℝ
  scale_nonneg : 0 ≤ scale
  rate_pos : 0 < rate
  eventually_bound : ∀ᶠ m : ℕ in atTop,
    ‖bettinConreyCentralCenteredCoefficient m‖ ≤
      scale * routeCRootExponentialMajorant rate m

/-- An eventual root-exponential estimate automatically absorbs its finite
initial segment into a larger constant.  Thus the downstream package does
not ask the paper for an artificial all-index estimate. -/
theorem nonempty_rootDecay_of_asymptoticEnvelope
    (A : BettinConreyCentralCoefficientAsymptoticEnvelope) :
    Nonempty BettinConreyCentralCoefficientRootDecay := by
  rcases eventually_atTop.1 A.eventually_bound with ⟨N, hN⟩
  let prefixScale : ℝ :=
    ∑ m ∈ Finset.Icc 2 N,
      ‖bettinConreyCentralCenteredCoefficient m‖ /
        routeCRootExponentialMajorant A.rate m
  let globalScale : ℝ := max A.scale prefixScale
  have hprefix_nonneg : 0 ≤ prefixScale := by
    dsimp [prefixScale]
    apply Finset.sum_nonneg
    intro i _hi
    exact div_nonneg (norm_nonneg _)
      (routeCRootExponentialMajorant_nonneg A.rate i)
  have hglobal_nonneg : 0 ≤ globalScale := by
    dsimp [globalScale]
    exact le_max_of_le_left A.scale_nonneg
  refine ⟨{
    scale := globalScale
    rate := A.rate
    scale_nonneg := hglobal_nonneg
    rate_pos := A.rate_pos
    bound := ?_ }⟩
  intro m hm2
  have hp : 0 < routeCRootExponentialMajorant A.rate m := by
    unfold routeCRootExponentialMajorant
    exact Real.exp_pos _
  by_cases hmN : N ≤ m
  · exact (hN m hmN).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
  · have hmmem : m ∈ Finset.Icc 2 N := by
      simp only [Finset.mem_Icc]
      exact ⟨hm2, Nat.le_of_lt (Nat.lt_of_not_ge hmN)⟩
    have hterm_nonneg : ∀ i ∈ Finset.Icc 2 N,
        0 ≤ ‖bettinConreyCentralCenteredCoefficient i‖ /
          routeCRootExponentialMajorant A.rate i := by
      intro i _hi
      exact div_nonneg (norm_nonneg _)
        (routeCRootExponentialMajorant_nonneg A.rate i)
    have hratio_prefix :
        ‖bettinConreyCentralCenteredCoefficient m‖ /
            routeCRootExponentialMajorant A.rate m ≤ prefixScale := by
      dsimp [prefixScale]
      exact Finset.single_le_sum hterm_nonneg hmmem
    have hratio_global :
        ‖bettinConreyCentralCenteredCoefficient m‖ /
            routeCRootExponentialMajorant A.rate m ≤ globalScale :=
      hratio_prefix.trans (le_max_right _ _)
    exact (div_le_iff₀ hp).mp hratio_global

/-- Canonical noncomputable selection of the global envelope supplied by the
preceding finite-prefix argument. -/
noncomputable def BettinConreyCentralCoefficientAsymptoticEnvelope.toRootDecay
    (A : BettinConreyCentralCoefficientAsymptoticEnvelope) :
    BettinConreyCentralCoefficientRootDecay :=
  Classical.choice (nonempty_rootDecay_of_asymptoticEnvelope A)

/-- The root-exponential envelope makes the shifted centered coefficient
norms summable. -/
theorem BettinConreyCentralCoefficientRootDecay.centered_shift_norm_summable
    (D : BettinConreyCentralCoefficientRootDecay) :
    Summable (fun n : ℕ =>
      ‖bettinConreyCentralCenteredCoefficient (n + 2)‖) := by
  have hmajor : Summable (fun n : ℕ =>
      D.scale * routeCRootExponentialMajorant D.rate (n + 2)) :=
    ((summable_nat_add_iff 2).2
      (summable_routeCRootExponentialMajorant D.rate D.rate_pos)).mul_left
        D.scale
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => D.bound (n + 2) (by omega)) hmajor

/-- Evaluation inside the unit disc preserves summability of the centered
row. -/
theorem BettinConreyCentralCoefficientRootDecay.centered_evaluation_summable
    (D : BettinConreyCentralCoefficientRootDecay)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      bettinConreyCentralCenteredCoefficient (n + 2) *
        (-z) ^ (n + 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => ?_) D.centered_shift_norm_summable
  rw [norm_mul, norm_pow, norm_neg]
  have hpow : ‖z‖ ^ (n + 2) ≤ 1 :=
    pow_le_one₀ (norm_nonneg z) hz.le
  exact mul_le_of_le_one_right (norm_nonneg _) hpow

/-- Consequently the complete raw Taylor series converges absolutely at
every point of the open unit disc.  Its value, rather than its convergence,
is the remaining Taylor theorem. -/
theorem BettinConreyCentralCoefficientRootDecay.raw_taylor_summable
    (D : BettinConreyCentralCoefficientRootDecay)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      bettinConreyCentralTaylorCoefficient (n + 2) *
        (-z) ^ (n + 2)) := by
  have hzneg : ‖-z‖ < 1 := by simpa using hz
  have hharm : Summable (fun n : ℕ =>
      (-z) ^ (n + 2) / ((n + 2 : ℕ) : ℂ)) :=
    ((hasSum_nat_add_iff' 2).2
      (Complex.hasSum_taylorSeries_neg_log hzneg)).summable
  have hcenter := D.centered_evaluation_summable z hz
  apply (hharm.add hcenter).congr
  intro n
  unfold bettinConreyCentralCenteredCoefficient
  ring

/-- The genuinely analytic remainder of the Taylor theorem after convergence
has been discharged from coefficient decay. -/
structure BettinConreyPsiZeroTaylorValueIdentity where
  tsum_eq : ∀ z : ℂ, ‖z‖ < 1 →
    (∑' n : ℕ,
      bettinConreyCentralTaylorCoefficient (n + 2) * (-z) ^ (n + 2)) =
      (Real.pi : ℂ) * I / 2 * (1 + z) *
          bettinConreyPsiZero (1 + z) + 1 + z / 2

/-- Decay plus the exact Taylor value produces the `HasSum` formulation used
by the source package. -/
noncomputable def BettinConreyPsiZeroTaylorValueIdentity.toHasSum
    (V : BettinConreyPsiZeroTaylorValueIdentity)
    (D : BettinConreyCentralCoefficientRootDecay) :
    BettinConreyPsiZeroTaylorHasSum where
  hasSum := by
    intro z hz
    rw [← V.tsum_eq z hz]
    exact (D.raw_taylor_summable z hz).hasSum

/-- Central reciprocity, the literal Taylor theorem, and the coefficient
envelope assemble the source-normalized analytic theorem without any further
analytic step. -/
noncomputable def bettinConreyCentralTaylorAnalyticTheorem
    (H : AuliBettinConreyRationalReciprocityPackage)
    (S : BettinConreyPsiZeroCentralSpecialization H)
    (T : BettinConreyPsiZeroTaylorHasSum)
    (D : BettinConreyCentralCoefficientRootDecay) :
    BettinConreyCentralTaylorAnalyticTheorem where
  psiZero := bettinConreyPsiZero
  central_reciprocity := by
    intro h k hh hk _hhk hcop
    exact bettinConreyCentralFinitePartSide_eq_psiZero
      H S h k hh hk hcop
  taylor_hasSum := T.hasSum
  decayScale := D.scale
  decayRate := D.rate
  decayScale_nonneg := D.scale_nonneg
  decayRate_pos := D.rate_pos
  centered_bound := D.bound

/-- Final local constructor: once the three genuinely analytic source
results have been proved, the exact `BettinConreyCentralTaylorPackage`
inhabitant is automatic. -/
noncomputable def bettinConreyCentralTaylorPackage
    (H : AuliBettinConreyRationalReciprocityPackage)
    (S : BettinConreyPsiZeroCentralSpecialization H)
    (T : BettinConreyPsiZeroTaylorHasSum)
    (D : BettinConreyCentralCoefficientRootDecay) :
    BettinConreyCentralTaylorPackage :=
  (bettinConreyCentralTaylorAnalyticTheorem H S T D).toPackage

/-- Version matching the form of the published asymptotic: eventual decay is
enough, because the finite prefix is absorbed automatically. -/
noncomputable def bettinConreyCentralTaylorPackageOfAsymptotic
    (H : AuliBettinConreyRationalReciprocityPackage)
    (S : BettinConreyPsiZeroCentralSpecialization H)
    (T : BettinConreyPsiZeroTaylorHasSum)
    (A : BettinConreyCentralCoefficientAsymptoticEnvelope) :
    BettinConreyCentralTaylorPackage :=
  bettinConreyCentralTaylorPackage H S T A.toRootDecay

/-- Most economical final constructor: the published asymptotic supplies
convergence, so only its eventual envelope and the exact Taylor value are
needed. -/
noncomputable def bettinConreyCentralTaylorPackageOfValueAndAsymptotic
    (H : AuliBettinConreyRationalReciprocityPackage)
    (S : BettinConreyPsiZeroCentralSpecialization H)
    (V : BettinConreyPsiZeroTaylorValueIdentity)
    (A : BettinConreyCentralCoefficientAsymptoticEnvelope) :
    BettinConreyCentralTaylorPackage :=
  let D := A.toRootDecay
  bettinConreyCentralTaylorPackage H S (V.toHasSum D) D

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCPsiZero
