import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCUniformCentralWindow

/-!
# Route C: analytic extension and the Lipschitz-growth gate

The rational reciprocity identity expresses the punctured period side by a
finite Hurwitz--zeta formula.  We use this expression to prove that the full
fixed-cutoff period-plus-dual aggregate has a removable analytic extension at
the central parameter.  Compactness then gives a finite Lipschitz constant on
the fixed disk `‖z‖ ≤ 1/2` for every cutoff.

The constants obtained by compactness are not uniform in the cutoff.  The
last structure isolates the exact remaining quantitative question: do these
constants grow at most polynomially?  Such a bound yields, by elementary
calculus alone, the polynomial central-window certificate introduced in the
previous module.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralLipschitz

open Complex Filter Function Set Topology
open scoped NNReal
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperBettinConreyAggregate
open RH.Criteria.NymanBeurling.BCFLogTaperEstermannEvaluationContour
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCUniformCentralWindow

/-- The finite Auli--Bettin--Conrey sum is holomorphic away from the sole
possible Hurwitz singularity `z = -1`. -/
theorem differentiableAt_auliBettinConreyFiniteSum
    (z : ℂ) (h q : ℕ) [NeZero q] (hz : z ≠ -1) :
    DifferentiableAt ℂ (fun w : ℂ =>
      auliBettinConreyFiniteSum w h q) z := by
  have hq0 : (q : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne q)
  letI : NeZero (q : ℂ) := ⟨hq0⟩
  have hneg : -z ≠ 1 := by
    intro hbad
    apply hz
    calc
      z = -(-z) := by ring
      _ = -1 := by rw [hbad]
  unfold auliBettinConreyFiniteSum
  apply (differentiableAt_const_cpow_of_neZero (q : ℂ) z).mul
  apply DifferentiableAt.fun_sum
  intro m _hm
  exact (differentiableAt_const (c := (cotangentTermV (m * h) q : ℂ))).mul
    ((HurwitzZeta.differentiableAt_hurwitzZeta
      (ZMod.toAddCircle (m : ZMod q)) hneg).comp z differentiableAt_id.neg)

theorem differentiableAt_auliBettinConreyFiniteSumTotal
    (z : ℂ) (h q : ℕ) (hq : 0 < q) (hz : z ≠ -1) :
    DifferentiableAt ℂ (fun w : ℂ =>
      auliBettinConreyFiniteSumTotal w h q) z := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  simpa only [auliBettinConreyFiniteSumTotal, dif_neg (Nat.ne_of_gt hq)] using
    differentiableAt_auliBettinConreyFiniteSum z h q hz

/-- The elementary side of the source-normalized master reciprocity. -/
noncomputable def auliBettinConreyRenormalizedExplicitSide
    (z : ℂ) (h k : ℕ) : ℂ :=
  auliBettinConreyFiniteSumTotal z h k -
      (((k : ℂ) / (h : ℂ)) ^ (1 + z)) *
        (-auliBettinConreyFiniteSumTotal z k h) +
    bettinConreyCorrection z h k

theorem auliBettinConreyRenormalizedPeriodSide_eq_explicit
    (H : AuliBettinConreyRationalReciprocityPackage)
    (z : ℂ) (h k : ℕ) (hz : z ≠ 0) (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) :
    auliBettinConreyRenormalizedPeriodSide H z h k =
      auliBettinConreyRenormalizedExplicitSide z h k := by
  rw [auliBettinConreyRenormalizedPeriodSide,
    ← H.reciprocity z h k hz hh hk hcop]
  unfold auliBettinConreyRenormalizedExplicitSide
  ring

theorem differentiableAt_auliBettinConreyRenormalizedExplicitSide
    (z : ℂ) (h k : ℕ) (hz : z ≠ 0) (hzneg : z ≠ -1)
    (hh : 0 < h) (hk : 0 < k) :
    DifferentiableAt ℂ (fun w : ℂ =>
      auliBettinConreyRenormalizedExplicitSide w h k) z := by
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hratio : (k : ℂ) / (h : ℂ) ≠ 0 := div_ne_zero hk0 hh0
  letI : NeZero ((k : ℂ) / (h : ℂ)) := ⟨hratio⟩
  letI : NeZero (k : ℂ) := ⟨hk0⟩
  have hzeta_arg : 1 - z ≠ 1 := by
    intro hbad
    apply hz
    calc
      z = 1 - (1 - z) := by ring
      _ = 0 := by rw [hbad]; ring
  have hfirst := differentiableAt_auliBettinConreyFiniteSumTotal z h k hk hzneg
  have hsecond := differentiableAt_auliBettinConreyFiniteSumTotal z k h hh hzneg
  have hpow : DifferentiableAt ℂ
      (fun w : ℂ => ((k : ℂ) / (h : ℂ)) ^ (1 + w)) z :=
    (differentiableAt_const_cpow_of_neZero
      ((k : ℂ) / (h : ℂ)) (1 + z)).comp z
      ((differentiableAt_const (c := (1 : ℂ))).add differentiableAt_id)
  have hkpow : DifferentiableAt ℂ (fun w : ℂ => (k : ℂ) ^ w) z :=
    differentiableAt_const_cpow_of_neZero (k : ℂ) z
  have hzeta : DifferentiableAt ℂ
    (fun w : ℂ => riemannZeta (1 - w)) z :=
    (differentiableAt_riemannZeta hzeta_arg).comp z
      ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id)
  have hcorrection : DifferentiableAt ℂ
      (fun w : ℂ => bettinConreyCorrection w h k) z := by
    unfold bettinConreyCorrection bettinConreyMeromorphicCorrection
    have hd := (differentiableAt_id.mul (hkpow.mul hzeta)).div_const
      ((Real.pi : ℂ) * (h : ℂ))
    convert hd using 1
    funext w
    simp only [id_eq, Pi.mul_apply]
    ring
  unfold auliBettinConreyRenormalizedExplicitSide
  exact (hfirst.sub (hpow.mul hsecond.neg)).add hcorrection

/-- On the fixed punctured disk, reciprocity transfers holomorphy of the
finite Hurwitz expression to the period side supplied by the package. -/
theorem differentiableAt_auliBettinConreyRenormalizedPeriodSide
    (H : AuliBettinConreyRationalReciprocityPackage)
    (z : ℂ) (h k : ℕ) (hz : z ≠ 0) (hzneg : z ≠ -1)
    (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    DifferentiableAt ℂ (fun w : ℂ =>
      auliBettinConreyRenormalizedPeriodSide H w h k) z := by
  have hexplicit := differentiableAt_auliBettinConreyRenormalizedExplicitSide
    z h k hz hzneg hh hk
  apply hexplicit.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact auliBettinConreyRenormalizedPeriodSide_eq_explicit
    H w h k hw hh hk hcop

theorem differentiableAt_routeCInteriorRenormalizedPeriodPair
    (H : AuliBettinConreyRationalReciprocityPackage)
    (z : ℂ) (N g a b : ℕ) (hz : z ≠ 0) (hzneg : z ≠ -1) :
    DifferentiableAt ℂ (fun w : ℂ =>
      routeCInteriorRenormalizedPeriodPair H w N g a b) z := by
  classical
  unfold routeCInteriorRenormalizedPeriodPair
  by_cases hcop : Nat.Coprime a b
  · simp only [dif_pos hcop]
    by_cases ha : 2 ≤ a
    · simp only [dif_pos ha]
      by_cases hb : 2 ≤ b
      · simp only [dif_pos hb]
        have hh₁ : 0 < inverseResidueNumerator a b hcop :=
          inverseResidueNumerator_pos a b hcop hb
        have hh₂ : 0 < inverseResidueNumerator b a hcop.symm :=
          inverseResidueNumerator_pos b a hcop.symm ha
        exact (differentiableAt_const (c :=
            -(routeCCentralPairScale N g a b : ℂ))).mul
          ((differentiableAt_auliBettinConreyRenormalizedPeriodSide H z
              (inverseResidueNumerator a b hcop) b hz hzneg hh₁ (by omega)
              (inverseResidueNumerator_coprime a b hcop)).add
            (differentiableAt_auliBettinConreyRenormalizedPeriodSide H z
              (inverseResidueNumerator b a hcop.symm) a hz hzneg hh₂ (by omega)
              (inverseResidueNumerator_coprime b a hcop.symm)))
      · simp only [dif_neg hb]
        fun_prop
    · simp only [dif_neg ha]
      fun_prop
  · simp only [dif_neg hcop]
    fun_prop

theorem differentiableAt_routeCInteriorRenormalizedPeriodDualAggregate
    (H : AuliBettinConreyRationalReciprocityPackage)
    (z : ℂ) (N : ℕ) (hz : z ≠ 0) (hzneg : z ≠ -1) :
    DifferentiableAt ℂ (fun w : ℂ =>
      routeCInteriorRenormalizedPeriodDualAggregate H w N) z := by
  unfold routeCInteriorRenormalizedPeriodDualAggregate
    routeCInteriorRenormalizedPeriodAggregate
  have hsum : DifferentiableAt ℂ (fun w : ℂ =>
      ∑ g ∈ Finset.Icc 1 N,
        ∑ a ∈ Finset.Icc 1 (N / g),
          ∑ b ∈ Finset.Icc 1 (N / g),
            routeCInteriorRenormalizedPeriodPair H w N g a b) z := by
    apply DifferentiableAt.fun_sum
    intro g _hg
    apply DifferentiableAt.fun_sum
    intro a _ha
    apply DifferentiableAt.fun_sum
    intro b _hb
    exact differentiableAt_routeCInteriorRenormalizedPeriodPair
      H z N g a b hz hzneg
  exact hsum.add (differentiableAt_const (c :=
    (routeCInteriorCentralDualAggregate N : ℂ)))

/-- Fill the removable central value with the exact source-normalized target. -/
noncomputable def routeCCentralAnalyticExtension
    (H : AuliBettinConreyRationalReciprocityPackage)
    (N : ℕ) (z : ℂ) : ℂ :=
  Function.update
    (fun w : ℂ => routeCInteriorRenormalizedPeriodDualAggregate H w N)
    0 (routeCCentralFinitePartTarget N) z

@[simp]
theorem routeCCentralAnalyticExtension_zero
    (H : AuliBettinConreyRationalReciprocityPackage) (N : ℕ) :
    routeCCentralAnalyticExtension H N 0 = routeCCentralFinitePartTarget N := by
  simp [routeCCentralAnalyticExtension]

theorem routeCCentralAnalyticExtension_of_ne
    (H : AuliBettinConreyRationalReciprocityPackage) (N : ℕ)
    {z : ℂ} (hz : z ≠ 0) :
    routeCCentralAnalyticExtension H N z =
      routeCInteriorRenormalizedPeriodDualAggregate H z N := by
  simp [routeCCentralAnalyticExtension, Function.update_of_ne hz]

/-- The fixed-cutoff central singularity is genuinely removable, not merely
continuous along a selected sequence. -/
theorem analyticAt_routeCCentralAnalyticExtension_zero
    (H : AuliBettinConreyRationalReciprocityPackage) (N : ℕ) :
    AnalyticAt ℂ (routeCCentralAnalyticExtension H N) 0 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hball : ∀ᶠ z : ℂ in nhdsWithin 0 {0}ᶜ,
        z ∈ Metric.ball 0 (1 / 2 : ℝ) :=
      (inf_le_left : nhdsWithin (0 : ℂ) {0}ᶜ ≤ nhds 0)
        (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [self_mem_nhdsWithin, hball] with z hz hzball
    have hzneg : z ≠ -1 := by
      intro hbad
      subst z
      norm_num [Metric.mem_ball, dist_zero_right] at hzball
    have horiginal :=
      differentiableAt_routeCInteriorRenormalizedPeriodDualAggregate
        H z N hz hzneg
    apply horiginal.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact routeCCentralAnalyticExtension_of_ne H N hw
  · change ContinuousAt
      (Function.update
        (fun w : ℂ => routeCInteriorRenormalizedPeriodDualAggregate H w N)
        0 (routeCCentralFinitePartTarget N)) 0
    simpa only [continuousAt_update_same] using
      (show Tendsto
        (fun z : ℂ => routeCInteriorRenormalizedPeriodDualAggregate H z N)
        (nhdsWithin 0 {0}ᶜ) (nhds (routeCCentralFinitePartTarget N)) by
          simpa [routeCCentralFinitePartTarget] using
            tendsto_routeCInteriorRenormalizedPeriodDualAggregate_zero H N)

/-- The extension is complex differentiable on a fixed disk independent of
the H15 cutoff. -/
theorem differentiableOn_routeCCentralAnalyticExtension_ball
    (H : AuliBettinConreyRationalReciprocityPackage) (N : ℕ) :
    DifferentiableOn ℂ (routeCCentralAnalyticExtension H N)
      (Metric.ball 0 (3 / 4 : ℝ)) := by
  intro z hzball
  by_cases hz : z = 0
  · subst z
    exact (analyticAt_routeCCentralAnalyticExtension_zero H N).differentiableAt
      |>.differentiableWithinAt
  · have hzneg : z ≠ -1 := by
      intro hbad
      subst z
      norm_num [Metric.mem_ball, dist_zero_right] at hzball
    have horiginal :=
      differentiableAt_routeCInteriorRenormalizedPeriodDualAggregate
        H z N hz hzneg
    have hextension : DifferentiableAt ℂ
        (routeCCentralAnalyticExtension H N) z := by
      apply horiginal.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact routeCCentralAnalyticExtension_of_ne H N hw
    exact hextension.differentiableWithinAt

theorem analyticOnNhd_routeCCentralAnalyticExtension_ball
    (H : AuliBettinConreyRationalReciprocityPackage) (N : ℕ) :
    AnalyticOnNhd ℂ (routeCCentralAnalyticExtension H N)
      (Metric.ball 0 (3 / 4 : ℝ)) :=
  (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
    (differentiableOn_routeCCentralAnalyticExtension_ball H N)

/-- A cutoff-dependent Lipschitz constant on the common half-disk. -/
structure RouteCHalfDiskLipschitzData
    (H : AuliBettinConreyRationalReciprocityPackage) where
  constant : ℕ → ℝ
  constant_pos : ∀ N, 0 < constant N
  bound : ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ 1 / 2 →
    ‖routeCCentralAnalyticExtension H N z -
        routeCCentralFinitePartTarget N‖ ≤ constant N * ‖z‖

/-- Analyticity and compactness give a finite Lipschitz constant at every
cutoff, on one disk common to all cutoffs.  No growth rate is asserted. -/
theorem exists_routeCHalfDiskLipschitzData
    (H : AuliBettinConreyRationalReciprocityPackage) :
    Nonempty (RouteCHalfDiskLipschitzData H) := by
  have hlocal : ∀ N : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ, ‖z‖ ≤ 1 / 2 →
      ‖routeCCentralAnalyticExtension H N z -
          routeCCentralFinitePartTarget N‖ ≤ K * ‖z‖ := by
    intro N
    have hanalytic := analyticOnNhd_routeCCentralAnalyticExtension_ball H N
    have hcont : ContDiffOn ℝ 1 (routeCCentralAnalyticExtension H N)
        (Metric.closedBall 0 (1 / 2 : ℝ)) := by
      intro z hz
      have hzopen : z ∈ Metric.ball 0 (3 / 4 : ℝ) :=
        Metric.closedBall_subset_ball (by norm_num) hz
      exact (((hanalytic z hzopen).contDiffAt (n := 1)).restrict_scalars ℝ)
        |>.contDiffWithinAt
    obtain ⟨K, hK⟩ := hcont.exists_lipschitzOnWith one_ne_zero
      (convex_closedBall (0 : ℂ) (1 / 2 : ℝ)) (isCompact_closedBall 0 (1 / 2 : ℝ))
    refine ⟨(K : ℝ) + 1, by positivity, ?_⟩
    intro z hz
    have hzmem : z ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have h0mem : (0 : ℂ) ∈ Metric.closedBall 0 (1 / 2 : ℝ) := by
      norm_num [Metric.mem_closedBall]
    have hlip := (lipschitzOnWith_iff_norm_sub_le.mp hK) hzmem h0mem
    calc
      ‖routeCCentralAnalyticExtension H N z -
          routeCCentralFinitePartTarget N‖ =
          ‖routeCCentralAnalyticExtension H N z -
            routeCCentralAnalyticExtension H N 0‖ := by
              rw [routeCCentralAnalyticExtension_zero]
      _ ≤ (K : ℝ) * ‖z‖ := by simpa using hlip
      _ ≤ ((K : ℝ) + 1) * ‖z‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z)
  choose constant hconstant_pos hconstant_bound using hlocal
  exact ⟨⟨constant, hconstant_pos, hconstant_bound⟩⟩

/-- The remaining quantitative question after compactness: polynomial growth
of the common-half-disk Lipschitz constants.  The normalization has no leading
constant; any ordinary polynomial bound can be absorbed by increasing the
integer exponent because `N+2 ≥ 2`. -/
structure RouteCPolynomialLipschitzGrowth
    {H : AuliBettinConreyRationalReciprocityPackage}
    (D : RouteCHalfDiskLipschitzData H) where
  exponent : ℕ
  constant_le : ∀ N : ℕ,
    D.constant N ≤ ((N : ℝ) + 2) ^ exponent

/-- The central radius forced by a polynomial Lipschitz bound.  Two extra
powers pay respectively for the target tolerance and a strict margin. -/
noncomputable def RouteCPolynomialLipschitzGrowth.radius
    {H : AuliBettinConreyRationalReciprocityPackage}
    {D : RouteCHalfDiskLipschitzData H}
    (Q : RouteCPolynomialLipschitzGrowth D) (N : ℕ) : ℝ :=
  1 / (((N : ℝ) + 2) ^ (Q.exponent + 2))

theorem RouteCPolynomialLipschitzGrowth.radius_pos
    {H : AuliBettinConreyRationalReciprocityPackage}
    {D : RouteCHalfDiskLipschitzData H}
    (Q : RouteCPolynomialLipschitzGrowth D) (N : ℕ) :
    0 < Q.radius N := by
  unfold RouteCPolynomialLipschitzGrowth.radius
  positivity

theorem RouteCPolynomialLipschitzGrowth.radius_le_slack
    {H : AuliBettinConreyRationalReciprocityPackage}
    {D : RouteCHalfDiskLipschitzData H}
    (Q : RouteCPolynomialLipschitzGrowth D) (N : ℕ) :
    Q.radius N ≤ routeCCentralWindowSlack N := by
  have hbase : 1 ≤ (N : ℝ) + 2 := by
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hpow : (N : ℝ) + 2 ≤
      ((N : ℝ) + 2) ^ (Q.exponent + 2) :=
    le_self_pow₀ hbase (by omega)
  unfold RouteCPolynomialLipschitzGrowth.radius routeCCentralWindowSlack
  exact one_div_le_one_div_of_le (by positivity)
    ((by linarith : (N : ℝ) + 1 ≤ (N : ℝ) + 2).trans hpow)

theorem RouteCPolynomialLipschitzGrowth.radius_le_half
    {H : AuliBettinConreyRationalReciprocityPackage}
    {D : RouteCHalfDiskLipschitzData H}
    (Q : RouteCPolynomialLipschitzGrowth D) (N : ℕ) :
    Q.radius N ≤ 1 / 2 := by
  have hbase_one : 1 ≤ (N : ℝ) + 2 := by
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hbase_two : 2 ≤ (N : ℝ) + 2 := by
    exact_mod_cast Nat.le_add_left 2 N
  have hpow : (N : ℝ) + 2 ≤
      ((N : ℝ) + 2) ^ (Q.exponent + 2) :=
    le_self_pow₀ hbase_one (by omega)
  unfold RouteCPolynomialLipschitzGrowth.radius
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    (hbase_two.trans hpow)

theorem RouteCPolynomialLipschitzGrowth.radius_tendsto_zero
    {H : AuliBettinConreyRationalReciprocityPackage}
    {D : RouteCHalfDiskLipschitzData H}
    (Q : RouteCPolynomialLipschitzGrowth D) :
    Tendsto Q.radius atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hevent := Metric.tendsto_nhds.mp
    routeCCentralWindowSlack_tendsto_zero ε hε
  filter_upwards [hevent] with N hN
  have hslack_lt : routeCCentralWindowSlack N < ε := by
    have habs : |routeCCentralWindowSlack N| < ε := by
      simpa [Real.dist_eq] using hN
    rwa [abs_of_pos (routeCCentralWindowSlack_pos N)] at habs
  have hradius_lt : Q.radius N < ε :=
    (Q.radius_le_slack N).trans_lt hslack_lt
  simpa [Real.dist_eq, abs_of_pos (Q.radius_pos N)] using hradius_lt

/-- Polynomial Lipschitz growth gives the complete punctured approximation
bound on the explicit polynomial window. -/
theorem RouteCPolynomialLipschitzGrowth.approximation_bound
    {H : AuliBettinConreyRationalReciprocityPackage}
    {D : RouteCHalfDiskLipschitzData H}
    (Q : RouteCPolynomialLipschitzGrowth D)
    (N : ℕ) (z : ℂ) (hz : z ≠ 0) (hznorm : ‖z‖ < Q.radius N) :
    ‖routeCInteriorRenormalizedPeriodDualAggregate H z N -
        routeCCentralFinitePartTarget N‖ < routeCCentralWindowSlack N := by
  have hzhalf : ‖z‖ ≤ 1 / 2 :=
    le_of_lt (hznorm.trans_le (Q.radius_le_half N))
  have hbound := D.bound N z hzhalf
  have hpow_pos : 0 < ((N : ℝ) + 2) ^ Q.exponent := by positivity
  have hcancel : ((N : ℝ) + 2) ^ Q.exponent * Q.radius N =
      1 / (((N : ℝ) + 2) ^ 2) := by
    unfold RouteCPolynomialLipschitzGrowth.radius
    rw [pow_add]
    field_simp [ne_of_gt hpow_pos]
  have hlast : 1 / (((N : ℝ) + 2) ^ 2) <
      routeCCentralWindowSlack N := by
    unfold routeCCentralWindowSlack
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith [sq_nonneg (N : ℝ)]
  calc
    ‖routeCInteriorRenormalizedPeriodDualAggregate H z N -
        routeCCentralFinitePartTarget N‖ =
        ‖routeCCentralAnalyticExtension H N z -
          routeCCentralFinitePartTarget N‖ := by
            rw [routeCCentralAnalyticExtension_of_ne H N hz]
    _ ≤ D.constant N * ‖z‖ := hbound
    _ ≤ ((N : ℝ) + 2) ^ Q.exponent * ‖z‖ :=
      mul_le_mul_of_nonneg_right (Q.constant_le N) (norm_nonneg z)
    _ < ((N : ℝ) + 2) ^ Q.exponent * Q.radius N :=
      mul_lt_mul_of_pos_left hznorm hpow_pos
    _ = 1 / (((N : ℝ) + 2) ^ 2) := hcancel
    _ < routeCCentralWindowSlack N := hlast

/-- The explicit central-window data obtained from polynomial Lipschitz
growth. -/
noncomputable def RouteCPolynomialLipschitzGrowth.toCentralWindowData
    {H : AuliBettinConreyRationalReciprocityPackage}
    {D : RouteCHalfDiskLipschitzData H}
    (Q : RouteCPolynomialLipschitzGrowth D) :
    RouteCCentralWindowData H where
  radius := Q.radius
  radius_pos := Q.radius_pos
  radius_tendsto_zero := Q.radius_tendsto_zero
  approximation_bound := Q.approximation_bound

/-- Thus a polynomial Lipschitz estimate instantiates the previously open
polynomial-window certificate with exponent `κ+2`. -/
noncomputable def RouteCPolynomialLipschitzGrowth.toPolynomialWindowCertificate
    {H : AuliBettinConreyRationalReciprocityPackage}
    {D : RouteCHalfDiskLipschitzData H}
    (Q : RouteCPolynomialLipschitzGrowth D) :
    RouteCPolynomialWindowCertificate Q.toCentralWindowData where
  exponent := Q.exponent + 2
  exponent_pos := by omega
  radius_lower := fun _N => le_rfl

/-- Final stop-test: after the polynomial Lipschitz bound is supplied, decay
of the explicit analytic family is still equivalent to decay of the exact
central H15 target. -/
theorem RouteCPolynomialLipschitzGrowth.analytic_tendsto_zero_iff_target
    {H : AuliBettinConreyRationalReciprocityPackage}
    {D : RouteCHalfDiskLipschitzData H}
    (Q : RouteCPolynomialLipschitzGrowth D) :
    Tendsto Q.toPolynomialWindowCertificate.toPath.analyticValue
        atTop (nhds 0) ↔
      Tendsto routeCCentralFinitePartTarget atTop (nhds 0) :=
  Q.toPolynomialWindowCertificate.analytic_tendsto_zero_iff_target

/-- Canonical proposition-valued formulation of the new quantitative gate,
without an arbitrary prior choice of compactness constants. -/
structure RouteCPolynomialHalfDiskControl
    (H : AuliBettinConreyRationalReciprocityPackage) where
  exponent : ℕ
  bound : ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ 1 / 2 →
    ‖routeCCentralAnalyticExtension H N z -
        routeCCentralFinitePartTarget N‖ ≤
      ((N : ℝ) + 2) ^ exponent * ‖z‖

noncomputable def RouteCPolynomialHalfDiskControl.toLipschitzData
    {H : AuliBettinConreyRationalReciprocityPackage}
    (P : RouteCPolynomialHalfDiskControl H) :
    RouteCHalfDiskLipschitzData H where
  constant := fun N => ((N : ℝ) + 2) ^ P.exponent
  constant_pos := fun _N => by positivity
  bound := P.bound

noncomputable def RouteCPolynomialHalfDiskControl.toGrowth
    {H : AuliBettinConreyRationalReciprocityPackage}
    (P : RouteCPolynomialHalfDiskControl H) :
    RouteCPolynomialLipschitzGrowth P.toLipschitzData where
  exponent := P.exponent
  constant_le := fun _N => le_rfl

noncomputable def RouteCPolynomialHalfDiskControl.toCentralWindowData
    {H : AuliBettinConreyRationalReciprocityPackage}
    (P : RouteCPolynomialHalfDiskControl H) :
    RouteCCentralWindowData H :=
  P.toGrowth.toCentralWindowData

noncomputable def RouteCPolynomialHalfDiskControl.toPolynomialWindowCertificate
    {H : AuliBettinConreyRationalReciprocityPackage}
    (P : RouteCPolynomialHalfDiskControl H) :
    RouteCPolynomialWindowCertificate P.toCentralWindowData :=
  P.toGrowth.toPolynomialWindowCertificate

/-- The polynomial regularity gate creates the explicit analytic path, while
the outer signed decay remains exactly the central-target problem. -/
theorem RouteCPolynomialHalfDiskControl.analytic_tendsto_zero_iff_target
    {H : AuliBettinConreyRationalReciprocityPackage}
    (P : RouteCPolynomialHalfDiskControl H) :
    Tendsto P.toPolynomialWindowCertificate.toPath.analyticValue
        atTop (nhds 0) ↔
      Tendsto routeCCentralFinitePartTarget atTop (nhds 0) :=
  P.toPolynomialWindowCertificate.analytic_tendsto_zero_iff_target

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralLipschitz
