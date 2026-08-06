import Mathlib
import NBMellinTools.NB18LogTaperRH

/-!
# The Nyman–Beurling / Báez-Duarte criterion

This file is about the classical criterion (Nyman 1950, Beurling 1955, Báez-Duarte 2003)

> The Riemann hypothesis holds if and only if `χ_{(0,1]}` lies in the closure, inside
> `L²((0,∞), dx)`, of the linear span of the dilations `ρ_n(x) = {1/(n x)}`, `n ≥ 1`.

## What is proved here

Everything *except* the criterion itself is proved unconditionally.  Concretely, we set up the
`L²((0,∞))` Hilbert space picture of the Báez-Duarte approximation problem and prove that the
following four statements are equivalent (with no number-theoretic input whatsoever):

* `NymanBeurlingTheorem.BDApproximable` — for every `ε > 0` some finite combination
  `∑_{k<N} c_k ρ_{k+1}` has `L²`-error `< ε` (coefficients indexed by `ℕ`);
* `NymanBeurlingTheorem.BDApproximableFin` — the same with coefficients indexed by `Fin N`
  (the form in which the criterion is usually stated);
* `NymanBeurlingTheorem.BDApproximableSeq` — there is a *sequence* of finite combinations whose
  `L²`-errors tend to `0`;
* `chi01L2 ∈ bdSpan.topologicalClosure` — the genuine closure statement in the Hilbert space
  `L²((0,∞))`: the class of `χ_{(0,1]}` lies in the closure of the `ℝ`-linear span of the
  classes of the Báez-Duarte generators.

See `NymanBeurlingTheorem.bdApproximable_iff_fin`,
`NymanBeurlingTheorem.bdApproximable_iff_seq` and
`NymanBeurlingTheorem.bdApproximable_iff_mem_closure`.

## The criterion itself

The criterion equates these conditions with the Riemann hypothesis.  Its proof is a deep piece
of classical analysis: the hard direction (`RH → approximability`) rests on Beurling's theorem
on shift-invariant subspaces / inner–outer factorisation in the Hardy space `H²` of a half
plane, and the converse rests on the boundedness of point evaluation in that same Hardy space.
None of this theory is available in Mathlib, and it is *not* developed here.  Accordingly the
criterion appears as the explicitly named hypothesis
`LogTaperBaezDuarte.NymanBeurlingCriterion` (a `Prop`, stated in `RequestProject.LogTaperRH`),
and the theorems of this file that use it carry it as a hypothesis.  Nothing is assumed
silently: no axiom is added, and no statement below is proved from a `sorry`.

The theorems `nyman_beurling_criterion`, `nyman_beurling_equivalent_infimum`,
`nyman_beurling_closure_form` and `nyman_beurling_seq_form` record the criterion in the four
equivalent shapes, each of them a consequence of the single classical input.

## Remark on the generators

The generators used here are `ρ_n(x) = {1/(n x)}` for `n ≥ 1`.  Several classical sources use
instead the *corrected* generators `ρ_θ(x) = {θ/x} - θ {1/x}` with `θ = 1/n`.  Since
`ρ_1(x) = {1/x}` belongs to the family used here, the corrected generators lie in the span of
the present ones, so the span used here contains the classical one (and exceeds it by at most
one dimension, namely the line spanned by `ρ_1`).
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace NymanBeurlingTheorem

open LogTaperBaezDuarte

/-! ## A general `L²` lemma -/

/-- The square of the `L²`-norm of `MemLp.toLp f` is the integral of `‖f‖²`. -/
theorem norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (h : MemLp f 2 μ) : ‖h.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h1 : ((‖h.toLp f‖ : ℝ) ^ 2 : ℝ) = RCLike.re (inner ℂ (h.toLp f) (h.toLp f)) := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [h1, L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) (h.toLp f) (h.toLp f))]
  refine integral_congr_ae ?_
  filter_upwards [h.coeFn_toLp] with x hx
  rw [hx]
  simp [← Complex.ofReal_pow]

/-! ## The Hilbert space picture -/

/-- The Hilbert space `L²((0,∞), dx)` of the Nyman–Beurling problem. -/
abbrev L2Pos : Type := Lp ℂ 2 (volume.restrict (Ioi (0:ℝ)))

/-- The class of `χ_{(0,1]}` in `L²((0,∞))`. -/
def chi01L2 : L2Pos := memLp_chi01.toLp _

/-- The class of the Báez-Duarte generator `ρ_{n+1}` in `L²((0,∞))`. -/
def rhoL2 (n : ℕ) : L2Pos := (memLp_rhoBD (n + 1) (Nat.le_add_left 1 n)).toLp _

/-- The class of a finite combination `∑_{k<N} c_k ρ_{k+1}` in `L²((0,∞))`. -/
def bdApproxL2 (N : ℕ) (c : ℕ → ℝ) : L2Pos := (memLp_bdApproxWith N c).toLp _

/-- The coercion of a finite sum in `Lp` is a.e. the sum of the coercions. -/
lemma coeFn_finset_sum {ι : Type*} (t : Finset ι) (F : ι → L2Pos) :
    ((∑ i ∈ t, F i : L2Pos) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      fun x => ∑ i ∈ t, (F i : ℝ → ℂ) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0:ℝ)))
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ t, F i), ih] with x h1 h2
      rw [h1]
      simp only [Pi.add_apply, Finset.sum_insert ha]
      rw [h2]

lemma coeFn_rhoL2 (n : ℕ) :
    (rhoL2 n : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0:ℝ))] rhoBD (n + 1) :=
  (memLp_rhoBD (n + 1) (Nat.le_add_left 1 n)).coeFn_toLp

lemma bdApproxL2_eq_sum (N : ℕ) (c : ℕ → ℝ) :
    bdApproxL2 N c = ∑ k : Fin N, c k • rhoL2 k := by
  have hcoe : (bdApproxL2 N c : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      fun x => ∑ k : Fin N, (c (k : ℕ) : ℂ) * rhoBD ((k : ℕ) + 1) x := by
    filter_upwards [(memLp_bdApproxWith N c).coeFn_toLp] with x hx
    simpa only [bdApproxL2, bdApproxWith] using hx
  have hterm : ∀ k : Fin N, ((c (k : ℕ) • rhoL2 (k : ℕ) : L2Pos) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0:ℝ))] fun x => (c (k : ℕ) : ℂ) * rhoBD ((k : ℕ) + 1) x := by
    intro k
    filter_upwards [Lp.coeFn_smul (c (k : ℕ)) (rhoL2 (k : ℕ)), coeFn_rhoL2 (k : ℕ)] with x hx hx'
    rw [hx]
    simp only [Pi.smul_apply]
    rw [hx', Complex.real_smul]
  have hsum : ((∑ k : Fin N, c (k : ℕ) • rhoL2 (k : ℕ) : L2Pos) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0:ℝ))]
        fun x => ∑ k : Fin N, (c (k : ℕ) : ℂ) * rhoBD ((k : ℕ) + 1) x := by
    filter_upwards [coeFn_finset_sum Finset.univ (fun k : Fin N => c (k : ℕ) • rhoL2 (k : ℕ)),
      ae_all_iff.2 hterm] with x h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun k _ => h2 k
  exact Lp.ext (hcoe.trans hsum.symm)

/-- The `L²`-error of a finite combination is the squared distance in `L²((0,∞))`. -/
lemma l2ErrorWith_eq_dist_sq (N : ℕ) (c : ℕ → ℝ) :
    l2ErrorWith N c = ‖chi01L2 - bdApproxL2 N c‖ ^ 2 := by
  have hmem : MemLp (fun x => chi01 x - bdApproxWith N c x) 2 (volume.restrict (Ioi (0:ℝ))) :=
    memLp_chi01.sub (memLp_bdApproxWith N c)
  have hsub : chi01L2 - bdApproxL2 N c = hmem.toLp _ := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_sub chi01L2 (bdApproxL2 N c), memLp_chi01.coeFn_toLp,
      (memLp_bdApproxWith N c).coeFn_toLp, hmem.coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h4]
    simp only [Pi.sub_apply, chi01L2, bdApproxL2] at h2 h3 ⊢
    rw [h2, h3]
  rw [hsub, norm_toLp_sq hmem, l2ErrorWith]

/-! ## The approximation properties -/

/-- **The Báez-Duarte approximation property** with `ℕ`-indexed coefficients: `χ_{(0,1]}` can be
approximated in `L²((0,∞))` to arbitrary accuracy by finite combinations of the `ρ_n`. -/
def BDApproximable : Prop := ∀ ε > 0, ∃ (N : ℕ) (c : ℕ → ℝ), l2ErrorWith N c < ε

/-- The same property with `Fin N`-indexed coefficients and the integral written out. -/
def BDApproximableFin : Prop :=
  ∀ ε > 0, ∃ (N : ℕ) (c : Fin N → ℝ),
    (∫ x in Ioi (0:ℝ), ‖chi01 x - ∑ n : Fin N, (c n : ℂ) * rhoBD ((n : ℕ) + 1) x‖ ^ 2) < ε

/-- The same property expressed by a sequence of approximants whose errors tend to `0`. -/
def BDApproximableSeq : Prop :=
  ∃ (N : ℕ → ℕ) (c : ℕ → ℕ → ℝ), Tendsto (fun k => l2ErrorWith (N k) (c k)) atTop (𝓝 0)

lemma l2ErrorWith_nonneg (N : ℕ) (c : ℕ → ℝ) : 0 ≤ l2ErrorWith N c := by
  rw [l2ErrorWith_eq_dist_sq]; positivity

/-- The `Fin`-indexed and `ℕ`-indexed forms of the approximation property agree. -/
theorem bdApproximable_iff_fin : BDApproximable ↔ BDApproximableFin := by
  constructor
  · intro h ε hε
    obtain ⟨N, c, hN⟩ := h ε hε
    refine ⟨N, fun k => c (k : ℕ), ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) hN
    rw [l2ErrorWith]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [bdApproxWith]
  · intro h ε hε
    obtain ⟨N, c, hN⟩ := h ε hε
    refine ⟨N, fun k => if hk : k < N then c ⟨k, hk⟩ else 0, ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) hN
    rw [l2ErrorWith]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    have hb : bdApproxWith N (fun k => if hk : k < N then c ⟨k, hk⟩ else 0) x
        = ∑ n : Fin N, (c n : ℂ) * rhoBD ((n : ℕ) + 1) x := by
      rw [bdApproxWith]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [k.is_lt]
    rw [hb]

/-- The approximation property is equivalent to the existence of a sequence of finite
combinations whose `L²`-errors tend to `0`. -/
theorem bdApproximable_iff_seq : BDApproximable ↔ BDApproximableSeq := by
  constructor
  · intro h
    choose N c hNc using fun k : ℕ => h (1 / (k + 1)) (by positivity)
    refine ⟨N, c, ?_⟩
    refine squeeze_zero (fun k => l2ErrorWith_nonneg _ _) (fun k => (hNc k).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · rintro ⟨N, c, h⟩ ε hε
    obtain ⟨k, hk⟩ := (h.eventually (gt_mem_nhds hε)).exists
    exact ⟨N k, c k, hk⟩

/-! ## The closure formulation -/

/-- The `ℝ`-linear span of the Báez-Duarte generators inside `L²((0,∞))`. -/
def bdSpan : Submodule ℝ L2Pos := Submodule.span ℝ (Set.range rhoL2)

lemma bdApproxL2_mem_bdSpan (N : ℕ) (c : ℕ → ℝ) : bdApproxL2 N c ∈ bdSpan := by
  rw [bdApproxL2_eq_sum]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨(k : ℕ), rfl⟩

/-- Every element of the span of the Báez-Duarte generators is a finite combination
`∑_{k<N} c_k ρ_{k+1}`. -/
lemma mem_bdSpan_iff (g : L2Pos) : g ∈ bdSpan ↔ ∃ (N : ℕ) (c : ℕ → ℝ), g = bdApproxL2 N c := by
  constructor
  · intro hg
    rw [bdSpan, Finsupp.mem_span_range_iff_exists_finsupp] at hg
    obtain ⟨c₀, hc₀⟩ := hg
    classical
    set N : ℕ := (c₀.support.sup id) + 1 with hN
    have hsupp : ∀ k ∈ c₀.support, k < N := fun k hk =>
      Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
    refine ⟨N, fun k => c₀ k, ?_⟩
    rw [bdApproxL2_eq_sum, ← hc₀, Finsupp.sum]
    rw [Fin.sum_univ_eq_sum_range (fun k => (c₀ k) • rhoL2 k) N]
    refine Finset.sum_subset (fun k hk => Finset.mem_range.2 (hsupp k hk)) ?_
    intro k _ hk
    rw [Finsupp.notMem_support_iff.1 hk, zero_smul]
  · rintro ⟨N, c, rfl⟩
    exact bdApproxL2_mem_bdSpan N c

/-- **The closure formulation.**  `χ_{(0,1]}` is approximable by finite combinations of the
Báez-Duarte generators exactly when its class lies in the closure of their span in
`L²((0,∞))`. -/
theorem bdApproximable_iff_mem_closure :
    BDApproximable ↔ chi01L2 ∈ bdSpan.topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨N, c, hN⟩ := h (ε ^ 2) (by positivity)
    refine ⟨bdApproxL2 N c, bdApproxL2_mem_bdSpan N c, ?_⟩
    rw [dist_eq_norm]
    have h1 : ‖chi01L2 - bdApproxL2 N c‖ ^ 2 < ε ^ 2 := by
      rw [← l2ErrorWith_eq_dist_sq]; exact hN
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h1
  · intro h ε hε
    obtain ⟨g, hg, hdist⟩ := h (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    obtain ⟨N, c, rfl⟩ := (mem_bdSpan_iff g).1 hg
    refine ⟨N, c, ?_⟩
    rw [l2ErrorWith_eq_dist_sq, ← dist_eq_norm]
    calc dist chi01L2 (bdApproxL2 N c) ^ 2 < Real.sqrt ε ^ 2 := by
          refine pow_lt_pow_left₀ hdist dist_nonneg (by norm_num)
      _ = ε := Real.sq_sqrt hε.le

/-! ## The criterion -/

/-- **The Nyman–Beurling criterion**, in the form stated in the query: the Riemann hypothesis
holds if and only if `χ_{(0,1]}` can be approximated in `L²((0,∞))` by finite linear
combinations `∑_{n<N} c_n ρ_{n+1}` of the Báez-Duarte generators `ρ_n(x) = {1/(n x)}`.

The classical criterion itself (Nyman 1950, Beurling 1955, Báez-Duarte 2003) is the hypothesis
`hNB`; the content proved here is that the `Fin`-indexed integral form of the approximation
property is equivalent to the form in which the criterion is stated. -/
theorem nyman_beurling_criterion (hNB : NymanBeurlingCriterion) :
    RiemannHypothesis ↔
      (∀ ε > 0, ∃ (N : ℕ) (c : Fin N → ℝ),
        (∫ x in Ioi (0:ℝ), ‖chi01 x - ∑ n : Fin N, (c n : ℂ) * rhoBD ((n : ℕ) + 1) x‖ ^ 2) < ε) :=
  hNB.trans bdApproximable_iff_fin

/-- The criterion in terms of the infimum of the `L²`-errors over all finite combinations. -/
theorem nyman_beurling_equivalent_infimum (hNB : NymanBeurlingCriterion) :
    RiemannHypothesis ↔ ∀ ε > 0, ∃ (N : ℕ) (c : ℕ → ℝ), l2ErrorWith N c < ε := hNB

/-- The criterion in terms of a sequence of approximants whose errors tend to `0`. -/
theorem nyman_beurling_seq_form (hNB : NymanBeurlingCriterion) :
    RiemannHypothesis ↔ BDApproximableSeq :=
  hNB.trans bdApproximable_iff_seq

/-- The criterion in its classical closure form: the Riemann hypothesis holds if and only if
`χ_{(0,1]}` lies in the `L²((0,∞))`-closure of the span of the Báez-Duarte generators. -/
theorem nyman_beurling_closure_form (hNB : NymanBeurlingCriterion) :
    RiemannHypothesis ↔ chi01L2 ∈ bdSpan.topologicalClosure :=
  hNB.trans bdApproximable_iff_mem_closure

/-- Decay of the log-taper `L²`-error implies the Riemann hypothesis, given the classical
criterion. -/
theorem logTaperL2Decay_implies_rh (hNB : NymanBeurlingCriterion) :
    LogTaperL2Decay → RiemannHypothesis :=
  QueryBLogTaperRH.logTaperL2Decay_implies_riemann_hypothesis hNB

end NymanBeurlingTheorem
