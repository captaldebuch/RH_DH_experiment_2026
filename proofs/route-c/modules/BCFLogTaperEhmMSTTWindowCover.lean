import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows

/-!
# Finite dyadic window cover for the Ehm--MSTT route

The MSTT interface controls sums on a full half-open interval `(S,S+H]`.
This module supplies the finite bookkeeping needed to cover the high dyadic
`m`-range `(X,2X]` by such windows.

The windows are adjacent and disjoint.  The last window is allowed to pass
the endpoint `2X`; it is clipped there, or equivalently supplied with the
cutoff weight `1_{m <= 2X}`.  This makes every analytic window have the same
length `H`, as required by `MSTTMobiusPolynomialPhaseEstimate`.

We also record the exact endpoint mismatch with an inclusive range and the
residue-class partition of a clipped window.  No MSTT estimate is assumed or
proved here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTWindowCover

open scoped BigOperators
open RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTLowRows
open RH.Criteria.NymanBeurling.BCFLogTaperMSTTPolynomialPhase

/-! ## Windows and their canonical index -/

/-- The high dyadic `m`-block to which the short-window cover applies. -/
def ehmMSTTDyadicMBlock (X : ℕ) : Finset ℕ :=
  Finset.Ioc X (2 * X)

/-- The left endpoint of the `r`-th length-`H` window. -/
def ehmMSTTWindowStart (X H r : ℕ) : ℕ :=
  X + r * H

/-- The full MSTT window `(X+rH, X+(r+1)H]`. -/
def ehmMSTTWindow (X H r : ℕ) : Finset ℕ :=
  Finset.Ioc (ehmMSTTWindowStart X H r)
    (ehmMSTTWindowStart X H r + H)

/-- A full MSTT window clipped to the dyadic endpoint `2X`. -/
def ehmMSTTClippedWindow (X H r : ℕ) : Finset ℕ :=
  (ehmMSTTWindow X H r).filter (fun m ↦ m ≤ 2 * X)

/-- One more than `X/H` windows always covers `(X,2X]`.  When `H` divides
`X`, the final indexed window is empty after clipping; this harmless padded
index avoids a divisibility case split. -/
def ehmMSTTWindowCount (X H : ℕ) : ℕ :=
  X / H + 1

/-- The unique window index attached to `m > X`. -/
def ehmMSTTWindowIndex (X H m : ℕ) : ℕ :=
  (m - (X + 1)) / H

theorem mem_ehmMSTTDyadicMBlock_iff (X m : ℕ) :
    m ∈ ehmMSTTDyadicMBlock X ↔ X < m ∧ m ≤ 2 * X := by
  simp [ehmMSTTDyadicMBlock]

theorem mem_ehmMSTTWindow_iff (X H r m : ℕ) :
    m ∈ ehmMSTTWindow X H r ↔
      ehmMSTTWindowStart X H r < m ∧
        m ≤ ehmMSTTWindowStart X H r + H := by
  simp [ehmMSTTWindow]

theorem mem_ehmMSTTClippedWindow_iff (X H r m : ℕ) :
    m ∈ ehmMSTTClippedWindow X H r ↔
      ehmMSTTWindowStart X H r < m ∧
        m ≤ ehmMSTTWindowStart X H r + H ∧ m ≤ 2 * X := by
  simp only [ehmMSTTClippedWindow, Finset.mem_filter,
    mem_ehmMSTTWindow_iff]
  tauto

theorem card_ehmMSTTWindow (X H r : ℕ) :
    (ehmMSTTWindow X H r).card = H := by
  simp [ehmMSTTWindow, Nat.card_Ioc]

theorem ehmMSTTWindowStart_ge (X H r : ℕ) :
    X ≤ ehmMSTTWindowStart X H r := by
  simp [ehmMSTTWindowStart]

/-- Every indexed left endpoint stays in `[X,2X]`. -/
theorem ehmMSTTWindowStart_le_two_mul
    (X H r : ℕ) (hH : 1 ≤ H)
    (hr : r ∈ Finset.range (ehmMSTTWindowCount X H)) :
    ehmMSTTWindowStart X H r ≤ 2 * X := by
  have hrle : r ≤ X / H := by
    have := Finset.mem_range.mp hr
    unfold ehmMSTTWindowCount at this
    omega
  have hrmul : r * H ≤ X :=
    (Nat.le_div_iff_mul_le (by omega)).mp hrle
  unfold ehmMSTTWindowStart
  omega

/-- A full indexed window can exceed `2X`, but by at most `H`. -/
theorem ehmMSTTWindowEnd_le_two_mul_add
    (X H r : ℕ) (hH : 1 ≤ H)
    (hr : r ∈ Finset.range (ehmMSTTWindowCount X H)) :
    ehmMSTTWindowStart X H r + H ≤ 2 * X + H := by
  exact Nat.add_le_add_right
    (ehmMSTTWindowStart_le_two_mul X H r hH hr) H

/-- Every point of `(X,2X]` lies in its canonical full window. -/
theorem mem_canonical_ehmMSTTWindow
    (X H m : ℕ) (hH : 1 ≤ H)
    (hm : m ∈ ehmMSTTDyadicMBlock X) :
    m ∈ ehmMSTTWindow X H (ehmMSTTWindowIndex X H m) := by
  rw [mem_ehmMSTTWindow_iff]
  have hXm : X < m := (mem_ehmMSTTDyadicMBlock_iff X m).1 hm |>.1
  have hsub : m - (X + 1) + (X + 1) = m :=
    Nat.sub_add_cancel (by omega)
  have hlo : (m - (X + 1)) / H * H ≤ m - (X + 1) :=
    Nat.div_mul_le_self _ _
  have hhi : m - (X + 1) <
      ((m - (X + 1)) / H + 1) * H :=
    (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_succ_self _)
  rw [Nat.add_mul, one_mul] at hhi
  unfold ehmMSTTWindowStart ehmMSTTWindowIndex
  constructor <;> omega

/-- The canonical window index lies in the padded finite index range. -/
theorem ehmMSTTWindowIndex_lt_count
    (X H m : ℕ)
    (hm : m ∈ ehmMSTTDyadicMBlock X) :
    ehmMSTTWindowIndex X H m < ehmMSTTWindowCount X H := by
  have hmle : m ≤ 2 * X :=
    (mem_ehmMSTTDyadicMBlock_iff X m).1 hm |>.2
  have hsuble : m - (X + 1) ≤ X := by omega
  have hdiv : (m - (X + 1)) / H ≤ X / H :=
    Nat.div_le_div_right hsuble
  unfold ehmMSTTWindowIndex ehmMSTTWindowCount
  omega

/-- Membership in a full window recovers its canonical index. -/
theorem ehmMSTTWindowIndex_eq_of_mem
    (X H r m : ℕ) (hXm : X < m)
    (hm : m ∈ ehmMSTTWindow X H r) :
    ehmMSTTWindowIndex X H m = r := by
  have hmem := (mem_ehmMSTTWindow_iff X H r m).1 hm
  have hsub : m - (X + 1) + (X + 1) = m :=
    Nat.sub_add_cancel (by omega)
  apply Nat.div_eq_of_lt_le
  · unfold ehmMSTTWindowStart at hmem
    omega
  · unfold ehmMSTTWindowStart at hmem
    have hhi : m - (X + 1) < r * H + H := by omega
    simpa only [Nat.add_mul, one_mul] using hhi

/-- Distinct full windows are disjoint.  The half-open convention assigns
their common endpoint to the earlier window only. -/
theorem ehmMSTTWindow_disjoint
    (X H r s : ℕ) (hrs : r ≠ s) :
    Disjoint (ehmMSTTWindow X H r) (ehmMSTTWindow X H s) := by
  apply Finset.disjoint_left.mpr
  intro m hmr hms
  have hXm : X < m :=
    (ehmMSTTWindowStart_ge X H r).trans_lt
      ((mem_ehmMSTTWindow_iff X H r m).1 hmr).1
  have hr := ehmMSTTWindowIndex_eq_of_mem X H r m hXm hmr
  have hs := ehmMSTTWindowIndex_eq_of_mem X H s m hXm hms
  exact hrs (hr.symm.trans hs)

/-! ## Exact dyadic cover and sum decomposition -/

theorem ehmMSTTDyadicMBlock_eq_biUnion_clippedWindows
    (X H : ℕ) (hH : 1 ≤ H) :
    ehmMSTTDyadicMBlock X =
      (Finset.range (ehmMSTTWindowCount X H)).biUnion
        (ehmMSTTClippedWindow X H) := by
  ext m
  constructor
  · intro hm
    apply Finset.mem_biUnion.mpr
    refine ⟨ehmMSTTWindowIndex X H m, ?_, ?_⟩
    · exact Finset.mem_range.mpr
        (ehmMSTTWindowIndex_lt_count X H m hm)
    · apply Finset.mem_filter.mpr
      exact ⟨mem_canonical_ehmMSTTWindow X H m hH hm,
        (mem_ehmMSTTDyadicMBlock_iff X m).1 hm |>.2⟩
  · intro hm
    rcases Finset.mem_biUnion.mp hm with ⟨r, _hr, hmr⟩
    rw [mem_ehmMSTTDyadicMBlock_iff]
    have hclip := (mem_ehmMSTTClippedWindow_iff X H r m).1 hmr
    exact ⟨(ehmMSTTWindowStart_ge X H r).trans_lt hclip.1,
      hclip.2.2⟩

theorem ehmMSTTClippedWindows_pairwiseDisjoint
    (X H : ℕ) :
    (↑(Finset.range (ehmMSTTWindowCount X H)) : Set ℕ).PairwiseDisjoint
      (ehmMSTTClippedWindow X H) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro r _hr s _hs hinter
  rcases hinter with ⟨m, hm⟩
  have hmr : m ∈ ehmMSTTWindow X H r :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp hm).1).1
  have hms : m ∈ ehmMSTTWindow X H s :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp hm).2).1
  by_contra hrs
  exact Finset.disjoint_left.mp
    (ehmMSTTWindow_disjoint X H r s hrs) hmr hms

/-- Exact decomposition of a dyadic sum into equal-length, clipped MSTT
windows. -/
theorem sum_ehmMSTTDyadicMBlock_eq_sum_clippedWindows
    {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (X H : ℕ) (hH : 1 ≤ H) :
    (∑ m ∈ ehmMSTTDyadicMBlock X, f m) =
      ∑ r ∈ Finset.range (ehmMSTTWindowCount X H),
        ∑ m ∈ ehmMSTTClippedWindow X H r, f m := by
  rw [ehmMSTTDyadicMBlock_eq_biUnion_clippedWindows X H hH,
    Finset.sum_biUnion (ehmMSTTClippedWindows_pairwiseDisjoint X H)]

/-- A clipped window is a full MSTT interval with an explicit dyadic
endpoint weight. -/
theorem sum_ehmMSTTClippedWindow_eq_fullWindow_indicator
    {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (X H r : ℕ) :
    (∑ m ∈ ehmMSTTClippedWindow X H r, f m) =
      ∑ m ∈ ehmMSTTWindow X H r,
        if m ≤ 2 * X then f m else 0 := by
  classical
  unfold ehmMSTTClippedWindow
  rw [Finset.sum_filter]

/-! ## Exact hypotheses for invoking the existing MSTT interface -/

/-- The five scale hypotheses required by the existing MSTT interface on
the shifted window based at `X+rH`.  In particular, both real-power bounds
are evaluated at this shifted base, not at the original dyadic `X`. -/
structure EhmMSTTWindowAdmissible
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (degree logSaving : ℕ) (epsilon : ℝ)
    (X H r : ℕ) : Prop where
  threshold_le :
    HM.threshold degree logSaving epsilon ≤ ehmMSTTWindowStart X H r
  base_ge_three : 3 ≤ ehmMSTTWindowStart X H r
  length_pos : 1 ≤ H
  length_lower :
    Real.rpow (ehmMSTTWindowStart X H r : ℝ)
        ((5 / 8 : ℝ) + epsilon) ≤ (H : ℝ)
  length_upper :
    (H : ℝ) ≤ Real.rpow (ehmMSTTWindowStart X H r : ℝ)
      (1 - epsilon)

/-- Threshold and elementary lower-base hypotheses transfer from the
dyadic scale to every shifted window.  The two real-power length bounds do
not follow from this lemma and remain fields of `EhmMSTTWindowAdmissible`. -/
theorem ehmMSTTWindowStart_elementary_hypotheses
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (degree logSaving : ℕ) (epsilon : ℝ)
    (X H r : ℕ)
    (hthreshold : HM.threshold degree logSaving epsilon ≤ X)
    (hX : 3 ≤ X) :
    HM.threshold degree logSaving epsilon ≤
        ehmMSTTWindowStart X H r ∧
      3 ≤ ehmMSTTWindowStart X H r := by
  exact ⟨hthreshold.trans (ehmMSTTWindowStart_ge X H r),
    hX.trans (ehmMSTTWindowStart_ge X H r)⟩

/-- Direct application of the existing weighted MSTT theorem on one full
window of the finite cover. -/
theorem norm_weighted_ehmMSTTWindow_le
    (HM : MSTTMobiusPolynomialPhaseEstimate)
    (degree logSaving : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (X H r : ℕ)
    (hwindow : EhmMSTTWindowAdmissible
      HM degree logSaving epsilon X H r)
    (P : Polynomial ℝ) (hdegree : P.natDegree ≤ degree)
    (w : ℕ → ℂ) :
    ‖∑ m ∈ ehmMSTTWindow X H r,
        ((((ArithmeticFunction.moebius m : ℤ) : ℂ) *
          msttPolynomialPhase P m) * w m)‖ ≤
      (HM.constant degree logSaving epsilon * (H : ℝ) /
          (Real.log (ehmMSTTWindowStart X H r : ℝ)) ^ logSaving) *
        complexWeightVariation w
          (ehmMSTTWindowStart X H r + 1)
          (ehmMSTTWindowStart X H r + H) := by
  unfold ehmMSTTWindow
  exact norm_weighted_msttMobiusPolynomialBlock_le HM degree logSaving
    epsilon hepsilon (ehmMSTTWindowStart X H r) H
    hwindow.threshold_le hwindow.base_ge_three hwindow.length_pos
    hwindow.length_lower hwindow.length_upper P hdegree w

/-! ## Inclusive endpoints and the full current `m`-range -/

/-- The inclusive block `[X,2X]` consists of the uncovered endpoint `X`
and the MSTT-compatible half-open block `(X,2X]`. -/
theorem Icc_eq_insert_ehmMSTTDyadicMBlock (X : ℕ) :
    Finset.Icc X (2 * X) = insert X (ehmMSTTDyadicMBlock X) := by
  ext m
  simp only [Finset.mem_Icc, Finset.mem_insert,
    mem_ehmMSTTDyadicMBlock_iff]
  omega

theorem sum_Icc_eq_endpoint_add_ehmMSTTDyadicMBlock
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (X : ℕ) :
    (∑ m ∈ Finset.Icc X (2 * X), f m) =
      f X + ∑ m ∈ ehmMSTTDyadicMBlock X, f m := by
  classical
  rw [Icc_eq_insert_ehmMSTTDyadicMBlock]
  simp [ehmMSTTDyadicMBlock]

/-- The complete current paired-row support `1 <= m <= 2X` contains a
low range `1 <= m <= X` in addition to the high dyadic MSTT block. -/
theorem Icc_one_two_mul_eq_low_union_ehmMSTTDyadicMBlock (X : ℕ) :
    Finset.Icc 1 (2 * X) =
      Finset.Icc 1 X ∪ ehmMSTTDyadicMBlock X := by
  ext m
  simp only [Finset.mem_Icc, Finset.mem_union,
    mem_ehmMSTTDyadicMBlock_iff]
  omega

theorem sum_Icc_one_two_mul_eq_low_add_dyadic
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (X : ℕ) :
    (∑ m ∈ Finset.Icc 1 (2 * X), f m) =
      (∑ m ∈ Finset.Icc 1 X, f m) +
        ∑ m ∈ ehmMSTTDyadicMBlock X, f m := by
  rw [Icc_one_two_mul_eq_low_union_ehmMSTTDyadicMBlock]
  apply Finset.sum_union
  apply Finset.disjoint_left.mpr
  intro m hmLow hmHigh
  have hmX := (Finset.mem_Icc.mp hmLow).2
  have hXm := (mem_ehmMSTTDyadicMBlock_iff X m).1 hmHigh |>.1
  omega

/-! ## Arithmetic subprogressions inside one window -/

/-- One residue class inside a clipped MSTT window. -/
def ehmMSTTClippedWindowResidue
    (X H r q a : ℕ) : Finset ℕ :=
  (ehmMSTTClippedWindow X H r).filter (fun m ↦ m % q = a)

theorem mem_ehmMSTTClippedWindowResidue_iff
    (X H r q a m : ℕ) :
    m ∈ ehmMSTTClippedWindowResidue X H r q a ↔
      m ∈ ehmMSTTClippedWindow X H r ∧ m % q = a := by
  simp [ehmMSTTClippedWindowResidue]

/-- Residues `0,...,q-1` partition a clipped window when `q>0`. -/
theorem ehmMSTTClippedWindow_eq_biUnion_residues
    (X H r q : ℕ) (hq : 1 ≤ q) :
    ehmMSTTClippedWindow X H r =
      (Finset.range q).biUnion
        (ehmMSTTClippedWindowResidue X H r q) := by
  ext m
  constructor
  · intro hm
    apply Finset.mem_biUnion.mpr
    refine ⟨m % q, Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
    exact Finset.mem_filter.mpr ⟨hm, rfl⟩
  · intro hm
    rcases Finset.mem_biUnion.mp hm with ⟨a, _ha, hma⟩
    exact (Finset.mem_filter.mp hma).1

theorem ehmMSTTClippedWindowResidues_pairwiseDisjoint
    (X H r q : ℕ) :
    (↑(Finset.range q) : Set ℕ).PairwiseDisjoint
      (ehmMSTTClippedWindowResidue X H r q) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro a _ha b _hb hinter
  rcases hinter with ⟨m, hm⟩
  have hma := (Finset.mem_filter.mp (Finset.mem_inter.mp hm).1).2
  have hmb := (Finset.mem_filter.mp (Finset.mem_inter.mp hm).2).2
  exact hma.symm.trans hmb

/-- Exact residue-class decomposition of a clipped-window sum.  The MSTT
interface itself controls the full interval; applying it to one residue
class requires either this indicator as a weight (and its variation loss)
or an additional progression-uniform analytic theorem. -/
theorem sum_ehmMSTTClippedWindow_eq_sum_residues
    {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (X H r q : ℕ) (hq : 1 ≤ q) :
    (∑ m ∈ ehmMSTTClippedWindow X H r, f m) =
      ∑ a ∈ Finset.range q,
        ∑ m ∈ ehmMSTTClippedWindowResidue X H r q a, f m := by
  rw [ehmMSTTClippedWindow_eq_biUnion_residues X H r q hq,
    Finset.sum_biUnion
      (ehmMSTTClippedWindowResidues_pairwiseDisjoint X H r q)]

/-- A residue subprogression is a full MSTT window with both its dyadic
endpoint and congruence conditions retained as an explicit weight. -/
theorem sum_ehmMSTTClippedWindowResidue_eq_fullWindow_indicator
    {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (X H r q a : ℕ) :
    (∑ m ∈ ehmMSTTClippedWindowResidue X H r q a, f m) =
      ∑ m ∈ ehmMSTTWindow X H r,
        if m ≤ 2 * X ∧ m % q = a then f m else 0 := by
  classical
  unfold ehmMSTTClippedWindowResidue ehmMSTTClippedWindow
  simp only [Finset.filter_filter]
  rw [Finset.sum_filter]

end RH.Criteria.NymanBeurling.BCFLogTaperEhmMSTTWindowCover
