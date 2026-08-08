import Mathlib

/-!
# Hardy space `H²` of the circle: basic infrastructure

This file sets up the Hilbert-space model of the Hardy space `H²` used in the formalization of
Beurling's theorem on shift-invariant subspaces.

We work with the space `L²(𝕋)` of square-integrable functions on the circle
`𝕋 = AddCircle 1`, equipped with the Haar probability measure, and we identify

* the *Hardy space* `H²` with the closed subspace of `L²(𝕋)` consisting of the functions all of
  whose negative Fourier coefficients vanish (the boundary-value model of the Hardy space of the
  unit disc), and
* the *shift* `S` with multiplication by the character `fourier 1 : x ↦ e^{2πix}`.

The main definitions are:

* `Beurling.Unimodular g` : `g` is a.e.-measurable with `‖g x‖ = 1` almost everywhere;
* `Beurling.mulL2 hg` : the linear isometry of `L²(𝕋)` given by multiplication by such a `g`;
* `Beurling.shiftL2` : the shift operator;
* `Beurling.HardyFrom N` : the closed subspace of functions whose Fourier coefficients vanish
  below `N`; `Beurling.Hardy2 = HardyFrom 0` is the Hardy space itself.
-/

open MeasureTheory Complex Submodule

noncomputable section

namespace Beurling

/-- The circle, as the additive circle of period one. -/
abbrev Circ := AddCircle (1 : ℝ)

instance factOneCirc : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- Haar probability measure on the circle. -/
abbrev mu : Measure Circ := AddCircle.haarAddCircle

/-- The Hilbert space `L²(𝕋)`. -/
abbrev L2C := Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))

/-! ### Multiplication by a unimodular function -/

/-- A function on the circle which is a.e. measurable and has modulus one a.e. -/
structure Unimodular (g : Circ → ℂ) : Prop where
  meas : AEStronglyMeasurable g mu
  norm_eq : ∀ᵐ x ∂mu, ‖g x‖ = 1

lemma memLp_mul {g : Circ → ℂ} (hg : Unimodular g) (f : L2C) :
    MemLp (fun x => g x * (f : Circ → ℂ) x) 2 mu := by
  refine MemLp.mono (Lp.memLp f) (hg.meas.mul (Lp.aestronglyMeasurable f)) ?_
  filter_upwards [hg.norm_eq] with x hx
  simp [hx]

/-- Multiplication by a unimodular function is a linear isometry of `L²(𝕋)`. -/
def mulL2 {g : Circ → ℂ} (hg : Unimodular g) : L2C →ₗᵢ[ℂ] L2C where
  toFun f := (memLp_mul hg f).toLp _
  map_add' f₁ f₂ := by
    apply Lp.ext
    filter_upwards [(memLp_mul hg (f₁ + f₂)).coeFn_toLp,
      Lp.coeFn_add ((memLp_mul hg f₁).toLp _) ((memLp_mul hg f₂).toLp _),
      (memLp_mul hg f₁).coeFn_toLp, (memLp_mul hg f₂).coeFn_toLp, Lp.coeFn_add f₁ f₂] with
      x h1 h2 h3 h4 h5
    rw [h1, h2]
    simp only [Pi.add_apply] at *
    rw [h3, h4, h5]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_mul hg (c • f)).coeFn_toLp, Lp.coeFn_smul c ((memLp_mul hg f).toLp _),
      (memLp_mul hg f).coeFn_toLp, Lp.coeFn_smul c f] with x h1 h2 h3 h4
    simp only [RingHom.id_apply] at *
    rw [h1, h2]
    simp only [Pi.smul_apply, smul_eq_mul] at *
    rw [h3, h4]
    ring
  norm_map' f := by
    change ‖(memLp_mul hg f).toLp _‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
    filter_upwards [(memLp_mul hg f).coeFn_toLp, hg.norm_eq] with x h1 h2
    rw [h1]
    simp [h2]

lemma mulL2_coeFn {g : Circ → ℂ} (hg : Unimodular g) (f : L2C) :
    ⇑(mulL2 hg f) =ᵐ[mu] fun x => g x * (f : Circ → ℂ) x :=
  (memLp_mul hg f).coeFn_toLp

lemma norm_fourier_apply (n : ℤ) (x : Circ) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

lemma unimodular_fourier (n : ℤ) : Unimodular (fun x => fourier n x) :=
  ⟨(map_continuous (fourier n)).aestronglyMeasurable, .of_forall (norm_fourier_apply n)⟩

/-- The shift operator on `L²(𝕋)`: multiplication by `fourier 1`. -/
def shiftL2 : L2C →ₗᵢ[ℂ] L2C := mulL2 (unimodular_fourier 1)

/-! ### Fourier coefficients -/

lemma fourierCoeff_eq_inner (f : L2C) (n : ℤ) :
    fourierCoeff (⇑f) n = inner ℂ (fourierLp 2 n) f := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply, coe_fourierBasis]

lemma eq_zero_of_fourierCoeff_eq_zero {f : L2C} (h : ∀ n : ℤ, fourierCoeff (⇑f) n = 0) : f = 0 := by
  have hs := hasSum_fourier_series_L2 f
  simp only [h, zero_smul] at hs
  exact hs.unique hasSum_zero

/-- Multiplying by the character `fourier m` shifts Fourier coefficients by `m`. -/
lemma fourierCoeff_mulL2_fourier (m n : ℤ) (f : L2C) :
    fourierCoeff (⇑(mulL2 (unimodular_fourier m) f)) n = fourierCoeff (⇑f) (n - m) := by
  rw [fourierCoeff_congr_ae (mulL2_coeFn (unimodular_fourier m) f)]
  simp only [fourierCoeff, smul_eq_mul]
  congr 1
  ext x
  rw [← mul_assoc, ← fourier_add, show -n + m = -(n - m) by ring]

lemma fourierCoeff_shiftL2 (n : ℤ) (f : L2C) :
    fourierCoeff (⇑(shiftL2 f)) n = fourierCoeff (⇑f) (n - 1) :=
  fourierCoeff_mulL2_fourier 1 n f

/-! ### The Hardy spaces `HardyFrom N` -/

/-- `HardyFrom N` is the closed subspace of `L²(𝕋)` of functions whose Fourier coefficients
vanish at all indices `< N`. -/
def HardyFrom (N : ℤ) : Submodule ℂ L2C :=
  (Submodule.span ℂ (fourierLp 2 '' {n : ℤ | n < N}))ᗮ

/-- The Hardy space `H²`, viewed inside `L²(𝕋)`: the functions whose negative Fourier
coefficients all vanish. -/
abbrev Hardy2 : Submodule ℂ L2C := HardyFrom 0

lemma mem_HardyFrom {N : ℤ} {f : L2C} :
    f ∈ HardyFrom N ↔ ∀ n : ℤ, n < N → fourierCoeff (⇑f) n = 0 := by
  constructor
  · intro hf n hn
    rw [fourierCoeff_eq_inner]
    exact hf _ (Submodule.subset_span ⟨n, hn, rfl⟩)
  · intro hf
    rw [HardyFrom, Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨n, hn, rfl⟩ := hx
        rw [← fourierCoeff_eq_inner]
        exact hf n hn
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
    | smul c x _ hx => simp [inner_smul_left, hx]

lemma isClosed_HardyFrom (N : ℤ) : IsClosed (HardyFrom N : Set L2C) :=
  Submodule.isClosed_orthogonal _

lemma shiftL2_mem_HardyFrom {N : ℤ} {f : L2C} (hf : f ∈ HardyFrom N) :
    shiftL2 f ∈ HardyFrom (N + 1) := by
  rw [mem_HardyFrom] at hf ⊢
  intro n hn
  rw [fourierCoeff_shiftL2]
  exact hf _ (by omega)

lemma HardyFrom_antitone {N M : ℤ} (h : M ≤ N) : HardyFrom N ≤ HardyFrom M := by
  intro f hf
  rw [mem_HardyFrom] at hf ⊢
  exact fun n hn => hf n (lt_of_lt_of_le hn h)

lemma eq_zero_of_mem_all_HardyFrom {f : L2C} (h : ∀ N : ℤ, f ∈ HardyFrom N) : f = 0 :=
  eq_zero_of_fourierCoeff_eq_zero fun n => (mem_HardyFrom.mp (h (n + 1))) n (by omega)

/-- `H²` is the closed linear span of the characters `fourier n`, `n ≥ 0`. -/
lemma Hardy2_eq_closure_span :
    Hardy2 = (Submodule.span ℂ (fourierLp 2 '' {n : ℤ | 0 ≤ n})).topologicalClosure := by
  apply le_antisymm
  · intro f hf
    have hs := hasSum_fourier_series_L2 f
    refine mem_closure_of_tendsto hs ?_
    filter_upwards with s
    refine Submodule.sum_mem _ fun n _ => ?_
    rcases lt_or_ge n 0 with hn | hn
    · rw [mem_HardyFrom.mp hf n hn, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, hn, rfl⟩)
  · refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_HardyFrom 0)
    rw [Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    simp only [Set.mem_setOf_eq] at hn
    rw [SetLike.mem_coe, mem_HardyFrom]
    intro m hm
    have hmn : m ≠ n := by omega
    rw [fourierCoeff_congr_ae (coeFn_fourierLp 2 n), fourierCoeff_fourier]
    simp [hmn]

end Beurling
