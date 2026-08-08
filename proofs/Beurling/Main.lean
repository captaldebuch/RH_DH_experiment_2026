import Beurling.FourierUniqueness

/-!
# Beurling's theorem on shift-invariant subspaces

This file proves **Beurling's theorem** (1949/1955) in the boundary-value model of the Hardy
space `H²` of the unit disc: every closed subspace `M` of `H²` which is invariant under the
shift `S : f ↦ z·f` is either trivial or of the form `M = θ · H²` for an inner function `θ`,
i.e. an element of `H²` of modulus one almost everywhere on the circle.

The proof follows the classical argument, but avoids the Wold decomposition:

* the *wandering vector* `e` is obtained as a unit vector of `M` orthogonal to the closure of
  `S(M)`; such a vector exists because otherwise `M ⊆ ⋂ₙ zⁿ H² = 0`;
* since `e ⊥ zⁿ e` for all `n ≥ 1` and `‖e‖ = 1`, all Fourier coefficients of `|e|² - 1`
  vanish, so `|e| = 1` a.e. by the `L¹` uniqueness theorem
  (`Beurling.ae_eq_zero_of_fourierCoeff_eq_zero`);  in other words `e` is inner;
* every `f ∈ M` equals `e · g` with `g = ē · f ∈ H²`, because the negative Fourier coefficients
  of `ē f` are the inner products `⟪e, zⁿ f⟫ = 0`;
* conversely `e · H² ⊆ M` because `e · zⁿ = Sⁿ e ∈ M` and `M` is closed.
-/

open MeasureTheory Complex Submodule Filter Topology

noncomputable section

namespace Beurling

/-! ### Elementary lemmas on multiplication operators -/

lemma mulL2_ext {g₁ g₂ : Circ → ℂ} (h1 : Unimodular g₁) (h2 : Unimodular g₂) {f₁ f₂ : L2C}
    (h : (fun x => g₁ x * (f₁ : Circ → ℂ) x) =ᵐ[mu] fun x => g₂ x * (f₂ : Circ → ℂ) x) :
    mulL2 h1 f₁ = mulL2 h2 f₂ := by
  apply Lp.ext
  filter_upwards [mulL2_coeFn h1 f₁, mulL2_coeFn h2 f₂, h] with x hx1 hx2 hx
  rw [hx1, hx2]
  exact hx

lemma mulL2_eq_self {g : Circ → ℂ} (h1 : Unimodular g) {f₁ f₂ : L2C}
    (h : (fun x => g x * (f₁ : Circ → ℂ) x) =ᵐ[mu] (f₂ : Circ → ℂ)) : mulL2 h1 f₁ = f₂ := by
  apply Lp.ext
  filter_upwards [mulL2_coeFn h1 f₁, h] with x hx1 hx
  rw [hx1]
  exact hx

lemma mulL2_fourier_zero (f : L2C) : mulL2 (unimodular_fourier 0) f = f := by
  refine mulL2_eq_self _ ?_
  filter_upwards with x
  simp

lemma mulL2_fourier_succ (n : ℤ) (f : L2C) :
    mulL2 (unimodular_fourier (n + 1)) f = shiftL2 (mulL2 (unimodular_fourier n) f) := by
  rw [shiftL2]
  refine mulL2_ext _ _ ?_
  filter_upwards [mulL2_coeFn (unimodular_fourier n) f] with x hx
  rw [hx, fourier_add]
  ring

/-- Multiplication by `fourier n` applied to `e` is the same as multiplication by `e` applied to
the character `fourier n`. -/
lemma mulL2_fourier_comm {e : L2C} (hu : Unimodular (e : Circ → ℂ)) (n : ℤ) :
    mulL2 (unimodular_fourier n) e = mulL2 hu (fourierLp 2 n) := by
  refine mulL2_ext _ _ ?_
  filter_upwards [coeFn_fourierLp 2 n] with x hx
  rw [hx]
  ring

/-- The inner product `⟪a, zⁿ b⟫` as an integral. -/
lemma inner_mulL2_fourier (a b : L2C) (n : ℤ) :
    inner ℂ a (mulL2 (unimodular_fourier n) b) =
      ∫ x, fourier n x * ((starRingEnd ℂ) ((a : Circ → ℂ) x) * (b : Circ → ℂ) x) ∂mu := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulL2_coeFn (unimodular_fourier n) b] with x hx
  rw [hx, RCLike.inner_apply]
  ring

/-! ### Inner functions -/

/-- An **inner function** in the boundary-value model: an element of `H²` whose modulus is one
almost everywhere on the circle. -/
structure IsInner (e : L2C) : Prop where
  mem : e ∈ Hardy2
  modulus_one : ∀ᵐ x ∂mu, ‖(e : Circ → ℂ) x‖ = 1

lemma IsInner.unimodular {e : L2C} (he : IsInner e) : Unimodular (e : Circ → ℂ) :=
  ⟨Lp.aestronglyMeasurable e, he.modulus_one⟩

/-- Multiplication by an inner function, as a linear isometry of `L²(𝕋)`. -/
def innerMul {e : L2C} (he : IsInner e) : L2C →ₗᵢ[ℂ] L2C := mulL2 he.unimodular

/-! ### Auxiliary steps of the proof -/

/-- If `M` is contained in the closure of its shift, then it is contained in every `HardyFrom N`,
`N ≥ 0`. -/
lemma le_HardyFrom_of_le_shift {M : Submodule ℂ L2C} (hMH : M ≤ Hardy2)
    (hEq : M ≤ (Submodule.map shiftL2.toLinearMap M).topologicalClosure) (N : ℕ) :
    M ≤ HardyFrom (N : ℤ) := by
  induction N with
  | zero => simpa using hMH
  | succ n ih =>
      intro f hf
      have hmem : f ∈ (Submodule.map shiftL2.toLinearMap M).topologicalClosure := hEq hf
      have : (Submodule.map shiftL2.toLinearMap M).topologicalClosure ≤
          HardyFrom ((n : ℤ) + 1) := by
        refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_HardyFrom _)
        rintro _ ⟨g, hg, rfl⟩
        exact shiftL2_mem_HardyFrom (ih hg)
      have := this hmem
      simpa [Nat.cast_succ] using this

/-- A nonzero closed shift-invariant subspace of `H²` is strictly larger than the closure of its
shift; hence it contains a nonzero *wandering vector*. -/
lemma exists_wandering {M : Submodule ℂ L2C} (hMH : M ≤ Hardy2) (hM0 : M ≠ ⊥) :
    ∃ v ∈ M, v ∉ (Submodule.map shiftL2.toLinearMap M).topologicalClosure := by
  by_contra h
  push_neg at h
  apply hM0
  rw [Submodule.eq_bot_iff]
  intro f hf
  refine eq_zero_of_mem_all_HardyFrom fun N => ?_
  obtain ⟨n, hn⟩ : ∃ n : ℕ, N ≤ (n : ℤ) := ⟨N.toNat, Int.self_le_toNat N⟩
  exact HardyFrom_antitone hn (le_HardyFrom_of_le_shift hMH (fun g hg => h g hg) n hf)

/-! ### The wandering vector is inner -/

lemma integrable_fourier_mul {g : Circ → ℂ} (hg : Integrable g mu) (n : ℤ) :
    Integrable (fun x => fourier n x * g x) mu :=
  hg.bdd_mul (map_continuous (fourier n)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => le_of_eq (norm_fourier_apply n x))

lemma integrable_fourier (n : ℤ) : Integrable (⇑(fourier (T := (1 : ℝ)) n)) mu := by
  have h : Integrable (fun _ : Circ => (1 : ℂ)) mu := integrable_const 1
  simpa using h.bdd_mul (map_continuous (fourier n)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => le_of_eq (norm_fourier_apply n x))

lemma integral_fourier_eq_zero {n : ℤ} (hn : n ≠ 0) : ∫ x, fourier n x ∂mu = 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) 0) (-n)
  simp only [fourierCoeff, smul_eq_mul, fourier_zero, mul_one, neg_neg] at h
  rw [h, Pi.single_apply, if_neg (by omega)]

/-- If a unit vector `e` of `L²(𝕋)` is orthogonal to all its forward shifts `zⁿ e`, `n ≥ 1`,
then `|e| = 1` almost everywhere. -/
lemma modulus_one_of_orthogonal {e : L2C} (henorm : ‖e‖ = 1)
    (horth : ∀ n : ℤ, 1 ≤ n → inner ℂ e (mulL2 (unimodular_fourier n) e) = (0 : ℂ)) :
    ∀ᵐ x ∂mu, ‖(e : Circ → ℂ) x‖ = 1 := by
  set F : Circ → ℂ := fun x => ((‖(e : Circ → ℂ) x‖ : ℂ)) ^ 2 with hFdef
  have hFint : Integrable F mu := by
    have h := L2.integrable_inner (𝕜 := ℂ) e e
    simpa [RCLike.inner_apply] using h
  have hinner : ∀ n : ℤ,
      inner ℂ e (mulL2 (unimodular_fourier n) e) = ∫ x, fourier n x * F x ∂mu := by
    intro n
    rw [inner_mulL2_fourier]
    exact integral_congr_ae (.of_forall fun x => by simp only [hFdef, Complex.conj_mul'])
  have hFzero : ∀ n : ℤ, n ≠ 0 → ∫ x, fourier n x * F x ∂mu = 0 := by
    intro n hn
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · have h1 : ∫ x, fourier (-n) x * F x ∂mu = 0 := by
        have h := horth (-n) (by omega)
        rwa [hinner (-n)] at h
      have h2 : ∫ x, fourier n x * F x ∂mu
          = (starRingEnd ℂ) (∫ x, fourier (-n) x * F x ∂mu) := by
        rw [← integral_conj]
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp [hFdef, map_mul]
      rw [h2, h1, map_zero]
    · have h := horth n (by omega)
      rwa [hinner n] at h
  have hFone : ∫ x, F x ∂mu = 1 := by
    have h := hinner 0
    rw [mulL2_fourier_zero, inner_self_eq_norm_sq_to_K, henorm] at h
    simpa using h.symm
  have hw : ∀ n : ℤ, fourierCoeff (fun x => F x - 1) n = 0 := by
    intro n
    have hsplit : fourierCoeff (fun x => F x - 1) n
        = (∫ x, fourier (-n) x * F x ∂mu) - ∫ x, fourier (-n) x ∂mu := by
      simp only [fourierCoeff, smul_eq_mul, mul_sub, mul_one]
      exact integral_sub (integrable_fourier_mul hFint _) (integrable_fourier (-n))
    rw [hsplit]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hFone]
    · rw [hFzero (-n) (by omega), integral_fourier_eq_zero (by omega), sub_zero]
  have hae := ae_eq_zero_of_fourierCoeff_eq_zero (hFint.sub (integrable_const 1)) hw
  filter_upwards [hae] with x hx
  have h0 : ((‖(e : Circ → ℂ) x‖ : ℂ)) ^ 2 = 1 := by
    have h : F x - 1 = 0 := hx
    rwa [sub_eq_zero] at h
  have h1 := congrArg norm h0
  simp only [norm_pow, Complex.norm_real, norm_norm, norm_one] at h1
  nlinarith [norm_nonneg ((e : Circ → ℂ) x)]

/-! ### `M` is contained in `e · H²` -/

lemma IsInner.conjUnimodular {e : L2C} (he : IsInner e) :
    Unimodular (fun x => (starRingEnd ℂ) ((e : Circ → ℂ) x)) := by
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable e), ?_⟩
  filter_upwards [he.modulus_one] with x hx
  simpa using hx

/-- If `e` is inner and orthogonal to all forward shifts `zⁿ f` (`n ≥ 1`) of elements of `M`,
then every `f ∈ M` lies in `e · H²`. -/
lemma mem_map_innerMul {M : Submodule ℂ L2C} {e : L2C} (he : IsInner e)
    (horth : ∀ f ∈ M, ∀ n : ℤ, 1 ≤ n → inner ℂ e (mulL2 (unimodular_fourier n) f) = (0 : ℂ))
    {f : L2C} (hf : f ∈ M) :
    f ∈ Submodule.map (innerMul he).toLinearMap Hardy2 := by
  refine ⟨mulL2 he.conjUnimodular f, ?_, ?_⟩
  · change mulL2 he.conjUnimodular f ∈ Hardy2
    rw [mem_HardyFrom]
    intro m hm
    have h1 : fourierCoeff (⇑(mulL2 he.conjUnimodular f)) m
        = inner ℂ e (mulL2 (unimodular_fourier (-m)) f) := by
      rw [inner_mulL2_fourier]
      refine integral_congr_ae ?_
      filter_upwards [mulL2_coeFn he.conjUnimodular f] with x hx
      simp only [smul_eq_mul, hx]
    rw [h1]
    exact horth f hf (-m) (by omega)
  · refine mulL2_eq_self he.unimodular ?_
    filter_upwards [mulL2_coeFn he.conjUnimodular f, he.modulus_one] with x h1 h2
    simp only [h1]
    have h3 : (e : Circ → ℂ) x * (starRingEnd ℂ) ((e : Circ → ℂ) x) = 1 := by
      rw [Complex.mul_conj', h2]
      norm_num
    rw [← mul_assoc, h3, one_mul]

/-! ### `e · H²` is contained in `M` -/

lemma map_innerMul_le {M : Submodule ℂ L2C} {e : L2C} (he : IsInner e)
    (hMclosed : IsClosed (M : Set L2C))
    (hshift : ∀ n : ℤ, 0 ≤ n → mulL2 (unimodular_fourier n) e ∈ M) :
    Submodule.map (innerMul he).toLinearMap Hardy2 ≤ M := by
  rw [Submodule.map_le_iff_le_comap, Hardy2_eq_closure_span]
  refine Submodule.topologicalClosure_minimal _ ?_
    (hMclosed.preimage (innerMul he).continuous)
  rw [Submodule.span_le]
  rintro _ ⟨n, hn, rfl⟩
  simp only [Set.mem_setOf_eq] at hn
  have hmem : (innerMul he) (fourierLp 2 n) ∈ M := by
    rw [innerMul, ← mulL2_fourier_comm he.unimodular n]
    exact hshift n hn
  exact hmem

/-! ### Beurling's theorem -/

/-- The main construction: from a wandering vector one produces the inner function. -/
lemma exists_isInner_of_wandering (M : Submodule ℂ L2C) (hMH : M ≤ Hardy2)
    (hMclosed : IsClosed (M : Set L2C)) (SM : Submodule ℂ L2C)
    (hSMclosed : IsClosed (SM : Set L2C)) (hSMle : SM ≤ M)
    (hpowM : ∀ n : ℕ, ∀ f ∈ M, mulL2 (unimodular_fourier (n : ℤ)) f ∈ M)
    (hpowSM : ∀ n : ℤ, 1 ≤ n → ∀ f ∈ M, mulL2 (unimodular_fourier n) f ∈ SM)
    (v : L2C) (hvM : v ∈ M) (hvSM : v ∉ SM) :
    ∃ (e : L2C) (he : IsInner e), M = Submodule.map (innerMul he).toLinearMap Hardy2 := by
  haveI : CompleteSpace SM := hSMclosed.completeSpace_coe
  set e₁ := v - SM.starProjection v with he₁def
  have he₁M : e₁ ∈ M := M.sub_mem hvM (hSMle (SM.starProjection_apply_mem v))
  have he₁perp : e₁ ∈ SMᗮ := SM.sub_starProjection_mem_orthogonal v
  have he₁ne : e₁ ≠ 0 := by
    intro h
    apply hvSM
    have hv : v = SM.starProjection v := by rw [he₁def] at h; rwa [sub_eq_zero] at h
    rw [hv]
    exact SM.starProjection_apply_mem v
  have hnorm₁ : ‖e₁‖ ≠ 0 := norm_ne_zero_iff.mpr he₁ne
  set e := ((‖e₁‖ : ℂ))⁻¹ • e₁ with hedef
  have henorm : ‖e‖ = 1 := by
    rw [hedef, norm_smul, norm_inv, Complex.norm_real, norm_norm]
    field_simp
  have heM : e ∈ M := M.smul_mem _ he₁M
  have heperp : e ∈ SMᗮ := SMᗮ.smul_mem _ he₁perp
  have horth : ∀ f ∈ M, ∀ n : ℤ, 1 ≤ n → inner ℂ e (mulL2 (unimodular_fourier n) f) = (0 : ℂ) := by
    intro f hf n hn
    have hu := hpowSM n hn f hf
    have h0 : inner ℂ (mulL2 (unimodular_fourier n) f) e = (0 : ℂ) := heperp _ hu
    exact inner_eq_zero_symm.mp h0
  have heInner : IsInner e := ⟨hMH heM, modulus_one_of_orthogonal henorm (horth e heM)⟩
  refine ⟨e, heInner, le_antisymm (fun f hf => mem_map_innerMul heInner horth hf) ?_⟩
  refine map_innerMul_le heInner hMclosed ?_
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
  exact hpowM k e heM

/-- **Beurling's theorem**.  A closed subspace `M` of the Hardy space `H²` which is invariant
under the shift `S : f ↦ z · f` is either the zero subspace or of the form `M = θ · H²`, where
`θ` is an inner function, i.e. an element of `H²` of modulus one almost everywhere on the
circle. -/
theorem beurling_shift_invariant_subspace (M : Submodule ℂ L2C) (hMH : M ≤ Hardy2)
    (hMclosed : IsClosed (M : Set L2C)) (hMinv : ∀ f ∈ M, shiftL2 f ∈ M) :
    M = ⊥ ∨ ∃ (e : L2C) (he : IsInner e),
      M = Submodule.map (innerMul he).toLinearMap Hardy2 := by
  by_cases hM0 : M = ⊥
  · exact Or.inl hM0
  right
  set SM : Submodule ℂ L2C := (Submodule.map shiftL2.toLinearMap M).topologicalClosure with hSMdef
  have hSMclosed : IsClosed (SM : Set L2C) := Submodule.isClosed_topologicalClosure _
  have hSMle : SM ≤ M := by
    refine Submodule.topologicalClosure_minimal _ ?_ hMclosed
    rintro _ ⟨f, hf, rfl⟩
    exact hMinv f hf
  have hpowM : ∀ n : ℕ, ∀ f ∈ M, mulL2 (unimodular_fourier (n : ℤ)) f ∈ M := by
    intro n
    induction n with
    | zero => intro f hf; rwa [Nat.cast_zero, mulL2_fourier_zero]
    | succ k ih =>
        intro f hf
        have hc : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
        rw [hc, mulL2_fourier_succ]
        exact hMinv _ (ih f hf)
  have hpowSM : ∀ n : ℤ, 1 ≤ n → ∀ f ∈ M, mulL2 (unimodular_fourier n) f ∈ SM := by
    intro n hn f hf
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
    rw [mulL2_fourier_succ]
    exact Submodule.le_topologicalClosure _ ⟨_, hpowM k f hf, rfl⟩
  obtain ⟨v, hvM, hvSM⟩ := exists_wandering hMH hM0
  exact exists_isInner_of_wandering M hMH hMclosed SM hSMclosed hSMle hpowM hpowSM v hvM hvSM

/-! ### The converse direction, and a pointwise restatement -/

lemma mulL2_fourier_mem_HardyFrom {e : L2C} (he : e ∈ Hardy2) :
    ∀ n : ℕ, mulL2 (unimodular_fourier (n : ℤ)) e ∈ HardyFrom (n : ℤ) := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, mulL2_fourier_zero]; exact he
  | succ k ih =>
      have hc : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [hc, mulL2_fourier_succ]
      exact shiftL2_mem_HardyFrom ih

lemma shiftL2_mem_Hardy2 {f : L2C} (hf : f ∈ Hardy2) : shiftL2 f ∈ Hardy2 :=
  HardyFrom_antitone (by norm_num) (shiftL2_mem_HardyFrom hf)

lemma shiftL2_mulL2_comm {g : Circ → ℂ} (hg : Unimodular g) (f : L2C) :
    shiftL2 (mulL2 hg f) = mulL2 hg (shiftL2 f) := by
  rw [shiftL2]
  refine mulL2_ext _ _ ?_
  filter_upwards [mulL2_coeFn hg f, mulL2_coeFn (unimodular_fourier 1) f] with x h1 h2
  rw [h1, h2]
  ring

/-- **Converse of Beurling's theorem**: for every inner function `θ`, the subspace `θ · H²` is a
closed, shift-invariant subspace of `H²`. -/
theorem map_innerMul_isShiftInvariant {e : L2C} (he : IsInner e) :
    Submodule.map (innerMul he).toLinearMap Hardy2 ≤ Hardy2 ∧
      IsClosed ((Submodule.map (innerMul he).toLinearMap Hardy2 : Submodule ℂ L2C) : Set L2C) ∧
      ∀ f ∈ Submodule.map (innerMul he).toLinearMap Hardy2,
        shiftL2 f ∈ Submodule.map (innerMul he).toLinearMap Hardy2 := by
  refine ⟨?_, ?_, ?_⟩
  · refine map_innerMul_le he (isClosed_HardyFrom 0) ?_
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
    exact HardyFrom_antitone (by positivity) (mulL2_fourier_mem_HardyFrom he.mem k)
  · have hcompl : IsComplete ((innerMul he) '' (Hardy2 : Set L2C)) :=
      (LinearIsometry.isComplete_image_iff (innerMul he)).mpr
        (isClosed_HardyFrom 0).isComplete
    have hcoe : ((Submodule.map (innerMul he).toLinearMap Hardy2 : Submodule ℂ L2C) : Set L2C)
        = (innerMul he) '' (Hardy2 : Set L2C) := rfl
    rw [hcoe]
    exact hcompl.isClosed
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨shiftL2 g, shiftL2_mem_Hardy2 hg, ?_⟩
    simpa [innerMul] using (shiftL2_mulL2_comm he.unimodular g).symm

/-- Membership in `θ · H²`, written out pointwise. -/
lemma mem_map_innerMul_iff {e : L2C} (he : IsInner e) (f : L2C) :
    f ∈ Submodule.map (innerMul he).toLinearMap Hardy2 ↔
      ∃ g : L2C, g ∈ Hardy2 ∧
        (f : Circ → ℂ) =ᵐ[mu] fun x => (e : Circ → ℂ) x * (g : Circ → ℂ) x := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, mulL2_coeFn he.unimodular g⟩
  · rintro ⟨g, hg, hfg⟩
    refine ⟨g, hg, ?_⟩
    apply Lp.ext
    filter_upwards [mulL2_coeFn he.unimodular g, hfg] with x h1 h2
    change (mulL2 he.unimodular g : Circ → ℂ) x = (f : Circ → ℂ) x
    rw [h1, h2]

/-- **Beurling's theorem, pointwise form**.  A closed shift-invariant subspace `M` of `H²` is
either `{0}` or consists exactly of the functions `θ · g` with `g ∈ H²`, for a fixed inner
function `θ`. -/
theorem beurling_shift_invariant_subspace_pointwise (M : Submodule ℂ L2C) (hMH : M ≤ Hardy2)
    (hMclosed : IsClosed (M : Set L2C)) (hMinv : ∀ f ∈ M, shiftL2 f ∈ M) :
    (M : Set L2C) = {0} ∨ ∃ e : L2C, IsInner e ∧ (M : Set L2C) =
      {f : L2C | ∃ g : L2C, g ∈ Hardy2 ∧
        (f : Circ → ℂ) =ᵐ[mu] fun x => (e : Circ → ℂ) x * (g : Circ → ℂ) x} := by
  rcases beurling_shift_invariant_subspace M hMH hMclosed hMinv with h | ⟨e, he, hMe⟩
  · exact Or.inl (by rw [h]; rfl)
  · refine Or.inr ⟨e, he, ?_⟩
    ext f
    rw [SetLike.mem_coe, hMe, mem_map_innerMul_iff he f]
    rfl

/-! ### Transporting the theorem along an isometric isomorphism

Beurling's theorem is proved above for the concrete model `H² ⊆ L²(𝕋)`.  The following version
shows how to use it in any Hilbert space equipped with an isometric isomorphism onto `L²(𝕋)`
carrying the given operator to the shift — for instance a Hardy space of a half-plane, once the
corresponding isometry has been constructed. -/

/-- **Beurling's theorem, transported**.  If `U` is an isometric isomorphism of a Hilbert space
`H` onto `L²(𝕋)` taking a subspace `Hard` onto `H²` and an isometry `T` to the shift, then every
closed `T`-invariant subspace of `Hard` is either trivial or the `U`-preimage of `θ · H²` for an
inner function `θ`. -/
theorem beurling_of_isometryEquiv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] L2C) (Hard : Submodule ℂ H)
    (hHard : Submodule.map U.toLinearIsometry.toLinearMap Hard = Hardy2)
    (T : H →ₗᵢ[ℂ] H) (hT : ∀ f, U (T f) = shiftL2 (U f))
    (M : Submodule ℂ H) (hM : M ≤ Hard) (hMclosed : IsClosed (M : Set H))
    (hMinv : ∀ f ∈ M, T f ∈ M) :
    M = ⊥ ∨ ∃ (e : L2C) (he : IsInner e),
      M = Submodule.comap U.toLinearIsometry.toLinearMap
        (Submodule.map (innerMul he).toLinearMap Hardy2) := by
  set M' := Submodule.map U.toLinearIsometry.toLinearMap M with hM'
  have hinj : Function.Injective (U.toLinearIsometry.toLinearMap) := U.injective
  have hMeq : M = Submodule.comap U.toLinearIsometry.toLinearMap M' :=
    (Submodule.comap_map_eq_of_injective hinj M).symm
  have hM'H : M' ≤ Hardy2 := by
    rw [← hHard]
    exact Submodule.map_mono hM
  have hM'closed : IsClosed ((M' : Submodule ℂ L2C) : Set L2C) := by
    have hcoe : ((M' : Submodule ℂ L2C) : Set L2C) = U '' (M : Set H) := rfl
    rw [hcoe]
    exact U.toHomeomorph.isClosedMap _ hMclosed
  have hM'inv : ∀ f ∈ M', shiftL2 f ∈ M' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨T f, hMinv f hf, hT f⟩
  rcases beurling_shift_invariant_subspace M' hM'H hM'closed hM'inv with h | ⟨e, he, hMe⟩
  · left
    rw [Submodule.eq_bot_iff]
    intro f hf
    have h1 : U f ∈ M' := ⟨f, hf, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    simpa using congrArg U.symm h1
  · exact Or.inr ⟨e, he, by rw [← hMe, hMeq]⟩

/-! ### Non-vacuity checks

The hypotheses of Beurling's theorem are satisfiable: the Hardy space itself is a nonzero closed
shift-invariant subspace, and the constant function `1` is an inner function. -/

lemma fourierLp_mem_Hardy2 {n : ℤ} (hn : 0 ≤ n) : (fourierLp 2 n : L2C) ∈ Hardy2 := by
  rw [mem_HardyFrom]
  intro m hm
  have hmn : m ≠ n := by omega
  rw [fourierCoeff_congr_ae (coeFn_fourierLp 2 n), fourierCoeff_fourier]
  simp [hmn]

lemma isInner_fourierLp_zero : IsInner (fourierLp 2 (0 : ℤ)) := by
  refine ⟨fourierLp_mem_Hardy2 le_rfl, ?_⟩
  filter_upwards [coeFn_fourierLp (T := (1 : ℝ)) 2 0] with x hx
  rw [hx]
  exact norm_fourier_apply 0 x

lemma Hardy2_ne_bot : Hardy2 ≠ ⊥ := by
  intro h
  have hmem : (fourierLp 2 (0 : ℤ) : L2C) ∈ Hardy2 := fourierLp_mem_Hardy2 le_rfl
  rw [h, Submodule.mem_bot] at hmem
  have hnorm : ‖(fourierLp 2 (0 : ℤ) : L2C)‖ = 1 := by
    simpa using (orthonormal_fourier (T := (1 : ℝ))).1 (0 : ℤ)
  rw [hmem] at hnorm
  simp at hnorm

/-- The Hardy space itself satisfies all the hypotheses of Beurling's theorem and is nonzero. -/
theorem hardy2_satisfies_hypotheses :
    Hardy2 ≤ Hardy2 ∧ IsClosed ((Hardy2 : Submodule ℂ L2C) : Set L2C) ∧
      (∀ f ∈ Hardy2, shiftL2 f ∈ Hardy2) ∧ Hardy2 ≠ ⊥ :=
  ⟨le_rfl, isClosed_HardyFrom 0, fun _ hf => shiftL2_mem_Hardy2 hf, Hardy2_ne_bot⟩

end Beurling
