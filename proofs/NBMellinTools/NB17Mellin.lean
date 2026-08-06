import Mathlib

/-!
# Mellin-transform toolbox for the Nyman–Beurling / Báez-Duarte circle of ideas

This file collects the elementary Mellin-transform lemmas that are used in the
Nyman–Beurling files:

* `NB17Mellin.hasMellin_congr` : the Mellin transform only sees the values of a function
  on `Ioi 0`;
* `NB17Mellin.hasMellin_finset_sum` : additivity of the Mellin transform over a finite sum;
* `NB17Mellin.hasMellin_indicator_Ioc01` : `M[χ_{(0,1]}](s) = 1/s` for `Re s > 0`;
* `NB17Mellin.fractInv` and `NB17Mellin.hasMellin_fractInv_mul` : the behaviour of the
  Báez-Duarte generator `x ↦ {1/(a x)}` under dilation;
* `NB17Mellin.MellinPlancherelIdentity` : the Mellin–Plancherel identity, stated as a `Prop`
  so that it can be carried around as an explicit hypothesis.
-/

open MeasureTheory Set Filter Complex Real Topology

noncomputable section

namespace NB17Mellin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ## Congruence and finite sums -/

/-- `MellinConvergent` only depends on the values of the function on `Ioi 0`. -/
theorem mellinConvergent_congr {f g : ℝ → E} {s : ℂ} (h : ∀ x ∈ Ioi (0:ℝ), f x = g x) :
    MellinConvergent f s ↔ MellinConvergent g s := by
  refine integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [h x hx]

/-- The Mellin transform only depends on the values of the function on `Ioi 0`. -/
theorem mellin_congr {f g : ℝ → E} {s : ℂ} (h : ∀ x ∈ Ioi (0:ℝ), f x = g x) :
    mellin f s = mellin g s := by
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [h x hx]

/-- `HasMellin` only depends on the values of the function on `Ioi 0`. -/
theorem hasMellin_congr {f g : ℝ → E} {s : ℂ} {m : E} (h : ∀ x ∈ Ioi (0:ℝ), f x = g x) :
    HasMellin f s m ↔ HasMellin g s m := by
  unfold HasMellin
  rw [mellinConvergent_congr h, mellin_congr h]

/-- The Mellin transform of a finite sum is the sum of the Mellin transforms. -/
theorem hasMellin_finset_sum {ι : Type*} (t : Finset ι) (f : ι → ℝ → E) (s : ℂ)
    (hconv : ∀ i ∈ t, MellinConvergent (f i) s) :
    HasMellin (fun x => ∑ i ∈ t, f i x) s (∑ i ∈ t, mellin (f i) s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [HasMellin, MellinConvergent, mellin]
  | insert a t ha ih =>
      have hconv' : ∀ i ∈ t, MellinConvergent (f i) s := fun i hi =>
        hconv i (Finset.mem_insert_of_mem hi)
      have hA : MellinConvergent (f a) s := hconv a (Finset.mem_insert_self a t)
      have hB : MellinConvergent (fun x => ∑ i ∈ t, f i x) s := (ih hconv').1
      have hadd := hasMellin_add hA hB
      have hsum : (fun x => ∑ i ∈ insert a t, f i x) = fun x => f a x + ∑ i ∈ t, f i x := by
        funext x; rw [Finset.sum_insert ha]
      rw [(ih hconv').2] at hadd
      rw [hsum, Finset.sum_insert ha]
      exact hadd

/-! ## The indicator of `(0,1]` -/

/-- The Mellin transform of `χ_{(0,1]}` is `1/s` on the half-plane `Re s > 0`. -/
theorem hasMellin_indicator_Ioc01 {s : ℂ} (hs : 0 < s.re) :
    HasMellin (Set.indicator (Ioc (0:ℝ) 1) (fun _ => (1 : ℂ))) s (1 / s) :=
  hasMellin_one_Ioc hs

/-! ## The Báez-Duarte generator -/

/-- `fractInv x = {1/x}`, the fractional part of the reciprocal. -/
def fractInv (x : ℝ) : ℂ := ((Int.fract x⁻¹ : ℝ) : ℂ)

/-- The Mellin-transform formula for `x ↦ {1/x}`, stated as a `Prop`:
`∫_0^∞ {1/x} x^{s-1} dx = -ζ(s)/s` on the critical strip `0 < Re s < 1`.
It is proved in `NBMellinTools.NB17ZetaFract`. -/
def ZetaFractMellinFormula : Prop :=
  ∀ {s : ℂ}, 0 < s.re → s.re < 1 → HasMellin fractInv s (-riemannZeta s / s)

/-- Dilation: the Mellin transform of `x ↦ {1/(a x)}` is `a^{-s}` times that of `x ↦ {1/x}`. -/
theorem hasMellin_fractInv_mul (h : ZetaFractMellinFormula) {a : ℝ} (ha : 0 < a) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    HasMellin (fun x => fractInv (a * x)) s ((a : ℂ) ^ (-s) * (-riemannZeta s / s)) := by
  obtain ⟨hconv, hval⟩ := h h0 h1
  refine ⟨(MellinConvergent.comp_mul_left ha).2 hconv, ?_⟩
  rw [mellin_comp_mul_left fractInv s ha, hval, smul_eq_mul]

/-! ## The Mellin–Plancherel identity -/

/-- **The Mellin–Plancherel identity** (classical).  For a function `f` supported in `(0,∞)`
which is square-integrable there, and whose Mellin transform converges on the critical line,

`∫_0^∞ |f(x)|² dx = (1/2π) ∫_ℝ |M f(1/2 + i t)|² dt.`

It is stated as a `Prop` so that theorems depending on it carry it as an explicit hypothesis. -/
def MellinPlancherelIdentity : Prop :=
  ∀ f : ℝ → ℂ, (∀ x ≤ (0:ℝ), f x = 0) →
    AEStronglyMeasurable f (volume.restrict (Ioi (0:ℝ))) →
    IntegrableOn (fun x => ‖f x‖ ^ 2) (Ioi (0:ℝ)) →
    (∀ t : ℝ, MellinConvergent f ((1:ℂ)/2 + I * t)) →
    (∫ x in Ioi (0:ℝ), ‖f x‖ ^ 2) =
      (1 / (2 * π)) * ∫ t : ℝ, ‖mellin f ((1:ℂ)/2 + I * t)‖ ^ 2

end NB17Mellin
