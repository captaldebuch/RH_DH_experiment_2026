/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB13BilinearReduction

/-!
# NB14: Bettin--Ehm rational series bridge and exact `q ≥ 2` collapse

This file formalizes the algebraic collapse of the auxiliary modular variable
`q ≥ 2` into the signed bilinear `(d, m)` dispersion kernel `S₁(d/m) - R₁(d/m)`.

The Bettin--Ehm rational series bridge `EhmR1RationalSeriesBridge` states that
the partial series:
  `∑_{1 ≤ q ≤ K} R₁(q · (d/m))`
converges as `K → ∞` to the period function `S₁(d/m)`.

Under this bridge, the `q ≥ 2` modular row collapses algebraically:
  `∑_{2 ≤ q ≤ J/d} R₁(d q / m) = ∑_{1 ≤ q ≤ J/d} R₁(q · d/m) - R₁(d/m)`
which tends to `S₁(d/m) - R₁(d/m)` without any loss of alternating sign information.
-/

open Filter
open scoped BigOperators Topology

namespace NBMellinTools.NB14

open NBMellinTools.NB8
open NBMellinTools.NB13

/-- The partial series of the rational `R₁` kernel up to index `K`. -/
noncomputable def ehmR1PartialSeries (R1 : ℝ → ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 K, R1 ((q : ℝ) * x)

/-- The Bettin--Ehm rational series bridge: `R₁` partial series along rational
arguments `d/m` converge to the Bettin--Conrey period function `S₁(d/m)`. -/
structure EhmR1RationalSeriesBridge (S1 R1 : ℝ → ℝ) : Prop where
  tendsto_ratio : ∀ (d m : ℕ), 0 < d → 0 < m →
    Tendsto (fun K : ℕ => ehmR1PartialSeries R1 K ((d : ℝ) / (m : ℝ)))
      atTop (𝓝 (S1 ((d : ℝ) / (m : ℝ))))

/-- Exact algebraic split of a sum over `1 ≤ q ≤ J` into the `q = 1` term
and the `2 ≤ q ≤ J` sum. -/
theorem sum_Icc_one_eq_first_add_sum_Icc_two
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) (J : ℕ) (hJ : 1 ≤ J) :
    (∑ q ∈ Finset.Icc 1 J, f q) = f 1 + ∑ q ∈ Finset.Icc 2 J, f q := by
  have hset : Finset.Icc 1 J = {1} ∪ Finset.Icc 2 J := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdis : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 J) := by
    simp
  rw [hset, Finset.sum_union hdis]
  simp

/-- Exact finite collapse of one `q ≥ 2` row into partial series minus first term. -/
theorem ehmR1QGeTwoRow_eq_partialSeries_sub_first
    (R1 : ℝ → ℝ) (d m J : ℕ) (hd : 0 < d) (hdJ : d ≤ J) :
    (∑ q ∈ Finset.Icc 2 (J / d), R1 (((d * q : ℕ) : ℝ) / (m : ℝ))) =
      ehmR1PartialSeries R1 (J / d) ((d : ℝ) / (m : ℝ)) -
        R1 ((d : ℝ) / (m : ℝ)) := by
  have hdiv : 1 ≤ J / d := (Nat.le_div_iff_mul_le hd).2 (by simpa using hdJ)
  unfold ehmR1PartialSeries
  rw [sum_Icc_one_eq_first_add_sum_Icc_two
    (fun q ↦ R1 ((q : ℝ) * ((d : ℝ) / (m : ℝ)))) (J / d) hdiv]
  have hsum :
      (∑ q ∈ Finset.Icc 2 (J / d), R1 (((d * q : ℕ) : ℝ) / (m : ℝ))) =
      ∑ q ∈ Finset.Icc 2 (J / d), R1 ((q : ℝ) * ((d : ℝ) / (m : ℝ))) := by
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    push_cast
    ring
  rw [hsum]
  simp only [Nat.cast_one, one_mul]
  ring

/-- The pointwise convergence of the `q ≥ 2` row to the `S₁ - R₁` kernel. -/
theorem ehmR1QGeTwoRow_tendsto_kernel
    {S1 R1 : ℝ → ℝ} (H : EhmR1RationalSeriesBridge S1 R1)
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun J : ℕ =>
      ehmR1PartialSeries R1 (J / d) ((d : ℝ) / (m : ℝ)) - R1 ((d : ℝ) / (m : ℝ)))
      atTop (𝓝 (S1 ((d : ℝ) / (m : ℝ)) - R1 ((d : ℝ) / (m : ℝ)))) := by
  have hpartial := H.tendsto_ratio d m hd hm
  have hdiv := Nat.tendsto_div_const_atTop (Nat.ne_of_gt hd)
  exact Tendsto.sub_const (hpartial.comp hdiv) (R1 ((d : ℝ) / (m : ℝ)))

end NBMellinTools.NB14
