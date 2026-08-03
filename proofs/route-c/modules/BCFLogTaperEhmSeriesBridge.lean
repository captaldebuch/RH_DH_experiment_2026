import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperEhmHyperbola

/-!
# Autocorrelation--`R₁` series bridge for the Ehm log taper

This module isolates the analytic identity

`S₁(x) = ∑_{k ≥ 1} R₁(kx)`

as a reusable `HasSum` interface and proves everything that follows from it
for the finite hyperbolic truncations.  In particular, the hyperbolic cutoff
converges to Ehm's finite inversion error.  No uniformity in the BCF cutoff
`N` is asserted here; that is the remaining H15-strength problem.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge

open scoped BigOperators Topology
open Filter
open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperEhm
open RH.Criteria.NymanBeurling.BCFLogTaperEhmKernel
open RH.Criteria.NymanBeurling.BCFLogTaperEhmHyperbola

/-- The ordinary partial sum of the positive-index `R₁` series. -/
noncomputable def ehmR1PartialSeries
    (R1 : ℝ → ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K, R1 ((k : ℝ) * x)

/-- The exact analytic bridge between an autocorrelation kernel `S1` and an
`R1` series.  `HasSum` records both the value and convergence of the series;
it does not assert any cutoff-uniform rate. -/
structure EhmR1SeriesBridge (S1 R1 : ℝ → ℝ) where
  hasSum_series : ∀ x : ℝ, 0 < x →
    HasSum (fun q : ℕ => R1 (((q + 1 : ℕ) : ℝ) * x)) (S1 x)

/-- The concrete open bridge for Ehm's autocorrelation and elementary
`R₁` function. -/
abbrev EhmAutocorrelationR1SeriesBridge :=
  EhmR1SeriesBridge ehmS1Autocorrelation ehmR1

/-- A quadratic reciprocal-decay estimate for `R1`.  This is a standard
analytic input strong enough to make every positive-scale `R1` series
absolutely summable; it says nothing yet about the value of that series. -/
structure EhmR1QuadraticDecay (R1 : ℝ → ℝ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound : ∀ y : ℝ, 0 < y → |R1 y| ≤ C / y ^ 2

/-- Quadratic reciprocal decay gives absolute summability of the shifted
positive-index `R1` series at every positive scale. -/
theorem EhmR1QuadraticDecay.summable_series
    {R1 : ℝ → ℝ} (H : EhmR1QuadraticDecay R1)
    (x : ℝ) (hx : 0 < x) :
    Summable (fun q : ℕ => R1 (((q + 1 : ℕ) : ℝ) * x)) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hpShift : Summable (fun q : ℕ => 1 / (((q + 1 : ℕ) : ℝ) ^ (2 : ℕ))) := by
    exact hp.comp_injective (fun a b hab => by omega)
  have hmajorant : Summable (fun q : ℕ =>
      (H.C / x ^ 2) * (1 / (((q + 1 : ℕ) : ℝ) ^ (2 : ℕ)))) :=
    hpShift.mul_left (H.C / x ^ 2)
  apply hmajorant.of_norm_bounded
  intro q
  rw [Real.norm_eq_abs]
  calc
    |R1 (((q + 1 : ℕ) : ℝ) * x)| ≤
        H.C / ((((q + 1 : ℕ) : ℝ) * x) ^ 2) :=
      H.bound _ (mul_pos (by positivity) hx)
    _ = (H.C / x ^ 2) *
        (1 / (((q + 1 : ℕ) : ℝ) ^ (2 : ℕ))) := by
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hq0 : (((q + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [hx0, hq0]

/-- Identification of the absolutely convergent `R1` series with an
autocorrelation kernel.  Separating this from decay makes the two analytic
obligations explicit. -/
structure EhmR1SeriesValueIdentity (S1 R1 : ℝ → ℝ) where
  value : ∀ x : ℝ, 0 < x →
    S1 x = ∑' q : ℕ, R1 (((q + 1 : ℕ) : ℝ) * x)

/-- Reciprocal decay plus the value identity constructs the full `HasSum`
bridge used by the hyperbolic limit theorems. -/
noncomputable def EhmR1SeriesBridge.of_decay_and_value
    {S1 R1 : ℝ → ℝ}
    (HD : EhmR1QuadraticDecay R1)
    (HV : EhmR1SeriesValueIdentity S1 R1) :
    EhmR1SeriesBridge S1 R1 where
  hasSum_series x hx := by
    rw [HV.value x hx]
    exact (HD.summable_series x hx).hasSum

/-- Concrete reciprocal-decay obligation for Ehm's elementary `R₁`. -/
abbrev EhmConcreteR1QuadraticDecay := EhmR1QuadraticDecay ehmR1

/-- Concrete value-identification obligation for Ehm's autocorrelation. -/
abbrev EhmAutocorrelationR1SeriesValueIdentity :=
  EhmR1SeriesValueIdentity ehmS1Autocorrelation ehmR1

private theorem sum_Icc_one_eq_sum_range_shift
    (f : ℕ → ℝ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, f k) =
      ∑ q ∈ Finset.range K, f (q + 1) := by
  apply Finset.sum_bij (fun k _ => k - 1)
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    simp only [Finset.mem_range]
    omega
  · intro a ha b hb hab
    have ha1 := (Finset.mem_Icc.mp ha).1
    have hb1 := (Finset.mem_Icc.mp hb).1
    omega
  · intro q hq
    simp only [Finset.mem_range] at hq
    refine ⟨q + 1, Finset.mem_Icc.mpr ?_, ?_⟩
    · omega
    · simp
  · intro k hk
    have hk1 := (Finset.mem_Icc.mp hk).1
    rw [Nat.sub_add_cancel hk1]

/-- A series bridge gives convergence of the usual positive-index partial
sums to `S1(x)`. -/
theorem ehmR1PartialSeries_tendsto
    {S1 R1 : ℝ → ℝ} (H : EhmR1SeriesBridge S1 R1)
    (x : ℝ) (hx : 0 < x) :
    Tendsto (fun K : ℕ => ehmR1PartialSeries R1 K x)
      atTop (𝓝 (S1 x)) := by
  have hseries := (H.hasSum_series x hx).tendsto_sum_nat
  apply Tendsto.congr _ hseries
  intro K
  exact (sum_Icc_one_eq_sum_range_shift
    (fun k : ℕ => R1 ((k : ℝ) * x)) K).symm

/-- A hyperbolic row is exactly an ordinary partial `R₁` series with cutoff
`J / d` and scale `d*x`. -/
theorem ehmFiniteHyperbolicRow_eq_partialSeries
    (R1 : ℝ → ℝ) (c x : ℝ) (d J : ℕ) (hd : 0 < d) :
    (∑ k ∈ Finset.Icc 1 J,
      if d * k ≤ J then
        c * R1 (((d * k : ℕ) : ℝ) * x)
      else 0) =
      c * ehmR1PartialSeries R1 (J / d) ((d : ℝ) * x) := by
  classical
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Icc 1 J).filter (fun k => d * k ≤ J) =
        Finset.Icc 1 (J / d) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, _⟩, hdkJ⟩
      exact ⟨hk1, (Nat.le_div_iff_mul_le hd).mpr (by simpa [mul_comm] using hdkJ)⟩
    · rintro ⟨hk1, hkdiv⟩
      have hkdJ : k * d ≤ J := (Nat.le_div_iff_mul_le hd).mp hkdiv
      have hkJ : k ≤ J := hkdiv.trans (Nat.div_le_self J d)
      exact ⟨⟨hk1, hkJ⟩, by simpa [mul_comm] using hkdJ⟩
  rw [hfilter]
  unfold ehmR1PartialSeries
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  push_cast
  ring

/-- For fixed `N` and positive `x`, the finite hyperbolic truncation tends
to the finite `S₁` transform.  This is pointwise in `N`; it contains no
uniform boundary estimate. -/
theorem ehmFiniteS1HyperbolicSum_tendsto
    {S1 R1 : ℝ → ℝ} (H : EhmR1SeriesBridge S1 R1)
    (N : ℕ) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun J : ℕ => ehmFiniteS1HyperbolicSum R1 N J x)
      atTop
      (𝓝 (∑ d ∈ Finset.Icc 1 N,
        dirichletCoeff N d * S1 ((d : ℝ) * x))) := by
  classical
  unfold ehmFiniteS1HyperbolicSum
  apply tendsto_finsetSum
  intro d hdmem
  have hd : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdmem).1
  have hdx : 0 < (d : ℝ) * x := mul_pos (by exact_mod_cast hd) hx
  have hpartial := ehmR1PartialSeries_tendsto H ((d : ℝ) * x) hdx
  have hdiv := Nat.tendsto_div_const_atTop (Nat.ne_of_gt hd)
  have hlimit := (hpartial.comp hdiv).const_mul (dirichletCoeff N d)
  apply Tendsto.congr _ hlimit
  intro J
  exact (ehmFiniteHyperbolicRow_eq_partialSeries R1
    (dirichletCoeff N d) x d J hd).symm

/-- After the autocorrelation--series bridge, the finite outer hyperbolic
defect converges exactly to Ehm's inversion error. -/
theorem ehmFiniteHyperbolicInversionError_tendsto
    {S1 R1 : ℝ → ℝ} (H : EhmR1SeriesBridge S1 R1)
    (N : ℕ) :
    Tendsto (fun J : ℕ => ehmFiniteHyperbolicInversionError R1 N J)
      atTop (𝓝 (ehmInversionError S1 R1 N)) := by
  classical
  unfold ehmFiniteHyperbolicInversionError ehmInversionError
  apply tendsto_finsetSum
  intro m hmmem
  have hm : 0 < m :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hmmem).1
  have hmx : (0 : ℝ) < 1 / (m : ℝ) := by
    exact one_div_pos.mpr (by exact_mod_cast hm)
  have hinner := ehmFiniteS1HyperbolicSum_tendsto
    H N (1 / (m : ℝ)) hmx
  have hlimit := (hinner.sub_const (R1 (1 / (m : ℝ)))).const_mul
    (dirichletCoeff N m / (m : ℝ))
  simpa [div_eq_mul_inv, mul_assoc] using hlimit

end RH.Criteria.NymanBeurling.BCFLogTaperEhmSeriesBridge
