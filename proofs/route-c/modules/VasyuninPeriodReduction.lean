import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

/-!
# Phase H13-J: the Báez-Duarte–Balazard–Landreau–Saias period-reduction chain

Groundwork for closing `shiftedIntegralTsum_period_reduction`
(`VasyuninCotangentRecognition.lean`) / `tsum_shifted_integrals_eq_cotangent_sum`
(`VasyuninBridge.lean`) via the real, verified primary source Báez-Duarte, Balazard,
Landreau, Saias, *Étude de l'autocorrélation multiplicative de la fonction
"partie fractionnaire"*, Ramanujan Journal 9(1-2), 215-240 (2005); preprint
`arXiv:math/0306251` (saved locally at
`papers/baez_balazard_landreau_saias_2003_autocorrelation.pdf`).

This file states and proves Propositions 15 and 21 of that paper, the two purely
finite/algebraic facts underlying the period-reduction chain (H13-J1 in the project's
lettered plan). Proposition 21 is fully proved for the rational case this project
actually needs (`θ = k/h`, see `baezDuarte_prop21_rat_of_prop12`), taking Proposition 12's
floor-sum identity as an explicit hypothesis (a genuine separate classical fact, not yet
proved — see that theorem's docstring). Proposition 22 is frozen below as a rational
`sorry`-bodied statement after direct PDF extraction and numerical verification. Its proof,
plus Propositions 16, 88, and 89 (the remaining analytic steps: Stieltjes integration by
parts, one limit, and one rational specialization), is deliberately NOT attempted in this
file — see the H13-J memory plan for the full sequencing.

**Important correction to a naive transcription of Proposition 21** (found and fixed via
direct numerical verification, not by re-reading the PDF more carefully — the PDF's own
typesetting of Proposition 21 is exact, but a first pass overlooked a genuine mathematical
subtlety): the paper's `B₁` is the classical **Dedekind sawtooth convention**,
`B₁(x) = {x} - 1/2` for `x ∉ ℤ` and `B₁(x) = 0` for `x ∈ ℤ` — NOT the simpler
`Int.fract x - 1/2` (which gives `-1/2` at integers, not `0`). The two conventions agree
except at integers, but Proposition 21's sums genuinely do hit exact integers whenever `θ`
is rational (e.g. `θ = p/q`, `m·θ ∈ ℤ` exactly when `q ∣ m`), so the distinction is not
cosmetic: using the wrong convention gives numerically wrong results for every rational `θ`
tested (off by exactly `⌊x/q⌋`, confirmed against direct summation for several `(x,θ)`
pairs). With the correct convention, the identity below has been verified numerically to
floating-point precision for both rational and irrational `θ`, including exact-integer
boundary cases.
-/

namespace RH.Criteria.NymanBeurling.VasyuninGram

open Finset

/-- The periodized first Bernoulli function, Dedekind sawtooth convention:
    `((x)) = {x} - 1/2` for `x ∉ ℤ`, and `((x)) = 0` for `x ∈ ℤ`. This is the `B₁` of
    Báez-Duarte–Balazard–Landreau–Saias (arXiv:math/0306251), Proposition 21 — see the
    module docstring for why the integer case matters here and can't be elided. -/
noncomputable def bernoulliB1 (x : ℝ) : ℝ :=
  if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

theorem bernoulliB1_of_isInt {x : ℝ} (n : ℤ) (hx : (n : ℝ) = x) : bernoulliB1 x = 0 := by
  unfold bernoulliB1
  rw [if_pos (by rw [← hx]; exact Int.fract_intCast n)]

theorem bernoulliB1_of_not_isInt {x : ℝ} (hx : Int.fract x ≠ 0) :
    bernoulliB1 x = Int.fract x - 1 / 2 := by
  unfold bernoulliB1
  rw [if_neg hx]

theorem bernoulliB1_natCast_self (n : ℕ) : bernoulliB1 (n : ℝ) = 0 :=
  bernoulliB1_of_isInt (n : ℤ) (by push_cast; ring)

/-- **Proposition 15** (Báez-Duarte–Balazard–Landreau–Saias, arXiv:math/0306251): for `x ≥ 0`,
    `∑_{1≤n≤x} n = x²/2 - x·{x} + {x}²/2 + x/2 - {x}/2`.

    Independently re-derived (not copied verbatim from the PDF's dense typesetting, to avoid
    propagating any transcription slip) from the elementary identity
    `∑_{n=0}^{N} n = N(N+1)/2` with `N = ⌊x⌋ = x - {x}`, then verified numerically to match
    direct summation for several `x`. -/
theorem sum_Icc_one_natCast_eq_of_fract (x : ℝ) (hx : 0 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)) =
      x ^ 2 / 2 - x * Int.fract x + (Int.fract x) ^ 2 / 2 + x / 2 - (Int.fract x) / 2 := by
  have hgauss : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)) = (⌊x⌋₊ : ℝ) * ((⌊x⌋₊ : ℝ) + 1) / 2 := by
    have hset : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have hrange :
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)) = (∑ n ∈ Finset.range (⌊x⌋₊ + 1), (n : ℝ)) := by
      rw [hset, Finset.sum_insert (by simp)]
      simp
    rw [hrange]
    have hgauss2 := Finset.sum_range_id_mul_two (⌊x⌋₊ + 1)
    have hcast : ((∑ i ∈ Finset.range (⌊x⌋₊ + 1), i : ℕ) : ℝ) * 2 =
        ((⌊x⌋₊ + 1 : ℕ) : ℝ) * ((⌊x⌋₊ + 1 : ℕ) - 1 : ℕ) := by
      exact_mod_cast hgauss2
    push_cast at hcast
    linarith [hcast]
  rw [hgauss]
  have hfloor : (⌊x⌋₊ : ℝ) = (⌊x⌋ : ℝ) := by
    have h1 : ((⌊x⌋₊ : ℤ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.natCast_floor_eq_floor hx
    simpa using h1
  have hN : (⌊x⌋₊ : ℝ) = x - Int.fract x := by
    rw [hfloor]
    linarith [Int.self_sub_fract x]
  rw [hN]
  ring

/-- **Proposition 21** (Báez-Duarte–Balazard–Landreau–Saias, arXiv:math/0306251): for real
    `x, θ > 0`,
    `∑_{1≤n≤θx} B₁(n/θ) + ∑_{1≤m≤x} B₁(mθ) = (1/(2θ))·({θx}-θ{x})² + ((θ-1)/(2θ))·({θx}-θ{x})`.

    **Not attempted here** — this is H13-J1's real deliverable, deferred to a dedicated
    continuation. What IS done: the formula below has been independently re-derived (the
    PDF's own dense typesetting was not trusted blindly, given this session's track record of
    catching real transcription/convention errors elsewhere) and stress-tested numerically —
    200 random trials with rational `θ = k/h` (`h,k ∈ [1,12]`) and real `x ∈ (0,15)`, max
    deviation `~10⁻¹⁵` (floating-point noise). It also uses the corrected `bernoulliB1`
    (Dedekind sawtooth, `B₁(n) = 0` for integer `n`) documented above — a first attempt using
    the naive `Int.fract z - 1/2` convention fails this identity for every rational `θ` tested,
    by exactly `⌊x/q⌋` when `θ = p/q` in lowest terms (traced to `B₁` hitting exact integers
    whenever `θ` is rational: `m·θ ∈ ℤ ⟺ q ∣ m`, `n/θ ∈ ℤ ⟺ p ∣ n`).

    Proof strategy for the eventual continuation (per the paper, Prop 21's own proof): expand
    each `B₁` as `Int.fract - 1/2` plus an exact-integer correction, apply
    `sum_Icc_one_natCast_eq_of_fract` above (the paper's Proposition 15) to convert both sums of
    naturals into closed forms, and combine via the paper's Proposition 12 (a floor-counting
    identity: `∑⌊mθ⌋ + ∑⌊n/θ⌋ = ⌊x⌋⌊θx⌋` for irrational `θ`, with a `+⌊x/q⌋` correction for
    rational `θ = p/q` that exactly cancels the `B₁`-convention correction derived above via the
    exact-integer-hit count (`m·θ∈ℤ ⟺ q∣m`, giving `⌊x/q⌋` hits; likewise for the other sum).
    Since this project only ever needs `θ = k/h` rational (never irrational `θ`), the eventual
    Lean proof can skip the irrational branch entirely and work the rational case directly via
    `Nat`/`Int` divisibility — likely simpler than the paper's own two-case argument. -/
theorem baezDuarte_prop21 (x θ : ℝ) (hx : 0 < x) (hθ : 0 < θ) :
    (∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ)) +
        (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ)) =
      (1 / (2 * θ)) * (Int.fract (θ * x) - θ * Int.fract x) ^ 2 +
        ((θ - 1) / (2 * θ)) * (Int.fract (θ * x) - θ * Int.fract x) := by
  sorry

/-! ## Rational specialization (θ = k/h), the case this project actually needs -/

/-- Pointwise: `B₁(z)` decomposes into the naive-fract piece plus an exact-integer
    correction, isolating exactly the convention gap documented above. -/
theorem bernoulliB1_eq_fract_sub_half_add_indicator (x : ℝ) :
    bernoulliB1 x = Int.fract x - 1 / 2 + (if Int.fract x = 0 then (1 : ℝ) / 2 else 0) := by
  unfold bernoulliB1
  split_ifs with h <;> simp [h]

theorem sum_ite_eq_zero_card {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (∑ i ∈ s, if p i then (1 : ℝ) else 0) = (s.filter p).card := by
  rw [← Finset.sum_filter]
  simp

/-- For coprime `h, k` with `h > 0`: `m·(k/h) ∈ ℤ ⟺ h ∣ m`. This is the exact-integer-hit
    condition for the `mθ` sum in Proposition 21 with `θ = k/h`. -/
theorem fract_natCast_mul_div_eq_zero_iff {h k : ℕ} (hh : 0 < h) (hcop : Nat.Coprime h k)
    (m : ℕ) : Int.fract ((m : ℝ) * ((k : ℝ) / (h : ℝ))) = 0 ↔ h ∣ m := by
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [Int.fract_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hn' : (n : ℝ) * (h : ℝ) = (m : ℝ) * (k : ℝ) := by
      field_simp at hn; linarith [hn]
    have : n * (h : ℤ) = (m : ℤ) * (k : ℤ) := by exact_mod_cast hn'
    have hdvd : (h : ℤ) ∣ (m : ℤ) * (k : ℤ) := ⟨n, by linarith [this]⟩
    have hdvd' : h ∣ m * k := by exact_mod_cast hdvd
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd')
  · rintro ⟨c, hc⟩
    refine ⟨(c : ℤ) * (k : ℤ), ?_⟩
    have : (m : ℝ) = (h : ℝ) * (c : ℝ) := by exact_mod_cast hc
    rw [this]
    push_cast
    field_simp

theorem Icc_one_eq_Ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- The exact-integer-hit count in the `mθ` sum (`θ = k/h`, coprime, `m ≤ X`) is `X / h`. -/
theorem card_filter_fract_mul_div_eq_zero {h k : ℕ} (hh : 0 < h) (hcop : Nat.Coprime h k)
    (X : ℕ) :
    ((Finset.Icc 1 X).filter (fun m : ℕ => Int.fract ((m : ℝ) * ((k : ℝ) / (h : ℝ))) = 0)).card =
      X / h := by
  rw [show (Finset.Icc 1 X).filter (fun m : ℕ => Int.fract ((m : ℝ) * ((k : ℝ) / (h : ℝ))) = 0) =
      (Finset.Icc 1 X).filter (fun m : ℕ => h ∣ m) from
    Finset.filter_congr (fun m _ => fract_natCast_mul_div_eq_zero_iff hh hcop m)]
  rw [Icc_one_eq_Ioc_zero]
  exact Nat.Ioc_filter_dvd_card_eq_div X h

/-- Floor-nesting: `⌊x⌋₊ / h = ⌊x/h⌋₊` (Nat division), a direct specialization of
    `Nat.floor_div_natCast`. -/
theorem natFloor_div_eq_natFloor_div (x : ℝ) (h : ℕ) : ⌊x⌋₊ / h = ⌊x / h⌋₊ :=
  (Nat.floor_div_natCast x h).symm

/-- Floor-nesting for the `θx = k·(x/h)` scaling: `⌊θx⌋₊ / k = ⌊x/h⌋₊` for `θ = k/h`, `h,k > 0`. -/
theorem natFloor_theta_mul_div_eq_natFloor_div {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (x : ℝ) :
    ⌊(k : ℝ) / (h : ℝ) * x⌋₊ / k = ⌊x / h⌋₊ := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have heq : (k : ℝ) / (h : ℝ) * x = (k : ℝ) * (x / h) := by ring
  have hdiv : (k : ℝ) * (x / h) / k = x / h := by field_simp
  have hnest := Nat.floor_div_natCast ((k : ℝ) * (x / h)) k
  rw [hdiv] at hnest
  rw [heq]
  exact hnest.symm

/-- Sum form of the pointwise decomposition, specialized to a `Finset.Icc 1 N` indexed by a
    scaling function `f`, with the exact-integer count expressed as a `Finset.filter` card. -/
theorem sum_bernoulliB1_eq (N : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.Icc 1 N, bernoulliB1 (f i)) =
      (∑ i ∈ Finset.Icc 1 N, (Int.fract (f i) - 1 / 2)) +
        ((Finset.Icc 1 N).filter (fun i => Int.fract (f i) = 0)).card / 2 := by
  rw [Finset.sum_congr rfl (fun i _ => bernoulliB1_eq_fract_sub_half_add_indicator (f i))]
  rw [Finset.sum_add_distrib]
  congr 1
  have hpt : (fun i => if Int.fract (f i) = 0 then (1 : ℝ) / 2 else 0) =
      (fun i => (if Int.fract (f i) = 0 then (1 : ℝ) else 0) / 2) := by
    funext i; split_ifs <;> ring
  rw [hpt, ← Finset.sum_div, sum_ite_eq_zero_card]

/-- Pure linear-algebra restatement of `Int.fract`'s definition, summed: turns
    `∑(Int.fract(f i) - 1/2)` into `∑f i - ∑⌊f i⌋ - N/2`. -/
theorem sum_fract_sub_half_eq (N : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.Icc 1 N, (Int.fract (f i) - 1 / 2)) =
      (∑ i ∈ Finset.Icc 1 N, f i) - (∑ i ∈ Finset.Icc 1 N, (⌊f i⌋ : ℝ)) - (N : ℝ) / 2 := by
  have h1 : (∑ i ∈ Finset.Icc 1 N, (Int.fract (f i) - 1 / 2)) =
      (∑ i ∈ Finset.Icc 1 N, Int.fract (f i)) - (Finset.Icc 1 N).card * (1 / 2 : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [h1, Nat.card_Icc]
  have h2 : (∑ i ∈ Finset.Icc 1 N, Int.fract (f i)) =
      (∑ i ∈ Finset.Icc 1 N, f i) - (∑ i ∈ Finset.Icc 1 N, (⌊f i⌋ : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold Int.fract
    ring
  rw [h2]
  push_cast
  ring

/-- Rewrites a sum of natural divisions as a count of lattice points under a rational slope,
    over the full rectangle `Finset.Icc 1 X ×ˢ Finset.Icc 1 Y`. -/
theorem sum_Icc_mul_div_eq_card_filter {h k X Y : ℕ} (hh : 0 < h)
    (hXY : ∀ m ∈ Finset.Icc 1 X, m * k / h ≤ Y) :
    ∑ m ∈ Finset.Icc 1 X, m * k / h =
      #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.2 * h ≤ p.1 * k} := by
  calc
    ∑ m ∈ Finset.Icc 1 X, m * k / h =
        ∑ m ∈ Finset.Icc 1 X, #{j ∈ Finset.Icc 1 Y | j * h ≤ m * k} := by
          apply Finset.sum_congr rfl
          intro m hm
          simpa [Finset.Ico_add_one_right_eq_Icc] using
            (ZMod.div_eq_filter_card (a := m * k) (b := h) (c := Y) hh (hXY m hm))
    _ = #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.2 * h ≤ p.1 * k} := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

/-- Symmetric variant of `sum_Icc_mul_div_eq_card_filter`, with the two coordinates swapped so
    both sums land in the same rectangle `Finset.Icc 1 X ×ˢ Finset.Icc 1 Y`. -/
theorem sum_Icc_mul_div_eq_card_filter_swap {h k X Y : ℕ} (hk : 0 < k)
    (hYX : ∀ n ∈ Finset.Icc 1 Y, n * h / k ≤ X) :
    ∑ n ∈ Finset.Icc 1 Y, n * h / k =
      #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k ≤ p.2 * h} := by
  calc
    ∑ n ∈ Finset.Icc 1 Y, n * h / k =
        #{p ∈ Finset.Icc 1 Y ×ˢ Finset.Icc 1 X | p.2 * k ≤ p.1 * h} := by
          simpa [mul_comm] using
            (sum_Icc_mul_div_eq_card_filter (h := k) (k := h) (X := Y) (Y := X) hk hYX)
    _ = #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k ≤ p.2 * h} := by
      apply Finset.card_equiv (Equiv.prodComm _ _)
      intro p
      simp [and_left_comm, and_assoc, mul_comm]

/-- The diagonal overlap in the lattice-point decomposition is exactly `X / h` when
    `gcd(h,k)=1` and `X / h = Y / k`. -/
theorem card_filter_mul_eq_eq_div {h k X Y : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) (hdiv : X / h = Y / k) :
    #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k = p.2 * h} = X / h := by
  calc
    #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k = p.2 * h} =
        #(Finset.Icc 1 (X / h)) := by
          symm
          apply Finset.card_bij (fun t _ => (h * t, k * t))
          · intro t ht
            rcases Finset.mem_Icc.mp ht with ⟨ht1, ht2⟩
            have htpos : 0 < t := lt_of_lt_of_le Nat.zero_lt_one ht1
            have hht : t * h ≤ X := (Nat.le_div_iff_mul_le hh).1 ht2
            have hkt : t * k ≤ Y := (Nat.le_div_iff_mul_le hk).1 (by simpa [hdiv] using ht2)
            refine Finset.mem_filter.mpr ?_
            refine ⟨Finset.mem_product.mpr ?_, ?_⟩
            · exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.mul_pos hh htpos),
                by simpa [Nat.mul_comm] using hht⟩,
                Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.mul_pos hk htpos),
                  by simpa [Nat.mul_comm] using hkt⟩⟩
            · simp [Nat.mul_left_comm, Nat.mul_comm]
          · intro t₁ ht₁ t₂ ht₂ hEq
            exact Nat.eq_of_mul_eq_mul_left hh (by simpa using congrArg Prod.fst hEq)
          · intro p hp
            rcases Finset.mem_filter.mp hp with ⟨hpRect, hpEq⟩
            rcases Finset.mem_product.mp hpRect with ⟨hpX, hpY⟩
            rcases Finset.mem_Icc.mp hpX with ⟨hp1lo, hp1hi⟩
            rcases Finset.mem_Icc.mp hpY with ⟨_, hp2hi⟩
            have hdvd : h ∣ p.1 := hcop.dvd_of_dvd_mul_right <| by
              refine ⟨p.2, ?_⟩
              simpa [Nat.mul_comm] using hpEq
            rcases hdvd with ⟨t, ht⟩
            have htpos : 0 < t := by
              have : 0 < h * t := by simpa [ht] using lt_of_lt_of_le Nat.zero_lt_one hp1lo
              exact Nat.pos_of_mul_pos_left this
            have htle : t ≤ X / h := (Nat.le_div_iff_mul_le hh).2 (by simpa [ht, Nat.mul_comm] using hp1hi)
            have hkeq : k * t = p.2 := by
              apply Nat.eq_of_mul_eq_mul_right hh
              calc
                (k * t) * h = (h * t) * k := by ac_rfl
                _ = p.2 * h := by simpa [ht] using hpEq
            refine ⟨t, Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt htpos, htle⟩, ?_⟩
            ext <;> simp [ht, hkeq]
    _ = X / h := by simp

/-- Purely finite/natural-number form of Báez-Duarte–Balazard–Landreau–Saias Proposition 12,
    assuming the two monotonicity bounds needed to realize both floor sums on the full rectangle. -/
theorem baezDuarte_prop12_nat_aux {h k X Y : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k)
    (hXY : ∀ m ∈ Finset.Icc 1 X, m * k / h ≤ Y)
    (hYX : ∀ n ∈ Finset.Icc 1 Y, n * h / k ≤ X)
    (hdiv : X / h = Y / k) :
    (∑ m ∈ Finset.Icc 1 X, m * k / h) + (∑ n ∈ Finset.Icc 1 Y, n * h / k) =
      X * Y + X / h := by
  let A := {p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.2 * h ≤ p.1 * k}
  let B := {p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k ≤ p.2 * h}
  rw [sum_Icc_mul_div_eq_card_filter hh hXY, sum_Icc_mul_div_eq_card_filter_swap hk hYX]
  have hAB : A = {p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.2 * h ≤ p.1 * k} := rfl
  have hBB : B = {p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k ≤ p.2 * h} := rfl
  rw [← Finset.card_union_add_card_inter A B]
  have hUnion : A ∪ B = Finset.Icc 1 X ×ˢ Finset.Icc 1 Y := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with hpA | hpB
      · exact (Finset.mem_filter.mp hpA).1
      · exact (Finset.mem_filter.mp hpB).1
    · intro hp
      rcases le_total (p.2 * h) (p.1 * k) with hle | hle
      · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_filter.mpr ⟨hp, hle⟩
      · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_filter.mpr ⟨hp, hle⟩
  have hInter : A ∩ B = {p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k = p.2 * h} := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_inter.mp hp with ⟨hpA, hpB⟩
      rcases Finset.mem_filter.mp hpA with ⟨hpRect, hAineq⟩
      rcases Finset.mem_filter.mp hpB with ⟨_, hBineq⟩
      exact Finset.mem_filter.mpr ⟨hpRect, le_antisymm hBineq hAineq⟩
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpRect, hpEq⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨hpRect, hpEq.ge⟩, Finset.mem_filter.mpr ⟨hpRect, hpEq.le⟩⟩
  calc
    #(A ∪ B) + #(A ∩ B) =
        #(Finset.Icc 1 X ×ˢ Finset.Icc 1 Y) +
          #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k = p.2 * h} := by
            rw [hUnion, hInter]
    _ = #(Finset.Icc 1 X ×ˢ Finset.Icc 1 Y) + X / h := by
          rw [card_filter_mul_eq_eq_div hh hk hcop hdiv]
    _ = X * Y + X / h := by
          rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc]
          simp

/-- **Proposition 12, rational case** (Báez-Duarte–Balazard–Landreau–Saias): for coprime
    positive naturals `h, k` and real `x > 0`,
    `∑_{m≤⌊x⌋} ⌊m·k/h⌋ + ∑_{n≤⌊(k/h)x⌋} ⌊n·h/k⌋ = ⌊x⌋⌊(k/h)x⌋ + ⌊x/h⌋`.

    The proof is purely combinatorial: each floor sum becomes the cardinality of one triangle of
    lattice points in the rectangle `[1,⌊x⌋] × [1,⌊(k/h)x⌋]`; the two triangles cover the whole
    rectangle and overlap exactly on the diagonal `m*k = n*h`, whose cardinality is
    `⌊x / h⌋ = ⌊(k/h)x⌋ / k = ⌊x⌋ / h`. -/
theorem baezDuarte_prop12_rat {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) (x : ℝ) (hx : 0 < x) :
    (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (⌊(m : ℝ) * ((k : ℝ) / (h : ℝ))⌋ : ℝ)) +
        (∑ n ∈ Finset.Icc 1 ⌊(k : ℝ) / (h : ℝ) * x⌋₊, (⌊(n : ℝ) / ((k : ℝ) / (h : ℝ))⌋ : ℝ)) =
      (⌊x⌋₊ : ℝ) * (⌊(k : ℝ) / (h : ℝ) * x⌋₊ : ℝ) + (⌊x / (h : ℝ)⌋₊ : ℝ) := by
  set θ : ℝ := (k : ℝ) / (h : ℝ) with hθdef
  set X : ℕ := ⌊x⌋₊ with hXdef
  set Y : ℕ := ⌊θ * x⌋₊ with hYdef
  clear_value θ X Y
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hθpos : 0 < θ := by
    rw [hθdef]
    positivity
  have hθnonneg : 0 ≤ θ := hθpos.le
  have hXdiv : X / h = ⌊x / (h : ℝ)⌋₊ := by
    rw [hXdef]
    exact natFloor_div_eq_natFloor_div x h
  have hYdiv : Y / k = ⌊x / (h : ℝ)⌋₊ := by
    rw [hYdef, hθdef]
    exact natFloor_theta_mul_div_eq_natFloor_div hh hk x
  have hdiv : X / h = Y / k := by rw [hXdiv, hYdiv]
  have hXY : ∀ m ∈ Finset.Icc 1 X, m * k / h ≤ Y := by
    intro m hm
    have hmX : (m : ℝ) ≤ X := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hXx : (X : ℝ) ≤ x := by rw [hXdef]; exact Nat.floor_le hx.le
    have hmx : (m : ℝ) ≤ x := hmX.trans hXx
    have hle : ((m * k : ℕ) : ℝ) / (h : ℝ) ≤ θ * x := by
      rw [show ((m * k : ℕ) : ℝ) / (h : ℝ) = (m : ℝ) * θ by
        rw [hθdef]
        push_cast
        ring]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hmx hθnonneg
    rw [show m * k / h = ⌊((m * k : ℕ) : ℝ) / (h : ℝ)⌋₊ by
      simpa using (Nat.floor_div_eq_div (K := ℝ) (m * k) h).symm, hYdef]
    exact Nat.floor_le_floor hle
  have hYX : ∀ n ∈ Finset.Icc 1 Y, n * h / k ≤ X := by
    intro n hn
    have hnY : (n : ℝ) ≤ Y := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hYθx : (Y : ℝ) ≤ θ * x := by
      rw [hYdef]
      exact Nat.floor_le (by positivity : (0 : ℝ) ≤ θ * x)
    have hnθx : (n : ℝ) ≤ θ * x := hnY.trans hYθx
    have hscaled :
        (n : ℝ) * ((h : ℝ) / (k : ℝ)) ≤ (θ * x) * ((h : ℝ) / (k : ℝ)) :=
      mul_le_mul_of_nonneg_right hnθx (by positivity)
    have hle : ((n * h : ℕ) : ℝ) / (k : ℝ) ≤ x := by
      have hleft : ((n * h : ℕ) : ℝ) / (k : ℝ) = (n : ℝ) * ((h : ℝ) / (k : ℝ)) := by
        push_cast
        ring
      have hright : (θ * x) * ((h : ℝ) / (k : ℝ)) = x := by
        rw [hθdef]
        field_simp [hhR, hkR]
      rw [hright] at hscaled
      have hle' : (n : ℝ) * ((h : ℝ) / (k : ℝ)) ≤ x := hscaled
      simpa [hleft, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hle'
    rw [show n * h / k = ⌊((n * h : ℕ) : ℝ) / (k : ℝ)⌋₊ by
      simpa using (Nat.floor_div_eq_div (K := ℝ) (n * h) k).symm, hXdef]
    exact Nat.floor_le_floor hle
  have hnat :
      (∑ m ∈ Finset.Icc 1 X, m * k / h) + (∑ n ∈ Finset.Icc 1 Y, n * h / k) =
        X * Y + X / h :=
    baezDuarte_prop12_nat_aux hh hk hcop hXY hYX hdiv
  have hsumX :
      (∑ m ∈ Finset.Icc 1 X, (⌊(m : ℝ) * θ⌋ : ℝ)) =
        ∑ m ∈ Finset.Icc 1 X, ((m * k / h : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [← natCast_floor_eq_intCast_floor (show (0 : ℝ) ≤ (m : ℝ) * θ by positivity)]
    have hfloor : ⌊(m : ℝ) * θ⌋₊ = m * k / h := by
      calc
        ⌊(m : ℝ) * θ⌋₊ = ⌊((m * k : ℕ) : ℝ) / (h : ℝ)⌋₊ := by
          congr 1
          rw [hθdef]
          push_cast
          ring
        _ = m * k / h := Nat.floor_div_eq_div (K := ℝ) (m * k) h
    rw [hfloor]
  have hsumY :
      (∑ n ∈ Finset.Icc 1 Y, (⌊(n : ℝ) / θ⌋ : ℝ)) =
        ∑ n ∈ Finset.Icc 1 Y, ((n * h / k : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [← natCast_floor_eq_intCast_floor (show (0 : ℝ) ≤ (n : ℝ) / θ by
      exact div_nonneg (by positivity) hθnonneg)]
    have hfloor : ⌊(n : ℝ) / θ⌋₊ = n * h / k := by
      calc
        ⌊(n : ℝ) / θ⌋₊ = ⌊((n * h : ℕ) : ℝ) / (k : ℝ)⌋₊ := by
          congr 1
          rw [hθdef]
          field_simp [hhR, hkR]
          push_cast
          ring
        _ = n * h / k := Nat.floor_div_eq_div (K := ℝ) (n * h) k
    rw [hfloor]
  have hFreal : ((X / h : ℕ) : ℝ) = (⌊x / (h : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast hXdiv
  have hXreal : (X : ℝ) = (⌊x⌋₊ : ℝ) := by rw [hXdef]
  have hYreal : (Y : ℝ) = (⌊(k : ℝ) / (h : ℝ) * x⌋₊ : ℝ) := by
    rw [hYdef, hθdef]
  have hprod :
      (X : ℝ) * (Y : ℝ) =
        (⌊x⌋₊ : ℝ) * (⌊(k : ℝ) / (h : ℝ) * x⌋₊ : ℝ) := by
    rw [hXreal, hYreal]
  have hmain :
      (∑ m ∈ Finset.Icc 1 X, (⌊(m : ℝ) * θ⌋ : ℝ)) +
          (∑ n ∈ Finset.Icc 1 Y, (⌊(n : ℝ) / θ⌋ : ℝ)) =
        (⌊x⌋₊ : ℝ) * (⌊(k : ℝ) / (h : ℝ) * x⌋₊ : ℝ) + (⌊x / (h : ℝ)⌋₊ : ℝ) := by
    rw [hsumY, hsumX]
    calc
      (∑ m ∈ Finset.Icc 1 X, ((m * k / h : ℕ) : ℝ)) +
          (∑ n ∈ Finset.Icc 1 Y, ((n * h / k : ℕ) : ℝ)) =
          (X : ℝ) * (Y : ℝ) + ((X / h : ℕ) : ℝ) := by
            exact_mod_cast hnat
      _ = (X : ℝ) * (Y : ℝ) + (⌊x / (h : ℝ)⌋₊ : ℝ) := by rw [hFreal]
      _ = (⌊x⌋₊ : ℝ) * (⌊(k : ℝ) / (h : ℝ) * x⌋₊ : ℝ) + (⌊x / (h : ℝ)⌋₊ : ℝ) := by
        simpa using congrArg (fun t : ℝ => t + (⌊x / (h : ℝ)⌋₊ : ℝ)) hprod
  simpa [hXdef, hYdef, hθdef] using hmain

/-- **Proposition 21, rational case** (`θ = k/h`, coprime, `h,k > 0` — the only case this
    project needs), assembled from Proposition 15 (`sum_Icc_one_natCast_eq_of_fract`, proved
    above) and Proposition 12's rational-case floor-sum identity, taken here as an explicit
    hypothesis (`hprop12`) rather than proved — a genuine, separate classical lattice-point
    counting fact (the BBLS paper itself cites Hardy-Littlewood, *The lattice-points of a
    right-angled triangle*, for this style of result), deliberately isolated rather than
    attempted here. This mirrors the project's own established discipline of taking hard,
    separable analytic content as an explicit hypothesis (e.g.
    `QuadraticInteractionAnalyticSubEstimates` in `QuadraticInteraction.lean`).

    Once `hprop12` is available, everything else is finite real-number algebra: expand both
    `bernoulliB1` sums via `sum_bernoulliB1_eq`, convert the resulting `Int.fract` sums via
    `sum_fract_sub_half_eq`, apply Proposition 15 to the two natural-number sums, substitute
    `hprop12` for the two floor sums, and simplify the exact-integer-hit correction terms via
    `card_filter_fract_mul_div_eq_zero` and the floor-nesting lemmas (both hit counts reduce to
    `⌊x/h⌋₊`, which is exactly `hprop12`'s own correction term — this is the "cancellation"
    the paper's own proof describes for the general case, made explicit and direct here for the
    rational case). Hand-verified symbolically (not just numerically) before writing this
    proof: every non-cancelling term matches the target RHS exactly. -/
theorem baezDuarte_prop21_rat_of_prop12_aux {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) (x : ℝ) (hx : 0 < x)
    (hprop12 :
      (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (⌊(m : ℝ) * ((k : ℝ) / (h : ℝ))⌋ : ℝ)) +
          (∑ n ∈ Finset.Icc 1 ⌊(k : ℝ) / (h : ℝ) * x⌋₊, (⌊(n : ℝ) / ((k : ℝ) / (h : ℝ))⌋ : ℝ)) =
        (⌊x⌋₊ : ℝ) * (⌊(k : ℝ) / (h : ℝ) * x⌋₊ : ℝ) + (⌊x / (h : ℝ)⌋₊ : ℝ)) :
    (∑ n ∈ Finset.Icc 1 ⌊(k : ℝ) / (h : ℝ) * x⌋₊, bernoulliB1 ((n : ℝ) / ((k : ℝ) / (h : ℝ)))) +
        (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * ((k : ℝ) / (h : ℝ)))) =
      (1 / (2 * ((k : ℝ) / (h : ℝ)))) *
          (Int.fract ((k : ℝ) / (h : ℝ) * x) - (k : ℝ) / (h : ℝ) * Int.fract x) ^ 2 +
        ((((k : ℝ) / (h : ℝ)) - 1) / (2 * ((k : ℝ) / (h : ℝ)))) *
          (Int.fract ((k : ℝ) / (h : ℝ) * x) - (k : ℝ) / (h : ℝ) * Int.fract x) := by
  set θ : ℝ := (k : ℝ) / (h : ℝ) with hθdef
  set X : ℕ := ⌊x⌋₊ with hXdef
  set Y : ℕ := ⌊θ * x⌋₊ with hYdef
  clear_value θ X Y
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθR : θ ≠ 0 := hθpos.ne'
  -- Step 1+2: expand both B1 sums into fract-sums, then into plain sums minus floor-sums.
  have hB1n := sum_bernoulliB1_eq Y (fun n => (n : ℝ) / θ)
  have hB1m := sum_bernoulliB1_eq X (fun m => (m : ℝ) * θ)
  have hfn := sum_fract_sub_half_eq Y (fun n => (n : ℝ) / θ)
  have hfm := sum_fract_sub_half_eq X (fun m => (m : ℝ) * θ)
  -- Step 3: Proposition 15 applied to both index sets.
  have hP15n : (∑ n ∈ Finset.Icc 1 Y, (n : ℝ)) =
      (θ * x) ^ 2 / 2 - (θ * x) * Int.fract (θ * x) + (Int.fract (θ * x)) ^ 2 / 2 +
        (θ * x) / 2 - (Int.fract (θ * x)) / 2 := by
    have hh15 := sum_Icc_one_natCast_eq_of_fract (θ * x) (by positivity)
    rwa [← hYdef] at hh15
  have hP15m : (∑ m ∈ Finset.Icc 1 X, (m : ℝ)) =
      x ^ 2 / 2 - x * Int.fract x + (Int.fract x) ^ 2 / 2 + x / 2 - (Int.fract x) / 2 := by
    have hh15 := sum_Icc_one_natCast_eq_of_fract x hx.le
    rwa [← hXdef] at hh15
  -- Step 4: the two exact-integer-hit filter cards both reduce to ⌊x/h⌋₊.
  have hcardm : ((Finset.Icc 1 X).filter (fun m : ℕ => Int.fract ((m : ℝ) * θ) = 0)).card =
      X / h := by
    rw [hθdef]; exact card_filter_fract_mul_div_eq_zero hh hcop X
  have hcardn : ((Finset.Icc 1 Y).filter (fun n : ℕ => Int.fract ((n : ℝ) / θ) = 0)).card =
      Y / k := by
    rw [show (Finset.Icc 1 Y).filter (fun n : ℕ => Int.fract ((n : ℝ) / θ) = 0) =
        (Finset.Icc 1 Y).filter (fun n : ℕ => Int.fract ((n : ℝ) * ((h : ℝ) / (k : ℝ))) = 0) from
      Finset.filter_congr (fun n _ => by
        have heq : (n : ℝ) / θ = (n : ℝ) * ((h : ℝ) / (k : ℝ)) := by rw [hθdef]; field_simp
        rw [heq])]
    exact card_filter_fract_mul_div_eq_zero hk hcop.symm Y
  have hFdef : ((X / h : ℕ) : ℝ) = (⌊x / (h : ℝ)⌋₊ : ℝ) := by
    have := natFloor_div_eq_natFloor_div x h
    rw [← hXdef] at this
    exact_mod_cast this
  have hFdef2 : ((Y / k : ℕ) : ℝ) = (⌊x / (h : ℝ)⌋₊ : ℝ) := by
    have hnest := natFloor_theta_mul_div_eq_natFloor_div hh hk x
    rw [← hθdef, ← hYdef] at hnest
    exact_mod_cast hnest
  -- Split the two `∑ i, i/θ` and `∑ i, i*θ` sums into `(∑ i, i)` scaled by `θ`.
  have hsplitn : (∑ n ∈ Finset.Icc 1 Y, (n : ℝ) / θ) = (∑ n ∈ Finset.Icc 1 Y, (n : ℝ)) / θ := by
    rw [Finset.sum_div]
  have hsplitm : (∑ m ∈ Finset.Icc 1 X, (m : ℝ) * θ) = (∑ m ∈ Finset.Icc 1 X, (m : ℝ)) * θ := by
    rw [Finset.sum_mul]
  -- Assemble: rewrite both B1 sums, combine, substitute Proposition 12, cancel the F-terms.
  rw [hB1n, hB1m, hfn, hfm, hsplitn, hsplitm, hP15n, hP15m, hcardm, hcardn, hFdef, hFdef2]
  have hXR : (X : ℝ) = x - Int.fract x := by
    have h1 : ((X : ℤ) : ℝ) = x - Int.fract x := by
      rw [hXdef]
      have := Int.natCast_floor_eq_floor hx.le
      have h2 : ((⌊x⌋₊ : ℤ) : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast this
      rw [h2]; linarith [Int.self_sub_fract x]
    exact_mod_cast h1
  have hYR : (Y : ℝ) = θ * x - Int.fract (θ * x) := by
    have h1 : ((Y : ℤ) : ℝ) = θ * x - Int.fract (θ * x) := by
      rw [hYdef]
      have := Int.natCast_floor_eq_floor (by positivity : (0:ℝ) ≤ θ * x)
      have h2 : ((⌊θ * x⌋₊ : ℤ) : ℝ) = (⌊θ * x⌋ : ℝ) := by exact_mod_cast this
      rw [h2]; linarith [Int.self_sub_fract (θ * x)]
    exact_mod_cast h1
  rw [hXR, hYR] at hprop12 ⊢
  linear_combination (norm := (field_simp; ring)) -hprop12

/-- **Proposition 21, rational case** (`θ = k/h`, coprime, `h,k > 0`), now unconditional:
    the classical floor-sum input is supplied by `baezDuarte_prop12_rat`. -/
theorem baezDuarte_prop21_rat_of_prop12 {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) (x : ℝ) (hx : 0 < x) :
    (∑ n ∈ Finset.Icc 1 ⌊(k : ℝ) / (h : ℝ) * x⌋₊, bernoulliB1 ((n : ℝ) / ((k : ℝ) / (h : ℝ)))) +
        (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * ((k : ℝ) / (h : ℝ)))) =
      (1 / (2 * ((k : ℝ) / (h : ℝ)))) *
          (Int.fract ((k : ℝ) / (h : ℝ) * x) - (k : ℝ) / (h : ℝ) * Int.fract x) ^ 2 +
        ((((k : ℝ) / (h : ℝ)) - 1) / (2 * ((k : ℝ) / (h : ℝ)))) *
          (Int.fract ((k : ℝ) / (h : ℝ) * x) - (k : ℝ) / (h : ℝ) * Int.fract x) := by
  exact baezDuarte_prop21_rat_of_prop12_aux hh hk hcop x hx
    (baezDuarte_prop12_rat hh hk hcop x hx)

/-! ## Proposition 22 statement (rational θ = k/h)

The next BBLS step is Proposition 22: a Riemann--Stieltjes integration-by-parts
identity obtained from Proposition 21.  This project only needs the rational
specialization `θ = k/h`, so the frozen statement below follows the same convention as
`baezDuarte_prop21_rat_of_prop12`.

The statement was extracted directly from the saved PDF, visually checked against the
rendered page, and numerically verified by exact piecewise integration for several
rational `(x, θ)` test cases before being introduced here.  The proof is deliberately
left for the next continuation: it should be a discrete Abel/Stieltjes summation-by-parts
argument, not a new analytic estimate.
-/

/-- Elementary positive-endpoint primitive used in the Proposition 22/Proposition 16
    integration-by-parts chain: a constant multiple of `t⁻²` integrates to the endpoint
    difference of `-c/t`.  This small lemma is intentionally local to the BBLS period
    reduction file; the remaining Proposition 22 proof still needs the step-function Abel
    identity and the paper's Proposition 16 fractional-part split. -/
theorem intervalIntegral_const_div_sq (c a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, c / t ^ 2) = c * (1 / a - 1 / b) := by
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => -c / u) (c / t ^ 2) t := by
    intro t ht
    have htpos : 0 < t := by
      rcases le_total a b with hab | hba
      · have ht' : t ∈ Set.Icc a b := by
          simpa [Set.uIcc_of_le hab] using ht
        linarith [ht'.1]
      · have ht' : t ∈ Set.Icc b a := by
          simpa [Set.uIcc_of_ge hba] using ht
        linarith [ht'.1]
    have htne : t ≠ 0 := ne_of_gt htpos
    have h := HasDerivAt.const_mul (-c) (hasDerivAt_inv htne)
    have hfun : (fun u : ℝ => -c * u⁻¹) = fun u : ℝ => -c / u := by
      funext u
      ring
    have hval : -c * -(t ^ 2)⁻¹ = c / t ^ 2 := by
      field_simp
    rw [hfun, hval] at h
    exact h
  have hint : IntervalIntegrable (fun t : ℝ => c / t ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact continuousOn_id.pow 2
    · intro t ht
      have htpos : 0 < t := by
        rcases le_total a b with hab | hba
        · have ht' : t ∈ Set.Icc a b := by
            simpa [Set.uIcc_of_le hab] using ht
          linarith [ht'.1]
        · have ht' : t ∈ Set.Icc b a := by
            simpa [Set.uIcc_of_ge hba] using ht
          linarith [ht'.1]
      positivity
  calc
    (∫ t in a..b, c / t ^ 2) = (-c / b) - (-c / a) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · exact hderiv
      · exact hint
    _ = c * (1 / a - 1 / b) := by
      field_simp [ne_of_gt ha, ne_of_gt hb]
      ring

/-- A floor-indexed partial sum is constant on the half-open unit interval `[n,n+1)`. -/
theorem stepPartialSum_eq_on_Ico (a : ℕ → ℝ) (n : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ico (n : ℝ) ((n + 1 : ℕ) : ℝ)) :
    (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) = ∑ m ∈ Finset.Icc 1 n, a m := by
  have hfloor : ⌊u⌋₊ = n := Nat.floor_eq_on_Ico n u (by simpa using hu)
  rw [hfloor]

/-- The initial block contributes zero: on `(0,1)` the floor-indexed step sum is empty. -/
theorem stepPartialSum_div_sq_integral_zero_block (a : ℕ → ℝ) :
    (∫ u in (0 : ℝ)..(1 : ℝ), (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2) = 0 := by
  have hcongr :
      (∫ u in (0 : ℝ)..(1 : ℝ), (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2) =
        (∫ _u in (0 : ℝ)..(1 : ℝ), (0 : ℝ)) := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)] with u hu_ne hu_mem
      have huIco : u ∈ Set.Ico (0 : ℝ) (1 : ℝ) :=
        ⟨hu_mem.1.le, lt_of_le_of_ne hu_mem.2 hu_ne⟩
      change (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2 = 0
      rw [stepPartialSum_eq_on_Ico a 0 (by simpa using huIco)]
      simp
    · filter_upwards with u hu_mem
      exfalso
      have : (1 : ℝ) < 0 := lt_of_lt_of_le hu_mem.1 hu_mem.2
      norm_num at this
  rw [hcongr]
  simp

/-- If `⌊x⌋₊ = 0`, then the whole step-function integral from `0` to `x` vanishes. -/
theorem stepPartialSum_div_sq_integral_of_floor_eq_zero (a : ℕ → ℝ) {x : ℝ}
    (hx : 0 < x) (hfloor : ⌊x⌋₊ = 0) :
    (∫ u in (0 : ℝ)..x, (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2) = 0 := by
  have hxlt : x < 1 := Nat.floor_eq_zero.mp hfloor
  have hcongr :
      (∫ u in (0 : ℝ)..x, (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2) =
        (∫ _u in (0 : ℝ)..x, (0 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) x := by
      simpa [Set.uIcc_of_le hx.le] using hu
    have huIco : u ∈ Set.Ico (0 : ℝ) (1 : ℝ) :=
      ⟨huIcc.1, lt_of_le_of_lt huIcc.2 hxlt⟩
    change (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2 = 0
    rw [stepPartialSum_eq_on_Ico a 0 (by simpa using huIco)]
    simp
  rw [hcongr]
  simp

/-- Integral of one positive unit block of the floor-indexed step function. -/
theorem stepPartialSum_div_sq_integral_nat_block (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ u in (n : ℝ)..((n + 1 : ℕ) : ℝ),
        (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2) =
      (∑ m ∈ Finset.Icc 1 n, a m) *
        (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) := by
  have hcongr :
      (∫ u in (n : ℝ)..((n + 1 : ℕ) : ℝ),
          (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2) =
        (∫ u in (n : ℝ)..((n + 1 : ℕ) : ℝ),
          (∑ m ∈ Finset.Icc 1 n, a m) / u ^ 2) := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (((n + 1 : ℕ) : ℝ))]
        with u hu_ne hu_mem
      have huIco : u ∈ Set.Ico (n : ℝ) ((n + 1 : ℕ) : ℝ) :=
        ⟨hu_mem.1.le, lt_of_le_of_ne hu_mem.2 hu_ne⟩
      change (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2 =
        (∑ m ∈ Finset.Icc 1 n, a m) / u ^ 2
      rw [stepPartialSum_eq_on_Ico a n huIco]
    · filter_upwards with u hu_mem
      exfalso
      have hle : (((n + 1 : ℕ) : ℝ) ≤ (n : ℝ)) := le_trans hu_mem.1.le hu_mem.2
      have hnat : n + 1 ≤ n := by exact_mod_cast hle
      omega
  rw [hcongr]
  exact intervalIntegral_const_div_sq (∑ m ∈ Finset.Icc 1 n, a m) (n : ℝ)
    ((n + 1 : ℕ) : ℝ) (by exact_mod_cast hn) (by positivity)

/-- Local integrability of the floor-indexed step function on each unit block. -/
theorem stepPartialSum_div_sq_intervalIntegrable_nat_block (a : ℕ → ℝ) (n : ℕ) :
    IntervalIntegrable (fun u : ℝ => (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2)
      MeasureTheory.volume (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
  by_cases hn : n = 0
  · subst n
    have hAE :
        (fun u : ℝ => (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2) =ᵐ[
          MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (1 : ℝ))] (fun _ : ℝ => 0) := by
      change ∀ᵐ u : ℝ ∂MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (1 : ℝ)),
        (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2 = 0
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)] with u hu_ne hu
      have huIoc : u ∈ Set.Ioc (0 : ℝ) (1 : ℝ) := by
        simpa [Set.uIoc_of_le zero_le_one] using hu
      have huIco : u ∈ Set.Ico (0 : ℝ) (1 : ℝ) :=
        ⟨huIoc.1.le, lt_of_le_of_ne huIoc.2 hu_ne⟩
      rw [stepPartialSum_eq_on_Ico a 0 (by simpa using huIco)]
      simp
    simpa using (intervalIntegrable_congr_ae hAE).2 IntervalIntegrable.zero
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let c : ℝ := ∑ m ∈ Finset.Icc 1 n, a m
    have hAE :
        (fun u : ℝ => (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2) =ᵐ[
          MeasureTheory.volume.restrict (Set.uIoc (n : ℝ) ((n + 1 : ℕ) : ℝ))]
          (fun u : ℝ => c / u ^ 2) := by
      change ∀ᵐ u : ℝ ∂MeasureTheory.volume.restrict
          (Set.uIoc (n : ℝ) ((n + 1 : ℕ) : ℝ)),
        (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2 = c / u ^ 2
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (((n + 1 : ℕ) : ℝ))]
        with u hu_ne hu
      have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      have huIoc : u ∈ Set.Ioc (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
        simpa [Set.uIoc_of_le hle] using hu
      have huIco : u ∈ Set.Ico (n : ℝ) ((n + 1 : ℕ) : ℝ) :=
        ⟨huIoc.1.le, lt_of_le_of_ne huIoc.2 hu_ne⟩
      rw [stepPartialSum_eq_on_Ico a n huIco]
    have hg : IntervalIntegrable (fun u : ℝ => c / u ^ 2) MeasureTheory.volume
        (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div
      · exact continuousOn_const
      · exact continuousOn_id.pow 2
      · intro u hu
        have huIcc : u ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
          simpa [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ n)] using hu
        have hupos : 0 < u := lt_of_lt_of_le (by exact_mod_cast hnpos) huIcc.1
        positivity
    exact (intervalIntegrable_congr_ae hAE).2 hg

/-- Integral from `0` to an integer endpoint, with the final block isolated for later
    cancellation against the endpoint term in Abel summation. -/
theorem stepPartialSum_div_sq_integral_zero_to_nat (a : ℕ → ℝ) (N : ℕ) :
    (∫ u in (0 : ℝ)..(N : ℝ), (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2) =
      (∑ k ∈ Finset.Icc 1 N,
          (∑ m ∈ Finset.Icc 1 k, a m) *
            (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) -
        (∑ m ∈ Finset.Icc 1 N, a m) *
          (1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hprevInt : IntervalIntegrable
          (fun u : ℝ => (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2)
          MeasureTheory.volume (0 : ℝ) (N : ℝ) := by
        simpa using (IntervalIntegrable.trans_iterate
          (a := fun k : ℕ => (k : ℝ)) (n := N)
          (fun k _hk => stepPartialSum_div_sq_intervalIntegrable_nat_block a k))
      have hblockInt := stepPartialSum_div_sq_intervalIntegrable_nat_block a N
      have hadd := intervalIntegral.integral_add_adjacent_intervals hprevInt hblockInt
      rw [← hadd, ih]
      by_cases hN0 : N = 0
      · subst N
        have hzero :
            (∫ x in ((0 : ℕ) : ℝ)..(((0 + 1 : ℕ)) : ℝ),
              (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, a m) / x ^ 2) = 0 := by
          simpa using stepPartialSum_div_sq_integral_zero_block a
        rw [hzero]
        norm_num
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
        rw [stepPartialSum_div_sq_integral_nat_block a hNpos]
        have hone : 1 ≤ N + 1 := by omega
        rw [Finset.sum_Icc_succ_top hone]
        ring

/-- Tail block from the last integer endpoint `N = ⌊x⌋₊` to `x`. -/
theorem stepPartialSum_div_sq_integral_floor_tail (a : ℕ → ℝ) {x : ℝ}
    (hx : 0 < x) {N : ℕ} (hN : ⌊x⌋₊ = N) (hNpos : 0 < N) :
    (∫ u in (N : ℝ)..x, (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2) =
      (∑ m ∈ Finset.Icc 1 N, a m) * (1 / (N : ℝ) - 1 / x) := by
  have hNx : (N : ℝ) ≤ x := by
    rw [← hN]
    exact Nat.floor_le hx.le
  have hxlt : x < ((N + 1 : ℕ) : ℝ) := by
    rw [← hN]
    simpa [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
  have hcongr :
      (∫ u in (N : ℝ)..x, (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2) =
        (∫ u in (N : ℝ)..x, (∑ m ∈ Finset.Icc 1 N, a m) / u ^ 2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have huIcc : u ∈ Set.Icc (N : ℝ) x := by
      simpa [Set.uIcc_of_le hNx] using hu
    have huIco : u ∈ Set.Ico (N : ℝ) ((N + 1 : ℕ) : ℝ) :=
      ⟨huIcc.1, lt_of_le_of_lt huIcc.2 hxlt⟩
    change (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2 =
      (∑ m ∈ Finset.Icc 1 N, a m) / u ^ 2
    rw [stepPartialSum_eq_on_Ico a N huIco]
  rw [hcongr]
  exact intervalIntegral_const_div_sq (∑ m ∈ Finset.Icc 1 N, a m) (N : ℝ) x
    (by exact_mod_cast hNpos) hx

/-- Local integrability on the final tail block `N..x`, where `N = ⌊x⌋₊ > 0`. -/
theorem stepPartialSum_div_sq_intervalIntegrable_floor_tail (a : ℕ → ℝ) {x : ℝ}
    (hx : 0 < x) {N : ℕ} (hN : ⌊x⌋₊ = N) (hNpos : 0 < N) :
    IntervalIntegrable (fun u : ℝ => (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2)
      MeasureTheory.volume (N : ℝ) x := by
  let c : ℝ := ∑ m ∈ Finset.Icc 1 N, a m
  have hNx : (N : ℝ) ≤ x := by
    rw [← hN]
    exact Nat.floor_le hx.le
  have hxlt : x < ((N + 1 : ℕ) : ℝ) := by
    rw [← hN]
    simpa [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
  have hEq : Set.EqOn
      (fun u : ℝ => (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2)
      (fun u : ℝ => c / u ^ 2) (Set.uIoc (N : ℝ) x) := by
    intro u hu
    have huIoc : u ∈ Set.Ioc (N : ℝ) x := by
      simpa [Set.uIoc_of_le hNx] using hu
    have huIco : u ∈ Set.Ico (N : ℝ) ((N + 1 : ℕ) : ℝ) :=
      ⟨huIoc.1.le, lt_of_le_of_lt huIoc.2 hxlt⟩
    change (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2 = c / u ^ 2
    rw [stepPartialSum_eq_on_Ico a N huIco]
  have hg : IntervalIntegrable (fun u : ℝ => c / u ^ 2) MeasureTheory.volume (N : ℝ) x := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact continuousOn_id.pow 2
    · intro u hu
      have huIcc : u ∈ Set.Icc (N : ℝ) x := by
        simpa [Set.uIcc_of_le hNx] using hu
      have hupos : 0 < u := lt_of_lt_of_le (by exact_mod_cast hNpos) huIcc.1
      positivity
  exact (intervalIntegrable_congr hEq).2 hg

/-- Finite Abel summation for a cutoff that vanishes at `N + 1`, local to the BBLS
    step-function proof.  This is the same proof shape as the private Phase 14 helper
    `sum_Icc_mul_sub_endpoint_eq_sum_partial` in `MobiusSummatory.lean`. -/
private theorem finite_abel_sum_Icc_mul_sub_endpoint_eq_sum_partial
    (a b : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1))) =
      ∑ k ∈ Finset.Icc 1 N,
        (∑ j ∈ Finset.Icc 1 k, a j) * (b k - b (k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hone : 1 ≤ N + 1 := by omega
      rw [Finset.sum_Icc_succ_top hone, Finset.sum_Icc_succ_top hone]
      have hshift :
          (∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1 + 1))) =
            (∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1))) +
              (∑ k ∈ Finset.Icc 1 N, a k) * (b (N + 1) - b (N + 1 + 1)) := by
        calc
          _ = ∑ k ∈ Finset.Icc 1 N,
                (a k * (b k - b (N + 1)) +
                  a k * (b (N + 1) - b (N + 1 + 1))) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
          _ = _ := by
              rw [Finset.sum_add_distrib, Finset.sum_mul]
      rw [hshift, ih, Finset.sum_Icc_succ_top hone]
      ring

/-- Discrete Abel summation in the exact form needed for the step-function integral. -/
theorem sum_Icc_div_eq_endpoint_add_abel (a : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, a k / (k : ℝ)) =
      (∑ k ∈ Finset.Icc 1 N, a k) / ((N + 1 : ℕ) : ℝ) +
        ∑ k ∈ Finset.Icc 1 N,
          (∑ j ∈ Finset.Icc 1 k, a j) *
            (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
  have habel := finite_abel_sum_Icc_mul_sub_endpoint_eq_sum_partial
    a (fun k : ℕ => 1 / (k : ℝ)) N
  have hdiff :
      (∑ k ∈ Finset.Icc 1 N, a k / (k : ℝ)) -
          (∑ k ∈ Finset.Icc 1 N, a k) / ((N + 1 : ℕ) : ℝ) =
        ∑ k ∈ Finset.Icc 1 N,
          (∑ j ∈ Finset.Icc 1 k, a j) *
            (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
    calc
      (∑ k ∈ Finset.Icc 1 N, a k / (k : ℝ)) -
          (∑ k ∈ Finset.Icc 1 N, a k) / ((N + 1 : ℕ) : ℝ) =
          ∑ k ∈ Finset.Icc 1 N,
            (a k / (k : ℝ) - a k / ((N + 1 : ℕ) : ℝ)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_div]
      _ = ∑ k ∈ Finset.Icc 1 N,
            a k * (1 / (k : ℝ) - 1 / ((N + 1 : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = _ := habel
  linarith

/-- Step-function Abel/Stieltjes summation-by-parts identity.

For the step sum `S(u) = ∑_{1≤m≤u} a_m`, this proves
`∑_{1≤m≤x} a_m/m = S(x)/x + ∫₀ˣ S(u)/u² du`.  This is the first
mechanical ingredient needed for the frozen BBLS Proposition 22 proof. -/
theorem stepFunction_abel_stieltjes_identity (a : ℕ → ℝ) {x : ℝ} (hx : 0 < x) :
    (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, a m / (m : ℝ)) =
      (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, a m) / x +
        ∫ u in (0 : ℝ)..x, (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2 := by
  by_cases hfloor0 : ⌊x⌋₊ = 0
  · rw [hfloor0]
    rw [stepPartialSum_div_sq_integral_of_floor_eq_zero a hx hfloor0]
    simp
  · set N : ℕ := ⌊x⌋₊ with hN
    have hNfloor : ⌊x⌋₊ = N := hN.symm
    have hNpos : 0 < N := Nat.pos_of_ne_zero hfloor0
    have hprevInt : IntervalIntegrable
        (fun u : ℝ => (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2)
        MeasureTheory.volume (0 : ℝ) (N : ℝ) := by
      simpa using (IntervalIntegrable.trans_iterate
        (a := fun k : ℕ => (k : ℝ)) (n := N)
        (fun k _hk => stepPartialSum_div_sq_intervalIntegrable_nat_block a k))
    have htailInt := stepPartialSum_div_sq_intervalIntegrable_floor_tail a hx hNfloor hNpos
    have hadd := intervalIntegral.integral_add_adjacent_intervals hprevInt htailInt
    have hzeroN := stepPartialSum_div_sq_integral_zero_to_nat a N
    have htail := stepPartialSum_div_sq_integral_floor_tail a hx hNfloor hNpos
    have habel := sum_Icc_div_eq_endpoint_add_abel a N
    rw [hN]
    calc
      (∑ m ∈ Finset.Icc 1 N, a m / (m : ℝ)) =
          (∑ m ∈ Finset.Icc 1 N, a m) / ((N + 1 : ℕ) : ℝ) +
            ∑ k ∈ Finset.Icc 1 N,
              (∑ j ∈ Finset.Icc 1 k, a j) *
                (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := habel
      _ = (∑ m ∈ Finset.Icc 1 N, a m) / x +
            ∫ u in (0 : ℝ)..x, (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2 := by
          rw [← hadd, hzeroN, htail]
          ring

/-- The scaled companion Abel/Stieltjes identity for the second Proposition 22 sum.

This is just `stepFunction_abel_stieltjes_identity` instantiated with
`a n = B₁(n / θ)` and endpoint `θ*x`. -/
theorem bernoulliB1_scaled_companion_abel_stieltjes_identity {θ x : ℝ}
    (hθ : 0 < θ) (hx : 0 < x) :
    (∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ) / (n : ℝ)) =
      (∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ)) / (θ * x) +
        ∫ u in (0 : ℝ)..(θ * x),
          (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, bernoulliB1 ((n : ℝ) / θ)) / u ^ 2 := by
  simpa using
    (stepFunction_abel_stieltjes_identity
      (fun n : ℕ => bernoulliB1 ((n : ℝ) / θ)) (x := θ * x) (mul_pos hθ hx))

/-- Local interval integrability of the weighted fractional-part function away from zero.

The proof uses only measurability of `Int.fract` and the elementary bound
`0 ≤ Int.fract y < 1`: on an interval whose lower unordered endpoint is positive,
`1 / t²` is bounded.  This packages the local integrability infrastructure needed for
the BBLS Proposition 16 Frullani step without enumerating the finitely many breakpoints
of the fractional part function. -/
theorem fract_mul_div_sq_intervalIntegrable {c a b : ℝ} (hpos : 0 < min a b) :
    IntervalIntegrable (fun t : ℝ => Int.fract (c * t) / t ^ 2)
      MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff]
  refine MeasureTheory.IntegrableOn.of_bound ?hsfin ?hmeas (1 / (min a b) ^ 2) ?hbound
  · rw [Real.volume_uIoc]
    exact ENNReal.ofReal_lt_top
  · exact (by
      measurability :
        Measurable (fun t : ℝ => Int.fract (c * t) / t ^ 2)).aestronglyMeasurable.restrict
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with t ht
    have htIoc : t ∈ Set.Ioc (min a b) (max a b) := by
      simpa [Set.uIoc] using ht
    have hmin_lt_t : min a b < t := htIoc.1
    have htpos : 0 < t := lt_trans hpos hmin_lt_t
    have hfract_nonneg : 0 ≤ Int.fract (c * t) := Int.fract_nonneg _
    have hfract_le : Int.fract (c * t) ≤ 1 := le_of_lt (Int.fract_lt_one _)
    have hm2pos : 0 < (min a b) ^ 2 := sq_pos_of_pos hpos
    have hsq : (min a b) ^ 2 ≤ t ^ 2 := by
      nlinarith [hmin_lt_t.le, hpos, htpos]
    have hden : 1 / t ^ 2 ≤ 1 / (min a b) ^ 2 :=
      one_div_le_one_div_of_le hm2pos hsq
    have hnonneg : 0 ≤ Int.fract (c * t) / t ^ 2 :=
      div_nonneg hfract_nonneg (sq_nonneg t)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      Int.fract (c * t) / t ^ 2 ≤ 1 / t ^ 2 := by
        gcongr
      _ ≤ 1 / (min a b) ^ 2 := hden

set_option linter.flexible false in
/-- Linear fractional-part scaling under the substitution `u = θ*t`.

This is the non-quadratic companion to `fract_sq_scaled_integral`, and is the substitution
step appearing in BBLS Proposition 16. -/
theorem fract_scaled_integral {θ a b : ℝ} (hθ : 0 < θ) :
    (∫ t in a..b, Int.fract (θ * t) / t ^ 2) =
      θ * (∫ u in (θ * a)..(θ * b), Int.fract u / u ^ 2) := by
  let f : ℝ → ℝ := fun u => Int.fract u / u ^ 2
  have hpoint : (fun t : ℝ => Int.fract (θ * t) / t ^ 2) =
      fun t : ℝ => θ ^ 2 * f (θ * t) := by
    funext t
    dsimp [f]
    by_cases ht : t = 0
    · simp [ht]
    · have hθne : θ ≠ 0 := hθ.ne'
      field_simp [hθne, ht, pow_two]
  rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  have hcomp :=
    intervalIntegral.integral_comp_mul_left (f := f) (a := a) (b := b) hθ.ne'
  simp [f, smul_eq_mul] at hcomp ⊢
  rw [hcomp]
  field_simp [hθ.ne']

/-- Local interval integrability of the BBLS Proposition 16 difference integrand away from
zero. -/
theorem prop16_fract_diff_div_sq_intervalIntegrable {θ a b : ℝ} (hpos : 0 < min a b) :
    IntervalIntegrable (fun t : ℝ => (Int.fract (θ * t) - θ * Int.fract t) / t ^ 2)
      MeasureTheory.volume a b := by
  have h1 := fract_mul_div_sq_intervalIntegrable (c := θ) (a := a) (b := b) hpos
  have h2 := fract_mul_div_sq_intervalIntegrable (c := 1) (a := a) (b := b) hpos
  have h2' : IntervalIntegrable (fun t : ℝ => θ * (Int.fract t / t ^ 2))
      MeasureTheory.volume a b := by
    simpa [one_mul] using h2.const_mul θ
  have hsub := h1.sub h2'
  convert hsub using 1
  ext t
  ring

/-- On the open interval below `α = min 1 (1/θ)`, the Proposition 16 difference integrand
vanishes pointwise.  The endpoint is intentionally excluded: if `α = 1`, then
`Int.fract 1 = 0`, so the identity can fail exactly at the endpoint, which is harmless for
interval-integral congruences. -/
theorem prop16_fract_diff_eq_zero_of_lt_alpha {θ α t : ℝ} (hθ : 0 < θ)
    (hα : α = min 1 (1 / θ)) (ht0 : 0 ≤ t) (htα : t < α) :
    Int.fract (θ * t) - θ * Int.fract t = 0 := by
  have hα_le_one : α ≤ 1 := by
    rw [hα]
    exact min_le_left _ _
  have hθα_le_one : θ * α ≤ 1 := by
    rw [hα]
    by_cases hθle : θ ≤ 1
    · have hmin : min (1 : ℝ) (1 / θ) = 1 :=
        min_eq_left (one_le_one_div hθ hθle)
      rw [hmin]
      simpa using hθle
    · have hθge : 1 ≤ θ := le_of_not_ge hθle
      have h1θle : 1 / θ ≤ 1 := by
        simpa using (one_div_le_one_div_of_le zero_lt_one hθge)
      have hmin : min (1 : ℝ) (1 / θ) = 1 / θ := min_eq_right h1θle
      rw [hmin]
      have hmul : θ * (1 / θ) = 1 := by
        field_simp [hθ.ne']
      rw [hmul]
  have ht_lt_one : t < 1 := lt_of_lt_of_le htα hα_le_one
  have hθt_nonneg : 0 ≤ θ * t := mul_nonneg hθ.le ht0
  have hθt_lt_one : θ * t < 1 :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left htα hθ) hθα_le_one
  rw [Int.fract_eq_self.mpr ⟨ht0, ht_lt_one⟩]
  rw [Int.fract_eq_self.mpr ⟨hθt_nonneg, hθt_lt_one⟩]
  ring

/-- Positive-endpoint primitive for `1/t`, local to the BBLS Proposition 16 proof. -/
theorem intervalIntegral_one_div (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, (1 : ℝ) / t) = Real.log b - Real.log a := by
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt Real.log (1 / t) t := by
    intro t ht
    have htpos : 0 < t := by
      rcases le_total a b with hab | hba
      · have ht' : t ∈ Set.Icc a b := by
          simpa [Set.uIcc_of_le hab] using ht
        linarith [ht'.1]
      · have ht' : t ∈ Set.Icc b a := by
          simpa [Set.uIcc_of_ge hba] using ht
        linarith [ht'.1]
    simpa [one_div] using Real.hasDerivAt_log htpos.ne'
  have hint : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact continuousOn_id
    · intro t ht
      have htpos : 0 < t := by
        rcases le_total a b with hab | hba
        · have ht' : t ∈ Set.Icc a b := by
            simpa [Set.uIcc_of_le hab] using ht
          linarith [ht'.1]
        · have ht' : t ∈ Set.Icc b a := by
            simpa [Set.uIcc_of_ge hba] using ht
          linarith [ht'.1]
      exact ne_of_gt htpos
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- On intervals contained in `(0,1]`, the fractional-part integral reduces to the logarithmic
primitive.  Endpoint disagreements at `1` are removed by an a.e. congruence. -/
theorem fract_div_sq_integral_of_pos_le_one {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    (∫ u in a..b, Int.fract u / u ^ 2) = Real.log b - Real.log a := by
  have hcongr :
      (∫ u in a..b, Int.fract u / u ^ 2) = (∫ u in a..b, (1 : ℝ) / u) := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)] with u hu_ne hu
      have hupos : 0 < u := lt_trans ha hu.1
      have hule : u ≤ 1 := le_trans hu.2 hb1
      have hult : u < 1 := lt_of_le_of_ne hule hu_ne
      rw [Int.fract_eq_self.mpr ⟨hupos.le, hult⟩]
      field_simp [ne_of_gt hupos]
    · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)] with u hu_ne hu
      have hupos : 0 < u := lt_trans hb hu.1
      have hule : u ≤ 1 := le_trans hu.2 ha1
      have hult : u < 1 := lt_of_le_of_ne hule hu_ne
      rw [Int.fract_eq_self.mpr ⟨hupos.le, hult⟩]
      field_simp [ne_of_gt hupos]
  rw [hcongr]
  exact intervalIntegral_one_div a b ha hb

/-- The Proposition 16 difference integrand integrates to zero on any oriented interval
contained in `[0, α]`, where `α = min 1 (1/θ)`.  The proof uses an a.e. congruence to avoid
the possible endpoint discontinuity at `α`. -/
theorem prop16_fract_diff_integral_eq_zero_of_nonneg_le_alpha {θ α a b : ℝ}
    (hθ : 0 < θ) (hα : α = min 1 (1 / θ))
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (haα : a ≤ α) (hbα : b ≤ α) :
    (∫ t in a..b, (Int.fract (θ * t) - θ * Int.fract t) / t ^ 2) = 0 := by
  have hcongr :
      (∫ t in a..b, (Int.fract (θ * t) - θ * Int.fract t) / t ^ 2) =
        (∫ _t in a..b, (0 : ℝ)) := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume α] with t ht_ne ht
      have ht0 : 0 ≤ t := le_trans ha0 ht.1.le
      have htα : t < α := lt_of_le_of_ne (le_trans ht.2 hbα) ht_ne
      rw [prop16_fract_diff_eq_zero_of_lt_alpha hθ hα ht0 htα]
      simp
    · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume α] with t ht_ne ht
      have ht0 : 0 ≤ t := le_trans hb0 ht.1.le
      have htα : t < α := lt_of_le_of_ne (le_trans ht.2 haα) ht_ne
      rw [prop16_fract_diff_eq_zero_of_lt_alpha hθ hα ht0 htα]
      simp
  rw [hcongr]
  simp

/-- **BBLS Proposition 16**, Frullani-type fractional-part identity.

For positive real `x` and `θ`, Báez-Duarte--Balazard--Landreau--Saias prove

`∫₀ˣ t⁻²({θt} - θ{t}) dt =
  θ log(1/θ) + θ ∫ₓ^{θx} u⁻² {u} du`.

The proof splits at `α = min 1 (1/θ)`, where the difference integrand vanishes below
`α`, uses the substitution `u = θ*t`, and evaluates the remaining small interval via
`{u} = u` on `(0,1)`.  The formula was re-checked against the paper and by exact
piecewise numerical integration on rational test cases before formalization. -/
theorem baezDuarte_prop16_frullani {θ x : ℝ} (hθ : 0 < θ) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, (Int.fract (θ * t) - θ * Int.fract t) / t ^ 2) =
      θ * Real.log (1 / θ) + θ * (∫ u in x..(θ * x), Int.fract u / u ^ 2) := by
  set α : ℝ := min 1 (1 / θ) with hαdef
  have hα : α = min 1 (1 / θ) := hαdef
  have hαpos : 0 < α := by
    rw [hα]
    exact lt_min zero_lt_one (one_div_pos.mpr hθ)
  have hαle1 : α ≤ 1 := by
    rw [hα]
    exact min_le_left _ _
  have hθαpos : 0 < θ * α := mul_pos hθ hαpos
  have hθαle1 : θ * α ≤ 1 := by
    rw [hα]
    by_cases hθle : θ ≤ 1
    · have hmin : min (1 : ℝ) (1 / θ) = 1 := min_eq_left (one_le_one_div hθ hθle)
      rw [hmin]
      simpa using hθle
    · have hθge : 1 ≤ θ := le_of_not_ge hθle
      have h1θle : 1 / θ ≤ 1 := by
        simpa using (one_div_le_one_div_of_le zero_lt_one hθge)
      have hmin : min (1 : ℝ) (1 / θ) = 1 / θ := min_eq_right h1θle
      rw [hmin]
      have hmul : θ * (1 / θ) = 1 := by field_simp [hθ.ne']
      rw [hmul]
  by_cases hxα : x < α
  · have hleftzero := prop16_fract_diff_integral_eq_zero_of_nonneg_le_alpha
      (θ := θ) (α := α) (a := (0 : ℝ)) (b := x) hθ hα (by norm_num) hx.le hαpos.le hxα.le
    have hxle1 : x ≤ 1 := le_trans hxα.le hαle1
    have hθxpos : 0 < θ * x := mul_pos hθ hx
    have hθxle1 : θ * x ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hxα.le hθ.le) hθαle1
    have hint := fract_div_sq_integral_of_pos_le_one hx hθxpos hxle1 hθxle1
    rw [hleftzero, hint]
    rw [Real.log_mul hθ.ne' hx.ne']
    rw [show (1 / θ : ℝ) = θ⁻¹ by ring, Real.log_inv]
    ring
  · have hαx : α ≤ x := le_of_not_gt hxα
    have hzero0α := prop16_fract_diff_integral_eq_zero_of_nonneg_le_alpha
      (θ := θ) (α := α) (a := (0 : ℝ)) (b := α) hθ hα (by norm_num) hαpos.le hαpos.le le_rfl
    have hsmallAE :
        (fun t : ℝ => (Int.fract (θ * t) - θ * Int.fract t) / t ^ 2) =ᵐ[
          MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) α)] (fun _ : ℝ => 0) := by
      change ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) α),
        (Int.fract (θ * t) - θ * Int.fract t) / t ^ 2 = 0
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume α] with t ht_ne ht
      have htIoc : t ∈ Set.Ioc (0 : ℝ) α := by
        simpa [Set.uIoc_of_le hαpos.le] using ht
      have htz := prop16_fract_diff_eq_zero_of_lt_alpha hθ hα htIoc.1.le
        (lt_of_le_of_ne htIoc.2 ht_ne)
      rw [htz]
      simp
    have hsmallInt : IntervalIntegrable
        (fun t : ℝ => (Int.fract (θ * t) - θ * Int.fract t) / t ^ 2)
        MeasureTheory.volume (0 : ℝ) α := by
      exact (intervalIntegrable_congr_ae hsmallAE).2 IntervalIntegrable.zero
    have hlargeInt : IntervalIntegrable
        (fun t : ℝ => (Int.fract (θ * t) - θ * Int.fract t) / t ^ 2)
        MeasureTheory.volume α x := by
      have hmin : min α x = α := min_eq_left hαx
      exact prop16_fract_diff_div_sq_intervalIntegrable (θ := θ) (a := α) (b := x)
        (by simpa [hmin] using hαpos)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hsmallInt hlargeInt
    have hleft :
        (∫ t in (0 : ℝ)..x, (Int.fract (θ * t) - θ * Int.fract t) / t ^ 2) =
          ∫ t in α..x, (Int.fract (θ * t) - θ * Int.fract t) / t ^ 2 := by
      rw [← hadd, hzero0α, zero_add]
    have hexpand :
        (∫ t in α..x, (Int.fract (θ * t) - θ * Int.fract t) / t ^ 2) =
          (∫ t in α..x, Int.fract (θ * t) / t ^ 2) -
            θ * (∫ t in α..x, Int.fract t / t ^ 2) := by
      have hmin : min α x = α := min_eq_left hαx
      have hpos : 0 < min α x := by simpa [hmin] using hαpos
      have h1 := fract_mul_div_sq_intervalIntegrable (c := θ) (a := α) (b := x) hpos
      have h2 := fract_mul_div_sq_intervalIntegrable (c := 1) (a := α) (b := x) hpos
      have h2' : IntervalIntegrable (fun t : ℝ => θ * (Int.fract t / t ^ 2))
          MeasureTheory.volume α x := by
        simpa [one_mul] using h2.const_mul θ
      have hfun : (fun t : ℝ => (Int.fract (θ * t) - θ * Int.fract t) / t ^ 2) =
          fun t : ℝ => Int.fract (θ * t) / t ^ 2 - θ * (Int.fract t / t ^ 2) := by
        funext t
        ring
      rw [hfun]
      rw [intervalIntegral.integral_sub h1 h2']
      rw [intervalIntegral.integral_const_mul]
    have hscaled := fract_scaled_integral (θ := θ) (a := α) (b := x) hθ
    have hinterval :
        (∫ u in (θ * α)..(θ * x), Int.fract u / u ^ 2) -
            (∫ u in α..x, Int.fract u / u ^ 2) =
          Real.log (1 / θ) + (∫ u in x..(θ * x), Int.fract u / u ^ 2) := by
      have hab : IntervalIntegrable (fun u : ℝ => Int.fract u / u ^ 2)
          MeasureTheory.volume (θ * α) (θ * x) := by
        simpa [one_mul] using
          (fract_mul_div_sq_intervalIntegrable (c := 1) (a := θ * α) (b := θ * x)
            (lt_min hθαpos (mul_pos hθ hx)))
      have hcd : IntervalIntegrable (fun u : ℝ => Int.fract u / u ^ 2)
          MeasureTheory.volume α x := by
        simpa [one_mul] using
          (fract_mul_div_sq_intervalIntegrable (c := 1) (a := α) (b := x)
            (lt_min hαpos hx))
      have hac : IntervalIntegrable (fun u : ℝ => Int.fract u / u ^ 2)
          MeasureTheory.volume (θ * α) α := by
        simpa [one_mul] using
          (fract_mul_div_sq_intervalIntegrable (c := 1) (a := θ * α) (b := α)
            (lt_min hθαpos hαpos))
      have hcomm := intervalIntegral.integral_interval_sub_interval_comm hab hcd hac
      have hlogint : (∫ u in (θ * α)..α, Int.fract u / u ^ 2) =
          Real.log α - Real.log (θ * α) :=
        fract_div_sq_integral_of_pos_le_one hθαpos hαpos hθαle1 hαle1
      have hlogeq : Real.log α - Real.log (θ * α) = Real.log (1 / θ) := by
        rw [Real.log_mul hθ.ne' hαpos.ne']
        rw [show (1 / θ : ℝ) = θ⁻¹ by ring]
        rw [Real.log_inv]
        ring
      rw [hcomm, hlogint, hlogeq]
      rw [intervalIntegral.integral_symm]
      ring
    rw [hleft, hexpand, hscaled]
    rw [← mul_sub]
    rw [hinterval]
    ring

set_option linter.flexible false in
/-- Quadratic scaling identity used in the proof of BBLS Proposition 22.

The identity appears explicitly in the proof on page 12 of
Báez-Duarte--Balazard--Landreau--Saias (arXiv:math/0306251), and was numerically checked
piecewise on rational test cases before formalization.  It is a direct change of variables
`u ↦ θ*u`. -/
theorem fract_sq_scaled_integral {θ x : ℝ} (hθ : 0 < θ) :
    (∫ u in (0 : ℝ)..x, (Int.fract (θ * u)) ^ 2 / u ^ 2) =
      θ * (∫ u in (0 : ℝ)..(θ * x), (Int.fract u) ^ 2 / u ^ 2) := by
  let f : ℝ → ℝ := fun u => (Int.fract u) ^ 2 / u ^ 2
  have hpoint : (fun u : ℝ => (Int.fract (θ * u)) ^ 2 / u ^ 2) =
      fun u : ℝ => θ ^ 2 * f (θ * u) := by
    funext u
    dsimp [f]
    by_cases hu : u = 0
    · simp [hu]
    · have hθne : θ ≠ 0 := hθ.ne'
      field_simp [hθne, hu, pow_two]
  rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  have hcomp :=
    intervalIntegral.integral_comp_mul_left (f := f) (a := (0 : ℝ)) (b := x) hθ.ne'
  simp [f, smul_eq_mul] at hcomp ⊢
  rw [hcomp]
  field_simp [hθ.ne']

/-- Interval integrability on `[0, x]` of a measurable function admitting a uniform bound
on `(0, x]`.  This is the `of_bound` pattern of `fract_mul_div_sq_intervalIntegrable`,
specialized to a left endpoint at zero: the value at `0` itself is irrelevant, so the bound
is only required on the half-open interval. -/
theorem intervalIntegrable_of_bound_on_Ioc {f : ℝ → ℝ} {x C : ℝ} (hx : 0 ≤ x)
    (hmeas : Measurable f) (hbound : ∀ u ∈ Set.Ioc (0 : ℝ) x, |f u| ≤ C) :
    IntervalIntegrable f MeasureTheory.volume (0 : ℝ) x := by
  rw [intervalIntegrable_iff]
  refine MeasureTheory.IntegrableOn.of_bound ?hsfin ?hmeas C ?hbound
  · rw [Real.volume_uIoc]
    exact ENNReal.ofReal_lt_top
  · exact hmeas.aestronglyMeasurable.restrict
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with u hu
    have huIoc : u ∈ Set.Ioc (0 : ℝ) x := by simpa [Set.uIoc_of_le hx] using hu
    simpa [Real.norm_eq_abs] using hbound u huIoc

set_option linter.flexible false in
/-- **Proposition 22, rational case** (`θ = k/h`, coprime, `h,k > 0`), from
    Báez-Duarte--Balazard--Landreau--Saias, arXiv:math/0306251.

    The paper's statement for real positive `x, θ` is:
    `∑_{1≤m≤x} B₁(mθ)/m + θ ∑_{1≤n≤θx} B₁(n/θ)/n`
    equals the displayed integral expression.  Here it is specialized to the rational
    parameter `θ = k/h`, the only case needed downstream for Vasyunin period reduction.
-/
theorem baezDuarte_prop22_rat {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) (x : ℝ) (hx : 0 < x) :
    let θ : ℝ := (k : ℝ) / (h : ℝ)
    (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ) / (m : ℝ)) +
        θ * (∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ) / (n : ℝ)) =
      (θ / 2) * (∫ t in (0 : ℝ)..x, (Int.fract t) ^ 2 / t ^ 2) +
        (1 / 2) * (∫ t in (0 : ℝ)..(θ * x), (Int.fract t) ^ 2 / t ^ 2) -
        (∫ t in (0 : ℝ)..x, (Int.fract t * Int.fract (θ * t)) / t ^ 2) +
        ((θ - 1) / 2) * Real.log (1 / θ) +
        ((θ - 1) / 2) * (∫ t in x..(θ * x), Int.fract t / t ^ 2) +
        (1 / (2 * θ * x)) * (Int.fract (θ * x) - θ * Int.fract x) ^ 2 +
        ((θ - 1) / (2 * θ * x)) * (Int.fract (θ * x) - θ * Int.fract x) := by
  intro θ
  have hθval : θ = (k : ℝ) / (h : ℝ) := rfl
  clear_value θ
  have hθpos : 0 < θ := by rw [hθval]; positivity
  have hθne : θ ≠ 0 := hθpos.ne'
  have hxne : x ≠ 0 := hx.ne'
  have hθx : 0 < θ * x := mul_pos hθpos hx
  -- `Int.fract y ≤ y` for nonnegative `y`.
  have hfle : ∀ y : ℝ, 0 ≤ y → Int.fract y ≤ y := by
    intro y hy
    have h0 : (0 : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hy
    linarith [Int.self_sub_fract y]
  -- Integrability of the step-sum integrands over `[0, y]` for any positive `y`.
  have hGenInt : ∀ (a : ℕ → ℝ) (y : ℝ), 0 < y →
      IntervalIntegrable (fun u : ℝ => (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2)
        MeasureTheory.volume (0 : ℝ) y := by
    intro a y hy
    by_cases hfloor0 : ⌊y⌋₊ = 0
    · have hlt1 : y < 1 := Nat.floor_eq_zero.mp hfloor0
      have hzero : Set.EqOn (fun u : ℝ => (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2)
          (fun _ : ℝ => (0 : ℝ)) (Set.uIoc (0 : ℝ) y) := by
        intro u hu
        have huIoc : u ∈ Set.Ioc (0 : ℝ) y := by simpa [Set.uIoc_of_le hy.le] using hu
        have hfl : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.mpr (lt_of_le_of_lt huIoc.2 hlt1)
        change (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2 = 0
        rw [hfl]
        simp
      exact (intervalIntegrable_congr hzero).2 intervalIntegrable_const
    · set N : ℕ := ⌊y⌋₊ with hNdef
      have hNpos : 0 < N := Nat.pos_of_ne_zero hfloor0
      have hprevInt : IntervalIntegrable
          (fun u : ℝ => (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, a m) / u ^ 2)
          MeasureTheory.volume (0 : ℝ) (N : ℝ) := by
        simpa using (IntervalIntegrable.trans_iterate
          (a := fun j : ℕ => (j : ℝ)) (n := N)
          (fun j _hj => stepPartialSum_div_sq_intervalIntegrable_nat_block a j))
      exact hprevInt.trans
        (stepPartialSum_div_sq_intervalIntegrable_floor_tail a hy hNdef.symm hNpos)
  have hSInt : IntervalIntegrable
      (fun u : ℝ => (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, bernoulliB1 ((m : ℝ) * θ)) / u ^ 2)
      MeasureTheory.volume (0 : ℝ) x :=
    hGenInt (fun m => bernoulliB1 ((m : ℝ) * θ)) x hx
  have hTInt0 : IntervalIntegrable
      (fun v : ℝ => (∑ n ∈ Finset.Icc 1 ⌊v⌋₊, bernoulliB1 ((n : ℝ) / θ)) / v ^ 2)
      MeasureTheory.volume (0 : ℝ) (θ * x) :=
    hGenInt (fun n => bernoulliB1 ((n : ℝ) / θ)) (θ * x) hθx
  -- Change of variables `v = θ*u`: integrability of the composed integrand on `[0, x]`.
  have hTcomp : IntervalIntegrable
      (fun u : ℝ => (∑ n ∈ Finset.Icc 1 ⌊θ * u⌋₊, bernoulliB1 ((n : ℝ) / θ)) / (θ * u) ^ 2)
      MeasureTheory.volume (0 : ℝ) x := by
    simpa [hθne, mul_div_cancel_left₀] using hTInt0.comp_mul_left (c := θ)
  have hTuInt : IntervalIntegrable
      (fun u : ℝ => (∑ n ∈ Finset.Icc 1 ⌊θ * u⌋₊, bernoulliB1 ((n : ℝ) / θ)) / u ^ 2)
      MeasureTheory.volume (0 : ℝ) x := by
    have heq : (fun u : ℝ =>
          (∑ n ∈ Finset.Icc 1 ⌊θ * u⌋₊, bernoulliB1 ((n : ℝ) / θ)) / u ^ 2) =
        fun u : ℝ =>
          θ ^ 2 * ((∑ n ∈ Finset.Icc 1 ⌊θ * u⌋₊, bernoulliB1 ((n : ℝ) / θ)) / (θ * u) ^ 2) := by
      funext u
      by_cases hu : u = 0
      · simp [hu]
      · field_simp [hθne, hu, pow_two]
    rw [heq]
    exact hTcomp.const_mul (θ ^ 2)
  -- The substitution identity turning the scaled companion integral into `[0, x]` form.
  have hTsub : (∫ u in (0 : ℝ)..x,
        (∑ n ∈ Finset.Icc 1 ⌊θ * u⌋₊, bernoulliB1 ((n : ℝ) / θ)) / u ^ 2) =
      θ * ∫ v in (0 : ℝ)..(θ * x),
        (∑ n ∈ Finset.Icc 1 ⌊v⌋₊, bernoulliB1 ((n : ℝ) / θ)) / v ^ 2 := by
    let f : ℝ → ℝ := fun v => (∑ n ∈ Finset.Icc 1 ⌊v⌋₊, bernoulliB1 ((n : ℝ) / θ)) / v ^ 2
    have hpoint : (fun u : ℝ =>
          (∑ n ∈ Finset.Icc 1 ⌊θ * u⌋₊, bernoulliB1 ((n : ℝ) / θ)) / u ^ 2) =
        fun u : ℝ => θ ^ 2 * f (θ * u) := by
      funext u
      dsimp [f]
      by_cases hu : u = 0
      · simp [hu]
      · field_simp [hθne, hu, pow_two]
    rw [hpoint]
    rw [intervalIntegral.integral_const_mul]
    have hcomp :=
      intervalIntegral.integral_comp_mul_left (f := f) (a := (0 : ℝ)) (b := x) hθne
    simp [f, smul_eq_mul] at hcomp ⊢
    rw [hcomp]
    field_simp [hθne]
  -- Step 1: the two Abel/Stieltjes identities.
  have hA : (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ) / (m : ℝ)) =
      (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ)) / x +
        ∫ u in (0 : ℝ)..x, (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, bernoulliB1 ((m : ℝ) * θ)) / u ^ 2 :=
    stepFunction_abel_stieltjes_identity (fun m : ℕ => bernoulliB1 ((m : ℝ) * θ)) hx
  have hB : (∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ) / (n : ℝ)) =
      (∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ)) / (θ * x) +
        ∫ u in (0 : ℝ)..(θ * x),
          (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, bernoulliB1 ((n : ℝ) / θ)) / u ^ 2 :=
    bernoulliB1_scaled_companion_abel_stieltjes_identity hθpos hx
  -- Step 2: combine the two `[0, x]` integrals into one.
  have hcombine : (∫ u in (0 : ℝ)..x,
        ((∑ m ∈ Finset.Icc 1 ⌊u⌋₊, bernoulliB1 ((m : ℝ) * θ)) / u ^ 2 +
          (∑ n ∈ Finset.Icc 1 ⌊θ * u⌋₊, bernoulliB1 ((n : ℝ) / θ)) / u ^ 2)) =
      (∫ u in (0 : ℝ)..x, (∑ m ∈ Finset.Icc 1 ⌊u⌋₊, bernoulliB1 ((m : ℝ) * θ)) / u ^ 2) +
        ∫ u in (0 : ℝ)..x, (∑ n ∈ Finset.Icc 1 ⌊θ * u⌋₊, bernoulliB1 ((n : ℝ) / θ)) / u ^ 2 :=
    intervalIntegral.integral_add hSInt hTuInt
  -- Step 3: rewrite the combined integrand pointwise via Proposition 21.
  have hcongr : (∫ u in (0 : ℝ)..x,
        ((∑ m ∈ Finset.Icc 1 ⌊u⌋₊, bernoulliB1 ((m : ℝ) * θ)) / u ^ 2 +
          (∑ n ∈ Finset.Icc 1 ⌊θ * u⌋₊, bernoulliB1 ((n : ℝ) / θ)) / u ^ 2)) =
      ∫ u in (0 : ℝ)..x,
        ((1 / (2 * θ)) * (Int.fract (θ * u) - θ * Int.fract u) ^ 2 +
          ((θ - 1) / (2 * θ)) * (Int.fract (θ * u) - θ * Int.fract u)) / u ^ 2 := by
    apply intervalIntegral.integral_congr
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) x := by simpa [Set.uIcc_of_le hx.le] using hu
    dsimp only
    by_cases hu0 : u = 0
    · simp [hu0]
    · have hupos : 0 < u := lt_of_le_of_ne huIcc.1 (Ne.symm hu0)
      have hprop21 := baezDuarte_prop21_rat_of_prop12 hh hk hcop u hupos
      rw [← hθval] at hprop21
      linear_combination (1 / u ^ 2) * hprop21
  -- Step 4: integrability of the four expanded quadratic pieces on `[0, x]`.
  have hPsq : ∀ c : ℝ, 0 < c → IntervalIntegrable
      (fun u : ℝ => (Int.fract (c * u)) ^ 2 / u ^ 2) MeasureTheory.volume (0 : ℝ) x := by
    intro c hc
    refine intervalIntegrable_of_bound_on_Ioc hx.le
      (((measurable_id.const_mul c).fract.pow_const 2).div (measurable_id.pow_const 2))
      (C := c ^ 2) ?_
    intro u hu
    have hupos : 0 < u := hu.1
    have h1 := Int.fract_nonneg (c * u)
    have h2 := hfle (c * u) (by positivity)
    have hle : (Int.fract (c * u)) ^ 2 / u ^ 2 ≤ c ^ 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < u ^ 2)]
      nlinarith [mul_self_le_mul_self h1 h2]
    have hnn : 0 ≤ (Int.fract (c * u)) ^ 2 / u ^ 2 := by positivity
    rwa [abs_of_nonneg hnn]
  have hP1 : IntervalIntegrable (fun u : ℝ => (Int.fract (θ * u)) ^ 2 / u ^ 2)
      MeasureTheory.volume (0 : ℝ) x := hPsq θ hθpos
  have hP3 : IntervalIntegrable (fun u : ℝ => (Int.fract u) ^ 2 / u ^ 2)
      MeasureTheory.volume (0 : ℝ) x := by
    simpa using hPsq 1 one_pos
  have hP2 : IntervalIntegrable
      (fun u : ℝ => Int.fract u * Int.fract (θ * u) / u ^ 2)
      MeasureTheory.volume (0 : ℝ) x := by
    refine intervalIntegrable_of_bound_on_Ioc hx.le
      ((measurable_fract.mul (measurable_id.const_mul θ).fract).div
        (measurable_id.pow_const 2))
      (C := θ) ?_
    intro u hu
    have hupos : 0 < u := hu.1
    have h1 := hfle u hupos.le
    have h2 := hfle (θ * u) (by positivity)
    have h3 := Int.fract_nonneg (θ * u)
    have h4 := Int.fract_nonneg u
    have hprod : Int.fract u * Int.fract (θ * u) ≤ u * (θ * u) :=
      mul_le_mul h1 h2 h3 hupos.le
    have hle : Int.fract u * Int.fract (θ * u) / u ^ 2 ≤ θ := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < u ^ 2)]
      nlinarith
    have hnn : 0 ≤ Int.fract u * Int.fract (θ * u) / u ^ 2 := by positivity
    rwa [abs_of_nonneg hnn]
  have hP4 : IntervalIntegrable
      (fun u : ℝ => (Int.fract (θ * u) - θ * Int.fract u) / u ^ 2)
      MeasureTheory.volume (0 : ℝ) x := by
    set α : ℝ := min 1 (1 / θ) with hα
    have hαpos : 0 < α := lt_min one_pos (one_div_pos.mpr hθpos)
    refine intervalIntegrable_of_bound_on_Ioc hx.le
      (((measurable_id.const_mul θ).fract.sub (measurable_fract.const_mul θ)).div
        (measurable_id.pow_const 2))
      (C := (1 + θ) / α ^ 2) ?_
    intro u hu
    by_cases huα : u < α
    · rw [prop16_fract_diff_eq_zero_of_lt_alpha hθpos hα hu.1.le huα, zero_div, abs_zero]
      positivity
    · have hαu : α ≤ u := le_of_not_gt huα
      have h1 := Int.fract_nonneg (θ * u)
      have h2 := (Int.fract_lt_one (θ * u)).le
      have h3 := Int.fract_nonneg u
      have h4 := (Int.fract_lt_one u).le
      have h5 : 0 ≤ θ * Int.fract u := mul_nonneg hθpos.le h3
      have h6 : θ * Int.fract u ≤ θ := by
        have := mul_le_mul_of_nonneg_left h4 hθpos.le
        simpa using this
      have hnum : |Int.fract (θ * u) - θ * Int.fract u| ≤ 1 + θ := by
        rw [abs_le]
        constructor <;> linarith
      have hu2 : α ^ 2 ≤ u ^ 2 := by nlinarith [hαpos.le]
      rw [abs_div, abs_of_nonneg (sq_nonneg u)]
      calc |Int.fract (θ * u) - θ * Int.fract u| / u ^ 2
          ≤ (1 + θ) / u ^ 2 := by gcongr
        _ ≤ (1 + θ) / α ^ 2 := by gcongr
  have hP1c : IntervalIntegrable
      (fun u : ℝ => (1 / (2 * θ)) * ((Int.fract (θ * u)) ^ 2 / u ^ 2))
      MeasureTheory.volume (0 : ℝ) x := hP1.const_mul _
  have hP3c : IntervalIntegrable
      (fun u : ℝ => (θ / 2) * ((Int.fract u) ^ 2 / u ^ 2))
      MeasureTheory.volume (0 : ℝ) x := hP3.const_mul _
  have hP4c : IntervalIntegrable
      (fun u : ℝ => ((θ - 1) / (2 * θ)) * ((Int.fract (θ * u) - θ * Int.fract u) / u ^ 2))
      MeasureTheory.volume (0 : ℝ) x := hP4.const_mul _
  have hab : IntervalIntegrable
      (fun u : ℝ => (1 / (2 * θ)) * ((Int.fract (θ * u)) ^ 2 / u ^ 2) -
        Int.fract u * Int.fract (θ * u) / u ^ 2)
      MeasureTheory.volume (0 : ℝ) x := hP1c.sub hP2
  have habc : IntervalIntegrable
      (fun u : ℝ => (1 / (2 * θ)) * ((Int.fract (θ * u)) ^ 2 / u ^ 2) -
        Int.fract u * Int.fract (θ * u) / u ^ 2 + (θ / 2) * ((Int.fract u) ^ 2 / u ^ 2))
      MeasureTheory.volume (0 : ℝ) x := hab.add hP3c
  -- Step 5: split the Proposition 21 integral into its four pieces.
  have hsplit : (∫ u in (0 : ℝ)..x,
        ((1 / (2 * θ)) * (Int.fract (θ * u) - θ * Int.fract u) ^ 2 +
          ((θ - 1) / (2 * θ)) * (Int.fract (θ * u) - θ * Int.fract u)) / u ^ 2) =
      (1 / (2 * θ)) * (∫ u in (0 : ℝ)..x, (Int.fract (θ * u)) ^ 2 / u ^ 2) -
        (∫ u in (0 : ℝ)..x, Int.fract u * Int.fract (θ * u) / u ^ 2) +
        (θ / 2) * (∫ u in (0 : ℝ)..x, (Int.fract u) ^ 2 / u ^ 2) +
        ((θ - 1) / (2 * θ)) *
          (∫ u in (0 : ℝ)..x, (Int.fract (θ * u) - θ * Int.fract u) / u ^ 2) := by
    have hfun : (fun u : ℝ =>
          ((1 / (2 * θ)) * (Int.fract (θ * u) - θ * Int.fract u) ^ 2 +
            ((θ - 1) / (2 * θ)) * (Int.fract (θ * u) - θ * Int.fract u)) / u ^ 2) =
        fun u : ℝ =>
          (1 / (2 * θ)) * ((Int.fract (θ * u)) ^ 2 / u ^ 2) -
            Int.fract u * Int.fract (θ * u) / u ^ 2 +
            (θ / 2) * ((Int.fract u) ^ 2 / u ^ 2) +
            ((θ - 1) / (2 * θ)) * ((Int.fract (θ * u) - θ * Int.fract u) / u ^ 2) := by
      funext u
      by_cases hu : u = 0
      · simp [hu]
      · field_simp
        ring
    rw [hfun, intervalIntegral.integral_add habc hP4c,
      intervalIntegral.integral_add hab hP3c, intervalIntegral.integral_sub hP1c hP2]
    simp only [intervalIntegral.integral_const_mul]
  -- Step 6: the two scaled-integral evaluations.
  have hI1eq := fract_sq_scaled_integral (θ := θ) (x := x) hθpos
  have hI4eq := baezDuarte_prop16_frullani hθpos hx
  -- Step 7: the boundary term, Proposition 21 evaluated at `x` itself.
  have hbdry : (∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ)) +
      (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ)) =
      (1 / (2 * θ)) * (Int.fract (θ * x) - θ * Int.fract x) ^ 2 +
        ((θ - 1) / (2 * θ)) * (Int.fract (θ * x) - θ * Int.fract x) := by
    have h21 := baezDuarte_prop21_rat_of_prop12 hh hk hcop x hx
    rw [← hθval] at h21
    exact h21
  -- Final assembly: everything is now linear algebra over the collected identities.
  -- The four weighted sums are made opaque first, so that `field_simp` cannot
  -- renormalize divisions inside their summands inconsistently between occurrences.
  set A1 : ℝ := ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ) / (m : ℝ) with hA1def
  set A2 : ℝ := ∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ) / (n : ℝ) with hA2def
  set SB1 : ℝ := ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ) with hSB1def
  set SB2 : ℝ := ∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ) with hSB2def
  clear_value A1 A2 SB1 SB2
  linear_combination (norm := (field_simp; ring))
    hA + θ * hB - hTsub - hcombine + hcongr + hsplit + (1 / (2 * θ)) * hI1eq +
      ((θ - 1) / (2 * θ)) * hI4eq + (1 / x) * hbdry

end RH.Criteria.NymanBeurling.VasyuninGram
