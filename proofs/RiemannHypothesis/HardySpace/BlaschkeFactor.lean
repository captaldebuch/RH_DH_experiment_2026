import Mathlib

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RiemannHypothesis.HardySpace

/-- Single Blaschke factor for a point a ∈ 𝔻: b_a(z) = (z - a) / (1 - Complex.conj a * z). -/
def blaschkeFactor (a z : ℂ) : ℂ :=
  (z - a) / (1 - Complex.conj a * z)

/-- A Blaschke factor has modulus 1 on the unit circle |z| = 1. -/
theorem norm_blaschkeFactor_eq_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    ‖blaschkeFactor a z‖ = 1 := by
  have hza : ‖z - a‖ ≠ 0 := by
    intro h0
    have : z = a := sub_eq_zero.mp h0
    rw [this] at hz
    linarith
  unfold blaschkeFactor
  rw [norm_div]
  have hden : ‖1 - Complex.conj a * z‖ = ‖z - a‖ := by
    calc ‖1 - Complex.conj a * z‖
      _ = ‖z * (Complex.conj z - Complex.conj a)‖ := by
        congr 1
        calc 1 - Complex.conj a * z
          _ = z * Complex.conj z - Complex.conj a * z := by rw [mul_conj, hz, normSq_one, Nat.cast_one]
          _ = z * (Complex.conj z - Complex.conj a) := by ring
      _ = ‖z‖ * ‖Complex.conj (z - a)‖ := by rw [norm_mul, map_sub]
      _ = 1 * ‖z - a‖ := by rw [hz, norm_conj]
      _ = ‖z - a‖ := by ring
  rw [hden, div_self hza]

end RiemannHypothesis.HardySpace
