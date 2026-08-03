import RiemannHypothesis.Criteria.NymanBeurling.H15FractionalTail

/-!
# H15 Mellin/Dirichlet-polynomial interface

This file records the first exact piece of the Mellin-energy route for the
explicit cutoff Möbius vector.  The finite Dirichlet polynomial is defined
with the same Cesàro cutoff as `cutoffMobiusCoeff`.  Its value at `s = 1` is
identified with the already-controlled cutoff Möbius sum.  The genuinely
analytic Mellin/Plancherel identity is not asserted here: the exact finite
identity below isolates the part that can be discharged without new harmonic
analysis.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.MobiusSummatory

/-! ## The explicit cutoff Möbius Dirichlet polynomial -/

/-- The Dirichlet polynomial suggested by the cutoff Möbius vector.  The
coefficient is written as `μ(h) * cutoffWeight`; this is the negative of
`cutoffMobiusCoeff`, matching the usual inverse-zeta normalization. -/
noncomputable def cutoffMobiusDirichletPolynomial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 N,
    (((ArithmeticFunction.moebius h : ℤ) : ℝ) * cutoffWeight N h : ℂ) *
      ((h : ℂ) ^ (-s))

/-- At the real point `s = 1`, the polynomial is exactly the cutoff Möbius
sum appearing in the H14 Dirichlet estimates. -/
theorem cutoffMobiusDirichletPolynomial_one_eq_cutoffMobiusOverKSum
    (N : ℕ) :
    cutoffMobiusDirichletPolynomial N (1 : ℂ) =
      (cutoffMobiusOverKSum N : ℂ) := by
  unfold cutoffMobiusDirichletPolynomial cutoffMobiusOverKSum
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hhpos : 0 < h :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hh).1
  have hhne : h ≠ 0 := Nat.ne_of_gt hhpos
  simp only [Complex.cpow_neg_one, Complex.ofReal_natCast,
    Complex.ofReal_mul, Complex.ofReal_div]
  unfold cutoffWeight
  push_cast
  field_simp [hhne]

/-- The preceding identity transports the H14 decay estimate to the value of
the explicit polynomial at `s = 1`. -/
theorem cutoffMobiusDirichletPolynomial_one_tendsto_zero_of_decay
    (H : ClassicalMertensDecay) :
  Filter.Tendsto (fun N : ℕ => cutoffMobiusDirichletPolynomial N (1 : ℂ))
      Filter.atTop (nhds (0 : ℂ)) := by
  let api := ClassicalMertensAPI.ofDecayOnly H
  have hconv :=
    (Complex.continuous_ofReal.tendsto 0).comp
      api.cutoff_overK_tendsto_zero
  simpa only [cutoffMobiusDirichletPolynomial_one_eq_cutoffMobiusOverKSum] using hconv

end RH.Criteria.NymanBeurling.QuadraticInteraction
