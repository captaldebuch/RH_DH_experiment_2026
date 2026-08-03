import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperContour
import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperSpectral

/-!
# Exact bridge and finite contour facts for the BCF logarithmic taper

The finite BCF Dirichlet polynomial is entire, hence its rectangular contour
integral vanishes.  Independently, the Mellin--Plancherel bridge identifies
the finite BCF energy and the critical-line spectral energy *exactly*.

This module intentionally contains no residue/horizontal/vertical remainder
package.  Such terms cannot mediate between `energy` and `spectralEnergy`:
once Mellin--Plancherel is available, those quantities are equal.  A contour
argument involving `riemannZeta` or `riemannZeta'/riemannZeta` is therefore a
possible future analytic tool for the RH-strength spectral-vanishing problem,
not an additional comparison layer here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperPairedContour

open RH.Criteria.NymanBeurling.BCFLogTaper
open RH.Criteria.NymanBeurling.BCFLogTaperContour
open RH.Criteria.NymanBeurling.BCFLogTaperMellin
open RH.Criteria.NymanBeurling.BCFLogTaperSpectral

/-- The finite BCF Dirichlet polynomial has no residue contribution on a
rectangle: it is entire.  This is the contour fact available without any
zeta-function input. -/
theorem finite_dirichletPolynomial_rectangle_identity (N : ℕ) (z w : ℂ) :
    (∫ x : ℝ in z.re..w.re, dirichletPolynomial N (x + z.im * Complex.I)) -
        (∫ x : ℝ in z.re..w.re, dirichletPolynomial N (x + w.im * Complex.I)) +
        Complex.I • (∫ y : ℝ in z.im..w.im,
          dirichletPolynomial N (w.re + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in z.im..w.im,
          dirichletPolynomial N (z.re + y * Complex.I)) = 0 :=
  dirichletPolynomial_boundary_rect_eq_zero N z w

/-- The proved Mellin/Fourier bridge supplies the complete finite-to-spectral
comparison; there is no contour remainder. -/
theorem energy_eq_spectralEnergy_exact (N : ℕ) :
    energy N = spectralEnergy N :=
  energy_eq_spectralEnergy N

/-- Equivalently, the named finite/spectral comparison remainder vanishes
identically. -/
theorem spectralRemainder_eq_zero_exact (N : ℕ) :
    spectralRemainder N = 0 :=
  spectralRemainder_eq_zero N

end RH.Criteria.NymanBeurling.BCFLogTaperPairedContour
