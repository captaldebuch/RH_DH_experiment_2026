# Hardy Space & Inner-Outer Factorization Library

This library formalizes the **Hardy Space $H^2$ infrastructure** and **Inner-Outer Factorization** on the unit disc $\mathbb{D}$ and right half-plane $\{\Re z > 1/2\}$.

## Files

- **`BlaschkeFactor.lean`**: Single Blaschke factor $b_a(z) = \frac{z-a}{1-\bar{a}z}$ definitions and isometric boundary properties.
- **`BlaschkeProduct.lean`**: Infinite Blaschke product $B(z) = \prod \frac{\bar{a_n}}{|a_n|} \frac{a_n - z}{1 - \bar{a_n}z}$.
- **`BlaschkeZeros.lean`**: Blaschke zero condition $\sum (1 - |a_n|) < \infty$ derived from Jensen's formula (`isBlaschkeFamily_zeroFamily`).
- **`HardyDisc.lean`**: Hardy space $H^2(\mathbb{D})$ definition, norm, and Cauchy reproducing kernels.
- **`InnerOuterDisc.lean`**: Inner-outer factorization on the unit disc $\mathbb{D}$ (`hardyDisc_inner_outer`).
- **`InnerOuterHalfPlane.lean`**: Inner-outer factorization on the half-plane $\{\Re z > 1/2\}$ (`inner_outer_factorization`), exact uniqueness up to zero-free units (`inner_outer_unique_up_to_unit`), and machine-verified counterexample disproof of literal uniqueness (`inner_outer_factorization_not_unique`).
