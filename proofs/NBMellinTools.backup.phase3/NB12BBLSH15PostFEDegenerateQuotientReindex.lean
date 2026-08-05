/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.NB12BBLSH15PostFEActualSupportDegenerateSector

/-!
# NB12zzzaU: quotient reindexing of the density-degenerate sector

On the actual H15 support, the missing modulus `p` and the two ordered-pair
moduli `q,q'` all lie in the same dyadic block `[Q,2Q)`.  In the sector where
the external-shell density degenerates, `p ∣ q*q'`, so the canonical quotient

`k = q*q' / p`

reindexes the divisibility condition exactly as `q*q' = p*k`.

This file proves that `k` is itself of dyadic scale: under `0 < Q`, it satisfies

`Q < 2*k` and `k < 4*Q`.

Thus quotient reindexing is exact but does not by itself remove a full
dyadic variable.  Any saving in this sector must use the signed H15
coefficients, not only the support condition `p ∣ q*q'`.
-/

namespace NBMellinTools.NB12

/-! ## Actual support lies in the original modulus block -/

theorem h15PostFEResidueSupport_modulus_mem_supportedBlock
    {n g U Q : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ h15PostFEResidueSupport n g U Q) :
    z.2 ∈ h15BettinChandeeSupportedNatBlock
      (NB8.logTaperLength n) g Q := by
  classical
  rw [h15PostFEResidueSupport, Finset.mem_image] at hz
  rcases hz with ⟨k, hk, rfl⟩
  simpa [h15PostFEResidueKey] using
    (h15PostFECollectedUnionKey_modulus_mem hk)

theorem h15PostFEResidueModulusSupport_mem_supportedBlock
    {n g U Q p : ℕ}
    (hp : p ∈ h15PostFEResidueModulusSupport n g U Q) :
    p ∈ h15BettinChandeeSupportedNatBlock
      (NB8.logTaperLength n) g Q := by
  classical
  rw [h15PostFEResidueModulusSupport, Finset.mem_image] at hp
  rcases hp with ⟨z, hz, rfl⟩
  exact h15PostFEResidueSupport_modulus_mem_supportedBlock hz

theorem h15PostFEActualMissingModulus_mem_supportedBlock
    {n g U Q : ℕ} {i : H15PostFEMissingAtomIndex}
    (hi : i ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q)) :
    i.1 ∈ h15BettinChandeeSupportedNatBlock
      (NB8.logTaperLength n) g Q := by
  exact h15PostFEResidueModulusSupport_mem_supportedBlock
    (Finset.mem_sigma.mp hi).1

theorem h15PostFEActualOrientedPairModuli_mem_supportedBlock
    {n g U Q : ℕ} {x : H15PostFEOrientedPairAtomIndex}
    (hx : x ∈ h15PostFEActualOrientedPairSupport n g U Q) :
    x.1.1.2 ∈ h15BettinChandeeSupportedNatBlock
        (NB8.logTaperLength n) g Q ∧
      x.1.2.2 ∈ h15BettinChandeeSupportedNatBlock
        (NB8.logTaperLength n) g Q := by
  have hx' := Finset.mem_product.mp hx
  have hraw := h15PostFEReducedOrderedPairResidueSupport_subset
    n g U Q hx'.1
  have hactual := h15PostFEOrderedPairResidueSupport_subset_actual hraw
  exact ⟨h15PostFEResidueSupport_modulus_mem_supportedBlock hactual.1,
    h15PostFEResidueSupport_modulus_mem_supportedBlock hactual.2⟩

/-! ## Canonical quotient and its exact identity -/

def h15PostFEDegenerateQuotient (p q q' : ℕ) : ℕ :=
  q * q' / p

theorem h15PostFEDegenerateQuotient_spec
    {p q q' : ℕ} (hdiv : p ∣ q * q') :
    q * q' = p * h15PostFEDegenerateQuotient p q q' := by
  unfold h15PostFEDegenerateQuotient
  exact (Nat.mul_div_cancel' hdiv).symm

/-! ## The quotient remains at dyadic scale -/

theorem h15PostFEDegenerateQuotient_pos
    {p q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hdiv : p ∣ q * q') :
    0 < h15PostFEDegenerateQuotient p q q' := by
  unfold h15PostFEDegenerateQuotient
  have hp : 0 < p := Nat.pos_of_dvd_of_pos hdiv (Nat.mul_pos hq hq')
  exact Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hq hq') hdiv) hp

/-- Once the positive quotient is introduced, the missing modulus is
recovered uniquely from `(q,q',k)`. -/
theorem h15PostFEDegenerateMissingModulus_eq_product_div_quotient
    {p q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hdiv : p ∣ q * q') :
    p = q * q' / h15PostFEDegenerateQuotient p q q' := by
  rw [h15PostFEDegenerateQuotient_spec hdiv]
  simpa [mul_comm] using (Nat.mul_div_right p
    (h15PostFEDegenerateQuotient_pos hq hq' hdiv)).symm

theorem h15PostFEDegenerateQuotient_lt_four_mul
    {Q p q q' : ℕ} (hQ : 0 < Q)
    (hpLower : Q ≤ p)
    (hqUpper : q < 2 * Q) (hq'Upper : q' < 2 * Q)
    (hdiv : p ∣ q * q') :
    h15PostFEDegenerateQuotient p q q' < 4 * Q := by
  let k := h15PostFEDegenerateQuotient p q q'
  have hspec : q * q' = p * k := h15PostFEDegenerateQuotient_spec hdiv
  have hQk_le : Q * k ≤ p * k := Nat.mul_le_mul_right k hpLower
  have htwoQPos : 0 < 2 * Q := by omega
  have hprod_lt : q * q' < (2 * Q) * (2 * Q) := by
    calc
      q * q' ≤ (2 * Q) * q' :=
        Nat.mul_le_mul_right q' (Nat.le_of_lt hqUpper)
      _ < (2 * Q) * (2 * Q) :=
        (Nat.mul_lt_mul_left htwoQPos).2 hq'Upper
  have hQk_lt : Q * k < Q * (4 * Q) := by
    calc
      Q * k ≤ p * k := hQk_le
      _ = q * q' := hspec.symm
      _ < (2 * Q) * (2 * Q) := hprod_lt
      _ = Q * (4 * Q) := by ring
  exact (Nat.mul_lt_mul_left hQ).mp hQk_lt

theorem h15PostFEDegenerateQuotient_half_scale
    {Q p q q' : ℕ} (hQ : 0 < Q)
    (hpUpper : p < 2 * Q)
    (hqLower : Q ≤ q) (hq'Lower : Q ≤ q')
    (hdiv : p ∣ q * q') :
    Q < 2 * h15PostFEDegenerateQuotient p q q' := by
  let k := h15PostFEDegenerateQuotient p q q'
  have hspec : q * q' = p * k := h15PostFEDegenerateQuotient_spec hdiv
  have hkpos : 0 < k := by
    apply h15PostFEDegenerateQuotient_pos
    · exact hQ.trans_le hqLower
    · exact hQ.trans_le hq'Lower
    · exact hdiv
  have hQQ_le : Q * Q ≤ q * q' :=
    Nat.mul_le_mul hqLower hq'Lower
  have hpk_lt : p * k < (2 * Q) * k :=
    (Nat.mul_lt_mul_right hkpos).2 hpUpper
  have hQQ_lt : Q * Q < Q * (2 * k) := by
    calc
      Q * Q ≤ q * q' := hQQ_le
      _ = p * k := hspec
      _ < (2 * Q) * k := hpk_lt
      _ = Q * (2 * k) := by ring
  exact (Nat.mul_lt_mul_left hQ).mp hQQ_lt

/-! ## Actual H15 degenerate-sector scale certificate -/

theorem h15PostFEActualDegenerateQuotient_dyadicScale
    {n g U Q : ℕ} {i : H15PostFEMissingAtomIndex}
    {x : H15PostFEOrientedPairAtomIndex}
    (hQ : 0 < Q)
    (hi : i ∈ h15PostFEJointMissingAtomSupport
      (h15PostFEResidueModulusSupport n g U Q)
      (h15PostFEReducedMissingResidues n g U Q))
    (hx : x ∈ h15PostFEActualOrientedPairSupport n g U Q)
    (hdeg : h15PostFEMissingPairExternalDensityDegenerate i x) :
    Q < 2 * h15PostFEDegenerateQuotient
        i.1 x.1.1.2 x.1.2.2 ∧
      h15PostFEDegenerateQuotient i.1 x.1.1.2 x.1.2.2 < 4 * Q := by
  have hp := mem_h15BettinChandeeSupportedNatBlock.mp
    (h15PostFEActualMissingModulus_mem_supportedBlock hi)
  have hpair := h15PostFEActualOrientedPairModuli_mem_supportedBlock hx
  have hq := mem_h15BettinChandeeSupportedNatBlock.mp hpair.1
  have hq' := mem_h15BettinChandeeSupportedNatBlock.mp hpair.2
  exact ⟨h15PostFEDegenerateQuotient_half_scale hQ hp.2.1 hq.1 hq'.1 hdeg,
    h15PostFEDegenerateQuotient_lt_four_mul hQ hp.1
      hq.2.1 hq'.2.1 hdeg⟩

end NBMellinTools.NB12
