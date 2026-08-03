import RiemannHypothesis.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDescent

/-!
# Route C: source-normalized three-term descent

The parameter-dependent Bettin--Conrey period relation is homogeneous.  In
the source reciprocity formula, the correction is
`z * k^z * ζ(1-z)/(πh)`; its leading parameter cancels the zeta pole.  Hence
no additional polar subtraction belongs on the period side, and its central
three-term descent remains homogeneous.

This file records the rational three-term relation as a proposition-valued
paper interface and proves the passage from that relation to the central
recurrence.  Thus the recurrence field required by
`RouteCUnitIntervalPeriodCoefficientData` no longer has to be supplied as an
independent analytic hypothesis.

For audit purposes the file also evaluates the logarithmic divided
difference that would arise from the *unscaled* meromorphic quotient.  That
limit is mathematically correct but is not inserted into the source-normalized
reciprocity relation.

No uniform outer-cutoff estimate is asserted here.
-/

namespace RH.Criteria.NymanBeurling.BCFLogTaperRouteCThreeTermDefect

open Complex Filter Topology
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCCentralReciprocity
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCAdaptiveTransfer
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodFinitePart
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDiagonal
open RH.Criteria.NymanBeurling.BCFLogTaperRouteCPeriodDescent

/-- The multiplier occurring in the rational three-term relation. -/
noncomputable def routeCPeriodDescentFactor
    (z : ℂ) (h k : ℕ) : ℂ :=
  ((k : ℂ) / (h : ℂ)) ^ (1 + z)

/-- The divided difference associated with the unscaled meromorphic
quotient.  It is not a term in the source-normalized period recurrence. -/
noncomputable def routeCPeriodDescentAnalyticDefect
    (z : ℂ) (h k : ℕ) : ℂ :=
  (routeCPeriodDescentFactor z h k - (k : ℂ) / (h : ℂ)) /
    ((Real.pi : ℂ) * ((h - k : ℕ) : ℂ) * z)

/-- Rational specialization of the Bettin--Conrey three-term relation.
This is a cited analytic interface; no inhabitant is declared here. -/
structure AuliBettinConreyRationalThreeTermPackage
    (H : AuliBettinConreyRationalReciprocityPackage) where
  threeTerm : ∀ (z : ℂ) (h k : ℕ), z ≠ 0 → 0 < k → k < h →
    H.periodFunction z ((((h - k : ℕ) : ℝ) / (k : ℝ) : ℝ) : ℂ) -
        H.periodFunction z (((h : ℝ) / (k : ℝ) : ℝ) : ℂ) =
      routeCPeriodDescentFactor z h k *
        H.periodFunction z ((((h - k : ℕ) : ℝ) / (h : ℝ) : ℝ) : ℂ)

/-- The divided difference forced by the pole subtraction converges to the
negative of the central logarithmic descent defect. -/
theorem tendsto_routeCPeriodDescentAnalyticDefect_zero
    (h k : ℕ) (hk : 0 < k) (hkh : k < h) :
    Tendsto (fun z : ℂ => routeCPeriodDescentAnalyticDefect z h k)
      (𝓝[≠] 0) (𝓝 (-routeCCentralPeriodDescentDefect h k)) := by
  let r : ℝ := (k : ℝ) / (h : ℝ)
  have hh : 0 < h := Nat.zero_lt_of_lt hkh
  have hr : 0 < r := div_pos (by exact_mod_cast hk) (by exact_mod_cast hh)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hderiv : HasDerivAt (fun z : ℂ => (r : ℂ) ^ (1 + z))
      (Complex.log (r : ℂ) * (r : ℂ)) 0 := by
    have hexp : HasDerivAt (fun z : ℂ => 1 + z) 1 0 := by
      simpa using (hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).add
        (hasDerivAt_id (x := (0 : ℂ)))
    convert hexp.const_cpow (c := (r : ℂ)) (Or.inl hrC) using 1 <;>
      simp <;> ring
  have hslope : Tendsto
      (fun z : ℂ => ((r : ℂ) ^ (1 + z) - (r : ℂ)) / z)
      (𝓝[≠] 0) (𝓝 (Complex.log (r : ℂ) * (r : ℂ))) := by
    have hs := hderiv.tendsto_slope
    convert hs using 1
    funext z
    rw [slope_def_field]
    simp
  have hquot := hslope.div_const
    ((Real.pi : ℂ) * ((h - k : ℕ) : ℂ))
  have hlog : Complex.log (r : ℂ) = (Real.log r : ℂ) :=
    (Complex.ofReal_log hr.le).symm
  have hfun :
      (fun z : ℂ => routeCPeriodDescentAnalyticDefect z h k) =
        (fun z : ℂ =>
          ((r : ℂ) ^ (1 + z) - (r : ℂ)) / z /
            ((Real.pi : ℂ) * ((h - k : ℕ) : ℂ))) := by
    funext z
    unfold routeCPeriodDescentAnalyticDefect routeCPeriodDescentFactor
    dsimp [r]
    push_cast
    ring
  rw [hfun]
  convert hquot using 1
  rw [hlog]
  have hratio : (h : ℝ) / (k : ℝ) = r⁻¹ := by
    dsimp [r]
    field_simp
  have hlogratio : Real.log ((h : ℝ) / (k : ℝ)) = -Real.log r := by
    rw [hratio, Real.log_inv]
  have hre :
      Real.log r * r / (Real.pi * ((h - k : ℕ) : ℝ)) =
        -((k : ℝ) * Real.log ((h : ℝ) / (k : ℝ)) /
          (Real.pi * ((h - k : ℕ) : ℝ) * (h : ℝ))) := by
    rw [hlogratio]
    dsimp [r]
    ring
  congr 1
  unfold routeCCentralPeriodDescentDefect
  push_cast
  exact_mod_cast hre.symm

/-- Applying the parameter-dependent three-term relation to the
source-normalized period side gives the homogeneous descent exactly. -/
theorem auliBettinConreyRenormalizedPeriodSide_descent
    (H : AuliBettinConreyRationalReciprocityPackage)
    (P : AuliBettinConreyRationalThreeTermPackage H)
    (z : ℂ) (h k : ℕ) (hz : z ≠ 0) (hk : 0 < k) (hkh : k < h) :
    auliBettinConreyRenormalizedPeriodSide H z h k =
      auliBettinConreyRenormalizedPeriodSide H z (h - k) k -
        routeCPeriodDescentFactor z h k *
          auliBettinConreyRenormalizedPeriodSide H z (h - k) h := by
  have hperiod := P.threeTerm z h k hz hk hkh
  have hperiod' :
      H.periodFunction z (((h : ℝ) / (k : ℝ) : ℝ) : ℂ) =
        H.periodFunction z ((((h - k : ℕ) : ℝ) / (k : ℝ) : ℝ) : ℂ) -
          routeCPeriodDescentFactor z h k *
            H.periodFunction z
              ((((h - k : ℕ) : ℝ) / (h : ℝ) : ℝ) : ℂ) := by
    linear_combination -hperiod
  unfold auliBettinConreyRenormalizedPeriodSide
  rw [hperiod']
  ring

/-- The cited parameter-dependent three-term relation forces the homogeneous
central recurrence in the source normalization. -/
theorem bettinConreyCentralFinitePartSide_descent_of_threeTerm
    (H : AuliBettinConreyRationalReciprocityPackage)
    (P : AuliBettinConreyRationalThreeTermPackage H)
    (h k : ℕ) (hk : 0 < k) (hkh : k < h) (hcop : Nat.Coprime h k) :
    (bettinConreyCentralFinitePartSide h k : ℂ) =
      (bettinConreyCentralFinitePartSide (h - k) k : ℂ) -
        ((k : ℂ) / (h : ℂ)) *
          (bettinConreyCentralFinitePartSide (h - k) h : ℂ) := by
  have hh : 0 < h := Nat.zero_lt_of_lt hkh
  have hu : 0 < h - k := Nat.sub_pos_of_lt hkh
  have hcop₁ : Nat.Coprime (h - k) k :=
    (Nat.coprime_sub_self_left hkh.le).2 hcop
  have hcop₂ : Nat.Coprime (h - k) h :=
    (Nat.coprime_self_sub_left hkh.le).2 hcop.symm
  have hleft := tendsto_auliBettinConreyRenormalizedPeriodSide_zero
    H h k hh hk hcop
  have hfirst := tendsto_auliBettinConreyRenormalizedPeriodSide_zero
    H (h - k) k hu hk hcop₁
  have hsecond := tendsto_auliBettinConreyRenormalizedPeriodSide_zero
    H (h - k) h hu hh hcop₂
  have hbase0 : ((k : ℂ) / (h : ℂ)) ≠ 0 := by
    exact div_ne_zero (by exact_mod_cast hk.ne') (by exact_mod_cast hh.ne')
  have hfactor : Tendsto
      (fun z : ℂ => routeCPeriodDescentFactor z h k)
      (𝓝[≠] 0) (𝓝 ((k : ℂ) / (h : ℂ))) := by
    have hc : ContinuousAt
        (fun z : ℂ => ((k : ℂ) / (h : ℂ)) ^ (1 + z)) 0 := by
      exact (continuousAt_const_cpow hbase0).comp
        (continuousAt_const.add continuousAt_id)
    simpa [routeCPeriodDescentFactor, hbase0] using
      hc.tendsto.mono_left inf_le_left
  have hright := hfirst.sub (hfactor.mul hsecond)
  have heq :
      (fun z : ℂ => auliBettinConreyRenormalizedPeriodSide H z h k) =ᶠ[𝓝[≠] 0]
        (fun z : ℂ =>
          auliBettinConreyRenormalizedPeriodSide H z (h - k) k -
            routeCPeriodDescentFactor z h k *
              auliBettinConreyRenormalizedPeriodSide H z (h - k) h) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact auliBettinConreyRenormalizedPeriodSide_descent
      H P z h k hz hk hkh
  have hleft' := hleft.congr' heq
  have hlimit := tendsto_nhds_unique hleft' hright
  exact hlimit

/-- The genuinely local analytic data: an absolutely summable Taylor
expansion only on the unit interval.  The global descent recurrence is not a
field of this structure. -/
structure RouteCUnitIntervalTaylorCoefficientData where
  baseCompleted : ℕ → ℕ → ℂ
  baseCenteredMode : ℕ → ℕ → ℕ → ℂ
  baseCenteredMode_norm_summable : ∀ h k,
    Summable (fun n : ℕ => ‖baseCenteredMode h k n‖)
  base_eq : ∀ h k, 0 < h → 0 < k → h ≤ k → Nat.Coprime h k →
    (bettinConreyCentralFinitePartSide h k : ℂ) =
      baseCompleted h k + ∑' n : ℕ, baseCenteredMode h k n

/-- Reciprocity plus the paper's three-term relation supplies the corrected
descent field required by the existing Euclidean reconstruction. -/
noncomputable def RouteCUnitIntervalTaylorCoefficientData.toPeriodCoefficientData
    (D : RouteCUnitIntervalTaylorCoefficientData)
    (H : AuliBettinConreyRationalReciprocityPackage)
    (P : AuliBettinConreyRationalThreeTermPackage H) :
    RouteCUnitIntervalPeriodCoefficientData where
  baseCompleted := D.baseCompleted
  baseCenteredMode := D.baseCenteredMode
  baseCenteredMode_norm_summable := D.baseCenteredMode_norm_summable
  base_eq := D.base_eq
  descent_eq := bettinConreyCentralFinitePartSide_descent_of_threeTerm H P

/-- The source-level data now hands off directly to the adaptive cofinal H15
stop test, with no separately assumed central recurrence. -/
theorem exists_cofinal_routeCUnitIntervalTaylorLowMode_iff_target
    (D : RouteCUnitIntervalTaylorCoefficientData)
    (H : AuliBettinConreyRationalReciprocityPackage)
    (P : AuliBettinConreyRationalThreeTermPackage H) :
    ∃ K : ℕ → ℕ,
      (∀ N, N ≤ K N) ∧
      (Tendsto (fun N : ℕ =>
          routeCAdaptiveTransformLow
            ((D.toPeriodCoefficientData H P).toLocalPeriodData.toPrimitiveSummableData.toNormSummableTransfer)
            (K N) N)
          atTop (nhds 0) ↔
        Tendsto routeCCentralFinitePartTarget atTop (nhds 0)) :=
  exists_cofinal_routeCUnitIntervalLowMode_iff_target
    (D.toPeriodCoefficientData H P)

end RH.Criteria.NymanBeurling.BCFLogTaperRouteCThreeTermDefect
