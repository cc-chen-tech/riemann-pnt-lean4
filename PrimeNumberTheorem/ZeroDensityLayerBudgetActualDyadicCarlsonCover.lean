import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicCarlsonAutomaticCount

/-!
# A concrete dyadic real-part cover for actual zeta zeros

At scale `m`, layer `j` uses gap

`g_j(m) = 2^j delta(m)`

and strip `(1 - 2 g_j, 1 - g_j]`.  Consecutive strips meet at one endpoint,
distinct strips are disjoint, and the first `L` strips cover exactly

`(1 - 2^L delta(m), 1 - delta(m)]`.

This supplies the concrete dynamic real-part geometry missing from the
variable-family Carlson transfer.
-/

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

noncomputable section

noncomputable def dyadicCarlsonGap
    (delta : ℕ → ℝ) (m j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * delta m

/-- A scalar lies in one of the first `n` dyadic gap strips whenever it lies
between their outer endpoints. -/
theorem exists_dyadicCarlsonGap_layer
    (delta x : ℝ) :
    ∀ n : ℕ,
      1 - (2 : ℝ) ^ n * delta < x →
      x ≤ 1 - delta →
      ∃ j : ℕ, j < n ∧
        1 - 2 * ((2 : ℝ) ^ j * delta) < x ∧
        x ≤ 1 - (2 : ℝ) ^ j * delta := by
  intro n
  induction n with
  | zero =>
      intro hlow hupper
      simp only [pow_zero, one_mul] at hlow
      exact (not_lt_of_ge hupper hlow).elim
  | succ n ih =>
      intro hlow hupper
      by_cases hcut : x ≤ 1 - (2 : ℝ) ^ n * delta
      · refine ⟨n, Nat.lt_succ_self n, ?_, hcut⟩
        convert hlow using 1 <;> ring
      · obtain ⟨j, hj, hjlow, hjupper⟩ :=
          ih (lt_of_not_ge hcut) hupper
        exact ⟨j, hj.trans (Nat.lt_succ_self n), hjlow, hjupper⟩

/-- Every active dyadic gap dominates the base gap. -/
theorem delta_le_dyadicCarlsonGap
    {delta : ℕ → ℝ} {m j : ℕ}
    (hdelta : 0 ≤ delta m) :
    delta m ≤ dyadicCarlsonGap delta m j := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ j :=
    pow_le_pow_right₀ (by norm_num) (Nat.zero_le j)
  unfold dyadicCarlsonGap
  calc
    delta m = 1 * delta m := by ring
    _ ≤ (2 : ℝ) ^ j * delta m :=
      mul_le_mul_of_nonneg_right hpow hdelta

/-- Different dyadic layers are automatically factor-two separated. -/
theorem dyadicCarlsonGap_familySeparated
    {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    (hdelta : ∀ m, 0 ≤ delta m) :
    CarlsonDynamicGapFamilySeparated layers (dyadicCarlsonGap delta) := by
  intro m i j hij
  have hval : i.1 ≠ j.1 := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hijlt | hjilt
  · left
    have hpow :
        (2 : ℝ) ^ (i.1 + 1) ≤ (2 : ℝ) ^ j.1 :=
      pow_le_pow_right₀ (by norm_num)
        (Nat.succ_le_iff.mpr hijlt)
    unfold dyadicCarlsonGap
    calc
      2 * ((2 : ℝ) ^ i.1 * delta m) =
          (2 : ℝ) ^ (i.1 + 1) * delta m := by
            rw [pow_succ]
            ring
      _ ≤ (2 : ℝ) ^ j.1 * delta m :=
        mul_le_mul_of_nonneg_right hpow (hdelta m)
  · right
    have hpow :
        (2 : ℝ) ^ (j.1 + 1) ≤ (2 : ℝ) ^ i.1 :=
      pow_le_pow_right₀ (by norm_num)
        (Nat.succ_le_iff.mpr hjilt)
    unfold dyadicCarlsonGap
    calc
      2 * ((2 : ℝ) ^ j.1 * delta m) =
          (2 : ℝ) ^ (j.1 + 1) * delta m := by
            rw [pow_succ]
            ring
      _ ≤ (2 : ℝ) ^ i.1 * delta m :=
        mul_le_mul_of_nonneg_right hpow (hdelta m)

/-- The actual dyadic zeta union contains every positive zero in its exact
real-part interval. -/
theorem mem_actualDynamicDyadicCarlsonGapStripUnion
    {alpha : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    {m : ℕ} {rho : ℂ}
    (hzero : RiemannHypothesis.IsNontrivialZero rho)
    (him : 0 < rho.im)
    (himHeight :
      rho.im ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hreLower :
      1 - (2 : ℝ) ^ (layers m) * delta m < rho.re)
    (hreUpper : rho.re ≤ 1 - delta m) :
    rho ∈ actualDynamicCarlsonGapStripUnion
      alpha layers (dyadicCarlsonGap delta) m := by
  obtain ⟨j, hj, hjLower, hjUpper⟩ :=
    exists_dyadicCarlsonGap_layer
      (delta m) rho.re (layers m) hreLower hreUpper
  let i : Fin (layers m) := ⟨j, hj⟩
  unfold actualDynamicCarlsonGapStripUnion
    actualPositiveCarlsonFiniteStripUnion
  rw [Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [mem_actualPositiveCarlsonStrip]
  simpa [i, dyadicCarlsonGap] using
    (show
      RiemannHypothesis.IsNontrivialZero rho ∧
        0 < rho.im ∧
        rho.im ≤ carlsonPolynomialHeight alpha (m : ℝ) ∧
        1 - 2 * ((2 : ℝ) ^ j * delta m) < rho.re ∧
        rho.re ≤ 1 - (2 : ℝ) ^ j * delta m
      from ⟨hzero, him, himHeight, hjLower, hjUpper⟩)

/-- Concrete dyadic specialization of the automatic actual-zeta dynamic
Carlson transfer. -/
theorem exists_constants_tendsto_actualDynamicDyadicCarlsonGapStripUnion_mass_zero
    {alpha : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    (halpha : 0 < alpha)
    (hdeltaNonneg : ∀ m, 0 ≤ delta m)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hactiveGap :
      ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
        dyadicCarlsonGap delta m i.1 ≤ 1 / 8 ∧
          128 * alpha * dyadicCarlsonGap delta m i.1 ≤ 1)
    (hmargin :
      IsCarlsonMovingQuadraticLogPowerLayerCountGap delta layers) :
    ∃ A C₁ C₂ : ℝ,
      0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
        (ActualDynamicCarlsonGapFamilyHeightConditions
            C₁ C₂ alpha layers (dyadicCarlsonGap delta) →
          Tendsto
            (fun m =>
              ∑ rho ∈ actualDynamicCarlsonGapStripUnion
                  alpha layers (dyadicCarlsonGap delta) m,
                ‖pntRelativeZeroContribution (m : ℝ) rho‖)
            atTop (nhds 0)) := by
  have hlayerGap :
      ∀ᶠ m : ℕ in atTop, ∀ i : Fin (layers m),
        delta m ≤ dyadicCarlsonGap delta m i.1 ∧
          dyadicCarlsonGap delta m i.1 ≤ 1 / 8 ∧
          128 * alpha * dyadicCarlsonGap delta m i.1 ≤ 1 := by
    filter_upwards [hactiveGap] with m hgm
    intro i
    exact
      ⟨delta_le_dyadicCarlsonGap (hdeltaNonneg m),
        (hgm i).1, (hgm i).2⟩
  exact
    exists_constants_tendsto_actualDynamicCarlsonGapStripUnion_mass_zero
      halpha hdelta hlayerGap hmargin
        (dyadicCarlsonGap_familySeparated hdeltaNonneg)

end

end PrimeNumberTheorem
