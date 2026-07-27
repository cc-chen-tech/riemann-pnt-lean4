import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicTailInconsistency

/-!
# Inconsistency of fixed finite-cluster right-half tail buckets

The obstruction in the right-edge tail certificate is not specific to the
right-edge cluster.  For every fixed finite cluster `S`, the
Riemann--von Mangoldt lower bound supplies a positive-ordinate nontrivial zero
outside both `S` and the critical-line reflection of `S`.

At any cofinal truncation height, that zero and its reflection eventually both
belong to the outside-cluster tail.  A bucket family whose every lower endpoint
is strictly greater than `1 / 2` would force both reflected real parts to be
strictly greater than `1 / 2`, which is impossible.

Consequently the current fixed-finite-cluster weighted-good-height transfer
hypotheses cannot be constructed as stated.  This module records the
nonvacuity failure; it does not implement the required critical-half tail.
-/

open Filter

noncomputable section

namespace PrimeNumberTheorem

/-- There is a positive-ordinate nontrivial zeta zero outside every prescribed
finite set. -/
theorem exists_positiveOrdinate_nontrivialZero_not_mem_finset
    (F : Finset ℂ) :
    ∃ rho : ℂ,
      RiemannHypothesis.IsNontrivialZero rho ∧
        0 < rho.im ∧ rho ∉ F := by
  classical
  rcases
      RiemannVonMangoldt.exists_eventually_riemannZeroCount_ge_selbergScale with
    ⟨c, hc, hcount⟩
  let M : ℝ :=
    (∑ rho ∈ F, analyticOrderNatAt riemannZeta rho : ℕ)
  let D : ℝ := 2 * Real.pi
  let B : ℝ := (M + 1) * D / c
  obtain ⟨T, hcountT, hT⟩ :=
    (hcount.and
      (eventually_gt_atTop (max (Real.exp 1) B))).exists
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hTexp : Real.exp 1 < T :=
    (le_max_left _ _).trans_lt hT
  have hTB : B < T :=
    (le_max_right _ _).trans_lt hT
  have hTpos : 0 < T := (Real.exp_pos 1).trans hTexp
  have hlogT : 1 ≤ Real.log T := by
    have hlog :=
      Real.log_le_log (Real.exp_pos 1) hTexp.le
    simpa using hlog
  have hnumerator :
      (M + 1) * D < T * c := by
    exact (div_lt_iff₀ hc).mp (by simpa [B] using hTB)
  have hfactor :
      M + 1 < c * (T / D) := by
    calc
      M + 1 < (T * c) / D :=
        (lt_div_iff₀ hD).2 hnumerator
      _ = c * (T / D) := by ring
  have hfactorPos : 0 < c * (T / D) := by linarith
  have hscale :
      M < c * (T / D * Real.log T) := by
    have hmul :
        c * (T / D) ≤ c * (T / D) * Real.log T :=
      by simpa using
        mul_le_mul_of_nonneg_left hlogT hfactorPos.le
    calc
      M < M + 1 := by linarith
      _ < c * (T / D) := hfactor
      _ ≤ c * (T / D) * Real.log T := hmul
      _ = c * (T / D * Real.log T) := by ring
  have hcountLarge :
      M < (RiemannVonMangoldt.riemannZeroCount T : ℝ) :=
    hscale.trans_le (by simpa [D] using hcountT)
  by_contra hnone
  push_neg at hnone
  have hsubset :
      RiemannVonMangoldt.positiveNontrivialZerosFinset T ⊆ F := by
    intro rho hrho
    have hmem :=
      RiemannVonMangoldt.mem_positiveNontrivialZerosFinset.mp hrho
    exact hnone rho hmem.1 hmem.2.1
  have hcountLeNat :
      RiemannVonMangoldt.riemannZeroCount T ≤
        ∑ rho ∈ F, analyticOrderNatAt riemannZeta rho := by
    unfold RiemannVonMangoldt.riemannZeroCount
    exact
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ => Nat.zero_le _)
  have hcountLe :
      (RiemannVonMangoldt.riemannZeroCount T : ℝ) ≤ M := by
    dsimp [M]
    exact_mod_cast hcountLeNat
  exact (not_le_of_gt hcountLarge) hcountLe

/-- A fixed finite cluster equipped at every height parameter with an
outside-cluster bucket family whose endpoints are the fixed profile `sigma`. -/
def PositiveOutsideClusterBucketFamilyAboveHalf
    (T : ℝ → ℝ)
    (S : Finset ℂ)
    {n : ℕ}
    (sigma : Fin n → ℝ) : Prop :=
  ∃ input : (x : ℝ) →
      PositiveZeroOutsideClusterBucketInput (T x) S n,
    ∀ i x, (input x).sigma i = sigma i

/-- No cofinal height schedule admits a fixed-finite-cluster outside-tail
bucket family whose lower endpoints all lie strictly right of `1 / 2`. -/
theorem not_positiveOutsideClusterBucketFamilyAboveHalf_of_tendsto
    {T : ℝ → ℝ}
    (hT : Tendsto T atTop atTop)
    (S : Finset ℂ)
    {n : ℕ}
    (sigma : Fin n → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i) :
    ¬PositiveOutsideClusterBucketFamilyAboveHalf T S sigma := by
  classical
  rintro ⟨input, hfixedSigma⟩
  let reflectedS :=
    S.image RiemannVonMangoldt.criticalLineReflection
  let forbidden := S ∪ reflectedS
  obtain ⟨rho, hzero, him, hrhoForbidden⟩ :=
    exists_positiveOrdinate_nontrivialZero_not_mem_finset forbidden
  have hrhoS : rho ∉ S := by
    intro hrho
    exact hrhoForbidden (Finset.mem_union_left reflectedS hrho)
  let reflected :=
    RiemannVonMangoldt.criticalLineReflection rho
  have hreflectedZero :
      RiemannHypothesis.IsNontrivialZero reflected :=
    RiemannVonMangoldt.isNontrivialZero_criticalLineReflection hzero
  have hreflectedIm : reflected.im = rho.im := by
    simp [reflected, RiemannVonMangoldt.criticalLineReflection]
  have hreflectedS : reflected ∉ S := by
    intro hreflectedMem
    apply hrhoForbidden
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨reflected, hreflectedMem, ?_⟩
    simpa [reflected] using
      RiemannVonMangoldt.criticalLineReflection_involutive rho
  obtain ⟨x, hx⟩ := ((tendsto_atTop.1 hT) rho.im).exists
  have hrhoOutside :
      rho ∈ positiveNontrivialZerosOutsideClusterFinset (T x) S :=
    mem_positiveNontrivialZerosOutsideClusterFinset.mpr
      ⟨hzero, him, hx, hrhoS⟩
  have hreflectedOutside :
      reflected ∈ positiveNontrivialZerosOutsideClusterFinset (T x) S :=
    mem_positiveNontrivialZerosOutsideClusterFinset.mpr
      ⟨hreflectedZero, by simpa [hreflectedIm] using him,
        by simpa [hreflectedIm] using hx, hreflectedS⟩
  have hsigmaAtX : ∀ i, 1 / 2 < (input x).sigma i := by
    intro i
    rw [hfixedSigma i x]
    exact hsigma i
  have hrhoRight : 1 / 2 < rho.re :=
    (input x).half_lt_re_of_sigma_half hsigmaAtX hrhoOutside
  have hreflectedRight : 1 / 2 < reflected.re :=
    (input x).half_lt_re_of_sigma_half hsigmaAtX hreflectedOutside
  have hreflectedRe : reflected.re = 1 - rho.re := by
    simp [reflected, RiemannVonMangoldt.criticalLineReflection]
  rw [hreflectedRe] at hreflectedRight
  linarith

/-- Every inhabitable cofinal fixed-finite-cluster bucket family must contain
at least one lower endpoint at or to the left of the critical line.

Thus a profile made exclusively from Carlson strips with `1 / 2 < sigma i`
cannot cover the full outside-cluster tail.
-/
theorem exists_sigma_le_half_of_positiveOutsideClusterBucketFamily
    {T : ℝ → ℝ}
    (hT : Tendsto T atTop atTop)
    (S : Finset ℂ)
    {n : ℕ}
    (sigma : Fin n → ℝ)
    (hfamily : PositiveOutsideClusterBucketFamilyAboveHalf T S sigma) :
    ∃ i, sigma i ≤ 1 / 2 := by
  by_contra hnone
  push Not at hnone
  exact
    (not_positiveOutsideClusterBucketFamilyAboveHalf_of_tendsto
      hT S sigma hnone) hfamily

/-- The actual weighted-balanced selected height cannot support the fixed
finite-cluster outside-tail bucket input used by the current unified transfer
theorems. -/
theorem
    not_actualWeightedBalancedGoodHeight_positiveOutsideClusterBucketFamilyAboveHalf
    {beta : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ) :
    ¬PositiveOutsideClusterBucketFamilyAboveHalf
      (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
        beta sigma tau selection)
      S sigma := by
  apply not_positiveOutsideClusterBucketFamilyAboveHalf_of_tendsto
  · exact
      actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_tendsto_atTop
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
  · exact hsigma

end PrimeNumberTheorem
