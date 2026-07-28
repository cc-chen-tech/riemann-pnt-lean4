import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageThresholdBarrier

/-!
# Dynamic equal-real-part boundary packages

The fixed-package threshold barrier shows that a main cluster truncated at a
fixed height cannot support strict Carlson decay if further zeros occur on the
same real-part line. This module replaces it pointwise by the package truncated
at the current selected height.

At each height the dynamic package absorbs every visible zero on the boundary
line. If `beta` is a right edge for the visible finite zero set, the remaining
finite complement has a positive, height-dependent real-part gap.
-/

open scoped Topology

namespace PrimeNumberTheorem

/-- The equal-real-part package truncated at the current height. -/
noncomputable def dynamicEqualRealPartZeroPackage
    (H : ℝ → ℝ) (beta x : ℝ) : Finset ℂ :=
  ZeroForcedOscillation.equalRealPartZeroPackage (H x) beta

theorem mem_dynamicEqualRealPartZeroPackage
    {H : ℝ → ℝ} {beta x : ℝ} {z : ℂ} :
    z ∈ dynamicEqualRealPartZeroPackage H beta x ↔
      RiemannHypothesis.IsNontrivialZero z ∧
        |z.im| ≤ H x ∧ z.re = beta := by
  simp [dynamicEqualRealPartZeroPackage,
    ZeroForcedOscillation.mem_equalRealPartZeroPackage]

theorem positiveOutside_dynamicEqualRealPartZeroPackage_re_ne
    {H : ℝ → ℝ} {beta x : ℝ} {z : ℂ}
    (hz :
      z ∈ positiveNontrivialZerosOutsideClusterFinset (H x)
        (dynamicEqualRealPartZeroPackage H beta x)) :
    z.re ≠ beta := by
  intro hzre
  rcases mem_positiveNontrivialZerosOutsideClusterFinset.mp hz with
    ⟨hzero, hzim, hheight, hzpackage⟩
  apply hzpackage
  rw [mem_dynamicEqualRealPartZeroPackage]
  exact ⟨hzero, by simpa [abs_of_pos hzim] using hheight, hzre⟩

theorem positiveOutside_dynamicEqualRealPartZeroPackage_re_lt
    {H : ℝ → ℝ} {beta x : ℝ}
    (hright :
      ∀ z ∈ positiveNontrivialZerosFinset (H x), z.re ≤ beta)
    {z : ℂ}
    (hz :
      z ∈ positiveNontrivialZerosOutsideClusterFinset (H x)
        (dynamicEqualRealPartZeroPackage H beta x)) :
    z.re < beta := by
  have hzfull : z ∈ positiveNontrivialZerosFinset (H x) :=
    (Finset.mem_sdiff.mp hz).1
  exact lt_of_le_of_ne (hright z hzfull)
    (positiveOutside_dynamicEqualRealPartZeroPackage_re_ne hz)

/--
A finite family lying strictly below `beta` has a uniform positive gap below
`beta`.
-/
theorem exists_pos_gap_below_of_finset
    {ι : Type*} (S : Finset ι) (value : ι → ℝ) (beta : ℝ)
    (hstrict : ∀ i ∈ S, value i < beta) :
    ∃ delta, 0 < delta ∧ ∀ i ∈ S, value i ≤ beta - delta := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | @insert a S ha ih =>
      have haStrict : value a < beta :=
        hstrict a (by simp)
      have hSStrict : ∀ i ∈ S, value i < beta := by
        intro i hi
        exact hstrict i (by simp [hi])
      rcases ih hSStrict with ⟨delta, hdelta, hgap⟩
      let epsilon := min delta ((beta - value a) / 2)
      have hepsilon : 0 < epsilon := by
        dsimp [epsilon]
        exact lt_min hdelta (by linarith)
      refine ⟨epsilon, hepsilon, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with hiEq | hiS
      · subst i
        have hepsilonLe : epsilon ≤ (beta - value a) / 2 :=
          min_le_right _ _
        linarith
      · have hiGap := hgap i hiS
        have hepsilonLe : epsilon ≤ delta := min_le_left _ _
        linarith

theorem exists_dynamicEqualRealPartOutside_pos_gap
    {H : ℝ → ℝ} {beta x : ℝ}
    (hright :
      ∀ z ∈ positiveNontrivialZerosFinset (H x), z.re ≤ beta) :
    ∃ delta, 0 < delta ∧
      ∀ z ∈ positiveNontrivialZerosOutsideClusterFinset (H x)
          (dynamicEqualRealPartZeroPackage H beta x),
        z.re ≤ beta - delta := by
  exact exists_pos_gap_below_of_finset
    (positiveNontrivialZerosOutsideClusterFinset (H x)
      (dynamicEqualRealPartZeroPackage H beta x))
    Complex.re beta
    (fun z hz =>
      positiveOutside_dynamicEqualRealPartZeroPackage_re_lt hright hz)

theorem relativeChebyshevPsi0Error_eq_dynamicBoundaryPackage_add_actualResiduals
    (H : ℝ → ℝ) (beta x : ℝ) :
    relativeChebyshevPsi0Error x =
      dynamicVisibleClusterPNTMain H
          (dynamicEqualRealPartZeroPackage H beta x) x +
        (actualPNTClosedRealAxisRelativeTerm x +
          actualPNTExplicitFormulaRelativeRemainder H x +
          dynamicOutsideClusterPNTComplement H
            (dynamicEqualRealPartZeroPackage H beta x) x) := by
  exact relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
    H (dynamicEqualRealPartZeroPackage H beta x) x

end PrimeNumberTheorem
