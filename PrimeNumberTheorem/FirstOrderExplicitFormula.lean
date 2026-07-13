import MathlibAux.BoundaryRectResidue
import PrimeNumberTheorem.ExplicitFormulaResidues
import PrimeNumberTheorem.ExplicitFormulaRectangle
import PrimeNumberTheorem.ExplicitFormulaAux
import PrimeNumberTheorem.FirstOrderLSeriesPerron
import PrimeNumberTheorem.LeftVerticalEdge
import PrimeNumberTheorem.SecondOrderExplicitFormula

open Complex Filter Topology Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

/-- Every member of the finite trivial-zero truncation is a simple zeta
zero. -/
theorem analyticOrderNatAt_riemannZeta_eq_one_of_mem_finiteTrivialZeroSum
    {ρ : ℂ} {T : ℝ} (hρ : ρ ∈ finiteTrivialZeroSum T) :
    analyticOrderNatAt riemannZeta ρ = 1 := by
  rcases mem_finiteTrivialZeroSum_iff.mp hρ with ⟨n, _hn, hnρ⟩
  rw [← hnρ]
  simpa only [Nat.cast_add, Nat.cast_one] using
    analyticOrderNatAt_riemannZeta_neg_even n

/-- On the finite trivial-zero truncation, the multiplicity-aware contour
residue sum is exactly the simple-residue sum. -/
theorem sum_finiteTrivialZeroSum_multiplicity_residues_eq
    {x T : ℝ} :
    (∑ ρ ∈ finiteTrivialZeroSum T,
        -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) =
      ∑ ρ ∈ finiteTrivialZeroSum T, -((x : ℂ) ^ ρ) / ρ := by
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [analyticOrderNatAt_riemannZeta_eq_one_of_mem_finiteTrivialZeroSum hρ]
  norm_num

/-- The multiplicity-aware trivial-zero truncations dictated by the contour
residue formula converge to the classical logarithmic correction. -/
theorem tendsto_finiteTrivialZeroSum_multiplicity_residues
    {x : ℝ} (hx : 1 < x) :
    Tendsto
      (fun N : ℕ => ∑ ρ ∈ finiteTrivialZeroSum (2 * (N : ℝ)),
        -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ)
      atTop
      (nhds (((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))) := by
  convert ExplicitFormulaAux.tendsto_finiteTrivialZeroSum_residues hx using 1
  funext N
  exact sum_finiteTrivialZeroSum_multiplicity_residues_eq

/-- The subset of a contour pole finset consisting of displayed negative
even integers. -/
noncomputable def trivialZeroPart (poles : Finset ℂ) : Finset ℂ := by
  classical
  exact poles.filter fun p : ℂ =>
    ∃ n : ℕ, p = (-2 * ((n : ℕ) + 1) : ℂ)

/-- The complementary part of a contour pole finset after removing the
displayed negative even integers. -/
noncomputable def remainingPolePart (poles : Finset ℂ) : Finset ℂ := by
  classical
  exact poles.filter fun p : ℂ =>
    ¬∃ n : ℕ, p = (-2 * ((n : ℕ) + 1) : ℂ)

/-- The canonical remaining-pole finset at height `H`: the poles at
`0`, `1`, and all nontrivial zeta zeros up to that height. -/
noncomputable def explicitRemainingPolePart (H : ℝ) : Finset ℂ := by
  classical
  exact {0, 1} ∪ nontrivialZerosFinset H

/-- Under the moving rectangle's completeness contract, the abstract
remaining-pole finset is exactly `{0,1}` together with the height-truncated
nontrivial zeros. -/
theorem remainingPolePart_eq_explicit (poles : Finset ℂ) (N : ℕ) {c H : ℝ}
    (hc : 1 < c) (hH : 0 < H)
    (hpoles : ∀ p ∈ poles,
      -(2 * (N : ℝ) + 1) < p.re ∧ p.re < c ∧ -H < p.im ∧ p.im < H)
    (hclass : ∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0)
    (hcomplete : ∀ p,
      p ∈ ([[-(2 * (N : ℝ) + 1), c]] ×ℂ [[-H, H]] : Set ℂ) →
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) :
    remainingPolePart poles = explicitRemainingPolePart H := by
  classical
  ext p
  simp only [remainingPolePart, Finset.mem_filter, explicitRemainingPolePart,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hpole, hnottriv⟩
    rcases hclass p hpole with rfl | rfl | hpzero
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · right
      apply mem_nontrivialZerosFinset.mpr
      have hre_pos : 0 < p.re := by
        by_contra hnot
        exact (riemannZeta_ne_zero_of_re_le_zero
          (le_of_not_gt hnot) (by simpa [not_exists] using hnottriv)) hpzero
      have hre_lt : p.re < 1 := by
        by_contra hnot
        exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hnot)) hpzero
      have him := (hpoles p hpole).2.2
      exact ⟨⟨hpzero, hre_pos, hre_lt⟩, abs_le.mpr ⟨him.1.le, him.2.le⟩⟩
  · intro hp
    rcases hp with (rfl | rfl) | hpzero
    · refine ⟨hcomplete 0 ?_ (Or.inl rfl), ?_⟩
      · have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        have ha_c : -(2 * (N : ℝ) + 1) ≤ c := by linarith
        have hheight : -H ≤ H := by linarith
        rw [Complex.mem_reProdIm, Set.uIcc_of_le ha_c,
          Set.uIcc_of_le hheight]
        norm_num
        constructor
        · constructor <;> linarith
        · linarith
      · simp only [not_exists]
        intro n hn
        have hre := congrArg Complex.re hn
        norm_num at hre
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
    · refine ⟨hcomplete 1 ?_ (Or.inr (Or.inl rfl)), ?_⟩
      · have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        have ha_c : -(2 * (N : ℝ) + 1) ≤ c := by linarith
        have hheight : -H ≤ H := by linarith
        rw [Complex.mem_reProdIm, Set.uIcc_of_le ha_c,
          Set.uIcc_of_le hheight]
        norm_num
        constructor
        · constructor <;> linarith
        · linarith
      · simp only [not_exists]
        intro n hn
        have hre := congrArg Complex.re hn
        norm_num at hre
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
    · rcases mem_nontrivialZerosFinset.mp hpzero with ⟨hnt, hheight⟩
      refine ⟨hcomplete p ?_ (Or.inr (Or.inr hnt.1)), ?_⟩
      · have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        have ha_c : -(2 * (N : ℝ) + 1) ≤ c := by linarith
        have hheightIcc : -H ≤ H := by linarith
        rw [Complex.mem_reProdIm, Set.uIcc_of_le ha_c,
          Set.uIcc_of_le hheightIcc]
        exact ⟨⟨by linarith [hnt.2.1], by linarith [hnt.2.2]⟩,
          abs_le.mp hheight⟩
      · simp only [not_exists]
        intro n hn
        have hre := congrArg Complex.re hn
        norm_num at hre
        linarith [hnt.2.1]

/-- The actual residue sum over the remaining contour poles is the classical
pole-at-one term, the kernel-pole-at-zero term, and the multiplicity-weighted
finite nontrivial-zero sum. -/
theorem sum_remainingPolePart_residue_eq
    (poles : Finset ℂ) (residue : ℂ → ℂ) (N : ℕ) {x c H : ℝ}
    (hc : 1 < c) (hH : 0 < H)
    (hpoles : ∀ p ∈ poles,
      -(2 * (N : ℝ) + 1) < p.re ∧ p.re < c ∧ -H < p.im ∧ p.im < H)
    (hclass : ∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0)
    (hcomplete : ∀ p,
      p ∈ ([[-(2 * (N : ℝ) + 1), c]] ×ℂ [[-H, H]] : Set ℂ) →
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles)
    (hresidue : ∀ p ∈ poles, residue p =
      if p = 1 then (x : ℂ)
      else if p = 0 then -deriv riemannZeta 0 / riemannZeta 0
      else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) :
    (∑ p ∈ remainingPolePart poles, residue p) =
      (x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
        ∑ ρ ∈ nontrivialZerosFinset H,
          -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
  classical
  have hpart : remainingPolePart poles = explicitRemainingPolePart H :=
    remainingPolePart_eq_explicit poles N hc hH hpoles hclass hcomplete
  rw [hpart, explicitRemainingPolePart]
  have hdisjoint : Disjoint ({0, 1} : Finset ℂ) (nontrivialZerosFinset H) := by
    rw [Finset.disjoint_left]
    intro p hp01 hpnt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp01
    have hnt := (mem_nontrivialZerosFinset.mp hpnt).1
    rcases hp01 with rfl | rfl
    · have hpos := hnt.2.1
      norm_num at hpos
    · have hlt := hnt.2.2
      norm_num at hlt
  rw [Finset.sum_union hdisjoint]
  have hzeroRem : (0 : ℂ) ∈ remainingPolePart poles := by
    rw [hpart]
    simp [explicitRemainingPolePart]
  have honeRem : (1 : ℂ) ∈ remainingPolePart poles := by
    rw [hpart]
    simp [explicitRemainingPolePart]
  have hzeroPole := (Finset.mem_filter.mp hzeroRem).1
  have honePole := (Finset.mem_filter.mp honeRem).1
  have h01 : (∑ p ∈ ({0, 1} : Finset ℂ), residue p) =
      (x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 := by
    rw [Finset.sum_insert (by norm_num : (0 : ℂ) ∉ ({1} : Finset ℂ)),
      Finset.sum_singleton]
    rw [hresidue 0 hzeroPole, hresidue 1 honePole]
    simp
    ring
  rw [h01]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hnt := (mem_nontrivialZerosFinset.mp hρ).1
  have hρ0 : ρ ≠ 0 := by
    intro h
    have hpos := hnt.2.1
    rw [h] at hpos
    norm_num at hpos
  have hρ1 : ρ ≠ 1 := by
    intro h
    have hlt := hnt.2.2
    rw [h] at hlt
    norm_num at hlt
  have hρrem : ρ ∈ remainingPolePart poles := by
    rw [hpart]
    simp [explicitRemainingPolePart, hρ]
  have hρpole := (Finset.mem_filter.mp hρrem).1
  rw [hresidue ρ hρpole, if_neg hρ1, if_neg hρ0]

/-- For a rectangle whose left edge lies halfway between `-2N` and
`-2(N+1)`, the trivial-zero part of its complete pole finset is exactly
`{-2, -4, ..., -2N}`. -/
theorem trivialZeroPart_eq_finiteTrivialZeroSum
    (poles : Finset ℂ) (N : ℕ) {c H : ℝ}
    (hc : 1 < c) (hH : 0 < H)
    (hpoles : ∀ p ∈ poles,
      -(2 * (N : ℝ) + 1) < p.re ∧ p.re < c ∧ -H < p.im ∧ p.im < H)
    (hcomplete : ∀ p,
      p ∈ ([[-(2 * (N : ℝ) + 1), c]] ×ℂ [[-H, H]] : Set ℂ) →
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) :
    trivialZeroPart poles = finiteTrivialZeroSum (2 * (N : ℝ)) := by
  classical
  ext p
  simp only [trivialZeroPart, Finset.mem_filter]
  constructor
  · rintro ⟨hp, n, rfl⟩
    apply mem_finiteTrivialZeroSum_iff.mpr
    refine ⟨n, ?_, rfl⟩
    rw [show 2 * (N : ℝ) / 2 = (N : ℝ) by ring, Nat.floor_natCast]
    have hleft := (hpoles _ hp).1
    have hre : (-2 * ((n : ℕ) + 1) : ℂ).re =
        -2 * ((n : ℝ) + 1) := by norm_num
    rw [hre] at hleft
    have hnR : (n : ℝ) < N := by linarith
    exact_mod_cast hnR
  · intro hp
    rcases mem_finiteTrivialZeroSum_iff.mp hp with ⟨n, hn, hnp⟩
    rw [show 2 * (N : ℝ) / 2 = (N : ℝ) by ring, Nat.floor_natCast] at hn
    rw [← hnp]
    refine ⟨hcomplete _ ?_ (Or.inr (Or.inr ?_)), ⟨n, rfl⟩⟩
    · have hnR : (n : ℝ) < N := by exact_mod_cast hn
      have hnSuccR : ((n + 1 : ℕ) : ℝ) ≤ N := by
        exact_mod_cast (Nat.succ_le_iff.mpr hn)
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      have hre : (-2 * ((n : ℕ) + 1) : ℂ).re =
          -2 * ((n : ℝ) + 1) := by norm_num
      have him : (-2 * ((n : ℕ) + 1) : ℂ).im = 0 := by norm_num
      have hre_lower : -(2 * (N : ℝ) + 1) ≤
          (-2 * ((n : ℕ) + 1) : ℂ).re := by
        rw [hre]
        norm_num at hnSuccR ⊢
        linarith
      have hre_upper : (-2 * ((n : ℕ) + 1) : ℂ).re ≤ c := by
        rw [hre]
        linarith
      have ha_c : -(2 * (N : ℝ) + 1) ≤ c := by linarith
      have hheight : -H ≤ H := by linarith
      rw [Complex.mem_reProdIm]
      constructor
      · rw [Set.uIcc_of_le ha_c]
        exact ⟨hre_lower, hre_upper⟩
      · rw [Set.uIcc_of_le hheight, him]
        exact ⟨by linarith, hH.le⟩
    · simpa only [Nat.cast_add, Nat.cast_one] using
        riemannZeta_neg_two_mul_nat_add_one n

/-- Every contour-pole sum is the sum over its trivial-zero part plus the
remaining poles. -/
theorem sum_contourPoleResidues_eq_trivial_add_remaining
    (poles : Finset ℂ) (residue : ℂ → ℂ) :
    (∑ p ∈ poles, residue p) =
      (∑ p ∈ trivialZeroPart poles, residue p) +
        ∑ p ∈ remainingPolePart poles, residue p := by
  classical
  symm
  exact Finset.sum_filter_add_sum_filter_not poles
    (fun p : ℂ => ∃ n : ℕ, p = (-2 * ((n : ℕ) + 1) : ℂ)) residue

/-- Under the contour theorem's pole and residue contracts, the residue sum
over the extracted trivial-zero part is the explicit finite simple-residue
sum. -/
theorem sum_trivialZeroPart_residue_eq
    (poles : Finset ℂ) (residue : ℂ → ℂ) (N : ℕ) {x c H : ℝ}
    (hc : 1 < c) (hH : 0 < H)
    (hpoles : ∀ p ∈ poles,
      -(2 * (N : ℝ) + 1) < p.re ∧ p.re < c ∧ -H < p.im ∧ p.im < H)
    (hcomplete : ∀ p,
      p ∈ ([[-(2 * (N : ℝ) + 1), c]] ×ℂ [[-H, H]] : Set ℂ) →
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles)
    (hresidue : ∀ p ∈ poles, residue p =
      if p = 1 then (x : ℂ)
      else if p = 0 then -deriv riemannZeta 0 / riemannZeta 0
      else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) :
    (∑ p ∈ trivialZeroPart poles, residue p) =
      ∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)), -((x : ℂ) ^ p) / p := by
  classical
  have hpart :=
    trivialZeroPart_eq_finiteTrivialZeroSum poles N hc hH hpoles hcomplete
  rw [hpart]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : p ≠ 0 := finiteTrivialZeroSum_ne_zero_of_mem hp
  have hp1 : p ≠ 1 := by
    have hneg := finiteTrivialZeroSum_re_lt_zero_of_mem hp
    intro h
    rw [h] at hneg
    norm_num at hneg
  have hpole : p ∈ poles := by
    rw [← hpart] at hp
    exact (Finset.mem_filter.mp hp).1
  rw [hresidue p hpole, if_neg hp1, if_neg hp0]
  rw [analyticOrderNatAt_riemannZeta_eq_one_of_mem_finiteTrivialZeroSum hp]
  norm_num

/-- The complete residue sum returned by the moving rectangle splits into
the explicit first `N` trivial-zero residues and the remaining pole sum. -/
theorem sum_contourPoleResidues_eq_finiteTrivial_add_remaining
    (poles : Finset ℂ) (residue : ℂ → ℂ) (N : ℕ) {x c H : ℝ}
    (hc : 1 < c) (hH : 0 < H)
    (hpoles : ∀ p ∈ poles,
      -(2 * (N : ℝ) + 1) < p.re ∧ p.re < c ∧ -H < p.im ∧ p.im < H)
    (hcomplete : ∀ p,
      p ∈ ([[-(2 * (N : ℝ) + 1), c]] ×ℂ [[-H, H]] : Set ℂ) →
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles)
    (hresidue : ∀ p ∈ poles, residue p =
      if p = 1 then (x : ℂ)
      else if p = 0 then -deriv riemannZeta 0 / riemannZeta 0
      else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) :
    (∑ p ∈ poles, residue p) =
      (∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)), -((x : ℂ) ^ p) / p) +
        ∑ p ∈ remainingPolePart poles, residue p := by
  rw [sum_contourPoleResidues_eq_trivial_add_remaining]
  rw [sum_trivialZeroPart_residue_eq poles residue N hc hH hpoles hcomplete hresidue]

/-- On an ordered rectangle containing `0` in its interior, the first-order
explicit-formula integrand satisfies the finite residue formula.  The right
edge can be fixed independently of the height, as required by Perron
inversion. -/
theorem exists_boundaryRectIntegral_explicitFormulaIntegrand_eq_residue_sum
    {x a c W : ℝ} (hx : 0 < x) (ha : a < 0) (hc : 0 < c)
    (hW : 0 < W)
    (hboundary : ∀ p ∈ ([[a, c]] ×ℂ [[-W, W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈ ([[a, c]] ×ℂ [[-W, W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else if p = 0 then -deriv riemannZeta 0 / riemannZeta 0
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) ∧
      MathlibAux.boundaryRectIntegral
          (explicitFormulaIntegrand x) a c (-W) W =
        (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
  classical
  let K : Set ℂ := [[a, c]] ×ℂ [[-W, W]]
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_uIcc.reProdIm isCompact_uIcc
  rcases exists_finite_explicitFormulaIntegrand_analytic_regularized_remainder
      hx hKcompact with
    ⟨poles, residue, hpoles_mem, hpoles_classify, hpoles_complete,
      hresidue, hoff_eq, hregular⟩
  let raw : ℂ → ℂ := fun z =>
    explicitFormulaIntegrand x z -
      ∑ p ∈ poles, (z - p)⁻¹ * residue p
  let g : ℂ → ℂ := toMeromorphicNFOn raw K
  have hregular' : AnalyticOnNhd ℂ g K := by
    simpa [g, raw] using hregular
  have hpoles : ∀ p ∈ poles,
      a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W := by
    intro p hp
    rcases hpoles_mem p hp with hp0 | hpK
    · subst p
      simpa using And.intro ha (And.intro hc
        (And.intro (neg_lt_zero.mpr hW) hW))
    · exact hboundary p hpK (hpoles_classify p hp)
  have hboundary_eq : ∀ z ∈ K,
      ¬(a < z.re ∧ z.re < c ∧ -W < z.im ∧ z.im < W) →
        explicitFormulaIntegrand x z =
          g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p := by
    intro z hzK hzboundary
    have hz_not_pole : z ∉ poles := by
      intro hzpoles
      exact hzboundary (hpoles z hzpoles)
    have hg_eq := hoff_eq z hzK hz_not_pole
    change g z = raw z at hg_eq
    rw [hg_eq]
    simp only [raw]
    ring
  refine ⟨poles, residue, hpoles, hpoles_classify, hpoles_complete,
    (fun p _hp => hresidue p), ?_⟩
  calc
    MathlibAux.boundaryRectIntegral (explicitFormulaIntegrand x) a c (-W) W =
        MathlibAux.boundaryRectIntegral
          (fun z : ℂ => g z +
            ∑ p ∈ poles, (z - p)⁻¹ * residue p) a c (-W) W := by
      apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
      simpa [K] using hboundary_eq
    _ = (2 * Real.pi * I) * ∑ p ∈ poles, residue p :=
      MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
        poles residue hregular'.differentiableOn hpoles

/-- The normalized contribution of the bottom, top, and left edges when the
ordinary Perron contour is shifted from `Re(s)=c` to `Re(s)=a`. -/
noncomputable def firstOrderContourRemainder
    (x a c W : ℝ) : ℂ :=
  ((∫ σ : ℝ in a..c,
      explicitFormulaIntegrand x
        ((σ : ℂ) + ((-(2 * Real.pi * W) : ℝ) : ℂ) * I)) -
    (∫ σ : ℝ in a..c,
      explicitFormulaIntegrand x
        ((σ : ℂ) + (((2 * Real.pi * W) : ℝ) : ℂ) * I)) -
    I * (∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
      explicitFormulaIntegrand x ((a : ℂ) + t * I))) /
    (2 * Real.pi * I)

/-- The fixed right edge in the first-order contour shift is exactly the
ordinary Perron integral, hence converges to `psi0`. -/
theorem tendsto_scaledRightIntegral_explicitFormulaIntegrand_atTop
    {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    Tendsto
      (fun W : ℝ => ∫ w : ℝ in (-W)..W,
        explicitFormulaIntegrand x
          ((c : ℂ) + 2 * Real.pi * w * I))
      atTop (nhds (chebyshevPsi0 x : ℂ)) := by
  have h := tendsto_truncated_neg_logDeriv_firstOrderPerron_atTop hx hc
  convert h using 1
  funext W
  apply intervalIntegral.integral_congr
  intro w _hw
  simp only [explicitFormulaIntegrand, perronLine, logDeriv_apply]
  ring

/-- Exact finite-height first-order contour shift.  The normalized right-line
Perron integral equals the finite residue sum minus the other three normalized
rectangle edges. -/
theorem exists_scaledRightIntegral_eq_residue_sum_sub_firstOrderContourRemainder
    {x a c W : ℝ} (hx : 0 < x) (ha : a < 0) (hc : 0 < c)
    (hW : 0 < W)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else if p = 0 then -deriv riemannZeta 0 / riemannZeta 0
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) ∧
      (∫ w : ℝ in (-W)..W,
          explicitFormulaIntegrand x
            ((c : ℂ) + 2 * Real.pi * w * I)) =
        (∑ p ∈ poles, residue p) -
          firstOrderContourRemainder x a c W := by
  have hheight : 0 < 2 * Real.pi * W := by positivity
  rcases exists_boundaryRectIntegral_explicitFormulaIntegrand_eq_residue_sum
      hx ha hc hheight hboundary with
    ⟨poles, residue, hpoles, hclass, hcomplete, hresidue, hrect⟩
  refine ⟨poles, residue, hpoles, hclass, hcomplete, hresidue, ?_⟩
  have hright := I_mul_verticalIntegral_eq_two_pi_I_mul_scaledIntegral
    (explicitFormulaIntegrand x) c W
  unfold MathlibAux.boundaryRectIntegral at hrect
  simp only [smul_eq_mul] at hrect
  rw [hright] at hrect
  have hden : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  let B : ℂ := ∫ σ : ℝ in a..c,
    explicitFormulaIntegrand x
      ((σ : ℂ) + ((-(2 * Real.pi * W) : ℝ) : ℂ) * I)
  let T : ℂ := ∫ σ : ℝ in a..c,
    explicitFormulaIntegrand x
      ((σ : ℂ) + (((2 * Real.pi * W) : ℝ) : ℂ) * I)
  let L : ℂ := ∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
    explicitFormulaIntegrand x ((a : ℂ) + t * I)
  let R : ℂ := ∫ w : ℝ in (-W)..W,
    explicitFormulaIntegrand x
      ((c : ℂ) + 2 * Real.pi * w * I)
  let S : ℂ := ∑ p ∈ poles, residue p
  have hrect' : (B - T + (2 * Real.pi * I) * R) - I * L =
      (2 * Real.pi * I) * S := by
    simpa [B, T, L, R, S] using hrect
  change R = S - (B - T - I * L) / (2 * Real.pi * I)
  field_simp [hden]
  linear_combination hrect'

/-- A good-height rectangle in the moving-left family, with left edge between
consecutive trivial zeros, has an exact first-order contour identity in which
the abstract pole sum is split into the first `N` trivial-zero residues and
the remaining poles. -/
theorem
    exists_movingLeft_scaledRightIntegral_eq_trivial_add_remaining_sub_remainder
    {x c W : ℝ} (N : ℕ) (hx : 0 < x) (hc : 1 < c) (hW : 0 < W)
    (hgood : goodHeight (2 * Real.pi * W)) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        -(2 * (N : ℝ) + 1) < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[-(2 * (N : ℝ) + 1), c]] ×ℂ
            [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else if p = 0 then -deriv riemannZeta 0 / riemannZeta 0
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) ∧
      (∫ w : ℝ in (-W)..W,
          explicitFormulaIntegrand x ((c : ℂ) + 2 * Real.pi * w * I)) =
        (∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)),
            -((x : ℂ) ^ p) / p) +
          (∑ p ∈ remainingPolePart poles, residue p) -
            firstOrderContourRemainder x (-(2 * (N : ℝ) + 1)) c W := by
  have hH : 0 < 2 * Real.pi * W := by positivity
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have ha : -(2 * (N : ℝ) + 1) < 0 := by linarith
  have hboundary : ∀ p ∈
      ([[-(2 * (N : ℝ) + 1), c]] ×ℂ
        [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        -(2 * (N : ℝ) + 1) < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W := by
    intro p hp hclass
    rcases hclass with rfl | rfl | hpzero
    · simpa using And.intro ha (And.intro (one_pos.trans hc)
        (And.intro (neg_lt_zero.mpr hH) hH))
    · have hleft : -(2 * (N : ℝ) + 1) < (1 : ℝ) := by
        have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      simpa using And.intro hleft (And.intro hc
        (And.intro (neg_lt_zero.mpr hH) hH))
    · have hp' := hp
      simp only [Complex.mem_reProdIm] at hp'
      have hre_bounds := hp'.1
      have ha_le_c : -(2 * (N : ℝ) + 1) ≤ c := by
        have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      rw [Set.uIcc_of_le ha_le_c] at hre_bounds
      have him_bounds := hp'.2
      rw [Set.uIcc_of_le (by linarith :
        -(2 * Real.pi * W) ≤ 2 * Real.pi * W)] at him_bounds
      by_cases htriv : ∃ n : ℕ, p = -2 * ((n : ℂ) + 1)
      · rcases htriv with ⟨n, hn⟩
        have hre := congrArg Complex.re hn
        have him := congrArg Complex.im hn
        norm_num at hre him
        have hre_lower : -(2 * (N : ℝ) + 1) < p.re := by
          by_contra hnot
          have hre_eq : p.re = -(2 * (N : ℝ) + 1) := by
            linarith [hre_bounds.1]
          rw [hre_eq] at hre
          have hnat : 2 * N + 1 = 2 * (n + 1) := by
            exact_mod_cast (by linarith :
              (2 * (N : ℝ) + 1) = 2 * ((n : ℝ) + 1))
          omega
        have hre_upper : p.re < c := by linarith
        exact ⟨hre_lower, hre_upper, by linarith, by linarith⟩
      · have hre_pos : 0 < p.re := by
          by_contra hnot
          exact (riemannZeta_ne_zero_of_re_le_zero
            (le_of_not_gt hnot) (by simpa [not_exists] using htriv)) hpzero
        have hre_lt_one : p.re < 1 := by
          by_contra hnot
          exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hnot)) hpzero
        have habs_le : |p.im| ≤ 2 * Real.pi * W := abs_le.mpr him_bounds
        have habs_ne : |p.im| ≠ 2 * Real.pi * W :=
          hgood p ⟨hpzero, hre_pos, hre_lt_one⟩
        have him_strict := abs_lt.mp (lt_of_le_of_ne habs_le habs_ne)
        exact ⟨by linarith, by linarith, him_strict.1, him_strict.2⟩
  rcases exists_scaledRightIntegral_eq_residue_sum_sub_firstOrderContourRemainder
      hx ha (one_pos.trans hc) hW hboundary with
    ⟨poles, residue, hpoles, hclass, hcomplete, hresidue, hcontour⟩
  refine ⟨poles, residue, hpoles, hclass, hcomplete, hresidue, ?_⟩
  rw [hcontour]
  rw [sum_contourPoleResidues_eq_finiteTrivial_add_remaining
    poles residue N hc hH hpoles hcomplete hresidue]

/-- Concrete finite first-order explicit formula at a good height.  The
abstract contour pole finset has been eliminated: the right Perron integral is
the sum of the trivial-zero residues, the poles at `1` and `0`, and the
multiplicity-weighted nontrivial-zero residues, minus the other three contour
edges. -/
theorem movingLeft_scaledRightIntegral_eq_truncatedExplicitFormula
    {x c W : ℝ} (N : ℕ) (hx : 0 < x) (hc : 1 < c) (hW : 0 < W)
    (hgood : goodHeight (2 * Real.pi * W)) :
    (∫ w : ℝ in (-W)..W,
        explicitFormulaIntegrand x ((c : ℂ) + 2 * Real.pi * w * I)) =
      (∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)), -((x : ℂ) ^ p) / p) +
        ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
          ∑ ρ ∈ nontrivialZerosFinset (2 * Real.pi * W),
            -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
        firstOrderContourRemainder x (-(2 * (N : ℝ) + 1)) c W := by
  have hH : 0 < 2 * Real.pi * W := by positivity
  rcases
      exists_movingLeft_scaledRightIntegral_eq_trivial_add_remaining_sub_remainder
        N hx hc hW hgood with
    ⟨poles, residue, hpoles, hclass, hcomplete, hresidue, hcontour⟩
  rw [hcontour]
  rw [sum_remainingPolePart_residue_eq
    poles residue N hc hH hpoles hclass hcomplete hresidue]

/-- There is a joint cofinal sequence of moving-left Perron rectangles:
the height and the number of enclosed trivial zeros both tend to infinity, every
horizontal boundary is good, each finite-height identity has its trivial-zero
part split out, and those trivial-zero sums converge to the classical
logarithmic correction. -/
theorem exists_jointCofinal_movingLeft_firstOrderContours
    {x c : ℝ} (hx : 1 < x) (hc : 1 < c) :
    ∃ (K : ℕ) (W : ℕ → ℝ), StrictMono W ∧ Tendsto W atTop atTop ∧
      (∀ n, ((n + K : ℕ) : ℝ) < 2 * Real.pi * W n ∧
        2 * Real.pi * W n < ((n + K : ℕ) : ℝ) + 1) ∧
      Tendsto
        (fun n : ℕ => ∑ p ∈ finiteTrivialZeroSum (2 * (n : ℝ)),
          -((x : ℂ) ^ p) / p)
        atTop
        (nhds (((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))) ∧
      Tendsto
        (fun n : ℕ => ∫ t : ℝ in (-(2 * Real.pi * W n))..(2 * Real.pi * W n),
          explicitFormulaIntegrand x
            (((-(2 * (n : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (nhds 0) ∧
      ∀ n, 0 < W n ∧ goodHeight (2 * Real.pi * W n) ∧
        (∫ w : ℝ in (-(W n))..(W n),
            explicitFormulaIntegrand x
              ((c : ℂ) + 2 * Real.pi * w * I)) =
          (∑ p ∈ finiteTrivialZeroSum (2 * (n : ℝ)),
              -((x : ℂ) ^ p) / p) +
            ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
              ∑ ρ ∈ nontrivialZerosFinset (2 * Real.pi * W n),
                -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
              firstOrderContourRemainder x (-(2 * (n : ℝ) + 1)) c (W n) := by
  rcases exists_linearlyControlled_goodHeight_gt_one with
    ⟨K, T, hTmono, hTtend, hT⟩
  let W : ℕ → ℝ := fun n => T n / (2 * Real.pi)
  have hden : 0 < 2 * Real.pi := by positivity
  refine ⟨K, W, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact div_lt_div_of_pos_right (hTmono hab) hden
  · exact hTtend.atTop_div_const hden
  · intro n
    have hscale : 2 * Real.pi * W n = T n := by
      dsimp [W]
      field_simp
    rw [hscale]
    exact ⟨(hT n).1, (hT n).2.1⟩
  · exact ExplicitFormulaAux.tendsto_finiteTrivialZeroSum_residues hx
  · apply tendsto_integral_explicitFormulaIntegrand_odd_vertical_atTop
      (K := K) (T := fun n => 2 * Real.pi * W n) hx
    · intro n
      have hscale : 2 * Real.pi * W n = T n := by
        dsimp [W]
        field_simp
      rw [hscale]
      have hbase : 0 ≤ ((n + K : ℕ) : ℝ) := Nat.cast_nonneg _
      exact hbase.trans (hT n).1.le
    · intro n
      have hscale : 2 * Real.pi * W n = T n := by
        dsimp [W]
        field_simp
      rw [hscale]
      simpa [Nat.cast_add] using (hT n).2.1.le
  · intro n
    have hTgt : 1 < T n := (hT n).2.2.1
    have hTgood : goodHeight (T n) := (hT n).2.2.2
    have hW : 0 < W n := div_pos (lt_trans zero_lt_one hTgt) hden
    have hscale : 2 * Real.pi * W n = T n := by
      dsimp [W]
      field_simp
    refine ⟨hW, ?_, ?_⟩
    · rw [hscale]
      exact hTgood
    · simpa only [hscale] using
        movingLeft_scaledRightIntegral_eq_truncatedExplicitFormula
          n (zero_lt_one.trans hx) hc hW
            (by rw [hscale]; exact hTgood)

/-- Along a joint cofinal moving-left sequence, the
multiplicity-weighted nontrivial-zero sum minus the contour remainder converges
unconditionally.  If the remainder tends to zero, this gives the corresponding
zero-sum limit along the same cofinal sequence; a full principal-value formula
still requires passage from this sequence to arbitrary truncation heights. -/
theorem exists_jointCofinal_nontrivialZeroSum_sub_remainder_tendsto
    {x c : ℝ} (hx : 1 < x) (hc : 1 < c) :
    ∃ W : ℕ → ℝ, StrictMono W ∧ Tendsto W atTop atTop ∧
      (∀ n, goodHeight (2 * Real.pi * W n)) ∧
      Tendsto
        (fun n : ℕ =>
          (∑ ρ ∈ nontrivialZerosFinset (2 * Real.pi * W n),
              -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
            firstOrderContourRemainder x (-(2 * (n : ℝ) + 1)) c (W n))
        atTop
        (nhds ((chebyshevPsi0 x : ℂ) -
          (((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)) -
          ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0))) := by
  rcases exists_jointCofinal_movingLeft_firstOrderContours hx hc with
    ⟨_K, W, hmono, hWtend, _hlinear, htriv, _hleft, hformula⟩
  have hright :=
    (tendsto_scaledRightIntegral_explicitFormulaIntegrand_atTop
      (zero_lt_one.trans hx) hc).comp hWtend
  have hcombined := (hright.sub htriv).sub
    (tendsto_const_nhds : Tendsto
      (fun _n : ℕ => (x : ℂ) - deriv riemannZeta 0 / riemannZeta 0)
      atTop (nhds ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0)))
  refine ⟨W, hmono, hWtend, (fun n => (hformula n).2.1), ?_⟩
  apply hcombined.congr'
  filter_upwards [] with n
  have heq := (hformula n).2.2
  change
    (∫ w : ℝ in (-(W n))..(W n),
        explicitFormulaIntegrand x ((c : ℂ) + 2 * Real.pi * w * I)) -
        (∑ p ∈ finiteTrivialZeroSum (2 * (n : ℝ)), -((x : ℂ) ^ p) / p) -
        ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0) =
      (∑ ρ ∈ nontrivialZerosFinset (2 * Real.pi * W n),
          -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
        firstOrderContourRemainder x (-(2 * (n : ℝ) + 1)) c (W n)
  linear_combination heq

/-- A good height gives an unconditional fixed first-order rectangle with
left edge `Re(s)=-1` and arbitrary fixed right edge `Re(s)=c>1`.  The left
edge contains no trivial zero, the right edge is zero-free, and `goodHeight`
excludes nontrivial zeros from the horizontal edges. -/
theorem
    exists_scaledRightIntegral_eq_residue_sum_sub_firstOrderContourRemainder_of_goodHeight
    {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) (hW : 0 < W)
    (hgood : ExplicitFormulaAux.goodHeight (2 * Real.pi * W)) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        -1 < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[-1, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else if p = 0 then -deriv riemannZeta 0 / riemannZeta 0
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) ∧
      (∫ w : ℝ in (-W)..W,
          explicitFormulaIntegrand x
            ((c : ℂ) + 2 * Real.pi * w * I)) =
        (∑ p ∈ poles, residue p) -
          firstOrderContourRemainder x (-1) c W := by
  have hH : 0 < 2 * Real.pi * W := by positivity
  apply exists_scaledRightIntegral_eq_residue_sum_sub_firstOrderContourRemainder
    hx (by norm_num) (one_pos.trans hc) hW
  intro p hp hclass
  rcases hclass with rfl | rfl | hpzero
  · simpa using And.intro (by norm_num : (-1 : ℝ) < 0)
      (And.intro (one_pos.trans hc)
        (And.intro (neg_lt_zero.mpr hH) hH))
  · simpa using And.intro (by norm_num : (-1 : ℝ) < 1)
      (And.intro hc (And.intro (neg_lt_zero.mpr hH) hH))
  · have hp' := hp
    simp only [Complex.mem_reProdIm] at hp'
    have hre_bounds := hp'.1
    rw [Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤ c)] at hre_bounds
    have him_bounds := hp'.2
    rw [Set.uIcc_of_le (by linarith : -(2 * Real.pi * W) ≤ 2 * Real.pi * W)]
      at him_bounds
    have htrivial : ∀ n : ℕ, p ≠ -2 * ((n : ℂ) + 1) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp at hre
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith [hre_bounds.1]
    have hre_pos : 0 < p.re := by
      by_contra hnot
      exact (riemannZeta_ne_zero_of_re_le_zero (le_of_not_gt hnot) htrivial)
        hpzero
    have hre_lt_one : p.re < 1 := by
      by_contra hnot
      exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hnot)) hpzero
    have habs_le : |p.im| ≤ 2 * Real.pi * W := abs_le.mpr him_bounds
    have habs_ne : |p.im| ≠ 2 * Real.pi * W :=
      hgood p ⟨hpzero, hre_pos, hre_lt_one⟩
    have him_strict := abs_lt.mp (lt_of_le_of_ne habs_le habs_ne)
    exact ⟨by linarith, by linarith, him_strict.1, him_strict.2⟩

end ExplicitFormulaResidues
end PrimeNumberTheorem
