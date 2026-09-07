import MathlibAux.ArgumentCrossing
import Mathlib.Algebra.BigOperators.Field

/-!
# Open-component argument crossings

These lemmas use one-sided phase limits, never values of a nonvanishing curve
at a zero endpoint. The summed variation is the sum of component increments;
it does not include artificial positive `m * pi` jumps at zeros.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace MathlibAux

/-- Strict interior levels only: a limiting endpoint need not be attained. -/
noncomputable def argumentCrossingInteriorIndices (alpha beta : ℝ) : Finset ℤ :=
  Finset.Ioo ⌊(alpha - Real.pi / 2) / Real.pi⌋
    ⌈(beta - Real.pi / 2) / Real.pi⌉

@[simp]
theorem mem_argumentCrossingInteriorIndices_iff {alpha beta : ℝ} {k : ℤ} :
    k ∈ argumentCrossingInteriorIndices alpha beta ↔
      argumentCrossingLevel k ∈ Ioo alpha beta := by
  rw [argumentCrossingInteriorIndices, ← Int.cast_mem_Ioo_iff]
  constructor
  · intro hk
    have h₁ := (lt_div_iff₀ Real.pi_pos).mp hk.2
    have h₂ := (div_lt_iff₀ Real.pi_pos).mp hk.1
    unfold argumentCrossingLevel
    constructor <;> linarith
  · intro hk
    unfold argumentCrossingLevel at hk
    constructor
    · apply (div_lt_iff₀ Real.pi_pos).mpr
      linarith [hk.1]
    · apply (lt_div_iff₀ Real.pi_pos).mpr
      linarith [hk.2]

/-- Open endpoint rounding costs at most one, including exactly aligned
endpoints, empty intervals, and negative component variation. -/
theorem argumentCrossingInteriorIndices_card_lower_bound {alpha beta : ℝ} :
    (beta - alpha) / Real.pi - 1 ≤
      (argumentCrossingInteriorIndices alpha beta).card := by
  let x := (alpha - Real.pi / 2) / Real.pi
  let y := (beta - Real.pi / 2) / Real.pi
  have hfloor : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have hceil : y ≤ (⌈y⌉ : ℝ) := Int.le_ceil y
  have hnat : (⌈y⌉ - ⌊x⌋ - 1 : ℤ) ≤
      ((⌈y⌉ - ⌊x⌋ - 1).toNat : ℤ) := by omega
  have hreal : (⌈y⌉ : ℝ) - (⌊x⌋ : ℝ) - 1 ≤
      ((⌈y⌉ - ⌊x⌋ - 1).toNat : ℝ) := by exact_mod_cast hnat
  have hnormalize : (beta - alpha) / Real.pi = y - x := by
    dsimp [x, y]
    ring
  rw [argumentCrossingInteriorIndices, Int.card_Ioo]
  change (beta - alpha) / Real.pi - 1 ≤ ((⌈y⌉ - ⌊x⌋ - 1).toNat : ℝ)
  rw [hnormalize]
  linarith

/-- A level strictly between one-sided argument limits is attained at a
genuinely nonzero interior point, not merely at a zero endpoint. -/
theorem exists_argumentCrossing_of_oneSided_limits
    {g ell : ℝ → ℂ} {a b alpha beta : ℝ} (hab : a < b)
    (hell : ContinuousOn ell (Ioo a b))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell t) = g t)
    (hleft : Tendsto (fun t => (ell t).im) (nhdsWithin a (Ioi a)) (nhds alpha))
    (hright : Tendsto (fun t => (ell t).im) (nhdsWithin b (Iio b)) (nhds beta))
    {k : ℤ} (hk : argumentCrossingLevel k ∈ Ioo alpha beta) :
    ∃ t ∈ Ioo a b, (ell t).im = argumentCrossingLevel k ∧
      (g t).re = 0 ∧ g t ≠ 0 := by
  have hneLeft : NeBot (nhdsWithin a (Ioo a b)) := by
    rw [nhdsWithin_Ioo_eq_nhdsGT hab]
    infer_instance
  have hneRight : NeBot (nhdsWithin b (Ioo a b)) := by
    rw [nhdsWithin_Ioo_eq_nhdsLT hab]
    infer_instance
  have hleft' : Tendsto (fun t => (ell t).im)
      (nhdsWithin a (Ioo a b)) (nhds alpha) := by
    simpa [nhdsWithin_Ioo_eq_nhdsGT hab] using hleft
  have hright' : Tendsto (fun t => (ell t).im)
      (nhdsWithin b (Ioo a b)) (nhds beta) := by
    simpa [nhdsWithin_Ioo_eq_nhdsLT hab] using hright
  obtain ⟨t, ht, hphase⟩ := isPreconnected_Ioo.intermediate_value_Ioo
    (l₁ := nhdsWithin a (Ioo a b)) (l₂ := nhdsWithin b (Ioo a b))
    inf_le_right inf_le_right
    (Complex.continuous_im.comp_continuousOn hell) hleft' hright' hk
  change (ell t).im = argumentCrossingLevel k at hphase
  refine ⟨t, ht, hphase, ?_, ?_⟩
  · rw [← hexp t ht, Complex.exp_re, hphase, argumentCrossingLevel,
      Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero, mul_zero]
  · rw [← hexp t ht]
    exact Complex.exp_ne_zero _

/-- The zero multiplicity pays for the componentwise endpoint losses.
The numerator is the balanced sum of component increments, not a total
endpoint difference containing additional zero jumps. -/
theorem argumentCrossing_component_budget
    {ι : Type*} [Fintype ι] {A B : ι → ℝ} {n : ι → ℕ} {M : ℕ}
    (hlocal : ∀ i, (B i - A i) / Real.pi - 1 ≤ n i)
    (hcomponents : Fintype.card ι ≤ M + 1) :
    (∑ i, (B i - A i)) / Real.pi - M - 1 ≤ ∑ i, (n i : ℝ) := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlocal i)
  have hsum' : (∑ i, (B i - A i)) / Real.pi - (Fintype.card ι : ℝ) ≤
      ∑ i, (n i : ℝ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] at hsum
    rw [← Finset.sum_div] at hsum
    exact hsum
  have hcard : (Fintype.card ι : ℝ) ≤ (M : ℝ) + 1 := by
    exact_mod_cast hcomponents
  linarith

/-- Choose actual interior crossing points. Distinct phase levels force
distinct real points, so the lattice lower bound is a point-count bound. -/
theorem exists_finset_argumentCrossings_of_oneSided_limits
    {g ell : ℝ → ℂ} {a b alpha beta : ℝ} (hab : a < b)
    (hell : ContinuousOn ell (Ioo a b))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell t) = g t)
    (hleft : Tendsto (fun t => (ell t).im) (nhdsWithin a (Ioi a)) (nhds alpha))
    (hright : Tendsto (fun t => (ell t).im) (nhdsWithin b (Iio b)) (nhds beta)) :
    ∃ S : Finset ℝ, (beta - alpha) / Real.pi - 1 ≤ S.card ∧
      ∀ t ∈ S, t ∈ Ioo a b ∧ (g t).re = 0 ∧ g t ≠ 0 := by
  classical
  let K := argumentCrossingInteriorIndices alpha beta
  have hcross : ∀ k : ↥K, ∃ t ∈ Ioo a b,
      (ell t).im = argumentCrossingLevel k.1 ∧ (g t).re = 0 ∧ g t ≠ 0 := by
    intro k
    exact exists_argumentCrossing_of_oneSided_limits hab hell hexp hleft hright
      (mem_argumentCrossingInteriorIndices_iff.mp k.2)
  let tau : ↥K → ℝ := fun k => Classical.choose (hcross k)
  have htau : ∀ k : ↥K, tau k ∈ Ioo a b ∧
      (ell (tau k)).im = argumentCrossingLevel k.1 ∧
      (g (tau k)).re = 0 ∧ g (tau k) ≠ 0 :=
    fun k => Classical.choose_spec (hcross k)
  have hinj : Function.Injective tau := by
    intro k l hkl
    have hlevels : argumentCrossingLevel k.1 = argumentCrossingLevel l.1 := by
      rw [← (htau k).2.1, ← (htau l).2.1, hkl]
    have hcasts : (k.1 : ℝ) = (l.1 : ℝ) := by
      unfold argumentCrossingLevel at hlevels
      nlinarith [Real.pi_pos]
    apply Subtype.ext
    exact_mod_cast hcasts
  let S := Finset.univ.image tau
  have hcard : S.card = K.card := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  refine ⟨S, ?_, ?_⟩
  · rw [hcard]
    exact argumentCrossingInteriorIndices_card_lower_bound
  · intro t ht
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨(htau k).1, (htau k).2.2⟩

/-- Sum genuine crossing points over disjoint open components. The variation
is the balanced sum of component increments; no positive zero jumps enter. -/
theorem exists_finset_argumentCrossings_of_disjoint_components
    {ι : Type*} [Fintype ι] {g : ℝ → ℂ} {ell : ι → ℝ → ℂ}
    {a b A B : ι → ℝ} {M : ℕ}
    (hab : ∀ i, a i < b i)
    (hell : ∀ i, ContinuousOn (ell i) (Ioo (a i) (b i)))
    (hexp : ∀ i, ∀ t ∈ Ioo (a i) (b i), Complex.exp (ell i t) = g t)
    (hleft : ∀ i, Tendsto (fun t => (ell i t).im)
      (nhdsWithin (a i) (Ioi (a i))) (nhds (A i)))
    (hright : ∀ i, Tendsto (fun t => (ell i t).im)
      (nhdsWithin (b i) (Iio (b i))) (nhds (B i)))
    (hdisjoint : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hcomponents : Fintype.card ι ≤ M + 1) :
    ∃ S : Finset ℝ,
      (∑ i, (B i - A i)) / Real.pi - M - 1 ≤ S.card ∧
      ∀ t ∈ S, (∃ i, t ∈ Ioo (a i) (b i)) ∧ (g t).re = 0 ∧ g t ≠ 0 := by
  classical
  have hlocal := fun i => exists_finset_argumentCrossings_of_oneSided_limits
    (hab i) (hell i) (hexp i) (hleft i) (hright i)
  let S : ι → Finset ℝ := fun i => Classical.choose (hlocal i)
  have hspec : ∀ i, (B i - A i) / Real.pi - 1 ≤ (S i).card ∧
      ∀ t ∈ S i, t ∈ Ioo (a i) (b i) ∧ (g t).re = 0 ∧ g t ≠ 0 :=
    fun i => Classical.choose_spec (hlocal i)
  have hsets : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint S := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro t hti htj
    exact Set.disjoint_left.mp (hdisjoint hij)
      ((hspec i).2 t hti).1 ((hspec j).2 t htj).1
  have hcard : (Finset.univ.biUnion S).card = ∑ i, (S i).card :=
    Finset.card_biUnion hsets
  refine ⟨Finset.univ.biUnion S, ?_, ?_⟩
  · rw [hcard, Nat.cast_sum]
    exact argumentCrossing_component_budget (fun i => (hspec i).1) hcomponents
  · intro t ht
    obtain ⟨i, _, hti⟩ := Finset.mem_biUnion.mp ht
    exact ⟨⟨i, ((hspec i).2 t hti).1⟩, ((hspec i).2 t hti).2⟩

/-- The balanced component phase increment is independent of the chosen
continuous logarithm. The same deck shift occurs at both endpoints. -/
theorem continuousLog_phase_increment_eq
    {ell₁ ell₂ : ℝ → ℂ} {a b A₁ B₁ A₂ B₂ : ℝ}
    (hab : a < b) (h₁ : ContinuousOn ell₁ (Ioo a b))
    (h₂ : ContinuousOn ell₂ (Ioo a b))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell₁ t) = Complex.exp (ell₂ t))
    (hA₁ : Tendsto (fun t => (ell₁ t).im) (nhdsWithin a (Ioi a)) (nhds A₁))
    (hB₁ : Tendsto (fun t => (ell₁ t).im) (nhdsWithin b (Iio b)) (nhds B₁))
    (hA₂ : Tendsto (fun t => (ell₂ t).im) (nhdsWithin a (Ioi a)) (nhds A₂))
    (hB₂ : Tendsto (fun t => (ell₂ t).im) (nhdsWithin b (Iio b)) (nhds B₂)) :
    B₁ - A₁ = B₂ - A₂ := by
  have hmid : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
  obtain ⟨k, hk⟩ := exists_int_continuousLogs_eq_add_two_pi_I h₁ h₂ hexp hmid
  let C : ℝ := ((k : ℂ) * (2 * Real.pi * I)).im
  have hA' : Tendsto (fun t => (ell₁ t).im) (nhdsWithin a (Ioi a))
      (nhds (A₂ + C)) := by
    apply (hA₂.add_const C).congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    simpa only [Complex.add_im] using (congrArg Complex.im (hk t ht)).symm
  have hB' : Tendsto (fun t => (ell₁ t).im) (nhdsWithin b (Iio b))
      (nhds (B₂ + C)) := by
    apply (hB₂.add_const C).congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    simpa only [Complex.add_im] using (congrArg Complex.im (hk t ht)).symm
  have hA := tendsto_nhds_unique hA₁ hA'
  have hB := tendsto_nhds_unique hB₁ hB'
  linarith

end MathlibAux
