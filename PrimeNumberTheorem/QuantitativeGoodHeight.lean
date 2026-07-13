import PrimeNumberTheorem.ExplicitFormulaAux
import PrimeNumberTheorem.NontrivialZeroMultiplicity
import ZeroFreeRegion.PhragmenLindelofZeta

open Complex Filter Set Topology

namespace PrimeNumberTheorem
namespace ExplicitFormulaAux

/-- Absolute ordinates of nontrivial zeros in the fixed-width window used to
select a quantitatively safe contour height. -/
noncomputable def localZeroHeights (A : ℝ) : Finset ℝ :=
  ((nontrivialZerosFinset (A + 2)).filter fun ρ : ℂ =>
      A - 1 / 4 ≤ |ρ.im| ∧ |ρ.im| ≤ A + 5 / 4).image fun ρ => |ρ.im|

lemma mem_localZeroHeights_of_nontrivialZero {A : ℝ} {ρ : ℂ}
    (hρ : RiemannHypothesis.IsNontrivialZero ρ)
    (hlow : A - 1 / 4 ≤ |ρ.im|) (hhigh : |ρ.im| ≤ A + 5 / 4) :
    |ρ.im| ∈ localZeroHeights A := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨ρ, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨mem_nontrivialZerosFinset.mpr ⟨hρ, ?_⟩, hlow, hhigh⟩
  linarith

/-- The number of distinct absolute ordinates in the fixed local window is
uniformly `O(log A)`.  Both signs of the ordinate are covered by fixed disks,
while functional-equation symmetry moves every zero to `Re ρ ≥ 1 / 2`. -/
theorem exists_card_localZeroHeights_le_log_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 4 ≤ A →
      ((localZeroHeights A).card : ℝ) ≤ B * (1 + Real.log (A + 6)) := by
  classical
  rcases ZeroFreeRegion.exists_finsum_divisor_riemannZeta_fixed_disk_log_bound with
    ⟨Bmass, hBmass, hmass⟩
  refine ⟨2 * Bmass, mul_nonneg (by norm_num) hBmass, ?_⟩
  intro A hA
  let t : ℝ := A + 1 / 2
  let cpos : ℂ := (2 : ℂ) + I * t
  let cneg : ℂ := (2 : ℂ) + I * ((-t : ℝ) : ℂ)
  have ht : 4 ≤ |t| := by
    rw [abs_of_nonneg (by dsimp [t]; linarith)]
    dsimp [t]
    linarith
  have hneg_t : 4 ≤ |-t| := by simpa using ht
  have havoid (s : ℝ) (hs : 4 ≤ |s|) :
      ∀ z : ℂ, z ∈ Metric.closedBall ((2 : ℂ) + I * s) (17 / 10 : ℝ) → z ≠ 1 := by
    intro z hz hzone
    subst z
    have hdist : ‖(1 : ℂ) - ((2 : ℂ) + I * s)‖ ≤ (17 / 10 : ℝ) := by
      simpa [Complex.dist_eq] using (Metric.mem_closedBall.mp hz)
    have him : |s| ≤ ‖(1 : ℂ) - ((2 : ℂ) + I * s)‖ := by
      simpa using Complex.abs_im_le_norm ((1 : ℂ) - ((2 : ℂ) + I * s))
    linarith
  rcases ZeroFreeRegion.exists_finset_riemannZeta_zeros_closedBall_card_le_divisor_mass
      (c := cpos) (r := (17 / 10 : ℝ)) (R := (17 / 10 : ℝ)) le_rfl
      (by simpa [cpos] using havoid t ht) with
    ⟨zerosPos, hzerosPos, hcardPos⟩
  rcases ZeroFreeRegion.exists_finset_riemannZeta_zeros_closedBall_card_le_divisor_mass
      (c := cneg) (r := (17 / 10 : ℝ)) (R := (17 / 10 : ℝ)) le_rfl
      (by simpa [cneg] using havoid (-t) hneg_t) with
    ⟨zerosNeg, hzerosNeg, hcardNeg⟩
  have hcardPos' : (zerosPos.card : ℝ) ≤
      ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall cpos (17 / 10 : ℝ)) u : ℝ) := by
    rw [ZeroFreeRegion.finsum_divisor_riemannZeta_closedBall_eq_finsum_mem_of_le
      (c := cpos) (b := (17 / 10 : ℝ)) (R := (17 / 10 : ℝ)) le_rfl]
    exact hcardPos
  have hcardNeg' : (zerosNeg.card : ℝ) ≤
      ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall cneg (17 / 10 : ℝ)) u : ℝ) := by
    rw [ZeroFreeRegion.finsum_divisor_riemannZeta_closedBall_eq_finsum_mem_of_le
      (c := cneg) (b := (17 / 10 : ℝ)) (R := (17 / 10 : ℝ)) le_rfl]
    exact hcardNeg
  have hright_mem (ρ : ℂ) (hρ : RiemannHypothesis.IsNontrivialZero ρ)
      (hlow : A - 1 / 4 ≤ |ρ.im|) (hhigh : |ρ.im| ≤ A + 5 / 4)
      (hre : (1 / 2 : ℝ) ≤ ρ.re) : ρ ∈ zerosPos ∪ zerosNeg := by
    have hre_high : ρ.re < 1 := hρ.2.2
    by_cases him : 0 ≤ ρ.im
    · apply Finset.mem_union.mpr
      left
      apply (hzerosPos ρ).mpr
      refine ⟨?_, hρ.1⟩
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have hlow' : A - 1 / 4 ≤ ρ.im := by simpa [abs_of_nonneg him] using hlow
      have hhigh' : ρ.im ≤ A + 5 / 4 := by simpa [abs_of_nonneg him] using hhigh
      have hsquare : ‖ρ - cpos‖ ^ 2 ≤ (17 / 10 : ℝ) ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply, cpos, t]
        nlinarith
      simpa [cpos] using
        (show ‖ρ - cpos‖ ≤ (17 / 10 : ℝ) by
          nlinarith [norm_nonneg (ρ - cpos)])
    · have him' : ρ.im < 0 := lt_of_not_ge him
      apply Finset.mem_union.mpr
      right
      apply (hzerosNeg ρ).mpr
      refine ⟨?_, hρ.1⟩
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have hlow' : A - 1 / 4 ≤ -ρ.im := by simpa [abs_of_neg him'] using hlow
      have hhigh' : -ρ.im ≤ A + 5 / 4 := by simpa [abs_of_neg him'] using hhigh
      have hsquare : ‖ρ - cneg‖ ^ 2 ≤ (17 / 10 : ℝ) ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply, cneg, t]
        nlinarith
      simpa [cneg] using
        (show ‖ρ - cneg‖ ≤ (17 / 10 : ℝ) by
          nlinarith [norm_nonneg (ρ - cneg)])
  have hsubset : localZeroHeights A ⊆
      (zerosPos ∪ zerosNeg).image fun ρ : ℂ => |ρ.im| := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨ρ, hρ, rfl⟩
    rcases Finset.mem_filter.mp hρ with ⟨hρtrunc, hlow, hhigh⟩
    have hρzero : RiemannHypothesis.IsNontrivialZero ρ :=
      (mem_nontrivialZerosFinset.mp hρtrunc).1
    by_cases hre : (1 / 2 : ℝ) ≤ ρ.re
    · exact Finset.mem_image.mpr ⟨ρ, hright_mem ρ hρzero hlow hhigh hre, rfl⟩
    · let ρ' : ℂ := 1 - ρ
      have hρ'zero : RiemannHypothesis.IsNontrivialZero ρ' := by
        simpa [ρ'] using nontrivial_zero_symmetric' hρzero
      have hre' : (1 / 2 : ℝ) ≤ ρ'.re := by
        dsimp [ρ']
        linarith
      have habs : |ρ'.im| = |ρ.im| := by simp [ρ', Complex.sub_im]
      apply Finset.mem_image.mpr
      refine ⟨ρ', hright_mem ρ' hρ'zero ?_ ?_ hre', habs⟩
      · rw [habs]
        exact hlow
      · rw [habs]
        exact hhigh
  have hcardImage : ((localZeroHeights A).card : ℝ) ≤
      (((zerosPos ∪ zerosNeg).image fun ρ : ℂ => |ρ.im|).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have himageCard :
      (((zerosPos ∪ zerosNeg).image fun ρ : ℂ => |ρ.im|).card : ℝ) ≤
        ((zerosPos ∪ zerosNeg).card : ℝ) := by
    exact_mod_cast Finset.card_image_le
  have hunionCard : ((zerosPos ∪ zerosNeg).card : ℝ) ≤
      (zerosPos.card : ℝ) + (zerosNeg.card : ℝ) := by
    exact_mod_cast Finset.card_union_le zerosPos zerosNeg
  have hmassPos := hmass t ht
  have hmassNeg := hmass (-t) hneg_t
  have hzerosPosBound : (zerosPos.card : ℝ) ≤
      Bmass * (1 + Real.log (|t| + 5)) := by
    exact hcardPos'.trans (by simpa [cpos] using hmassPos)
  have hzerosNegBound : (zerosNeg.card : ℝ) ≤
      Bmass * (1 + Real.log (|t| + 5)) := by
    exact hcardNeg'.trans (by simpa only [cneg, map_neg, abs_neg] using hmassNeg)
  have hlog : Real.log (|t| + 5) ≤ Real.log (A + 6) := by
    apply Real.log_le_log
    · positivity
    · rw [abs_of_nonneg (by dsimp [t]; linarith)]
      dsimp [t]
      linarith
  have hfactor : Bmass * (1 + Real.log (|t| + 5)) ≤
      Bmass * (1 + Real.log (A + 6)) := by
    apply mul_le_mul_of_nonneg_left _ hBmass
    linarith
  calc
    ((localZeroHeights A).card : ℝ) ≤
        (((zerosPos ∪ zerosNeg).image fun ρ : ℂ => |ρ.im|).card : ℝ) := hcardImage
    _ ≤ ((zerosPos ∪ zerosNeg).card : ℝ) := himageCard
    _ ≤ (zerosPos.card : ℝ) + (zerosNeg.card : ℝ) := hunionCard
    _ ≤ 2 * Bmass * (1 + Real.log (A + 6)) := by
      nlinarith [hzerosPosBound.trans hfactor, hzerosNegBound.trans hfactor]

/-- Total analytic multiplicity of nontrivial zeros in the fixed-width window
used by the quantitative good-height construction. -/
noncomputable def localZeroMultiplicity (A : ℝ) : ℝ :=
  ∑ ρ ∈ (nontrivialZerosFinset (A + 2)).filter fun ρ : ℂ =>
      A - 1 / 4 ≤ |ρ.im| ∧ |ρ.im| ≤ A + 5 / 4,
    (analyticOrderNatAt riemannZeta ρ : ℝ)

/-- The total multiplicity, rather than merely the number of distinct
ordinates, of nontrivial zeros in the local contour window is `O(log A)`. -/
theorem exists_localZeroMultiplicity_le_log_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 4 ≤ A →
      localZeroMultiplicity A ≤ B * (1 + Real.log (A + 6)) := by
  classical
  rcases ZeroFreeRegion.exists_finsum_divisor_riemannZeta_fixed_disk_log_bound with
    ⟨Bmass, hBmass, hmass⟩
  refine ⟨4 * Bmass, mul_nonneg (by norm_num) hBmass, ?_⟩
  intro A hA
  let S : Finset ℂ :=
    (nontrivialZerosFinset (A + 2)).filter fun ρ : ℂ =>
      A - 1 / 4 ≤ |ρ.im| ∧ |ρ.im| ≤ A + 5 / 4
  let Sright : Finset ℂ := S.filter fun ρ : ℂ => (1 / 2 : ℝ) ≤ ρ.re
  let Sleft : Finset ℂ := S.filter fun ρ : ℂ => ¬(1 / 2 : ℝ) ≤ ρ.re
  let SleftImage : Finset ℂ := Sleft.image fun ρ : ℂ => 1 - ρ
  let Spos : Finset ℂ := Sright.filter fun ρ : ℂ => 0 ≤ ρ.im
  let Sneg : Finset ℂ := Sright.filter fun ρ : ℂ => ¬0 ≤ ρ.im
  let t : ℝ := A + 1 / 2
  let cpos : ℂ := (2 : ℂ) + I * t
  let cneg : ℂ := (2 : ℂ) + I * ((-t : ℝ) : ℂ)
  have ht : 4 ≤ |t| := by
    rw [abs_of_nonneg (by dsimp [t]; linarith)]
    dsimp [t]
    linarith
  have hneg_t : 4 ≤ |-t| := by simpa using ht
  have havoid (s : ℝ) (hs : 4 ≤ |s|) :
      ∀ z : ℂ, z ∈ Metric.closedBall ((2 : ℂ) + I * s) (17 / 10 : ℝ) → z ≠ 1 := by
    intro z hz hzone
    subst z
    have hdist : ‖(1 : ℂ) - ((2 : ℂ) + I * s)‖ ≤ (17 / 10 : ℝ) := by
      simpa [Complex.dist_eq] using (Metric.mem_closedBall.mp hz)
    have him : |s| ≤ ‖(1 : ℂ) - ((2 : ℂ) + I * s)‖ := by
      simpa using Complex.abs_im_le_norm ((1 : ℂ) - ((2 : ℂ) + I * s))
    linarith
  have hS_data (ρ : ℂ) (hρS : ρ ∈ S) :
      RiemannHypothesis.IsNontrivialZero ρ ∧
        A - 1 / 4 ≤ |ρ.im| ∧ |ρ.im| ≤ A + 5 / 4 := by
    rcases Finset.mem_filter.mp hρS with ⟨hρtrunc, hlow, hhigh⟩
    exact ⟨(mem_nontrivialZerosFinset.mp hρtrunc).1, hlow, hhigh⟩
  have hreflect_mem (ρ : ℂ) (hρ : ρ ∈ Sleft) : 1 - ρ ∈ Sright := by
    rcases Finset.mem_filter.mp hρ with ⟨hρS, hre_not⟩
    rcases Finset.mem_filter.mp hρS with ⟨hρtrunc, hlow, hhigh⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨one_sub_mem_nontrivialZerosFinset hρtrunc, ?_, ?_⟩, ?_⟩
    · simpa [Complex.sub_im] using hlow
    · simpa [Complex.sub_im] using hhigh
    · simp only [Complex.sub_re, Complex.one_re]
      linarith [lt_of_not_ge hre_not]
  have hreflect_injective : Function.Injective (fun ρ : ℂ => 1 - ρ) := by
    intro ρ σ h
    calc
      ρ = 1 - (1 - ρ) := by ring
      _ = 1 - (1 - σ) := congrArg (fun z : ℂ => 1 - z) h
      _ = σ := by ring
  have hleftImage_subset : SleftImage ⊆ Sright := by
    intro ρ hρ
    rcases Finset.mem_image.mp hρ with ⟨z, hz, rfl⟩
    exact hreflect_mem z hz
  have hsum_left_image :
      (∑ ρ ∈ SleftImage, (analyticOrderNatAt riemannZeta ρ : ℝ)) =
        ∑ ρ ∈ Sleft, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    rw [show SleftImage = Sleft.image (fun ρ : ℂ => 1 - ρ) by rfl,
      Finset.sum_image (fun ρ _hρ σ _hσ h => hreflect_injective h)]
    apply Finset.sum_congr rfl
    intro ρ hρ
    exact_mod_cast
      analyticOrderNatAt_riemannZeta_one_sub_of_nontrivialZero
        (hS_data ρ (Finset.mem_filter.mp hρ).1).1
  have hleft_le_right :
      (∑ ρ ∈ Sleft, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        ∑ ρ ∈ Sright, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    rw [← hsum_left_image]
    apply Finset.sum_le_sum_of_subset_of_nonneg hleftImage_subset
    intro ρ _hρ _hnot
    exact Nat.cast_nonneg _
  have hpos_disk (ρ : ℂ) (hρ : ρ ∈ Spos) :
      ρ ∈ Metric.closedBall cpos (17 / 10 : ℝ) := by
    rcases Finset.mem_filter.mp hρ with ⟨hρright, him⟩
    rcases Finset.mem_filter.mp hρright with ⟨hρS, hre⟩
    rcases hS_data ρ hρS with ⟨hzero, hlow, hhigh⟩
    rw [Metric.mem_closedBall, Complex.dist_eq]
    have hlow' : A - 1 / 4 ≤ ρ.im := by simpa [abs_of_nonneg him] using hlow
    have hhigh' : ρ.im ≤ A + 5 / 4 := by simpa [abs_of_nonneg him] using hhigh
    have hsquare : ‖ρ - cpos‖ ^ 2 ≤ (17 / 10 : ℝ) ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply, cpos, t]
      nlinarith [hzero.2.2]
    simpa [cpos] using
      (show ‖ρ - cpos‖ ≤ (17 / 10 : ℝ) by
        nlinarith [norm_nonneg (ρ - cpos)])
  have hneg_disk (ρ : ℂ) (hρ : ρ ∈ Sneg) :
      ρ ∈ Metric.closedBall cneg (17 / 10 : ℝ) := by
    rcases Finset.mem_filter.mp hρ with ⟨hρright, him_not⟩
    rcases Finset.mem_filter.mp hρright with ⟨hρS, hre⟩
    rcases hS_data ρ hρS with ⟨hzero, hlow, hhigh⟩
    have him : ρ.im < 0 := lt_of_not_ge him_not
    rw [Metric.mem_closedBall, Complex.dist_eq]
    have hlow' : A - 1 / 4 ≤ -ρ.im := by simpa [abs_of_neg him] using hlow
    have hhigh' : -ρ.im ≤ A + 5 / 4 := by simpa [abs_of_neg him] using hhigh
    have hsquare : ‖ρ - cneg‖ ^ 2 ≤ (17 / 10 : ℝ) ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply, cneg, t]
      nlinarith [hzero.2.2]
    simpa [cneg] using
      (show ‖ρ - cneg‖ ≤ (17 / 10 : ℝ) by
        nlinarith [norm_nonneg (ρ - cneg)])
  have hpos_mass :
      (∑ ρ ∈ Spos, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
          (Metric.closedBall cpos (17 / 10 : ℝ)) u : ℝ) := by
    apply sum_analyticOrderNatAt_riemannZeta_le_finsum_divisor_closedBall
      Spos (by simpa [cpos] using havoid t ht)
    intro ρ hρ
    exact ⟨(hS_data ρ (Finset.mem_filter.mp
      (Finset.mem_filter.mp hρ).1).1).1, hpos_disk ρ hρ⟩
  have hneg_mass :
      (∑ ρ ∈ Sneg, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
          (Metric.closedBall cneg (17 / 10 : ℝ)) u : ℝ) := by
    apply sum_analyticOrderNatAt_riemannZeta_le_finsum_divisor_closedBall
      Sneg (by simpa [cneg] using havoid (-t) hneg_t)
    intro ρ hρ
    exact ⟨(hS_data ρ (Finset.mem_filter.mp
      (Finset.mem_filter.mp hρ).1).1).1, hneg_disk ρ hρ⟩
  have hmassPos := hmass t ht
  have hmassNeg := hmass (-t) hneg_t
  have hpos_bound :
      (∑ ρ ∈ Spos, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        Bmass * (1 + Real.log (|t| + 5)) :=
    hpos_mass.trans (by simpa [cpos] using hmassPos)
  have hneg_bound :
      (∑ ρ ∈ Sneg, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        Bmass * (1 + Real.log (|t| + 5)) :=
    hneg_mass.trans (by simpa only [cneg, map_neg, abs_neg] using hmassNeg)
  have hright_split :
      (∑ ρ ∈ Sright, (analyticOrderNatAt riemannZeta ρ : ℝ)) =
        (∑ ρ ∈ Spos, (analyticOrderNatAt riemannZeta ρ : ℝ)) +
          ∑ ρ ∈ Sneg, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    symm
    exact Finset.sum_filter_add_sum_filter_not Sright
      (fun ρ : ℂ => 0 ≤ ρ.im)
      (fun ρ : ℂ => (analyticOrderNatAt riemannZeta ρ : ℝ))
  have htotal_split :
      (∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ)) =
        (∑ ρ ∈ Sright, (analyticOrderNatAt riemannZeta ρ : ℝ)) +
          ∑ ρ ∈ Sleft, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    symm
    exact Finset.sum_filter_add_sum_filter_not S
      (fun ρ : ℂ => (1 / 2 : ℝ) ≤ ρ.re)
      (fun ρ : ℂ => (analyticOrderNatAt riemannZeta ρ : ℝ))
  have hlog : Real.log (|t| + 5) ≤ Real.log (A + 6) := by
    apply Real.log_le_log
    · positivity
    · rw [abs_of_nonneg (by dsimp [t]; linarith)]
      dsimp [t]
      linarith
  have hfactor : Bmass * (1 + Real.log (|t| + 5)) ≤
      Bmass * (1 + Real.log (A + 6)) := by
    apply mul_le_mul_of_nonneg_left _ hBmass
    linarith
  have hright_bound :
      (∑ ρ ∈ Sright, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        2 * Bmass * (1 + Real.log (A + 6)) := by
    rw [hright_split]
    nlinarith [hpos_bound.trans hfactor, hneg_bound.trans hfactor]
  change localZeroMultiplicity A ≤ _
  rw [show localZeroMultiplicity A =
      ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) by
    rfl, htotal_split]
  nlinarith [hleft_le_right, hright_bound]

/-- Sum of the norms of the multiplicity-weighted explicit-formula terms in
the fixed-width local zero window. -/
noncomputable def localZeroContributionNorm (x A : ℝ) : ℝ :=
  ∑ ρ ∈ (nontrivialZerosFinset (A + 2)).filter fun ρ : ℂ =>
      A - 1 / 4 ≤ |ρ.im| ∧ |ρ.im| ≤ A + 5 / 4,
    ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖

/-- A fixed-width window contributes `O_x(log A / A)` to the
multiplicity-weighted explicit-formula zero sum. -/
theorem exists_localZeroContributionNorm_le_log_div
    {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      localZeroContributionNorm x A ≤
        C * x * (1 + Real.log (A + 6)) / (A - 1 / 2) := by
  classical
  rcases exists_localZeroMultiplicity_le_log_bound with ⟨C, hC, hmult⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  let S : Finset ℂ :=
    (nontrivialZerosFinset (A + 2)).filter fun ρ : ℂ =>
      A - 1 / 4 ≤ |ρ.im| ∧ |ρ.im| ≤ A + 5 / 4
  have hden : 0 < A - 1 / 2 := by linarith
  have hpoint (ρ : ℂ) (hρ : ρ ∈ S) :
      ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        (analyticOrderNatAt riemannZeta ρ : ℝ) * x / (A - 1 / 2) := by
    rcases Finset.mem_filter.mp hρ with ⟨hρtrunc, hlow, _hhigh⟩
    have hzero := (mem_nontrivialZerosFinset.mp hρtrunc).1
    apply norm_multiplicity_zero_contribution_le_div_height hx hden hzero
    linarith
  have hsum : localZeroContributionNorm x A ≤
      ∑ ρ ∈ S,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * x / (A - 1 / 2) := by
    dsimp [localZeroContributionNorm, S]
    exact Finset.sum_le_sum fun ρ hρ => hpoint ρ hρ
  have hrewrite :
      (∑ ρ ∈ S,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * x / (A - 1 / 2)) =
        x / (A - 1 / 2) * localZeroMultiplicity A := by
    dsimp [localZeroMultiplicity, S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _hρ
    ring
  rw [hrewrite] at hsum
  calc
    localZeroContributionNorm x A ≤
        x / (A - 1 / 2) * localZeroMultiplicity A := hsum
    _ ≤ x / (A - 1 / 2) * (C * (1 + Real.log (A + 6))) := by
      apply mul_le_mul_of_nonneg_left (hmult A hA)
      exact div_nonneg (zero_lt_one.trans hx).le hden.le
    _ = C * x * (1 + Real.log (A + 6)) / (A - 1 / 2) := by ring

/-- The contribution of any fixed-width high zero window vanishes as the
window moves to infinite height. -/
theorem tendsto_localZeroContributionNorm_atTop
    {x : ℝ} (hx : 1 < x) :
    Tendsto (localZeroContributionNorm x) atTop (𝓝 0) := by
  rcases exists_localZeroContributionNorm_le_log_div hx with ⟨C, _hC, hbound⟩
  have hshift : Tendsto (fun A : ℝ => A + 6) atTop atTop :=
    tendsto_atTop_add_const_right atTop 6 tendsto_id
  have hpow (k : ℕ) : Tendsto
      (fun A : ℝ => Real.log (A + 6) ^ k / (A - 1 / 2))
      atTop (𝓝 0) := by
    have hreal :=
      (Real.tendsto_pow_log_div_mul_add_atTop
        1 (-13 / 2) k one_ne_zero).comp hshift
    convert hreal using 1
    funext A
    dsimp [Function.comp_def]
    congr 1
    ring
  have hratio : Tendsto
      (fun A : ℝ => (1 + Real.log (A + 6)) / (A - 1 / 2))
      atTop (𝓝 0) := by
    have hsum := (hpow 0).add (hpow 1)
    simpa only [pow_zero, pow_one, zero_add] using hsum.congr' (by
      filter_upwards [] with A
      ring)
  have hupper : Tendsto
      (fun A : ℝ => C * x * (1 + Real.log (A + 6)) / (A - 1 / 2))
      atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hratio.const_mul (C * x)
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [] with A
    exact Finset.sum_nonneg fun ρ _hρ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with A hA
    exact hbound A hA

/-- Every unit interval contains a height separated from every nontrivial-zero
ordinate by an explicit pigeonhole distance.  Unlike `exists_goodHeight_Ioo`,
this theorem gives the quantitative input needed to bound principal parts of
`zeta'/zeta` on a horizontal contour. -/
theorem exists_goodHeight_Icc_quantitatively_separated (A : ℝ) :
    ∃ T ∈ Set.Icc A (A + 1),
      goodHeight T ∧
        ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ →
          1 / ((4 : ℝ) * (((localZeroHeights A).card : ℝ) + 1)) ≤
            |T - abs ρ.im| := by
  classical
  let H := localZeroHeights A
  rcases ZeroFreeRegion.exists_radius_separated_from_finset H
      (show A < A + 1 by linarith) with ⟨T, hT, hsep⟩
  have hdelta_pos :
      0 < 1 / ((4 : ℝ) * ((H.card : ℝ) + 1)) := by positivity
  have hdelta_quarter :
      1 / ((4 : ℝ) * ((H.card : ℝ) + 1)) ≤ 1 / 4 := by
    have hone : (1 : ℝ) ≤ (H.card : ℝ) + 1 := by
      have hcard : (0 : ℝ) ≤ (H.card : ℝ) := by positivity
      linarith
    have hden : (4 : ℝ) ≤ 4 * ((H.card : ℝ) + 1) := by nlinarith
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hall : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ →
      1 / ((4 : ℝ) * ((H.card : ℝ) + 1)) ≤ |T - abs ρ.im| := by
    intro ρ hρ
    by_cases hlow : A - 1 / 4 ≤ |ρ.im|
    · by_cases hhigh : |ρ.im| ≤ A + 5 / 4
      · have hmem : |ρ.im| ∈ H := by
          simpa [H] using mem_localZeroHeights_of_nontrivialZero hρ hlow hhigh
        simpa [H] using hsep |ρ.im| hmem
      · have hfar : 1 / 4 ≤ |T - abs ρ.im| := by
          have hheight : A + 5 / 4 < |ρ.im| := lt_of_not_ge hhigh
          rw [abs_of_nonpos]
          · linarith [hT.2]
          · linarith [hT.2]
        exact hdelta_quarter.trans hfar
    · have hfar : 1 / 4 ≤ |T - abs ρ.im| := by
        have hheight : |ρ.im| < A - 1 / 4 := lt_of_not_ge hlow
        rw [abs_of_nonneg]
        · linarith [hT.1]
        · linarith [hT.1]
      exact hdelta_quarter.trans hfar
  refine ⟨T, hT, ?_, ?_⟩
  · intro ρ hρ heq
    have h := hall ρ hρ
    rw [← heq, sub_self, abs_zero] at h
    exact (not_lt_of_ge h) hdelta_pos
  · simpa [H] using hall

/-- Every sufficiently high unit interval contains a contour height whose
distance from every nontrivial-zero ordinate has an explicit logarithmic lower
bound.  This packages the local Jensen zero count with the quantitative
finite-set avoidance theorem. -/
theorem exists_goodHeight_Icc_logarithmically_separated :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        goodHeight T ∧
          ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ →
            1 / ((4 : ℝ) * (B * (1 + Real.log (A + 6)) + 1)) ≤
              |T - abs ρ.im| := by
  rcases exists_card_localZeroHeights_le_log_bound with ⟨B, hB, hcard⟩
  refine ⟨B, hB, ?_⟩
  intro A hA
  rcases exists_goodHeight_Icc_quantitatively_separated A with
    ⟨T, hT, hgood, hsep⟩
  refine ⟨T, hT, hgood, ?_⟩
  have hcardA := hcard A hA
  have hden :
      (4 : ℝ) * (((localZeroHeights A).card : ℝ) + 1) ≤
        4 * (B * (1 + Real.log (A + 6)) + 1) := by
    nlinarith
  have hden_pos :
      0 < (4 : ℝ) * (((localZeroHeights A).card : ℝ) + 1) := by
    positivity
  intro ρ hρ
  exact (one_div_le_one_div_of_le hden_pos hden).trans (hsep ρ hρ)

end ExplicitFormulaAux
end PrimeNumberTheorem
