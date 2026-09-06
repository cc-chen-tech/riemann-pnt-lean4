import PrimeNumberTheorem.WindowedMellinResponseIdentity
import PrimeNumberTheorem.WindowedMellinL3
import PrimeNumberTheorem.GlobalZeroCount
import ZeroFreeRegion.MeromorphicAux

/-!
# L3 capstone: the windowed detector conclusion

The final L3 assembly documented in
`docs/research/2026-08-24-pr474-windowed-detector-single-layer-forcing.md`:
under the counterfactual decomposition of the truncated zero set into the
seed, the outside-window top layer and the complementary layer, the
truncated explicit formula (L2 identity), the two coefficient bounds
(round 41) and the exponent budgets contradict the hypothesis that the
windowed response equals the accounted sum — provided the seed signal
*exceeds* that sum (the oscillation witness).  Hence, if the seed's
signal is present in `[T0, T0+H]`, some accounted-for source is missing —
the gate's `hbranch` successor: a top-layer zero in the window.

All analytic inputs (the truncated explicit formula `hexplicit`, its
error `herr`, the budgets, the seed signal) are explicit parameters; when
the cubic line discharges `hexplicit`/`herr` and the vk-edge witness
discharges the signal, the axiom audit of the route closes at zero.
-/

namespace PrimeNumberTheorem
namespace WindowedMellinL3

open Complex
open Filter
open MeasureTheory
open scoped BigOperators
open ExplicitFormulaAux

/-- L3 CAPSTONE: the accounted-sum response bound contradicts the seed
signal excess. -/
theorem windowedDetector_contradicts_noTopLayerZero
    {lam gap β h T0 H γ : ℝ} {seed : ℂ} {top complementary : Finset ℂ} {Err : ℝ → ℂ}
    {MassA MassB : ℝ} {KA Ce : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hT0 : 0 < T0) (hH : 0 < H)
    (hβ : 0 < β) (hgap : 0 < gap) (hhsmall : h ≤ Real.log 2)
    (hCe : 0 ≤ Ce)
    (hdisj1 : seed ∉ top) (hdisj2 : seed ∉ complementary) (hdisj : Disjoint top complementary)
    (hseed : RiemannHypothesis.IsNontrivialZero seed) (hseed_re : seed.re = β)
    (hz_seed : seed - Complex.I * γ ≠ 0) (hγavoid_seed : γ ≠ seed.im)
    (hzero_top : ∀ ρ ∈ top, RiemannHypothesis.IsNontrivialZero ρ)
    (hre_top : ∀ ρ ∈ top, ρ.re = β)
    (hz_top : ∀ ρ ∈ top, ρ - Complex.I * γ ≠ 0)
    (hγavoid_top : ∀ ρ ∈ top, γ ≠ ρ.im)
    (hhigh_top : ∀ ρ ∈ top, T0 / 2 ≤ ρ.im)
    (hzero_comp : ∀ ρ ∈ complementary, RiemannHypothesis.IsNontrivialZero ρ)
    (hre_comp : ∀ ρ ∈ complementary, ρ.re ≤ β - gap)
    (hz_comp : ∀ ρ ∈ complementary, ρ - Complex.I * γ ≠ 0)
    (hγavoid_comp : ∀ ρ ∈ complementary, γ ≠ ρ.im)
    (hhigh_comp : ∀ ρ ∈ complementary, T0 / 2 ≤ ρ.im)
    (hMassA : (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤ MassA)
    (hMassB : (complementary.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤ MassB)
    (hErrCont : Continuous Err)
    (hexplicit : ∀ᶠ x in atTop, (WindowedMellinL2.centeredSecondDifferencePsi x h : ℂ) =
        (({seed} ∪ top ∪ complementary).sum fun ρ =>
          ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2) +
          Err x)
    (hErrBound : ∀ᶠ x in atTop, ‖Err x‖ ≤ Ce * x ^ (1 - 1 / 20 : ℝ))
    (hbudgetA : ∀ᶠ X in atTop, max 4 (36 / (h * (T0 / 2)) ^ 2) * 4 * X ^ (lam * β) / T0 * MassA <
      X ^ (lam * β) / (16 * β * (T0 + H)))
    (hbudgetB : ∀ᶠ X in atTop, max 4 (36 / (h * (T0 / 2)) ^ 2) * 4 * X ^ (lam * (β - gap)) / T0 * MassB <
      X ^ (lam * β) / (16 * β * (T0 + H)))
    (hbudgetErr : ∀ᶠ X in atTop, Ce * (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)) <
      X ^ (lam * β) / (16 * β * (T0 + H)))
    (hsignal : ∀ᶠ X in atTop,
      ‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ‖ +
        X ^ (lam * β) / (16 * β * (T0 + H)) * 3 <
        ‖WindowedMellinL2.windowedResponse X lam h γ‖) :
    False := by
  -- the identity over the truncated set
  have hne_of_zero {ρ : ℂ} (hz : RiemannHypothesis.IsNontrivialZero ρ) : ρ ≠ 0 := by
    intro hz0
    have hpos := hz.2.1
    rw [hz0] at hpos
    norm_num at hpos
  have hnonzero_all : ∀ ρ ∈ ({seed} ∪ top ∪ complementary), ρ ≠ 0 := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h | h
    · rcases Finset.mem_union.mp h with h1 | h2
      · rw [Finset.mem_singleton.mp h1]
        exact hne_of_zero hseed
      · exact hne_of_zero (hzero_top ρ h2)
    · exact hne_of_zero (hzero_comp ρ h)
  have hz_all : ∀ ρ ∈ ({seed} ∪ top ∪ complementary), ρ - Complex.I * γ ≠ 0 := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h | h
    · rcases Finset.mem_union.mp h with h1 | h2
      · rw [Finset.mem_singleton.mp h1]
        exact hz_seed
      · exact hz_top ρ h2
    · exact hz_comp ρ h
  have hident := WindowedMellinL2.windowedMellinResponse_eq_sum_add_error
    (lam := lam) (h := h) (γ := γ) (Ce := Ce) ({seed} ∪ top ∪ complementary) Err
    hlam hh hErrCont hCe hnonzero_all hz_all hexplicit hErrBound
  have hcontra {X : ℝ} (hX1 : 1 < X)
      (hid : ‖WindowedMellinL2.windowedResponse X lam h γ - (({seed} ∪ top ∪ complementary).sum fun ρ =>
        WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ)‖ ≤
        Ce * (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)))
      (hA' : max 4 (36 / (h * (T0 / 2)) ^ 2) * 4 * X ^ (lam * β) / T0 * MassA <
        X ^ (lam * β) / (16 * β * (T0 + H)))
      (hB' : max 4 (36 / (h * (T0 / 2)) ^ 2) * 4 * X ^ (lam * (β - gap)) / T0 * MassB <
        X ^ (lam * β) / (16 * β * (T0 + H)))
      (hE' : Ce * (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)) < X ^ (lam * β) / (16 * β * (T0 + H)))
      (hsig : ‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ‖ +
        X ^ (lam * β) / (16 * β * (T0 + H)) * 3 < ‖WindowedMellinL2.windowedResponse X lam h γ‖) :
      False := by
    have hXpos : 0 < X := lt_trans zero_lt_one hX1
    have hXlam0 : 0 < X ^ lam := Real.rpow_pos_of_pos hXpos lam
    have hA : (top.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖) <
        X ^ (lam * β) / (16 * β * (T0 + H)) := by
      have hb := topLayerCoeffResponseSum_le
        (X := X) (lam := lam) (β := β) (h := h) (T0 := T0) (γ := γ) (Mass := MassA)
        hX1 hlam hh hT0 hhsmall hzero_top hre_top hz_top hγavoid_top hhigh_top hMassA
      have hbrid : (top.sum fun ρ =>
            ‖WindowedMellinL2.zeroResponseCoeff ρ h * ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) =
          (top.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖) := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [WindowedMellinL2.integral_cpow_eq_integralFactor hXpos hXlam0 (hz_top ρ hρ)]
      rw [hbrid] at hb
      exact hb.trans_lt hA'
    have hB : (complementary.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖) <
        X ^ (lam * β) / (16 * β * (T0 + H)) := by
      have hb := complementaryCoeffResponseSum_le
        (X := X) (lam := lam) (gap := gap) (β := β) (h := h) (T0 := T0) (γ := γ) (Mass := MassB)
        hX1 hlam hh hT0 hhsmall hzero_comp hre_comp hz_comp hγavoid_comp hhigh_comp hMassB
      have hbrid : (complementary.sum fun ρ =>
            ‖WindowedMellinL2.zeroResponseCoeff ρ h * ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) =
          (complementary.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖) := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [WindowedMellinL2.integral_cpow_eq_integralFactor hXpos hXlam0 (hz_comp ρ hρ)]
      rw [hbrid] at hb
      exact hb.trans_lt hB'
    have hsum_split : (({seed} ∪ top ∪ complementary).sum fun ρ =>
        WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ) =
        WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ +
          (top.sum fun ρ => WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ) +
          (complementary.sum fun ρ => WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ) := by
      rw [Finset.sum_union]
      · rw [Finset.sum_union]
        · simp
        · exact Finset.disjoint_singleton_left.mpr hdisj1
      · exact Finset.disjoint_left.mpr (fun ρ hρ => by
          rcases Finset.mem_union.mp hρ with h1 | h2
          · have hρseed : ρ = seed := Finset.mem_singleton.mp h1
            simpa [← hρseed] using hdisj2
          · exact Finset.disjoint_left.mp hdisj h2)
    have htrunc : ‖(({seed} ∪ top ∪ complementary).sum fun ρ =>
        WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ)‖ ≤
        (‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ‖ +
          (top.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖)) +
          (complementary.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖) := by
      rw [hsum_split]
      calc
        ‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ +
              (top.sum fun ρ => WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ) +
              (complementary.sum fun ρ => WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ)‖ ≤
            ‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ +
              (top.sum fun ρ => WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ)‖ +
              ‖complementary.sum fun ρ => WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖ :=
          norm_add_le _ _
        _ ≤ (‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ‖ +
              ‖top.sum fun ρ => WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖) +
              ‖complementary.sum fun ρ => WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖ := by
          exact add_le_add_left (norm_add_le _ _) _
        _ ≤ (‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ‖ +
              (top.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖)) +
              ‖complementary.sum fun ρ => WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖ := by
          exact add_le_add_left (add_le_add_right (norm_sum_le _ _) _) _
        _ ≤ (‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ‖ +
              (top.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖)) +
              (complementary.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖) := by
          exact add_le_add_right (norm_sum_le _ _) _
    have hwr : ‖WindowedMellinL2.windowedResponse X lam h γ‖ ≤
        ‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ‖ +
          (top.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖) +
          (complementary.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖) +
          Ce * (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)) := by
      calc
        ‖WindowedMellinL2.windowedResponse X lam h γ‖ =
            ‖(WindowedMellinL2.windowedResponse X lam h γ - (({seed} ∪ top ∪ complementary).sum fun ρ =>
              WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ)) +
              (({seed} ∪ top ∪ complementary).sum fun ρ =>
                WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ)‖ := by
          ring_nf
        _ ≤ ‖WindowedMellinL2.windowedResponse X lam h γ - (({seed} ∪ top ∪ complementary).sum fun ρ =>
              WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ)‖ +
              ‖(({seed} ∪ top ∪ complementary).sum fun ρ =>
                WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ)‖ :=
          norm_add_le _ _
        _ ≤ Ce * (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)) +
              (‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ‖ +
                (top.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖) +
                (complementary.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖)) := by
          exact add_le_add hid htrunc
        _ = ‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ‖ +
              (top.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖) +
              (complementary.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ‖) +
              Ce * (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)) := by ring
    nlinarith [hwr, hA, hB, hE', hsig]
  have hX1ev : ∀ᶠ X in atTop, (1 : ℝ) < X := Filter.eventually_gt_atTop (1 : ℝ)
  have hall : ∀ᶠ X in atTop, ((1 : ℝ) < X) ∧
      ‖WindowedMellinL2.windowedResponse X lam h γ - (({seed} ∪ top ∪ complementary).sum fun ρ =>
        WindowedMellinL2.zeroResponseCoeff ρ h * WindowedMellinL2.integralFactor ρ X lam γ)‖ ≤
        Ce * (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)) ∧
      max 4 (36 / (h * (T0 / 2)) ^ 2) * 4 * X ^ (lam * β) / T0 * MassA <
        X ^ (lam * β) / (16 * β * (T0 + H)) ∧
      max 4 (36 / (h * (T0 / 2)) ^ 2) * 4 * X ^ (lam * (β - gap)) / T0 * MassB <
        X ^ (lam * β) / (16 * β * (T0 + H)) ∧
      Ce * (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)) < X ^ (lam * β) / (16 * β * (T0 + H)) ∧
      ‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ‖ +
        X ^ (lam * β) / (16 * β * (T0 + H)) * 3 < ‖WindowedMellinL2.windowedResponse X lam h γ‖ := by
    exact Filter.Eventually.and hX1ev (Filter.Eventually.and hident (Filter.Eventually.and hbudgetA
      (Filter.Eventually.and hbudgetB (Filter.Eventually.and hbudgetErr hsignal))))
  rcases Filter.Eventually.exists hall with ⟨X, hX1, hid, hA, hB, hE, hsig⟩
  exact hcontra hX1 hid hA hB hE hsig

/-- Extraction: under the capstone hypotheses, the top layer's
frequency-weighted mass must *exceed* the budget `MassA` — equivalently the
top-layer window packet cannot be empty once the seed signal, the identity
and the complementary budget hold.  This is the negative-information form of
`windowedDetector_contradicts_noTopLayerZero`, used by the gate's `hbranch`
supplier to force successors. -/
theorem windowedDetector_topLayerMass_exceeds
    {lam gap β h T0 H γ : ℝ} {seed : ℂ} {top complementary : Finset ℂ} {Err : ℝ → ℂ}
    {MassA MassB : ℝ} {KA Ce : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hT0 : 0 < T0) (hH : 0 < H)
    (hβ : 0 < β) (hgap : 0 < gap) (hhsmall : h ≤ Real.log 2)
    (hCe : 0 ≤ Ce)
    (hdisj1 : seed ∉ top) (hdisj2 : seed ∉ complementary) (hdisj : Disjoint top complementary)
    (hseed : RiemannHypothesis.IsNontrivialZero seed) (hseed_re : seed.re = β)
    (hz_seed : seed - Complex.I * γ ≠ 0) (hγavoid_seed : γ ≠ seed.im)
    (hzero_top : ∀ ρ ∈ top, RiemannHypothesis.IsNontrivialZero ρ)
    (hre_top : ∀ ρ ∈ top, ρ.re = β)
    (hz_top : ∀ ρ ∈ top, ρ - Complex.I * γ ≠ 0)
    (hγavoid_top : ∀ ρ ∈ top, γ ≠ ρ.im)
    (hhigh_top : ∀ ρ ∈ top, T0 / 2 ≤ ρ.im)
    (hzero_comp : ∀ ρ ∈ complementary, RiemannHypothesis.IsNontrivialZero ρ)
    (hre_comp : ∀ ρ ∈ complementary, ρ.re ≤ β - gap)
    (hz_comp : ∀ ρ ∈ complementary, ρ - Complex.I * γ ≠ 0)
    (hγavoid_comp : ∀ ρ ∈ complementary, γ ≠ ρ.im)
    (hhigh_comp : ∀ ρ ∈ complementary, T0 / 2 ≤ ρ.im)
    (hMassB : (complementary.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤ MassB)
    (hErrCont : Continuous Err)
    (hexplicit : ∀ᶠ x in atTop, (WindowedMellinL2.centeredSecondDifferencePsi x h : ℂ) =
        (({seed} ∪ top ∪ complementary).sum fun ρ =>
          ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2) +
          Err x)
    (hErrBound : ∀ᶠ x in atTop, ‖Err x‖ ≤ Ce * x ^ (1 - 1 / 20 : ℝ))
    (hbudgetA : ∀ᶠ X in atTop, max 4 (36 / (h * (T0 / 2)) ^ 2) * 4 * X ^ (lam * β) / T0 * MassA <
      X ^ (lam * β) / (16 * β * (T0 + H)))
    (hbudgetB : ∀ᶠ X in atTop, max 4 (36 / (h * (T0 / 2)) ^ 2) * 4 * X ^ (lam * (β - gap)) / T0 * MassB <
      X ^ (lam * β) / (16 * β * (T0 + H)))
    (hbudgetErr : ∀ᶠ X in atTop, Ce * (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)) <
      X ^ (lam * β) / (16 * β * (T0 + H)))
    (hsignal : ∀ᶠ X in atTop,
      ‖WindowedMellinL2.zeroResponseCoeff seed h * WindowedMellinL2.integralFactor seed X lam γ‖ +
        X ^ (lam * β) / (16 * β * (T0 + H)) * 3 <
        ‖WindowedMellinL2.windowedResponse X lam h γ‖) :
    MassA < (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
  by_contra hnot
  have hMassA : (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤ MassA :=
    le_of_not_gt hnot
  exact windowedDetector_contradicts_noTopLayerZero
    (lam := lam) (gap := gap) (β := β) (h := h) (T0 := T0) (H := H) (γ := γ)
    (seed := seed) (top := top) (complementary := complementary) (Err := Err)
    (MassA := MassA) (MassB := MassB) (KA := KA) (Ce := Ce)
    hlam hh hT0 hH hβ hgap hhsmall hCe
    hdisj1 hdisj2 hdisj hseed hseed_re hz_seed hγavoid_seed
    hzero_top hre_top hz_top hγavoid_top hhigh_top
    hzero_comp hre_comp hz_comp hγavoid_comp hhigh_comp
    hMassA hMassB hErrCont hexplicit hErrBound hbudgetA hbudgetB hbudgetErr hsignal

end WindowedMellinL3
end PrimeNumberTheorem
