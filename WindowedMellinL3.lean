import PrimeNumberTheorem.WindowedMellinL2
import ZeroFreeRegion.MeromorphicAux

/-!
# L3 threshold comparison: the complementary (B) layer

Self-contained part of the L3 threshold assembly
(`docs/research/windowed-detector-L3-threshold.md`): the total response of
the *complementary* layer — zeros with `Re ρ ≤ β - gap` — is bounded by
`2 X^(λ(β-gap))` times the frequency-weighted mass, and is strictly
dominated by the aligned seed response once the exponent budget

    C (1 + log(T0+H+6))² (T0+H) / H  <  X^(λ·gap) / (4β)

holds.  The (A) top-layer-outside terms and the kernel multiplier
`C_h` belong to the cubic kernel modules
(`ZeroDensityLayerBudgetCubicKernelNearOne`); they multiply these
estimates by a factor of the form `K (1 + o(1))` and do not change the
exponent comparison.

The mass hypothesis below is exactly the conclusion of
`HalfIsolatedZeroDichotomy.dyadic_distance_sum_le` (L1), so the two
lemmas here assemble L1 + L2 without the kernel line.
-/

namespace PrimeNumberTheorem
namespace WindowedMellinL3

open scoped BigOperators
open Filter

/-- L3-B: the total complementary-layer response is bounded by
`2 X^(λ(β-gap))` times the frequency-weighted mass. -/
theorem complementaryResponseSum_le {X lam gap β T0 H C : ℝ}
    {complementary : Finset ℂ} {γ : ℝ}
    (hX : 1 < X) (hlam : 1 < lam) (hgap : 0 < gap)
    (hzero : ∀ ρ ∈ complementary, RiemannHypothesis.IsNontrivialZero ρ)
    (hre : ∀ ρ ∈ complementary, ρ.re ≤ β - gap)
    (hre_nonneg : ∀ ρ ∈ complementary, 0 ≤ ρ.re)
    (hz : ∀ ρ ∈ complementary, ρ - Complex.I * γ ≠ 0)
    (hγavoid : ∀ ρ ∈ complementary, γ ≠ ρ.im)
    (hMass :
      (complementary.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤
        C * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H) :
    (complementary.sum fun ρ => ‖∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
      2 * X ^ (lam * (β - gap)) *
        (C * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H) := by
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hXlam0 : 0 < X ^ lam := Real.rpow_pos_of_pos hX0 lam
  have hXle : X ≤ X ^ lam := by
    have h1 : X ^ (1 : ℝ) ≤ X ^ lam :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hX) hlam.le
    simpa [Real.rpow_one] using h1
  have hpow : (X ^ lam) ^ (β - gap) = X ^ (lam * (β - gap)) := by
    rw [Real.rpow_mul hX0.le lam (β - gap)]
  have hresp {ρ : ℂ} (hρ : ρ ∈ complementary) :
      ‖∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ ≤
        2 * X ^ (lam * (β - gap)) / |γ - ρ.im| := by
    have hb := WindowedMellinL2.complementaryResponse_le
      (ρ := ρ) (X := X) (lam := lam) (γ := γ)
      hX hlam (hre_nonneg ρ hρ) (hz ρ hρ) (hγavoid ρ hρ)
    calc
      ‖∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ ≤
          2 * (X ^ lam) ^ ρ.re / |γ - ρ.im| := hb
      _ ≤ 2 * X ^ (lam * (β - gap)) / |γ - ρ.im| := by
        have hle : (X ^ lam) ^ ρ.re ≤ X ^ (lam * (β - gap)) := by
          have h1 : (X ^ lam) ^ ρ.re ≤ (X ^ lam) ^ (β - gap) := by
            exact Real.rpow_le_rpow_of_exponent_le (le_trans (le_of_lt hX) hXle) (hre ρ hρ)
          simpa [hpow] using h1
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hle (by norm_num : 0 ≤ (2 : ℝ))) (abs_nonneg _)
  calc
    (complementary.sum fun ρ => ‖∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
        complementary.sum (fun ρ => 2 * X ^ (lam * (β - gap)) / |γ - ρ.im|) := by
      exact Finset.sum_le_sum (fun ρ hρ => hresp hρ)
    _ ≤ complementary.sum (fun ρ => 2 * X ^ (lam * (β - gap)) *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|)) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hm1 : (1 : ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by
        have hζ : riemannZeta ρ = 0 := (hzero ρ hρ).1
        have hρ1 : ρ ≠ 1 := by
          intro h
          have hre' := (hzero ρ hρ).2.2
          rw [h] at hre'
          norm_num at hre'
        exact_mod_cast (Nat.succ_le_of_lt
          (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hρ1 hζ))
      have hpos : 0 < |γ - ρ.im| := abs_pos.mpr (sub_ne_zero.mpr (hγavoid ρ hρ))
      have ha : 0 ≤ 2 * X ^ (lam * (β - gap)) / |γ - ρ.im| := by
        exact div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hX0.le _)) hpos.le
      calc
        2 * X ^ (lam * (β - gap)) / |γ - ρ.im| ≤
            2 * X ^ (lam * (β - gap)) / |γ - ρ.im| *
              (analyticOrderNatAt riemannZeta ρ : ℝ) := by
          exact le_mul_of_one_le_right ha hm1
        _ = 2 * X ^ (lam * (β - gap)) *
              ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by ring
    _ = 2 * X ^ (lam * (β - gap)) *
          (complementary.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * X ^ (lam * (β - gap)) *
          (C * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H) := by
      exact mul_le_mul_of_nonneg_left hMass (by
        exact mul_nonneg (by norm_num) (Real.rpow_nonneg hX0.le (lam * (β - gap))))

/-- L3-B (strict): under the exponent budget
`C (1+log(T0+H+6))² (T0+H)/H < X^(λ·gap) / (4β)` the complementary-layer
response is strictly smaller than the aligned seed response. -/
theorem complementaryResponseSum_lt_seedResponse
    {X lam gap β T0 H C : ℝ} {complementary : Finset ℂ} {γ : ℝ}
    (hX : 1 < X) (hlam : 1 < lam) (hgap : 0 < gap) (hβ : 0 < β)
    (hzero : ∀ ρ ∈ complementary, RiemannHypothesis.IsNontrivialZero ρ)
    (hre : ∀ ρ ∈ complementary, ρ.re ≤ β - gap)
    (hre_nonneg : ∀ ρ ∈ complementary, 0 ≤ ρ.re)
    (hz : ∀ ρ ∈ complementary, ρ - Complex.I * γ ≠ 0)
    (hγavoid : ∀ ρ ∈ complementary, γ ≠ ρ.im)
    (hMass :
      (complementary.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤
        C * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H)
    (hBudget : C * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H <
      X ^ (lam * gap) / (4 * β))
    (hseed : X ^ (lam * β) / (2 * β) ≤ ∫ x in X..X ^ lam, x ^ (β - 1)) :
    (complementary.sum fun ρ => ‖∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) <
      ∫ x in X..X ^ lam, x ^ (β - 1) := by
  have hB := complementaryResponseSum_le hX hlam hgap hzero hre hre_nonneg hz hγavoid hMass
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hβ' : β ≠ 0 := ne_of_gt hβ
  calc
    (complementary.sum fun ρ => ‖∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
        2 * X ^ (lam * (β - gap)) *
          (C * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H) := hB
    _ < 2 * X ^ (lam * (β - gap)) * (X ^ (lam * gap) / (4 * β)) := by
      exact mul_lt_mul_of_pos_left hBudget (by
        exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hX0 (lam * (β - gap))))
    _ = X ^ (lam * β) / (2 * β) := by
      have hpow : X ^ (lam * (β - gap)) * X ^ (lam * gap) = X ^ (lam * β) := by
        rw [← Real.rpow_add hX0 (lam * (β - gap)) (lam * gap)]
        congr 1
        ring
      have hstep : 2 * X ^ (lam * (β - gap)) * (X ^ (lam * gap) / (4 * β)) =
          X ^ (lam * β) / (2 * β) := by
        calc
          2 * X ^ (lam * (β - gap)) * (X ^ (lam * gap) / (4 * β))
              = 2 * (X ^ (lam * (β - gap)) * X ^ (lam * gap)) / (4 * β) := by
            field_simp [hβ']
          _ = 2 * X ^ (lam * β) / (4 * β) := by rw [hpow]
          _ = X ^ (lam * β) / (2 * β) := by
            field_simp [hβ']
            ring
      exact hstep
    _ ≤ ∫ x in X..X ^ lam, x ^ (β - 1) := hseed

end WindowedMellinL3
end PrimeNumberTheorem
