import PrimeNumberTheorem.WindowedMellinL2
import PrimeNumberTheorem.WindowedDetectorResponseKernel
import PrimeNumberTheorem.GlobalZeroCount
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

/-- L3-A count: the top-layer frequency-weighted mass is bounded by
`(1/η)` times the global multiplicity bound. -/
theorem topLayerMass_le {T0 H η Cg : ℝ} {top : Finset ℂ} {γ : ℝ}
    (hη : 0 < η)
    (hzero : ∀ ρ ∈ top, RiemannHypothesis.IsNontrivialZero ρ)
    (hηavoid : ∀ ρ ∈ top, η ≤ |γ - ρ.im|)
    (him_pos : ∀ ρ ∈ top, 0 < ρ.im)
    (him_le : ∀ ρ ∈ top, ρ.im ≤ T0 + H)
    (hgm : ExplicitFormulaAux.globalZeroMultiplicity (T0 + H) ≤
      Cg * (T0 + H) * (1 + Real.log (T0 + H + 6))) :
    (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤
      (1 / η) * (Cg * (T0 + H) * (1 + Real.log (T0 + H + 6))) := by
  have hsub : top ⊆ nontrivialZerosFinset (T0 + H) := by
    intro ρ hρ
    exact mem_nontrivialZerosFinset.mpr ⟨hzero ρ hρ, by
      rw [abs_of_pos (him_pos ρ hρ)]
      exact him_le ρ hρ⟩
  have hsum_m : (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
      ExplicitFormulaAux.globalZeroMultiplicity (T0 + H) := by
    simpa [ExplicitFormulaAux.globalZeroMultiplicity] using
      (Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => hsub hρ)
        (fun ρ hρ _ => by exact_mod_cast Nat.zero_le _))
  calc
    (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤
        top.sum (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / η) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have h1 : 1 / |γ - ρ.im| ≤ 1 / η := one_div_le_one_div_of_le hη (hηavoid ρ hρ)
      have hm : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by exact_mod_cast Nat.zero_le _
      have h2 : (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / |γ - ρ.im|) ≤
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / η) :=
        mul_le_mul_of_nonneg_left h1 hm
      simpa [div_eq_mul_inv] using h2
    _ = (1 / η) * (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      ring
    _ ≤ (1 / η) * ExplicitFormulaAux.globalZeroMultiplicity (T0 + H) := by
      exact mul_le_mul_of_nonneg_left hsum_m (by positivity : 0 ≤ 1 / η)
    _ ≤ (1 / η) * (Cg * (T0 + H) * (1 + Real.log (T0 + H + 6))) := by
      exact mul_le_mul_of_nonneg_left hgm (by positivity : 0 ≤ 1 / η)

/-- L3-A packet count: a mass *lower* bound forces a cardinality lower
bound on the top-layer window packet, via the per-zero multiplicity cap
`globalZeroMultiplicity ≤ Cg (T0+H) (1 + log(T0+H+6))` and the
`η`-separation of the detection point from the top layer.  Combined with
`windowedDetector_topLayerMass_exceeds` this converts the detector
contradiction into the gate's growing packet `q T`. -/
theorem topLayerPacket_card_le_of_mass
    {T0 H η Cg MassA : ℝ} {top : Finset ℂ} {γ : ℝ} {q : ℕ}
    (hη : 0 < η) (hCg : 0 < Cg) (hT0H : 0 < T0 + H)
    (hzero : ∀ ρ ∈ top, RiemannHypothesis.IsNontrivialZero ρ)
    (hηavoid : ∀ ρ ∈ top, η ≤ |γ - ρ.im|)
    (him_pos : ∀ ρ ∈ top, 0 < ρ.im)
    (him_le : ∀ ρ ∈ top, ρ.im ≤ T0 + H)
    (hgm : ExplicitFormulaAux.globalZeroMultiplicity (T0 + H) ≤
      Cg * (T0 + H) * (1 + Real.log (T0 + H + 6)))
    (hmass : MassA < (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|))
    (hq : (q : ℝ) ≤ MassA * η / (Cg * (T0 + H) * (1 + Real.log (T0 + H + 6)))) :
    q ≤ top.card := by
  let CgM : ℝ := Cg * (T0 + H) * (1 + Real.log (T0 + H + 6))
  have hMpos : 0 < CgM := by
    dsimp [CgM]
    have hlog : 0 < 1 + Real.log (T0 + H + 6) := by
      have h1 : 1 ≤ T0 + H + 6 := by linarith
      have hlog0 : 0 ≤ Real.log (T0 + H + 6) := Real.log_nonneg h1
      linarith
    positivity
  have hmass_per : (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤
      (1 / η) * CgM * (top.card : ℝ) := by
    have hper {ρ : ℂ} (hρ : ρ ∈ top) : (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
        ExplicitFormulaAux.globalZeroMultiplicity (T0 + H) := by
      have hsub : ρ ∈ nontrivialZerosFinset (T0 + H) :=
        mem_nontrivialZerosFinset.mpr ⟨hzero ρ hρ, by
          rw [abs_of_pos (him_pos ρ hρ)]
          exact him_le ρ hρ⟩
      simpa [ExplicitFormulaAux.globalZeroMultiplicity] using
        (Finset.single_le_sum (s := nontrivialZerosFinset (T0 + H))
          (f := fun σ => (analyticOrderNatAt riemannZeta σ : ℝ))
          (fun σ hσ => Nat.cast_nonneg (analyticOrderNatAt riemannZeta σ)) hsub)
    calc
      (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤
          top.sum (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / η) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have h1 : 1 / |γ - ρ.im| ≤ 1 / η := one_div_le_one_div_of_le hη (hηavoid ρ hρ)
        have hm : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by exact_mod_cast Nat.zero_le _
        have h2 : (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / |γ - ρ.im|) ≤
            (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / η) :=
          mul_le_mul_of_nonneg_left h1 hm
        simpa [div_eq_mul_inv] using h2
      _ = (1 / η) * (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ hρ
        ring
      _ ≤ (1 / η) * (ExplicitFormulaAux.globalZeroMultiplicity (T0 + H)) * (top.card : ℝ) := by
        have hsum_m' : (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
            ExplicitFormulaAux.globalZeroMultiplicity (T0 + H) * (top.card : ℝ) := by
          calc
            (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
                top.sum (fun _ => ExplicitFormulaAux.globalZeroMultiplicity (T0 + H)) := by
              exact Finset.sum_le_sum (fun ρ hρ => hper hρ)
            _ = ExplicitFormulaAux.globalZeroMultiplicity (T0 + H) * (top.card : ℝ) := by
              simp [mul_comm]
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hsum_m' (by positivity : 0 ≤ 1 / η)
      _ ≤ (1 / η) * CgM * (top.card : ℝ) := by
        dsimp [CgM]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgm (by positivity : 0 ≤ 1 / η)) (Nat.cast_nonneg _)
  have hlt : MassA * η / CgM < (top.card : ℝ) := by
    have hmain : MassA < (1 / η) * CgM * (top.card : ℝ) :=
      lt_of_lt_of_le hmass hmass_per
    have h1' : MassA * η < CgM * (top.card : ℝ) := by
      have h2 : MassA * η < ((1 / η) * CgM * (top.card : ℝ)) * η :=
        mul_lt_mul_of_pos_right hmain hη
      have h3 : ((1 / η) * CgM * (top.card : ℝ)) * η = CgM * (top.card : ℝ) := by
        field_simp [hη.ne']
      rwa [h3] at h2
    exact (div_lt_iff₀ hMpos).mpr (by simpa [mul_comm] using h1')
  have hq' : (q : ℝ) < (top.card : ℝ) := by
    calc
      (q : ℝ) ≤ MassA * η / (Cg * (T0 + H) * (1 + Real.log (T0 + H + 6))) := hq
      _ = MassA * η / CgM := rfl
      _ < (top.card : ℝ) := hlt
  exact Nat.le_of_lt (by exact_mod_cast hq' : q < top.card)

/-- L3-A: the (outside-window) top-layer response sum with kernel factor
`C_h`, under a uniform kernel bound `‖C_h ρ‖ ≤ KA`. -/
theorem topLayerResponseSum_le {X lam β KA Mass : ℝ} {top : Finset ℂ} {γ : ℝ}
    {C_h : ℂ → ℂ}
    (hX : 1 < X) (hlam : 1 < lam)
    (hzero : ∀ ρ ∈ top, RiemannHypothesis.IsNontrivialZero ρ)
    (hre_top : ∀ ρ ∈ top, ρ.re = β)
    (hre_nonneg : ∀ ρ ∈ top, 0 ≤ ρ.re)
    (hz : ∀ ρ ∈ top, ρ - Complex.I * γ ≠ 0)
    (hγavoid : ∀ ρ ∈ top, γ ≠ ρ.im)
    (hKA : 0 ≤ KA)
    (hKernel : ∀ ρ ∈ top, ‖C_h ρ‖ ≤ KA)
    (hMass : (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤ Mass) :
    (top.sum fun ρ => ‖C_h ρ * ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
      KA * 2 * X ^ (lam * β) * Mass := by
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hXlam0 : 0 < X ^ lam := Real.rpow_pos_of_pos hX0 lam
  have hpow : (X ^ lam) ^ β = X ^ (lam * β) := by
    rw [Real.rpow_mul hX0.le lam β]
  have hm1 {ρ : ℂ} (hρ : ρ ∈ top) : (1 : ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    have hζ : riemannZeta ρ = 0 := (hzero ρ hρ).1
    have hρ1 : ρ ≠ 1 := by
      intro h
      have hre' := (hzero ρ hρ).2.2
      rw [h] at hre'
      norm_num at hre'
    exact_mod_cast (Nat.succ_le_of_lt
      (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hρ1 hζ))
  have hresp {ρ : ℂ} (hρ : ρ ∈ top) :
      ‖C_h ρ * ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ ≤
        KA * 2 * X ^ (lam * β) / |γ - ρ.im| := by
    have hb := WindowedMellinL2.complementaryResponse_le
      (ρ := ρ) (X := X) (lam := lam) (γ := γ)
      hX hlam (hre_nonneg ρ hρ) (hz ρ hρ) (hγavoid ρ hρ)
    have hre' : ρ.re = β := hre_top ρ hρ
    calc
      ‖C_h ρ * ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ ≤
          ‖C_h ρ‖ * ‖∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ := norm_mul_le _ _
      _ ≤ KA * (2 * (X ^ lam) ^ ρ.re / |γ - ρ.im|) := by
        exact mul_le_mul (hKernel ρ hρ) hb (norm_nonneg _) hKA
      _ = KA * 2 * X ^ (lam * β) / |γ - ρ.im| := by
        rw [hre', hpow]
        ring
  calc
    (top.sum fun ρ => ‖C_h ρ * ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
        top.sum (fun ρ => KA * 2 * X ^ (lam * β) / |γ - ρ.im|) := by
      exact Finset.sum_le_sum (fun ρ hρ => hresp hρ)
    _ ≤ top.sum (fun ρ => KA * 2 * X ^ (lam * β) *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|)) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hpos : 0 < |γ - ρ.im| := abs_pos.mpr (sub_ne_zero.mpr (hγavoid ρ hρ))
      have ha : 0 ≤ KA * 2 * X ^ (lam * β) / |γ - ρ.im| := by
        exact div_nonneg (mul_nonneg (mul_nonneg hKA (by norm_num))
          (Real.rpow_nonneg hX0.le (lam * β))) hpos.le
      calc
        KA * 2 * X ^ (lam * β) / |γ - ρ.im| ≤
            KA * 2 * X ^ (lam * β) / |γ - ρ.im| * (analyticOrderNatAt riemannZeta ρ : ℝ) := by
          exact le_mul_of_one_le_right ha (hm1 hρ)
        _ = KA * 2 * X ^ (lam * β) * ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
          ring
    _ = KA * 2 * X ^ (lam * β) *
          (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
      rw [Finset.mul_sum]
    _ ≤ KA * 2 * X ^ (lam * β) * Mass := by
      exact mul_le_mul_of_nonneg_left hMass (by
        exact mul_nonneg (mul_nonneg hKA (by norm_num))
          (Real.rpow_nonneg hX0.le (lam * β)))

/-- L3-A instantiated with the real kernel: the total response of the
top layer (outside the avoided window) is bounded by
`max 4 (36/(h·T0/2)²) · 4 · X^(λβ+β) / T0` times the frequency-weighted
mass, on the kernel-valid range `h ≤ log 2`, `T0/2 ≤ Im ρ`. -/
theorem topLayerResponseSum_le_of_kernel
    {X lam β h T0 : ℝ} {top : Finset ℂ} {γ : ℝ} {Mass : ℝ}
    (hX : 1 < X) (hlam : 1 < lam) (hh : 0 < h) (hT0 : 0 < T0)
    (hhsmall : h ≤ Real.log 2)
    (hzero : ∀ ρ ∈ top, RiemannHypothesis.IsNontrivialZero ρ)
    (hre_top : ∀ ρ ∈ top, ρ.re = β)
    (hz : ∀ ρ ∈ top, ρ - Complex.I * γ ≠ 0)
    (hγavoid : ∀ ρ ∈ top, γ ≠ ρ.im)
    (hhigh : ∀ ρ ∈ top, T0 / 2 ≤ ρ.im)
    (hMass : (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤ Mass) :
    (top.sum fun ρ => ‖WindowedMellinL2.zeroResponseKernel ρ X h γ *
      ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
      max 4 (36 / (h * (T0 / 2)) ^ 2) * 4 * X ^ (lam * β + β) / T0 * Mass := by
  let KA : ℝ := max 4 (36 / (h * (T0 / 2)) ^ 2)
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hXlam0 : 0 < X ^ lam := Real.rpow_pos_of_pos hX0 lam
  have hT0half_pos : 0 < T0 / 2 := div_pos hT0 (by norm_num)
  have hKA : 0 ≤ KA := by
    dsimp [KA]
    exact le_trans (by norm_num : 0 ≤ (4 : ℝ)) (le_max_left _ _)
  have hresp {ρ : ℂ} (hρ : ρ ∈ top) :
      ‖WindowedMellinL2.zeroResponseKernel ρ X h γ *
        ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ ≤
        KA * 4 * X ^ (lam * β + β) / T0 *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
    have hreβ : ρ.re = β := hre_top ρ hρ
    have hb := WindowedMellinL2.complementaryResponse_le
      (ρ := ρ) (X := X) (lam := lam) (γ := γ)
      hX hlam (le_of_lt (hzero ρ hρ).2.1) (hz ρ hρ) (hγavoid ρ hρ)
    rw [hreβ] at hb
    have hre0 : 0 ≤ ρ.re := le_of_lt (hzero ρ hρ).2.1
    have hre1 : ρ.re ≤ 1 := le_of_lt (hzero ρ hρ).2.2
    have hρne : ρ ≠ 0 := by
      intro h
      have hpos := (hzero ρ hρ).2.1
      rw [h] at hpos
      norm_num at hpos
    have hnormρ : T0 / 2 ≤ ‖ρ‖ := by
      have him : T0 / 2 ≤ ρ.im := hhigh ρ hρ
      have him' : |ρ.im| = ρ.im := abs_of_pos (lt_of_lt_of_le hT0half_pos him)
      calc
        T0 / 2 ≤ |ρ.im| := by rw [him']; exact him
        _ ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
    have hk := WindowedMellinL2.norm_zeroResponseKernel_le_uniform
      (γ := γ) (hx := hX0) hh hre0 hre1 hT0 hnormρ hhsmall hρne
    rw [hreβ] at hk
    have hβ1 : β ≤ 1 := by
      rw [← hre_top ρ hρ]
      exact hre1
    have hβnonneg : 0 ≤ β := by
      rw [← hre_top ρ hρ]
      exact hre0
    have hXβ : X ^ β ≤ X := by
      have h1 : X ^ β ≤ X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt hX) hβ1
      simpa [Real.rpow_one] using h1
    have hpow1 : (X ^ lam) ^ β = X ^ (lam * β) := by
      rw [Real.rpow_mul hX0.le lam β]
    have hpow2 : X ^ (lam * β) * X ^ β = X ^ (lam * β + β) := by
      exact (Real.rpow_add hX0 (lam * β) β).symm
    have hrec : 1 / ‖ρ‖ ≤ 2 / T0 := by
      have h1 : 1 / ‖ρ‖ ≤ 1 / (T0 / 2) :=
        one_div_le_one_div_of_le hT0half_pos hnormρ
      have h2 : 1 / (T0 / 2) = 2 / T0 := by
        field_simp [hT0.ne', ne_of_gt hT0half_pos]
      simpa [h2] using h1
    have hm0 : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by exact_mod_cast Nat.zero_le _
    have hXβ0 : 0 ≤ X ^ β := Real.rpow_nonneg hX0.le β
    have hXlb0 : 0 ≤ X ^ (lam * β) := Real.rpow_nonneg hX0.le (lam * β)
    have hposd : 0 < |γ - ρ.im| := abs_pos.mpr (sub_ne_zero.mpr (hγavoid ρ hρ))
    have hA : KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ β / ‖ρ‖) *
          (2 * (X ^ lam) ^ β / |γ - ρ.im|) ≤
        KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ β * (2 / T0)) *
          (2 * X ^ (lam * β) / |γ - ρ.im|) := by
      rw [hpow1]
      have hrec' : (analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ β / ‖ρ‖ ≤
          (analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ β * (2 / T0) := by
        have h1 : (analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ β / ‖ρ‖ =
            (analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ β * (1 / ‖ρ‖) := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_left hrec (mul_nonneg hm0 hXβ0)
      have hrecKa : KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ β / ‖ρ‖) ≤
          KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ β * (2 / T0)) := by
        exact mul_le_mul_of_nonneg_left hrec' hKA
      have hprod : 0 ≤ 2 * X ^ (lam * β) / |γ - ρ.im| := by
        exact div_nonneg (mul_nonneg (by norm_num) hXlb0) hposd.le
      have hb0 : 0 ≤ KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ β * (2 / T0)) := by
        exact mul_nonneg hKA (mul_nonneg (mul_nonneg hm0 hXβ0)
          (div_nonneg (by norm_num) hT0.le))
      exact mul_le_mul hrecKa le_rfl hprod hb0
    have hB : KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ β * (2 / T0)) *
          (2 * X ^ (lam * β) / |γ - ρ.im|) =
        KA * 4 * X ^ (lam * β + β) / T0 *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
      have hstep : KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ β * (2 / T0)) *
            (2 * X ^ (lam * β) / |γ - ρ.im|) =
          KA * (analyticOrderNatAt riemannZeta ρ : ℝ) * (X ^ β * X ^ (lam * β)) *
            (4 / T0) / |γ - ρ.im| := by
        field_simp [hT0.ne', hposd.ne']
        ring
      rw [hstep]
      rw [show X ^ β * X ^ (lam * β) = X ^ (lam * β) * X ^ β by ring]
      rw [hpow2]
      field_simp [hT0.ne', hposd.ne']
    calc
      ‖WindowedMellinL2.zeroResponseKernel ρ X h γ *
          ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ ≤
          ‖WindowedMellinL2.zeroResponseKernel ρ X h γ‖ *
            ‖∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ := norm_mul_le _ _
      _ ≤ (KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) * X ^ β / ‖ρ‖)) *
            (2 * (X ^ lam) ^ β / |γ - ρ.im|) := by
        exact mul_le_mul hk hb (norm_nonneg _) (by
          exact mul_nonneg hKA (div_nonneg (mul_nonneg hm0 hXβ0) (norm_nonneg ρ)))
      _ ≤ KA * 4 * X ^ (lam * β + β) / T0 *
            ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
        exact hA.trans_eq hB
  calc
    (top.sum fun ρ => ‖WindowedMellinL2.zeroResponseKernel ρ X h γ *
      ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
        top.sum (fun ρ => KA * 4 * X ^ (lam * β + β) / T0 *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|)) := by
      exact Finset.sum_le_sum (fun ρ hρ => hresp hρ)
    _ = KA * 4 * X ^ (lam * β + β) / T0 *
          (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
      rw [Finset.mul_sum]
    _ ≤ KA * 4 * X ^ (lam * β + β) / T0 * Mass := by
      exact mul_le_mul_of_nonneg_left hMass (by
        exact div_nonneg (mul_nonneg (mul_nonneg hKA (by norm_num))
          (Real.rpow_nonneg hX0.le (lam * β + β))) hT0.le)

/-- L3 threshold assembly: the total (top + complementary) response is
strictly below the seed-with-kernel scale `X^(λβ+β)/(2β(T0+H))`, once the
two per-layer budgets hold (these are exactly the exponent-budget
conditions the gate instantiation discharges via
`AmplificationGateExponentBudget` and the parameter choice
`γ₀ h' > 2d`). -/
theorem topAndComplementaryResponse_lt_seedScale
    {X lam gap β T0 H KA : ℝ} {top complementary : Finset ℂ} {γ : ℝ}
    {MassA MassB : ℝ} {C_h : ℂ → ℂ}
    (hX : 1 < X) (hlam : 1 < lam) (hβ : 0 < β) (hgap : 0 < gap)
    (hKA : 0 ≤ KA) (hT0 : 0 < T0) (hH : 0 < H)
    (hA : (top.sum fun ρ => ‖C_h ρ * ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
        KA * 4 * X ^ (lam * β + β) / T0 * MassA)
    (hB : (complementary.sum fun ρ => ‖C_h ρ * ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
        KA * 4 * X ^ ((lam + 1) * (β - gap)) / T0 * MassB)
    (hbudgetA : KA * 4 * MassA / T0 < 1 / (4 * β * (T0 + H)))
    (hbudgetB : KA * 4 * X ^ ((lam + 1) * (β - gap)) / T0 * MassB <
      X ^ (lam * β + β) / (4 * β * (T0 + H))) :
    ((top.sum fun ρ => ‖C_h ρ * ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) +
      (complementary.sum fun ρ => ‖C_h ρ * ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖)) <
      X ^ (lam * β + β) / (2 * β * (T0 + H)) := by
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hXpow : 0 < X ^ (lam * β + β) := Real.rpow_pos_of_pos hX0 (lam * β + β)
  have hA' : (top.sum fun ρ => ‖C_h ρ * ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) <
      X ^ (lam * β + β) / (4 * β * (T0 + H)) := by
    have h1 : KA * 4 * X ^ (lam * β + β) / T0 * MassA <
        X ^ (lam * β + β) * (1 / (4 * β * (T0 + H))) := by
      have hrewrite : KA * 4 * X ^ (lam * β + β) / T0 * MassA =
          X ^ (lam * β + β) * (KA * 4 * MassA / T0) := by ring
      rw [hrewrite]
      exact mul_lt_mul_of_pos_left hbudgetA hXpow
    have h2 : X ^ (lam * β + β) * (1 / (4 * β * (T0 + H))) =
        X ^ (lam * β + β) / (4 * β * (T0 + H)) := by ring
    exact hA.trans_lt (by rwa [h2] at h1)
  have hB' : (complementary.sum fun ρ => ‖C_h ρ * ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) <
      X ^ (lam * β + β) / (4 * β * (T0 + H)) := by
    exact hB.trans_lt hbudgetB
  have hQ : X ^ (lam * β + β) / (4 * β * (T0 + H)) + X ^ (lam * β + β) / (4 * β * (T0 + H)) =
      X ^ (lam * β + β) / (2 * β * (T0 + H)) := by
    field_simp [hβ.ne', ne_of_gt (mul_pos hT0 hH)]
    ring
  linarith [hA', hB', hQ]

/-- L3-A coefficient form: the top-layer response-coefficient sum
(`Σ ‖coeff·I‖`, the shape produced by the L2 response identity) is
`≤ KA·4·X^(λβ)/T0·Mass`. -/
theorem topLayerCoeffResponseSum_le
    {X lam β h T0 : ℝ} {top : Finset ℂ} {γ : ℝ} {Mass : ℝ}
    (hX : 1 < X) (hlam : 1 < lam) (hh : 0 < h) (hT0 : 0 < T0)
    (hhsmall : h ≤ Real.log 2)
    (hzero : ∀ ρ ∈ top, RiemannHypothesis.IsNontrivialZero ρ)
    (hre_top : ∀ ρ ∈ top, ρ.re = β)
    (hz : ∀ ρ ∈ top, ρ - Complex.I * γ ≠ 0)
    (hγavoid : ∀ ρ ∈ top, γ ≠ ρ.im)
    (hhigh : ∀ ρ ∈ top, T0 / 2 ≤ ρ.im)
    (hMass : (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤ Mass) :
    (top.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h *
      ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
      max 4 (36 / (h * (T0 / 2)) ^ 2) * 4 * X ^ (lam * β) / T0 * Mass := by
  let KA : ℝ := max 4 (36 / (h * (T0 / 2)) ^ 2)
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hXlam0 : 0 < X ^ lam := Real.rpow_pos_of_pos hX0 lam
  have hT0half_pos : 0 < T0 / 2 := div_pos hT0 (by norm_num)
  have hKA : 0 ≤ KA := by
    dsimp [KA]
    exact le_trans (by norm_num : 0 ≤ (4 : ℝ)) (le_max_left _ _)
  have hresp {ρ : ℂ} (hρ : ρ ∈ top) :
      ‖WindowedMellinL2.zeroResponseCoeff ρ h *
        ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ ≤
        KA * 4 * X ^ (lam * β) / T0 *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
    have hreβ : ρ.re = β := hre_top ρ hρ
    have hb := WindowedMellinL2.complementaryResponse_le
      (ρ := ρ) (X := X) (lam := lam) (γ := γ)
      hX hlam (le_of_lt (hzero ρ hρ).2.1) (hz ρ hρ) (hγavoid ρ hρ)
    rw [hreβ] at hb
    rw [show (X ^ lam) ^ β = X ^ (lam * β) by rw [Real.rpow_mul hX0.le lam β]] at hb
    have hre0 : 0 ≤ ρ.re := le_of_lt (hzero ρ hρ).2.1
    have hre1 : ρ.re ≤ 1 := le_of_lt (hzero ρ hρ).2.2
    have hρne : ρ ≠ 0 := by
      intro h
      have hpos := (hzero ρ hρ).2.1
      rw [h] at hpos
      norm_num at hpos
    have hnormρ : T0 / 2 ≤ ‖ρ‖ := by
      have him : T0 / 2 ≤ ρ.im := hhigh ρ hρ
      have him' : |ρ.im| = ρ.im := abs_of_pos (lt_of_lt_of_le hT0half_pos him)
      calc
        T0 / 2 ≤ |ρ.im| := by rw [him']; exact him
        _ ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
    have hmult := ExplicitFormulaResidues.norm_cubicKernelMultiplier_le_uniform
      hh hre0 hre1 hT0 hnormρ hhsmall hρne
    have hcoeff : ‖WindowedMellinL2.zeroResponseCoeff ρ h‖ ≤
        KA * (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
      dsimp [WindowedMellinL2.zeroResponseCoeff, KA]
      rw [norm_mul, norm_div, norm_neg]
      have hm : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by exact_mod_cast Nat.zero_le _
      simp
      have h1 : (analyticOrderNatAt riemannZeta ρ : ℝ) * ‖ExplicitFormulaResidues.cubicKernelMultiplier ρ h‖ / ‖ρ‖ ≤
          max 4 (36 / (h * (T0 / 2)) ^ 2) * (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
        exact div_le_div_of_nonneg_right
          (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hmult hm) (norm_nonneg ρ)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h1
    have hrec : 1 / ‖ρ‖ ≤ 2 / T0 := by
      have h1 : 1 / ‖ρ‖ ≤ 1 / (T0 / 2) :=
        one_div_le_one_div_of_le hT0half_pos hnormρ
      have h2 : 1 / (T0 / 2) = 2 / T0 := by
        field_simp [hT0.ne', ne_of_gt hT0half_pos]
      simpa [h2] using h1
    have hm0 : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by exact_mod_cast Nat.zero_le _
    have hposd : 0 < |γ - ρ.im| := abs_pos.mpr (sub_ne_zero.mpr (hγavoid ρ hρ))
    calc
      ‖WindowedMellinL2.zeroResponseCoeff ρ h *
          ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ ≤
          ‖WindowedMellinL2.zeroResponseCoeff ρ h‖ *
            ‖∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ := norm_mul_le _ _
      _ ≤ (KA * (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) *
            (2 * X ^ (lam * β) / |γ - ρ.im|) := by
        exact mul_le_mul hcoeff hb (norm_nonneg _) (by
          exact div_nonneg (mul_nonneg hKA hm0) (norm_nonneg ρ))
      _ ≤ KA * 4 * X ^ (lam * β) / T0 *
            ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
        have h1 : (KA * (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) *
              (2 * X ^ (lam * β) / |γ - ρ.im|) ≤
            (KA * (analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / T0)) *
              (2 * X ^ (lam * β) / |γ - ρ.im|) := by
          have hrec' : (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤
              (analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / T0) := by
            have h1' : (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ =
                (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / ‖ρ‖) := by ring
            rw [h1']
            exact mul_le_mul_of_nonneg_left hrec hm0
          have hrecKa : KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) ≤
              KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / T0)) := by
            exact mul_le_mul_of_nonneg_left hrec' hKA
          have hprod : 0 ≤ 2 * X ^ (lam * β) / |γ - ρ.im| := by
            exact div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hX0.le (lam * β)))
              hposd.le
          have hb0 : 0 ≤ KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / T0)) := by
            exact mul_nonneg hKA (mul_nonneg hm0 (div_nonneg (by norm_num) hT0.le))
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul hrecKa le_rfl hprod hb0)
        have h2 : (KA * (analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / T0)) *
              (2 * X ^ (lam * β) / |γ - ρ.im|) =
            KA * 4 * X ^ (lam * β) / T0 *
              ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
          field_simp [hT0.ne', hposd.ne']
          ring
        exact h1.trans_eq h2
  calc
    (top.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h *
      ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
        top.sum (fun ρ => KA * 4 * X ^ (lam * β) / T0 *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|)) := by
      exact Finset.sum_le_sum (fun ρ hρ => hresp hρ)
    _ = KA * 4 * X ^ (lam * β) / T0 *
          (top.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
      rw [Finset.mul_sum]
    _ ≤ KA * 4 * X ^ (lam * β) / T0 * Mass := by
      exact mul_le_mul_of_nonneg_left hMass (by
        exact div_nonneg (mul_nonneg (mul_nonneg hKA (by norm_num))
          (Real.rpow_nonneg hX0.le (lam * β))) hT0.le)

/-- L3-B coefficient form: the complementary-layer response-coefficient
sum is `≤ KA·4·X^(λ(β−gap))/T0·Mass`. -/
theorem complementaryCoeffResponseSum_le
    {X lam gap β h T0 : ℝ} {complementary : Finset ℂ} {γ : ℝ} {Mass : ℝ}
    (hX : 1 < X) (hlam : 1 < lam) (hh : 0 < h) (hT0 : 0 < T0)
    (hhsmall : h ≤ Real.log 2)
    (hzero : ∀ ρ ∈ complementary, RiemannHypothesis.IsNontrivialZero ρ)
    (hre_comp : ∀ ρ ∈ complementary, ρ.re ≤ β - gap)
    (hz : ∀ ρ ∈ complementary, ρ - Complex.I * γ ≠ 0)
    (hγavoid : ∀ ρ ∈ complementary, γ ≠ ρ.im)
    (hhigh : ∀ ρ ∈ complementary, T0 / 2 ≤ ρ.im)
    (hMass : (complementary.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤ Mass) :
    (complementary.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h *
      ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
      max 4 (36 / (h * (T0 / 2)) ^ 2) * 4 * X ^ (lam * (β - gap)) / T0 * Mass := by
  let KA : ℝ := max 4 (36 / (h * (T0 / 2)) ^ 2)
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hXlam0 : 0 < X ^ lam := Real.rpow_pos_of_pos hX0 lam
  have hT0half_pos : 0 < T0 / 2 := div_pos hT0 (by norm_num)
  have hKA : 0 ≤ KA := by
    dsimp [KA]
    exact le_trans (by norm_num : 0 ≤ (4 : ℝ)) (le_max_left _ _)
  have hresp {ρ : ℂ} (hρ : ρ ∈ complementary) :
      ‖WindowedMellinL2.zeroResponseCoeff ρ h *
        ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ ≤
        KA * 4 * X ^ (lam * (β - gap)) / T0 *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
    have hb := WindowedMellinL2.complementaryResponse_le
      (ρ := ρ) (X := X) (lam := lam) (γ := γ)
      hX hlam (le_of_lt (hzero ρ hρ).2.1) (hz ρ hρ) (hγavoid ρ hρ)
    have hbre : ‖∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ ≤
        2 * X ^ (lam * (β - gap)) / |γ - ρ.im| := by
      have h1 : (X ^ lam) ^ ρ.re ≤ (X ^ lam) ^ (β - gap) := by
        have hXle : X ≤ X ^ lam := by
          have h1' : X ^ (1 : ℝ) ≤ X ^ lam :=
            Real.rpow_le_rpow_of_exponent_le (le_of_lt hX) hlam.le
          simpa [Real.rpow_one] using h1'
        exact Real.rpow_le_rpow_of_exponent_le (le_trans (le_of_lt hX) hXle) (hre_comp ρ hρ)
      have hpow : (X ^ lam) ^ (β - gap) = X ^ (lam * (β - gap)) := by
        rw [Real.rpow_mul hX0.le lam (β - gap)]
      have h2 : 2 * (X ^ lam) ^ ρ.re / |γ - ρ.im| ≤
          2 * X ^ (lam * (β - gap)) / |γ - ρ.im| := by
        have h1' : (X ^ lam) ^ ρ.re ≤ X ^ (lam * (β - gap)) := by
          simpa [hpow] using h1
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1' (by norm_num : 0 ≤ (2 : ℝ))) (abs_nonneg _)
      exact hb.trans h2
    have hre0 : 0 ≤ ρ.re := le_of_lt (hzero ρ hρ).2.1
    have hre1 : ρ.re ≤ 1 := le_of_lt (hzero ρ hρ).2.2
    have hρne : ρ ≠ 0 := by
      intro h
      have hpos := (hzero ρ hρ).2.1
      rw [h] at hpos
      norm_num at hpos
    have hnormρ : T0 / 2 ≤ ‖ρ‖ := by
      have him : T0 / 2 ≤ ρ.im := hhigh ρ hρ
      have him' : |ρ.im| = ρ.im := abs_of_pos (lt_of_lt_of_le hT0half_pos him)
      calc
        T0 / 2 ≤ |ρ.im| := by rw [him']; exact him
        _ ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
    have hmult := ExplicitFormulaResidues.norm_cubicKernelMultiplier_le_uniform
      hh hre0 hre1 hT0 hnormρ hhsmall hρne
    have hcoeff : ‖WindowedMellinL2.zeroResponseCoeff ρ h‖ ≤
        KA * (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
      dsimp [WindowedMellinL2.zeroResponseCoeff, KA]
      rw [norm_mul, norm_div, norm_neg]
      have hm : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by exact_mod_cast Nat.zero_le _
      simp
      have h1 : (analyticOrderNatAt riemannZeta ρ : ℝ) * ‖ExplicitFormulaResidues.cubicKernelMultiplier ρ h‖ / ‖ρ‖ ≤
          max 4 (36 / (h * (T0 / 2)) ^ 2) * (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
        exact div_le_div_of_nonneg_right
          (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hmult hm) (norm_nonneg ρ)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h1
    have hrec : 1 / ‖ρ‖ ≤ 2 / T0 := by
      have h1 : 1 / ‖ρ‖ ≤ 1 / (T0 / 2) :=
        one_div_le_one_div_of_le hT0half_pos hnormρ
      have h2 : 1 / (T0 / 2) = 2 / T0 := by
        field_simp [hT0.ne', ne_of_gt hT0half_pos]
      simpa [h2] using h1
    have hm0 : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by exact_mod_cast Nat.zero_le _
    have hposd : 0 < |γ - ρ.im| := abs_pos.mpr (sub_ne_zero.mpr (hγavoid ρ hρ))
    calc
      ‖WindowedMellinL2.zeroResponseCoeff ρ h *
          ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ ≤
          ‖WindowedMellinL2.zeroResponseCoeff ρ h‖ *
            ‖∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ := norm_mul_le _ _
      _ ≤ (KA * (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) *
            (2 * X ^ (lam * (β - gap)) / |γ - ρ.im|) := by
        exact mul_le_mul hcoeff hbre (norm_nonneg _) (by
          exact div_nonneg (mul_nonneg hKA hm0) (norm_nonneg ρ))
      _ ≤ KA * 4 * X ^ (lam * (β - gap)) / T0 *
            ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
        have h1 : (KA * (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) *
              (2 * X ^ (lam * (β - gap)) / |γ - ρ.im|) ≤
            (KA * (analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / T0)) *
              (2 * X ^ (lam * (β - gap)) / |γ - ρ.im|) := by
          have hrec' : (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤
              (analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / T0) := by
            have h1' : (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ =
                (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / ‖ρ‖) := by ring
            rw [h1']
            exact mul_le_mul_of_nonneg_left hrec hm0
          have hrecKa : KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) ≤
              KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / T0)) := by
            exact mul_le_mul_of_nonneg_left hrec' hKA
          have hprod : 0 ≤ 2 * X ^ (lam * (β - gap)) / |γ - ρ.im| := by
            exact div_nonneg (mul_nonneg (by norm_num)
              (Real.rpow_nonneg hX0.le (lam * (β - gap)))) hposd.le
          have hb0 : 0 ≤ KA * ((analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / T0)) := by
            exact mul_nonneg hKA (mul_nonneg hm0 (div_nonneg (by norm_num) hT0.le))
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul hrecKa le_rfl hprod hb0)
        have h2 : (KA * (analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / T0)) *
              (2 * X ^ (lam * (β - gap)) / |γ - ρ.im|) =
            KA * 4 * X ^ (lam * (β - gap)) / T0 *
              ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
          field_simp [hT0.ne', hposd.ne']
          ring
        exact h1.trans_eq h2
  calc
    (complementary.sum fun ρ => ‖WindowedMellinL2.zeroResponseCoeff ρ h *
      ∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖) ≤
        complementary.sum (fun ρ => KA * 4 * X ^ (lam * (β - gap)) / T0 *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|)) := by
      exact Finset.sum_le_sum (fun ρ hρ => hresp hρ)
    _ = KA * 4 * X ^ (lam * (β - gap)) / T0 *
          (complementary.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
      rw [Finset.mul_sum]
    _ ≤ KA * 4 * X ^ (lam * (β - gap)) / T0 * Mass := by
      exact mul_le_mul_of_nonneg_left hMass (by
        exact div_nonneg (mul_nonneg (mul_nonneg hKA (by norm_num))
          (Real.rpow_nonneg hX0.le (lam * (β - gap)))) hT0.le)

end WindowedMellinL3
end PrimeNumberTheorem
