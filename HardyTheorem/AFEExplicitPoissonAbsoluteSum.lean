import HardyTheorem.AFEExplicitPoissonFrequencyCutoff
import HardyTheorem.AFEExplicitPoissonFarTail

/-! Absolute convergence and signed-frequency reassembly at fixed upper cutoff. -/

open Filter

namespace HardyTheorem.AFE

/-- The quantitative far tail implies actual absolute convergence.  The
resulting integer reindexing takes place at fixed `N`, before any cutoff limit. -/
theorem explicitPoissonMode_summable_and_tsum_pairs
    {C₁ C₂ sigma N t : ℝ} {K : ℕ}
    (hs : 0 < sigma) (hK : 6 ≤ K) (hN : 2 * (K : ℝ) ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    let f := explicitPoissonMode sigma ((K : ℝ) + 1) N t
    Summable (fun m : ℕ => ‖f ((m + 1 : ℕ) : ℤ)‖ + ‖f (-((m + 1 : ℕ) : ℤ))‖) ∧
      Summable f ∧
      (∑' k : ℤ, f k) = f 0 +
        ∑' m : ℕ, (f ((m + 1 : ℕ) : ℤ) + f (-((m + 1 : ℕ) : ℤ))) := by
  let f := explicitPoissonMode sigma ((K : ℝ) + 1) N t
  let P : ℕ → ℝ := fun m => ‖f (m : ℤ)‖ + ‖f (-(m : ℤ))‖
  let M := Nat.ceil (t / (Real.pi * K))
  have hK6 : 6 ≤ (K : ℝ) := by exact_mod_cast hK
  have ht0 : 0 ≤ t := (show 0 ≤ 2 * Real.pi * (K : ℝ) ^ 2 by positivity).trans htL
  obtain ⟨hML, _, _, hfar⟩ := sqrt_heightCell_frequency_cutoff hK htL htU
  have hmass := (summable_tsum_explicitPoissonFarMass_le hs
    (show 2 ≤ (K : ℝ) + 1 by linarith) (show (K : ℝ) + 1 ≤ N by linarith)
    ht0 hC₁0 hC₂0 hC₁ hC₂).1
  have heq : explicitPoissonFarMass sigma ((K : ℝ) + 1) N t =ᶠ[atTop] P := by
    filter_upwards [eventually_ge_atTop M] with m hm
    have hm1 : 1 ≤ m := by change M ≤ m at hm; change 2 * K ≤ M at hML; omega
    have hgap : t / ((K : ℝ) + 1 - 1) ≤ Real.pi * m := by
      simpa only [show (K : ℝ) + 1 - 1 = (K : ℝ) by ring] using hfar m hm
    simp only [explicitPoissonFarMass, hm1, hgap, and_self, if_pos, P, f]
  have hP : Summable P := hmass.congr_atTop heq
  have hpos : Summable (fun m : ℕ => f (m : ℤ)) := by
    apply Summable.of_norm_bounded hP
    intro m
    dsimp only [P]
    linarith [norm_nonneg (f (-(m : ℤ)))]
  have hneg : Summable (fun m : ℕ => f (-(m : ℤ))) := by
    apply Summable.of_norm_bounded hP
    intro m
    dsimp only [P]
    linarith [norm_nonneg (f (m : ℤ))]
  have hsucc : Function.Injective (fun m : ℕ => m + 1) := by
    intro m n h
    exact Nat.add_right_cancel h
  have hPtail : Summable (fun m : ℕ => P (m + 1)) := hP.comp_injective hsucc
  have hposTail : Summable (fun m : ℕ => f ((m + 1 : ℕ) : ℤ)) := hpos.comp_injective hsucc
  have hnegTail : Summable (fun m : ℕ => f (-((m + 1 : ℕ) : ℤ))) := hneg.comp_injective hsucc
  have hnegInt : Summable (fun m : ℕ => f (-((m : ℤ) + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hnegTail
  have hf : Summable f := Summable.of_nat_of_neg_add_one hpos hnegInt
  refine ⟨hPtail, hf, ?_⟩
  calc
    _ = (∑' m : ℕ, f (m : ℤ)) + ∑' m : ℕ, f (-((m : ℤ) + 1)) :=
      tsum_of_nat_of_neg_add_one hpos hnegInt
    _ = (f 0 + ∑' m : ℕ, f ((m + 1 : ℕ) : ℤ)) +
        ∑' m : ℕ, f (-((m + 1 : ℕ) : ℤ)) := by
      rw [hpos.tsum_eq_zero_add]
      simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one]
    _ = f 0 + ((∑' m : ℕ, f ((m + 1 : ℕ) : ℤ)) +
        ∑' m : ℕ, f (-((m + 1 : ℕ) : ℤ))) := by ring
    _ = _ := by rw [hposTail.tsum_add hnegTail]

end HardyTheorem.AFE
