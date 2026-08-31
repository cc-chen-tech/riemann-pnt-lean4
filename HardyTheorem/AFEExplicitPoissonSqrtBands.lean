import HardyTheorem.AFEExplicitPoissonFrequencyCutoff
import HardyTheorem.AFEExplicitPoissonFiniteBand
import HardyTheorem.AFEExplicitPoissonEndpointMode

/-! Exact finite negative-frequency bands in a square-root height cell. -/

namespace HardyTheorem.AFE

/-- The modes `K+4,...,M` inject into the proven nonstationary harmonic band.
The omitted nearest integer is contained in the separate five-mode band. -/
theorem sum_norm_explicitPoissonMode_sqrt_above_le_log
    {C₁ sigma N t : ℝ} {K : ℕ}
    (hs : 0 < sigma) (hK : 6 ≤ K) (hN : 2 * (K : ℝ) ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    let M := Nat.ceil (t / (Real.pi * K))
    (∑ m ∈ Finset.Icc (K + 4) M,
      ‖explicitPoissonMode sigma ((K : ℝ) + 1) N t (-(m : ℤ))‖) ≤
      (8 * C₁ * (K : ℝ) ^ (-sigma) / Real.pi) * (1 + Real.log M) := by
  classical
  let M := Nat.ceil (t / (Real.pi * K))
  let b := Nat.floor (t / (2 * Real.pi * (K : ℝ)))
  let F : ℕ → ℝ := fun m => ‖explicitPoissonMode sigma ((K : ℝ) + 1) N t (-(m : ℤ))‖
  have hK6 : 6 ≤ (K : ℝ) := by exact_mod_cast hK
  have ht0 : 0 ≤ t := (show 0 ≤ 2 * Real.pi * (K : ℝ) ^ 2 by positivity).trans htL
  have hb : b ≤ K + 2 := (sqrt_heightCell_frequency_cutoff hK htL htU).2.2.1
  have hsubset : Finset.Icc (K + 4) M ⊆
      (Finset.Icc 1 M).image (fun j => b + 1 + j) := by
    intro m hm
    rcases Finset.mem_Icc.mp hm with ⟨hml, hmM⟩
    refine Finset.mem_image.mpr ⟨m - (b + 1), Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩ <;> omega
  have hsum : (∑ m ∈ Finset.Icc (K + 4) M, F m) ≤
      ∑ j ∈ Finset.Icc 1 M, F (b + 1 + j) := by
    calc
      _ ≤ ∑ m ∈ (Finset.Icc 1 M).image (fun j => b + 1 + j), F m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun m _ _ => norm_nonneg _)
      _ = _ := Finset.sum_image (fun m _ n _ h => Nat.add_left_cancel h)
  have hband := sum_norm_explicitPoissonMode_above_endpoint_le_log M hs
    (show 1 < (K : ℝ) + 1 by linarith) (show (K : ℝ) + 1 ≤ N by linarith)
    ht0 hC₁0 hC₁
  exact hsum.trans (by
    simpa only [show (K : ℝ) + 1 - 1 = (K : ℝ) by ring] using hband)

/-- Only five modes are charged to the uniform stationary-endpoint bound. -/
theorem sum_norm_explicitPoissonMode_five_sqrt_endpoints_le
    {C₁ sigma N t : ℝ} {K : ℕ}
    (hs : 0 < sigma) (hK : 6 ≤ K) (hN : 2 * (K : ℝ) ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∑ m ∈ Finset.Icc (K - 1) (K + 3),
      ‖explicitPoissonMode sigma ((K : ℝ) + 1) N t (-(m : ℤ))‖) ≤
      5 * (12 * (4 * C₁ + 2) / Real.sqrt (Real.pi / 2) +
        4 * (1 + 4 * C₁) / Real.pi) * (K : ℝ) ^ (-sigma) := by
  have hK6 : 6 ≤ (K : ℝ) := by exact_mod_cast hK
  have hcard : (Finset.Icc (K - 1) (K + 3)).card = 5 := by
    rw [Nat.card_Icc]
    omega
  calc
    _ ≤ ∑ _m ∈ Finset.Icc (K - 1) (K + 3),
        (12 * (4 * C₁ + 2) / Real.sqrt (Real.pi / 2) +
          4 * (1 + 4 * C₁) / Real.pi) * (K : ℝ) ^ (-sigma) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmK : (K : ℝ) - 1 ≤ (m : ℝ) := by
        have h := (Finset.mem_Icc.mp hm).1
        have h' : ((K - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast h
        simpa only [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one] using h'
      exact norm_explicitPoissonMode_near_sqrt_endpoint_le
        hs hK6 hN htL htU hmK hC₁0 hC₁
    _ = _ := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      push_cast
      ring

end HardyTheorem.AFE
