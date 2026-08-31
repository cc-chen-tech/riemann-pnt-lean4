import HardyTheorem.AFEExplicitPoissonAbsoluteSum

/-! Truncating the actual absolutely convergent Poisson series at its exact
height-dependent frequency cutoff.  The upper spatial cutoff stays finite. -/

namespace HardyTheorem.AFE

private theorem sum_range_succ_eq_Icc (f : ℕ → ℂ) (M : ℕ) :
    (∑ m ∈ Finset.range M, f (m + 1)) = ∑ m ∈ Finset.Icc 1 M, f m := by
  apply Finset.sum_bij (fun (m : ℕ) _ => m + 1)
  · intro m hm
    simp only [Finset.mem_range] at hm
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro m hm n hn h
    exact Nat.add_right_cancel h
  · intro m hm
    rcases Finset.mem_Icc.mp hm with ⟨h1, hM⟩
    exact ⟨m - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro m hm
    rfl

/-- Both tails, with their actual signs and no unproved convergence input,
are bounded by the proven nonnegative far-frequency mass. -/
theorem norm_explicitPoisson_tsum_sub_finite_modes_le
    {C₁ C₂ sigma N t : ℝ} {K : ℕ}
    (hs : 0 < sigma) (hK : 6 ≤ K) (hN : 2 * (K : ℝ) ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    let M := Nat.ceil (t / (Real.pi * K))
    let f := explicitPoissonMode sigma ((K : ℝ) + 1) N t
    ‖(∑' k : ℤ, f k) - f 0 -
        (∑ m ∈ Finset.Icc 1 M, f (m : ℤ)) -
        (∑ m ∈ Finset.Icc 1 M, f (-(m : ℤ)))‖ ≤
      4 * explicitPoissonFarConstant C₁ C₂ sigma * (K : ℝ) ^ (-sigma) / Real.pi ^ 2 := by
  let M := Nat.ceil (t / (Real.pi * K))
  let f := explicitPoissonMode sigma ((K : ℝ) + 1) N t
  let g : ℕ → ℂ := fun m => f ((m + 1 : ℕ) : ℤ) + f (-((m + 1 : ℕ) : ℤ))
  let mass := explicitPoissonFarMass sigma ((K : ℝ) + 1) N t
  let e : ℕ → ℕ := fun m => m + M + 1
  have hK6 : 6 ≤ (K : ℝ) := by exact_mod_cast hK
  have ht0 : 0 ≤ t := (show 0 ≤ 2 * Real.pi * (K : ℝ) ^ 2 by positivity).trans htL
  obtain ⟨hpair, _, htsum⟩ := explicitPoissonMode_summable_and_tsum_pairs
    hs hK hN htL htU hC₁0 hC₂0 hC₁ hC₂
  have hg : Summable g := Summable.of_norm_bounded hpair (fun m => norm_add_le _ _)
  have hsplit := hg.sum_add_tsum_nat_add M
  have hfinite : (∑ m ∈ Finset.range M, g m) =
      (∑ m ∈ Finset.Icc 1 M, f (m : ℤ)) +
        (∑ m ∈ Finset.Icc 1 M, f (-(m : ℤ))) := by
    rw [sum_range_succ_eq_Icc (fun m => f (m : ℤ) + f (-(m : ℤ))) M,
      Finset.sum_add_distrib]
  have hresidual : (∑' k : ℤ, f k) - f 0 -
      (∑ m ∈ Finset.Icc 1 M, f (m : ℤ)) -
      (∑ m ∈ Finset.Icc 1 M, f (-(m : ℤ))) = ∑' m : ℕ, g (m + M) := by
    rw [htsum, ← hsplit, hfinite]
    ring
  change ‖(∑' k : ℤ, f k) - f 0 - (∑ m ∈ Finset.Icc 1 M, f (m : ℤ)) -
    (∑ m ∈ Finset.Icc 1 M, f (-(m : ℤ)))‖ ≤ _
  rw [hresidual]
  obtain ⟨hmass, hbound⟩ := summable_tsum_explicitPoissonFarMass_le hs
    (show 2 ≤ (K : ℝ) + 1 by linarith) (show (K : ℝ) + 1 ≤ N by linarith)
    ht0 hC₁0 hC₂0 hC₁ hC₂
  have he : Function.Injective e := by
    intro m n h
    dsimp only [e] at h
    omega
  have hmassTail : Summable (fun m => mass (e m)) := hmass.comp_injective he
  have hnonneg (m : ℕ) : 0 ≤ mass m := by
    dsimp only [mass, explicitPoissonFarMass]
    split_ifs <;> positivity
  have hsubset : (∑' m : ℕ, mass (e m)) ≤ ∑' m : ℕ, mass m :=
    Summable.tsum_le_tsum_of_inj e he (fun m _ => hnonneg m)
      (fun _ => le_rfl) hmassTail hmass
  have hgap := (sqrt_heightCell_frequency_cutoff hK htL htU).2.2.2
  have hpoint (m : ℕ) : ‖g (m + M)‖ ≤ mass (e m) := by
    have hm1 : 1 ≤ e m := by dsimp only [e]; omega
    have hfar : t / ((K : ℝ) + 1 - 1) ≤ Real.pi * e m := by
      simpa only [show (K : ℝ) + 1 - 1 = (K : ℝ) by ring] using
        hgap (e m) (show M ≤ e m by dsimp only [e]; omega)
    simp only [mass, explicitPoissonFarMass, hm1, hfar, and_self, if_pos]
    exact norm_add_le _ _
  exact (tsum_of_norm_bounded hmassTail.hasSum hpoint).trans
    (hsubset.trans (by simpa only [show (K : ℝ) + 1 - 1 = (K : ℝ) by ring] using hbound))

end HardyTheorem.AFE
