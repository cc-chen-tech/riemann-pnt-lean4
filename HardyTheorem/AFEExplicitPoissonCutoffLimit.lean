import HardyTheorem.AFEExplicitPoissonFiniteBudget

/-! Remove the upper cutoff from the whole primal expression.  No limit is
exchanged with the infinite Poisson series or with an individual mode. -/

open Complex Filter
open scoped Topology

namespace HardyTheorem.AFE

/-- The first zeta approximation and the uniform finite-cutoff budget imply
the actual critical-line zeta estimate with its finite dual Gamma sum. -/
theorem norm_riemannZeta_sub_primal_sub_dualGamma_le
    {C₁ C₂ t : ℝ} {K : ℕ} (hK : 6 ≤ K)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    let s : ℂ := (1 / 2 : ℂ) + I * t
    let M := Nat.ceil (t / (Real.pi * K))
    ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (-s)) -
        (∑ m ∈ Finset.Icc 1 K, poissonGammaTerm (1 / 2) t m)‖ ≤
      explicitPoissonCriticalFiniteConstant C₁ C₂ * (K : ℝ) ^ (-(1 / 2) : ℝ) *
        (1 + Real.log M) := by
  let s : ℂ := (1 / 2 : ℂ) + I * t
  let M := Nat.ceil (t / (Real.pi * K))
  let D : ℂ := ∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (-s)
  let G : ℂ := ∑ m ∈ Finset.Icc 1 K, poissonGammaTerm (1 / 2) t m
  let B := explicitPoissonCriticalFiniteConstant C₁ C₂ *
    (K : ℝ) ^ (-(1 / 2) : ℝ) * (1 + Real.log M)
  let V : ℕ → ℂ := fun N =>
    (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (1 - s)
  have hsre : s.re = 1 / 2 := by norm_num [s]
  have hsim : s.im = t := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num [hsre] at h'
  have hK0 : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have ht0 : 0 < t := (show 0 < 2 * Real.pi * (K : ℝ) ^ 2 by positivity).trans_le htL
  obtain ⟨C, _, happrox⟩ := exists_riemannZeta_first_approximation
  let Q := (K : ℝ) - 1 + (4 / Real.pi) * (harmonic (K - 2) : ℝ) + C
  have hevent : ∀ᶠ N : ℕ in atTop,
      ‖riemannZeta s - D - G‖ ≤ B + Q * (N : ℝ) ^ (-(1 / 2) : ℝ) := by
    have hlarge : ∀ᶠ N : ℕ in atTop, 2 * t ≤ (N : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * t)
    filter_upwards [eventually_ge_atTop (2 * K), hlarge] with N hN hNt
    have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hfar : 2 * t ≤ 2 * Real.pi * (N : ℝ) := by
      have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      have hmul := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      nlinarith
    obtain ⟨E, hEeq, hE⟩ := happrox s N
      (by rw [hsre]; norm_num) (by rw [hsre]; norm_num) hs1 hN1
      (by rw [hsim, abs_of_pos ht0]; linarith)
    have hpole : (N : ℂ) ^ (1 - s) / (s - 1) =
        -((N : ℂ) ^ (1 - s) / (1 - s)) := by
      rw [show s - 1 = -(1 - s) by ring, div_neg]
    have hz : riemannZeta s = V N + E := by
      simp only [Nat.floor_natCast, Complex.ofReal_natCast, one_div,
        ← Complex.cpow_neg] at hEeq
      rw [hpole] at hEeq
      simpa only [V, sub_eq_add_neg] using hEeq
    rw [hsre] at hE
    have hfin : ‖V N - D - G‖ ≤ B +
        ((K : ℝ) - 1 + (4 / Real.pi) * (harmonic (K - 2) : ℝ)) *
          (N : ℝ) ^ (-(1 / 2) : ℝ) :=
      norm_dirichlet_sum_sub_pole_sub_dualGamma_le
        hK hN htL htU hfar hC₁0 hC₂0 hC₁ hC₂
    have htriangle : ‖riemannZeta s - D - G‖ ≤ ‖V N - D - G‖ + ‖E‖ := by
      rw [hz, show V N + E - D - G = (V N - D - G) + E by ring]
      exact norm_add_le _ _
    exact (htriangle.trans (add_le_add hfin hE)).trans_eq (by dsimp only [Q]; ring)
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => B + Q * (N : ℝ) ^ (-(1 / 2) : ℝ)) atTop (𝓝 B) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hpow) :
        Tendsto (fun N : ℕ => B + Q * (N : ℝ) ^ (-(1 / 2) : ℝ)) atTop (𝓝 (B + Q * 0)))
  exact ge_of_tendsto hlim hevent

end HardyTheorem.AFE
