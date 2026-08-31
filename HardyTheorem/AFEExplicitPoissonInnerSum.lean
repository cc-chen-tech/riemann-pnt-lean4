import HardyTheorem.AFEExplicitPoissonInnerMode
import HardyTheorem.AFEEndpointHarmonic

/-! Exact harmonic summation of the inner stationary Gamma errors. -/

open Complex Set MeasureTheory

namespace HardyTheorem.AFE

private theorem sum_reciprocal_inner_gap_le_harmonic {beta : ℝ} (R : ℕ)
    (hbeta : (R : ℝ) + 1 ≤ beta) :
    (∑ m ∈ Finset.Icc 1 R, (beta - (m : ℝ))⁻¹) ≤ (harmonic R : ℝ) := by
  have hreflect : (∑ m ∈ Finset.Icc 1 R, (((R + 1 - m : ℕ) : ℝ))⁻¹) =
      ∑ j ∈ Finset.Icc 1 R, (j : ℝ)⁻¹ := by
    refine Finset.sum_bij (fun m _ => R + 1 - m) ?_ ?_ ?_ ?_
    · intro m hm
      have hm' := Finset.mem_Icc.mp hm
      exact Finset.mem_Icc.mpr (by omega)
    · intro m hm n hn hmn
      have hm' := Finset.mem_Icc.mp hm
      have hn' := Finset.mem_Icc.mp hn
      omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      exact ⟨R + 1 - j, Finset.mem_Icc.mpr (by omega), by omega⟩
    · intro m _
      rfl
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 R, (((R + 1 - m : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      obtain ⟨hm1, hmR⟩ := Finset.mem_Icc.mp hm
      have hj : 0 < (((R + 1 - m : ℕ) : ℝ)) := by
        exact_mod_cast (show 0 < R + 1 - m by omega)
      have hden : (((R + 1 - m : ℕ) : ℝ)) ≤ beta - m := by
        rw [Nat.cast_sub (by omega : m ≤ R + 1), Nat.cast_add, Nat.cast_one]
        linarith
      exact (inv_le_inv₀ (hj.trans_le hden) hj).mpr hden
    _ = ∑ j ∈ Finset.Icc 1 R, (j : ℝ)⁻¹ := hreflect
    _ = _ := by
      rw [harmonic_eq_sum_Icc]
      simp

/-- Sum all inner mode errors with an exact harmonic coefficient and a
vanishing upper-cutoff remainder.  The nearest frequency is excluded by
the explicit one-unit endpoint gap. -/
theorem sum_norm_explicitPoissonMode_sub_gamma_le_harmonic
    {C₁ sigma x t : ℝ} {N R : ℕ}
    (hs0 : 0 < sigma) (hs1 : sigma < 1) (hx : 1 < x) (hxN : x ≤ (N : ℝ))
    (hbeta : (R : ℝ) + 1 ≤ t / (2 * Real.pi * x))
    (hfar : 2 * t ≤ 2 * Real.pi * (N : ℝ)) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∑ m ∈ Finset.Icc 1 R,
      ‖explicitPoissonMode sigma x N t (-(m : ℤ)) - poissonGammaTerm sigma t m‖) ≤
      ((3 + 8 * C₁) / Real.pi) * (x - 1) ^ (-sigma) * (harmonic R : ℝ) +
      ((R : ℝ) + (4 / Real.pi) * (harmonic R : ℝ)) * (N : ℝ) ^ (-sigma) := by
  have hx0 : 0 < x := by linarith
  let beta : ℝ := t / (2 * Real.pi * x)
  let A : ℝ := ((3 + 8 * C₁) / Real.pi) * (x - 1) ^ (-sigma)
  let Z : ℝ := (N : ℝ) ^ (-sigma)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hhar : (∑ m ∈ Finset.Icc 1 R, (m : ℝ)⁻¹) = (harmonic R : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp
  have hsum : (∑ m ∈ Finset.Icc 1 R,
      ‖explicitPoissonMode sigma x N t (-(m : ℤ)) - poissonGammaTerm sigma t m‖) ≤
      A * (∑ m ∈ Finset.Icc 1 R, (beta - (m : ℝ))⁻¹) +
        ((R : ℝ) + (4 / Real.pi) * (harmonic R : ℝ)) * Z := by
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 R,
          (A * (beta - (m : ℝ))⁻¹ + (1 + (4 / Real.pi) * (m : ℝ)⁻¹) * Z) := by
        apply Finset.sum_le_sum
        intro m hm
        obtain ⟨hm1, hmR⟩ := Finset.mem_Icc.mp hm
        have hm1R : 1 ≤ (m : ℝ) := by exact_mod_cast hm1
        have hmRR : (m : ℝ) ≤ (R : ℝ) := by exact_mod_cast hmR
        have hm_beta : (m : ℝ) < t / (2 * Real.pi * x) := by linarith
        have hgap : 2 * Real.pi * (m : ℝ) * x < t := by
          have h := (lt_div_iff₀ (show 0 < 2 * Real.pi * x by positivity)).mp hm_beta
          nlinarith
        have hfar_m : 2 * t ≤ 2 * Real.pi * (m : ℝ) * (N : ℝ) := by
          have h := mul_le_mul_of_nonneg_left hm1R
            (show 0 ≤ 2 * Real.pi * (N : ℝ) by positivity)
          nlinarith
        calc
          _ ≤ ((3 + 8 * C₁) / Real.pi) * (x - 1) ^ (-sigma) /
              (t / (2 * Real.pi * x) - m) +
              (1 + 4 / (Real.pi * m)) * (N : ℝ) ^ (-sigma) :=
            norm_explicitPoissonMode_sub_gamma_le hs0 hs1 hx hxN hm1 hgap hfar_m hC₁0 hC₁
          _ = _ := by
            dsimp only [A, beta, Z]
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          Finset.sum_add_distrib, ← Finset.mul_sum, hhar]
        simp
  exact hsum.trans (add_le_add
    (mul_le_mul_of_nonneg_left (sum_reciprocal_inner_gap_le_harmonic R hbeta) hA) le_rfl)

/-- The square-root height cell supplies the inner-band gap for `1<=m<=K-2`. -/
theorem sum_norm_explicitPoissonMode_inner_sqrt_sub_gamma_le
    {C₁ sigma t : ℝ} {K N : ℕ}
    (hs0 : 0 < sigma) (hs1 : sigma < 1) (hK : 3 ≤ K) (hN : K + 1 ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (hfar : 2 * t ≤ 2 * Real.pi * (N : ℝ)) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∑ m ∈ Finset.Icc 1 (K - 2),
      ‖explicitPoissonMode sigma ((K : ℝ) + 1) N t (-(m : ℤ)) - poissonGammaTerm sigma t m‖) ≤
      ((3 + 8 * C₁) / Real.pi) * (K : ℝ) ^ (-sigma) * (harmonic (K - 2) : ℝ) +
      (((K - 2 : ℕ) : ℝ) + (4 / Real.pi) * (harmonic (K - 2) : ℝ)) * (N : ℝ) ^ (-sigma) := by
  have hK0 : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hbeta : (((K - 2 : ℕ) : ℝ) + 1) ≤ t / (2 * Real.pi * ((K : ℝ) + 1)) := by
    rw [Nat.cast_sub (by omega : 2 ≤ K)]
    push_cast
    apply (le_div_iff₀ (show 0 < 2 * Real.pi * ((K : ℝ) + 1) by positivity)).mpr
    nlinarith [Real.pi_pos]
  have h := sum_norm_explicitPoissonMode_sub_gamma_le_harmonic
    hs0 hs1 (show 1 < (K : ℝ) + 1 by linarith)
    (show (K : ℝ) + 1 ≤ (N : ℝ) by exact_mod_cast hN) hbeta hfar hC₁0 hC₁
  simpa only [show (K : ℝ) + 1 - 1 = (K : ℝ) by ring] using h

end HardyTheorem.AFE
