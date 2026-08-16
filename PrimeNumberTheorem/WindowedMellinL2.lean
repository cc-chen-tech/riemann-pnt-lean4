import Mathlib

/-!
# L2 windowed Mellin response: analytic core

Self-contained analytic core of the L2 layer (windowed Mellin response):
the per-zero response integrals `∫_X^{X^lam} x^(ρ - 1 - iγ) dx` and their
endpoint bounds.  These are the exact statements consumed by the L3
threshold assembly; the truncated explicit formula identity that ties
them to the windowed detector signal lives with the cubic kernel modules
(`ZeroDensityLayerBudgetCubicKernelFactorization`).

Reference: `docs/research/windowed-detector-L2-mellin-response.md` and
`docs/research/lean-drafts/WindowedMellinL2Draft.lean`.

Contents

- `integralFactor ρ X lam γ`: the closed form
  `((X^lam)^(ρ-iγ) - X^(ρ-iγ)) / (ρ - iγ)` of the response integral.
- `integral_cpow_eq_integralFactor`: the complex-power fundamental
  theorem on `[X, X^lam]`.
- `integral_rpow_sub_one_eq`: the real seed integral
  `∫ x^(β-1) = ((X^lam)^β - X^β) / β`.
- `seedResponse_aligned_lowerBound`: at the aligned frequency the seed
  response is eventually `≥ X^(lamβ) / (2β)`.
- `complementaryResponse_le`: for `0 ≤ Re ρ` and `γ ≠ Im ρ`, the
  response of `ρ` is `≤ 2 (X^lam)^(Re ρ) / |γ - Im ρ|`.
-/

namespace PrimeNumberTheorem
namespace WindowedMellinL2

open scoped BigOperators
open Filter

/-- The complex windowed response factor (closed form of the response
integral): `∫_X^{X^lam} x^(ρ - 1 - iγ) dx = ((X^lam)^(ρ-iγ) - X^(ρ-iγ)) / (ρ - iγ)`. -/
noncomputable def integralFactor (ρ : ℂ) (X lam γ : ℝ) : ℂ :=
  (((X ^ lam : ℝ) : ℂ) ^ (ρ - Complex.I * γ) - (X : ℂ) ^ (ρ - Complex.I * γ))
    / (ρ - Complex.I * γ)

/-- Norm of a positive-real complex power: `‖x^z‖ = x^(Re z)`. -/
lemma norm_cpow_ofReal_pos {t : ℝ} {z : ℂ} (ht : 0 < t) :
    ‖(t : ℂ) ^ z‖ = t ^ z.re := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt ht) z]
  rw [Complex.norm_exp]
  rw [Complex.mul_re]
  rw [Complex.log_ofReal_re t, Complex.log_im (t : ℂ), Complex.arg_ofReal_of_nonneg ht.le]
  have harg : Real.log t * z.re - 0 * z.im = Real.log t * z.re := by ring
  rw [harg]
  rw [← Real.rpow_def_of_pos ht z.re]

/-- The complex-power fundamental theorem on `[X, X^lam]`: the response
integral equals the endpoint factor. -/
theorem integral_cpow_eq_integralFactor {ρ : ℂ} {X lam γ : ℝ}
    (hX : 0 < X) (hlampos : 0 < X ^ lam) (hz : ρ - Complex.I * γ ≠ 0) :
    (∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)) =
      integralFactor ρ X lam γ := by
  let z : ℂ := ρ - Complex.I * γ
  have hz' : z ≠ 0 := by simpa [z] using hz
  have hmem_pos : ∀ t ∈ Set.uIcc X (X ^ lam), 0 < t := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact lt_of_lt_of_le hX h1
    · exact lt_of_lt_of_le hlampos h2
  have hderiv {t : ℝ} (ht : t ≠ 0) :
      HasDerivAt (fun s : ℝ => (s : ℂ) ^ z) (z * (t : ℂ) ^ (z - 1)) t := by
    simpa using (hasDerivAt_ofReal_cpow_const (x := t) ht (r := z) hz')
  have hF {t : ℝ} (ht : t ≠ 0) :
      HasDerivAt (fun s : ℝ => (s : ℂ) ^ z / z) ((t : ℂ) ^ (z - 1)) t := by
    have hm : HasDerivAt (fun s : ℝ => (s : ℂ) ^ z * z⁻¹)
        ((z * (t : ℂ) ^ (z - 1)) * z⁻¹) t :=
      (hderiv ht).mul_const z⁻¹
    have hval : (z * (t : ℂ) ^ (z - 1)) * z⁻¹ = (t : ℂ) ^ (z - 1) := by
      rw [← div_eq_mul_inv]
      field_simp [hz']
    simpa [hval] using hm
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (z - 1)) (Set.uIcc X (X ^ lam)) := by
    exact ContinuousOn.cpow_const
      (f := fun t : ℝ => (t : ℂ)) (b := z - 1)
      Complex.continuous_ofReal.continuousOn
      (fun t ht => (Complex.ofReal_mem_slitPlane).mpr (hmem_pos t ht))
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => (s : ℂ) ^ z / z) (f' := fun t : ℝ => (t : ℂ) ^ (z - 1))
    (a := X) (b := X ^ lam)
    (fun t ht => hF (by exact ne_of_gt (hmem_pos t ht)))
    hcont.intervalIntegrable
  dsimp [integralFactor, z]
  rw [sub_div]
  exact hmain

/-- The real seed-response integral on `[X, X^lam]`:
`∫ x^(β-1) = ((X^lam)^β - X^β) / β`. -/
theorem integral_rpow_sub_one_eq {X lam β : ℝ} (hX : 0 < X) (hlampos : 0 < X ^ lam)
    (hβ : β ≠ 0) :
    (∫ x in X..X ^ lam, x ^ (β - 1)) = ((X ^ lam) ^ β - X ^ β) / β := by
  have hmem_pos : ∀ t ∈ Set.uIcc X (X ^ lam), 0 < t := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact lt_of_lt_of_le hX h1
    · exact lt_of_lt_of_le hlampos h2
  have hderiv {t : ℝ} (ht : t ≠ 0) :
      HasDerivAt (fun s : ℝ => s ^ β) (β * t ^ (β - 1)) t := by
    simpa using (Real.hasDerivAt_rpow_const (p := β) (x := t) (Or.inl ht))
  have hF {t : ℝ} (ht : t ≠ 0) :
      HasDerivAt (fun s : ℝ => s ^ β / β) (t ^ (β - 1)) t := by
    have hm : HasDerivAt (fun s : ℝ => s ^ β * β⁻¹) ((β * t ^ (β - 1)) * β⁻¹) t :=
      (hderiv ht).mul_const β⁻¹
    have hval : (β * t ^ (β - 1)) * β⁻¹ = t ^ (β - 1) := by
      rw [← div_eq_mul_inv]
      field_simp [hβ]
    simpa [hval] using hm
  have hcont : ContinuousOn (fun t : ℝ => t ^ (β - 1)) (Set.uIcc X (X ^ lam)) := by
    intro t ht
    exact (Real.continuousAt_rpow_const t (β - 1) (Or.inl (ne_of_gt (hmem_pos t ht)))).continuousWithinAt
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => s ^ β / β) (f' := fun t : ℝ => t ^ (β - 1))
    (a := X) (b := X ^ lam)
    (fun t ht => hF (by exact ne_of_gt (hmem_pos t ht)))
    hcont.intervalIntegrable
  rw [sub_div]
  exact hmain

/-- L2 TARGET (seed lower bound, aligned frequency): the seed response is
eventually `≥ X^(lamβ) / (2β)`. -/
theorem seedResponse_aligned_lowerBound {lam β : ℝ} (hlam : 1 < lam) (hβ : 0 < β) :
    ∀ᶠ X in atTop, X ^ (lam * β) / (2 * β) ≤ ∫ x in X..X ^ lam, x ^ (β - 1) := by
  have htend : Filter.Tendsto (fun X : ℝ => X ^ ((lam - 1) * β)) atTop atTop :=
    tendsto_rpow_atTop (mul_pos (sub_pos.mpr hlam) hβ)
  have htwo : ∀ᶠ (X : ℝ) in atTop, 2 ≤ X ^ ((lam - 1) * β) :=
    htend.eventually (Filter.eventually_ge_atTop (2 : ℝ))
  have hX1ev : ∀ᶠ (X : ℝ) in atTop, 1 ≤ X := Filter.eventually_ge_atTop (1 : ℝ)
  filter_upwards [htwo, hX1ev] with X h2le hX1
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hXlam0 : 0 < X ^ lam := Real.rpow_pos_of_pos hX lam
  have hβ' : β ≠ 0 := ne_of_gt hβ
  rw [integral_rpow_sub_one_eq hX hXlam0 hβ']
  have hpowmul : (X ^ lam) ^ β = X ^ (lam * β) := by
    rw [← Real.rpow_mul hX.le lam β]
  have hsub : X ^ (lam * β) / 2 ≤ X ^ (lam * β) - X ^ β := by
    have hmul : X ^ β * X ^ ((lam - 1) * β) = X ^ (lam * β) := by
      rw [← Real.rpow_add hX β ((lam - 1) * β)]
      congr 1
      ring
    have h1 : X ^ β * 2 ≤ X ^ (lam * β) := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_left h2le (Real.rpow_nonneg hX.le β)
    nlinarith [h1, (Real.rpow_nonneg hX.le β)]
  calc
    X ^ (lam * β) / (2 * β) = X ^ (lam * β) / 2 / β := by
      field_simp [hβ']
    _ ≤ (X ^ (lam * β) - X ^ β) / β := by
      exact div_le_div_of_nonneg_right hsub hβ.le
    _ = ((X ^ lam) ^ β - X ^ β) / β := by
      rw [← hpowmul]

/-- L2 TARGET (complementary upper bound): for `0 ≤ Re ρ` and `γ ≠ Im ρ`,
the response at frequency `γ` is bounded by `2 (X^lam)^(Re ρ) / |γ - Im ρ|`. -/
theorem complementaryResponse_le {ρ : ℂ} {X lam γ : ℝ}
    (hX : 1 < X) (hlam : 1 < lam) (hre : 0 ≤ ρ.re) (hz : ρ - Complex.I * γ ≠ 0)
    (hγ : γ ≠ ρ.im) :
    ‖∫ x in X..X ^ lam, (x : ℂ) ^ (ρ - Complex.I * γ - 1)‖ ≤
      2 * (X ^ lam) ^ ρ.re / |γ - ρ.im| := by
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hXlam0 : 0 < X ^ lam := Real.rpow_pos_of_pos hX0 lam
  have hftc := integral_cpow_eq_integralFactor hX0 hXlam0 hz
  rw [hftc]
  dsimp [integralFactor]
  have hXle : X ≤ X ^ lam := by
    have h1 : X ^ (1 : ℝ) ≤ X ^ lam :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hX) hlam.le
    simpa [Real.rpow_one] using h1
  have hA : ‖((X ^ lam : ℝ) : ℂ) ^ (ρ - Complex.I * γ)‖ = (X ^ lam) ^ ρ.re := by
    simpa [Complex.sub_re, Complex.mul_re, Complex.mul_im] using
      (norm_cpow_ofReal_pos (t := X ^ lam) (z := ρ - Complex.I * γ) hXlam0)
  have hB : ‖(X : ℂ) ^ (ρ - Complex.I * γ)‖ = X ^ ρ.re := by
    simpa [Complex.sub_re, Complex.mul_re, Complex.mul_im] using
      (norm_cpow_ofReal_pos (t := X) (z := ρ - Complex.I * γ) hX0)
  have hXrpow : X ^ ρ.re ≤ (X ^ lam) ^ ρ.re :=
    Real.rpow_le_rpow hX0.le hXle hre
  have hd : |γ - ρ.im| ≤ ‖ρ - Complex.I * γ‖ := by
    have h1 : |(ρ - Complex.I * γ).im| ≤ ‖ρ - Complex.I * γ‖ := Complex.abs_im_le_norm _
    have h2 : (ρ - Complex.I * γ).im = ρ.im - γ := by
      simp [Complex.sub_im, Complex.mul_im]
    rwa [h2, abs_sub_comm] at h1
  have hγpos : 0 < |γ - ρ.im| := abs_pos.mpr (sub_ne_zero.mpr hγ)
  calc
    ‖(((X ^ lam : ℝ) : ℂ) ^ (ρ - Complex.I * γ) - (X : ℂ) ^ (ρ - Complex.I * γ)) / (ρ - Complex.I * γ)‖
        ≤ (‖((X ^ lam : ℝ) : ℂ) ^ (ρ - Complex.I * γ)‖ + ‖(X : ℂ) ^ (ρ - Complex.I * γ)‖) / ‖ρ - Complex.I * γ‖ := by
      rw [norm_div]
      exact div_le_div_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ ((X ^ lam) ^ ρ.re + X ^ ρ.re) / ‖ρ - Complex.I * γ‖ := by
      rw [hA, hB]
    _ ≤ ((X ^ lam) ^ ρ.re + X ^ ρ.re) / |γ - ρ.im| := by
      exact div_le_div_of_nonneg_left
        (add_nonneg (Real.rpow_nonneg hXlam0.le ρ.re) (Real.rpow_nonneg hX0.le ρ.re))
        hγpos hd
    _ ≤ ((X ^ lam) ^ ρ.re + (X ^ lam) ^ ρ.re) / |γ - ρ.im| := by
      exact div_le_div_of_nonneg_right (add_le_add_right hXrpow _) hγpos.le
    _ = 2 * (X ^ lam) ^ ρ.re / |γ - ρ.im| := by ring

end WindowedMellinL2
end PrimeNumberTheorem
