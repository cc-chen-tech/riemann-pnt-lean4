import PrimeNumberTheorem.MWKFCubicAFEJointSmooth
import PrimeNumberTheorem.MWKFCubicAFEDyadicMoment

open Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The actual dyadic frequency sum after physical time integration

Apply Poisson to the actual integrated Schwartz kernel. Exact lattice
reindexing and the already proved finite-support lattice/time interchange
then identify it with the integral of the original dyadic Poisson box.
No parameter-uniform Fourier majorant or cross-box frequency exchange is used.
-/

private theorem fourier_pos_dilate (f : ℝ → ℂ) {s : ℝ} (hs : 0 < s) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ f (s * x)) ξ = (s⁻¹ : ℂ) * 𝓕 f (ξ / s) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  let g : ℝ → ℂ := fun y ↦ Complex.exp (((-2 * Real.pi * y * (ξ / s) : ℝ) : ℂ) * I) * f y
  have heq : (fun x : ℝ ↦ Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * I) * f (s * x)) =
      fun x ↦ g (s * x) := by
    funext x
    dsimp only [g]
    have hc : -2 * Real.pi * (s * x) * (ξ / s) = -2 * Real.pi * x * ξ := by
      calc
        _ = (-2 * Real.pi * x) * (s * (ξ / s)) := by ring
        _ = _ := by rw [mul_div_cancel₀ ξ hs.ne']
    rw [hc]
  rw [heq, Measure.integral_comp_mul_left]
  simp only [abs_of_pos (inv_pos.mpr hs), Complex.real_smul, Complex.ofReal_inv]
  rfl

private theorem smooth_compact_poisson_scaled (K : ℝ → ℂ)
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {s : ℝ} (hs : 0 < s) (a : ℝ) :
    (∑' j : ℤ, K (a + s * j)) = (s⁻¹ : ℂ) * ∑' h : ℤ,
      𝓕 K ((h : ℝ) / s) * Complex.exp (2 * (Real.pi : ℂ) * I * (h : ℂ) * (a : ℂ) / (s : ℂ)) := by
  have hGc : HasCompactSupport (fun x : ℝ ↦ K (s * x)) := by
    simpa only [smul_eq_mul] using hc.comp_smul hs.ne'
  let G : 𝓢(ℝ, ℂ) := hGc.toSchwartzMap (hK.comp (contDiff_const.mul contDiff_id))
  have hp := G.tsum_eq_tsum_fourier (a / s)
  have hl : (∑' j : ℤ, G (a / s + j)) = ∑' j : ℤ, K (a + s * j) := by
    apply tsum_congr
    intro j
    change K (s * (a / s + (j : ℝ))) = _
    rw [mul_add, mul_div_cancel₀ a hs.ne']
  rw [hl] at hp
  rw [hp, ← tsum_mul_left]
  apply tsum_congr
  intro h
  have hf : (𝓕 G) h = (s⁻¹ : ℂ) * 𝓕 K ((h : ℝ) / s) := fourier_pos_dilate K hs h
  rw [hf, fourier_coe_apply]
  simp only [Complex.ofReal_one, div_one, Complex.ofReal_div]
  ring

private theorem integrated_progression_eq_lattice
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e) {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) :
    (∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
      cubicAFEProgressionCutoffSummand W T X V χ t m.val) =
    ∑' j : ℤ, ∫ t : ℝ, cubicAFEProgressionCutoffSummand W T X V χ t
      (cubicAFEProgressionLattice d e δ j : ℝ) := by
  let K : ℝ → ℂ := fun x ↦ ∫ t : ℝ, cubicAFEProgressionCutoffSummand W T X V χ t x
  let f : ℤ → ℂ := fun j ↦ K (cubicAFEProgressionLattice d e δ j : ℝ)
  let g : cubicAFEProgression d e δ → ℤ := fun m ↦ cubicAFEProgressionLatticeIndex d e δ m.val
  have hi : ∀ m : cubicAFEProgression d e δ,
      cubicAFEProgressionLattice d e δ (g m) = (m.val : ℤ) :=
    fun m ↦ cubicAFEProgressionLattice_index he m.property
  have hginj : Function.Injective g := by
    intro m n h
    apply Subtype.ext
    have hz : (m.val : ℤ) = (n.val : ℤ) := by rw [← hi m, ← hi n, h]
    exact_mod_cast hz
  have hsupport : Function.support f ⊆ range g := by
    intro j hj
    have hdom : (cubicAFEProgressionLattice d e δ j : ℝ) ∈ cubicAFEProgressionDomain d e δ := by
      by_contra hn
      apply hj
      dsimp only [f, K]
      simp only [cubicAFEProgressionCutoffSummand_eq_zero_of_not_domain W T X V χ _ hn,
        integral_zero]
    have hpos : 0 < cubicAFEProgressionLattice d e δ j := by exact_mod_cast hdom.1
    let m : cubicAFEProgression d e δ :=
      ⟨(cubicAFEProgressionLattice d e δ j).toNat, cubicAFEProgressionLattice_toNat_mem he hdom⟩
    refine ⟨m, ?_⟩
    apply cubicAFEProgressionLattice_injective he δ
    rw [hi m]
    exact Int.toNat_of_nonneg hpos.le
  calc
    _ = ∑' m : cubicAFEProgression d e δ, f (g m) := by
      apply tsum_congr
      intro m
      dsimp only [f, K]
      rw [hi m]
      simp only [Int.cast_natCast]
    _ = _ := hginj.tsum_eq hsupport

/-- Poisson for the actual time-integrated progression. Both the Jacobian
and the negative inverse-residue phase are explicit. -/
theorem cubicAFEIntegratedProgression_poisson
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) :
    (∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
      cubicAFEProgressionCutoffSummand W T X V χ t m.val) =
    (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
      𝓕 (fun x : ℝ ↦ ∫ t : ℝ, cubicAFEProgressionCutoffSummand W T X V χ t x)
        ((h : ℝ) / ((e / Nat.gcd d e : ℕ) : ℝ)) *
      Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (δ : ℂ) *
        (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℂ) /
          ((e / Nat.gcd d e : ℕ) : ℂ)) := by
  have hq : 0 < Nat.gcd d e := by
    simpa only [Nat.gcd_comm] using Nat.gcd_pos_of_pos_left d he
  have hsN : 0 < e / Nat.gcd d e := by
    have heq := (gcd_extraction hq.ne').2.1
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, mul_zero] at heq
    exact he.ne' heq
  have hs : (0 : ℝ) < ((e / Nat.gcd d e : ℕ) : ℝ) := by exact_mod_cast hsN
  rw [integrated_progression_eq_lattice W T X V he χ]
  simp only [cubicAFEProgressionLattice, Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_natCast]
  rw [smooth_compact_poisson_scaled _
    (contDiff_integral_cubicAFEProgressionCutoffSummand W hT hX V hd he χ)
    (hasCompactSupport_integral_cubicAFEProgressionCutoffSummand W T X V χ) hs]
  simp only [Complex.ofReal_natCast, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_intCast]
  congr 1
  apply tsum_congr
  intro h
  congr 1
  congr 1
  ring

/-- Frequency sum outside the physical integral, for each actual dyadic box.
This follows from integrated-kernel Poisson, not an assumed Fourier majorant. -/
theorem integral_cubicAFEDyadicPoissonTerm_eq_frequencySum
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (jk : ℕ × ℕ) :
    (∫ t : ℝ, cubicAFEDyadicPoissonTerm (d := d) W T X V he δ jk t) =
    (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
      (∫ t : ℝ, 𝓕 (cubicAFEProgressionCutoffSummand W T X V
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t)
          ((h : ℝ) / ((e / Nat.gcd d e : ℕ) : ℝ))) *
      Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (δ : ℂ) *
        (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℂ) /
          ((e / Nat.gcd d e : ℕ) : ℂ)) := by
  rw [integral_cubicAFEDyadicPoissonTerm_eq W hT hX V hd he δ jk]
  let χ := cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2
  have hl : (∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
      (χ m.val : ℂ) * cubicAFECombinedSummandFinite W T X V d e t
        (cubicAFEProgressionPair d e δ m.val)) =
      ∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
        cubicAFEProgressionCutoffSummand W T X V χ t m.val := by
    apply tsum_congr
    intro m
    apply integral_congr_ae
    filter_upwards [] with t
    exact (cubicAFEProgressionCutoffSummand_eq_discrete W T X V hd he χ t m.property).symm
  rw [hl, cubicAFEIntegratedProgression_poisson W hT hX V hd he χ]
  congr 1
  apply tsum_congr
  intro h
  rw [integral_fourier_cubicAFEProgressionCutoffSummand W hT hX V hd he χ]

end PrimeNumberTheorem.MWKFCubic
