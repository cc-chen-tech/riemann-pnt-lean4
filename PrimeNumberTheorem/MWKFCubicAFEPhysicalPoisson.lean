import PrimeNumberTheorem.MWKFCubicAFEPhysicalKernel
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open Complex Filter MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Poisson summation for a cutoff of the actual progression kernel

The cutoff's closed support lies inside the two-positive-index region.
The physical kernel's smoothness and Schwartz hypotheses are proved, not
postulated. This is a fixed-parameter identity; no uniform Fourier-tail or
dyadic-reassembly estimate is asserted here.
-/

structure CubicProgressionCutoff (d e : ℕ) (δ : ℤ) where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  support_subset : tsupport toFun ⊆ cubicAFEProgressionDomain d e δ

instance {d e : ℕ} {δ : ℤ} : CoeFun (CubicProgressionCutoff d e δ) (fun _ ↦ ℝ → ℝ) :=
  ⟨CubicProgressionCutoff.toFun⟩

noncomputable def cubicAFEProgressionCutoffSummand
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) (t x : ℝ) : ℂ :=
  (χ x : ℂ) * cubicAFEProgressionPhysicalSummand W T X V d e δ t x

theorem contDiff_cubicAFEProgressionCutoffSummand
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {δ : ℤ} (χ : CubicProgressionCutoff d e δ) (t : ℝ) (hX : 1 / 2 < X) :
    ContDiff ℝ ∞ (cubicAFEProgressionCutoffSummand W T X V χ t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ.toFun
  · exact ((Complex.ofRealCLM.contDiff.comp χ.smooth).contDiffAt).mul
      ((contDiffOn_cubicAFEProgressionPhysicalSummand W T X V hd he δ t hX).contDiffAt
        ((isOpen_cubicAFEProgressionDomain d e δ).mem_nhds (χ.support_subset hx)))
  · have hzero : χ.toFun =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have hz : ContDiffAt ℝ ∞ (fun _ : ℝ ↦ (0 : ℂ)) x := contDiffAt_const
    apply hz.congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [cubicAFEProgressionCutoffSummand, show χ y = 0 from hy,
      Complex.ofReal_zero, zero_mul]

theorem hasCompactSupport_cubicAFEProgressionCutoffSummand
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) (t : ℝ) :
    HasCompactSupport (cubicAFEProgressionCutoffSummand W T X V χ t) :=
  (χ.compact.comp_left Complex.ofReal_zero).mul_right

noncomputable def cubicAFEProgressionSchwartz
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {δ : ℤ} (χ : CubicProgressionCutoff d e δ) (t : ℝ) (hX : 1 / 2 < X) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_cubicAFEProgressionCutoffSummand W T X V χ t).toSchwartzMap
    (contDiff_cubicAFEProgressionCutoffSummand W T X V hd he χ t hX)

theorem cubicAFEProgressionCutoffSummand_eq_discrete
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {δ : ℤ} (χ : CubicProgressionCutoff d e δ) (t : ℝ) {m : ℕ}
    (hm : m ∈ cubicAFEProgression d e δ) :
    cubicAFEProgressionCutoffSummand W T X V χ t m = (χ m : ℂ) *
      cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m) := by
  unfold cubicAFEProgressionCutoffSummand
  rw [cubicAFEProgressionPhysicalSummand_eq_discrete W T X V hd he t hm]

private theorem fourier_comp_pos_mul (f : ℝ → ℂ) {s : ℝ} (hs : 0 < s) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ f (s * x)) ξ = (s⁻¹ : ℂ) * 𝓕 f (ξ / s) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  let g : ℝ → ℂ := fun y ↦ Complex.exp (((-2 * Real.pi * y * (ξ / s) : ℝ) : ℂ) * I) * f y
  have hg : (fun x : ℝ ↦ Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * I) * f (s * x)) =
      fun x ↦ g (s * x) := by
    funext x
    dsimp only [g]
    have hscale : -2 * Real.pi * (s * x) * (ξ / s) = -2 * Real.pi * x * ξ := by
      calc
        _ = (-2 * Real.pi * x) * (s * (ξ / s)) := by ring
        _ = _ := by rw [mul_div_cancel₀ ξ hs.ne']
    rw [hscale]
  rw [hg, Measure.integral_comp_mul_left]
  simp only [abs_of_pos (inv_pos.mpr hs), Complex.real_smul, Complex.ofReal_inv]
  rfl

/-- The actual cutoff kernel on a residue lattice. Both the `1/s` Jacobian
and full Fourier phase are exposed. The residue is a real parameter here;
the inverse-residue specialization follows separately. -/
theorem cubicAFEProgressionCutoff_poisson
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {δ : ℤ} (χ : CubicProgressionCutoff d e δ) (t : ℝ) (hX : 1 / 2 < X)
    {s : ℝ} (hs : 0 < s) (a : ℝ) :
    (∑' n : ℤ, cubicAFEProgressionCutoffSummand W T X V χ t (a + s * n)) =
      (s⁻¹ : ℂ) * ∑' h : ℤ,
        𝓕 (cubicAFEProgressionCutoffSummand W T X V χ t) ((h : ℝ) / s) *
          Complex.exp (2 * (Real.pi : ℂ) * I * (h : ℂ) * (a : ℂ) / (s : ℂ)) := by
  let K := cubicAFEProgressionCutoffSummand W T X V χ t
  have hK : ContDiff ℝ ∞ K := contDiff_cubicAFEProgressionCutoffSummand W T X V hd he χ t hX
  have hKc : HasCompactSupport K := hasCompactSupport_cubicAFEProgressionCutoffSummand W T X V χ t
  have hGc : HasCompactSupport (fun x : ℝ ↦ K (s * x)) := by
    simpa only [smul_eq_mul] using hKc.comp_smul hs.ne'
  let G : 𝓢(ℝ, ℂ) := hGc.toSchwartzMap (hK.comp (contDiff_const.mul contDiff_id))
  have hps := G.tsum_eq_tsum_fourier (a / s)
  have hleft : (∑' n : ℤ, G (a / s + n)) = ∑' n : ℤ, K (a + s * n) := by
    apply tsum_congr
    intro n
    change K (s * (a / s + (n : ℝ))) = _
    rw [mul_add, mul_div_cancel₀ a hs.ne']
  rw [hleft] at hps
  change (∑' n : ℤ, K (a + s * n)) = _
  rw [hps, ← tsum_mul_left]
  apply tsum_congr
  intro h
  have hF : (𝓕 G) h = (s⁻¹ : ℂ) * 𝓕 K ((h : ℝ) / s) := by
    exact fourier_comp_pos_mul K hs h
  rw [hF, fourier_coe_apply]
  simp only [Complex.ofReal_one, div_one, Complex.ofReal_div]
  dsimp only [K]
  ring

/-- Specialize to the exact inverse residue from the shifted-divisor
equation. The phase is `e(-h*delta*rbar/s)` with no coprimality assumption
on delta and no exclusion of modulus one. -/
theorem cubicAFEProgressionCutoff_poisson_inverseResidue
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {δ : ℤ} (χ : CubicProgressionCutoff d e δ) (t : ℝ) (hX : 1 / 2 < X) :
    (∑' n : ℤ, cubicAFEProgressionCutoffSummand W T X V χ t
      (-(δ : ℝ) * (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℝ) +
        ((e / Nat.gcd d e : ℕ) : ℝ) * n)) =
      (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
        𝓕 (cubicAFEProgressionCutoffSummand W T X V χ t)
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
  rw [cubicAFEProgressionCutoff_poisson W T X V hd he χ t hX hs]
  simp only [Complex.ofReal_natCast, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_intCast]
  congr 1
  apply tsum_congr
  intro h
  congr 1
  congr 1
  ring

end PrimeNumberTheorem.MWKFCubic
