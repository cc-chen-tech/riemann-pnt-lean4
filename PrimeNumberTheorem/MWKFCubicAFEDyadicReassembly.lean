import PrimeNumberTheorem.MWKFCubicAFEDyadicCutoff

open Complex Set MeasureTheory
open scoped FourierTransform

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Absolutely convergent actual dyadic reassembly

The positive partition has total mass exactly one at each original integer
point. We first prove summability jointly in the integer and dyadic indices,
then commute these sums and apply the actual local Poisson formula. The
Fourier series remains inside each dyadic box; no uniform Fourier-tail bound
or interchange of the frequency sum across boxes is claimed here.
-/

theorem cubicAFEProgressionDyadicCutoff_nonneg {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (j k : ℕ) (x : ℝ) :
    0 ≤ cubicAFEProgressionDyadicCutoff (d := d) he δ j k x :=
  mul_nonneg (cubicAFEDyadicWindow_nonneg j x)
    (cubicAFEDyadicWindow_nonneg k (cubicAFEProgressionRealSecond d e δ x))

theorem cubicAFEProgressionDyadicCutoff_scales {d e : ℕ} (he : 0 < e)
    {δ : ℤ} {j k : ℕ} {x : ℝ}
    (hx : cubicAFEProgressionDyadicCutoff (d := d) he δ j k x ≠ 0) :
    x ∈ Icc ((2 : ℝ)^j / 2) (2 * (2 : ℝ)^j) ∧
      cubicAFEProgressionRealSecond d e δ x ∈ Icc ((2 : ℝ)^k / 2) (2 * (2 : ℝ)^k) := by
  have hh := mul_ne_zero_iff.mp hx
  exact ⟨tsupport_cubicAFEDyadicWindow_subset j (subset_tsupport _ hh.1),
    tsupport_cubicAFEDyadicWindow_subset k (subset_tsupport _ hh.2)⟩

/-- Joint absolute convergence is proved before the two sums are commuted.
The summability input here concerns the original series only; it is
discharged for the actual AFE series below. -/
theorem summable_cubicAFEProgression_dyadic_weighted {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (f : cubicAFEProgression d e δ → ℂ) (hf : Summable f) :
    Summable (fun z : cubicAFEProgression d e δ × (ℕ × ℕ) ↦
      (cubicAFEProgressionDyadicCutoff (d := d) he δ z.2.1 z.2.2 z.1.val : ℂ) * f z.1) := by
  have hnorm : ∀ m : cubicAFEProgression d e δ,
      HasSum (fun jk : ℕ × ℕ ↦
        ‖(cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) * f m‖) ‖f m‖ := by
    intro m
    have hr : HasSum (fun jk : ℕ × ℕ ↦
        cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val * ‖f m‖) ‖f m‖ := by
      simpa only [one_mul] using (hasSum_cubicAFEProgressionDyadicCutoff he m.property).mul_right ‖f m‖
    apply hr.congr_fun
    intro jk
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (cubicAFEProgressionDyadicCutoff_nonneg he δ jk.1 jk.2 m.val)]
  have hnormsum : Summable (fun z : cubicAFEProgression d e δ × (ℕ × ℕ) ↦
      ‖(cubicAFEProgressionDyadicCutoff (d := d) he δ z.2.1 z.2.2 z.1.val : ℂ) * f z.1‖) := by
    apply (summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)).mpr
    refine ⟨fun m ↦ (hnorm m).summable, ?_⟩
    simpa only [(hnorm _).tsum_eq] using hf.norm
  exact hnormsum.of_norm

theorem tsum_cubicAFEProgression_eq_dyadic {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (f : cubicAFEProgression d e δ → ℂ) (hf : Summable f) :
    (∑' m : cubicAFEProgression d e δ, f m) =
      ∑' jk : ℕ × ℕ, ∑' m : cubicAFEProgression d e δ,
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) * f m := by
  have hpoint : ∀ m : cubicAFEProgression d e δ,
      (∑' jk : ℕ × ℕ,
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) * f m) = f m := by
    intro m
    have hc : HasSum (fun jk : ℕ × ℕ ↦
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ)) (1 : ℂ) :=
      Complex.hasSum_ofReal.mpr (hasSum_cubicAFEProgressionDyadicCutoff he m.property)
    simpa only [Complex.ofReal_one, one_mul] using (hc.mul_right (f m)).tsum_eq
  calc
    _ = ∑' m : cubicAFEProgression d e δ, ∑' jk : ℕ × ℕ,
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) * f m :=
      tsum_congr (fun m ↦ (hpoint m).symm)
    _ = _ := (summable_cubicAFEProgression_dyadic_weighted he δ f hf).tsum_comm.symm

theorem summable_cubicAFEProgressionSummand
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ)
    {d e : ℕ} (he : 0 < e) (δ : ℤ) (t : ℝ) :
    Summable (fun m : cubicAFEProgression d e δ ↦
      cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val)) :=
  (cubicAFEProgressionEquiv he δ).summable_iff.mpr
    ((summable_cubicAFECombinedSummandFinite W T hX V d e t).subtype _)

/-- Literal Fourier expression of one actual two-index dyadic box. -/
noncomputable def cubicAFEDyadicPoissonTerm
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (jk : ℕ × ℕ) (t : ℝ) : ℂ :=
  (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
    𝓕 (cubicAFEProgressionCutoffSummand W T X V
      (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t)
      ((h : ℝ) / ((e / Nat.gcd d e : ℕ) : ℝ)) *
      Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (δ : ℂ) *
        (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℂ) /
          ((e / Nat.gcd d e : ℕ) : ℂ))

theorem cubicAFEDyadicPoissonTerm_eq_cutoffSum
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (δ : ℤ) (jk : ℕ × ℕ) (t : ℝ) (hX : 1 / 2 < X) :
    cubicAFEDyadicPoissonTerm (d := d) W T X V he δ jk t =
      ∑' m : cubicAFEProgression d e δ,
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) *
          cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val) := by
  let χ := cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2
  change cubicAFEDyadicPoissonTerm W T X V he δ jk t = _
  rw [cubicAFEDyadicPoissonTerm, ← cubicAFEShiftFiberCutoff_poisson W T X V hd he χ t hX,
    tsum_cubicAFEShiftFiber_eq_progression (d := d) he δ
      (fun p : ℕ × ℕ ↦ (χ (p.1 + 1 : ℕ) : ℂ) * cubicAFECombinedSummandFinite W T X V d e t p)]
  apply tsum_congr
  intro m
  rw [(cubicAFEProgressionPair_succ he m.property).1]

/-- Exact dyadic Poisson reassembly of every original shifted fiber.
The order is dyadic boxes first, frequencies inside each box. -/
theorem cubicAFEShiftFiber_eq_dyadicPoisson
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (δ : ℤ) (t : ℝ) (hX : 1 / 2 < X) :
    (∑' p : cubicAFEShiftFiber d e δ, cubicAFECombinedSummandFinite W T X V d e t p.val) =
      ∑' jk : ℕ × ℕ, cubicAFEDyadicPoissonTerm (d := d) W T X V he δ jk t := by
  rw [tsum_cubicAFEShiftFiber_eq_progression he δ]
  rw [tsum_cubicAFEProgression_eq_dyadic he δ _
    (summable_cubicAFEProgressionSummand W T hX V he δ t)]
  apply tsum_congr
  intro jk
  exact (cubicAFEDyadicPoissonTerm_eq_cutoffSum W T X V hd he δ jk t hX).symm

theorem summable_cubicAFEDyadicPoissonTerm
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (δ : ℤ) (t : ℝ) (hX : 1 / 2 < X) :
    Summable (fun jk : ℕ × ℕ ↦ cubicAFEDyadicPoissonTerm (d := d) W T X V he δ jk t) := by
  have hs := summable_cubicAFEProgression_dyadic_weighted (d := d) he δ _
    (summable_cubicAFEProgressionSummand (d := d) W T hX V he δ t)
  apply hs.prod_symm.prod.congr
  intro jk
  exact (cubicAFEDyadicPoissonTerm_eq_cutoffSum W T X V hd he δ jk t hX).symm

/-- The physical time-integrated progression admits the same dyadic
reassembly. The cutoff is independent of physical time. This does not
exchange a Fourier-frequency series with the time integral. -/
theorem cubicAFEProgressionIntegral_eq_dyadic
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : 0 < e) (δ : ℤ) :
    (∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val)) =
      ∑' jk : ℕ × ℕ, ∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) *
          cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val) := by
  simp_rw [integral_const_mul]
  exact tsum_cubicAFEProgression_eq_dyadic he δ _
    (summable_integral_cubicAFE_progression W hT hX V hd he δ)

theorem summable_cubicAFEProgressionDyadicIntegral
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : 0 < e) (δ : ℤ) :
    Summable (fun jk : ℕ × ℕ ↦ ∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
      (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m.val : ℂ) *
        cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val)) := by
  simp_rw [integral_const_mul]
  exact (summable_cubicAFEProgression_dyadic_weighted he δ _
    (summable_integral_cubicAFE_progression W hT hX V hd he δ)).prod_symm.prod

end PrimeNumberTheorem.MWKFCubic
