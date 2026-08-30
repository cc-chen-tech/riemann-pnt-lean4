import PrimeNumberTheorem.MWKFCubicSmoothIntegral

open Complex Filter MeasureTheory Set
open scoped ContDiff Topology SchwartzMap

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Joint smoothness and the integrated physical Schwartz kernel

Every regularity statement is proved for the actual finite-height AFE kernel.
The resulting Schwartz bounds are at fixed parameters, not uniform in T.
-/

private theorem contDiff_Gamma_comp_of_re_pos
    {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hp : ∀ p, 0 < (f p).re) :
    ContDiff ℝ ∞ (fun p ↦ Gammaℝ (f p)) := by
  have hi : ContDiff ℝ ∞ (fun p ↦ (Gammaℝ (f p))⁻¹) :=
    (differentiable_Gammaℝ_inv.contDiff.restrict_scalars ℝ).comp hf
  have hii : ContDiff ℝ ∞ (fun p ↦ ((Gammaℝ (f p))⁻¹)⁻¹) :=
    hi.inv (fun p ↦ inv_ne_zero (Gammaℝ_ne_zero_of_re_pos (hp p)))
  simpa only [inv_inv] using hii

theorem contDiff_cubicAFEScalar_joint {X : ℝ} (hX : 1 / 2 < X) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ cubicAFEScalar p.1 (cubicAFEVerticalPoint X p.2)) := by
  let s : ℝ × ℝ → ℂ := fun p ↦ cubicCriticalPoint p.1
  let u : ℝ × ℝ → ℂ := fun p ↦ 1 - s p
  let z : ℝ × ℝ → ℂ := fun p ↦ cubicAFEVerticalPoint X p.2
  have hs : ContDiff ℝ ∞ s := by
    exact contDiff_const.add (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_fst))
  have hu : ContDiff ℝ ∞ u := contDiff_const.sub hs
  have hz : ContDiff ℝ ∞ z := by
    exact contDiff_const.add ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
  have hs0 : ∀ p, s p ≠ 0 := fun p ↦ cubicCriticalPoint_ne_zero p.1
  have hu0 : ∀ p, u p ≠ 0 := fun p ↦ one_sub_cubicCriticalPoint_ne_zero p.1
  have hz0 : ∀ p, z p ≠ 0 := by
    intro p h
    have hh := congrArg Complex.re h
    simp [z, cubicAFEVerticalPoint] at hh
    linarith
  have hGs : ContDiff ℝ ∞ (fun p ↦ Gammaℝ (s p)) :=
    contDiff_Gamma_comp_of_re_pos hs (fun p ↦ by norm_num [s, cubicCriticalPoint])
  have hGu : ContDiff ℝ ∞ (fun p ↦ Gammaℝ (u p)) :=
    contDiff_Gamma_comp_of_re_pos hu (fun p ↦ by norm_num [u, s, cubicCriticalPoint])
  have hGsz : ContDiff ℝ ∞ (fun p ↦ Gammaℝ (s p + z p)) :=
    contDiff_Gamma_comp_of_re_pos (hs.add hz) (fun p ↦ by
      simp [s, z, cubicCriticalPoint, cubicAFEVerticalPoint]; linarith)
  have hGuz : ContDiff ℝ ∞ (fun p ↦ Gammaℝ (u p + z p)) :=
    contDiff_Gamma_comp_of_re_pos (hu.add hz) (fun p ↦ by
      norm_num [u, s, z, cubicCriticalPoint, cubicAFEVerticalPoint]; linarith)
  have hkernel : ContDiff ℝ ∞ (fun p ↦ cubicAFEKernelG p.1 (z p)) := by
    unfold cubicAFEKernelG cubicAFEPoleCanceller
    simp only [div_eq_mul_inv]
    exact (hz.pow 2).cexp.mul
      (((contDiff_const.sub (contDiff_const.mul (hz.pow 2))).mul
        (contDiff_const.sub ((hz.pow 2).mul ((hs.pow 2).inv
          (fun p ↦ pow_ne_zero 2 (hs0 p)))))).mul
        (contDiff_const.sub ((hz.pow 2).mul ((hu.pow 2).inv
          (fun p ↦ pow_ne_zero 2 (hu0 p))))))
  have hgamma0 : ∀ p, Gammaℝ (s p) * Gammaℝ (u p) ≠ 0 := by
    intro p
    simpa [s, u, cubicAFEGammaProduct] using cubicAFEGammaProduct_zero_ne p.1
  have hform : (fun p : ℝ × ℝ ↦ cubicAFEScalar p.1 (cubicAFEVerticalPoint X p.2)) =
      fun p ↦ cubicAFEKernelG p.1 (z p) * (Gammaℝ (s p + z p) * Gammaℝ (u p + z p)) *
        (Gammaℝ (s p) * Gammaℝ (u p))⁻¹ * (z p)⁻¹ := by
    funext p
    simp [cubicAFEScalar, cubicAFEGammaProduct, s, u, z, div_eq_mul_inv]
  rw [hform]
  exact ((hkernel.mul (hGsz.mul hGuz)).mul ((hGs.mul hGu).inv hgamma0)).mul (hz.inv hz0)

theorem contDiff_cubicAFELogProductWeightFinite_joint
    {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ ↦ cubicAFELogProductWeightFinite p.1 X V p.2) := by
  have hs : ContDiff ℝ ∞ (fun p : (ℝ × ℂ) × ℝ ↦
      cubicAFEScalar p.1.1 (cubicAFEVerticalPoint X p.2)) :=
    (contDiff_cubicAFEScalar_joint hX).comp
      (f := fun p : (ℝ × ℂ) × ℝ ↦ (p.1.1, p.2)) (by fun_prop)
  have hz : ContDiff ℝ ∞ (fun p : (ℝ × ℂ) × ℝ ↦ cubicAFEVerticalPoint X p.2) := by
    exact contDiff_const.add ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
  have hi : ContDiff ℝ ∞ (fun p : (ℝ × ℂ) × ℝ ↦
      cubicAFEScalar p.1.1 (cubicAFEVerticalPoint X p.2) *
        Complex.exp (-cubicAFEVerticalPoint X p.2 * p.1.2)) :=
    hs.mul ((hz.neg.mul (contDiff_snd.comp contDiff_fst)).cexp)
  exact contDiff_const.mul (contDiff_intervalIntegral_joint _ hi (-V) V)

theorem contDiffOn_cubicAFERealProductWeightFinite_joint
    {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ cubicAFERealProductWeightFinite p.1 X V p.2)
      {p | 0 < p.2} := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  exact (contDiff_cubicAFELogProductWeightFinite_joint hX V).contDiffAt.comp p
    (f := fun q : ℝ × ℝ ↦ (q.1, (Real.log q.2 : ℂ)))
    (contDiff_fst.contDiffAt.prodMk
      (Complex.ofRealCLM.contDiff.contDiffAt.comp p
        (contDiff_snd.contDiffAt.log hp.ne')))

theorem contDiffOn_cubicAFEProgressionPhysicalSummand_joint
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (δ : ℤ) (hX : 1 / 2 < X) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ cubicAFEProgressionPhysicalSummand W T X V d e δ p.1 p.2)
      {p | p.2 ∈ cubicAFEProgressionDomain d e δ} := by
  intro p hp
  have hP : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ cubicAFEProgressionRealProduct d e δ z.2) := by
    unfold cubicAFEProgressionRealProduct cubicAFEProgressionRealSecond
    fun_prop
  have hpos := cubicAFEProgressionRealProduct_pos he hp
  have hsqrt : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦
      (Real.sqrt (cubicAFEProgressionRealProduct d e δ z.2) : ℂ)⁻¹) p := by
    apply (Complex.ofRealCLM.contDiff.contDiffAt.comp p (hP.contDiffAt.sqrt hpos.ne')).inv
    change (Real.sqrt (cubicAFEProgressionRealProduct d e δ p.2) : ℂ) ≠ 0
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have hden : p.2 * ((d / Nat.gcd d e : ℕ) : ℝ) ≠ 0 := by
    apply mul_ne_zero hp.1.ne'
    intro hz
    have hn : d / Nat.gcd d e = 0 := by exact_mod_cast hz
    have hg := (gcd_extraction (Nat.gcd_pos_of_pos_left e hd).ne').1
    rw [hn, mul_zero] at hg
    exact hd.ne' hg
  have hphase : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦
      Real.log (1 + (δ : ℝ) / (z.2 * ((d / Nat.gcd d e : ℕ) : ℝ)))) p := by
    have hdv : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦
        z.2 * ((d / Nat.gcd d e : ℕ) : ℝ)) p :=
      contDiff_snd.contDiffAt.mul contDiffAt_const
    have hq : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦
        (δ : ℝ) / (z.2 * ((d / Nat.gcd d e : ℕ) : ℝ))) p :=
      contDiffAt_const.div hdv hden
    exact (contDiffAt_const.add hq).log (cubicAFEProgression_logArgument_pos hd hp).ne'
  have hexp : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦ Complex.exp ((I *
      (Real.log (1 + (δ : ℝ) / (z.2 * ((d / Nat.gcd d e : ℕ) : ℝ))) : ℂ)) * z.1)) p :=
    ((contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p hphase)).mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp p contDiff_fst.contDiffAt)).cexp
  have hw : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦
      cubicAFERealProductWeightFinite z.1 X V (cubicAFEProgressionRealProduct d e δ z.2)) p :=
    ((contDiffOn_cubicAFERealProductWeightFinite_joint hX V).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hpos)).comp p
        (f := fun z : ℝ × ℝ ↦ (z.1, cubicAFEProgressionRealProduct d e δ z.2))
        (contDiff_fst.contDiffAt.prodMk hP.contDiffAt)
  have hW : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ (W (z.1 / T) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (W.smooth.comp (contDiff_fst.div_const T))
  exact ((contDiffAt_const.mul (((hsqrt.mul contDiffAt_const).mul hexp).mul hw)).mul
    hW.contDiffAt).contDiffWithinAt

theorem contDiff_cubicAFEProgressionCutoffSummand_joint
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {δ : ℤ} (χ : CubicProgressionCutoff d e δ) (hX : 1 / 2 < X) :
    ContDiff ℝ ∞ (Function.uncurry (cubicAFEProgressionCutoffSummand W T X V χ)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.2 ∈ tsupport χ.toFun
  · exact (Complex.ofRealCLM.contDiff.comp (χ.smooth.comp contDiff_snd)).contDiffAt.mul
      ((contDiffOn_cubicAFEProgressionPhysicalSummand_joint W T X V hd he δ hX).contDiffAt
        (((isOpen_cubicAFEProgressionDomain d e δ).preimage continuous_snd).mem_nhds
          (χ.support_subset hp)))
  · have hz : χ.toFun =ᶠ[𝓝 p.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
    have hz' := continuousAt_snd.eventually hz
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ ↦ (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [hz'] with z hz
    simp only [Function.uncurry, cubicAFEProgressionCutoffSummand,
      show χ z.2 = 0 from hz, Complex.ofReal_zero, zero_mul]

theorem contDiff_integral_cubicAFEProgressionCutoffSummand
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) :
    ContDiff ℝ ∞ (fun x : ℝ ↦ ∫ t : ℝ, cubicAFEProgressionCutoffSummand W T X V χ t x) := by
  apply contDiff_integral_joint_compactSupport
    (fun p : ℝ × ℝ ↦ cubicAFEProgressionCutoffSummand W T X V χ p.2 p.1)
  · exact (contDiff_cubicAFEProgressionCutoffSummand_joint W T X V hd he χ hX).comp
      (f := Prod.swap) (contDiff_snd.prodMk contDiff_fst)
  · exact (hasCompactSupport_cubicAFEProgressionCutoffSummand_joint W hT X V χ).comp_homeomorph
      (Homeomorph.prodComm ℝ ℝ)

theorem hasCompactSupport_integral_cubicAFEProgressionCutoffSummand
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) :
    HasCompactSupport (fun x : ℝ ↦ ∫ t : ℝ, cubicAFEProgressionCutoffSummand W T X V χ t x) := by
  apply HasCompactSupport.of_support_subset_isCompact χ.compact
  intro x hx
  by_contra hn
  have hz : χ x = 0 := by
    by_contra hz
    exact hn (subset_tsupport χ.toFun hz)
  apply hx
  simp only [cubicAFEProgressionCutoffSummand, hz, Complex.ofReal_zero, zero_mul, integral_zero]

noncomputable def cubicAFEIntegratedProgressionSchwartz
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_integral_cubicAFEProgressionCutoffSummand W T X V χ).toSchwartzMap
    (contDiff_integral_cubicAFEProgressionCutoffSummand W hT hX V hd he χ)

end PrimeNumberTheorem.MWKFCubic
