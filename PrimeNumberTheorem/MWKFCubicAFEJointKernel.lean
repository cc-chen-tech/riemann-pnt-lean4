import PrimeNumberTheorem.MWKFCubicAFEPhysicalPoisson

open Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Joint time/space regularity of the actual finite-height kernel

These statements keep the physical test weight, Mellin weight and full phase.
Compactness is for fixed parameters; no uniform Fourier-tail estimate follows.
-/

theorem continuous_cubicAFELogProductWeightFinite_joint
    {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    Continuous (fun p : ℝ × ℂ ↦ cubicAFELogProductWeightFinite p.1 X V p.2) := by
  have hs : Continuous (fun p : (ℝ × ℂ) × ℝ ↦
      cubicAFEScalar p.1.1 (cubicAFEVerticalPoint X p.2)) :=
    (continuous_cubicAFEScalar_joint hX).comp
      (f := fun p : (ℝ × ℂ) × ℝ ↦ (p.1.1, p.2))
      ((continuous_fst.fst).prodMk continuous_snd)
  have hz : Continuous (fun p : (ℝ × ℂ) × ℝ ↦ cubicAFEVerticalPoint X p.2) := by
    unfold cubicAFEVerticalPoint
    fun_prop
  have hi : Continuous (Function.uncurry (fun p : ℝ × ℂ ↦ fun y : ℝ ↦
      cubicAFEScalar p.1 (cubicAFEVerticalPoint X y) *
        Complex.exp (-cubicAFEVerticalPoint X y * p.2))) :=
    hs.mul (Complex.continuous_exp.comp (hz.neg.mul continuous_fst.snd))
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hi (-V) V)

theorem continuousOn_cubicAFERealProductWeightFinite_joint
    {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ ↦ cubicAFERealProductWeightFinite p.1 X V p.2)
      {p | 0 < p.2} := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  exact (continuous_cubicAFELogProductWeightFinite_joint hX V).continuousAt.comp
    (f := fun q : ℝ × ℝ ↦ (q.1, (Real.log q.2 : ℂ)))
    (continuousAt_fst.prodMk
      (Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_snd.log (ne_of_gt hp))))

theorem continuousOn_cubicAFEProgressionPhysicalSummand_joint
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (δ : ℤ) (hX : 1 / 2 < X) :
    ContinuousOn (fun p : ℝ × ℝ ↦
      cubicAFEProgressionPhysicalSummand W T X V d e δ p.1 p.2)
      {p | p.2 ∈ cubicAFEProgressionDomain d e δ} := by
  intro p hp
  have hP : Continuous (fun z : ℝ × ℝ ↦ cubicAFEProgressionRealProduct d e δ z.2) := by
    unfold cubicAFEProgressionRealProduct cubicAFEProgressionRealSecond
    fun_prop
  have hpos := cubicAFEProgressionRealProduct_pos he hp
  have hsqrt : ContinuousAt
      (fun z : ℝ × ℝ ↦ (Real.sqrt (cubicAFEProgressionRealProduct d e δ z.2) : ℂ)⁻¹) p := by
    apply (Complex.continuous_ofReal.continuousAt.comp hP.continuousAt.sqrt).inv₀
    change (Real.sqrt (cubicAFEProgressionRealProduct d e δ p.2) : ℂ) ≠ 0
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have hden : p.2 * ((d / Nat.gcd d e : ℕ) : ℝ) ≠ 0 := by
    apply mul_ne_zero hp.1.ne'
    intro hz
    have hn : d / Nat.gcd d e = 0 := by exact_mod_cast hz
    have hg := (gcd_extraction (Nat.gcd_pos_of_pos_left e hd).ne').1
    rw [hn, mul_zero] at hg
    exact hd.ne' hg
  have hphase : ContinuousAt (fun z : ℝ × ℝ ↦
      Real.log (1 + (δ : ℝ) / (z.2 * ((d / Nat.gcd d e : ℕ) : ℝ)))) p :=
    (continuousAt_const.add (continuousAt_const.div
      (continuousAt_snd.mul continuousAt_const) hden)).log
        (cubicAFEProgression_logArgument_pos hd hp).ne'
  have hexp : ContinuousAt (fun z : ℝ × ℝ ↦
      Complex.exp ((I * (Real.log (1 + (δ : ℝ) /
        (z.2 * ((d / Nat.gcd d e : ℕ) : ℝ))) : ℂ)) * z.1)) p :=
    Complex.continuous_exp.continuousAt.comp
      ((continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hphase)).mul
        (Complex.continuous_ofReal.continuousAt.comp continuousAt_fst))
  have hw : ContinuousAt (fun z : ℝ × ℝ ↦
      cubicAFERealProductWeightFinite z.1 X V (cubicAFEProgressionRealProduct d e δ z.2)) p :=
    ((continuousOn_cubicAFERealProductWeightFinite_joint hX V).continuousAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hpos)).comp
        (f := fun z : ℝ × ℝ ↦ (z.1, cubicAFEProgressionRealProduct d e δ z.2))
        (continuousAt_fst.prodMk hP.continuousAt)
  have hW : Continuous (fun z : ℝ × ℝ ↦ (W (z.1 / T) : ℂ)) :=
    Complex.continuous_ofReal.comp (W.continuous.comp (continuous_fst.div_const T))
  exact ((continuousAt_const.mul
    (((hsqrt.mul continuousAt_const).mul hexp).mul hw)).mul hW.continuousAt).continuousWithinAt

theorem continuous_cubicAFEProgressionCutoffSummand_joint
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {δ : ℤ} (χ : CubicProgressionCutoff d e δ) (hX : 1 / 2 < X) :
    Continuous (Function.uncurry (cubicAFEProgressionCutoffSummand W T X V χ)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p.2 ∈ tsupport χ.toFun
  · exact (Complex.continuous_ofReal.comp (χ.smooth.continuous.comp continuous_snd)).continuousAt.mul
      ((continuousOn_cubicAFEProgressionPhysicalSummand_joint W T X V hd he δ hX).continuousAt
        (((isOpen_cubicAFEProgressionDomain d e δ).preimage continuous_snd).mem_nhds
          (χ.support_subset hp)))
  · have hz : χ.toFun =ᶠ[𝓝 p.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
    have hz' := continuousAt_snd.eventually hz
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ ↦ (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [hz'] with z hz
    simp only [Function.uncurry, cubicAFEProgressionCutoffSummand,
      show χ z.2 = 0 from hz, Complex.ofReal_zero, zero_mul]

theorem hasCompactSupport_cubicAFEProgressionCutoffSummand_joint
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) (X V : ℝ) {d e : ℕ} {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) :
    HasCompactSupport (Function.uncurry (cubicAFEProgressionCutoffSummand W T X V χ)) := by
  apply ((W.hasCompactSupport_dilate hT).prod χ.compact).of_isClosed_subset isClosed_closure
  apply closure_minimal _ ((isClosed_tsupport _).prod (isClosed_tsupport _))
  intro p hp
  have hn : cubicAFEProgressionCutoffSummand W T X V χ p.1 p.2 ≠ 0 := hp
  constructor
  · apply subset_tsupport (fun t ↦ W (t / T))
    intro hz
    apply hn
    simp only [cubicAFEProgressionCutoffSummand, cubicAFEProgressionPhysicalSummand,
      hz, Complex.ofReal_zero, mul_zero]
  · apply subset_tsupport χ.toFun
    intro hz
    apply hn
    simp only [cubicAFEProgressionCutoffSummand, show χ p.2 = 0 from hz,
      Complex.ofReal_zero, zero_mul]

end PrimeNumberTheorem.MWKFCubic
