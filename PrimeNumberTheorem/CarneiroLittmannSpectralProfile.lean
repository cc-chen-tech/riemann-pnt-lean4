import PrimeNumberTheorem.TriangleFourierKernel

open Complex MeasureTheory Set

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- The unit translation phase in the standard `-2 * pi * I` Fourier
convention. -/
noncomputable def carneiroLittmannSpectralPhase (u : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * u : ℝ) : ℂ) * Complex.I)

private noncomputable def carneiroLittmannSpectralLeft (u : ℝ) : ℂ :=
  carneiroLittmannSpectralPhase u * (1 + u) +
    (carneiroLittmannSpectralPhase u - 1) /
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I)

private noncomputable def carneiroLittmannSpectralRight (u : ℝ) : ℂ :=
  carneiroLittmannSpectralPhase u * (1 - u) -
    (carneiroLittmannSpectralPhase u - 1) /
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I)

/-- Compact spectral profile whose standard Fourier transform will recover
the Carneiro--Littmann derivative. -/
noncomputable def carneiroLittmannSpectralProfile (u : ℝ) : ℂ :=
  if u ≤ -1 then 0
  else if u ≤ 0 then carneiroLittmannSpectralLeft u
  else if u ≤ 1 then carneiroLittmannSpectralRight u
  else 0

private theorem carneiroLittmannSpectralPhase_neg_one :
    carneiroLittmannSpectralPhase (-1) = 1 := by
  unfold carneiroLittmannSpectralPhase
  rw [show (((-2 * Real.pi * (-1 : ℝ) : ℝ) : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * Complex.I by
    push_cast
    ring]
  exact Complex.exp_two_pi_mul_I

@[simp] theorem carneiroLittmannSpectralPhase_zero :
    carneiroLittmannSpectralPhase 0 = 1 := by
  simp [carneiroLittmannSpectralPhase]

private theorem carneiroLittmannSpectralPhase_one :
    carneiroLittmannSpectralPhase 1 = 1 := by
  unfold carneiroLittmannSpectralPhase
  rw [show (((-2 * Real.pi * (1 : ℝ) : ℝ) : ℂ) * Complex.I) =
      -(2 * (Real.pi : ℂ) * Complex.I) by
    push_cast
    ring]
  rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

private theorem carneiroLittmannSpectralLeft_neg_one :
    carneiroLittmannSpectralLeft (-1) = 0 := by
  simp [carneiroLittmannSpectralLeft,
    carneiroLittmannSpectralPhase_neg_one]

private theorem carneiroLittmannSpectralLeft_zero :
    carneiroLittmannSpectralLeft 0 = 1 := by
  simp [carneiroLittmannSpectralLeft]

private theorem carneiroLittmannSpectralRight_zero :
    carneiroLittmannSpectralRight 0 = 1 := by
  simp [carneiroLittmannSpectralRight]

private theorem carneiroLittmannSpectralRight_one :
    carneiroLittmannSpectralRight 1 = 0 := by
  simp [carneiroLittmannSpectralRight,
    carneiroLittmannSpectralPhase_one]

private theorem continuous_carneiroLittmannSpectralPhase :
    Continuous carneiroLittmannSpectralPhase := by
  unfold carneiroLittmannSpectralPhase
  fun_prop

private theorem continuous_carneiroLittmannSpectralLeft :
    Continuous carneiroLittmannSpectralLeft := by
  unfold carneiroLittmannSpectralLeft carneiroLittmannSpectralPhase
  fun_prop

private theorem continuous_carneiroLittmannSpectralRight :
    Continuous carneiroLittmannSpectralRight := by
  unfold carneiroLittmannSpectralRight carneiroLittmannSpectralPhase
  fun_prop

theorem continuous_carneiroLittmannSpectralProfile :
    Continuous carneiroLittmannSpectralProfile := by
  have hRightPiece : Continuous (fun u : ℝ =>
      if u ≤ 1 then carneiroLittmannSpectralRight u else 0) := by
    exact continuous_if_le continuous_id continuous_const
      continuous_carneiroLittmannSpectralRight.continuousOn
      continuous_const.continuousOn (by
        intro u hu
        subst u
        exact carneiroLittmannSpectralRight_one)
  have hMiddlePiece : Continuous (fun u : ℝ =>
      if u ≤ 0 then carneiroLittmannSpectralLeft u
      else if u ≤ 1 then carneiroLittmannSpectralRight u else 0) := by
    exact continuous_if_le continuous_id continuous_const
      continuous_carneiroLittmannSpectralLeft.continuousOn
      hRightPiece.continuousOn (by
        intro u hu
        subst u
        norm_num
        rw [carneiroLittmannSpectralLeft_zero,
          carneiroLittmannSpectralRight_zero])
  unfold carneiroLittmannSpectralProfile
  exact continuous_if_le continuous_id continuous_const
    continuous_const.continuousOn hMiddlePiece.continuousOn (by
      intro u hu
      subst u
      norm_num
      exact carneiroLittmannSpectralLeft_neg_one.symm)

theorem carneiroLittmannSpectralProfile_eq_zero_of_one_le_abs
    {u : ℝ} (hu : 1 ≤ |u|) :
    carneiroLittmannSpectralProfile u = 0 := by
  rcases (le_abs.mp hu) with hu | hu
  · by_cases huOne : u = 1
    · subst u
      simp [carneiroLittmannSpectralProfile,
        carneiroLittmannSpectralRight_one]
    · have huGtOne : 1 < u := lt_of_le_of_ne hu (Ne.symm huOne)
      have huNotNegOne : ¬u ≤ -1 := not_le.mpr (by linarith)
      have huNotZero : ¬u ≤ 0 := not_le.mpr (by linarith)
      have huNotOne : ¬u ≤ 1 := not_le.mpr huGtOne
      simp [carneiroLittmannSpectralProfile, huNotNegOne, huNotZero,
        huNotOne]
  · have huNeg : u ≤ -1 := by linarith
    simp [carneiroLittmannSpectralProfile, huNeg]

theorem hasCompactSupport_carneiroLittmannSpectralProfile :
    HasCompactSupport carneiroLittmannSpectralProfile := by
  apply HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc
  intro u hu
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  apply carneiroLittmannSpectralProfile_eq_zero_of_one_le_abs
  rcases hu with hu | hu
  · rw [abs_of_neg (hu.trans_le (by norm_num))]
    linarith
  · rw [abs_of_pos ((by norm_num : (0 : ℝ) < 1).trans hu)]
    linarith

theorem integrable_carneiroLittmannSpectralProfile :
    Integrable carneiroLittmannSpectralProfile :=
  continuous_carneiroLittmannSpectralProfile.integrable_of_hasCompactSupport
    hasCompactSupport_carneiroLittmannSpectralProfile

private noncomputable def carneiroLittmannSpectralFrequency : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) * Complex.I

private noncomputable def carneiroLittmannSpectralPrimitiveLeft (u : ℝ) : ℂ :=
  ((1 + u : ℝ) : ℂ) * (carneiroLittmannSpectralPhase u - 1)

private noncomputable def carneiroLittmannSpectralPrimitiveRight (u : ℝ) : ℂ :=
  ((1 - u : ℝ) : ℂ) * (carneiroLittmannSpectralPhase u - 1)

private noncomputable def carneiroLittmannSpectralPrimitiveDerivativeLeft
    (u : ℝ) : ℂ :=
  carneiroLittmannSpectralPhase u - 1 +
    ((1 + u : ℝ) : ℂ) *
      (-carneiroLittmannSpectralFrequency * carneiroLittmannSpectralPhase u)

private noncomputable def carneiroLittmannSpectralPrimitiveDerivativeRight
    (u : ℝ) : ℂ :=
  -(carneiroLittmannSpectralPhase u - 1) +
    ((1 - u : ℝ) : ℂ) *
      (-carneiroLittmannSpectralFrequency * carneiroLittmannSpectralPhase u)

private noncomputable def carneiroLittmannSpectralPrimitiveRightPiece
    (u : ℝ) : ℂ :=
  if u ≤ 1 then carneiroLittmannSpectralPrimitiveRight u else 0

private noncomputable def carneiroLittmannSpectralPrimitiveDerivativeRightPiece
    (u : ℝ) : ℂ :=
  if u ≤ 1 then carneiroLittmannSpectralPrimitiveDerivativeRight u else 0

private noncomputable def carneiroLittmannSpectralPrimitiveMiddle
    (u : ℝ) : ℂ :=
  if u ≤ 0 then carneiroLittmannSpectralPrimitiveLeft u
  else carneiroLittmannSpectralPrimitiveRightPiece u

private noncomputable def carneiroLittmannSpectralPrimitiveDerivativeMiddle
    (u : ℝ) : ℂ :=
  if u ≤ 0 then carneiroLittmannSpectralPrimitiveDerivativeLeft u
  else carneiroLittmannSpectralPrimitiveDerivativeRightPiece u

/-- A compactly supported primitive used to split the spectral profile into
a derivative term and a translated triangle term. -/
noncomputable def carneiroLittmannSpectralPrimitive (u : ℝ) : ℂ :=
  if u ≤ -1 then 0 else carneiroLittmannSpectralPrimitiveMiddle u

/-- The continuous derivative of `carneiroLittmannSpectralPrimitive`. -/
noncomputable def carneiroLittmannSpectralPrimitiveDerivative (u : ℝ) : ℂ :=
  if u ≤ -1 then 0 else carneiroLittmannSpectralPrimitiveDerivativeMiddle u

private theorem hasDerivAt_carneiroLittmannSpectralPhase (u : ℝ) :
    HasDerivAt carneiroLittmannSpectralPhase
      (-carneiroLittmannSpectralFrequency * carneiroLittmannSpectralPhase u) u := by
  have hInner : HasDerivAt
      (fun y : ℝ => -carneiroLittmannSpectralFrequency * (y : ℂ))
      (-carneiroLittmannSpectralFrequency) u := by
    convert (((hasDerivAt_id (u : ℂ)).const_mul
      (-carneiroLittmannSpectralFrequency)).comp_ofReal) using 1 <;> ring
  have hExp := (Complex.hasDerivAt_exp
    (-carneiroLittmannSpectralFrequency * (u : ℂ))).comp u hInner
  have hPhaseEq : carneiroLittmannSpectralPhase = fun y : ℝ =>
      Complex.exp (-carneiroLittmannSpectralFrequency * (y : ℂ)) := by
    funext y
    simp only [carneiroLittmannSpectralPhase,
      carneiroLittmannSpectralFrequency]
    congr 1
    push_cast
    ring
  rw [hPhaseEq]
  simpa only [Function.comp_apply, mul_comm] using hExp

private theorem hasDerivAt_carneiroLittmannSpectralPrimitiveLeft (u : ℝ) :
    HasDerivAt carneiroLittmannSpectralPrimitiveLeft
      (carneiroLittmannSpectralPrimitiveDerivativeLeft u) u := by
  have hAffine : HasDerivAt (fun y : ℝ => ((1 + y : ℝ) : ℂ)) 1 u := by
    have hId : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 u :=
      (hasDerivAt_id (u : ℂ)).comp_ofReal
    convert hId.const_add 1 using 1
    funext y
    push_cast
    ring
  convert hAffine.mul
    ((hasDerivAt_carneiroLittmannSpectralPhase u).sub_const 1) using 1 <;>
      simp [carneiroLittmannSpectralPrimitiveLeft,
        carneiroLittmannSpectralPrimitiveDerivativeLeft] <;> ring

private theorem hasDerivAt_carneiroLittmannSpectralPrimitiveRight (u : ℝ) :
    HasDerivAt carneiroLittmannSpectralPrimitiveRight
      (carneiroLittmannSpectralPrimitiveDerivativeRight u) u := by
  have hAffine : HasDerivAt (fun y : ℝ => ((1 - y : ℝ) : ℂ)) (-1) u := by
    have hId : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 u :=
      (hasDerivAt_id (u : ℂ)).comp_ofReal
    convert hId.const_sub 1 using 1
    funext y
    push_cast
    ring
  convert hAffine.mul
    ((hasDerivAt_carneiroLittmannSpectralPhase u).sub_const 1) using 1 <;>
      simp [carneiroLittmannSpectralPrimitiveRight,
        carneiroLittmannSpectralPrimitiveDerivativeRight] <;> ring

private theorem continuous_carneiroLittmannSpectralPrimitiveLeft :
    Continuous carneiroLittmannSpectralPrimitiveLeft := by
  unfold carneiroLittmannSpectralPrimitiveLeft carneiroLittmannSpectralPhase
  fun_prop

private theorem continuous_carneiroLittmannSpectralPrimitiveRight :
    Continuous carneiroLittmannSpectralPrimitiveRight := by
  unfold carneiroLittmannSpectralPrimitiveRight carneiroLittmannSpectralPhase
  fun_prop

private theorem continuous_carneiroLittmannSpectralPrimitiveDerivativeLeft :
    Continuous carneiroLittmannSpectralPrimitiveDerivativeLeft := by
  unfold carneiroLittmannSpectralPrimitiveDerivativeLeft
    carneiroLittmannSpectralPhase carneiroLittmannSpectralFrequency
  fun_prop

private theorem continuous_carneiroLittmannSpectralPrimitiveDerivativeRight :
    Continuous carneiroLittmannSpectralPrimitiveDerivativeRight := by
  unfold carneiroLittmannSpectralPrimitiveDerivativeRight
    carneiroLittmannSpectralPhase carneiroLittmannSpectralFrequency
  fun_prop

private theorem carneiroLittmannSpectralPrimitiveRight_one :
    carneiroLittmannSpectralPrimitiveRight 1 = 0 := by
  simp [carneiroLittmannSpectralPrimitiveRight,
    carneiroLittmannSpectralPhase_one]

private theorem carneiroLittmannSpectralPrimitiveDerivativeRight_one :
    carneiroLittmannSpectralPrimitiveDerivativeRight 1 = 0 := by
  simp [carneiroLittmannSpectralPrimitiveDerivativeRight,
    carneiroLittmannSpectralPhase_one]

private theorem carneiroLittmannSpectralPrimitiveLeft_zero :
    carneiroLittmannSpectralPrimitiveLeft 0 = 0 := by
  simp [carneiroLittmannSpectralPrimitiveLeft]

private theorem carneiroLittmannSpectralPrimitiveRight_zero :
    carneiroLittmannSpectralPrimitiveRight 0 = 0 := by
  simp [carneiroLittmannSpectralPrimitiveRight]

private theorem carneiroLittmannSpectralPrimitiveDerivativeLeft_zero :
    carneiroLittmannSpectralPrimitiveDerivativeLeft 0 =
      -carneiroLittmannSpectralFrequency := by
  simp [carneiroLittmannSpectralPrimitiveDerivativeLeft]

private theorem carneiroLittmannSpectralPrimitiveDerivativeRight_zero :
    carneiroLittmannSpectralPrimitiveDerivativeRight 0 =
      -carneiroLittmannSpectralFrequency := by
  simp [carneiroLittmannSpectralPrimitiveDerivativeRight]

private theorem carneiroLittmannSpectralPrimitiveLeft_neg_one :
    carneiroLittmannSpectralPrimitiveLeft (-1) = 0 := by
  simp [carneiroLittmannSpectralPrimitiveLeft,
    carneiroLittmannSpectralPhase_neg_one]

private theorem carneiroLittmannSpectralPrimitiveDerivativeLeft_neg_one :
    carneiroLittmannSpectralPrimitiveDerivativeLeft (-1) = 0 := by
  simp [carneiroLittmannSpectralPrimitiveDerivativeLeft,
    carneiroLittmannSpectralPhase_neg_one]

private theorem continuous_carneiroLittmannSpectralPrimitiveRightPiece :
    Continuous carneiroLittmannSpectralPrimitiveRightPiece := by
  unfold carneiroLittmannSpectralPrimitiveRightPiece
  exact continuous_if_le continuous_id continuous_const
    continuous_carneiroLittmannSpectralPrimitiveRight.continuousOn
    continuous_const.continuousOn (by
      intro u hu
      subst u
      exact carneiroLittmannSpectralPrimitiveRight_one)

private theorem continuous_carneiroLittmannSpectralPrimitiveDerivativeRightPiece :
    Continuous carneiroLittmannSpectralPrimitiveDerivativeRightPiece := by
  unfold carneiroLittmannSpectralPrimitiveDerivativeRightPiece
  exact continuous_if_le continuous_id continuous_const
    continuous_carneiroLittmannSpectralPrimitiveDerivativeRight.continuousOn
    continuous_const.continuousOn (by
      intro u hu
      subst u
      exact carneiroLittmannSpectralPrimitiveDerivativeRight_one)

private theorem hasDerivAt_carneiroLittmannSpectralPrimitiveRightPiece (u : ℝ) :
    HasDerivAt carneiroLittmannSpectralPrimitiveRightPiece
      (carneiroLittmannSpectralPrimitiveDerivativeRightPiece u) u := by
  refine hasDerivAt_of_hasDerivAt_of_ne'
    (f := carneiroLittmannSpectralPrimitiveRightPiece)
    (g := carneiroLittmannSpectralPrimitiveDerivativeRightPiece)
    (x := (1 : ℝ)) ?_ ?_ ?_ u
  · intro y hy
    rcases lt_or_gt_of_ne hy with hy | hy
    · have hBase := hasDerivAt_carneiroLittmannSpectralPrimitiveRight y
      have hEq : carneiroLittmannSpectralPrimitiveRightPiece =ᶠ[nhds y]
          carneiroLittmannSpectralPrimitiveRight := by
        filter_upwards [Iio_mem_nhds hy] with z hz
        change z < 1 at hz
        rw [carneiroLittmannSpectralPrimitiveRightPiece, if_pos hz.le]
      simpa [carneiroLittmannSpectralPrimitiveDerivativeRightPiece, hy.le] using
        hBase.congr_of_eventuallyEq hEq
    · have hBase : HasDerivAt (fun _ : ℝ => (0 : ℂ)) 0 y :=
        hasDerivAt_const y 0
      have hEq : carneiroLittmannSpectralPrimitiveRightPiece =ᶠ[nhds y]
          (fun _ : ℝ => (0 : ℂ)) := by
        filter_upwards [Ioi_mem_nhds hy] with z hz
        change 1 < z at hz
        rw [carneiroLittmannSpectralPrimitiveRightPiece,
          if_neg (not_le.mpr hz)]
      simpa [carneiroLittmannSpectralPrimitiveDerivativeRightPiece,
        not_le.mpr hy] using hBase.congr_of_eventuallyEq hEq
  · exact continuous_carneiroLittmannSpectralPrimitiveRightPiece.continuousAt
  · exact continuous_carneiroLittmannSpectralPrimitiveDerivativeRightPiece.continuousAt

private theorem continuous_carneiroLittmannSpectralPrimitiveMiddle :
    Continuous carneiroLittmannSpectralPrimitiveMiddle := by
  unfold carneiroLittmannSpectralPrimitiveMiddle
  exact continuous_if_le continuous_id continuous_const
    continuous_carneiroLittmannSpectralPrimitiveLeft.continuousOn
    continuous_carneiroLittmannSpectralPrimitiveRightPiece.continuousOn (by
      intro u hu
      subst u
      rw [carneiroLittmannSpectralPrimitiveLeft_zero]
      simp [carneiroLittmannSpectralPrimitiveRightPiece,
        carneiroLittmannSpectralPrimitiveRight_zero])

private theorem continuous_carneiroLittmannSpectralPrimitiveDerivativeMiddle :
    Continuous carneiroLittmannSpectralPrimitiveDerivativeMiddle := by
  unfold carneiroLittmannSpectralPrimitiveDerivativeMiddle
  exact continuous_if_le continuous_id continuous_const
    continuous_carneiroLittmannSpectralPrimitiveDerivativeLeft.continuousOn
    continuous_carneiroLittmannSpectralPrimitiveDerivativeRightPiece.continuousOn (by
      intro u hu
      subst u
      rw [carneiroLittmannSpectralPrimitiveDerivativeLeft_zero]
      simp [carneiroLittmannSpectralPrimitiveDerivativeRightPiece,
        carneiroLittmannSpectralPrimitiveDerivativeRight_zero])

private theorem hasDerivAt_carneiroLittmannSpectralPrimitiveMiddle (u : ℝ) :
    HasDerivAt carneiroLittmannSpectralPrimitiveMiddle
      (carneiroLittmannSpectralPrimitiveDerivativeMiddle u) u := by
  refine hasDerivAt_of_hasDerivAt_of_ne'
    (f := carneiroLittmannSpectralPrimitiveMiddle)
    (g := carneiroLittmannSpectralPrimitiveDerivativeMiddle)
    (x := (0 : ℝ)) ?_ ?_ ?_ u
  · intro y hy
    rcases lt_or_gt_of_ne hy with hy | hy
    · have hBase := hasDerivAt_carneiroLittmannSpectralPrimitiveLeft y
      have hEq : carneiroLittmannSpectralPrimitiveMiddle =ᶠ[nhds y]
          carneiroLittmannSpectralPrimitiveLeft := by
        filter_upwards [Iio_mem_nhds hy] with z hz
        change z < 0 at hz
        rw [carneiroLittmannSpectralPrimitiveMiddle, if_pos hz.le]
      simpa [carneiroLittmannSpectralPrimitiveDerivativeMiddle, hy.le] using
        hBase.congr_of_eventuallyEq hEq
    · have hBase := hasDerivAt_carneiroLittmannSpectralPrimitiveRightPiece y
      have hEq : carneiroLittmannSpectralPrimitiveMiddle =ᶠ[nhds y]
          carneiroLittmannSpectralPrimitiveRightPiece := by
        filter_upwards [Ioi_mem_nhds hy] with z hz
        change 0 < z at hz
        rw [carneiroLittmannSpectralPrimitiveMiddle,
          if_neg (not_le.mpr hz)]
      simpa [carneiroLittmannSpectralPrimitiveDerivativeMiddle,
        not_le.mpr hy] using hBase.congr_of_eventuallyEq hEq
  · exact continuous_carneiroLittmannSpectralPrimitiveMiddle.continuousAt
  · exact continuous_carneiroLittmannSpectralPrimitiveDerivativeMiddle.continuousAt

private theorem continuous_carneiroLittmannSpectralPrimitive :
    Continuous carneiroLittmannSpectralPrimitive := by
  unfold carneiroLittmannSpectralPrimitive
  exact continuous_if_le continuous_id continuous_const
    continuous_const.continuousOn
    continuous_carneiroLittmannSpectralPrimitiveMiddle.continuousOn (by
      intro u hu
      subst u
      simp [carneiroLittmannSpectralPrimitiveMiddle,
        carneiroLittmannSpectralPrimitiveLeft_neg_one])

private theorem continuous_carneiroLittmannSpectralPrimitiveDerivative :
    Continuous carneiroLittmannSpectralPrimitiveDerivative := by
  unfold carneiroLittmannSpectralPrimitiveDerivative
  exact continuous_if_le continuous_id continuous_const
    continuous_const.continuousOn
    continuous_carneiroLittmannSpectralPrimitiveDerivativeMiddle.continuousOn (by
      intro u hu
      subst u
      simp [carneiroLittmannSpectralPrimitiveDerivativeMiddle,
        carneiroLittmannSpectralPrimitiveDerivativeLeft_neg_one])

theorem hasDerivAt_carneiroLittmannSpectralPrimitive (u : ℝ) :
    HasDerivAt carneiroLittmannSpectralPrimitive
      (carneiroLittmannSpectralPrimitiveDerivative u) u := by
  refine hasDerivAt_of_hasDerivAt_of_ne'
    (f := carneiroLittmannSpectralPrimitive)
    (g := carneiroLittmannSpectralPrimitiveDerivative)
    (x := (-1 : ℝ)) ?_ ?_ ?_ u
  · intro y hy
    rcases lt_or_gt_of_ne hy with hy | hy
    · have hBase : HasDerivAt (fun _ : ℝ => (0 : ℂ)) 0 y :=
        hasDerivAt_const y 0
      have hEq : carneiroLittmannSpectralPrimitive =ᶠ[nhds y]
          (fun _ : ℝ => (0 : ℂ)) := by
        filter_upwards [Iio_mem_nhds hy] with z hz
        change z < -1 at hz
        rw [carneiroLittmannSpectralPrimitive, if_pos hz.le]
      simpa [carneiroLittmannSpectralPrimitiveDerivative, hy.le] using
        hBase.congr_of_eventuallyEq hEq
    · have hBase := hasDerivAt_carneiroLittmannSpectralPrimitiveMiddle y
      have hEq : carneiroLittmannSpectralPrimitive =ᶠ[nhds y]
          carneiroLittmannSpectralPrimitiveMiddle := by
        filter_upwards [Ioi_mem_nhds hy] with z hz
        change -1 < z at hz
        rw [carneiroLittmannSpectralPrimitive,
          if_neg (not_le.mpr hz)]
      simpa [carneiroLittmannSpectralPrimitiveDerivative,
        not_le.mpr hy] using hBase.congr_of_eventuallyEq hEq
  · exact continuous_carneiroLittmannSpectralPrimitive.continuousAt
  · exact continuous_carneiroLittmannSpectralPrimitiveDerivative.continuousAt

theorem differentiable_carneiroLittmannSpectralPrimitive :
    Differentiable ℝ carneiroLittmannSpectralPrimitive :=
  fun u => (hasDerivAt_carneiroLittmannSpectralPrimitive u).differentiableAt

private theorem hasCompactSupport_carneiroLittmannSpectralPrimitive :
    HasCompactSupport carneiroLittmannSpectralPrimitive := by
  apply HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc
  intro u hu
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · simp [carneiroLittmannSpectralPrimitive, hu.le]
  · have huNegOne : ¬u ≤ -1 := not_le.mpr (by linarith)
    have huZero : ¬u ≤ 0 := not_le.mpr (by linarith)
    have huOne : ¬u ≤ 1 := not_le.mpr hu
    simp [carneiroLittmannSpectralPrimitive,
      carneiroLittmannSpectralPrimitiveMiddle,
      carneiroLittmannSpectralPrimitiveRightPiece,
      huNegOne, huZero, huOne]

private theorem hasCompactSupport_carneiroLittmannSpectralPrimitiveDerivative :
    HasCompactSupport carneiroLittmannSpectralPrimitiveDerivative := by
  apply HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc
  intro u hu
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · simp [carneiroLittmannSpectralPrimitiveDerivative, hu.le]
  · have huNegOne : ¬u ≤ -1 := not_le.mpr (by linarith)
    have huZero : ¬u ≤ 0 := not_le.mpr (by linarith)
    have huOne : ¬u ≤ 1 := not_le.mpr hu
    simp [carneiroLittmannSpectralPrimitiveDerivative,
      carneiroLittmannSpectralPrimitiveDerivativeMiddle,
      carneiroLittmannSpectralPrimitiveDerivativeRightPiece,
      huNegOne, huZero, huOne]

theorem integrable_carneiroLittmannSpectralPrimitive :
    Integrable carneiroLittmannSpectralPrimitive :=
  continuous_carneiroLittmannSpectralPrimitive.integrable_of_hasCompactSupport
    hasCompactSupport_carneiroLittmannSpectralPrimitive

private theorem integrable_carneiroLittmannSpectralPrimitiveDerivative :
    Integrable carneiroLittmannSpectralPrimitiveDerivative :=
  continuous_carneiroLittmannSpectralPrimitiveDerivative.integrable_of_hasCompactSupport
    hasCompactSupport_carneiroLittmannSpectralPrimitiveDerivative

theorem integrable_deriv_carneiroLittmannSpectralPrimitive :
    Integrable (deriv carneiroLittmannSpectralPrimitive) := by
  refine integrable_carneiroLittmannSpectralPrimitiveDerivative.congr ?_
  filter_upwards with u
  exact (hasDerivAt_carneiroLittmannSpectralPrimitive u).deriv.symm

end DirichletPolynomial
end PrimeNumberTheorem
