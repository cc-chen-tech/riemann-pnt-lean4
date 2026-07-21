import PrimeNumberTheorem.TriangleFourierKernel
import Mathlib.Analysis.Fourier.FourierTransformDeriv

open Complex MeasureTheory Set
open FourierTransform

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

/-- Algebraic decomposition of the compact spectral profile into the
derivative of the compact primitive and a modulated triangle kernel. -/
theorem carneiroLittmannSpectralPrimitiveDerivative_eq (u : ℝ) :
    carneiroLittmannSpectralPrimitiveDerivative u =
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        (carneiroLittmannSpectralProfile u -
          2 * (triangleFourierKernel u : ℂ) *
            carneiroLittmannSpectralPhase u) := by
  have hFrequency : carneiroLittmannSpectralFrequency =
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) := rfl
  have hFrequencyNe : carneiroLittmannSpectralFrequency ≠ 0 := by
    rw [hFrequency]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero))
      Complex.I_ne_zero
  by_cases hneg : u ≤ -1
  · have huNonpos : u ≤ 0 := hneg.trans (by norm_num)
    have hAbs : 1 ≤ |u| := by
      rw [abs_of_nonpos huNonpos]
      linarith
    have hTriangle : triangleFourierKernel u = 0 := by
      unfold triangleFourierKernel
      rw [max_eq_right]
      linarith
    rw [carneiroLittmannSpectralPrimitiveDerivative, if_pos hneg,
      carneiroLittmannSpectralProfile, if_pos hneg, hTriangle]
    push_cast
    ring
  · have hLower : -1 < u := lt_of_not_ge hneg
    by_cases hzero : u ≤ 0
    · have hTriangle : triangleFourierKernel u = 1 + u := by
        unfold triangleFourierKernel
        rw [abs_of_nonpos hzero, max_eq_left]
        · ring
        · linarith
      rw [carneiroLittmannSpectralPrimitiveDerivative, if_neg hneg,
        carneiroLittmannSpectralPrimitiveDerivativeMiddle, if_pos hzero,
        carneiroLittmannSpectralProfile, if_neg hneg, if_pos hzero,
        hTriangle]
      unfold carneiroLittmannSpectralPrimitiveDerivativeLeft
        carneiroLittmannSpectralLeft
      rw [hFrequency]
      field_simp [hFrequencyNe]
      push_cast
      ring
    · have huPos : 0 < u := lt_of_not_ge hzero
      by_cases hone : u ≤ 1
      · have hTriangle : triangleFourierKernel u = 1 - u := by
          unfold triangleFourierKernel
          rw [abs_of_nonneg huPos.le, max_eq_left]
          exact sub_nonneg.mpr hone
        rw [carneiroLittmannSpectralPrimitiveDerivative, if_neg hneg,
          carneiroLittmannSpectralPrimitiveDerivativeMiddle, if_neg hzero,
          carneiroLittmannSpectralPrimitiveDerivativeRightPiece, if_pos hone,
          carneiroLittmannSpectralProfile, if_neg hneg, if_neg hzero,
          if_pos hone, hTriangle]
        unfold carneiroLittmannSpectralPrimitiveDerivativeRight
          carneiroLittmannSpectralRight
        rw [hFrequency]
        field_simp [hFrequencyNe]
        push_cast
        ring
      · have honeLt : 1 < u := lt_of_not_ge hone
        have hTriangle : triangleFourierKernel u = 0 := by
          unfold triangleFourierKernel
          rw [abs_of_pos huPos, max_eq_right]
          linarith
        rw [carneiroLittmannSpectralPrimitiveDerivative, if_neg hneg,
          carneiroLittmannSpectralPrimitiveDerivativeMiddle, if_neg hzero,
          carneiroLittmannSpectralPrimitiveDerivativeRightPiece, if_neg hone,
          carneiroLittmannSpectralProfile, if_neg hneg, if_neg hzero,
          if_neg hone, hTriangle]
        push_cast
        ring

private theorem integrable_carneiroLittmannModulatedTriangle :
    Integrable (fun u : ℝ => carneiroLittmannSpectralPhase u *
      (triangleFourierKernel u : ℂ)) := by
  have hProduct : Integrable (fun u : ℝ =>
      (triangleFourierKernel u : ℂ) * carneiroLittmannSpectralPhase u) := by
    apply integrable_triangleFourierKernel.ofReal.mul_bdd (c := 1)
    · exact continuous_carneiroLittmannSpectralPhase.aestronglyMeasurable
    · filter_upwards with u
      simp [carneiroLittmannSpectralPhase, Complex.norm_exp]
  refine hProduct.congr ?_
  filter_upwards with u
  ring

private theorem fourier_sub_of_integrable {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun u => f u - g u) x = 𝓕 f x - 𝓕 g x := by
  have hf' : Integrable (fun v : ℝ => 𝐞 (-(v * x)) • f v) := by
    exact (VectorFourier.fourierIntegral_convergent_iff
      (e := 𝐞) (μ := volume) (L := LinearMap.mul ℝ ℝ)
      Real.continuous_fourierChar (by fun_prop) x).2 hf
  have hg' : Integrable (fun v : ℝ => 𝐞 (-(v * x)) • g v) := by
    exact (VectorFourier.fourierIntegral_convergent_iff
      (e := 𝐞) (μ := volume) (L := LinearMap.mul ℝ ℝ)
      Real.continuous_fourierChar (by fun_prop) x).2 hg
  rw [Real.fourier_real_eq, Real.fourier_real_eq, Real.fourier_real_eq]
  rw [← MeasureTheory.integral_sub hf' hg']
  congr 1
  funext u
  rw [smul_sub]

private theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    𝓕 (fun u => c * f u) x = c * 𝓕 f x := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  calc
    (∫ u : ℝ, 𝐞 (-(u * x)) • (c * f u)) =
        ∫ u : ℝ, c * (𝐞 (-(u * x)) • f u) := by
      congr 1
      funext u
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    _ = c * ∫ u : ℝ, 𝐞 (-(u * x)) • f u :=
      MeasureTheory.integral_const_mul _ _

private theorem fourier_carneiroLittmannModulatedTriangle (x : ℝ) :
    𝓕 (fun u : ℝ => carneiroLittmannSpectralPhase u *
      (triangleFourierKernel u : ℂ)) x =
        (carneiroLittmannSincSquareBase (x + 1) : ℂ) := by
  calc
    𝓕 (fun u : ℝ => carneiroLittmannSpectralPhase u *
        (triangleFourierKernel u : ℂ)) x =
        ∫ u : ℝ,
          Complex.exp (((-2 * Real.pi * u * x : ℝ) : ℂ) * Complex.I) •
            (carneiroLittmannSpectralPhase u *
              (triangleFourierKernel u : ℂ)) :=
      Real.fourier_real_eq_integral_exp_smul _ _
    _ = ∫ u : ℝ,
        Complex.exp (((-2 * Real.pi * u * (x + 1) : ℝ) : ℂ) * Complex.I) •
          (triangleFourierKernel u : ℂ) := by
      congr 1
      funext u
      simp only [carneiroLittmannSpectralPhase, smul_eq_mul]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = 𝓕 (fun u : ℝ => (triangleFourierKernel u : ℂ)) (x + 1) :=
      (Real.fourier_real_eq_integral_exp_smul _ _).symm
    _ = (carneiroLittmannSincSquareBase (x + 1) : ℂ) := by
      simpa only [carneiroLittmannSincSquareBase] using
        fourier_triangleFourierKernel (x + 1)

private theorem carneiroLittmannSpectralPrimitive_eq (u : ℝ) :
    carneiroLittmannSpectralPrimitive u =
      carneiroLittmannSpectralPhase u * (triangleFourierKernel u : ℂ) -
        (triangleFourierKernel u : ℂ) := by
  by_cases hneg : u ≤ -1
  · have huNonpos : u ≤ 0 := hneg.trans (by norm_num)
    have hAbs : 1 ≤ |u| := by
      rw [abs_of_nonpos huNonpos]
      linarith
    have hTriangle : triangleFourierKernel u = 0 := by
      unfold triangleFourierKernel
      rw [max_eq_right]
      linarith
    rw [carneiroLittmannSpectralPrimitive, if_pos hneg, hTriangle]
    norm_num
  · have hLower : -1 < u := lt_of_not_ge hneg
    by_cases hzero : u ≤ 0
    · have hTriangle : triangleFourierKernel u = 1 + u := by
        unfold triangleFourierKernel
        rw [abs_of_nonpos hzero, max_eq_left]
        · ring
        · linarith
      rw [carneiroLittmannSpectralPrimitive, if_neg hneg,
        carneiroLittmannSpectralPrimitiveMiddle, if_pos hzero,
        carneiroLittmannSpectralPrimitiveLeft, hTriangle]
      push_cast
      ring
    · have huPos : 0 < u := lt_of_not_ge hzero
      by_cases hone : u ≤ 1
      · have hTriangle : triangleFourierKernel u = 1 - u := by
          unfold triangleFourierKernel
          rw [abs_of_nonneg huPos.le, max_eq_left]
          exact sub_nonneg.mpr hone
        rw [carneiroLittmannSpectralPrimitive, if_neg hneg,
          carneiroLittmannSpectralPrimitiveMiddle, if_neg hzero,
          carneiroLittmannSpectralPrimitiveRightPiece, if_pos hone,
          carneiroLittmannSpectralPrimitiveRight, hTriangle]
        push_cast
        ring
      · have honeLt : 1 < u := lt_of_not_ge hone
        have hTriangle : triangleFourierKernel u = 0 := by
          unfold triangleFourierKernel
          rw [abs_of_pos huPos, max_eq_right]
          linarith
        rw [carneiroLittmannSpectralPrimitive, if_neg hneg,
          carneiroLittmannSpectralPrimitiveMiddle, if_neg hzero,
          carneiroLittmannSpectralPrimitiveRightPiece, if_neg hone,
          hTriangle]
        norm_num

private theorem fourier_carneiroLittmannSpectralPrimitive (x : ℝ) :
    𝓕 carneiroLittmannSpectralPrimitive x =
      (carneiroLittmannSincSquareBase (x + 1) : ℂ) -
        (carneiroLittmannSincSquareBase x : ℂ) := by
  have hFunction : carneiroLittmannSpectralPrimitive = fun u : ℝ =>
      carneiroLittmannSpectralPhase u * (triangleFourierKernel u : ℂ) -
        (triangleFourierKernel u : ℂ) := by
    funext u
    exact carneiroLittmannSpectralPrimitive_eq u
  rw [hFunction]
  calc
    𝓕 (fun u : ℝ =>
        carneiroLittmannSpectralPhase u * (triangleFourierKernel u : ℂ) -
          (triangleFourierKernel u : ℂ)) x =
        𝓕 (fun u : ℝ => carneiroLittmannSpectralPhase u *
          (triangleFourierKernel u : ℂ)) x -
            𝓕 (fun u : ℝ => (triangleFourierKernel u : ℂ)) x :=
      fourier_sub_of_integrable integrable_carneiroLittmannModulatedTriangle
        integrable_triangleFourierKernel.ofReal x
    _ = (carneiroLittmannSincSquareBase (x + 1) : ℂ) -
        𝓕 (fun u : ℝ => (triangleFourierKernel u : ℂ)) x := by
      rw [fourier_carneiroLittmannModulatedTriangle]
    _ = (carneiroLittmannSincSquareBase (x + 1) : ℂ) -
        (carneiroLittmannSincSquareBase x : ℂ) := by
      simpa only [carneiroLittmannSincSquareBase] using
        congrArg (fun z : ℂ =>
          (carneiroLittmannSincSquareBase (x + 1) : ℂ) - z)
          (fourier_triangleFourierKernel x)

private theorem fourier_carneiroLittmannSpectralPrimitiveDerivative (x : ℝ) :
    𝓕 carneiroLittmannSpectralPrimitiveDerivative x =
      carneiroLittmannSpectralFrequency * (x : ℂ) *
        ((carneiroLittmannSincSquareBase (x + 1) : ℂ) -
          (carneiroLittmannSincSquareBase x : ℂ)) := by
  have hDerivFunction : deriv carneiroLittmannSpectralPrimitive =
      carneiroLittmannSpectralPrimitiveDerivative := by
    funext u
    exact (hasDerivAt_carneiroLittmannSpectralPrimitive u).deriv
  have hFourierDeriv := congrFun
    (Real.fourier_deriv integrable_carneiroLittmannSpectralPrimitive
      differentiable_carneiroLittmannSpectralPrimitive
      integrable_deriv_carneiroLittmannSpectralPrimitive) x
  rw [hDerivFunction, fourier_carneiroLittmannSpectralPrimitive] at hFourierDeriv
  unfold carneiroLittmannSpectralFrequency
  push_cast
  simpa only [smul_eq_mul] using hFourierDeriv

/-- The compact spectral profile has the concrete Carneiro--Littmann
derivative as its standard Fourier transform. This replaces a Paley--Wiener
appeal by an explicit compact-spectrum calculation. -/
theorem fourier_carneiroLittmannSpectralProfile (x : ℝ) :
    𝓕 carneiroLittmannSpectralProfile x =
      (carneiroLittmannDerivative x : ℂ) := by
  let c : ℂ := carneiroLittmannSpectralFrequency
  let modulatedTriangle : ℝ → ℂ := fun u =>
    carneiroLittmannSpectralPhase u * (triangleFourierKernel u : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c, carneiroLittmannSpectralFrequency]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero))
      Complex.I_ne_zero
  have hDerivativeFunction : carneiroLittmannSpectralPrimitiveDerivative =
      fun u => c * (carneiroLittmannSpectralProfile u -
        2 * modulatedTriangle u) := by
    funext u
    rw [carneiroLittmannSpectralPrimitiveDerivative_eq]
    dsimp [c, modulatedTriangle, carneiroLittmannSpectralFrequency]
    ring
  have hTransformDerivative :
      𝓕 carneiroLittmannSpectralPrimitiveDerivative x =
        c * (𝓕 carneiroLittmannSpectralProfile x -
          2 * 𝓕 modulatedTriangle x) := by
    rw [hDerivativeFunction, fourier_const_mul]
    congr 1
    rw [fourier_sub_of_integrable integrable_carneiroLittmannSpectralProfile
      (integrable_carneiroLittmannModulatedTriangle.const_mul 2) x]
    rw [fourier_const_mul]
  have hDerivativeKnown :=
    fourier_carneiroLittmannSpectralPrimitiveDerivative x
  have hModulatedKnown :
      𝓕 modulatedTriangle x =
        (carneiroLittmannSincSquareBase (x + 1) : ℂ) := by
    exact fourier_carneiroLittmannModulatedTriangle x
  rw [hModulatedKnown] at hTransformDerivative
  rw [hDerivativeKnown] at hTransformDerivative
  have hFrequency : c = (((2 * Real.pi : ℝ) : ℂ) * Complex.I) := rfl
  have hCancelled :
      𝓕 carneiroLittmannSpectralProfile x -
          2 * (carneiroLittmannSincSquareBase (x + 1) : ℂ) =
        (x : ℂ) *
          ((carneiroLittmannSincSquareBase (x + 1) : ℂ) -
            (carneiroLittmannSincSquareBase x : ℂ)) := by
    apply mul_left_cancel₀ hc
    rw [hFrequency]
    simpa only [c, carneiroLittmannSpectralFrequency, mul_assoc] using
      hTransformDerivative.symm
  calc
    𝓕 carneiroLittmannSpectralProfile x =
        (x : ℂ) *
            ((carneiroLittmannSincSquareBase (x + 1) : ℂ) -
              (carneiroLittmannSincSquareBase x : ℂ)) +
          2 * (carneiroLittmannSincSquareBase (x + 1) : ℂ) := by
      linear_combination hCancelled
    _ = (carneiroLittmannDerivative x : ℂ) := by
      rw [carneiroLittmannDerivative_eq_translationDifference_add_sincSquare]
      simp only [carneiroLittmannTranslationPotential,
        carneiroLittmannSincSquare]
      push_cast
      ring

/-- Fourier inversion identifies the project-normalized transform of the
Carneiro--Littmann derivative with its compact spectral profile. -/
theorem fourierKernel_carneiroLittmannDerivative_eq_spectralProfile (xi : ℝ) :
    fourierKernel carneiroLittmannDerivative xi =
      carneiroLittmannSpectralProfile (xi / (2 * Real.pi)) := by
  have hFourierEq : 𝓕 carneiroLittmannSpectralProfile =
      fun x : ℝ => (carneiroLittmannDerivative x : ℂ) := by
    funext x
    exact fourier_carneiroLittmannSpectralProfile x
  have hFourierIntegrable : Integrable (𝓕 carneiroLittmannSpectralProfile) := by
    rw [hFourierEq]
    exact integrable_carneiroLittmannDerivative.ofReal
  have hInv := integrable_carneiroLittmannSpectralProfile.fourierInv_fourier_eq
    hFourierIntegrable
    continuous_carneiroLittmannSpectralProfile.continuousAt
    (v := xi / (2 * Real.pi))
  rw [Real.fourierInv_eq', hFourierEq] at hInv
  rw [← hInv]
  unfold fourierKernel
  apply integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul]
  have hPhase :
      Complex.exp (((2 * Real.pi * inner ℝ t
        (xi / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (Complex.I * (xi * t)) := by
    congr 1
    rw [show inner ℝ t (xi / (2 * Real.pi)) =
      t * (xi / (2 * Real.pi)) by
        calc
          inner ℝ t (xi / (2 * Real.pi)) =
              inner ℝ (t • (1 : ℝ))
                ((xi / (2 * Real.pi)) • (1 : ℝ)) := by simp
          _ = t * (xi / (2 * Real.pi)) * inner ℝ (1 : ℝ) 1 := by
            rw [real_inner_smul_left, real_inner_smul_right]
            ring
          _ = t * (xi / (2 * Real.pi)) := by norm_num]
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hPhase]
  ring

/-- The project-normalized Fourier transform of the derivative vanishes
outside the compact frequency band `|xi| < 2 * pi`. -/
theorem fourierKernel_carneiroLittmannDerivative_eq_zero_of_two_pi_le_abs
    {xi : ℝ} (hxi : 2 * Real.pi ≤ |xi|) :
    fourierKernel carneiroLittmannDerivative xi = 0 := by
  rw [fourierKernel_carneiroLittmannDerivative_eq_spectralProfile]
  apply carneiroLittmannSpectralProfile_eq_zero_of_one_le_abs
  rw [abs_div, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  exact (le_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)).2 (by
    simpa using hxi)

end DirichletPolynomial
end PrimeNumberTheorem
