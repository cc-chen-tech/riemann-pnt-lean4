import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTNontrivialRealTransfer

/-!
# Target-amplitude transfer to the unnormalized Chebyshev error

Multiplying the genuine relative error by a positive sample point converts the
target scale `x^(beta - 1)` into `x^beta`.  This module performs that conversion
for unsigned and signed arbitrarily-far real-point witnesses.
-/

namespace PrimeNumberTheorem

/-- The unnormalized centered Chebyshev error. -/
noncomputable def chebyshevPsi0Error (x : ℝ) : ℝ :=
  chebyshevPsi0 x - x

/-- Multiplying the relative target power by the sample point gives the
unnormalized target power. -/
theorem self_mul_targetZeroPowerAmplitude
    {beta x : ℝ} (hx : 0 < x) :
    x * targetZeroPowerAmplitude beta x = x ^ beta := by
  unfold targetZeroPowerAmplitude
  nth_rewrite 1 [← Real.rpow_one x]
  rw [← Real.rpow_add hx]
  congr 1
  ring

/-- The unnormalized error is the sample point times the relative error away
from zero. -/
theorem chebyshevPsi0Error_eq_self_mul_relative
    {x : ℝ} (hx : x ≠ 0) :
    chebyshevPsi0Error x = x * relativeChebyshevPsi0Error x := by
  simp only [chebyshevPsi0Error, relativeChebyshevPsi0Error]
  rw [mul_comm, div_mul_cancel₀ _ hx]

/-- An unsigned relative-error witness at scale `q * x^(beta - 1)` gives an
unnormalized witness at scale `q * x^beta`. -/
theorem HasFarTargetAmplitudeWitness.relativeChebyshevPsi0Error_to_unnormalized
    {beta q : ℝ}
    (hwitness :
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => q * targetZeroPowerAmplitude beta x)) :
    HasFarTargetAmplitudeWitness
      chebyshevPsi0Error
      (fun x => q * x ^ beta) := by
  intro X
  rcases hwitness (max X 1) with ⟨x, hxMax, hxWitness⟩
  have hxOne : 1 ≤ x := (le_max_right X 1).trans hxMax
  have hxPos : 0 < x := zero_lt_one.trans_le hxOne
  have hscaled :=
    mul_le_mul_of_nonneg_left hxWitness hxPos.le
  refine ⟨x, (le_max_left X 1).trans hxMax, ?_⟩
  calc
    q * x ^ beta =
        x * (q * targetZeroPowerAmplitude beta x) := by
          rw [← self_mul_targetZeroPowerAmplitude hxPos]
          ring
    _ ≤ x * |relativeChebyshevPsi0Error x| := hscaled
    _ = |chebyshevPsi0Error x| := by
      calc
        x * |relativeChebyshevPsi0Error x| =
            |x| * |relativeChebyshevPsi0Error x| := by
              rw [abs_of_pos hxPos]
        _ = |x * relativeChebyshevPsi0Error x| := (abs_mul _ _).symm
        _ = |chebyshevPsi0Error x| := by
          rw [chebyshevPsi0Error_eq_self_mul_relative hxPos.ne']

/-- A positive relative-error witness at scale `q * x^(beta - 1)` gives a
positive unnormalized witness at scale `q * x^beta`. -/
theorem
    HasFarPositiveTargetAmplitudeWitness.relativeChebyshevPsi0Error_to_unnormalized
    {beta q : ℝ}
    (hwitness :
      HasFarPositiveTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => q * targetZeroPowerAmplitude beta x)) :
    HasFarPositiveTargetAmplitudeWitness
      chebyshevPsi0Error
      (fun x => q * x ^ beta) := by
  intro X
  rcases hwitness (max X 1) with ⟨x, hxMax, hxWitness⟩
  have hxOne : 1 ≤ x := (le_max_right X 1).trans hxMax
  have hxPos : 0 < x := zero_lt_one.trans_le hxOne
  have hscaled :=
    mul_le_mul_of_nonneg_left hxWitness hxPos.le
  refine ⟨x, (le_max_left X 1).trans hxMax, ?_⟩
  calc
    q * x ^ beta =
        x * (q * targetZeroPowerAmplitude beta x) := by
          rw [← self_mul_targetZeroPowerAmplitude hxPos]
          ring
    _ ≤ x * relativeChebyshevPsi0Error x := hscaled
    _ = chebyshevPsi0Error x :=
      (chebyshevPsi0Error_eq_self_mul_relative hxPos.ne').symm

/-- A negative relative-error witness at scale `q * x^(beta - 1)` gives a
negative unnormalized witness at scale `q * x^beta`. -/
theorem
    HasFarNegativeTargetAmplitudeWitness.relativeChebyshevPsi0Error_to_unnormalized
    {beta q : ℝ}
    (hwitness :
      HasFarNegativeTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => q * targetZeroPowerAmplitude beta x)) :
    HasFarNegativeTargetAmplitudeWitness
      chebyshevPsi0Error
      (fun x => q * x ^ beta) := by
  intro X
  rcases hwitness (max X 1) with ⟨x, hxMax, hxWitness⟩
  have hxOne : 1 ≤ x := (le_max_right X 1).trans hxMax
  have hxPos : 0 < x := zero_lt_one.trans_le hxOne
  have hscaled :=
    mul_le_mul_of_nonneg_left hxWitness hxPos.le
  refine ⟨x, (le_max_left X 1).trans hxMax, ?_⟩
  calc
    chebyshevPsi0Error x =
        x * relativeChebyshevPsi0Error x :=
      chebyshevPsi0Error_eq_self_mul_relative hxPos.ne'
    _ ≤ x * (-(q * targetZeroPowerAmplitude beta x)) := hscaled
    _ = -(q * x ^ beta) := by
      rw [← self_mul_targetZeroPowerAmplitude hxPos]
      ring

/-- A signed relative-error target-scale certificate gives a signed
unnormalized certificate at scale `q * x^beta`. -/
theorem
    HasFarSignedTargetAmplitudeWitnesses.relativeChebyshevPsi0Error_to_unnormalized
    {beta q : ℝ}
    (hwitness :
      HasFarSignedTargetAmplitudeWitnesses
        relativeChebyshevPsi0Error
        (fun x => q * targetZeroPowerAmplitude beta x)) :
    HasFarSignedTargetAmplitudeWitnesses
      chebyshevPsi0Error
      (fun x => q * x ^ beta) :=
  ⟨hwitness.positive.relativeChebyshevPsi0Error_to_unnormalized,
    hwitness.negative.relativeChebyshevPsi0Error_to_unnormalized⟩

end PrimeNumberTheorem
