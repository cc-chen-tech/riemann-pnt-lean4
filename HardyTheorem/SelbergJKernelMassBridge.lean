import HardyTheorem.SelbergJFinalBound
import HardyTheorem.SelbergFourierMellinS1

open Complex

namespace HardyTheorem

/-! # Exact logarithmic mass bridge from the theta kernel to the inverse Fourier kernel -/

noncomputable def selbergResidueInverseFourierKernel
    (delta : ℝ) (X : ℕ) (y : ℝ) : ℂ :=
  (1 / 2 : ℂ) * selbergFourierZ delta y ^ (1 / 2 : ℂ) *
    selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0

noncomputable def selbergNonconstantInverseFourierKernel
    (delta : ℝ) (X : ℕ) (y : ℝ) : ℂ :=
  -selbergFourierZ delta y ^ (-1 / 2 : ℂ) *
    selbergNonconstantThetaKernel delta X y

theorem selbergExplicitInverseFourierKernel_eq_residue_add_nonconstant
    (delta : ℝ) (X : ℕ) (y : ℝ) :
    selbergExplicitInverseFourierKernel delta X y =
      selbergResidueInverseFourierKernel delta X y +
        selbergNonconstantInverseFourierKernel delta X y := by
  unfold selbergExplicitInverseFourierKernel
    selbergResidueInverseFourierKernel
    selbergNonconstantInverseFourierKernel
  ring

theorem normSq_selbergNonconstantInverseFourierKernel_log
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaPi : delta < Real.pi / 2)
    {x : ℝ} (hx : 0 < x) (X : ℕ) :
    Complex.normSq
        (selbergNonconstantInverseFourierKernel delta X (Real.log x)) =
      x * Complex.normSq (selbergPhysicalThetaKernel delta x X) := by
  have hnormZ :
      ‖selbergFourierZ delta (Real.log x) ^ (-1 / 2 : ℂ)‖ =
        Real.exp (Real.log x / 2) := by
    convert norm_selbergFourierZ_cpow
      hdelta hdeltaPi (Real.log x) (-1 / 2) 0 using 1 <;> norm_num
    ring
  have hexpSq : Real.exp (Real.log x / 2) ^ 2 = x := by
    rw [pow_two, ← Real.exp_add]
    convert Real.exp_log hx using 1
    ring
  unfold selbergNonconstantInverseFourierKernel
  rw [Complex.normSq_eq_norm_sq, norm_mul, norm_neg, hnormZ]
  rw [← selbergPhysicalThetaKernel_eq_nonconstantThetaKernel_log
    hdelta hdelta1 hx]
  rw [Complex.normSq_eq_norm_sq]
  calc
    (Real.exp (Real.log x / 2) *
        ‖selbergPhysicalThetaKernel delta x X‖) ^ 2 =
      Real.exp (Real.log x / 2) ^ 2 *
        ‖selbergPhysicalThetaKernel delta x X‖ ^ 2 := by ring
    _ = x * ‖selbergPhysicalThetaKernel delta x X‖ ^ 2 := by rw [hexpSq]

end HardyTheorem
