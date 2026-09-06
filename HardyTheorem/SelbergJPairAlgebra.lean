import HardyTheorem.SelbergFourierThetaKernel
import HardyTheorem.SelbergOscillatoryGaussian
import HardyTheorem.SelbergOffDiagonalFixedSide

open Complex
open MeasureTheory Set

namespace HardyTheorem

/-! # Exact one-pair algebra in Selberg's `J(x, theta)` expansion -/

noncomputable def selbergPhysicalSquareRatio
    (m kappa lambda : ℕ) : ℝ :=
  ((m * kappa : ℕ) : ℝ) ^ 2 / (lambda : ℝ) ^ 2

noncomputable def selbergPhysicalGaussianTerm
    (delta u : ℝ) (m kappa lambda : ℕ) : ℂ :=
  Complex.exp
    (-((Real.pi * selbergPhysicalSquareRatio m kappa lambda * u ^ 2 : ℝ) : ℂ) *
      ((Real.sin delta : ℂ) + I * Real.cos delta))

noncomputable def selbergPhysicalPairDamping
    (delta : ℝ) (m kappa lambda n mu nu : ℕ) : ℝ :=
  Real.pi * Real.sin delta *
    (selbergPhysicalSquareRatio m kappa lambda +
      selbergPhysicalSquareRatio n mu nu)

/-- The signed frequency in `term(m,kappa,lambda) * conj(term(n,mu,nu))`.
It is negative on the forward side `m*kappa/lambda > n*mu/nu`. -/
noncomputable def selbergPhysicalPairSignedFrequency
    (delta : ℝ) (m kappa lambda n mu nu : ℕ) : ℝ :=
  Real.pi * Real.cos delta *
    (selbergPhysicalSquareRatio n mu nu -
      selbergPhysicalSquareRatio m kappa lambda)

noncomputable def selbergPhysicalPairGapFrequency
    (delta : ℝ) (m kappa lambda n mu nu : ℕ) : ℝ :=
  Real.pi * Real.cos delta *
    (selbergPhysicalSquareRatio m kappa lambda -
      selbergPhysicalSquareRatio n mu nu)

noncomputable def selbergPhysicalPairIntegrand
    (delta theta u : ℝ) (m kappa lambda n mu nu : ℕ) : ℂ :=
  selbergOscillatoryGaussian
    (selbergPhysicalPairDamping delta m kappa lambda n mu nu)
    (selbergPhysicalPairSignedFrequency delta m kappa lambda n mu nu)
    theta u

theorem selbergGaussianThetaTerm_log_eq_physical
    {u : ℝ} (hu : 0 < u) (delta : ℝ) (mu nu n : ℕ) :
    selbergGaussianThetaTerm delta (Real.log u) mu nu n =
      selbergPhysicalGaussianTerm delta u n mu nu := by
  have hexp : Real.exp (2 * Real.log u) = u ^ 2 := by
    calc
      Real.exp (2 * Real.log u) = Real.exp (Real.log u) ^ (2 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ = u ^ 2 := by rw [Real.exp_log hu]
  unfold selbergGaussianThetaTerm selbergGaussianCoefficient
    selbergPhysicalGaussianTerm selbergPhysicalSquareRatio
  rw [selbergFourierZ_inv_sq, hexp]
  apply congrArg Complex.exp
  push_cast
  ring

theorem selbergPhysicalGaussian_mul_conj_eq_pairIntegrand
    (delta theta u : ℝ) (m kappa lambda n mu nu : ℕ) :
    (u ^ (-theta) : ℝ) •
        (selbergPhysicalGaussianTerm delta u m kappa lambda *
          (starRingEnd ℂ) (selbergPhysicalGaussianTerm delta u n mu nu)) =
      selbergPhysicalPairIntegrand delta theta u
        m kappa lambda n mu nu := by
  unfold selbergPhysicalGaussianTerm selbergPhysicalPairIntegrand
    selbergPhysicalPairDamping selbergPhysicalPairSignedFrequency
    selbergPhysicalSquareRatio selbergOscillatoryGaussian
  rw [← Complex.exp_conj, ← Complex.exp_add]
  apply congrArg (fun z : ℂ => (u ^ (-theta) : ℝ) • Complex.exp z)
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im] <;> ring

theorem selbergPhysicalPairSignedFrequency_neg_of_forward
    (delta : ℝ) (m kappa lambda n mu nu : ℕ) :
    selbergPhysicalPairSignedFrequency delta m kappa lambda n mu nu =
      -selbergPhysicalPairGapFrequency delta m kappa lambda n mu nu := by
  unfold selbergPhysicalPairSignedFrequency selbergPhysicalPairGapFrequency
  ring

theorem selbergPhysicalPairSignedFrequency_pos_of_reverse
    (delta : ℝ) (m kappa lambda n mu nu : ℕ) :
    selbergPhysicalPairSignedFrequency delta m kappa lambda n mu nu =
      selbergPhysicalPairGapFrequency delta n mu nu m kappa lambda := by
  unfold selbergPhysicalPairSignedFrequency selbergPhysicalPairGapFrequency
  ring

theorem selbergPhysicalPairDamping_swap
    (delta : ℝ) (m kappa lambda n mu nu : ℕ) :
    selbergPhysicalPairDamping delta m kappa lambda n mu nu =
      selbergPhysicalPairDamping delta n mu nu m kappa lambda := by
  unfold selbergPhysicalPairDamping
  ring

theorem selbergPhysicalPairIntegrand_forward_eq_conj_normalized
    (delta theta u : ℝ) (m kappa lambda n mu nu : ℕ) :
    selbergPhysicalPairIntegrand delta theta u m kappa lambda n mu nu =
      (starRingEnd ℂ) (selbergOscillatoryGaussian
        (selbergPhysicalPairDamping delta m kappa lambda n mu nu)
        (selbergPhysicalPairGapFrequency delta m kappa lambda n mu nu)
        theta u) := by
  unfold selbergPhysicalPairIntegrand selbergOscillatoryGaussian
  rw [selbergPhysicalPairSignedFrequency_neg_of_forward]
  change _ = star ((u ^ (-theta) : ℝ) • Complex.exp _)
  rw [star_smul, star_trivial]
  change _ = (u ^ (-theta) : ℝ) • (starRingEnd ℂ) (Complex.exp _)
  rw [← Complex.exp_conj]
  apply congrArg (fun z : ℂ => (u ^ (-theta) : ℝ) • Complex.exp z)
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]

theorem selbergPhysicalPairIntegrand_reverse_eq_normalized
    (delta theta u : ℝ) (m kappa lambda n mu nu : ℕ) :
    selbergPhysicalPairIntegrand delta theta u m kappa lambda n mu nu =
      selbergOscillatoryGaussian
        (selbergPhysicalPairDamping delta n mu nu m kappa lambda)
        (selbergPhysicalPairGapFrequency delta n mu nu m kappa lambda)
        theta u := by
  unfold selbergPhysicalPairIntegrand
  rw [selbergPhysicalPairSignedFrequency_pos_of_reverse,
    selbergPhysicalPairDamping_swap]

theorem selbergPhysicalPairDamping_pos
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {m kappa lambda n mu nu : ℕ}
    (hm : 1 ≤ m) (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda) :
    0 < selbergPhysicalPairDamping delta m kappa lambda n mu nu := by
  have hdeltaPi : delta < Real.pi :=
    hdelta1.trans_lt (by linarith [Real.pi_gt_three])
  have hsin : 0 < Real.sin delta :=
    Real.sin_pos_of_pos_of_lt_pi hdelta hdeltaPi
  have hratio : 0 < selbergPhysicalSquareRatio m kappa lambda := by
    unfold selbergPhysicalSquareRatio
    positivity
  have hratio2 : 0 ≤ selbergPhysicalSquareRatio n mu nu := by
    unfold selbergPhysicalSquareRatio
    positivity
  unfold selbergPhysicalPairDamping
  exact mul_pos (mul_pos Real.pi_pos hsin)
    (hratio.trans_le (le_add_of_nonneg_right hratio2))

theorem selbergPhysicalPairGapFrequency_pos_of_forward
    {delta : ℝ} (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    {m n kappa lambda mu nu : ℕ}
    (hm : 1 ≤ m) (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hnu : 1 ≤ nu) (hgap : n * lambda * mu < m * kappa * nu) :
    0 < selbergPhysicalPairGapFrequency delta m kappa lambda n mu nu := by
  have hcos : 0 < Real.cos delta :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  have hsquare := selberg_nat_square_gap_pos
    hm hkappa hlambda hnu hgap
  unfold selbergPhysicalPairGapFrequency selbergPhysicalSquareRatio
  positivity

theorem norm_integral_Ioi_selbergPhysicalPairIntegrand_forward_le
    {delta theta x : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {m n kappa lambda mu nu : ℕ}
    (hm : 1 ≤ m) (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hnu : 1 ≤ nu) (hgap : n * lambda * mu < m * kappa * nu) :
    ‖∫ u in Ioi x,
        selbergPhysicalPairIntegrand delta theta u
          m kappa lambda n mu nu‖ ≤
      2 * Real.exp
          (-selbergPhysicalPairDamping delta m kappa lambda n mu nu * x ^ 2) *
        x ^ (-theta - 1) /
          selbergPhysicalPairGapFrequency delta m kappa lambda n mu nu := by
  let f : ℝ → ℂ := fun u => selbergOscillatoryGaussian
    (selbergPhysicalPairDamping delta m kappa lambda n mu nu)
    (selbergPhysicalPairGapFrequency delta m kappa lambda n mu nu) theta u
  have hfun : (fun u => selbergPhysicalPairIntegrand delta theta u
      m kappa lambda n mu nu) = fun u => (starRingEnd ℂ) (f u) := by
    funext u
    exact selbergPhysicalPairIntegrand_forward_eq_conj_normalized
      delta theta u m kappa lambda n mu nu
  have hP := selbergPhysicalPairDamping_pos
    (n := n) (mu := mu) (nu := nu)
      hdelta hdelta1 hm hkappa hlambda
  have hQ := selbergPhysicalPairGapFrequency_pos_of_forward
    hdelta.le hdelta1 hm hkappa hlambda hnu hgap
  rw [hfun, integral_conj]
  change ‖star (∫ u in Ioi x, f u)‖ ≤ _
  rw [norm_star]
  exact norm_integral_Ioi_selbergOscillatoryGaussian_damped_le
    hP hQ htheta hx

theorem norm_integral_Ioi_selbergPhysicalPairIntegrand_reverse_le
    {delta theta x : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {m n kappa lambda mu nu : ℕ}
    (hn : 1 ≤ n) (hmu : 1 ≤ mu) (hnu : 1 ≤ nu)
    (hlambda : 1 ≤ lambda) (hgap : m * kappa * nu < n * lambda * mu) :
    ‖∫ u in Ioi x,
        selbergPhysicalPairIntegrand delta theta u
          m kappa lambda n mu nu‖ ≤
      2 * Real.exp
          (-selbergPhysicalPairDamping delta n mu nu m kappa lambda * x ^ 2) *
        x ^ (-theta - 1) /
          selbergPhysicalPairGapFrequency delta n mu nu m kappa lambda := by
  rw [show (fun u => selbergPhysicalPairIntegrand delta theta u
      m kappa lambda n mu nu) = fun u =>
        selbergOscillatoryGaussian
          (selbergPhysicalPairDamping delta n mu nu m kappa lambda)
          (selbergPhysicalPairGapFrequency delta n mu nu m kappa lambda)
          theta u by
    funext u
    exact selbergPhysicalPairIntegrand_reverse_eq_normalized
      delta theta u m kappa lambda n mu nu]
  have hP := selbergPhysicalPairDamping_pos
    (n := m) (mu := kappa) (nu := lambda)
      hdelta hdelta1 hn hmu hnu
  have hgap' : m * nu * kappa < n * mu * lambda := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hgap
  have hQ := selbergPhysicalPairGapFrequency_pos_of_forward
    hdelta.le hdelta1 hn hmu hnu hlambda hgap'
  exact norm_integral_Ioi_selbergOscillatoryGaussian_damped_le
    hP hQ htheta hx

end HardyTheorem
