import HardyTheorem.SelbergJDiagonalRay

open Complex

namespace HardyTheorem

/-! # Coefficient, phase, and damping identities on the diagonal gcd ray -/

theorem selbergPhysicalPairMollifierCoefficient_eq_diagonalBase
    (X kappa lambda mu nu : ℕ) :
    selbergPhysicalPairMollifierCoefficient X kappa lambda mu nu =
      selbergDiagonalMollifierBase X kappa nu mu lambda := by
  unfold selbergPhysicalPairMollifierCoefficient
    selbergDiagonalMollifierBase selbergDiagonalMollifierProduct
  ring

theorem selbergPhysicalPairDamping_on_gcdRay
    {delta : ℝ} {kappa lambda mu nu r : ℕ}
    (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (_hmu : 1 ≤ mu) (hnu : 1 ≤ nu) :
    selbergPhysicalPairDamping delta
        (r * ((lambda * mu) / Nat.gcd (kappa * nu) (lambda * mu)))
        kappa lambda
        (r * ((kappa * nu) / Nat.gcd (kappa * nu) (lambda * mu)))
        mu nu =
      selbergDiagonalGaussianParameter delta kappa mu
        (Nat.gcd (kappa * nu) (lambda * mu)) * (r : ℝ) ^ 2 := by
  let A := kappa * nu
  let B := lambda * mu
  let g := Nat.gcd A B
  have hg : 0 < g := Nat.gcd_pos_of_pos_left B
    (Nat.mul_pos hkappa hnu)
  have hgC : ((g : ℕ) : ℝ) ≠ 0 := by positivity
  have hcastA : (((A / g : ℕ) : ℝ)) = (A : ℝ) / (g : ℝ) :=
    Nat.cast_div (Nat.gcd_dvd_left A B) hgC
  have hcastB : (((B / g : ℕ) : ℝ)) = (B : ℝ) / (g : ℝ) :=
    Nat.cast_div (Nat.gcd_dvd_right A B) hgC
  unfold selbergPhysicalPairDamping selbergPhysicalSquareRatio
    selbergDiagonalGaussianParameter
  simp only [A, B, g] at hcastA hcastB ⊢
  push_cast
  rw [hcastA, hcastB]
  have hlambdaC : (lambda : ℝ) ≠ 0 := by positivity
  have hnuC : (nu : ℝ) ≠ 0 := by positivity
  field_simp [hgC, hlambdaC, hnuC]
  push_cast
  ring

theorem selbergPhysicalPairSignedFrequency_on_gcdRay
    {delta : ℝ} {kappa lambda mu nu r : ℕ}
    (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (_hmu : 1 ≤ mu) (hnu : 1 ≤ nu) :
    selbergPhysicalPairSignedFrequency delta
        (r * ((lambda * mu) / Nat.gcd (kappa * nu) (lambda * mu)))
        kappa lambda
        (r * ((kappa * nu) / Nat.gcd (kappa * nu) (lambda * mu)))
        mu nu = 0 := by
  let A := kappa * nu
  let B := lambda * mu
  let g := Nat.gcd A B
  have hg : 0 < g := Nat.gcd_pos_of_pos_left B
    (Nat.mul_pos hkappa hnu)
  have hgC : ((g : ℕ) : ℝ) ≠ 0 := by positivity
  have hcastA : (((A / g : ℕ) : ℝ)) = (A : ℝ) / (g : ℝ) :=
    Nat.cast_div (Nat.gcd_dvd_left A B) hgC
  have hcastB : (((B / g : ℕ) : ℝ)) = (B : ℝ) / (g : ℝ) :=
    Nat.cast_div (Nat.gcd_dvd_right A B) hgC
  unfold selbergPhysicalPairSignedFrequency selbergPhysicalSquareRatio
  simp only [A, B, g] at hcastA hcastB ⊢
  push_cast
  rw [hcastA, hcastB]
  have hlambdaC : (lambda : ℝ) ≠ 0 := by positivity
  have hnuC : (nu : ℝ) ≠ 0 := by positivity
  field_simp [hgC, hlambdaC, hnuC]
  push_cast
  ring

theorem selbergPhysicalPairIntegrand_on_gcdRay
    {delta theta u : ℝ} {kappa lambda mu nu r : ℕ}
    (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hmu : 1 ≤ mu) (hnu : 1 ≤ nu) (hr : 1 ≤ r) :
    selbergPhysicalPairIntegrand delta theta u
        (r * ((lambda * mu) / Nat.gcd (kappa * nu) (lambda * mu)))
        kappa lambda
        (r * ((kappa * nu) / Nat.gcd (kappa * nu) (lambda * mu)))
        mu nu =
      (selbergDiagonalOriginalIntegrand
        (selbergDiagonalGaussianParameter delta kappa mu
          (Nat.gcd (kappa * nu) (lambda * mu))) theta (r - 1) u : ℝ) := by
  unfold selbergPhysicalPairIntegrand selbergOscillatoryGaussian
    selbergDiagonalOriginalIntegrand
  rw [show r - 1 + 1 = r by omega]
  rw [selbergPhysicalPairDamping_on_gcdRay hkappa hlambda hmu hnu,
    selbergPhysicalPairSignedFrequency_on_gcdRay hkappa hlambda hmu hnu]
  norm_num

end HardyTheorem
