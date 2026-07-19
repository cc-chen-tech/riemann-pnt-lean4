import WeilExtremalKernels.FiniteQuadraticForm

open WeilExtremalKernels

example {n : ℕ} (L : FiniteMatrix n) (d x : FiniteVector n) :
    quadraticForm (ldlMatrix L d) x =
      ∑ k, d k * (columnLinearForm L x k) ^ 2 :=
  quadraticForm_ldlMatrix L d x

example {n : ℕ} (L : FiniteMatrix n) (d x : FiniteVector n)
    (hdiagonal : ∀ k, 0 ≤ d k) :
    0 ≤ quadraticForm (ldlMatrix L d) x :=
  quadraticForm_ldlMatrix_nonneg L d x hdiagonal

example {n : ℕ} (A : FiniteMatrix n) (certificate : LDLCertificate n)
    (hreconstruct : A = certificate.reconstruct)
    (hdiagonal : ∀ k, 0 ≤ certificate.diagonal k) :
    ∀ x, 0 ≤ quadraticForm A x :=
  quadraticForm_nonneg_of_certificate A certificate hreconstruct hdiagonal

example {n : ℕ} (A C R : FiniteMatrix n) (x : FiniteVector n) (ρ : ℝ)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ) :
    |quadraticForm A x - quadraticForm C x| ≤ ρ * squaredNorm x :=
  abs_quadraticForm_sub_le_rowBound A C R x ρ hR hentry hrow

example {n : ℕ} (A C R : FiniteMatrix n) (μ ρ : ℝ)
    (hcenter : ∀ x, μ * squaredNorm x ≤ quadraticForm C x)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ) (hbudget : ρ ≤ μ) :
    ∀ x, 0 ≤ quadraticForm A x :=
  quadraticForm_nonneg_of_interval A C R μ ρ hcenter hR hentry hrow hbudget

example {n : ℕ} (A C R : FiniteMatrix n) (μ ρ : ℝ)
    (hcenter : ∀ x, μ * squaredNorm x ≤ quadraticForm C x)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ) (hbudget : ρ < μ) :
    ∀ x, x ≠ 0 → 0 < quadraticForm A x :=
  quadraticForm_pos_of_interval A C R μ ρ hcenter hR hentry hrow hbudget
