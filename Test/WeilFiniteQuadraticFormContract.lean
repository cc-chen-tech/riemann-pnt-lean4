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
