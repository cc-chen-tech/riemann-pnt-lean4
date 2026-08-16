import WeilExtremalKernels.WeilSourceKernel

/-!
# The concrete rational pole source

The finite Guinand-Weil dictionary uses the scalar pole source

`psi(x) = C * x / (x^2 + beta^2)`.

Its Loewner kernel is the two-index rational pole matrix.  At
`beta = L / (4*pi)` and `C = 2*L*sinh(L/4)^2/pi^2`, that matrix is exactly
the expanded auxiliary pole formula and hence the factorized CCM rank-two
formula.
-/

namespace WeilExtremalKernels

/-- Scalar rational pole source evaluated at an integer Fourier index. -/
def rationalPoleSourceValue
    (C beta : Real) (n : Int) : Real :=
  C * (n : Real) / ((n : Real) ^ 2 + beta ^ 2)

/-- Derivative data of the rational pole source. -/
def rationalPoleSourceDerivative
    (C beta : Real) (n : Int) : Real :=
  C * (beta ^ 2 - (n : Real) ^ 2) /
    (((n : Real) ^ 2 + beta ^ 2) ^ 2)

/-- Concrete source data for the pole block. -/
def rationalPoleSourceData
    (C beta : Real) : WeilSourceData where
  value := rationalPoleSourceValue C beta
  derivative := rationalPoleSourceDerivative C beta

/-- Two-index rational form of the pole matrix. -/
def rationalPoleKernel
    (C beta : Real) (m n : Int) : Real :=
  C * (beta ^ 2 - (m : Real) * (n : Real)) /
    (((m : Real) ^ 2 + beta ^ 2) *
      ((n : Real) ^ 2 + beta ^ 2))

theorem poleSourceDenominator_pos
    {beta : Real} (hbeta : beta != 0) (n : Int) :
    0 < (n : Real) ^ 2 + beta ^ 2 := by
  exact add_pos_of_nonneg_of_pos
    (sq_nonneg (n : Real))
    (sq_pos_of_ne_zero hbeta)

/-- The Loewner divided difference of the rational source is its explicit
two-index pole matrix, including the diagonal derivative case. -/
theorem rationalPoleSourceData_kernel_eq_rational
    (C beta : Real) (hbeta : beta != 0)
    (m n : Int) :
    (rationalPoleSourceData C beta).kernel m n =
      rationalPoleKernel C beta m n := by
  have hmden :
      (m : Real) ^ 2 + beta ^ 2 != 0 :=
    (poleSourceDenominator_pos hbeta m).ne'
  have hnden :
      (n : Real) ^ 2 + beta ^ 2 != 0 :=
    (poleSourceDenominator_pos hbeta n).ne'
  by_cases hmn : m = n
  · subst n
    unfold WeilSourceData.kernel rationalPoleSourceData
      rationalPoleSourceDerivative rationalPoleKernel
      integerLoewnerKernel
    simp only [if_pos rfl]
    field_simp [hmden]
    ring
  · have hsub : (((m - n : Int) : Real)) != 0 := by
      exact_mod_cast sub_ne_zero.mpr hmn
    unfold WeilSourceData.kernel rationalPoleSourceData
      rationalPoleSourceValue rationalPoleKernel
      integerLoewnerKernel
    simp only [if_neg hmn]
    field_simp [hmden, hnden, hsub]
    ring

/-- Pole scale appearing in the finite dictionary. -/
def paperPoleBeta (L : Real) : Real :=
  L / (4 * Real.pi)

/-- Pole coefficient after rewriting `sqrt(c) + 1/sqrt(c) - 2` as
`4*sinh(L/4)^2`. -/
def paperPoleCoefficient
    (L sinhQuarter : Real) : Real :=
  2 * L * sinhQuarter ^ 2 / Real.pi ^ 2

theorem paperPoleBeta_ne_zero
    {L : Real} (hL : 0 < L) :
    paperPoleBeta L != 0 := by
  unfold paperPoleBeta
  positivity

/-- The source-form rational matrix is exactly the expanded auxiliary pole
formula. -/
theorem rationalPoleKernel_paper_eq_expanded
    {L : Real} (hL : 0 < L)
    (sinhQuarter : Real) (m n : Int) :
    rationalPoleKernel
        (paperPoleCoefficient L sinhQuarter)
        (paperPoleBeta L) m n =
      expandedPoleKernel L sinhQuarter m n := by
  have hbeta := paperPoleBeta_ne_zero hL
  have hmden :
      (m : Real) ^ 2 + paperPoleBeta L ^ 2 != 0 :=
    (poleSourceDenominator_pos hbeta m).ne'
  have hnden :
      (n : Real) ^ 2 + paperPoleBeta L ^ 2 != 0 :=
    (poleSourceDenominator_pos hbeta n).ne'
  have hmPole : poleDenominator L m != 0 :=
    (poleDenominator_pos hL m).ne'
  have hnPole : poleDenominator L n != 0 :=
    (poleDenominator_pos hL n).ne'
  unfold rationalPoleKernel paperPoleCoefficient
    paperPoleBeta expandedPoleKernel poleDenominator
  field_simp [Real.pi_ne_zero, hmden, hnden, hmPole, hnPole]
  ring

/-- The concrete paper pole source is compatible with the normalized CCM
rank-two factors. -/
theorem paperPoleSourceCompatible
    {L : Real} (hL : 0 < L)
    (sinhQuarter : Real) :
    PoleSourceCompatible
      (rationalPoleSourceData
        (paperPoleCoefficient L sinhQuarter)
        (paperPoleBeta L))
      (normalizedPoleC L (Real.sqrt L) sinhQuarter)
      (normalizedPoleS L (Real.sqrt L) sinhQuarter) := by
  intro m n
  rw [rationalPoleSourceData_kernel_eq_rational
    _ _ (paperPoleBeta_ne_zero hL)]
  rw [rationalPoleKernel_paper_eq_expanded hL]
  symm
  exact rankTwoPoleKernel_sqrt_eq_expanded
    hL sinhQuarter m n

end WeilExtremalKernels
