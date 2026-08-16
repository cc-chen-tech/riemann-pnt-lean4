import WeilExtremalKernels.WeilPrimeLoewner

/-!
# Scalar reduction of the archimedean route identity

The auxiliary route presents its off-diagonal archimedean entries as divided
differences of one odd scalar function.  Its diagonal entries are computed by
a separate scalar formula.  Consequently the two-dimensional matrix identity
with the CCM Loewner kernel reduces to two one-dimensional identities:

* equality of the scalar value data;
* equality of the scalar derivative data.

This module proves that reduction exactly.  It deliberately leaves the
hypergeometric/Lerch versus digamma identities as named hypotheses rather
than hiding them in a matrix-level assumption.
-/

namespace WeilExtremalKernels

/-- Scalar value data extracted from the auxiliary signed-`S` formula. -/
def auxiliaryArchimedeanValue
    (signedS : Int -> Real) (n : Int) : Real :=
  signedS n / Real.pi

/-- The final auxiliary archimedean contribution.

The supplied diagonal already includes the sign with which the archimedean
block enters the full Weil matrix.
-/
def auxiliaryArchimedeanKernel
    (signedS diagonal : Int -> Real) (m n : Int) : Real :=
  if m = n then diagonal n
  else
    (signedS m - signedS n) /
      (Real.pi * ((m - n : Int) : Real))

/-- The direct auxiliary archimedean matrix is a Loewner kernel before any
special-function identity is used. -/
theorem auxiliaryArchimedeanKernel_eq_loewner
    (signedS diagonal : Int -> Real) (m n : Int) :
    auxiliaryArchimedeanKernel signedS diagonal m n =
      integerLoewnerKernel
        (auxiliaryArchimedeanValue signedS) diagonal m n := by
  by_cases hmn : m = n
  · subst n
    simp [auxiliaryArchimedeanKernel, integerLoewnerKernel]
  · have hsub : (((m - n : Int) : Real)) != 0 := by
      exact_mod_cast sub_ne_zero.mpr hmn
    unfold auxiliaryArchimedeanKernel integerLoewnerKernel
      auxiliaryArchimedeanValue
    rw [if_neg hmn, if_neg hmn]
    field_simp [Real.pi_ne_zero, hsub]
    ring

/-- Pointwise equality of value and derivative data gives equality of their
Loewner kernels. -/
theorem integerLoewnerKernel_congr
    (value1 value2 derivative1 derivative2 : Int -> Real)
    (hvalue : forall k, value1 k = value2 k)
    (hderivative : forall k, derivative1 k = derivative2 k)
    (m n : Int) :
    integerLoewnerKernel value1 derivative1 m n =
      integerLoewnerKernel value2 derivative2 m n := by
  by_cases hmn : m = n
  · subst n
    simp [integerLoewnerKernel, hderivative]
  · simp [integerLoewnerKernel, hmn, hvalue]

/-- The archimedean route identity follows from two scalar identities. -/
theorem auxiliaryArchimedeanKernel_eq_ccm_of_scalar_identities
    (signedS diagonal alpha alphaDerivative : Int -> Real)
    (hvalue :
      forall k,
        alpha k = auxiliaryArchimedeanValue signedS k)
    (hderivative :
      forall k,
        alphaDerivative k = diagonal k)
    (m n : Int) :
    auxiliaryArchimedeanKernel signedS diagonal m n =
      integerLoewnerKernel alpha alphaDerivative m n := by
  rw [auxiliaryArchimedeanKernel_eq_loewner]
  exact integerLoewnerKernel_congr
    (auxiliaryArchimedeanValue signedS) alpha
    diagonal alphaDerivative
    (fun k => (hvalue k).symm)
    (fun k => (hderivative k).symm) m n

/-- Once the two archimedean scalar identities hold, the complete auxiliary
and CCM global kernels agree.  The finite prime-power bridge is discharged
internally by `integerLoewnerKernel_ccmPrimeSum_eq_auxiliary`. -/
theorem auxiliaryGlobalKernel_eq_ccm_of_archimedean_scalar_identities
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weight phase : ι -> Real)
    (signedS diagonal alpha alphaDerivative poleC poleS : Int -> Real)
    (hvalue :
      forall k,
        alpha k = auxiliaryArchimedeanValue signedS k)
    (hderivative :
      forall k,
        alphaDerivative k = diagonal k)
    (m n : Int) :
    auxiliaryGlobalKernel
        (auxiliaryArchimedeanKernel signedS diagonal)
        (auxiliaryPrimeKernelSum s weight phase)
        poleC poleS m n =
      ccmIntegerKernel
        (fun k => alpha k + ccmPrimeValueSum s weight phase k)
        (fun k =>
          alphaDerivative k +
            ccmPrimeDerivativeSum s weight phase k)
        poleC poleS m n := by
  exact auxiliaryGlobalKernel_eq_ccm_of_archimedean
    s weight phase alpha alphaDerivative poleC poleS
    (auxiliaryArchimedeanKernel signedS diagonal)
    (auxiliaryArchimedeanKernel_eq_ccm_of_scalar_identities
      signedS diagonal alpha alphaDerivative hvalue hderivative)
    m n

/-- The scalar archimedean identities also identify every finite cutoff
matrix, with no cutoff-dependent analytic hypothesis. -/
theorem auxiliaryGlobalKernel_cutoff_eq_ccm_of_archimedean_scalar_identities
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weight phase : ι -> Real)
    (signedS diagonal alpha alphaDerivative poleC poleS : Int -> Real)
    (hvalue :
      forall k,
        alpha k = auxiliaryArchimedeanValue signedS k)
    (hderivative :
      forall k,
        alphaDerivative k = diagonal k)
    (N : Nat) :
    integerKernelCutoffMatrix
        (auxiliaryGlobalKernel
          (auxiliaryArchimedeanKernel signedS diagonal)
          (auxiliaryPrimeKernelSum s weight phase)
          poleC poleS) N =
      integerKernelCutoffMatrix
        (ccmIntegerKernel
          (fun k => alpha k + ccmPrimeValueSum s weight phase k)
          (fun k =>
            alphaDerivative k +
              ccmPrimeDerivativeSum s weight phase k)
          poleC poleS) N := by
  apply integerKernelCutoffMatrix_eq_of_pointwise
  intro m n
  exact
    auxiliaryGlobalKernel_eq_ccm_of_archimedean_scalar_identities
      s weight phase signedS diagonal alpha alphaDerivative
      poleC poleS hvalue hderivative m n

end WeilExtremalKernels
