import WeilExtremalKernels.WeilArchimedeanSource

/-!
# Cauchy source algebra for the archimedean increment

After evaluating the sine-chord integral at integer nodes, the source has
the rational shape

`scale * x / (a^2 - x^2)`.

Its Loewner kernel is exactly the sum of the two Cauchy rank-one kernels
used by the archimedean tail formalization.  This module proves that purely
algebraic identity, including the diagonal derivative.
-/

namespace WeilExtremalKernels

/-- Rational source value underlying one archimedean density slice. -/
def cauchySourceValue
    (scale a : Real) (n : Int) : Real :=
  scale * (n : Real) / (a ^ 2 - (n : Real) ^ 2)

/-- Derivative of `scale*x/(a^2-x^2)` at an integer node. -/
def cauchySourceDerivative
    (scale a : Real) (n : Int) : Real :=
  scale * (a ^ 2 + (n : Real) ^ 2) /
    ((a ^ 2 - (n : Real) ^ 2) ^ 2)

def cauchySourceData
    (scale a : Real) : WeilSourceData where
  value := cauchySourceValue scale a
  derivative := cauchySourceDerivative scale a

/-- Sum of the two Cauchy rank-one kernels. -/
def cauchyRankTwoKernel
    (scale a : Real) (m n : Int) : Real :=
  (scale / 2) *
    ((a - (m : Real))⁻¹ * (a - (n : Real))⁻¹ +
      (a + (m : Real))⁻¹ * (a + (n : Real))⁻¹)

theorem cauchy_denominators_ne
    {a : Real} {n : Int}
    (hquadratic : a ^ 2 - (n : Real) ^ 2 != 0) :
    a - (n : Real) != 0 /\ a + (n : Real) != 0 := by
  constructor
  · intro h
    apply hquadratic
    calc
      a ^ 2 - (n : Real) ^ 2 =
          (a - (n : Real)) * (a + (n : Real)) := by ring
      _ = 0 := by rw [h, zero_mul]
  · intro h
    apply hquadratic
    calc
      a ^ 2 - (n : Real) ^ 2 =
          (a - (n : Real)) * (a + (n : Real)) := by ring
      _ = 0 := by rw [h, mul_zero]

/-- Divided-difference identity for the Cauchy source, valid both on and off
the diagonal. -/
theorem cauchySourceData_kernel_eq_rankTwo
    (scale a : Real) (m n : Int)
    (hm : a ^ 2 - (m : Real) ^ 2 != 0)
    (hn : a ^ 2 - (n : Real) ^ 2 != 0) :
    (cauchySourceData scale a).kernel m n =
      cauchyRankTwoKernel scale a m n := by
  obtain ⟨hmMinus, hmPlus⟩ := cauchy_denominators_ne hm
  obtain ⟨hnMinus, hnPlus⟩ := cauchy_denominators_ne hn
  by_cases hmn : m = n
  · subst n
    unfold WeilSourceData.kernel cauchySourceData
      cauchySourceDerivative cauchyRankTwoKernel
      integerLoewnerKernel
    simp only [if_pos rfl]
    field_simp [hm, hmMinus, hmPlus]
    ring
  · have hsub : (((m - n : Int) : Real)) != 0 := by
      exact_mod_cast sub_ne_zero.mpr hmn
    unfold WeilSourceData.kernel cauchySourceData
      cauchySourceValue cauchyRankTwoKernel
      integerLoewnerKernel
    simp only [if_neg hmn]
    field_simp
      [hm, hn, hmMinus, hmPlus, hnMinus, hnPlus, hsub]
    ring

/-- Pointwise source data of an archimedean density slice.  The scale is
twice the scalar Gram weight because the divided-difference identity carries
a factor `1/2`. -/
def archimedeanDensitySourceData
    (weight rho T : Real) : WeilSourceData :=
  cauchySourceData (2 * weight) (T / rho)

/-- The source kernel of one density slice is the weighted sum of its two
global Cauchy rank-one kernels. -/
theorem archimedeanDensitySourceData_kernel
    (weight rho T : Real) (m n : Int)
    (hm :
      (T / rho) ^ 2 - (m : Real) ^ 2 != 0)
    (hn :
      (T / rho) ^ 2 - (n : Real) ^ 2 != 0) :
    (archimedeanDensitySourceData weight rho T).kernel m n =
      weight *
        (((T / rho - (m : Real))⁻¹) *
            ((T / rho - (n : Real))⁻¹) +
          ((T / rho + (m : Real))⁻¹) *
            ((T / rho + (n : Real))⁻¹)) := by
  rw [cauchySourceData_kernel_eq_rankTwo
    (2 * weight) (T / rho) m n hm hn]
  unfold cauchyRankTwoKernel
  ring

/-- Algebraic compatibility proposition for a source slice and the existing
finite rank-two density.  Its hypotheses are exactly the nodewise closed
form and pole avoidance supplied by the sine-chord calculation. -/
def ArchimedeanDensitySourceCompatible
    (weight rho T : Real) (N : Nat) : Prop :=
  sourceCutoffMatrix
      (archimedeanDensitySourceData weight rho T) N =
    paperArchimedeanRankTwoDensity N weight rho T

end WeilExtremalKernels
