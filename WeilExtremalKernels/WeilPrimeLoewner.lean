import WeilExtremalKernels.WeilLoewnerKernel

/-!
# The prime-power block as an exact Loewner kernel

The auxiliary assembly evaluates each prime-power contribution directly with
sines and cosines.  The CCM assembly stores the same contribution as value
and derivative data for a Loewner divided-difference kernel.

At integer Fourier indices these descriptions agree by `2 * pi` periodicity.
This module proves that identity for one weighted phase and for every finite
sum of weighted phases.  It contains no interval arithmetic and no
special-function assumptions.
-/

namespace WeilExtremalKernels

open scoped BigOperators

/-- Phase used by the direct auxiliary prime-power formula. -/
def auxiliaryPrimeAngle (phase : Real) (n : Int) : Real :=
  2 * Real.pi * (n : Real) * phase

/-- Phase used by the CCM prime-power value and derivative data. -/
def ccmPrimeAngle (phase : Real) (n : Int) : Real :=
  2 * Real.pi * (n : Real) * (1 - phase)

/-- Integer Fourier frequencies turn the CCM sine phase into the negative
auxiliary sine phase. -/
theorem sin_ccmPrimeAngle
    (phase : Real) (n : Int) :
    Real.sin (ccmPrimeAngle phase n) =
      -Real.sin (auxiliaryPrimeAngle phase n) := by
  have hangle :
      ccmPrimeAngle phase n =
        (n : Real) * (2 * Real.pi) -
          auxiliaryPrimeAngle phase n := by
    unfold ccmPrimeAngle auxiliaryPrimeAngle
    ring
  rw [hangle]
  exact Real.sin_int_mul_two_pi_sub _ n

/-- Integer Fourier frequencies identify the two cosine phases. -/
theorem cos_ccmPrimeAngle
    (phase : Real) (n : Int) :
    Real.cos (ccmPrimeAngle phase n) =
      Real.cos (auxiliaryPrimeAngle phase n) := by
  have hangle :
      ccmPrimeAngle phase n =
        (n : Real) * (2 * Real.pi) -
          auxiliaryPrimeAngle phase n := by
    unfold ccmPrimeAngle auxiliaryPrimeAngle
    ring
  rw [hangle]
  exact Real.cos_int_mul_two_pi_sub _ n

/-- One weighted prime-power contribution to the CCM value data. -/
def ccmPrimeValue
    (weight phase : Real) (n : Int) : Real :=
  -weight * Real.sin (ccmPrimeAngle phase n) / Real.pi

/-- One weighted prime-power contribution to the CCM derivative data. -/
def ccmPrimeDerivative
    (weight phase : Real) (n : Int) : Real :=
  -2 * weight * (1 - phase) *
    Real.cos (ccmPrimeAngle phase n)

theorem ccmPrimeValue_eq_auxiliary
    (weight phase : Real) (n : Int) :
    ccmPrimeValue weight phase n =
      weight * Real.sin (auxiliaryPrimeAngle phase n) / Real.pi := by
  unfold ccmPrimeValue
  rw [sin_ccmPrimeAngle]
  ring

theorem ccmPrimeDerivative_eq_auxiliary
    (weight phase : Real) (n : Int) :
    ccmPrimeDerivative weight phase n =
      -2 * weight * (1 - phase) *
        Real.cos (auxiliaryPrimeAngle phase n) := by
  unfold ccmPrimeDerivative
  rw [cos_ccmPrimeAngle]

/-- The contribution of one prime power to the final auxiliary matrix.

This includes the minus sign with which the direct Guinand-Weil prime block
enters the assembled matrix.
-/
def auxiliaryPrimeKernel
    (weight phase : Real) (m n : Int) : Real :=
  if m = n then
    -2 * weight * (1 - phase) *
      Real.cos (auxiliaryPrimeAngle phase n)
  else
    weight *
      (Real.sin (auxiliaryPrimeAngle phase m) -
        Real.sin (auxiliaryPrimeAngle phase n)) /
      (Real.pi * ((m - n : Int) : Real))

/-- The direct auxiliary prime-power block is exactly the CCM Loewner block
at every pair of integer Fourier indices. -/
theorem integerLoewnerKernel_ccmPrime_eq_auxiliary
    (weight phase : Real) (m n : Int) :
    integerLoewnerKernel
        (ccmPrimeValue weight phase)
        (ccmPrimeDerivative weight phase) m n =
      auxiliaryPrimeKernel weight phase m n := by
  by_cases hmn : m = n
  · subst n
    simp [integerLoewnerKernel, auxiliaryPrimeKernel,
      ccmPrimeDerivative_eq_auxiliary]
  · have hsub : (((m - n : Int) : Real)) != 0 := by
      exact_mod_cast sub_ne_zero.mpr hmn
    rw [integerLoewnerKernel]
    simp only [if_neg hmn]
    rw [ccmPrimeValue_eq_auxiliary,
      ccmPrimeValue_eq_auxiliary]
    unfold auxiliaryPrimeKernel
    rw [if_neg hmn]
    field_simp [Real.pi_ne_zero, hsub]
    ring

/-- Loewner kernels commute with arbitrary finite sums of value and
derivative data. -/
theorem integerLoewnerKernel_finset_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (value derivative : ι -> Int -> Real)
    (m n : Int) :
    integerLoewnerKernel
        (fun k => ∑ q in s, value q k)
        (fun k => ∑ q in s, derivative q k) m n =
      ∑ q in s, integerLoewnerKernel (value q) (derivative q) m n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [integerLoewnerKernel]
  | @insert q s hqs ih =>
      simp only [Finset.sum_insert hqs]
      rw [integerLoewnerKernel_add, ih]

/-- CCM value data for a finite family of weighted prime-power phases. -/
def ccmPrimeValueSum
    {ι : Type*} (s : Finset ι)
    (weight phase : ι -> Real) (n : Int) : Real :=
  ∑ q in s, ccmPrimeValue (weight q) (phase q) n

/-- CCM derivative data for a finite family of weighted prime-power phases. -/
def ccmPrimeDerivativeSum
    {ι : Type*} (s : Finset ι)
    (weight phase : ι -> Real) (n : Int) : Real :=
  ∑ q in s, ccmPrimeDerivative (weight q) (phase q) n

/-- Direct auxiliary kernel for a finite family of weighted prime-power
phases. -/
def auxiliaryPrimeKernelSum
    {ι : Type*} (s : Finset ι)
    (weight phase : ι -> Real) (m n : Int) : Real :=
  ∑ q in s, auxiliaryPrimeKernel (weight q) (phase q) m n

/-- The full finite prime-power source agrees pointwise between the auxiliary
and CCM routes. -/
theorem integerLoewnerKernel_ccmPrimeSum_eq_auxiliary
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weight phase : ι -> Real)
    (m n : Int) :
    integerLoewnerKernel
        (ccmPrimeValueSum s weight phase)
        (ccmPrimeDerivativeSum s weight phase) m n =
      auxiliaryPrimeKernelSum s weight phase m n := by
  unfold ccmPrimeValueSum ccmPrimeDerivativeSum
    auxiliaryPrimeKernelSum
  rw [integerLoewnerKernel_finset_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  exact integerLoewnerKernel_ccmPrime_eq_auxiliary
    (weight q) (phase q) m n

/-- Assembly shape of the auxiliary global kernel after separating its
archimedean, prime-power, and pole sources. -/
def auxiliaryGlobalKernel
    (archimedean prime : Int -> Int -> Real)
    (poleC poleS : Int -> Real)
    (m n : Int) : Real :=
  archimedean m n + prime m n +
    rankTwoPoleKernel poleC poleS m n

/-- After the prime-power identity, equality of the full auxiliary and CCM
kernels reduces exactly to the archimedean Loewner identity. -/
theorem auxiliaryGlobalKernel_eq_ccm_of_archimedean
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weight phase : ι -> Real)
    (arch archDerivative poleC poleS : Int -> Real)
    (archimedean : Int -> Int -> Real)
    (harch :
      forall m n,
        archimedean m n =
          integerLoewnerKernel arch archDerivative m n)
    (m n : Int) :
    auxiliaryGlobalKernel archimedean
        (auxiliaryPrimeKernelSum s weight phase)
        poleC poleS m n =
      ccmIntegerKernel
        (fun k => arch k + ccmPrimeValueSum s weight phase k)
        (fun k =>
          archDerivative k +
            ccmPrimeDerivativeSum s weight phase k)
        poleC poleS m n := by
  rw [ccmIntegerKernel_source_decomposition]
  unfold auxiliaryGlobalKernel
  rw [harch,
    integerLoewnerKernel_ccmPrimeSum_eq_auxiliary]

/-- The same reduction holds simultaneously for every finite cutoff matrix. -/
theorem auxiliaryGlobalKernel_cutoff_eq_ccm_of_archimedean
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weight phase : ι -> Real)
    (arch archDerivative poleC poleS : Int -> Real)
    (archimedean : Int -> Int -> Real)
    (harch :
      forall m n,
        archimedean m n =
          integerLoewnerKernel arch archDerivative m n)
    (N : Nat) :
    integerKernelCutoffMatrix
        (auxiliaryGlobalKernel archimedean
          (auxiliaryPrimeKernelSum s weight phase)
          poleC poleS) N =
      integerKernelCutoffMatrix
        (ccmIntegerKernel
          (fun k => arch k + ccmPrimeValueSum s weight phase k)
          (fun k =>
            archDerivative k +
              ccmPrimeDerivativeSum s weight phase k)
          poleC poleS) N := by
  apply integerKernelCutoffMatrix_eq_of_pointwise
  intro m n
  exact auxiliaryGlobalKernel_eq_ccm_of_archimedean
    s weight phase arch archDerivative poleC poleS
    archimedean harch m n

end WeilExtremalKernels
