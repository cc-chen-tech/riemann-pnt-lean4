import WeilExtremalKernels.WeilPoleSource

/-!
# The concrete finite prime-power source

At a fixed prime cutoff there are finitely many prime powers.  Their source
value and derivative data are the finite CCM sums already identified with
the direct auxiliary Guinand-Weil block.
-/

namespace WeilExtremalKernels

/-- Source data of a finite family of weighted prime-power phases. -/
def finitePrimeSourceData
    {ι : Type*} (s : Finset ι)
    (weight phase : ι -> Real) : WeilSourceData where
  value := ccmPrimeValueSum s weight phase
  derivative := ccmPrimeDerivativeSum s weight phase

/-- The source kernel of a finite prime-power family is exactly the direct
auxiliary prime block. -/
theorem finitePrimeSourceData_kernel_eq_auxiliary
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weight phase : ι -> Real)
    (m n : Int) :
    (finitePrimeSourceData s weight phase).kernel m n =
      auxiliaryPrimeKernelSum s weight phase m n := by
  exact integerLoewnerKernel_ccmPrimeSum_eq_auxiliary
    s weight phase m n

/-- Every cutoff of the finite prime-power source agrees with the
independently assembled auxiliary prime matrix. -/
theorem finitePrimeSourceData_cutoff_eq_auxiliary
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weight phase : ι -> Real)
    (N : Nat) :
    sourceCutoffMatrix (finitePrimeSourceData s weight phase) N =
      integerKernelCutoffMatrix
        (auxiliaryPrimeKernelSum s weight phase) N := by
  apply integerKernelCutoffMatrix_eq_of_pointwise
  intro m n
  exact finitePrimeSourceData_kernel_eq_auxiliary
    s weight phase m n

/-- Prime-source cutoffs inherit exact centered nesting from the global
source representation. -/
theorem finitePrimeSourceData_centered_nested
    {ι : Type*}
    (s : Finset ι) (weight phase : ι -> Real)
    {M N : Nat} (hMN : M <= N) :
    sourceCutoffMatrix (finitePrimeSourceData s weight phase) M =
      centeredPrincipalSection hMN
        (sourceCutoffMatrix
          (finitePrimeSourceData s weight phase) N) := by
  exact sourceCutoffMatrix_centered_nested
    (finitePrimeSourceData s weight phase) hMN

end WeilExtremalKernels
