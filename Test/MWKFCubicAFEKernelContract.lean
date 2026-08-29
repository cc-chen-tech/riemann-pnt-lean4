import PrimeNumberTheorem.MWKFCubicAFEKernel

open Complex

namespace PrimeNumberTheorem.MWKFCubic

#check cubicCriticalPoint
#check cubicAFEPoleCanceller
#check cubicAFEKernelG

#check (@cubicCriticalPoint_ne_zero :
  ∀ t : ℝ, cubicCriticalPoint t ≠ 0)

#check (@one_sub_cubicCriticalPoint_ne_zero :
  ∀ t : ℝ, 1 - cubicCriticalPoint t ≠ 0)

#check (@cubicAFEKernelG_zero :
  ∀ t : ℝ, cubicAFEKernelG t 0 = 1)

#check (@cubicAFEKernelG_neg :
  ∀ (t : ℝ) (z : ℂ), cubicAFEKernelG t (-z) = cubicAFEKernelG t z)

#check (@cubicAFEKernelG_at_criticalPoint :
  ∀ t : ℝ, cubicAFEKernelG t (cubicCriticalPoint t) = 0)

#check (@cubicAFEKernelG_at_neg_criticalPoint :
  ∀ t : ℝ, cubicAFEKernelG t (-cubicCriticalPoint t) = 0)

#check (@cubicAFEKernelG_at_one_sub_criticalPoint :
  ∀ t : ℝ, cubicAFEKernelG t (1 - cubicCriticalPoint t) = 0)

#check (@cubicAFEKernelG_at_criticalPoint_sub_one :
  ∀ t : ℝ, cubicAFEKernelG t (cubicCriticalPoint t - 1) = 0)

#check (@cubicAFEKernelG_at_half :
  ∀ t : ℝ, cubicAFEKernelG t (1 / 2 : ℂ) = 0)

#check (@cubicAFEKernelG_at_neg_half :
  ∀ t : ℝ, cubicAFEKernelG t (-1 / 2 : ℂ) = 0)

end PrimeNumberTheorem.MWKFCubic
