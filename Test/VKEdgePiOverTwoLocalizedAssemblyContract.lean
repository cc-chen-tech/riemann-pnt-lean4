import PrimeNumberTheorem.VKEdgePiOverTwoLocalizedAssembly

open Filter Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check normalizedWindowValues
#check normalizedWindowSup
#check LocalizedContourData

example {rho : ℂ} {multiplicity mean C : ℝ}
    (hmultiplicity : 0 < multiplicity) (hmean : 0 < mean)
    (data : LocalizedContourData rho multiplicity mean)
    (hC : C < multiplicity / mean) :
    ∀ᶠ m : ℝ in atTop,
      ∃ y ∈ gaussianLogWindow m,
        C < |normalizedPsiError rho y| :=
  data.eventually_exists_normalizedPsiError_gt
    hmultiplicity hmean hC

example {rho : ℂ} {multiplicity mean C : ℝ}
    (hrho : rho ≠ 0)
    (hmultiplicity : 0 < multiplicity) (hmean : 0 < mean)
    (data : LocalizedContourData rho multiplicity mean)
    (hC : C < multiplicity / mean) :
    ∀ᶠ Y : ℝ in atTop,
      ∃ x ∈ powerSevenWindow Y,
        C * (x ^ rho.re / ‖rho‖) <
          |chebyshevPsi x - x| :=
  data.eventually_exists_psiError_in_powerSevenWindow
    hrho hmultiplicity hmean hC

end VKEdgePiOverTwo
end PrimeNumberTheorem
