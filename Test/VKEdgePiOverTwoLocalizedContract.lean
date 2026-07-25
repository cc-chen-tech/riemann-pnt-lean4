import PrimeNumberTheorem.VKEdgePiOverTwoLocalized

open Complex

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check gaussianLogWindow
#check logarithmicPowerSevenWindow
#check powerSevenWindow

#check gaussianLogWindow_log_div_four
#check exists_psiError_in_powerSevenWindow_of_normalizedPsiError

example {rho : ℂ} {C Y : ℝ}
    (hrho : rho ≠ 0) (hY : 1 ≤ Y)
    (hlocal :
      ∃ y ∈ logarithmicPowerSevenWindow Y,
        C < |normalizedPsiError rho y|) :
    ∃ x ∈ powerSevenWindow Y,
      C * (x ^ rho.re / ‖rho‖) <
        |chebyshevPsi x - x| :=
  exists_psiError_in_powerSevenWindow_of_normalizedPsiError
    hrho hY hlocal

end VKEdgePiOverTwo
end PrimeNumberTheorem
