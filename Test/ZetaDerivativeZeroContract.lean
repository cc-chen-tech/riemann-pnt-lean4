import PrimeNumberTheorem.ZetaDerivativeZero

open Complex

namespace PrimeNumberTheorem

example :
    deriv riemannZeta 0 / riemannZeta 0 =
      (Real.log (2 * Real.pi) : ℂ) :=
  deriv_riemannZeta_zero_div_riemannZeta_zero

end PrimeNumberTheorem
