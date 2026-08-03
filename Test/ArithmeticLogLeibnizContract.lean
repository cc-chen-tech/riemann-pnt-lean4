import HardyTheorem.ArithmeticLogLeibniz

open scoped ArithmeticFunction

namespace HardyTheorem

example (f g : ArithmeticFunction ℝ) :
    (f * g).pmul ArithmeticFunction.log =
      f.pmul ArithmeticFunction.log * g +
        f * g.pmul ArithmeticFunction.log :=
  arithmeticFunction_pmul_log_mul f g

end HardyTheorem
