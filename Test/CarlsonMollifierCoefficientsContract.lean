import PrimeNumberTheorem.CarlsonMollifierCoefficients

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (N n : ℕ) : ℂ := truncatedZetaArithmetic N n

example (X n : ℕ) : ℂ := truncatedMobiusArithmetic X n

example (X N n : ℕ) : ℂ := mollifiedTruncatedCoefficient X N n

example {X N n : ℕ} (hn : 0 < n) (hnX : n ≤ X) (hnN : n ≤ N) :
    mollifiedTruncatedCoefficient X N n = if n = 1 then 1 else 0 :=
  mollifiedTruncatedCoefficient_eq_one_apply hn hnX hnN

#print axioms mollifiedTruncatedCoefficient_eq_one_apply

end CarlsonZeroDensity
end PrimeNumberTheorem
