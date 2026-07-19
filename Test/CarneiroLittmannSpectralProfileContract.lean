import PrimeNumberTheorem.CarneiroLittmannSpectralProfile

open MeasureTheory Set

namespace PrimeNumberTheorem
namespace DirichletPolynomial

example : Continuous carneiroLittmannSpectralProfile :=
  continuous_carneiroLittmannSpectralProfile

example : HasCompactSupport carneiroLittmannSpectralProfile :=
  hasCompactSupport_carneiroLittmannSpectralProfile

example : Integrable carneiroLittmannSpectralProfile :=
  integrable_carneiroLittmannSpectralProfile

example {u : ℝ} (hu : 1 ≤ |u|) :
    carneiroLittmannSpectralProfile u = 0 :=
  carneiroLittmannSpectralProfile_eq_zero_of_one_le_abs hu

#print axioms continuous_carneiroLittmannSpectralProfile
#print axioms hasCompactSupport_carneiroLittmannSpectralProfile
#print axioms integrable_carneiroLittmannSpectralProfile
#print axioms carneiroLittmannSpectralProfile_eq_zero_of_one_le_abs

end DirichletPolynomial
end PrimeNumberTheorem
