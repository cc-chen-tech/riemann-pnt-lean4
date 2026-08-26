import HardyTheorem.ConreyFarRight

open Complex

namespace HardyTheorem

example (M : ℝ) :
    ∃ A : ℝ, ∀ z : ℂ, A ≤ z.re → M ≤ (Complex.digamma z).re :=
  exists_digamma_re_ge_of_re_ge M

example (M : ℝ) :
    ∃ A : ℝ, ∀ s : ℂ, A ≤ s.re →
      M ≤ (deriv conreyH s / conreyH s).re :=
  exists_logDeriv_conreyH_re_ge_of_re_ge M

example {g g0 g1 L : ℝ} (hg : g ≠ 0) :
    ∃ A : ℝ, ∀ s : ℂ, A ≤ s.re →
      conreyDegreeOneV1 g g0 g1 L s ≠ 0 :=
  exists_conreyDegreeOneV1_ne_zero_of_re_ge hg

example {Y : ℕ} {P : ℝ → ℝ} (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (sigma0 : ℝ) :
    ∃ A : ℝ, ∀ s : ℂ, A ≤ s.re →
      conreyMollifier Y sigma0 P s ≠ 0 :=
  exists_conreyMollifier_ne_zero_of_re_ge hY hP1 sigma0

example {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    ∃ A : ℝ, ∀ s : ℂ, A ≤ s.re →
      conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P s ≠ 0 :=
  exists_conreyMollifiedDegreeOneV1_ne_zero_of_re_ge hg hY hP1

#print axioms exists_digamma_re_ge_of_re_ge
#print axioms exists_logDeriv_conreyH_re_ge_of_re_ge
#print axioms exists_conreyDegreeOneV1_ne_zero_of_re_ge
#print axioms exists_conreyMollifier_ne_zero_of_re_ge
#print axioms exists_conreyMollifiedDegreeOneV1_ne_zero_of_re_ge

end HardyTheorem
