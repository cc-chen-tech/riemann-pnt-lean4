import PrimeNumberTheorem.LocalPsiL2ZeroCriterion

open Complex Filter
open Asymptotics
open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

#check (LocalPsiL2ExponentAtMost :
  ℝ → ℝ → Prop)

#check (riemannZeta_ne_zero_of_localPsiL2ExponentAtMost :
  ∀ {ε theta : ℝ},
    0 < ε →
    LocalPsiL2ExponentAtMost ε theta →
    ∀ {rho : ℂ},
      0 < rho.im →
      1 / 2 < rho.re →
      theta < rho.re →
      rho.re < 1 →
      riemannZeta rho ≠ 0)

#check (nontrivialZero_re_eq_half_of_localPsiL2ExponentAtMost_of_im_ne_zero :
  ∀ {ε : ℝ},
    0 < ε →
    LocalPsiL2ExponentAtMost ε (1 / 2) →
    ∀ {rho : ℂ},
      RiemannHypothesis.IsNontrivialZero rho →
      rho.im ≠ 0 →
      rho.re = 1 / 2)

#check (riemannHypothesis_of_localPsiL2ExponentAtMost_of_realAxis :
  ∀ {ε : ℝ},
    0 < ε →
    LocalPsiL2ExponentAtMost ε (1 / 2) →
    (∀ rho : ℂ,
      RiemannHypothesis.IsNontrivialZero rho →
      rho.im = 0 →
      rho.re = 1 / 2) →
    RiemannHypothesis.Statement)
