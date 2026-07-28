import PrimeNumberTheorem.LocalPsiL2MellinCriterion

open Complex

open scoped Topology

namespace Test

#check
  (PrimeNumberTheorem.VKEdgePiOverTwo.WeightedLogPsiL2Above :
    ℝ → Prop)

#check
  (@PrimeNumberTheorem.VKEdgePiOverTwo.differentiableAt_mellinPsiError_of_weightedLogPsiL2Above :
    ∀ {theta : ℝ},
      PrimeNumberTheorem.VKEdgePiOverTwo.WeightedLogPsiL2Above theta →
      ∀ {s : ℂ},
        theta < s.re →
        DifferentiableAt ℂ
          (fun z : ℂ =>
            mellin PrimeNumberTheorem.psiErrorAboveOneComplex (-z))
          s)

#check
  (@PrimeNumberTheorem.VKEdgePiOverTwo.weightedLogPsiL2Above_of_localPsiL2ExponentAtMost :
    ∀ {ε theta : ℝ},
      0 < ε →
      0 ≤ theta →
      PrimeNumberTheorem.VKEdgePiOverTwo.LocalPsiL2ExponentAtMost ε theta →
      PrimeNumberTheorem.VKEdgePiOverTwo.WeightedLogPsiL2Above theta)

#check
  (@PrimeNumberTheorem.VKEdgePiOverTwo.riemannZeta_ne_zero_of_mellinPsiError_differentiable :
    ∀ {theta : ℝ},
      0 ≤ theta →
      theta < 1 →
      (∀ s : ℂ,
        theta < s.re →
          DifferentiableAt ℂ
            (fun z : ℂ =>
              mellin PrimeNumberTheorem.psiErrorAboveOneComplex (-z))
            s) →
      ∀ rho : ℂ,
        theta < rho.re →
        rho.re < 1 →
        riemannZeta rho ≠ 0)

#check
  (@PrimeNumberTheorem.VKEdgePiOverTwo.riemannHypothesis_of_localPsiL2ExponentAtMost :
    ∀ {ε : ℝ},
      0 < ε →
      PrimeNumberTheorem.VKEdgePiOverTwo.LocalPsiL2ExponentAtMost ε (1 / 2) →
      RiemannHypothesis.Statement)

end Test
