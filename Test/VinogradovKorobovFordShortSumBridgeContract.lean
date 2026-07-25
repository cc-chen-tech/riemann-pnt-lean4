import ZeroFreeRegion.VinogradovKorobov.FordShortSumBridge

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

#check fordShortSumScale
#check FordShortSumPrefixBound
#check norm_dirichletInterval_le_weight_mul_of_prefix_bound
#check norm_dirichletInterval_le_fordShortSumScale
#check norm_dirichletInterval_le_sum_fordShortSumScale
#check norm_riemannZeta_strip_le_sum_fordShortSumScale

example (C D t : ℝ) (m : ℕ) :
    fordShortSumScale C D t m =
      C * (m : ℝ) *
        Real.exp (-(Real.log (m : ℝ)) ^ 3 /
          (D * (Real.log t) ^ 2)) := by
  rfl

example (C D sigma t : ℝ) (m N : ℕ)
    (hsigma : 0 ≤ sigma) (hm : 0 < m)
    (hshort : FordShortSumPrefixBound C D t m N) :
    ‖dirichletInterval sigma t m N‖ ≤
      dirichletWeight sigma m * fordShortSumScale C D t m :=
  norm_dirichletInterval_le_fordShortSumScale
    C D sigma t m N hsigma hm hshort

end ZeroFreeRegion.VinogradovKorobov
