import PrimeNumberTheorem.MWKFCubicAFEDirichlet

open Complex

namespace PrimeNumberTheorem.MWKFCubic

#check one_sub_cubicCriticalPoint_eq_conj
#check riemannZeta_cubicCriticalPoint_mul_one_sub_eq_normSq
#check cubicAFEGammaProduct
#check cubicAFEGammaProduct_zero_ne
#check completedRiemannZeta_product_eq_gamma_mul_normSq
#check cubicAFEDirichletTerm

#check (@summable_norm_cubicAFEDirichletTerm :
  ∀ (t : ℝ) {z : ℂ}, 1 / 2 < z.re →
    Summable (fun p : ℕ × ℕ ↦ ‖cubicAFEDirichletTerm t z p‖))

#check (@completedRiemannZeta_shifted_product_eq_tsum :
  ∀ (t : ℝ) {z : ℂ}, 1 / 2 < z.re →
    completedRiemannZeta (cubicCriticalPoint t + z) *
        completedRiemannZeta (1 - cubicCriticalPoint t + z) =
      cubicAFEGammaProduct t z *
        ∑' p : ℕ × ℕ, cubicAFEDirichletTerm t z p)

#check cubicAFENormalizedDirichletTerm

#check (@cubicAFECompletedIntegrand_div_gamma_eq_tsum :
  ∀ (t : ℝ) {z : ℂ}, 1 / 2 < z.re →
    cubicAFECompletedIntegrand t z / cubicAFEGammaProduct t 0 =
      ∑' p : ℕ × ℕ, cubicAFENormalizedDirichletTerm t z p)

end PrimeNumberTheorem.MWKFCubic
