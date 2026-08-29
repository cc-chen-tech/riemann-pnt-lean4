# Lean status of the cubic MWKF route

## Machine-checked in this PR

The following steps now have kernel-checked Lean proofs with no project axiom,
`sorry`, or `admit`:

| analytic step | Lean theorem |
|---|---|
| `d=q r`, `e=q s`, `(r,s)=1` gcd extraction | `gcd_extraction`, `gcd_scaled_eq_iff_coprime` |
| exact diagonal ray `m e=n d` iff `m=l(d/q)`, `n=l(e/q)` | `diagonal_eq_iff_exists_scale` |
| shifted/complementary-divisor equation | `shifted_eq_complementary_divisor` |
| finite signed level recombination `((mu*mu)*1)(n)=mu(n)` | `sum_moebius_convolution_divisors` |
| reciprocal-curve operator `x d/dx = x partial_x - xi partial_xi` | `normalized_reciprocalAmplitude_derivative` |
| finite dyadic/shell little-o aggregation | `isLittleO_finset_sum` |
| literal `N=floor(T^3)` zeta/Mobius integrand and full-line integral | `cubicMomentIntegrand`, `cubicMollifiedSecondMoment` |
| continuity, compact support, and integrability of the literal moment | `continuous_cubicMomentIntegrand`, `hasCompactSupport_cubicMomentIntegrand`, `integrable_cubicMomentIntegrand` |
| exact finite expansion of the cubic mollifier and its squared norm | `cubicMollifier_eq_sum`, `cubicMollifierNormSq_eq_doubleSum` |
| exact pair amplitude and phase `1/sqrt(de) exp(it(log e-log d))` | `cubicCriticalPair_eq_exp` |
| exact bridge to the standard twisted moment | `cubicTwistedMoment_eq_invSqrt_mul_standard` |
| exact pole-cancelled AFE kernel normalization, evenness, and all six zeros | `cubicAFEKernelG_zero`, `cubicAFEKernelG_neg`, `cubicAFEKernelG_at_criticalPoint`, `cubicAFEKernelG_at_half` |
| explicit entire extension of `G_t(z) Lambda(s_t+z) Lambda(1-s_t+z)` and equality off the four poles | `differentiable_cubicAFECompletedExtension`, `cubicAFECompletedExtension_eq` |
| evenness of the completed numerator and exact residue at the sole remaining `1/z` pole | `cubicAFECompletedExtension_neg`, `cubicAFECompletedIntegrand_residue_zero` |
| exact finite-square contour identity `boundary integral = 2 pi i residue` | `rectangleBoundaryIntegral_cubicAFECompletedIntegrand` |
| exact finite-height contour identity on every ordered rectangle containing zero, including `[-X,X] x [-V,V]` | `boundaryRectIntegral_cubicAFECompletedIntegrand`, `boundaryRectIntegral_cubicAFECompletedIntegrand_symmetric` |
| oddness of the completed integrand, exact top/bottom and left/right edge changes of variables, and the normalized finite-height vertical identity | `cubicAFECompletedIntegrand_neg`, `cubicAFECompletedIntegrand_horizontal_symmetry`, `cubicAFECompletedIntegrand_vertical_symmetry`, `cubicAFEFiniteVerticalIdentity` |
| uniform Mellin-transform bound on every closed vertical strip from endpoint absolute convergence | `exists_norm_mellin_le_on_reIcc` |
| uniform closed-strip bound for Mathlib's entire completed-zeta numerator | `exists_norm_completedRiemannZeta₀_le_on_reIcc` |
| explicit degree-six polynomial times Gaussian bound for the physical horizontal AFE edge | `exists_norm_cubicAFECompletedIntegrand_horizontal_le` |
| vanishing of the horizontal edge and exact infinite-height vertical-line contour limit | `tendsto_cubicAFECompletedIntegrand_horizontalIntegral`, `tendsto_cubicAFECompletedIntegrand_verticalIntegral` |
| critical-line conjugation, nonvanishing fixed gamma product, and exact conversion from the completed product to `normSq zeta` | `one_sub_cubicCriticalPoint_eq_conj`, `cubicAFEGammaProduct_zero_ne`, `completedRiemannZeta_product_eq_gamma_mul_normSq` |
| absolute summability of the physical `(m,n)` Dirichlet family for `re z > 1/2` | `summable_norm_cubicAFEDirichletTerm` |
| exact completed-zeta double Dirichlet expansion and its pointwise normalized AFE-integrand form | `completedRiemannZeta_shifted_product_eq_tsum`, `cubicAFECompletedIntegrand_div_gamma_eq_tsum` |
| continuity of the full physical AFE scalar and invariance of each Dirichlet-term norm along a vertical line | `continuous_cubicAFEScalar_vertical`, `norm_cubicAFEDirichletTerm_vertical_eq` |
| exact finite-height interchange of the double Dirichlet series and vertical integral by dominated convergence | `hasSum_intervalIntegral_cubicAFENormalizedDirichletTerm` |
| kernel-checked finite-height AFE whose normalized double sum converges to `normSq zeta(1/2+it)` | `cubicAFEDoubleSumFinite_eq`, `tendsto_two_mul_cubicAFEDoubleSumFinite` |
| continuity, compact support, and integrability of every ordered twisted term | `continuous_cubicTwistedIntegrand`, `hasCompactSupport_cubicTwistedIntegrand`, `integrable_cubicTwistedIntegrand` |
| exact finite sum--integral interchange into genuine twisted zeta moments | `cubicComplexMollifiedSecondMoment_eq_twisted_sum` |
| exact final `4/3` reassembly | `cubic_long_mollifier_asymptotic_of_exact_inputs` |
| final reassembly specialized to the literal integral | `cubic_actual_long_mollifier_asymptotic_of_exact_inputs` |

The axiom-audit modules report only Lean/Mathlib's standard foundational
axioms (`propext`, `Classical.choice`, and `Quot.sound`).

## Remaining formalization boundary

This PR does **not** yet make the analytic theorem unconditional inside Lean.
The left side is now the literal full-line integral, rather than an arbitrary
function `I`, and its two finite mollifier factors have been expanded and
interchanged with the integral.  The completed AFE contour has also been taken
to infinite height using an explicit physical horizontal-edge majorant.  What
remains is to extract the exact arithmetic phase and product-variable weight
from the now proved finite-height AFE, carry it through the twisted-moment
integral and QCT decomposition, prove the reciprocal-LCM main-term asymptotic
and every analytic tail estimate, and especially prove the cubic MRSTT Mobius
decorrelation theorem.  The final facade therefore keeps
`hexact`, `hmain`, and `hrem` as theorem hypotheses.  They are local binders,
not global axioms.

Consequently the accurate status is:

- complete internal paper proof candidate and executable parameter audit;
- first kernel-checked structural/reassembly layer complete;
- full end-to-end Lean formalization still requires formalizing the named
  analytic inputs, including the external MRSTT theorem.
