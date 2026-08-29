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
interchanged with the integral.  The exact AFE/QCT decomposition of each
twisted moment, reciprocal-LCM main-term
asymptotic, tail estimates, and especially the cubic MRSTT Mobius
decorrelation theorem are not available as proved Lean imports.  The final
facade therefore keeps `hexact`, `hmain`, and `hrem` as theorem hypotheses.
They are local binders, not global axioms.

Consequently the accurate status is:

- complete internal paper proof candidate and executable parameter audit;
- first kernel-checked structural/reassembly layer complete;
- full end-to-end Lean formalization still requires formalizing the named
  analytic inputs, including the external MRSTT theorem.
