# Lean status of the cubic MWKF route

本次语义审计修正了一个实质错误：`85c165d9` 中的 `CubicTestWeight.smooth` 使用
`ContDiff ℝ ⊤`，而当前 Mathlib 的这个外层 `⊤` 是 `ω`（实解析），
不是 `∞`（任意阶光滑）。实解析且紧支撑于 `[1,2]` 的全实线函数
只能是零函数，所以旧版本的核检查不能说明命题覆盖了所需的非零测试权。
现在定义使用 `ContDiff ℝ ∞`，并增加“从任意 C∞ 权构造”的类型回归和
`W(3/2)=1` 的显式非零紧支撑 bump 实例。依赖链必须在此定义下重编译；
不能把旧对象文件通过当作本次验证。

当前已将有限高度 AFE 到真实全线 mollified moment 的极限交换、
物理时间积分与完整算术级数的换序，以及有限高度对角/非对角拆分，
写成无额外解析假设的 Lean 定理。对角部分有严格的 gcd 射线双射重编号；
非对角部分已按所有正、负非零整数 shift 重组，完整相位为
`t*log(1+delta/(m*r))`，没有线性化或截断。每个 shift fiber 又已严格
重编号为 `m>0`、`delta+m*r>0`、`m=-delta*rbar (mod s)` 的单变量和，
并证明第二个指标与实数商 `(delta+m*r)/s` 精确一致。所有 Möbius 系数
与物理权均保留。这不是 `T -> infinity` 的渐近式，
也没有断言两个拆分部分分别存在高度极限；全局 QCT/Poisson 重组、主项渐近和
核心 Möbius 色散等输入仍须继续形式化。

有限高度 Mellin 权现有一个与正整数产品权精确一致的正实变量延拓：
先证明对复对数变量的全纯性，再限制到正实变量，得到 C∞ 正则性。
积分号下求导的支配界由紧集上的连续性构造，没有额外的支配假设。
这只证明固定参数的正则性，没有提供对 `T,V` 一致的导数或 Fourier 尾项界。

在此基础上，已构造真实 progression 物理核，保留两侧 Möbius 系数、
因子 `2`、两个平方根幅度、完整对数相位、Mellin 权及 `W(t/T)`。
它在 `x>0`、`delta+x*r>0` 的精确区域内光滑，并在 admissible progression
的整数点上等于原 AFE 求和项。对闭支撑包含在该区域内的 C∞ 截断 `chi`，
截断后的真实核 `K` 是 Schwartz 函数，已证明固定参数的公式

\[
\sum_{n\in\mathbb Z}K(a+sn)
=s^{-1}\sum_{h\in\mathbb Z}\widehat K(h/s)e(ha/s),\qquad s>0.
\]

取 `s=e/gcd(d,e)`、`a=-delta*rbar` 后，得到确切的
`s^(-1)*Khat(h/s)*e(-h*delta*rbar/s)`；没有排除 `s=1`，也没有要求
`gcd(delta,s)=1`。这不是实际 moment 的全局 Poisson 分解：仍须把正整数
progression 级数重编号到这个双向格点和，并构造、聚合实际 dyadic 截断。

## Machine-checked in this PR

The following steps now have kernel-checked Lean proofs with no project axiom,
`sorry`, or `admit`:

| analytic step | Lean theorem |
|---|---|
| correct C-infinity test-weight class, with nonzero compact bump regression | `CubicTestWeight.smooth`; `MWKFCubicActualMomentContract.lean` |
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
| exposed strip constant and a single horizontal-edge constant selected before all physical times | `norm_cubicAFECompletedIntegrand_horizontal_le_of_strip_bound`, `exists_norm_cubicAFECompletedIntegrand_horizontal_le_uniform` |
| vanishing of the horizontal edge and exact infinite-height vertical-line contour limit | `tendsto_cubicAFECompletedIntegrand_horizontalIntegral`, `tendsto_cubicAFECompletedIntegrand_verticalIntegral` |
| critical-line conjugation, nonvanishing fixed gamma product, and exact conversion from the completed product to `normSq zeta` | `one_sub_cubicCriticalPoint_eq_conj`, `cubicAFEGammaProduct_zero_ne`, `completedRiemannZeta_product_eq_gamma_mul_normSq` |
| absolute summability of the physical `(m,n)` Dirichlet family for `re z > 1/2` | `summable_norm_cubicAFEDirichletTerm` |
| exact completed-zeta double Dirichlet expansion and its pointwise normalized AFE-integrand form | `completedRiemannZeta_shifted_product_eq_tsum`, `cubicAFECompletedIntegrand_div_gamma_eq_tsum` |
| continuity of the full physical AFE scalar and invariance of each Dirichlet-term norm along a vertical line | `continuous_cubicAFEScalar_vertical`, `norm_cubicAFEDirichletTerm_vertical_eq` |
| exact finite-height interchange of the double Dirichlet series and vertical integral by dominated convergence | `hasSum_intervalIntegral_cubicAFENormalizedDirichletTerm` |
| kernel-checked finite-height AFE whose normalized double sum converges to `normSq zeta(1/2+it)` | `cubicAFEDoubleSumFinite_eq`, `tendsto_two_mul_cubicAFEDoubleSumFinite` |
| exact finite-height error with its sign, factor `pi`, and fixed gamma product | `two_mul_cubicAFEDoubleSumFinite_sub_normSq_eq` |
| exact factorization of each shifted Dirichlet term into its critical-line coefficient and an `(mn)^(-z)` monomial | `cubicAFEDirichletTerm_eq_zero_mul_product` |
| explicit `1/sqrt(mn)` amplitude and `exp(it(log n-log m))` phase | `cubicAFEDirichletTerm_zero_eq_exp` |
| finite-height AFE written with a Mellin weight depending on the two indices only through their product | `cubicAFEWeightFinite_eq_arithmetic_mul_productWeight`, `cubicAFEDoubleSumFinite_eq_arithmetic` |
| exact combined AFE--mollifier phase as `log((p.2+1)e)-log((p.1+1)d)` | `cubicAFECombinedLogPhase_eq_log_products`, `cubicAFECombinedArithmeticFactor_eq_exp` |
| exact structural diagonal `(p.2+1)e=(p.1+1)d`, on which the complete oscillatory factor is one | `cubicAFECombinedLogPhase_eq_zero_of_diagonal`, `cubicAFECombinedArithmeticFactor_eq_on_diagonal` |
| pointwise finite-height mollified AFE limit, without an unproved limit--integral interchange | `tendsto_cubicAFEMollifiedApproximation` |
| exact finite `(d,e)` reassembly of the finite-height mollified AFE | `cubicAFEMollifiedApproximation_eq_pairSum` |
| absolute summability of the finite-height AFE weights and every combined `(p,d,e)` family | `summable_cubicAFEWeightFinite`, `summable_cubicAFECombinedSummandFinite` |
| exact expansion of each ordered mollifier pair into the full combined `p`-sum | `cubicAFEMollifierPairApproximation_eq_tsum` |
| complete finite-height representation as `sum_d sum_e tsum_p` | `cubicAFEMollifiedApproximation_eq_tripleSum` |
| itemwise full amplitude/phase and phase-free exact diagonal | `cubicAFECombinedSummandFinite_eq_exp`, `cubicAFECombinedSummandFinite_eq_on_diagonal` |
| finite-height full-line moment and exact compact physical support | `cubicAFEMollifiedMomentFinite`, `cubicAFEMollifiedApproximation_eq_zero_of_not_mem`, `hasCompactSupport_cubicAFEMollifiedApproximation` |
| joint time/vertical continuity of the normalized integrand and time continuity/integrability of the finite-height mollified AFE | `continuous_cubicAFENormalizedVerticalIntegrand`, `continuous_cubicAFEDoubleSumFinite_time`, `continuous_cubicAFEMollifiedApproximation`, `integrable_cubicAFEMollifiedApproximation` |
| exact mollified horizontal-edge error with gamma factors, both mollifier factors and physical test weight retained | `cubicAFEMollifiedApproximation_sub_eq` |
| constructed integrable envelope `F(t) V^6 exp(-V^2)` for every `V >= 1` | `exists_integrable_cubicAFE_error_envelope` |
| unconditional finite-height AFE limit under the literal full-line mollified integral, at fixed nonzero `T` | `tendsto_cubicAFEMollifiedMomentFinite` |
| joint scalar/Dirichlet continuity in time and vertical coordinate | `continuous_cubicAFEScalar_joint`, `continuous_cubicAFENormalizedDirichletTerm_joint` |
| time-independent summable Dirichlet envelope for the finite-height weight | `norm_cubicAFEDirichletTerm_time_vertical_eq`, `norm_cubicAFEWeightFinite_le_envelope` |
| actual physical time-integral/series interchange with a continuous compact multiplier | `hasSum_integral_cubicAFEWeightFinite_mul` |
| exact outer multiplier and physical integral interchange for each ordered Möbius pair | `cubicAFECombinedSummandFinite_eq_outerWeight`, `hasSum_integral_cubicAFECombinedSummandFinite` |
| full finite-height `sum_d sum_e tsum_p integral_t` representation and its recombined height limit | `cubicAFEMollifiedMomentFinite_eq_tripleIntegral`, `tendsto_cubicAFETripleIntegral` |
| correctly oriented gcd diagonal ray with positive indices `m=(k+1)e/q`, `n=(k+1)d/q` | `cubicAFEDiagonalRay_succ`, `cubicAFEDiagonalRay_injective`, `cubicAFEDiagonalRay_surjective` |
| bijective diagonal series reindexing, explicit index product, and phase-free full integrand | `tsum_cubicAFEDiagonal_eq_ray`, `cubicAFEPositiveIndexProduct_diagonalRay`, `cubicAFECombinedSummandFinite_diagonalRay` |
| summability of both integrated subseries and exact split of the actual finite-height moment | `summable_integral_cubicAFE_diagonal_and_offDiagonal`, `cubicAFEMollifiedMomentFinite_eq_diagonal_add_offDiagonal` |
| integrated diagonal ray formula and height limit for the recombined diagonal/off-diagonal expression only | `cubicAFEDiagonalMomentFinite_eq_ray`, `tendsto_cubicAFEDiagonal_add_offDiagonal` |
| signed reduced shift `delta=n*s-m*r`, raw shift equal to `q*delta`, and exact zero-fiber criterion | `cubicAFEReducedShift`, `gcd_mul_cubicAFEReducedShift`, `cubicAFEReducedShift_zero_iff` |
| complete logarithmic phase and positivity of its argument, including negative shifts | `cubicAFECombinedLogPhase_eq_reducedShift`, `cubicAFEReducedShift_logArgument_pos` |
| complete physical integrand in reduced-shift coordinates | `cubicAFECombinedSummandFinite_eq_reducedShift` |
| disjoint-union equivalence and summable regrouping over all nonzero signed shifts | `cubicAFEShiftEquiv`, `hasSum_cubicAFE_shiftFibers`, `hasSum_integral_cubicAFE_shiftFibers` |
| actual integrated off-diagonal equals the full shifted-divisor expression; recombined height limit | `cubicAFEOffDiagonalMomentFinite_eq_shifted`, `cubicAFEMollifiedMomentFinite_eq_diagonal_add_shifted`, `tendsto_cubicAFEDiagonal_add_shifted` |
| positive single-variable progression, with positive numerator and exact divisibility; explicit inverse residue `m=-delta*rbar (mod s)` | `cubicAFEProgression`, `cubicAFEProgression_mem_iff_modEq`, `cubicAFEProgression_mem_iff_residue` |
| exact reconstruction of both positive indices and equality with the real quotient | `cubicAFEProgressionPair_succ`, `cubicAFEProgressionPair_mem`, `cubicAFEProgressionPair_second_cast` |
| bijection between each shift fiber and its admissible single-variable progression | `cubicAFEShiftFiber_first_injective`, `cubicAFEProgressionEquiv`, `tsum_cubicAFEShiftFiber_eq_progression` |
| summability and exact reindexing of the actual integrated progression expression | `summable_integral_cubicAFE_progression`, `cubicAFEShiftedMomentFinite_eq_progression` |
| actual finite-height moment equals diagonal plus progression expression, and the recombined height limit | `cubicAFEMollifiedMomentFinite_eq_diagonal_add_progression`, `tendsto_cubicAFEDiagonal_add_progression` |
| entire logarithmic extension of the actual finite-height Mellin product weight, with constructed compact domination | `differentiable_cubicAFELogProductWeightFinite` |
| exact positive-integer restriction and smoothness on positive real products, for every finite height orientation | `cubicAFERealProductWeightFinite_natCast`, `contDiffOn_cubicAFERealProductWeightFinite` |
| exact real second index/product, open positive-index region and positivity of the full logarithm argument | `cubicAFEProgressionRealSecond`, `cubicAFEProgressionRealProduct_pos`, `isOpen_cubicAFEProgressionDomain`, `cubicAFEProgression_logArgument_pos` |
| actual full progression kernel agrees with the original discrete AFE summand and is C-infinity on its positive-index region | `cubicAFEProgressionPhysicalSummand_eq_discrete`, `contDiffOn_cubicAFEProgressionPhysicalSummand` |
| a smooth cutoff with closed support inside that region makes the actual kernel globally smooth, compactly supported, and Schwartz | `contDiff_cubicAFEProgressionCutoffSummand`, `hasCompactSupport_cubicAFEProgressionCutoffSummand`, `cubicAFEProgressionSchwartz` |
| the cutoff kernel still agrees with the full discrete summand at every admissible integer | `cubicAFEProgressionCutoffSummand_eq_discrete` |
| fixed-cutoff Poisson formula with exact scaling factor and inverse-residue negative phase | `cubicAFEProgressionCutoff_poisson`, `cubicAFEProgressionCutoff_poisson_inverseResidue` |
| continuity, compact support, and integrability of every ordered twisted term | `continuous_cubicTwistedIntegrand`, `hasCompactSupport_cubicTwistedIntegrand`, `integrable_cubicTwistedIntegrand` |
| exact finite sum--integral interchange into genuine twisted zeta moments | `cubicComplexMollifiedSecondMoment_eq_twisted_sum` |
| exact final `4/3` reassembly | `cubic_long_mollifier_asymptotic_of_exact_inputs` |
| final reassembly specialized to the literal integral | `cubic_actual_long_mollifier_asymptotic_of_exact_inputs` |

The axiom-audit modules report only Lean/Mathlib's standard foundational
axioms (`propext`, `Classical.choice`, and `Quot.sound`).

### C-infinity correction verification

The constructor regression and the explicit nonzero bump both failed against
the old `C^omega` field and passed after the correction. Fourteen source
modules were compiled in dependency order, including the entire affected
AFE/progression chain, the new real-product weight, and the final facade.
Twenty-eight contract/audit files were then checked in one Lean invocation
(their imports hoisted and deduplicated to avoid repeatedly loading Mathlib).
The final exit code was zero; all 72 printed axiom reports contained only the
three standard foundations above. The nonzero bump theorem is audited too.
No local physical smoothness hypothesis, project axiom, or enlarged heartbeat
limit was inserted to obtain these results. This is a targeted verification,
not a full cold build of unrelated project modules.

### Physical-kernel and cutoff-Poisson verification

Both new source modules were compiled to proof objects. Thirty-two
contract/audit files (including the earlier C-infinity/nonzero-weight
regressions) were checked in a single import-deduplicated Lean invocation;
its final exit code was zero, with no error or warning diagnostics. All 86
axiom reports contained only the standard foundations. The tests include
negative shifts, the zero-index and zero-numerator boundaries, modulus one,
the noninteger real quotient `n(3/2)=7/10` for `(d,e,delta)=(6,10,-1)`, and an
explicit nonzero cutoff with its closed support in the positive-index region.
Typed contracts retain both the `1/s` factor and negative inverse-residue
phase. The new cutoff does not supply any hypothesis asserting smoothness,
summability, or a spectral bound for the physical kernel itself.

## Remaining formalization boundary

This PR does **not** yet make the analytic theorem unconditional inside Lean.
The left side is now the literal full-line integral, rather than an arbitrary
function `I`, and its two finite mollifier factors have been expanded and
interchanged with the integral.  The completed AFE contour has also been taken
to infinite height using an explicit physical horizontal-edge majorant.  At
each finite height the time-integral/arithmetic-series interchange is proved,
and the integrated expression is split into two summable diagonal/off-diagonal
subseries.  The diagonal ray is reindexed bijectively.  The off-diagonal is
regrouped over every nonzero signed shift using a disjoint-union equivalence;
the shift fibers and the resulting outer shift series are summable at each
finite height.  Each shift fiber has now been reindexed as a single positive
integer variable in the explicit inverse residue class, with the exact
positivity cutoff and real quotient identity.  The full physical kernel and
logarithmic phase are retained. The real extension of the complete progression
kernel and its local smoothness have now been proved. For every C-infinity
cutoff with closed support inside the positive-index region, the actual
cutoff kernel is Schwartz; its fixed-parameter Poisson formula includes the
exact Jacobian and the negative inverse-residue phase. The cutoff class has
an explicit nonzero bump regression. This is not yet the full Poisson
decomposition of the moment: the positive progression series still needs
to be identified with the bilateral residue lattice sum, the actual dyadic
cutoffs constructed and summed, and the physical time-integral interchanges
justified. Neither compactness in the logarithmic-extension proof nor the
Schwartz construction supplies uniform seminorm estimates in the varying
physical parameters.
The height limit remains
outside the recombined expression; separate limits and moving this limit
through either infinite subseries have not been proved.  What remains is to
carry the actual expression through the QCT/Poisson decomposition with all
needed convergence arguments, prove the reciprocal-LCM main-term asymptotic
and every analytic tail estimate, and especially prove the cubic MRSTT Mobius
decorrelation theorem.  The final facade therefore keeps
`hexact`, `hmain`, and `hrem` as theorem hypotheses.  They are local binders,
not global axioms.

Consequently the accurate status is:

- internal paper proof candidate and executable parameter audit;
- kernel-checked structural/reassembly, finite-height series/integral
  interchange, diagonal split/reindexing, signed-shift/progression regrouping,
  fixed-`T` recombined AFE integral limits, actual local physical-kernel
  regularity and the fixed-cutoff Poisson identity;
- full end-to-end Lean formalization still requires formalizing the named
  analytic inputs, including the external MRSTT theorem.
