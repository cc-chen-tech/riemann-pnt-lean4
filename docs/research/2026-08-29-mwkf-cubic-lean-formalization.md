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
也没有断言两个拆分部分分别存在高度极限；频率逐项的 QCT 重组、主项渐近和
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
`gcd(delta,s)=1`。现在已把原正整数 shift-fiber 级数严格连接到该双向格点和：
显式整数坐标及其逆映射覆盖每个非零项；截断支撑条件证明所有非正指标项为零，
没有靠 `toNat` 舍去有贡献的项。因此局部公式的左端已是原 AFE 求和项乘上
真实截断。

现在还已构造两个真实正指标的 dyadic 分解。记 `H=Real.smoothTransition`，取

\[
\phi_j(x)=H(2-x/2^j)-H(2-2x/2^j),\qquad j\ge0.
\]

已证明 `phi_j` 为 C∞、非负、至多为 1，闭支撑包含于
`[2^j/2,2*2^j]`；有限尺度和保留下边界项 `H(2-2x)`，当 `x>=1` 时
全尺度和严格为 1。实际截断为
`chi_(j,k)(x)=phi_j(x)*phi_k((delta+x*r)/s)`，其闭支撑位于两个指标均正的区域内，
不是从任意 cutoff 接口假设存在。原整数 progression 上的双尺度总权为 1。
此 partition 并非在每个正实点上都等于 1：小于 1 的连续指标区间仍有下边界权，
后续 Fourier 零模计算必须保留它。`x=1/4` 的有限尺度和为零的回归专门检查这一点。
先由此证明整数指标与 dyadic 指标的联合绝对可和性，再交换这两个求和，得到
每个原 shifted fiber 的点态 dyadic Poisson 表达。它保留完整物理核及相位，
次序明确为 `sum_(j,k) (1/s)*sum_h ...`；没有交换跨 box 的频率和，
也没有声称由此得到参数一致的 Fourier 尾项估计。
对真实物理时间积分后的 progression 级数，同样已证明 dyadic 重组及外层
box 级数绝对可和：截断独立于 `t`，可逐项提出积分，再使用原积分级数的
已证可和性。这不等于已证明 `integral_t` 与 Fourier 频率和之间的换序。

每个 box 的原整数级数现已进一步化为一个对所有时间共同有效的有限和：
索引集合保留原 progression 条件，并满足 `m<=2*2^j`，其外的截断严格为零。
原完整 AFE 单项的时间可积性也已证明，因此可用有限和积分定理交换
原格点和与物理时间积分。结合局部 Poisson，已得到真实积分 box 的等式及可积性。
再保留实际 `floor(T^3)` mollifier 支撑与所有正、负非零 shift，得到

\[
 I^{(V)}_{T,W}=D^{(V)}_{T,W}+P^{(V)}_{T,W},\qquad
 \lim_{V\to\infty}\bigl(D^{(V)}_{T,W}+P^{(V)}_{T,W}\bigr)=I_{\lfloor T^3\rfloor,W}(T).
\]

这里 `I^(V)`、`D^(V)` 分别是原有限高度 moment 与精确对角项，`P^(V)` 的嵌套
次序是 `sum_d sum_e sum_delta sum_(j,k) integral_t sum_h`，频率和保留在时间积分内。
Lean 定理使用原实 moment 的复数嵌入。已经证明每个 shift 的积分 box 级数可和，
以及保持该嵌套次序的外层 shift 级数可和；没有宣称所有指标可任意交换。
高度极限仅在重组整体之外，仍未证明对角和非对角分别存在高度极限。

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
| explicit integer lattice and inverse, including negative coordinates, non-unit shifts and modulus one | `cubicAFEProgressionLattice_injective`, `cubicAFEProgressionLattice_index`, `cubicAFEProgressionLattice_toNat_mem` |
| forbidden-domain terms vanish; exact positive-progression to bilateral-lattice reindexing without a postulated bijection | `cubicAFEProgressionCutoffSummand_eq_zero_of_not_domain`, `tsum_cubicAFEProgressionCutoff_eq_lattice` |
| end-to-end local Poisson formula starting from the original complete shifted-fiber summand | `cubicAFEShiftFiberCutoff_poisson` |
| explicit nonnegative smooth dyadic windows, precise support scales and finite telescoping with lower boundary retained | `cubicAFEDyadicWindow`, `tsupport_cubicAFEDyadicWindow_subset`, `sum_cubicAFEDyadicWindow_range` |
| actual one- and two-index dyadic partitions sum to one at positive integer-sized inputs | `hasSum_cubicAFEDyadicWindow`, `hasSum_cubicAFEDyadicWindow_product`, `hasSum_cubicAFEProgressionDyadicCutoff` |
| constructed progression cutoff and exact second-index scales/restriction, including negative shifts | `cubicAFEProgressionDyadicCutoff`, `cubicAFEProgressionDyadicCutoff_eq_discrete`, `cubicAFEProgressionDyadicCutoff_scales` |
| joint absolute summability precedes dyadic/integer reordering | `summable_cubicAFEProgression_dyadic_weighted`, `tsum_cubicAFEProgression_eq_dyadic` |
| actual shifted fiber equals its dyadic Poisson series, with an absolutely summable outer box series | `cubicAFEShiftFiber_eq_dyadicPoisson`, `summable_cubicAFEDyadicPoissonTerm` |
| exact dyadic reassembly of the literal time-integrated progression, with a summable outer box series | `cubicAFEProgressionIntegral_eq_dyadic`, `summable_cubicAFEProgressionDyadicIntegral` |
| exact finite set of contributing progression integers, uniformly for physical time | `cubicAFEProgressionDyadicIndices`, `cubicAFEProgressionDyadicCutoff_zero_of_not_mem_indices`, `tsum_cubicAFEDyadicProgression_eq_finsetSum` |
| actual individual AFE summand is time-integrable; finite-support time/lattice interchange | `integrable_cubicAFECombinedSummandFinite`, `integral_tsum_cubicAFEDyadicProgression` |
| whole physical Poisson box is time-integrable and equals the integrated original box | `integrable_cubicAFEDyadicPoissonTerm`, `integral_cubicAFEDyadicPoissonTerm_eq` |
| original integrated progression equals the sum of actual integrated Poisson boxes, with the stated nested summability | `cubicAFEProgressionIntegral_eq_dyadicPoisson`, `summable_integral_cubicAFEDyadicPoissonTerm`, `summable_shift_integral_cubicAFEDyadicPoissonTerm` |
| literal finite mollifier support and all nonzero signed shifts give the exact finite-height Poisson moment | `cubicAFEDyadicPoissonMomentFinite`, `cubicAFEProgressionMomentFinite_eq_dyadicPoisson`, `cubicAFEMollifiedMomentFinite_eq_diagonal_add_dyadicPoisson` |
| height limit of the recombined diagonal plus actual integrated Poisson moment only | `tendsto_cubicAFEDiagonal_add_dyadicPoisson` |
| joint time/log-product continuity of the actual finite-height Mellin integral | `continuous_cubicAFELogProductWeightFinite_joint`, `continuousOn_cubicAFERealProductWeightFinite_joint` |
| actual physical kernel jointly continuous on its exact positive-index region | `continuousOn_cubicAFEProgressionPhysicalSummand_joint` |
| global joint continuity and joint compact support of the actual cutoff kernel | `continuous_cubicAFEProgressionCutoffSummand_joint`, `hasCompactSupport_cubicAFEProgressionCutoffSummand_joint` |
| actual product-space integrability and time/Fourier interchange at each real frequency | `integrable_cubicAFEProgressionCutoffFourier_joint`, `integral_fourier_cubicAFEProgressionCutoffSummand` |
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

### Original-series to lattice verification

`MWKFCubicAFEProgressionPoisson.lean` compiled successfully to a proof object.
Thirty-four contract/audit files were checked in one import-deduplicated
Lean invocation, with final exit code zero and no error or warning diagnostics.
All 92 printed axiom reports used only the three standard foundations.
The new contracts test exact lattice coordinates and their inverses, negative
coordinates representing positive terms, non-unit shifts, modulus one, and
both forbidden-index cases. The full typed local formula starts with the
original AFE summand, not an unrelated real-variable function. Explicit
Euclidean-algorithm proofs check the chosen Bezout representatives: for
`(r,s)=(1,1)` Mathlib uses `gcdA=1`, although the residue class is also zero
modulo one. Ordinary `decide` was insufficient to unfold this recursive
algorithm; no `native_decide` was used.

The focused Python suite passed all 295 tests (14.87 seconds); the deterministic
coverage report exited successfully. Its `residual_top_level_gates=0` and
`unconditional asymptotic proved` labels remain internal executable-audit
claims, not a proof of the final Lean facade's analytic hypotheses.

### Actual dyadic construction and reassembly verification

Both `MWKFCubicAFEDyadicCutoff.lean` and `MWKFCubicAFEDyadicReassembly.lean`
compiled to proof objects. Thirty-eight contract/audit files were checked in
one import-deduplicated Lean invocation, with final exit code zero and no
error or warning diagnostics. All 110 printed axiom reports used only the
three standard foundations. The red-stage checks failed on the absent
construction/reassembly theorems before their implementation; the subsequent
full run checked the literal window values, both support endpoints, negative
and zero inputs, the retained lower-boundary term, and a negative-shift
fixture with exact second index `n(4)=2` for `(d,e,delta)=(6,10,-2)`.
Typed contracts expose the joint summability conclusion, full Poisson phase,
the nesting order of the box/frequency sums, and the actual time-integrated
dyadic identity without postulated partition or interchange hypotheses.

The product-series proof initially caused excessive definitional unfolding
while inferring the functions in `HasSum.mul`. Explicitly specifying the
two index functions resolved it. No heartbeat limit was increased; temporary
diagnostics were removed. The focused Python suite passed all 295 tests
(16.19 seconds), and deterministic coverage exited successfully. As above,
its proof-status label is not evidence that the remaining Lean analytic
inputs have been supplied. This remains targeted local verification, not
remote CI or independent expert review.

### Physical-time Poisson and full finite-height moment verification

`MWKFCubicAFEDyadicTimeIntegral.lean` and `MWKFCubicAFEDyadicMoment.lean`
compiled to proof objects. Forty-two contract/audit files were then checked
in one import-deduplicated Lean invocation. The final exit code was zero,
with no error or warning diagnostics; all 123 printed axiom reports used
only the three standard foundations. The red-stage contracts failed on the
missing finite-support/time-integral and full-moment theorems before their
implementation. The final tests include admissible and inadmissible integer
support points, a forbidden second index for a negative shift, the full
time/lattice interchange type, literal finite mollifier support and all
signed nonzero shifts, and the height limit of the recombined expression.
Neither a uniform Fourier majorant nor independent limits of the two pieces
are accepted as theorem hypotheses.

The focused Python suite passed all 295 tests (14.75 seconds), and the
deterministic coverage report exited successfully. Its internal proof-status
label still does not prove the remaining Lean analytic inputs. No project
axiom, placeholder, native evaluation axiom, or raised heartbeat limit was
introduced. These are local checks, not remote CI or external peer review.

## 真实物理核的逐频率时间积分

本批次补的是逐个 Fourier 频率的 Fubini，不是无穷频率级数的
时间积分换序。令 `K(t,x)` 为已有的完整 cutoff progression 核：
其中保留两侧 mollifier 系数、平方根振幅、完整 logarithmic phase、
有限高度 Mellin 权和 `W(t/T)`，没有替换为抽象平滑函数。

`MWKFCubicAFEJointKernel.lean` 从真实有限竖直积分证明 Mellin 权对
`(t,z)` 的联合连续性，再沿正实乘积变量取 logarithm，得到物理核在
正指标区域内的联合连续性。cutoff 的闭支撑位于该开区域；在闭支撑外
cutoff 局部恒零，因此完整 cutoff 核在整个 `ℝ × ℝ` 上连续。
其联合支撑包含于两个紧集的积：`W(t/T)` 的时间支撑与 cutoff 的
空间支撑。这里要求 `T ≠ 0`，不假设任何未证明的联合正则性或可积性。

`MWKFCubicAFEFourierTimeIntegral.lean` 因而得到每个实频率 `ξ` 的实际
乘积空间可积性以及

\[
\int_{\mathbb R}\widehat{K(t,\cdot)}(\xi)\,dt
=\widehat{\left(x\mapsto\int_{\mathbb R}K(t,x)\,dt\right)}(\xi).
\]

Fourier character 精确为 `exp(-2π i x ξ)`。结论包括 `ξ=0`、负 shift
和模数一；不对 shift 添互素条件。所有结论目前是固定物理参数的局部
结论：紧支撑本身不提供随参数统一的 seminorm，也不许可把 `∑_h` 移到
时间积分外，更不许可把高度极限移过任何子级数。

### 本批次验证

两个新源模块均成功编译并生成 proof objects。合计 46 个
contract/axiom-audit 文件在同一次 Lean 调用中核验（只对 import 提前去重，
正文不变），退出码 0，无 error/warning；130 条公理报告只包含
`propext`、`Classical.choice`、`Quot.sound`。实现前的两份 red-stage 合约
分别因缺少联合正则性定理及逐频率 Fubini 定理而失败；实现后的完整类型
合约不接受抽象可积性输入，且包含零频率、负 shift、模数一的特化。

联合连续性证明的首次 elaboration 遇到复合映射类型推断超时，显式指定
内层映射后消除；未提高 heartbeat 限额。聚焦 Python 测试为
`295 passed`（15.04 秒），确定性 coverage 正常退出。coverage 的内部
`unconditional asymptotic proved` 标签仍不等同于最终 Lean 定理成立。
本批次无新增项目公理、占位证明或 native evaluation 公理。按照单代理
约束完成本地自审；这些记录不是外部专家审阅或远端 CI。

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
an explicit nonzero bump regression. The positive progression series has
also been identified with the bilateral residue lattice sum: the integer
index map is injective and its range contains every nonzero lattice term.
This yields the fixed-cutoff Poisson formula for the original shifted-fiber
summand itself. The dyadic cutoffs on both actual positive indices have now
also been constructed and summed. Their nonnegative mass-one property proves
joint absolute convergence with the original progression index, permitting
the dyadic/integer reordering. The resulting pointwise Poisson expression
sums dyadic boxes on the outside and frequencies on the inside. The same
dyadic/integer reordering is proved for the actual time-integrated progression,
using the cutoff's time independence and the previously established
summability of the integrated original series. This is not
yet a frequency-by-frequency time-integrated QCT expression: using finite
integer support, the original lattice sum has now been interchanged with
time integration and the complete finite-height moment reassembled as its
exact diagonal plus integrated Poisson boxes. The nesting order is explicitly
`(d,e), delta, (j,k), integral_t, h`. Each individual Fourier transform now
commutes with the actual time integral, by joint continuity and compact
support of the actual kernel. Interchanging the **infinite** frequency series
with the time integral, any required cross-index reorderings and parameter-uniform
tail estimates remain to be established. Neither compactness in the logarithmic-extension proof nor the
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
  regularity, actual two-index dyadic partition, absolute integer/dyadic
  reassembly both pointwise and after the physical time integral, finite
  lattice/time interchange, the full finite-height diagonal-plus-integrated
  dyadic-Poisson moment, its recombined height limit, joint time/space kernel
  regularity and fixed-frequency physical-time/Fourier interchange;
- full end-to-end Lean formalization still requires formalizing the named
  analytic inputs, including the external MRSTT theorem.
