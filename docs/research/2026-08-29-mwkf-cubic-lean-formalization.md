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

最新一批已进一步证明实际核的联合 C∞ 性质，进而证明时间积分后的实际核
仍是 Schwartz。对这个核应用 Poisson，再连接原有限格点积分恒等式，
已将每个实际 box 的频率和移到时间积分外。新的完整有限高度表达式
`cubicAFEFrequencyMomentFinite` 保留次序
`sum_d sum_e sum_delta sum_(j,k) sum_h integral_t`；其与旧完整表达式相等，
且重组整体的高度极限也已连接回真实 moment。没有据此交换跨 box 的频率和，
也没有取得随 T 一致的 Fourier 尾项估计。

现已进一步证明实际连续 AFE 权的幂衰减、双边界物理核在时间/空间上的可积性，
以及所有整数 shift 的积分范数可和。由此可以合法地在无限 dyadic 箱和全部
非零 shift 上分别聚合零模与非零模，完整有限高度 moment 已写成
`(diagonal + zeroMode) + nonzeroMode`。这里的零模尚未求出渐近主项；
这一收敛证明也没有提供 `o(T)` 的 Möbius 消去或各部分的独立高度极限。

最新已证明实际对角项的有限高度 Mellin 公式，其算术核精确为
`lcm(d,e)^(-1) * (r*s)^(-z) * zeta(1+2z)`，其中 `r=d/gcd(d,e)`、
`s=e/gcd(d,e)`，两个交换步骤均有实际
可和支配。零模尚不能直接套用原论文的无边界公式：原论文的 dyadic 尺度
遍历整数，而当前已证分解以非负指标起步。新增有限下尺度补全给出了准确的
连续边界修正及其格点消失性质；全时间／shift 层面的去截断极限仍须证明。

实际正实产品 Mellin 权现已另行完成无限高度收敛及跨越零点的换线。
对 `-1/2<a<0<b`，严格得到 `V_b(t,P)=1+V_a(t,P)`，而不是把两个
不同积分线的权直接相等。由此取得零端点界 `|V_b|<=1+C_(t,a)*P^(-a)`。
这里证明的是固定 `t`、固定产品 `P>0` 的实际权；尚未交换完整物理
双重积分、所有 shift、下尺度深度与高度极限，也未获得随 T 一致的误差。
随后已证明实际完整产品权的加权 L1 性质，并通过保留 Jacobian 的变量
代换接回真实物理核。对固定时间和固定非零 shift，完成权乘上无限高度
物理核的空间积分现在确实趋于未截断域积分；不是仅有逐点趋于1。
尚未证明空间积分与高度极限交换，也未跨时间或全部 shift 聚合该结论。

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
| smoothness preserved by finite-interval integration and jointly compactly supported full-line integration | `contDiff_intervalIntegral_joint`, `contDiff_integral_joint_compactSupport` |
| actual scalar/Mellin/physical kernel jointly C-infinity, without abstract regularity hypotheses | `contDiff_cubicAFEScalar_joint`, `contDiff_cubicAFELogProductWeightFinite_joint`, `contDiffOn_cubicAFEProgressionPhysicalSummand_joint`, `contDiff_cubicAFEProgressionCutoffSummand_joint` |
| literal time-integrated kernel is smooth, compactly supported and Schwartz | `contDiff_integral_cubicAFEProgressionCutoffSummand`, `hasCompactSupport_integral_cubicAFEProgressionCutoffSummand`, `cubicAFEIntegratedProgressionSchwartz` |
| integrated actual progression Poisson, and frequency sum outside time integral in each actual box | `cubicAFEIntegratedProgression_poisson`, `integral_cubicAFEDyadicPoissonTerm_eq_frequencySum` |
| complete finite-height moment with frequency-before-time nesting and recombined height limit | `cubicAFEMollifiedMomentFinite_eq_diagonal_add_frequency`, `tendsto_cubicAFEDiagonal_add_frequency` |
| summability of whole frequency boxes and the outer signed-shift series in the stated nesting | `summable_cubicAFEFrequencyBoxFinite`, `summable_shift_cubicAFEFrequencyBoxFinite` |
| absolute convergence of each actual integrated Fourier coefficient series, including the full unit-modulus phase | `summable_norm_cubicAFEFrequencyCoefficient`, `summable_cubicAFEFrequencyCoefficient` |
| exact zero/nonzero frequency split of each box and any finite box family | `cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero`, `sum_cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero` |
| zero frequency equals the full physical double integral, not the zero-shift summand | `cubicAFEFrequencyCoefficient_zero`, `cubicAFEZeroModeBoxFinite_eq_physicalIntegral`, `cubicAFEZeroModeBoxFinite_eq_integratedKernel` |
| exact all-real dyadic lower-boundary mass and pointwise absolute kernel reassembly | `hasSum_cubicAFEDyadicWindow_allReal`, `hasSum_cubicAFEProgressionDyadicCutoff_allReal`, `hasSum_cubicAFEProgressionDyadicKernel_allReal`, `hasSum_norm_cubicAFEProgressionDyadicKernel_allReal` |
| actual positive-real Mellin decay and full physical envelope | `norm_cubicAFERealProductWeightFinite_le_envelope`, `norm_cubicAFEProgressionPhysicalSummand_le_envelope` |
| joint integrability of the actual two-boundary kernel | `integrable_cubicAFEBoundaryPhysicalKernel` |
| integrated absolute dyadic convergence and infinite zero-mode reassembly | `summable_integral_norm_cubicAFEProgressionDyadicKernel`, `hasSum_cubicAFEZeroModeBoxFinite` |
| exact translation-uniform lattice power bound | `summable_cubicAFELatticePower`, `tsum_cubicAFELatticePower_le` |
| all integer shifts have summable physical norm integrals | `summable_integral_norm_cubicAFEBoundaryPhysicalKernel` |
| separate zero/nonzero aggregation over all nonzero shifts and dyadic boxes | `summable_shift_cubicAFEZeroModeBoxFinite`, `summable_shift_cubicAFENonzeroModeBoxFinite`, `tsum_shift_cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero` |
| full finite-height diagonal/zero/nonzero identity and recombined height limit | `cubicAFEMollifiedMomentFinite_eq_diagonal_zero_nonzero`, `tendsto_cubicAFEDiagonal_zero_nonzero` |
| exact reciprocal-LCM diagonal Mellin monomial and zeta series | `cubicAFEDiagonal_sqrt_normalization`, `cubicAFEDiagonalMellinMonomial_eq`, `hasSum_cubicAFEDiagonalMellinMonomial` |
| actual finite-height diagonal Mellin integral, with both interchanges proved | `hasSum_intervalIntegral_cubicAFEDiagonalMellin`, `cubicAFEDiagonalMomentFinite_eq_mellin` |
| finite lower-scale completion, exact integer invariance and physical boundary correction | `hasSum_cubicAFEDyadicCompletionWeight`, `eventually_cubicAFEDyadicCompletionWeight_eq_one`, `cubicAFEDyadicCompletionCorrection_eq_zero_on_progression`, `cubicAFEDyadicCompletionKernel_eq_boundary_add_correction` |
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

## 联合光滑核、每箱频率换序与完整有限高度重组

`MWKFCubicSmoothIntegral.lean` 先证明一个实际需要的解析工具：联合 C∞
函数在固定有限区间积分后仍为 C∞。证明对有限阶作归纳，每阶偏 Fréchet
导数在参数闭球与积分区间的紧积上有界，因此可合法积分号下求导。
完整实线的紧支撑情形由实际支撑投影产生积分区间。没有输入预设的
derivative majorant，也不要求积分上下限正向排列。

`MWKFCubicAFEJointSmooth.lean` 将其用于真实有限高度 Mellin 权：
Gamma 因子的倒数全纯性与非零性先给出真实 scalar 的联合光滑性。
完整物理核在正指标区域光滑，cutoff 的闭支撑条件给出全局联合光滑性。
再用上述工具和已证联合紧支撑，得到
`x ↦ ∫ t, cubicAFEProgressionCutoffSummand ... t x` 的 C∞ 性质。
这个函数在原空间 cutoff 支撑外恒零，所以本身就是 Schwartz；
`cubicAFEIntegratedProgressionSchwartz` 的求值与该实际积分定义相同。

`MWKFCubicAFEIntegratedPoisson.lean` 对该积分后的核应用精确缩放 Poisson。
通过实际 progression 与双向格点的重编号、原整数 box 的共同有限支撑，
以及前批逐频率 Fubini，证明

\[
\int_t \frac1s\sum_{h\in\mathbb Z}
 \widehat{K_t}(h/s)e(-h\delta\bar r/s)\,dt
=\frac1s\sum_{h\in\mathbb Z}
 \left(\int_t\widehat{K_t}(h/s)\,dt\right)e(-h\delta\bar r/s).
\]

这是每个实际 dyadic box 的等式，非抽象统一支配假设。
`MWKFCubicAFEFrequencyMoment.lean` 将其逐 box 接回完整有限高度 moment，
保留实际 mollifier 支撑、全部正负非零 shift、两侧 dyadic 指标和完整相位。
新的频率表达式在原嵌套下的 box 级数与外层 shift 级数可和。
重组整体在高度趋于无穷时仍返回真实 moment。

仍然没有声称跨 box/shift 的全部 Fourier 项联合绝对可和，没有把高度极限
移入任一子级数，没有证明随 T 一致的 seminorm 或尾项节省。它解除的是
每箱的时间/频率次序限制，不是最终 cubic 渐近式所需的色散估计。

### 本批次验证

四个新源模块均编译成功并生成 proof objects；54 个合约/公理审计文件
在同一次 import 去重的 Lean 调用中核验通过（退出码 0，无 error/warning）。
148 条公理报告仅含三个标准基础公理。实现前四组 red-stage 合约均在缺失
新定理处失败。最终测试包括乘积参数、反向有限区间、实际积分核的定义相等、
负 shift 与非互素模数、完整 (1/s) 和逆剩余相位、频率在时间积分之外的
完整字面表达式，以及仅对重组整体作高度极限。

首轮完整测试发现负整数 `-6` 从整数转复数与复数常量间需要显式 cast
化简；修正特化测试后重新跑完全部 54 文件。未修改数学假设以迎合测试。
聚焦 Python 测试为 `295 passed`（14.68 秒），确定性 coverage 退出码 0。
仍须将 coverage 的内部 `unconditional asymptotic proved` 标签与尚未闭合
的最终 Lean 定理严格区分。无新增项目公理、sorry、admit 或 native evaluation
公理，未提高 heartbeat 限额。本批为单代理本地核验，不是外部专家审阅或远端 CI。

## 绝对频率可和、零模拆分与连续下边界权

`MWKFCubicAFEFrequencySummability.lean` 使用实际积分后 Schwartz 核，
证明其 Fourier 变换经非零缩放后的整数采样可和。完整逆剩余相位的范数
精确为 1，因此实际频率系数的范数级数也可和；这不是仅有完整 box 的
外层可和性。所有结论仍是固定物理参数的结论。

`MWKFCubicAFEZeroMode.lean` 在上述绝对收敛成立后，严格拆成
`zeroModeBox + nonzeroModeBox`，后者包含所有正负非零频率。零模为

\[
 Z_{j,k}=s^{-1}\int_t\int_x
 \chi_{j,k}(x)K^{\rm phys}_{d,e,\delta}(t,x)\,dx\,dt.
\]

它保留 `t log(1+delta/(xr))`、两侧 Möbius 系数、平方根幅度、有限高度
Mellin 权和 `W(t/T)`。`h=0` 不等于 `delta=0`。Fubini 将它与空间积分
在外的实际积分核等式连接；任意有限 box 集合也可合法分别求和。

`MWKFCubicAFEDyadicBoundary.lean` 进一步将以前只在整数大小指标上证明的
质量1分解推广为全实轴上的精确公式。令

\[
 \beta(x)=1-H(2-2x),\qquad H=\operatorname{smoothTransition}.
\]

已证明 `0≤beta≤1`、`x≤1/2` 时为0、`x≥1` 时为1，以及对每个实数 x

\[
 \sum_{j\ge0}\phi_j(x)=\beta(x),\qquad
 \sum_{j,k\ge0}\chi_{j,k}(x)=\beta(x)\beta((\delta+rx)/s).
\]

对真实核的复值和及范数和都已证明对应 HasSum。因此零模的连续积分必须
保留两侧 beta 因子，不能误用整数格点上的质量1结论将它们删除。

在该检查点，下一步是证明实际积分后的支配，例如在固定 d,e,T,X,V 且 X>1/2 下
对所有非零 shift 的非负积分

\[
 \sum_{\delta\ne0}\int_t\int_x
 \beta(x)\beta((\delta+rx)/s)
 \lVert K^{\rm phys}_{d,e,\delta}(t,x)\rVert\,dx\,dt<\infty.
\]

该检查点没有把这条积分支配当作已证输入：逐点范数级数可和不自动说明
积分后的级数可和，也不自动许可跨无限多个 box 将零模和非零模分别求和。
即使固定参数收敛完成，最终主项渐近与 T-一致尾项/色散估计仍须另证。

### 本批次验证

三个新源模块均编译成功并生成 proof objects。60 个合约/公理审计文件
同次核验通过（仅 imports 提前去重），退出码 0，无 error/warning；
167 条公理报告只含标准三个基础公理。三组 red-stage 合约均先在目标定理
缺失处失败。回归包括负 dilation、负 shift、模数一、非互素 shift/modulus、
完整零模物理积分、下边界 `x=1/4,1/2,1,-3`，以及第一指标为4但第二指标
为1/4时总 dyadic 质量为0的实例。

零频率补集使用显式 subtype 等价重编号，未靠未经验证的类型转换。
乘积级数首次 elaboration 的诊断显示窗口定义被展开211692次；显式指定
两个求和函数后消除超时，未提高 heartbeat 限额，临时诊断已删除并复编译。
聚焦测试为 `295 passed`（14.90秒）；确定性 coverage 正常退出。其内部
`unconditional asymptotic proved` 标签仍不能替代最后三个解析输入的 Lean
证明。无新增项目公理、占位证明或 native evaluation 公理。本批为单代理
本地核验，不是远端 CI 或外部专家审阅。

## 实际积分支配与全部 dyadic/shift 的零模聚合

上述积分支配现在已在 Lean 中证明，不再是待供给的假设。
令 `a=X+1/2>1`，`P=x*y`，`y=(delta+r*x)/s`，以及

\[
 E_{X,V}(t)=\left|\frac1{2\pi}\right|
 \left|\int_{-V}^{V}|\mathrm{scalar}(t,X+iv)|\,dv\right|.
\]

`MWKFCubicAFEPhysicalDecay.lean` 从原有限竖直积分直接证明

\[
 |V^{(V)}_{t,X}(P)|\le E_{X,V}(t)P^{-X}\quad(P>0),\qquad
 |K^{\rm phys}_{d,e,\delta}(t,x)|\le C_{d,e,T,X,V}(t)P^{-a},
\]

其中 `C(t)` 是两侧实际 mollifier 系数的乘积范数、原因子2、
`(sqrt(d*e))^(-1)`、`E(t)` 和 `|W(t/T)|` 的乘积；完整对数相位的范数为1。
`C` 的时间可积性由实际连续性与 W 的紧支撑证明。允许任意有限实高度 V，
包括负 V；没有添加正高度假设，也没有预设抽象 majorant。

定义 `G_X(x)=1_(x>1/2) x^(-a)`，已证明 G 可积。
令 `F_delta(t,x)=beta(x) beta(y) K_phys(t,x)`。在固定 shift 下，

\[
 |F_\delta(t,x)|\le C(t)(1/2)^{-a}G_X(x).
\]

`MWKFCubicAFEZeroModeReassembly.lean` 先从真实 cutoff 核的有限和极限
证明 F 可测，再利用上述可积乘积支配证明联合可积性。随后对实际范数级数
应用支配收敛，得到

\[
 \sum_{j,k}\int_{\mathbb R^2}|\chi_{j,k}(x)K^{\rm phys}(t,x)|\,d(t,x)<\infty,
 \qquad
 \sum_{j,k}Z_{j,k}=s^{-1}\int_t\int_x F_\delta(t,x)\,dx\,dt.
\]

这一步已许可固定 shift 的无限零模/非零模拆分，不再只是有限箱拆分。

### 平移一致的格点界与外层 shift

`MWKFCubicAFELatticeDecay.lean` 对任意实平移 b、任意实 `s>=1` 证明

\[
 \sum_{\delta\in\mathbb Z}\beta((\delta+b)/s)((\delta+b)/s)^{-a}
 \le (1/(2s))^{-a}\sum_{n\in\mathbb Z}|n|^{-a}<\infty.
\]

右侧零项按 Lean 实幂约定为0（此处负指数不为0）。证明使用精确整数切点
`m=floor(s/2-b)`：`delta<=m` 时 beta 为0；`n=delta-m>=1` 时
`(delta+b)/s>=n/(2s)>0`。整数平移是显式双射，因此上界与 b 无关。
模数因子没有被隐去；这不是对参数一致的省幂估计。

`MWKFCubicAFEShiftReassembly.lean` 将它用于 `b=r*x`，证明

\[
 \sum_{\delta\in\mathbb Z}\int_t\int_x
 \beta(x)\beta((\delta+rx)/s)|K^{\rm phys}_{d,e,\delta}(t,x)|\,dx\,dt<\infty.
\]

代码先证明乘积空间积分范数的级数可和；各 shift 的已证联合可积性通过
Fubini 给出这里的迭代积分。原始已证 frequency-box 总和减去现在已证的
零模总和，给出非零模总和可和。因此可以在全部非零 shift 上拆成两条
独立可和的嵌套级数，保留 `1/s`、正负频率、全部 gcd 层及物理权。
没有声称所有 `(delta,j,k,h)` 的 Fourier 系数范数可以任意联合求和。

### 接回完整有限高度 moment

`MWKFCubicAFESeparatedMoment.lean` 使用实际 `floor(T^3)` 支撑，将上面的
全部箱/shift 结果逐对 `(d,e)` 聚合，证明

\[
 I^{(V)}_{T,W}=(D^{(V)}_{T,W}+Z^{(V)}_{T,W})+E^{(V)}_{T,W},\qquad
 \lim_{V\to\infty}((D^{(V)}+Z^{(V)})+E^{(V)})=I_{\lfloor T^3\rfloor,W}(T).
\]

这里 Z、E 分别是全部零模和非零模；只证明重组整体的高度极限。
尚未计算 `D+Z` 的共同 Mellin 主项，尚未给出 E 的 `o(T)` 界，
也没有把各部分的独立高度极限或 T-一致尾项作为已证结论。

### 本批验证与自审

五组回归合约均先在目标声明缺失处失败。五个实际源模块已逐一编译生成
proof objects。70 个合约/公理审计文件同次核验通过，退出码0；仅将 imports
提前去重，正文原样检查。为避免长日志截断，另外单独复跑35个公理审计文件，
完整取得190条报告，均仅含 `propext`、`Classical.choice`、`Quot.sound`。
聚焦测试 `295 passed`（14.57秒），确定性 coverage 退出码0。后者的
`unconditional asymptotic proved` 和 `residual_top_level_gates=0` 仍只是内部
脚本标签，不能替代最终 Lean 定理的三个缺失输入。没有新增项目公理、sorry、
admit、native_decide 或提高 heartbeat 限额；未运行无关的全量 Lean 冷构建。
自审重点是积分次序、实连续指标的两侧 beta 边界、`s>=1` 的真实 gcd 来源、
负 shift/负高度和 `s=1`，以及不把固定参数收敛解释为渐近消去。
本批仍是单代理本地核验，不是外部同行审阅。

## 对角 Mellin 公式与双向尺度接口

令 `q=gcd(d,e)`、`r=d/q`、`s=e/q`。新模块
`MWKFCubicAFEDiagonalMellinKernel.lean` 先从有限 gcd/LCM 等式证明

\[
 \sqrt{rs}\sqrt{de}=[d,e],\qquad
 \frac{((k+1)^2rs)^{-z}}{\sqrt{(k+1)^2rs}\sqrt{de}}
 =\frac{(rs)^{-z}}{[d,e]}(k+1)^{-1-2z}.
\]

对 `Re z>0`，正尺度级数绝对收敛并精确产生 `zeta(1+2z)`；没有把
零尺度或额外 Euler 因子带入归一化。`d=6,e=10,k=0,z=0` 的回归结果
为 `1/30`，另有模数1、首个正尺度为1的回归。

`MWKFCubicAFEDiagonalMellinIntegral.lean` 定义实际
`S_t(z)=cubicAFEScalar t z`，它已包含 `G_t(z)g_t(z)/z`，并证明

\[
 D^{(V)}_{T,W}=
 \sum_{d,e\le\lfloor T^3\rfloor}\int_t
 2a_N(d)a_N(e)W(t/T)\frac1{2\pi}
 \int_{-V}^{V} S_t(X+iv)
 \frac{(rs)^{-X-iv}}{[d,e]}\zeta(1+2X+2iv)\,dv\,dt.
\]

此处沿用完整 mollifier 有限支撑，`T!=0`、`X>1/2`，任意实有限高度 V。
竖直积分与正尺度级数的交换使用实际 monomial 范数在竖线上的不变性，
以及 scalar 的连续性；物理时间积分与对角尺度和的交换使用原 AFE
可和范数族的对角注入子族和实际紧支撑时间 envelope。二者都不是接口假设。
本式不是留数计算，也没有把 V 极限移入某个独立拆分部分。

### 必须区分的两种零模

原研究文档 `2026-08-24-mobius-weighted-off-diagonal.md` 的 (3.1) 使用
`j in Z` 的双向 dyadic partition，(4.5a) 因而使用完整正实域。当前 Lean
partition 的 `j,k in N` 在连续变量上的总权却是 `beta(x) beta(y)`。
两种 partition 在正整数样本上一致，**不意味着两个零模积分可直接等同**。
因此本次没有把论文 (4.5d) 当作当前零模的已证公式，也未将这一接口差异
描述成论文自身的代数错误。

`MWKFCubicAFEDyadicCompletion.lean` 为这项转换定义

\[
 B_J(x,y)=\beta(2^Jx)\beta(2^Jy),\qquad
 \sum_{j,k\ge0}\phi_j(2^Jx)\phi_k(2^Jy)=B_J(x,y).
\]

这是把尺度下限降到 `2^(-J)` 的精确有限补全。已证明：

- `B_0=beta(x) beta(y)`；
- `x,y>=1` 时每个 J 都有 `B_J=1`；
- 对固定正实 x,y，J 足够大后 `B_J=1`；
- 实际物理修正 `(B_J-B_0)K_phys` 在每个 admissible progression 整数点为0；
- `B_J K_phys=B_0 K_phys+(B_J-B_0)K_phys` 是精确物理核等式。

在 `x=1/4,y=5/4` 上，`B_0=0` 而 `B_2=1` 的 Lean 回归明确说明连续
权确实发生改变。补全不改原格点和，但其零模与非零模部分需要配对处理。
尚未证明补全后的 Poisson 子级数极限、该修正的积分大小或 `J→∞` 与
`V→∞`、Mellin 换线之间的交换。逐点最终等于1不等于积分支配。

### 本批核验

三个新源模块已逐一编译，三组 red-stage 合约先在缺失声明处失败。
76个合约/公理审计文件同次核验通过，退出码0。仅将 imports 提前去重；
Lean 实际检查全部正文，输出过滤器保留全部公理报告及诊断，避免冗长
`#check` 类型打印遮蔽结果。完整取得204条公理报告，全部仅依赖
`propext`、`Classical.choice`、`Quot.sound`，无 error/warning。
聚焦测试 `295 passed`（14.51秒）；确定性 coverage 退出码0。coverage
的 `unconditional asymptotic proved` 标签仍不是最终三个解析输入的 Lean
证明。`git diff --check`、占位符和最终 `hexact/hmain/hrem` 状态扫描完成。
没有新增项目公理、sorry、admit、native_decide，也未提高 heartbeat 限额。
使用独立临时 proof-object 目录，未启动无关全量 Lean 冷构建。
自审检查了原2因子、`1/(2pi)`、`1/lcm`、`1+2z`、负有限高度、实际
对角注入子族，以及“正整数权相同不推出连续零模相同”的接口边界。
这仍是单代理本地核验，不是外部专家审阅或远端 CI。

## 有限下尺度的真实 Poisson 配对与完整 moment

本批进一步闭合了上一节的**有限深度**尺度接口：新增下尺度的真实核、
Poisson 零／非零配对、修正积分和 dyadic 聚合均已写成 Lean 证明。
这不包含下端点去截断或共同 Mellin 换线，也不证明最终 `hmain/hrem`。

### 实际 cutoff 与全部变量范围

`MWKFCubicAFECompletedCutoff.lean` 构造

\[
 \chi_{J;j,k}(x)=\phi_j(2^Jx)\phi_k(2^Jy_\delta(x)),\qquad
 y_\delta(x)=\frac{\delta+rx}{s},\quad J,j,k\in\mathbb N.
\]

保留 `d,e>0`、`r=d/gcd(d,e)`、`s=e/gcd(d,e)`、任意整数 `delta`。
不附加 `delta>0`、`gcd(delta,s)=1` 或 `s>1`。
cutoff 的 C∞、紧支撑及正指标域支撑条件均从实际函数证明，闭支撑满足

\[
 \frac{2^j}{2\cdot2^J}\le x\le\frac{2\cdot2^j}{2^J},\qquad
 \frac{2^k}{2\cdot2^J}\le y_\delta(x)\le\frac{2\cdot2^k}{2^J}.
\]

原箱精确嵌入为 `chi_(J;J+j,J+k)=chi_(0;j,k)`。若 `j<J` 或 `k<J`，
新箱在每个 admissible 正整数 progression 点上为零，端点等号也包括在内。
但是其连续核不必为零；合约使用 `d=e=1,delta=0,J=2,j=k=0,x=1/4`
核对新 cutoff 为1、旧 cutoff 为0，防止把格点消失误写成物理积分消失。

### 每箱频率配对与有限边界范围

`MWKFCubicAFECompletedPoisson.lean` 定义完整实际频率系数

\[
 F_{J;j,k}(h)=\left(\int_{\mathbb R}
   \widehat{\chi_{J;j,k}K_t}(h/s)\,dt\right)
   e(-h\delta\bar r/s).
\]

这里 `K_t` 是已有完整物理核，包含原2因子、Möbius 系数、平方根幅度、
`t*log(1+delta/(x*r))`、有限高度 Mellin 权和 `W(t/T)`。对任意实 `V`、
`X>1/2`、`T≠0`，频率级数的绝对可和性来自实际 integrated Schwartz 核。
先证明可和性，再抽取 `h=0`，得到

\[
 Z_{J;j,k}=s^{-1}\int_t\int_x\chi_{J;j,k}(x)K_t(x),\qquad
 E_{J;j,k}=s^{-1}\sum_{h\ne0}F_{J;j,k}(h).
\]

每个新增下尺度箱满足精确等式 `Z_(J;j,k)+E_(J;j,k)=0`；未宣称两者各自为零。

`MWKFCubicAFECompletedBoundary.lean` 证明新增非零连续箱实际上有限。
令

\[
 B=|\delta|+r+s+1,\qquad 2^{J+1}B<2^L,
 \qquad F_{J,L}=\{(j,k)\in[0,L)^2:j<J\text{ 或 }k<J\}.
\]

每个新增非零 cutoff 的两个真实指标均至多为 `B`，所以它的两个尺度
指标都严格小于 `L`。此处 `L` 的存在由 `2^L→∞` 证明，范围外的 cutoff
在**所有实数点**上严格为零。该界依赖 `J,d,e,delta`，不是一致尾项估计。

### 修正积分与分别可和的 dyadic 模式

`MWKFCubicAFECompletedReassembly.lean` 将原修正核精确写成有限和：

\[
 (B_J(x,y_\delta(x))-B_0(x,y_\delta(x)))K_t(x)
   =\sum_{(j,k)\in F_{J,L}}\chi_{J;j,k}(x)K_t(x).
\]

每项实际联合核连续、紧支撑，故修正联合核可积；有限和积分及 Fubini
随后给出 `C_J=s^(-1)*integral_t integral_x correction=sum_F Z_J`。
原尺度的已证可和性加上有限边界修正，进一步给出两个独立 HasSum：

\[
 \sum_{j,k\ge0}Z_{J;j,k}=\sum_{j,k\ge0}Z_{0;j,k}+C_J,\qquad
 \sum_{j,k\ge0}E_{J;j,k}=\sum_{j,k\ge0}E_{0;j,k}-C_J.
\]

两式中的无限 dyadic 系列都已证明可和，没有依靠 Lean 对不可和 `tsum`
的默认值。这里的有限修正消去是 Poisson 恒等式，不是 Möbius 幂节省估计。

### 回到原始有限高度 moment

`MWKFCubicAFECompletedMoment.lean` 还证明 completed 物理核联合可积、
全部 completed 零模之和等于其 literal `B_J*K` 双重积分，并对完整的
`floor(T^3)` mollifier 支撑重组：

\[
 I^{(V)}_{T,W}=D^{(V)}_{T,W}
   +\sum_{d,e}\sum_{\delta\ne0}
       \left(\sum_{j,k}Z_{J;j,k}+\sum_{j,k}E_{J;j,k}\right).
\]

外层 shift 系列只在括号中的零／非零模式先配对后求和，其可和性已经证明。
本批没有单独把 completed 零模或非零模移到整个 shift 和之外。
任意函数 `J : real -> nat` 都可以作为有限高度 `V` 时的深度：
上式每个 `V` 都精确成立，所以**重组后**的 `V→∞` 极限仍为原始真实积分。
这不推出任何单独的 `J→∞` 或 `V→∞` 零模／非零模极限，不允许把
`B_J` 直接替换成1，也未消除共同 Mellin 的端点正则化义务。

### 本批核验与自审

五个新源模块逐一编译通过并生成 proof objects，共755行实际定义和证明。
五组 red-stage 合约先在缺失目标声明处失败；最终86个合约／公理审计文件
同次核验退出码0。仅将 imports 提前去重，Lean 检查全部正文；输出过滤器
完整保留公理报告和诊断。取得236条公理报告，均仅依赖 `propext`、
`Classical.choice`、`Quot.sound`，没有 error/warning。
合约覆盖完整真实修正积分、字面物理零模、深度随高度变化的重组极限、
负 shift、不互素 shift／modulus、下尺度上端点、`J=0` 空边界及非零连续箱。

聚焦 pytest：`295 passed`（14.66秒）；deterministic coverage 正常退出。
其 `unconditional asymptotic proved`／`residual_top_level_gates=0` 仍是内部
参数账本，不能替代最终 `hexact/hmain/hrem` 的 Lean 证明。
没有新增项目公理、sorry、admit、native_decide，也没有提高 heartbeat 限额。
使用独立临时 olean 目录，未启动无关的全量 Lean 冷构建。

单代理自审逐项核对：`1/s` 与负 inverse-residue phase、完整对数相位、
下尺度边界等号、原箱加J的精确重编号、新增盒的有限支撑、联合可积性、
有限和积分、两种模式各自的 dyadic 可和性，以及外层 shift 必须先配对的
括号位置。全目标的主要未完成项没有改变：端点／Mellin 极限、主项渐近、
参数一致尾项及 cubic Möbius 核心估计。这不是独立代理审阅、远端 CI 或
外部同行专家确认。

## 实际产品权的无限高度与零端点换线

有限高度右线估计 `|V^(V)_b(t,P)|<=C_(t,b)*P^(-b)` 不能单独支配
`P->0` 的连续零模。新证明直接处理 gamma-only scalar，未从已完成的
completed-zeta AFE 极限推断每个实产品权的极限。

### Gamma 竖条界与实际 scalar 的绝对可积性

`MathlibAux/GammaVerticalStripBound.lean` 从实际 Euler 积分证明
`|Gamma(z)|<=Gamma(Re z)`（`Re z>0`），再由两端 Mellin 支配取得正闭
竖条上的 Gamma 和 GammaR 一致上界。这里不假设 Stirling 公式或谱估计。

`MWKFCubicAFEScalarDecay.lean` 对原来的三个 pole-cancelling 因子逐一估计，
得到精确的高斯多项式 majorant

\[
 H_X(y)=(1+|X|+|y|)^6e^{-y^2},\qquad
 |G_t(X+iy)|\le125e^{X^2}H_X(y).
\]

对 `X>-1/2` 且 `X!=0`，证明实际 `cubicAFEScalar` 连续、被
`A_(t,X)*H_X` 支配且绝对可积。范围包括后续所需的负实部直线；常数
依赖固定 `t,X`。Gamma 分母不会被隐藏为 T 一致常数。

### 保留积分线的完整权与高度极限

`MWKFCubicAFEWeightLimit.lean` 定义

\[
 V_X(t,P)=\frac1{2\pi}\int_{\mathbb R}
   \operatorname{scalar}_t(X+iy)e^{-(X+iy)\log P}\,dy,
 \qquad
 C_{t,X}=\frac1{2\pi}\int_{\mathbb R}|\operatorname{scalar}_t(X+iy)|\,dy.
\]

对 `P>0`、`X>-1/2`、`X!=0`，这个积分绝对收敛，原有限高度实产品权
确实趋于它；有限高度的 envelope 至多为 `C_(t,X)`，包括反向区间 `V<0`。
因此有限高度和完整高度的右线权都有与高度无关的 `C_(t,X)*P^(-X)` 上界。
这仍是固定时间的界，不是关于 T 的统一主项或余项。

### 有限矩形、两条水平边与留数一

`MWKFCubicAFEWeightContour.lean` 对实际分子
`G_t(z)*GammaProduct_t(z)/GammaProduct_t(0)*exp(-z*log P)` 证明
`Re z>-1/2` 上全纯、在零点值为1。使用真实 divided difference 构造正则部，
在 `z!=0` 处严格拆成 `remainder+1/z`。当
`-1/2<x0<0<x1`、`y0<0<y1` 时，边界矩形积分严格为 `2*pi*i`；
没有越过 Gamma 极点，也未把分子误称为整个复平面上的整函数。

`MWKFCubicAFEWeightShift.lean` 以正闭竖条 Gamma 界及高斯衰减同时处理
顶部和底部，得到两条水平积分趋零。分别使用左右竖线的绝对收敛，再取
有限矩形公式的极限，证明

\[
 V_b(t,P)=1+V_a(t,P),\qquad
 |V_b(t,P)|\le1+C_{t,a}P^{-a}
 \quad(P>0,\ -1/2<a<0<b).
\]

所有 `i`、`2*pi` 和留数的正号均由 Lean 等式核对。取 `a=-1/4` 得到
零端点界 `1+C_(t,-1/4)*P^(1/4)`；这是实际权的界，而非接口假设。

### 这一步尚未推出什么

上述换线处理 gamma-only 产品权；它不是共同 Mellin 的
“对角 + 全部零 Poisson mode”公式，后者的 zeta 因子、shift 和、三角函数
修正及端点极限仍须逐项证明。新界也不自动允许把 `J->infinity` 或
`V->infinity` 移入整个双重积分或任一无限模式子级数，更不包含核心
cubic Möbius 的 `o(T)` 消去。最终 `hexact/hmain/hrem` 假设保持不变。
下一步的未截断物理核可积性必须保留 `delta!=0`：零 shift 时两个正指标
可以同时趋零，平方根幅度具有 `1/x` 型端点。此前允许 `delta=0` 的
紧支撑回归盒不能用来推断未截断核的全半轴可积性。

### 本批核验与自审

五个新源模块逐一编译通过，共600行定义与证明。五组新增合约均先确认
缺失目标声明时失败，再接入实际证明。最终核验扩展到全部108个 MWKF
contract/axiom-audit 文件，退出码0；缺失的旧 reciprocal-amplitude 对象
补编译后纳入本次核验，未删减该组测试。只提前去重 imports，Lean 检查
所有正文，输出保留完整公理报告及诊断。

306条公理报告仅含 `propext`、`Classical.choice`、`Quot.sound`，没有
error/warning。具体回归包括 `|Gamma(1+it)|<=1`、正负竖线的绝对可积性、
负竖线有限高度极限、留数一矩形、`a=-1/4,b=3/4` 的换线等式和精确
四分之一次幂界。最后一项曾捕获默认化简未处理 `-(-1/4)` 的类型不匹配，
用显式负号等式修正后重跑全部108个文件；目标不等式及假设未改动。

聚焦 pytest 为 `295 passed`（14.49秒），deterministic coverage 退出码0。
coverage 的 `unconditional asymptotic proved`／`residual_top_level_gates=0`
仍是内部脚本账本，不是最终渐近式的 Lean 证明。
新文件无项目公理、sorry、admit、native_decide，未提高 heartbeat 限额。
`git diff --check` 与 staged diff 检查通过；继续使用隔离临时 proof-object
目录，未启动全量 Lean 冷构建。

单代理自审核对实际 Euler 积分、三个 pole-cancelling 因子、Gamma 正实部
区域、固定时间常数、完整实产品指数、矩形方向、两条水平边、`2*pi*i`
归一化和正留数。没有将本次检查称为独立代理、外部同行审阅或远端 CI。

## 固定时间、非零 shift 的真实物理域去截断

### 从点态界到完整产品半轴的 L1

`MWKFCubicAFEWeightEndpoint.lean` 先证明实际无限高度权对产品变量强可测。
对 `0<P<=1`，用已证换线得到统一端点界
`|V_X(t,P)|<=1+C_(t,-1/4)`（`X>0`）。对 `P>1` 使用右线界
`C_(t,X)*P^(-X)`。当 `X>1/2` 时，由两段实际可积幂函数证明

\[
 \int_0^\infty |P^{-1/2}V_X(t,P)|\,dP<\infty.
\]

这条命题包含零端点和无穷端，没有把端点截掉，也没有把条件收敛当成 L1。
实数幂先在 R 中计算再嵌入 C，避免把实数指数错误解释成复数幂实例。

### 二次产品的真实 Jacobian

`MWKFCubicAFEQuadraticEndpoint.lean` 处理 `r,s>0`、`delta!=0` 的两个符号，取

\[
 D_\delta=\{x>0:\delta+rx>0\},\quad
 P_\delta(x)=x(\delta+rx)/s,\quad
 P'_\delta(x)=(\delta+2rx)/s\ge |\delta|/s>0.
\]

证明此域上的可微性、单射性及正产品像，再应用带绝对 Jacobian 的换元
可积性定理。以确切的逆 Jacobian 上界 `s/|delta|` 除去导数，得到
`P_delta(x)^(-1/2)*V_X(t,P_delta(x))` 在整个 `D_delta` 上绝对可积。
负 shift 没有被替换为从零开始的积分；没有声称 `1/|delta|` 本身可对
所有 shift 求和，也不把它隐藏为参数一致常数。

### 接回原 Möbius、平方根及完整相位

`MWKFCubicAFEPhysicalEndpoint.lean` 定义 `cubicAFEProgressionPhysicalSummandVertical`，
只将原实际物理核中的有限高度产品权替换成已证的 `V_X`。保留两侧真实
Möbius mollifier 系数、因子2、`1/sqrt(d*e)`、`1/sqrt(P_delta(x))`、
`exp(i*t*log(1+delta/(x*r)))` 和 `W(t/T)`。

对正产品域的每个点，原物理核的 `V->infinity` 极限精确等于此新核。
再提取 `r=d/gcd(d,e)`、`s=e/gcd(d,e)`，以二次产品 L1 定理及完整相位模长1
证明固定时间、固定非零 shift 的真实新核在 `D_delta` 上绝对可积。
δ=0 仍允许在正产品点上取高度极限，但不进入未截断域积分的可积性定理。

记此真实无限高度核为 `K_infinity`，原实际补全权为
`B_J(x,y)=beta(2^J*x)*beta(2^J*y)`。从实际定义证明
`0<=B_J<=1`、可测性及正指标处最终等于1；用已证可积的 `|K_infinity|`
作支配，严格得到

\[
 \lim_{J\to\infty}\int_{D_\delta}
 B_J(x,(\delta+rx)/s)K_\infty(t,x)\,dx
 =\int_{D_\delta}K_\infty(t,x)\,dx.
\]

Poisson 的 `1/s` 因子和物理时间积分尚在外层。本条结论是固定时间、
固定非零 shift 的域积分，不是整个零模主项的求值；亦未证明先取
有限高度核的空间积分再令 `V->infinity` 与此新核的积分相同。
跨时间、跨 shift、独立模式的高度极限、共同 Mellin 主项和 T 一致余项
仍须继续证明，不能由本局部去截断推出最终渐近式。

### 本批核验与自审

三个新增源模块编译通过，共312行定义与证明。三组 red-stage 合约在目标
声明缺失时先失败；最终全部114个 MWKF 合约／公理审计文件同次核验退出码0。
314条完整公理报告仅含 `propext`、`Classical.choice`、`Quot.sound`，
没有 error/warning。回归包括零端点统一界、整条产品正半轴的范数可积性、
负 shift 的真实积分域、真实物理核的范数可积性、其完成积分极限，以及
允许零 shift 的单点高度极限。后一个条件没有被用于未截断域的可积性。

聚焦 pytest：`295 passed`（14.26秒）；deterministic coverage 正常退出。
内部 coverage 标签不代表这些新证明已经消除了最终 `hexact/hmain/hrem`。
`git diff --check`、staged diff 和新源文件占位符扫描通过；没有新增项目
公理、sorry、admit、native_decide，也没有提高 heartbeat 限额。
仍采用隔离 proof-object 目录及单代理顺序验证，未启动全量 Lean 冷构建。

自审明确保留了 `delta!=0`、两个正指标域、绝对 Jacobian、其下界
`|delta|/s`、原物理核全部系数和相位、实际完成权、以及实际可积支配。
本批只在固定时间／固定 shift 层面去截断；没有把点态高度极限误作积分
高度极限，也未把固定参数 L1 性质当作全局 o(T)。

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
summability of the integrated original series. Using finite
integer support, the original lattice sum has also been interchanged with
time integration and the complete finite-height moment reassembled as its
exact diagonal plus integrated Poisson boxes. The nesting order is explicitly
`(d,e), delta, (j,k), integral_t, h` in that earlier representation. Joint
smoothness and compact support now also prove that the literal time-integrated
kernel is Schwartz. Poisson applied to this kernel and the original finite
lattice/time interchange prove the actual per-box infinite-frequency/time
interchange. The complete finite-height moment is now also expressed in order
`(d,e), delta, (j,k), h, integral_t`, with its recombined height limit proved.
The actual inner frequency series is now absolutely summable; each box has
an exact zero/nonzero split and the zero term is identified with its full
physical double integral. Finite box families can be split as well. The
all-real dyadic mass is the product of the two explicit lower-boundary
weights. Actual real-product decay and a translation-uniform lattice bound
now prove integrated absolute convergence over all dyadic boxes and all
integer shifts. The zero and nonzero modes can consequently be aggregated
separately in the proved nested order, and the entire finite-height moment
is now `(diagonal + zeroMode) + nonzeroMode`. Arbitrary reordering of all
individual Fourier coefficients is not asserted. Any additional reorderings
needed for common Mellin/QCT evaluation and parameter-uniform tail estimates
remain to be established. The actual diagonal now has its finite-height
reciprocal-LCM/zeta Mellin formula, with both scale/integral interchanges
proved. The paper's bilateral dyadic zero mode still differs from the
current nonnegative-scale zero mode. Actual cutoffs at every finite lower-scale
completion depth, their exact lattice-invisible physical correction, and the
zero/nonzero correction pairing are now formalized. The added continuous
boxes have proved finite support with an explicit geometric bound. The actual
correction is a finite sum of jointly integrable kernels, and its double integral
equals the added zero modes. Both completed dyadic mode series are summable
at each fixed shift, and the paired completed shift series is summable.
The entire finite-height moment is unchanged by any finite completion depth;
even height-dependent finite depths preserve the recombined height limit.
Separate completed-mode summation across shifts, the lower-endpoint limit
at the complete time-integrated/shift-summed level, and the required
Mellin/height limit exchanges remain unproved.
For each fixed physical time and positive real product, the gamma-only
Mellin weight now has its independent, absolutely convergent height limit
on every nonzero line X>-1/2. Its actual residue-one contour shift from a
positive line to a negative line has also been proved, including both
horizontal-edge limits; this gives the small-product bound
`1+C_(t,a)*P^(-a)`. Weighted product L1 integrability and a Jacobian-preserving
pullback now also prove actual physical spatial integrability on the whole
two-positive-index domain for fixed time and nonzero shift. Dominated
convergence removes the actual lower-scale completion from that domain
integral of the infinite-height kernel. This is not an interchange of the
spatial integral with the finite-height limit, nor a dominated convergence
theorem for the complete time-integrated/shift-summed zero mode or either
infinite mode series.
Neither compactness in the logarithmic-extension proof nor the
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
  regularity, joint smoothness, integrated actual Schwartz kernel, actual
  per-box infinite-frequency/time interchange, and the full finite-height
  frequency-before-time moment with its recombined height limit, absolute
  inner-frequency convergence, per-box zero/nonzero split and all-real
  lower-boundary-weight reassembly, actual real-product power decay,
  integrated absolute dyadic/shift convergence, separate zero/nonzero
  aggregation, full finite-height diagonal/zero/nonzero decomposition,
  exact diagonal reciprocal-LCM Mellin formula, actual finite lower-scale
  cutoffs, finite support of added continuous boxes, physical correction
  integrability and its exact zero/nonzero pairing, separate completed dyadic
  mode reassembly, and the full paired completed moment with its recombined
  height limit, positive-strip Gamma bounds, absolute scalar vertical
  convergence, the independent real-product weight height limit, its
  residue-one finite rectangle, both horizontal-edge limits and its
  actual small-product contour-shift bound, full product-half-line weighted
  L1 integrability, nonzero-shift quadratic-product Jacobian pullback,
  literal physical-kernel pointwise height limit and spatial integrability,
  and its fixed-time, fixed-nonzero-shift completion integral limit;
- full end-to-end Lean formalization still requires formalizing the named
  analytic inputs, including the external MRSTT theorem.
