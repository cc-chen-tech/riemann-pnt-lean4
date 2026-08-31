# 固定光滑 H/L：三掩码重组支付幂次余因子完整包

白话结论：先把小模双谱的主角色部分写成 n、ρ、σ 三种整除指示，
再把所有分配合到共同列中，可以免去逐剩余类分离的 c^5 费用。
这样同一原模数 q=cp 的完整 centered 包，余因子 c 可从固定对数幂
扩大到 T^(3/7)。非单位频率、被排除的零双频和所有扩和差都保留；
不是只付某个角色，也不是把多个 saving 相乘。完整 twisted moment 仍未证明。

Git 父版本为 #557 **f2406d2802fd721e9db9f6c3f5e868b55a7fe5b1**。
唯一对象是 [CQ1](2026-08-31-physical-log-cofactor-whole-packet.md)
同一个 fixed smooth H/L、e prime、q=cp 原完整 centered 包。
本稿直接重跑原 μ(n) 未分解表达式，范围为
1≤c≤C≤T^(3/7)，c SF、p prime；η∈[7/6,5/4]。
大T时 C<E、C²<Q、p>2E、p>2U、U≫C；D_i≈sqrtT。
保留原A30、两taper、全部原单位、唯一2T/(RS)，不涉及 fullhδ。
固定q0=a0=b0=1；具体地，R≈S≈EQ≈T³、H≈L≈T^(5/2)、E≈T^η，
U=H/E、V=L/E、D1=Q/U、D2=Q/V、ν=RD1D2/(EQ)≈T。
e∈[E,2E)、q=cp∈[Q,2Q)，两者的原半开壳不变。
\(p_N(x)=1-\log x/\log N\)，原线性和准确为
\[
 {2T\over RS}\sum_{\substack{e,p\ {\rm prime},\ c\le C\ {\rm SF}\\
 E\le e<2E,\ Q\le cp<2Q,\ (ec,p)=(e,c)=1}}
 \mu(e)\mu(c)\mu(p)
 \sum_{\substack{n\ge1\\(n,ecp)=1}}\mu(n)p_N(n)p_N(ecp)
 \sum_{u,v\ne0}\Psi_{\rm sm}(n/R,ecp/S,ev/L,eu/H)1_{(uv,cp)=1}
 \left\{e_{cp}(-euv\bar n)-{\mu(cp)\over\varphi(cp)}\right\}. \tag{TM0}
\]
原r=n,s=ecp,h=eu,δ=ev；整包n,s≤N/2，不另插联合N边缘。
Ψ_sm来自FP1重插原F的光滑H/L单位分解，不能赋给旧literal硬包。
[RH1–6](2026-08-31-physical-prime-pair-reciprocal-hybrid.md)、
[LP1–4](2026-08-31-physical-prime-pair-principal-loglabels.md)固定原核。
A30为该核连同taper在原归一化坐标的总阶≤30半范数，始终显式保留；
本稿不自行把它当T^ε。有限小T只增大常数。

## TM1 小模因子只有三种整除指示

CQ的 Z_c=(S_c/c)e_c(-nρσ inverse(ep))。
先假定(nep,c)=1。c=ℓ prime 时记 R=1_(ℓ|ρ),S=1_(ℓ|σ)，
U=(1-R)(1-S)，B=RS，x=nρσ inverse(ep) modℓ。
逐有限和精确有

 Z_ℓ=U+e_ℓ(-x)/ℓ-B
     =A_ℓ(R,S)+1/[ℓφℓ] Σ_(χ≠χ0 modℓ) τℓ(barχ) χ(-nρσ)barχ(ep),
 A_ℓ=αℓ U+1/ℓ-B=wℓ-αℓ(R+S)-βℓRS,
 αℓ=(ℓ-2)/(ℓ-1), βℓ=1/(ℓ-1), wℓ=1-1/[ℓ(ℓ-1)].

ℓ=2 非主角色集为空，A₂=1/2-RS；不能假造primitive角色mod2。
χ是primitive零延拓，非单位ρσ落在Aℓ而不是被删除。

平方自由c逐素数CRT，将非主角色素数集合记λ，c=λa：

 Z_c=Σ_(λa=c) Σ_(χ primitive modλ)
     τλ(barχ)/[λφλ] χ(-nρσ)barχ(ep a)
     ∏_(ℓ|a) Aℓ(1ℓ|ρ,1ℓ|σ).                      (TM1)

λ=1有唯一平凡角色和τ1=1；λ含2时primitive集空。CRT互补a不可漏。
乘(n,c)单位指示后，把λ-unit交给χ，a的单位展开如下。
式在n非c-unit处定义为0，不在那里计算S_c的逆元。

## TM2 三掩码的精确lcm重组

再记N=1_(ℓ|n)。每个ℓ|a有多项式

 (1-N)Aℓ(R,S)
  =wℓ-wℓN-αℓR-αℓS+αℓNR+αℓNS-βℓRS+βℓNRS.       (TM2)

七个非空subset分别分给n、ρ、σ三列。令其除数f,j,k为SF，
g=lcm(f,j,k)，a=gz，(g,z)=1。每素数的非空系数按上表相乘为
v_g(f,j,k)，|v_g|≤1；剩余z素数全取空项w(z)=∏wℓ，0<w(z)≤1。
于是n=fm,ρ=jr,σ=ks，并保留原μ(fm)，不添加(m,f)/(m,z)。
κ=fjk/g是整数且与eλ互素。c=λgz，q=λgzp。剩余原系数包括
μ(e)μ(λ)μ(g)μ(z)μ(p)μ(fm)v_g(f,j,k)w(z)。
原n-mask的符号已在v_g中，不额外再乘一个μ(f)。

对固定g,f,j,k,L≈λ及z dyadic壳，zp是共同乘积列；
μ(z)w(z)、(z,g)=1、z SF和p prime都进入这个卷积系数，大小≤τ₂。
(z,λ)=1、λ-unit标签由χ的零延拓实现；(λ,g)=1保留模数行。
没有删除(z,λ)后在非零角色处新增非法项。

## TM3 两个联合硬壳的费用，不新增smooth边缘

Q≤λg zp<2Q、λgz≤C是原q/c独立壳在新坐标中的联合条件。
先固定dyadic λ≈L,z≈Z，p≈Q/(LgZ)（有限倍长覆盖，O(logT)块）。
仿照 [GW6](2026-08-31-physical-low-gauss-short-divisor.md)，
在整数q、c端点各自的半整数间隙构造以log(q/Q)、log(c)为变量的
光滑阶梯。前者固定log支撑，Var≪1、二阶导数L1≪Q，系数
≪min(1,1/|k|,Q/k²)，故Fourier ℓ1≪log(2Q)。
c从1至C时周期可取O(log(2C))，同理费用≪log²(2C)。
只在整数点取值，等于原硬指示，没有截断误差。
每项精确分成对数相位：q的频率落λ和zp列，
c的频率落λ和z列，不落两个Weyl标签；
不把这些尖锐插值的导数计入A30。所有截止误差精确为0。
p>c由c≤C、q≥Q、C²<Q自动成立，原大素数标签唯一。
每个乘积列卷积保留p的独立壳及所有内部z限制，不额外乘z行数。

原Φ在以下六个紧坐标统一分离：
 m/(R/f), e/E, λ/L, (zp)/(Q/(Lg)), r/(J1/j), s/(J2/k).
q/Q=(λ/L)*[(zp)/(Q/(Lg))]，f,j,k,g只改列长度；
连续chirp为 e(κmrs/(eλ zp))，自然参数仍X=RJ1J2/(EQ)，没有κ新损失。
原子H⁴有4>6/2+2/3，12+12+4=28≤30。所有原子频移和
两个标签权(1+|ωr|)^(1/3+eps)(1+|ωs|)^(1/3+eps)保留。
主核和硬壳分别分离，A30只支付一次。

## TM4 e非主角色与λ角色的精确Gauss融合

对CQ6新e模采用ψ≠ψ0。TM1与此展开相乘后的Gauss/互补因子为

 τe(barψ) τλ(barχ) barψ(λ)barχ(e)
       =τ_(eλ)(barψ barχ),
 共同系数为 τ_(eλ)(barψ barχ)/[λφ(eλ)]，
 角色为 (ψχ)(-κmrs) (barψ barχ)(zp).                (TM3)

不能只把ψχ当模e角色。其真实primitive导子为eλ；e>C≥λ，
所以从(e,λ)到eλ是唯一大素数标签，扩大到所有mod≤2EL不会重数。
μe μλ保留行标量，χκ保留，所有g单位条件仍在行限制中。
先取四多项式模长再共轭标签，与RH相同；不是线性值共轭替换。

固定g,f,j,k及λ≈L，n列长N1=R/f，另一乘积列长
K=QJ1J2/(Lgjk)=K0 θ/(Lgjk)，K0=QD1D2，
θ=(J1/D1)(J2/D2)，X=νθ。只有自然对偶尺度θ=1才可用K0/(Lgjk)。
一次 [CIS (1.6)](https://arxiv.org/pdf/1105.1176)
普通hybrid primitive LS给未乘
外2T/(RS)的界

 A30 T^eps UV/[Q L sqrt(EL(1+X))]
   sqrt{N1 K [N1+(EL)^2(1+X)] [K+(EL)^2(1+X)]}.    (TM4)

其自然尺度物理四项为
 T^(7/2-5η/2) L^-5/2 /(f g j k),
 T^(2-η) L^-1 /(f sqrt(gjk)),
 T^(5/2-3η/2) L^-3/2 /(g j k sqrtf),
 T /(sqrt(f g j k)).                               (TM5)

完整短X及两无限dual/Mellin尾按RH16的平方比较，
乘(√θ+θ)∏(1+λ_i)^(-8+eps)，仍可和；λ_i这里是dual比例非导子λ。
硬壳额外Fourier频率只乘共同列相位，不进标签权。

## TM5 e主角色：全部λ含principal与同一二列

先按CQ5完整付两个e-mask差，n=e*m与e|ρσ（交叠只减一次）。
现在n仍c-unit，TM1–2合法；e不再是角色modulus，而进入e*z*p共同列，
长度N2=S/(Lg)。eprime的独立壳及μ(e)也在该卷积内。
原e>c、p>2E保证e与c/p互素，不引入与λ耦合的未付mask。

系数Gauss模长准确为1/[φ(e)√λ φλ]，因而≪ε T^ε/[E L sqrtL]；
这里保留φ的亚幂费用，不把它字面替成模数。两个标签采用cube-free primitive
χλ的 [Petrow–Young Corollary 1.3](https://arxiv.org/pdf/1811.02452v3) Weyl界（λ=1保留ζ极点项/近平移零频，用GW7–8处理）；
固定j,k给标签积≤L^(1/3+eps) X^(5/6+eps)/sqrt(jk)。
这是平滑标签的Mellin反演界：在1/2线使用
|L(1/2+it,χλ)|≪[λ(1+|t|)]^(1/6+ε)，
λ=1的极点项J^(1+it)hatψ(1+it)以Schwartz衰减保留。
任意原子频移ω以(1+|ω|)^(1/3+ε)支付；近平移零频用平凡界，
不能把两个标签换成一般硬截断角色和。正负标签先分符号，
保留χ(−1)，不在线性式中随意共轭系数。
保留Mellin X^-1/2再对共同(N1,N2)跨(λ,χ,t)做一次Cauchy+LS：

 A30 T^eps UV/(QE) X^(1/3) L^-7/6 /sqrt(jk)
   sqrt{(R/f)(S/(Lg))[R/f+L²X][S/(Lg)+L²X]}.       (TM6)

λ=1由普通时间均值实现同式，不删除其principal。
其自然尺度物理四项为
 T^(10/3-2η) L^-13/6 /(f g sqrt(jk)),
 T^(7/3-2η) L^-2/3 /(f sqrt(gjk)),
 T^(7/3-2η) L^-7/6 /(g sqrt(fjk)),
 T^(4/3-2η) L^1/3 /(sqrt(f g j k)).                 (TM7)

在L≤C≤T^(3/7)、η≥7/6时均≤T；最后一项有很大余量。
H⁴付加权原子，主/离驻点时间尾和平移近零严格沿GW/LP：
一般块X=νθ，J1J2≈X，非空原整数块使X≥固定正数。
X≤1是统一有界短段；X≥1时主Mellin段幅度X^-1/2，
外时间环的六阶衰减支付LS至多一次幂的增长。
自然尺度比较多项式增长至多
θ^(1/3)max(1,θ)max(1,θ)^(2ε)，由双八阶尾支付。
新卷积至多τ4，其全部dual除数增长也显式留在正majorant内。
全部换序先对有限截断作等式，再由此正可和majorant放开；
不是只验证自然双频就声称无限尾完成。
额外ℓ^eps及无限dual除数增长留到可和majorant后才重命名eps。

## TM6 全g与七分配并未免费

固定g的每素数非空subset大小t=1,2,3给TM5/7最弱的末项
权重ℓ^(-(1+t)/2)，每个subset系数≤1。所以

 Σ_(g≤C) Σ_(lcm(f,j,k)=g) |v_g|/sqrt(fgjk)
 ≤∏_(ℓ≤C)[1+3/ℓ+3/ℓ^(3/2)+1/ℓ²] ≪eps C^eps.     (TM8)

也可用每g≤7^ω(g)/g及除数界得到C^eps，不要求素数定理。
其余六种分母都不少于sqrt(fgjk)，逐素数可核。
g、λ、z壳合计O(log³T)，只能在这一步吸入T^eps。
因此TM5和TM7不留sqrtC或c^5；此处是先重组后共同大筛的实质。

## TM7 旧差项在幂次C范围必须重算：零轴不可删

CQ第二CRT分支仍U≫c、p>2U，费用sum_c≤C
 A6 T UV/Q C^7/U^6。CQ的B_e和principal双e-mask差按c^-1求和可付。
CQ B_p按c^5求和≤A30 T^(-23/2+5η+eps) C^6。

不能沿用CQ对O_c和B_n,c的每c T平凡界直接求和。
c>1时Sc对每个ρ的完整模c平均为0；原sum仅ρ≠0，
所以Poisson完成后必须减ρ=0项。对固定σ的真实Φ有

 Σ_(ρ≠0) Sc Φ ≪ A30 c τ(c) D1 [(c/D1)^6+1/D1]
                      (1+|σ|/D2)^-6.              (TM9)

1/D1正是被排除零轴，不能声称整非零sum快衰减。
O_c再保留p双unit，以非零p倍数尾处理扩和。
B_n,c中n=pj的p相位为1，Sc只用n inverse modc仍合法；
先支付e和p非零倍数尾，原μ(pj)不因子化，再用同一TM9。
c=1用原CQ O_1/B_n,1≤T，不能用c>1零均值。
全部O/B_n的保守总账为

 A30 T^(1+eps)[1+C/D + C^7/D^6
                +C D^5/E^6 + C^7 D^5/Q^6], D≈sqrtT. (TM10)

C≤T^(3/7)时C^7/D6≤1，C/D≤T^-1/14，其余远小于1。
TM9所需6阶对dual参数的微分只是原compact标签的有界矩；
原σ六次IBP仍在A30内，无新增T导数损失。

## TM8 完整包、真正新增域及有限命题

由TM4–7及CQ的准确Raw=F+B_e−B_n−B_p和两个CRT分支，得到
\[
 |\mathcal C_{e\ {\rm prime},\ q=cp,\ c\le T^{3/7}}|
 \ll_\epsilon A_{30}T^{1+\epsilon},
 \qquad 7/6\le\eta\le5/4.                              \tag{TM11}
\]
它把对数c推广到所有SF c≤T^(3/7)。实质是TM2完整三mask重组、
TM3硬壳分离、TM4真实导子eλ以及TM9被排除零轴共同起作用。
η=6/5时重跑同包旧DP14仍给11/10预算：
把q族限制放在Cauchy后的模数行标量，可扩至全部模数。
新界1因此改善1/10；这是上界预算比较，不是原值下界。
c≤log^A原交集由CQ已付，不重复算作新增；例如c≈T^(2/5)
才是此次真正新增的未覆盖区域，不叠乘此前短II或频率带saving。

新真非空族可用c≈Y²,e≈Y⁶,p≈Y⁷互异素数，
R=S=ecp≈Y15,T=(8S)^(1/3)≈Y5，c≈T^(2/5)，
K_z=M_z=√T、H=L=S/√T、N=8S。
原u=v≈q/sqrtT≈Y^(13/2)<p，选不被c整除；nprime∈(S,2S)。
因此原q是复合模数，余因子c随T增长并超过全部固定log幂，
支持和n,s≤N/4均成立；这个见证的c本身取素数，不能称c为合数。
不声称任意核积分非零或positive density。

其余q不带这种大素因子、合数e、全canonical/q0、fullhδ、跨AFE/HL尾、
actual amplified和共同能量仍open，完整gate没有完成。

可直接形式化的有限命题是：TM1所有SF模数与全部非单位/零标签的
角色恒等式；TM2三掩码的唯一lcm分配；真实μ(fm)及全部CRT符号重组；
TM3有限硬指示在整数点的乘积相位分离；两个Gauss和真实eλ融合；
所有费用的有限有理指数关系。附脚本同时保留旧漏θ公式、零轴、
额外μf、模2虚假primitive和非单位层错误的反例。
这些finite checks不是解析大筛/无限尾证明，也不是Lean/main验收。
