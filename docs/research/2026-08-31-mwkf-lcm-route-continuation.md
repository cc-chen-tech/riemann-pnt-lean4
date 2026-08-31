# MWKF LCM 路线续篇：局部估计与未证输入

本文保全 #490 的研究续篇，不改变其局部结论或未证边界。
公共前置定义与 §1–§4.68 见 [canonical alternative-routes note](2026-08-25-mwkf-alternative-routes-spike.md)。
本文件的 §4.68.1–§4.79 及公式 (4.622)–(4.687)（含 4.686a）属于
独立的 **LCM continuation** 编号空间，不与 canonical 的同号章节或公式互指。
下文 §4.60、§4.15–§4.16、§4.46 仍指 canonical 的公共前缀；
所有 (9.*) 公式仍指 [原物理积分账本](2026-08-24-mobius-weighted-off-diagonal.md)。
局部改善不能移除完整有符号和、外层聚合或原物理权重的未证输入。

#### 4.68.1 Completing the shift first removes the hard error deficit

The conclusion after (4.621) is correct for a literal application of the
published Watt estimate, but it is not the best estimate of BBLR's exact
nonzero-frequency expression (14).  In the all-unsigned hard cell, complete
the (h)-sum before estimating the inverse fraction.

Put

\[
 d=(m_1,n_1),\qquad m_1=dm,\qquad n_1=dn,
\tag{4.621a}
\]

so that (m,n\asymp T/d) and ((m,n)=1).  Equation (14) has

\[
 0<|l|\le L,\qquad L\ll \frac{T^\varepsilon}{d},
\tag{4.621b}
\]

and its phase in (h) is

\[
 e\!\left(\mp l h\frac{\bar m}{n}\right).
\]

Poisson summation gives, for every fixed (A>0),

\[
 \sum_h W_0\!\left(\frac{dh}{T}\right)
 e\!\left(\mp l h\frac{\bar m}{n}\right)
 \ll_A \frac Td
 \left(1+\left|l\bar m\right|_n\right)^{-A},
\tag{4.621c}
\]

where (|x|_n) is the least absolute residue.  Here (T/d\asymp n), so
there is no omitted ratio of the shift length to the modulus.

As (m) runs through an interval of length (T/d\asymp n), inversion
permutes the reduced residue system modulo (n).  Multiplication by (l)
has fibres of size at most ((l,n)).  Therefore

\[
 \sum_{\substack{m\asymp T/d\\(m,n)=1}}
 \left|\sum_h W_0\!\left(\frac{dh}{T}\right)
 e\!\left(\mp l h\frac{\bar m}{n}\right)\right|
 \ll_A \frac Td(l,n)T^\varepsilon.
\tag{4.621d}
\]

The integral (F) in equation (14) has length (d), hence
(F\ll d).  Do not now use the pointwise inequality ((l,n)\le l).
Instead sum the frequency gcd by the exact identity

\[
 \sum_{1\le l\le L}(l,n)
 =\sum_{r\mid n}\varphi(r)\left\lfloor\frac Lr\right\rfloor
 \le L\tau(n).
\tag{4.621e}
\]

After (4.621d), the (F)-factor, the (n\asymp T/d)-sum and
(4.621e), the whole fixed-(d) nonzero-frequency contribution is

\[
 \mathcal R_d\ll
 \frac{T^2}{d}L T^\varepsilon
 \ll \frac{T^{2+\varepsilon}}{d^2}.
\tag{4.621f}
\]

Now (4.621b) forces (d\le T^\varepsilon).  Summing over (d) yields

\[
 \boxed{\mathcal R_{\pm}^{\rm hard,unsigned}
 \ll T^{2+\varepsilon}.}
\tag{4.621g}
\]

The approximation error already present in (14) is (H^2T^\varepsilon
=T^{2+\varepsilon}), so (4.621g) reaches the exact local target.  The
previous (T^{5/2}) ledger is therefore a deficit of the Watt-first route,
not a deficit of the hard nonzero-frequency sum itself.

The same calculation gives a finite post-Type coverage test.  Write the
BBLR exponents as

\[
 A=T^a,\ B=T^b,\ M_i=T^{\mu_i},\ N_i=T^{\nu_i},\ H=T^\alpha,
\]

with (a+\mu_1+\mu_2=b+\nu_1+\nu_2=P).  Reindex
(X=am_1/d), (Y=bn_1/d); the factorization multiplicities are divisor
bounded, so all Möbius atoms may remain in the two arbitrary outer
coefficients.  In the BBLR orientation (BN_1\le AM_1), equivalently
(b+\nu_1\le a+\mu_1) at exponent level, completing (h), summing the
(X)-residues and then applying (4.621e) to the complete (l)-average gives
the nonzero-frequency exponent

\[
 \boxed{
  E_{h\text{-comp}}
 =\mu_2+(a+\mu_1-b-\nu_1)_+
  +\max(b+\nu_1,\alpha)
  +(a+\mu_1-\nu_2)_+.}
\tag{4.621h}
\]

If (a+\mu_1-\nu_2<0), the nonzero (l)-family is empty by its exact
cutoff.  Otherwise the subcell is covered whenever

\[
 E_{h\text{-comp}}\le P.
\tag{4.621i}
\]

To recover the full symmetric proposition one must also allow the two
sides to be exchanged.  Set (x=a+\mu_1) and (y=b+\nu_1).  Balance gives
(\nu_2=P-y), so the cutoff exponent is

\[
a+\mu_1-\nu_2=x+y-P.
\]

The better of the two orientations simplifies exactly to

\[
 \boxed{
 E_{h\text{-comp}}^{\rm sym}
 =P+(\alpha-\min(x,y))_+ +(x+y-P)_+.}
\tag{4.621s}
\]

Consequently the complete coverage classification is:

1. if (x+y<P), the nonzero-frequency family is empty;
2. if (x+y=P), one of the two orientations reaches the target exactly
   when (\min(x,y)\ge\alpha);
3. if (x+y>P), the completion bound is strictly above (P).

Thus the remaining nonzero-frequency Type cells are not diffuse: they are
the supercritical half-polytope (x+y>P), together with the
too-small-prefix portion (\min(x,y)<\alpha) of the boundary.  The former
"reversed ordering" residual was an artefact of fixing one orientation.
No assertion is made that failure of this particular completion bound is
a lower bound for the original signed sum.

Formula (4.621s) also locates the remaining power exactly.  On the
supercritical subregion where (\min(x,y)\ge\alpha), the whole deficit is

\[
 E_{h\text{-comp}}^{\rm sym}-P=x+y-P,
\]

which is precisely the exponent of the surviving nonzero (l)-frequency
range.  In the symmetric signed hard cell (x=y=3/2), (P=2), this is one
full power: (L=T) and the bound is (T^3) against target (T^2).  A generic
square-root treatment of the (l)-family would recover only (T^{1/2}) and
would recreate the old half-power deficit.  Closing this region therefore
requires the complete (l)-range saving from its joint interaction with the
two outer coefficient families, or an exact recombination that removes the
range before absolute values.  On the remaining boundary portion
(x+y=P), the deficit is instead the short shift/modulus mismatch
(\alpha-\min(x,y)).

For (4.618), (4.621h) is exactly (2).  For example, the signed cell
(a=b=1), (mu_i=\nu_i=1/2), (alpha=1) instead gives (3), so the
new completion is a genuine additional coverage region, not a proof of all
Type cells.

Finally, (4.621g) concerns only (l\ne0).  The (l=0) Poisson main term
is of larger raw size and still has to be recombined across all four
Möbius outer allocations and the BBLR orderings, together with the already
registered zero-frequency master.  Consequently the whole coupled gate is
not yet proved, but its formerly worst **nonzero-frequency** cell is now
closed without any Möbius estimate.

The adapters `transition_bblr_hard_h_completion_audit` and
`transition_bblr_h_completion_subcell_audit` record (4.621a)--(4.621i).
The adapter `transition_bblr_symmetric_h_completion_audit` records the
left/right minimum (4.621s).
The helpers `inverse_multiplier_unit_fibre_max` and
`frequency_gcd_sum_identity` check the exact fibre and frequency-average
identities on finite moduli.

#### 4.68.2 The remaining BBLR main term is an exact phase-free outer product

The (l=0) term can be isolated without an estimate.  Put

\[
 \mathcal A_d(X)=
 \sum_{am_1=dX}\alpha_aW_1\!\left(\frac{m_1}{M_1}\right),
 \qquad
 \mathcal B_d(Y)=
 \sum_{bn_1=dY}\beta_bW_3\!\left(\frac{n_1}{N_1}\right),
\tag{4.621j}
\]

and

\[
 \mathcal K_d(X,Y)=
 \sum_h W_0\!\left(\frac{dh}{H}\right)
 \int_0^\infty
 W_2\!\left(\frac{Yx}{M_2}\right)
 W_4\!\left(\frac{Xx}{N_2}\right)\,dx.
\tag{4.621k}
\]

Since

\[
 d=(am_1,bn_1),\qquad X=\frac{am_1}{d},\qquad
 Y=\frac{bn_1}{d},\qquad (X,Y)=1,
\]

the main term in BBLR Proposition 3.1 is exactly

\[
 \boxed{
 \mathcal M_{\rm BBLR}
 =\sum_{d\ge1}\sum_{(X,Y)=1}
 \mathcal A_d(X)\mathcal B_d(Y)\mathcal K_d(X,Y).}
\tag{4.621l}
\]

All sums in (4.621l) are finite because the five original smooth weights
are compactly supported.  There is no endpoint error, no inverse residue
and no additive phase.  The two arbitrary outer coefficients remain
separate; in particular their two Möbius-bearing decompositions have not
been replaced by absolute values.

This identity also explains why the main term cannot be discarded
cellwise.  For a balanced side-product exponent (P), shift exponent
(alpha), and (d=T^eta), the (X,Y)-counts, the shift length (H/d), and
the integral length (dM_2/(BN_1)) give the fixed-(d) absolute-value
exponent

\[
 E_{\ell=0,d}=P+\alpha-2\eta.
\tag{4.621m}
\]

The dyadic (d)-layer contains (T^{\eta+o(1)}) values.  Hence

\[
 E_{\ell=0,\rm layer}=P+\alpha-\eta,
 \qquad
 \boxed{E_{\ell=0,\rm global}=P+\alpha.}
\tag{4.621n}
\]

Thus the raw phase-free main term is one complete shift length
(T^\alpha) above the local (T^P) target.  In the all-unsigned hard cell
this specializes to

\[
 \mathcal M_{\rm BBLR}^{\rm hard,unsigned}
 \ll T^{3+\varepsilon}
 \quad\text{against target }T^{2+\varepsilon}.
\tag{4.621o}
\]

Moreover, the plus/minus shifted equations in BBLR have the same
(l=0) term: their only orientation dependence is in the additive phase,
which has disappeared.  The two orientations therefore do not cancel
internally when their external weights agree.  Opposite signs from a
larger AFE recombination are not ruled out, but must be exhibited there.

Thus the
nonzero-frequency completion does not by itself cover the whole cell.
Inside the present DCV/square-function route, the correctly typed missing
object is the fully recombined BBLR zero-frequency contribution

\[
 \mathfrak G_{\rm BBLR}^{(0)}
 :=\sum_{\substack{\text{AFE directions, BBLR orderings,}\\
                    \text{four outer Möbius sectors}}}
 \mathcal M_{\rm BBLR},
 \qquad
 \mathfrak G_{\rm BBLR}^{(0)}
 \stackrel{?}{\ll}T^{P+\varepsilon}.
\tag{4.621p}
\]

The estimate in (4.621p) is not yet proved.  Nor is
\(\mathfrak G_{\rm BBLR}^{(0)}\) identified with the pre-Cauchy
\(\mathcal M_{\rm res}\) in (9.447): they live at different stated stages,
so they cannot be literally cancelled without first constructing an
adapter that undoes or bypasses the DCV reorganization.
The finite helper `bblr_zero_frequency_reindex_sides` verifies (4.621j)--
(4.621l) for arbitrary rational coefficient fixtures and deliberately sets
`registered_zero_master_identification_proved=False`.  This separates the
remaining main-term adapter from the now-bounded nonzero-frequency error.
The adapter `transition_bblr_zero_main_term_audit` records (4.621m)--
(4.621o) and the shift-orientation boundary with exact rational exponents.

There is no further coordinate obstruction to constructing a pair kernel
of the same algebraic shape as the finite master schema (9.437)--(9.448).
This does **not** yet identify the analytic stage: the BBLR comparison may
already lie inside a DCV/square-function reorganization, whereas
\(\mathcal M_{\rm res}\) in (9.447) is pre-Cauchy.  Put (x=dX), (y=dY),
so the coprimality in (4.621l) is equivalent to (d=(x,y)), and define the
labelled product kernel

\[
 W_h^{\rm BBLR}(x,y):=
 W_0\!\left(\frac{(x,y)h}{H}\right)
 \int_0^\infty
 W_2\!\left(\frac{y u}{(x,y)M_2}\right)
 W_4\!\left(\frac{x u}{(x,y)N_2}\right)\,du.
\tag{4.621q}
\]

Writing

\[
 A(x)=\sum_{am_1=x}\alpha_aW_1(m_1/M_1),\qquad
 B(y)=\sum_{bn_1=y}\beta_bW_3(n_1/N_1),
\]

equation (4.621l) becomes the literal pair-kernel identity

\[
 \boxed{
 \mathcal M_{\rm BBLR}
 =\sum_h\sum_{x,y\ge1}A(x)B(y)W_h^{\rm BBLR}(x,y).}
\tag{4.621r}
\]

Thus each original nonzero shift (h), together with its AFE direction,
BBLR ordering and dyadic label, can be retained in a
secondary-zero-packet-shaped kernel; no inverse phase or gcd endpoint is
lost.  What is still missing is not a kernel-coordinate map.  It is the
analytic proof that this BBLR object is at the same pre-Cauchy stage as
(9.440), that after summing every Type sector and ordering the functions
(A,B) in (4.621r) are exactly the completed left/right coefficients in
(9.439), and that the resulting labelled packet family is exhaustive.
Only after all three facts are proved can this BBLR object be compared
literally with the old pre-Cauchy master.  Independently, proving the bound
in (4.621p) inside the DCV route requires the exhaustive ordering/sector
sum and a (T^alpha)-saving estimate for that recombined object.

The finite helper `bblr_zero_frequency_reindex_sides` now verifies all
three equal values: the original factorized sum, the primitive
((d,X,Y))-sum, and the labelled product-pair sum (4.621r).  It marks the
coordinate bijection and shift-label preservation as true, while keeping
`pre_cauchy_stage_identification_proved=False`,
`completed_coefficient_identification_proved=False` and
`packet_family_exhaustive=False`.

#### 4.68.3 The supercritical nonzero family must be grouped by full reciprocal phase

The factorization-blind reindexing is not restricted to (l=0).  Let a
supplied finite BBLR packet retain its original ((h,delta))-provenance and
write

\[
 \mathscr W(d,X,Y;h,\delta,l)
\]

for its complete smooth weight, integral and nonzero-(l) phase.  The
analytic adapter from the original coupled kernel to this labelled BBLR
packet is still an obligation; the following finite statement says that
once those labels are supplied, no Type-factorization step is allowed to
delete them.

With (A_d,B_d) as in (4.621j), exact finite reindexing gives

\[
 \boxed{
 \mathscr S_{\rm BBLR}^{\ne0}
 =\sum_d\sum_{(X,Y)=1}A_d(X)B_d(Y)
   \sum_{h,\delta}\sum_{l\ne0}
   \mathscr W(d,X,Y;h,\delta,l).}
\tag{4.621t}
\]

Thus every Type sector having the same products (am_1=dX) and (bn_1=dY)
recombines inside (A_d(X)) and (B_d(Y)) before any absolute value.  Both
coupled products remain visible:

\[
 a_0:=h\delta,\qquad b_0:=hl,\qquad
 \phi(d,X,Y;h,l):=-\frac{b_0\bar X}{Y}\pmod1.
\tag{4.621u}
\]

In particular the all-unsigned outer cell cannot be estimated and summed
afterwards: its positive coefficient is cancelled, if at all, only inside
the complete aggregated (A_d,B_d).

The correct (TT^*) resonance is equality of the full rational phases in
(4.621u), not equality of either scalar product.  For two rows (u,v), it
is exactly

\[
 \frac{h_ul_u\overline{X_u}}{Y_u}
 \equiv
 \frac{h_vl_v\overline{X_v}}{Y_v}\pmod1.
\tag{4.621v}
\]

Distinct values of both (h\delta) and (hl) can satisfy (4.621v).  Hence a
partition by the original product frequency does not diagonalize the new
operator.

After lifting a finite row family to a common cyclic modulus (Q), exact
character orthogonality gives

\[
 \boxed{
 Q\sum_\phi\left|\sum_{u:\phi_u=\phi}c_u\right|^2
 =Q\sum_u|c_u|^2
  +Q\sum_{\substack{u\ne v\\\phi_u=\phi_v}}
       c_u\overline{c_v}.}
\tag{4.621w}
\]

The second term in (4.621w) is signed and can cancel the positive identity
diagonal.  Taking absolute values of phase classes, or applying Cauchy
before the Type sectors have recombined, deletes precisely this possible
source of the full (L)-saving.

On the supercritical region with (\min(x,y)\ge\alpha), put
(\lambda=x+y-P>0).  Equations (4.621s) and (4.621w) give the exact budget

\[
 E_{\rm raw}=P+\lambda,qquad
 S_{\rm required}=\lambda,qquad
 S_{\rm generic\ square\ root}=\frac\lambda2,qquad
 S_{\rm still\ missing}=\frac\lambda2.
\tag{4.621x}
\]

At the signed hard cell, (\lambda=1), so the remaining signed phase-class
gain is exactly (T^{1/2}) after a generic square-root treatment.  This is
not a proof of that gain; it identifies its only surviving location inside
the BBLR route.

The finite helper `bblr_nonzero_frequency_reindex_sides` verifies
(4.621t)--(4.621u) with nonzero (l), both original labels and both products
unchanged.  The helpers `bblr_reciprocal_phase_collision_audit` and
`bblr_phase_group_ttstar_sides` verify (4.621v)--(4.621w), including a
fixture in which distinct product frequencies collide and the signed cross
term reduces the positive identity diagonal.  The exponent adapter
`transition_bblr_phase_group_saving_audit` records (4.621x) and keeps
`required_phase_class_cancellation_proved=False`.

There is now also an exact row-level adapter from this labelled object to
the existing four-sector double-Möbius split.  For coprime \(r,s\), every
nonzero term in each of the \(I/I,I/II,II/I,II/II\) sectors retains both

\[
 a_0=h\delta,
 \quad e\!\left(-\frac{a_0\bar r}{s}\right),
 \qquad
 b_0=hl,
 \quad e\!\left(-\frac{b_0\bar r}{s}\right),
\tag{4.621y}
\]

as well as the exact factorizations of both Möbius variables.  Summing all
four sector coefficients still gives \(\mu(r)\mu(s)\); neither product is
replaced by an independent coefficient before recombination.  The finite
helper `coupled_product_double_mobius_certificate`, with its optional
nonzero `poisson_frequency`, verifies this statement exactly.

Equation (4.621y) is deliberately weaker than the missing analytic gate.
It proves that the Type split itself need not destroy either reciprocal
phase, but it does **not** identify the row variables \(r,s\) with every
completed BBLR \(X,Y\) row, prove exhaustiveness of that stage map, or
bound the signed phase classes in (4.621w).  Consequently
`both_reciprocal_phases_preserved=True` is a finite algebraic invariant,
not the required \(T^{\lambda/2}\) analytic saving.

#### 4.68.4 Joint \((h,l)\)-completion alone has an exact near-diagonal resonance

It is natural to try to recover the full \(L\)-saving in (4.621x) by
estimating the two BBLR variables \(h,l\) jointly.  Equation (14) of BBLR
does contain their joint phase

\[
 e\!\left(-hl\frac{\bar X}{Y}\right)e(lx).
\tag{4.621z}
\]

However, this local two-variable step cannot be uniform in \(X,Y\).  Put

\[
 X=Y+c,\qquad (c,Y)=1,
\]

and, for any \(0<h<Y\), define
\(r=[h\bar X]_Y\in\{0,\ldots,Y-1\}\).  Since
\(X\equiv c\pmod Y\), multiplication by \(X\) gives the exact integer
coordinate

\[
 \boxed{rc-h=kY,\qquad k\in\mathbb Z.}
\tag{4.621za}
\]

Thus the principal incidence \(k=0\) is exactly \(h=cr\), and on it

\[
 h\bar X=cr\bar c\equiv r\pmod Y.
\tag{4.621zaa}
\]

Choose a central residue \(r_0\) and evaluate the continuous BBLR variable
at \(x=r_0/Y\).  The combined phase in (4.621z) is then represented by

\[
 \frac{l(r_0-r)}{Y}.
\tag{4.621zb}
\]

On the signed hard scale take

\[
 Y\asymp T^{3/2},\qquad c\asymp T^{1/2},\qquad
 r,r_0\asymp T^{1/2},\qquad h=cr\asymp T,\qquad l\asymp T.
\]

These are forced scales, not a free example.  Slow \(l\)-phase requires
\(r\asymp xY\asymp Y/L\), while the principal equation \(h=cr\)
then gives

\[
 \boxed{c\asymp\frac{H}{r}\asymp\frac{HL}{Y}.}
\tag{4.621zab}
\]

At \(H=L=T\) and \(Y=T^{3/2}\), (4.621zab) is precisely
\(c=T^{1/2}\).

More importantly, the principal incidence is not a generic shifted
outer-correlation row.  Before Poisson summation, the plus-oriented BBLR
equation divided by \(d=(am_1,bn_1)\) is

\[
 Xm_2-Yn_2=h.
\]

On \(k=0\), equations (4.621za)--(4.621zaa) give

\[
 Xm_2-Yn_2=(X-Y)r,
\]

and hence

\[
 X(m_2-r)=Y(n_2-r).
\]

Because \((X,Y)=1\), this has the exact integer parametrization

\[
 \boxed{m_2=r+Yt,\qquad n_2=r+Xt,\qquad t\in\mathbb Z.}
\tag{4.621zac}
\]

In the signed hard cell, \(X,Y\asymp T^{3/2}\) while
\(m_2,n_2,r\asymp T^{1/2}\).  The dyadic support therefore gives
\(|m_2-r|<Y\) and \(|n_2-r|<X\) for large \(T\), so (4.621zac) forces

\[
 \boxed{t=0,\qquad m_2=n_2=r.}
\tag{4.621zad}
\]

Thus the principal slow packet is exactly a partial diagonal of the
original shifted equation.  The opposite sign/order is obtained by the
corresponding left/right swap.  It should first be extracted as an
explicit resonant term and recombined with the other BBLR orderings, AFE
direction and registered boundary terms; treating it immediately by
averaged Chowla discards this stronger origin.

The finite helper `bblr_principal_incidence_solution_line` verifies
(4.621zac) and the short-support implication (4.621zad) exactly.

The partial diagonal can now be pulled completely back through the two
BBLR signs before the approximation in equation (14).  Define the exact
product coefficients

\[
 \mathcal A(u)=\sum_{am_1=u}\alpha_a
   W_1\!\left(\frac{m_1}{M_1}\right),\qquad
 \mathcal B(v)=\sum_{bn_1=v}\beta_b
   W_3\!\left(\frac{n_1}{N_1}\right).
\tag{4.621zade}
\]

On \(m_2=n_2=r\), the plus sign is \(u>v\), the minus sign is
\(u<v\), and in both cases the positive original shift is
\(h=r|u-v|\).  Therefore the two signs recombine exactly as

\[
 \boxed{
 \begin{aligned}
 \mathscr S_{\rm pd,+}+\mathscr S_{\rm pd,-}
  ={}&\sum_{r\ge1}W_2\!\left(\frac r{M_2}\right)
                    W_4\!\left(\frac r{N_2}\right)\\
    &\times\sum_{u\ne v}\mathcal A(u)\mathcal B(v)
       W_0\!\left(\frac{r|u-v|}{H}\right).
 \end{aligned}}
\tag{4.621zadf}
\]

The omitted \(u=v\) line is exactly the original \(h=0\) diagonal,
which is already accounted for before the off-diagonal BBLR problem.
There is no Poisson truncation or equation-(14) weight-replacement error
in (4.621zadf), because it is an identity inside the original
\(\mathcal S_\pm\).

At the hard scale, (4.621zadf) has
\(u,v\asymp T^{3/2}\), \(r\asymp T^{1/2}\), and hence the weight forces

\[
 |u-v|\asymp H/r\asymp T^{1/2}.
\tag{4.621zadg}
\]

Thus the principal mode is now an explicit additive-band bilinear form,
not an unspecified reciprocal-phase packet.  This alone does not make it
a reciprocal-LCM form or prove a power saving: the next exact task is to
sum its labelled copies over all AFE directions and BBLR orderings and
compare the resulting kernel with the registered diagonal and reflected
boundary.

The finite helper `bblr_partial_diagonal_correlation_sides` verifies
(4.621zade)--(4.621zadf), keeps the common second factor \(r\), partitions
every unequal product pair into exactly one sign, and records both
`analytic_afe_packet_exhaustive=False` and
`original_zeta_mollifier_coefficient_adapter_proved=False`.  The last
flag is essential: the BBLR variables in (4.621zade) are the synthetic
outer/inner slots produced by (4.601), not yet the original factors in a
finite \(\zeta_XM_N\) convolution.  The helper also records
`partial_diagonal_target_bound_proved=False`.

There is a useful but **separate** coefficient-first comparison.  If one
starts directly from the truncated product \(\zeta_XM_N\), its finite
coefficient is

\[
 c_{X,N}(u)=
 \sum_{\substack{d\mid u\\d\le N,\ u/d\le X}}
 \mu(d)\left(1-\frac{\log d}{\log N}\right).
\tag{4.621zadh}
\]

The complete identity \(c_{X,N}(u)=\Lambda(u)/\log N\) is guaranteed
only for \(u\le\min(X,N)\).  If an analytic adapter were to identify a
BBLR product at exponent \(3/2\) with this standard one-sided AFE
coefficient, then

\[
 N=T^3,\qquad X=T^{1/2},\qquad u\asymp T^{3/2},
\]

and the finite-zeta boundary would be active.  The condition \(u/d\le X\)
would force the actually present mollifier divisors into

\[
 \boxed{T\ \lesssim d\lesssim T^{3/2},}
\tag{4.621zadi}
\]

while the omitted part of the complete divisor convolution has
\(d<T\).  There is no upper mollifier-cutoff defect here because
\(u<N\).  Equivalently, the exact coefficient-first identity is

\[
 (\log N)c_{X,N}(u)
 =\Lambda(u)+
  \sum_{\substack{d\mid u\\u/d>X}}
     \mu(d)\log\frac dN,
\tag{4.621zadj}
\]

and the second term cannot be dropped at \(u\asymp T^{3/2}\) in that
coefficient-first model.  This proves that the standard one-sided AFE
coefficient at that exponent is a large-divisor Möbius tail rather than a
pure \(\Lambda\)-coefficient.  It does **not** prove that either
\(\mathcal A\) or \(\mathcal B\) in (4.621zade) equals \(c_{X,N}\): in
(4.601), the signed atoms were convolved into arbitrary BBLR outer
coefficients and the remaining unsigned cofactors occupied the inner
slots.  Recovering \(c_{X,N}\) therefore requires an explicit,
packet-exhaustive stage adapter that has not been constructed.

The exponent helper `partial_diagonal_coefficient_first_audit` records
the complete range \(1/2\), the available divisor interval \([1,3/2]\),
and `pure_von_mangoldt_replacement_valid=False`.  This agrees with the
exact formal-prime-vector identities in the independent coefficient-first
audit.  It supplies no assertion about the BBLR product coefficients and
introduces no new asymptotic assertion.

In fact, a stronger negative statement is finite and exact: there is no
**parent-free, outer-index-only** identification at the Type stage.  Recall
the grouped coefficient from (4.613),

\[
 C_U(n;u)=-\!\sum_{\substack{dey=n\\de>U,\ d\le U\\dy=u}}
              \mu(d)\mu(y).
\]

For the same cutoff \(U=3\) and the same outer product \(u=2\), direct
enumeration gives

\[
 \boxed{C_3(6;2)=1,\qquad C_3(10;2)=2.}
\tag{4.621zadj1}
\]

Indeed, for \(n=6\) only \((d,e,y)=(2,3,1)\) survives, whereas for
\(n=10\) both \((1,5,2)\) and \((2,5,1)\) survive.  Consequently there is
no function \(F_U(u)\) satisfying \(C_U(n;u)=F_U(u)\) for every admissible
parent \(n\).  Since \(c_{X,N}(u)\) is a function of \(u\) (for fixed
\(X,N\)) alone, it cannot be inserted pointwise in place of
\(C_U(n;u)\).

This does not rule out a larger analytic adapter.  It proves that any valid
one must retain the parent variable, the unsigned inner quotient, every
Type sector, and the AFE/order packet labels until the full recombination.
The finite helper `bblr_coefficient_stage_separation_witness` verifies
(4.621zadj1) and records both
`direct_outer_index_only_adapter_refuted=True` and
`packet_exhaustive_parent_aware_adapter_still_open=True`.

Retaining that missing parent coordinate exposes a positive structure.
For one Type decomposition define the common-unsigned-cofactor kernel

\[
 \boxed{
 P_U(n,m)=
 \sum_{r\mid(n,m)}
 C_U\!\left(n;\frac nr\right)
 C_U\!\left(m;\frac mr\right).}
\tag{4.621zadj2}
\]

The divisor \(r\) is exactly the unsigned inner quotient: if the signed
outer products are \(u,v\), then \(n=ur\), \(m=vr\).  Hence the direct
partial-diagonal restriction and (4.621zadj2) agree with no endpoint term:

\[
 \sum_{\substack{u\mid n,\ v\mid m\\n/u=m/v}}
 C_U(n;u)C_U(m;v)=P_U(n,m).
\tag{4.621zadj3}
\]

For arbitrary finitely supported parent weights \(A,B\), a second finite
reindexing gives the exact gcd-Gram diagonalization

\[
 \boxed{
 \begin{aligned}
 \sum_{n,m}A(n)B(m)P_U(n,m)
 =\sum_{r\ge1}
 &\left(\sum_{r\mid n}A(n)
 C_U\!\left(n;\frac nr\right)\right)\\
 {}\times&\left(\sum_{r\mid m}B(m)
 C_U\!\left(m;\frac mr\right)\right).
 \end{aligned}}
\tag{4.621zadj4}
\]

In particular, when \(A=B\), the right side of (4.621zadj4) is a sum of
squares.  For the finite witness \(U=3,n=10,m=15\), the only common active
quotient is \(r=5\), and

\[
 P_3(10,15)=C_3(10;2)C_3(15;3)=4.
\]

Thus the parent-aware core of one BBLR partial diagonal returns to the same
totient/gcd-square philosophy as the original LCM main term; it is not a
pointwise \(\zeta_XM_N\)-coefficient identification.  The finite helper
`bblr_common_unsigned_cofactor_gram_sides` verifies
(4.621zadj2)--(4.621zadj4) with exact rationals and records
`parent_and_inner_quotient_retained=True`.  Its present scope is one
supplied pair of parent-weight families.  It deliberately keeps
`analytic_bblr_packet_exhaustive=False` and `target_bound_proved=False`:
the second Möbius parent on each determinant side, the BBLR slot
permutations, all AFE/order labels, and the original smooth kernel must
still be pulled through this Gram decomposition before it becomes an
analytic bound for the full principal term.

The same arithmetic can be lifted through the second Möbius parent on each
determinant side.  Write the original parent pairs as \((p,q)\) and
\((m,n)\), with their possibly distinct Type cutoffs
\((U_p,U_q,U_m,U_n)\), and suppose the selected BBLR slot equality is
between the unsigned quotients of \(q\) and \(n\).  Put

\[
 P_{U,V}(q,n)=\sum_{r\mid(q,n)}
 C_U\!\left(q;\frac qr\right)
 C_V\!\left(n;\frac nr\right),
 \qquad P_U=P_{U,U}.
\tag{4.621zadj4a}
\]

For a supplied slot/order kernel
\(W_\omega(p,q,m,n)\) that depends on the original parents, not on a
particular Type factorization, expand all four parents by (4.614).  The
finite partial-diagonal sum is

\[
\begin{aligned}
 \mathscr D_{U,\omega}
 =\sum_{p,q,m,n}W_\omega(p,q,m,n)
 \sum_{\substack{u_p\mid p,\ u_q\mid q\\
                   u_m\mid m,\ u_n\mid n\\
                   q/u_q=n/u_n}}
 &C_{U_p}(p;u_p)C_{U_q}(q;u_q)\\
 &\times C_{U_m}(m;u_m)C_{U_n}(n;u_n).
\end{aligned}
\tag{4.621zadj5}
\]

The \(p\)- and \(m\)-factorizations are unrestricted, so (4.614) and
(4.621zadj3) give the exact recombination

\[
 \boxed{
 \mathscr D_{U,\omega}
 =\sum_{p,q,m,n}W_\omega(p,q,m,n)
   \mu(p)\mu(m)P_{U_q,U_n}(q,n).}
\tag{4.621zadj6}
\]

Here the subscript \(U\) on \(\mathscr D_{U,\omega}\) denotes the full
cutoff tuple.  There is no Type truncation or boundary error in
(4.621zadj6).  In
particular, the four artificial BBLR Type expansions reduce to two genuine
Möbius parents multiplied by one cross-Gram gcd kernel.  It is
positive-semidefinite when \(U_q=U_n\); for unequal cutoffs it is the
bilinear pairing of the two different quotient projections.  Every supplied
slot/order label \(\omega\) may be retained separately and summed only after
this recombination.

For the exact fixture \(U=3\), the labels `main/slot-2` and `dual/slot-1`
give respectively

\[
 2\,\mu(6)\mu(14)P_3(10,15)=8,
 \qquad
 -\mu(10)\mu(6)P_3(15,10)=-4,
\]

and the labelled total is \(4\).  The finite helper
`bblr_four_parent_partial_diagonal_sides` verifies the direct four-Type
sum, the two-parent recombination (4.621zadj6), and the divisor form
(4.621zadj4a) independently with exact rationals.  It also verifies the
asymmetric-cutoff fixture
\((U_p,U_q,U_m,U_n)=(2,5,3,3)\), where
\(C_5(10;2)C_3(15;3)=2\).  Thus the identity is not restricted to the
symmetric hard cell.  The helper retains every supplied slot/order label.

For the actual determinant parents, the slot permutations collapse much
further.  The two side-products in (4.496) are

\[
 b r_1-a r_2=h,
\]

and the exact support in (4.499) includes

\[
 (a,b)=1,qquad(r_1,a)=1,qquad(r_2,b)=1.
\tag{4.621zadj7}
\]

The four possible cross-side equal-inner pairings therefore have gcds

\[
 \boxed{
 \begin{array}{c|c}
 \text{paired parents}&\text{possible common inner quotient}\\ \hline
 b\leftrightarrow a&1\\
 b\leftrightarrow r_2&1\\
 r_1\leftrightarrow a&1\\
 r_1\leftrightarrow r_2&r\mid(r_1,r_2),\quad r\mid h.
 \end{array}}
\tag{4.621zadj8}
\]

The last divisibility follows immediately from
\((r_1,r_2)\mid(br_1-ar_2)\).  Thus on the hard partial-diagonal block,
where the common BBLR inner variable satisfies \(r\asymp T^{1/2}>1\), the
first three slot pairings are empty.  Only the moving--moving pairing can
survive.  Writing

\[
 r_1=rx,\qquad r_2=ry
\]

then gives the exact parent-level incidence

\[
 \boxed{h=r(bx-ay).}
\tag{4.621zadj9}
\]

This is precisely the additive-band identity behind (4.621zadf), now with
the parent coordinates identified.  In (4.621zadj6) the surviving hard
ordering is therefore

\[
 p=b,\qquad q=r_1,\qquad m=a,\qquad n=r_2,
\]

and its arithmetic coefficient is

\[
 \boxed{
 \mu(a)\mu(b)
 P_{U_{r_1},U_{r_2}}(r_1,r_2),
 \qquad r\mid h.}
\tag{4.621zadj10}
\]

The finite helper `bblr_partial_diagonal_slot_coprimality` verifies all four
gcd rows in (4.621zadj8), the divisibility by \(h\), and that only the
moving--moving pair can support a nontrivial common quotient.  This removes
the hard-scale slot-permutation ambiguity; unit-inner boundary packets from
the other three pairings still belong in the eventual full packet ledger.

For the unique hard moving--moving pairing, the zero mode can now be
extracted at the correct parent stage.  Let \(A(b,r_1)\), \(B(a,r_2)\) be
arbitrary finitely supported parent weights, and let
\(K_{\omega,r}(c)\) be the supplied kernel for packet label \(\omega\),
where

\[
 r_1=rx,\qquad r_2=ry,\qquad c=bx-ay,\qquad h=rc.
\]

For packet labels which share the same two parent weights \(A,B\), first
combine every supplied label,

\[
 K_r(c)=\sum_\omega K_{\omega,r}(c),
\tag{4.621zadj11}
\]

and extend \(K_r(0)=0\) for the already-counted original diagonal.  The
finite moving-parent master is

\[
\boxed{
\begin{aligned}
 \mathscr D_{\rm mov}
 =\sum_{r,b,a,x,y}
 &A(b,rx)B(a,ry)\mu(b)\mu(a)\\
 &\times C_{U_1}(rx;x)C_{U_2}(ry;y)K_r(bx-ay).
\end{aligned}}
\tag{4.621zadj12}
\]

Choose a cyclic modulus \(\mathfrak Q>2\max|c|\), so signed shifts do not
alias, and put

\[
 \bar K_r=\frac1{\mathfrak Q}
 \sum_{c\bmod\mathfrak Q}K_r(c),
 \qquad K_r^\circ(c)=K_r(c)-\bar K_r.
\tag{4.621zadj13}
\]

Define the two parent-aware Type projections

\[
\begin{aligned}
 L_r&=\sum_{b,r\mid r_1}A(b,r_1)\mu(b)
 C_{U_1}\!\left(r_1;\frac{r_1}{r}\right),\\
 R_r&=\sum_{a,r\mid r_2}B(a,r_2)\mu(a)
 C_{U_2}\!\left(r_2;\frac{r_2}{r}\right).
\end{aligned}
\tag{4.621zadj14}
\]

Then finite reindexing gives the exact, boundary-free split

\[
\boxed{
 \mathscr D_{\rm mov}
 =\sum_r\bar K_rL_rR_r
 +\sum_{r,b,a,x,y}
 A(b,rx)B(a,ry)\mu(b)\mu(a)
 C_{U_1}(rx;x)C_{U_2}(ry;y)K_r^\circ(bx-ay),}
\tag{4.621zadj15}
\]

with

\[
 \sum_{c\bmod\mathfrak Q}K_r^\circ(c)=0
 \qquad\text{for every }r.
\tag{4.621zadj16}
\]

The order in (4.621zadj11)--(4.621zadj13) is essential: centering each AFE
or BBLR ordering separately would delete possible cancellation among their
constant modes.  In the exact rational fixture
\((b,r_1)=(7,10)\), \((a,r_2)=(5,15)\), \(U_1=U_2=3\), the sole active
row has \(r=5,c=-1\) and parent weight \(24\).  For the two supplied
packets the aggregate cyclic mean is \(5/7\), so (4.621zadj15) reads

\[
 24=\frac{120}{7}+\frac{48}{7}.
\]

The finite helper `bblr_moving_parent_zero_mode_sides` verifies
(4.621zadj11)--(4.621zadj16), preserves all packet labels, checks
\(r\mid h\), and records `packet_sum_precedes_centering=True`.  It keeps
`analytic_afe_ordering_kernel_exhaustive=False` and
`target_bound_proved=False`: the supplied-kernel identity is complete, but
the actual signed AFE/order/reflection kernel and its means \(\bar K_r\)
have not yet been derived.

There is a second qualification: the split (4.621zadj15) is a cyclic
centering identity, not yet the canonical zero dual frequency of
(4.488).  The no-alias modulus is only constrained by
\(\mathfrak Q>2\max|c|\), and

\[
 \bar K_r^{(\mathfrak Q)}
 =\frac1{\mathfrak Q}\sum_c K_r(c)
\tag{4.621zadj16a}
\]

depends on that auxiliary choice.  For the same rational fixture,
\(\mathfrak Q=7\) and \(\mathfrak Q=11\) give respectively

\[
\begin{array}{c|c|c|c}
\mathfrak Q&\mathscr D_{\rm mov}
 &\text{constant summand}&\text{centered summand}\\ \hline
7&24&120/7&48/7\\
11&24&120/11&144/11.
\end{array}
\tag{4.621zadj16b}
\]

Both rows recombine exactly, but their constant summands differ.  Thus one
cannot make the analytic principal term small merely by enlarging
\(\mathfrak Q\): the centered term changes by the compensating amount.
More importantly, (4.621zadj16a) cannot be identified with
\(\widehat F_B(0)/|\Delta|\) from (4.489) without an additional,
canonical adapter inherited from the original Poisson variables.

The finite witness bblr_cyclic_centering_modulus_dependence_witness
verifies (4.621zadj16b) and records both
constant_summand_depends_on_auxiliary_modulus as true and
cyclic_constant_identified_with_poisson_zero_mode as false.  Hence the
first analytic priority remains the direct evaluation of the physical
Poisson \(m=0\) functional; cyclic row centering is reserved for the
subsequent dispersion identity.

That physical functional has a canonical Gram reorganization.  For
\(\Delta\ne0\), set

\[
 G_B(z):=F_B(Bz),\qquad z=(v,j).
\]

Since \(|\det B|=|\Delta|\), ordinary change of variables gives

\[
\boxed{
 \frac1{|\Delta|}\widehat F_B(0)
 =\frac1{|\Delta|}\int_{\mathbb R^2}F_B(x)\,dx
 =\int_{\mathbb R^2}G_B(v,j)\,dv\,dj.}
\tag{4.621zadj16c}
\]

Thus the determinant denominator in the zero dual frequency is exactly
the Jacobian; it is not an additional small factor after the original
\((v,j)\) coordinates are restored.  Index one entry of the expanded
square by \(e=(r,s,w)\), retain its full Möbius/taper coefficient
\(\alpha_e\), and denote its one-entry continuous kernel by \(G_e(v,j)\).
For distinct entries the primitive positive support from (4.468) makes
\(\Delta=0\) equivalent to the already registered identity pair.  Hence
the offdiagonal Poisson zero mode is

\[
\boxed{
 Z^{\rm off}_0
 =c_W(T)\sum_{e\ne f}\alpha_e\overline{\alpha_f}
   \langle G_e,G_f\rangle
 =c_W(T)\bigl(E_{\rm cont}-D_{\rm cont}\bigr),}
\tag{4.621zadj16d}
\]

where

\[
 E_{\rm cont}:=\int_{\mathbb R^2}
   \left|\sum_e\alpha_eG_e(v,j)\right|^2\,dv\,dj,
 \qquad
 D_{\rm cont}:=\sum_e|\alpha_e|^2\|G_e\|_2^2.
\tag{4.621zadj16e}
\]

The distinction between \(D_{\rm cont}\) and the original discrete
identity diagonal \(D_{\rm disc}\) is essential: the matrix \(B\) is
singular on an identity pair, so (4.488) was never applied there.
Combining the quantities only after both have been defined gives the exact
resonant ledger

\[
\boxed{
 D_{\rm disc}+Z^{\rm off}_0
 =c_W(T)E_{\rm cont}
  +\underbrace{\bigl(D_{\rm disc}-c_W(T)D_{\rm cont}\bigr)}
   _{\mathcal E_{\rm samp}}.}
\tag{4.621zadj16f}
\]

Therefore the possible residual main term has two parts: a global
continuous Gram energy, still carrying all entry Möbius signs before the
square, and a diagonal sampling correction \(\mathcal E_{\rm samp}\).
Neither term has yet been bounded at the target scale, and no equality
between the continuous and discrete diagonals is assumed.

The finite helper bblr_poisson_zero_gram_sides verifies the algebra in
(4.621zadj16d)--(4.621zadj16f).  With primitive coefficient \(5/6\),
continuous energy \(21\), continuous self diagonal \(85\), and discrete
diagonal \(90\), its two sides are both \(110/3\), while the offdiagonal
zero term is \(-160/3\) and the sampling correction is \(115/6\).  This
also proves at finite level that the offdiagonal zero mode alone is
sign-indefinite; positivity belongs to \(E_{\rm cont}\), before the
continuous self diagonal is removed.

The power ledger of (4.621zadj16f) is now asymmetric in a useful way.
The discrete identity diagonal is the diagonal-scale term already counted
in (4.465), so its exponent is two.  For one continuous self pair, use
\((v,\delta=wv-js)\) as coordinates.  Since \(s\asymp T\),

\[
 dv\,dj=\frac1s\,dv\,d\delta,
 \qquad |v|,|\delta|\ll_W T^{1/2},
\]

and the normalized continuous area has exponent zero.  Summing the
\(T^2\) entry family gives

\[
\boxed{
 \log_T D_{\rm disc}=2,\qquad
 \log_T D_{\rm cont}=2,\qquad
 \log_T E_{\rm cont}^{\rm trivial}=3.}
\tag{4.621zadj16g}
\]

Consequently

\[
\boxed{
 \text{sampling-correction power deficit}=0,\qquad
 \text{required coupled-Gram saving}=3-2=1.}
\tag{4.621zadj16h}
\]

Thus \(\mathcal E_{\rm samp}\) introduces no new positive-power
obstruction.  Its endpoint logarithmic aggregation still has to be checked,
so this statement is not yet an \(o(T^2)\) estimate.  The whole missing
power remains concentrated in \(E_{\rm cont}\), where the Möbius signs
remain inside the continuous sum before squaring.

The adapter transition_poisson_resonant_gram_audit records
(4.621zadj16g)--(4.621zadj16h), sets
sampling_correction_has_no_positive_power_obstruction to true, but keeps
endpoint_logarithmic_aggregation_closed,
continuous_mobius_gram_bound_proved, and
whole_poisson_zero_mode_covered all false.

The continuous Gram also has a useful wave-packet interpretation.  For
one primitive entry \(e=(w,s)\), its one-entry factor is supported where

\[
 |v|\ll_W T^{1/2},\qquad
 |\delta=wv-js|\ll_W T^{1/2}.
\tag{4.621zadj16i}
\]

In the \((v,j)\)-plane this is a tube around
\(j=(w/s)v\).  Its longitudinal length is \(T^{1/2}\); since
\(\partial_j\delta=-s\asymp-T\), its transverse width is
\(T^{-1/2}\).  Therefore its angular resolution is exactly

\[
 \boxed{T^{-1/2}/T^{1/2}=T^{-1}.}
\tag{4.621zadj16j}
\]

There are \(T^{2+o(1)}\) primitive directions \(w/s\) with
\(w,s\asymp T\).  Resolution (4.621zadj16j) partitions them into
\(T^{1+o(1)}\) angular clusters, each containing \(T^{1+o(1)}\)
entries.  Consequently the two possible energy ledgers are

\[
\begin{array}{c|c}
\text{cluster behavior}&\text{total exponent}\\ \hline
\text{coherent}&1+2\cdot1=3,\\
\text{square-root in each cluster}&1+1=2.
\end{array}
\tag{4.621zadj16k}
\]

The second row is exactly the target and has no spare power.  The
coefficient inside one cluster is

\[
 \boxed{\alpha_{s,w}
   =\mu(s)\mu(ks+w)\,p_N(qs)p_N(q(ks+w))
   \times\text{the retained smooth factors}.}
\tag{4.621zadj16l}
\]

Thus the remaining resonant theorem is a vector-valued two-Möbius Farey
microcluster square function.  It is not enough to prove cancellation for
a scalar count in one sector; the one-entry wave packets vary within the
cluster and their common \(L^2(v,j)\) geometry must be retained.

Here is the exact finite replacement for the informal phrase “same
cluster”.  For an integer angular resolution \(Q\geq1\), put

\[
 b_Q(w,s)=\left\lfloor {Qw\over s}\right\rfloor,
 \qquad
 \Delta_{12}=w_1s_2-w_2s_1.
\tag{4.621zadj16m}
\]

Then elementary cross multiplication gives the two implications

\[
\begin{aligned}
 b_Q(w_1,s_1)=b_Q(w_2,s_2)
   &\Longrightarrow Q|\Delta_{12}|<s_1s_2,\\
 Q|\Delta_{12}|<s_1s_2
   &\Longrightarrow
   |b_Q(w_1,s_1)-b_Q(w_2,s_2)|\leq1.
\end{aligned}
\tag{4.621zadj16n}
\]

Thus “same cluster” is not literally equivalent to the determinant
collar.  The collar is instead covered exactly by a sector and its two
neighbors, so the angular interaction graph has multiplicity at most
three.  Taking \(Q\asymp T\) recovers the scale
\(|\Delta_{12}|\ll s_1s_2/T\asymp T\) without losing a power of \(T\).
The finite adapter farey_sector_pair_ledger records (4.621zadj16m-n), and
its exhaustive small-range test checks both implications including sector
boundaries.

At the critical resolution there is a second exact simplification.  If
the dyadic upper endpoint is chosen as \(Q\), so \(s\leq Q\), the fiber
over a fixed sector and denominator is

\[
 \left\{w\in\mathbb Z:
   \left\lceil{bs\over Q}\right\rceil
   \leq w<
   \left\lceil{(b+1)s\over Q}\right\rceil\right\}.
\tag{4.621zadj16o}
\]

Its cardinality is at most \(\lceil s/Q\rceil\leq1\).  Thus one angular
microcluster is exactly a truncated Beatty graph

\[
 w=w_b(s):=\left\lceil{bs\over Q}\right\rceil,
 \qquad bs\leq Qw<(b+1)s,
\tag{4.621zadj16p}
\]

not a two-dimensional cloud.  The helper farey_sector_fiber_ledger
records the half-open endpoints in (4.621zadj16o) and the single-fiber
claim in (4.621zadj16p).

There is also an entrywise multiplicative fold.  Put \(r=ks+w\).  The
primitive support already imposes \((r,s)=1\), hence

\[
 \boxed{\mu(r)\mu(s)=\mu(rs)},\qquad n:=rs,
\tag{4.621zadj16q}
\]

and the sector condition is equivalently

\[
 (kQ+b)s^2\leq Qn<(kQ+b+1)s^2.
\tag{4.621zadj16r}
\]

The helper farey_primitive_product_coordinate_ledger verifies
(4.621zadj16q-r) with the finite Möbius function.  This does **not** turn
the continuous Gram into a scalar one-Möbius sum: the wave packet and
the two mollifier tapers still depend separately on \((r,s)\), and one
squarefree \(n\) may have several admissible divisor splits.  What has
been removed is only the claim that two independent signs remain at the
entry coefficient level.

Finally, the inter-cluster bookkeeping costs only a constant.  Let

\[
 S_b(v,j):=\sum_{e:\,b_Q(e)=b}\alpha_eG_e(v,j).
\tag{4.621zadj16s}
\]

On the critical dyadic window \(|v|\asymp_W T^{1/2}\), simultaneous
support of two packets in (4.621zadj16i) forces their slopes to differ by
\(O_W(T^{-1})\).  Thus, with a cutoff-dependent fixed widening of the
sectors, there is an integer \(R=O_W(1)\) such that
\(\langle S_b,S_c\rangle=0\) for \(|b-c|>R\).  Therefore

\[
\boxed{
 \left\|\sum_bS_b\right\|_2^2
 \leq(2R+1)\sum_b\|S_b\|_2^2.}
\tag{4.621zadj16t}
\]

Indeed, expand the left side, retain only \(|b-c|\leq R\), and use
\(2|\langle S_b,S_c\rangle|\leq\|S_b\|_2^2+\|S_c\|_2^2\).
The helper banded_sector_gram_sides verifies the expansion and (4.621zadj16t)
for exact rational vectors.  Hence the one-power problem is genuinely
intra-cluster: no additional power is hidden in the adjacent-sector cover.

There is now a useful second centering which, unlike the auxiliary kernel
centering in (4.621zadj16a), is positive Parseval.  Embed all active sector
labels without aliasing into \(\mathbb Z/M\mathbb Z\), with
\(M\asymp_W Q\asymp T\), and define

\[
 a_{\rm AFE}:=h\delta,\qquad
 \xi\in\mathbb Z/M\mathbb Z.
\]

These are different variables: the first is the original product frequency,
while \(\xi\) is only the auxiliary sector character.  In particular the
packet labels \(h,\delta\) and their signs remain inside \(S_b\).  With this
notation define

\[
 \mathcal A_\xi:=\sum_b e(\xi b/M)S_b.
\tag{4.621zadj16u}
\]

Finite character orthogonality gives the exact vector identity

\[
 \boxed{
 \sum_b\|S_b\|_2^2
 =\frac1M\sum_{\xi\bmod M}\|\mathcal A_\xi\|_2^2
 =\frac{E_{\rm cont}}M
  +\frac1M\sum_{\xi\ne0}\|\mathcal A_\xi\|_2^2.}
\tag{4.621zadj16v}
\]

The first term on the right is the original continuous Gram divided by
\(M\), because \(\mathcal A_0=\sum_bS_b\).  Put

\[
 \mathcal N_{\ne0}:=\frac1M
  \sum_{\xi\ne0}\|\mathcal A_\xi\|_2^2,
 \qquad L:=2R+1.
\tag{4.621zadj16w}
\]

Character orthogonality also splits the entry self diagonal exactly.  From
\[
 \frac1M\sum_{\xi\ne0}e(\xi(b_e-b_f)/M)
 =\mathbf1_{b_e=b_f}-\frac1M
\]
one obtains
\[
 \boxed{\mathcal N_{\ne0}=\left(1-\frac1M\right)D_{\rm cont}+\mathcal N_{\ne0}^{\rm off},}
\tag{4.621zadj16w-diag}
\]
where
\[
 \mathcal N_{\ne0}^{\rm off}
 :=\sum_{e\ne f}\alpha_e\overline{\alpha_f}
 \left(\mathbf1_{b_e=b_f}-\frac1M\right)
 \langle G_e,G_f\rangle.
\tag{4.621zadj16w-off}
\]
Thus sector_character_is_trivial_on_entry_diagonal: every character phase
cancels when \(e=f\), and the nonprincipal average retains the factor
\(1-1/M\).  This is useful rather than harmful because (4.621zadj16g)
already places \(D_{\rm cont}\) at the target exponent \(2\).  After the
one-factor Type expansion, the primitive
\(\Delta_{\rm Type}=r_1s_2-r_2s_1=0\) terms in the enlarged factorization
recombine exactly to this same original-entry diagonal by (4.621zadj16z).
They are not a new Type-II diagonal loss.

When supplied the original_entry_ids, the finite helper
sector_character_parseval_sides first recombines all outer packets on one
original \((r,s)\) entry and then records the three quantities in
(4.621zadj16w-diag).  The labelled helper
labelled_type_zero_determinant_recombination retains every
\((h,\delta,\nu,\sigma)\) packet while recombining all \(dm=r\) cross
factorizations.  The latter identity does not estimate the different
outer packets on one entry.  It proves only that the remaining
positive-power Type obstruction lies in the \(e\ne f\), equivalently
\(\Delta_{\rm Type}\ne0\), part after the original-entry packets have been
recombined.

Combining (4.621zadj16t) and (4.621zadj16v) gives

\[
 \left(1-\frac LM\right)E_{\rm cont}
 \leq L\mathcal N_{\ne0}.
\tag{4.621zadj16x}
\]

Since \(L=O_W(1)\) and \(M\asymp T\), one may take \(M\geq2L\) and
absorb the sector principal character:

\[
 \boxed{E_{\rm cont}\leq2L\mathcal N_{\ne0}.}
\tag{4.621zadj16y}
\]

Thus the physical Poisson zero mode does **not** leave a second
uncontrolled angular zero frequency.  After the exact Gram
reorganization, its sector-principal copy is a factor \(M^{-1}\) of the
same unknown energy and moves to the left.  The remaining resonant gate is
the nonzero angular-character square function in (4.621zadj16w).

The helpers sector_character_parseval_sides and
sector_principal_absorption_audit verify (4.621zadj16v-x) over exact
rational vectors.  In the fixture \(M=7,R=1\), the feedback coefficient
is \(3/7\) and the exact nonprincipal multiplier is \(21/4<6=2L\).

The first exact Type decomposition can now be made after, rather than
before, this principal-mode absorption.  In every prime-log coordinate,

\[
 \boxed{-\mu(r)\log r
 =\sum_{dm=r}\mu(d)\Lambda(m).}
\tag{4.621zadj16z}
\]

Indeed, the coefficient of \(\log p\) on the left is
\(-\mu(r)v_p(r)\), while that on the right is

\[
 \sum_{1\leq \nu\leq v_p(r)}\mu(r/p^\nu).
\tag{4.621zadj16aa}
\]

These integers agree even when \(r\) is not squarefree.  On the unique
Beatty fiber \(r_b(s)=ks+w_b(s)\), absorb \(1/\log r_b(s)\) into the
smooth packet and write it as \(\widetilde G_{b,s}\).  Then every nonzero
sector character has the exact form

\[
\boxed{
 \mathcal A_\xi
 =-\sum_b e(\xi b/M)\sum_s\mu(s)
   \sum_{dm=r_b(s)}\mu(d)\Lambda(m)
   \widetilde G_{b,s},
 \qquad \xi\ne0.}
\tag{4.621zadj16ab}
\]

No Cauchy--Schwarz or absolute value occurs in (4.621zadj16ab).  The
first Möbius factor \(\mu(s)\), the angular character \(\xi\), the original
\(a_{\rm AFE}=h\delta\) packet labels, the relation
\(dm=ks+w_b(s)\), both mollifier tapers, and the vector packet are all
retained.  A dyadic split \(d\asymp D,m\asymp P,DP\asymp T\) now has the
usual exact alternatives: an extreme Type-I range with one of \(D,P\)
short, and a balanced Type-II range.  Merely applying (4.621zadj16z)
does not estimate either range; its purpose is to expose the prime-bearing
variable before the one global dispersion step.

The helper mobius_log_derivative_prime_coordinate_identity verifies
(4.621zadj16z-aa) for arbitrary finite integers without floating
logarithms.  The helper farey_single_mobius_type_identity additionally
checks the unique sector fiber and records all
\((d,m,\mu(s),\mu(d),p)\) terms with \(m=p^\nu\).  Neither helper marks
the nonzero-character Type-I/II estimate as proved.

Nonzero sector frequency must not itself be counted as a saving.  Put

\[
 C_u:=\sum_b\langle S_{b+u},S_b\rangle .
\tag{4.621zadj16ac}
\]

Then the same finite expansion gives

\[
 \|\mathcal A_\xi\|_2^2
 =\sum_{|u|\leq R}e(\xi u/M)C_u.
\tag{4.621zadj16ad}
\]

This is a trigonometric polynomial of fixed degree \(R\), not a quantity
which decays automatically as \(|a|\) grows.  In the finite fixture where
the nonzero \(S_b\) are mutually orthogonal, \(C_0=\sum_b\|S_b\|_2^2\)
and every \(C_u\) with \(u\ne0\) vanishes, so
\(\|\mathcal A_\xi\|_2^2=C_0\) for **every** character, including all
\(\xi\ne0\).  The helper sector_character_correlation_coefficients records
this exact counterexample.  Hence (4.621zadj16y) removes the principal
feedback but does not manufacture the remaining power saving; that saving
must arise inside (4.621zadj16ab), before Cauchy--Schwarz, from the retained
Möbius/prime-bearing variables.

The horocycle/Farey result of
[Panti](https://arxiv.org/abs/1503.02539) permits piecewise-smooth
denominator weights and derives macroscopic gap distributions.  It does
not state a microscopic \(T^{-1}\)-angular square function with the
moving product \(\mu(s)\mu(ks+w)\).  Likewise, one-Möbius nilsequence
orthogonality does not permit the second Möbius factor to move with the
same cluster.  No audited published result therefore supplies the second
row of (4.621zadj16k).

Fourier expansion of the strip variable does make additive Möbius
polynomials reappear: with
\(x=v/T^{1/2}\), \(y=(kv+j)/T^{1/2}\), the phase separates into a
product of sums at frequencies \(tx\) and \(-ty\).  This refines the
earlier interface audit of Verjovsky's additive polynomial, but does not
change its proof status: the required subpolynomial local moments in that
paper are equivalent to RH, not an unconditional estimate.  Moreover the
present \(t\)-integral and vector-valued weights have not been reduced to
its fixed \(c/N\)-arc functional.

The adapter transition_poisson_tube_cluster_audit records the tube scales,
the \(T\)-by-\(T\) cluster ledger, the exact coefficient (4.621zadj16l),
the bounded-neighbor correction (4.621zadj16n), and the zero square-root
margin.  It also records the exact Beatty fiber (4.621zadj16p), the
entrywise product fold (4.621zadj16q), and the surviving vector-kernel
obstruction.  It keeps
requires_vector_valued_two_mobius_cancellation true and
published_coverage false.

Section 4.60 already supplies one part of that analytic bridge.  Its
five-variable Fourier inversion writes the actual lifted zero-mode weight
as an exact signed superposition of separated tensors, with only a
polylogarithmic nuclear norm.  On one such tensor,

\[
 A(b,r_1)=U(b)V_1(r_1),\qquad
 B(a,r_2)=\widetilde U(a)V_2(r_2).
\tag{4.621zadj17}
\]

Consequently the parent projections in (4.621zadj14) factor exactly:

\[
\boxed{
\begin{aligned}
 L_r&=
 \left(\sum_b\mu(b)U(b)\right)
 \left(\sum_{r\mid r_1}V_1(r_1)
 C_{U_1}\!\left(r_1;\frac{r_1}{r}\right)\right),\\
 R_r&=
 \left(\sum_a\mu(a)\widetilde U(a)\right)
 \left(\sum_{r\mid r_2}V_2(r_2)
 C_{U_2}\!\left(r_2;\frac{r_2}{r}\right)\right).
\end{aligned}}
\tag{4.621zadj18}
\]

Thus the constant part of one separated tensor is

\[
\boxed{
 \left(\sum_b\mu(b)U(b)\right)
 \left(\sum_a\mu(a)\widetilde U(a)\right)
 \sum_r\bar K_rD_{1,r}D_{2,r},}
\tag{4.621zadj19}
\]

where \(D_{j,r}\) denotes the corresponding moving common-cofactor
projection.  The finite helper `bblr_tensor_parent_projection_sides`
verifies (4.621zadj18) directly and records
`static_mertens_factors_remain=True`.

There is an important qualification when (4.621zadj15) is passed through
the Fourier inversion of Section 4.60.  Distinct Fourier labels generally
have distinct one-variable parent weights.  Write them as
\(A_\omega,B_\omega\), and define \(L_{\omega,r},R_{\omega,r}\) from
(4.621zadj14) with those weights.  Then one may not first replace the
kernels by \(\sum_\omega K_{\omega,r}\).  The correct finite identity is

\[
\boxed{
 \mathscr D_{\rm tens}
 =\sum_{\omega,r}\bar K_{\omega,r}
    L_{\omega,r}R_{\omega,r}
  +\sum_\omega \mathscr D^\circ_\omega.}
\tag{4.621zadj19a}
\]

Here every \(K^\circ_{\omega,r}=K_{\omega,r}-\bar K_{\omega,r}\) has
zero cyclic row sum.  Consequently

\[
 \sum_\omega\bar K_{\omega,r}=0
 \quad\not\Longrightarrow\quad
 \sum_\omega\bar K_{\omega,r}
 L_{\omega,r}R_{\omega,r}=0
\tag{4.621zadj19b}
\]

unless the parent projections are common (or a stronger weighted
cancellation is proved).  This is exactly the distinction between AFE or
ordering packets which genuinely share parent weights and the continuous
Fourier tensors whose weights depend on the Fourier parameter.

An exact rational counterexample uses modulus \(7\), the parent rows from
the preceding fixture, and two labels.  Give the first label parent weight
\(24\) and kernel mean \(1/7\), and the second parent weight \(48\) and
kernel mean \(-1/7\).  Then the aggregate unweighted kernel mean is zero,
but the actual constant mode is

\[
 \boxed{24\cdot\frac17+48\cdot\left(-\frac17\right)
 =-\frac{24}{7}\ne0.}
\tag{4.621zadj19c}
\]

The helper `bblr_labelled_tensor_zero_mode_sides` verifies
(4.621zadj19a)--(4.621zadj19c), including the full split
\(-24=-24/7-144/7\).  It records
`aggregate_kernel_means_vanish=True` but
`weighted_constant_mode_vanishes=False`.  Thus the next analytic object is
not the unweighted mean of the reconstructed kernel: it is the complete
weighted functional in the first term of (4.621zadj19a).

Equation (4.621zadj19) explains both the gain and the remaining obstruction.
The moving parents have returned to a gcd/Gram divisor structure, but two
one-variable smooth Mertens factors remain.  On the top face they have
length \(A=T\).  Bounding every Fourier tensor and ordering separately
would therefore require the fixed half-power product saving already
isolated in (4.533); classical zero-free-region estimates provide
subpower/logarithmic decay, not that power.  This is a no-go statement for
termwise absolute values, not for the original signed superposition:
cancellation among Fourier tensors, AFE directions, orderings, or the
means \(\bar K_r\) may still remove the constant component before those
Mertens factors are majorized.

The remaining adapter boundary is now narrower.  BBLR introduces dyadic
weights that depend separately on its synthetic outer and inner slots.  To
apply (4.621zadj6) to the analytic principal term, one must first sum the
complete Type dyadic partitions and every slot permutation and prove that
their signed weight is the pullback of a kernel
\(W_\omega(p,q,m,n)\) on the original parents.  This packet-exhaustion
identity has not yet been written, so the helper records
`analytic_afe_packet_exhaustive=False` and `target_bound_proved=False`.

The dangerous additive principal mode can nevertheless be isolated
without estimating it.  Embed one finite product box in
\(\mathbb Z/\mathfrak Q\mathbb Z\), with \(\mathfrak Q\) larger than
twice the product cutoff so that signed shifts do not alias, and extend
the diagonal-excluded shift
kernel by \(K(0)=0\), and first sum every labelled AFE direction and BBLR
ordering with its sign.  Put

\[
 \bar K=\frac1{\mathfrak Q}\sum_{c\bmod\mathfrak Q}K(c),
 \qquad K^\circ(c)=K(c)-\bar K.
\tag{4.621zadk}
\]

Then \(\sum_cK^\circ(c)=0\) and exact cyclic reindexing gives

\[
 \boxed{
 \begin{aligned}
 \sum_{u,v}\mathcal A(u)\mathcal B(v)K(u-v)
 ={}&\bar K
   \left(\sum_u\mathcal A(u)\right)
   \left(\sum_v\mathcal B(v)\right)\\
 &+\sum_{u,v}\mathcal A(u)\mathcal B(v)K^\circ(u-v).
 \end{aligned}}
\tag{4.621zadl}
\]

Thus the partial diagonal has its own explicit constant Fourier mode and
a genuinely zero-mean additive remainder.  The next analytic stage has a
sharp trichotomy:

1. the fully derived AFE/ordering kernel satisfies \(\bar K=0\);
2. the first term of (4.621zadl) cancels a registered diagonal or boundary
   term;
3. it is a secondary main term that must be retained and bounded or added
   to the asymptotic.

No one of these alternatives is assumed.  In particular, centering each
ordering separately would be invalid because their constant modes may
cancel only after the signed packet sum.

The finite helper `additive_band_zero_mode_sides` verifies (4.621zadk)--
(4.621zadl) with exact rationals, retains every supplied packet label, and
keeps `analytic_afe_ordering_kernel_derived=False`.

The BBLR integration scale is exactly \(x\asymp T^{-1}\), matching
\(r_0/Y\).  Restricting to
\(|r-r_0|\le Y/(12L)\) leaves \(\asymp T^{1/2}\) values of \(r\), and
for every \(l\le L\asymp T\),

\[
 \left|\frac{l(r_0-r)}Y\right|\le\frac1{12}.
\]

All these unit-coefficient phases therefore have real part at least
\(1/2\).  The resulting coherent local packet has size

\[
 \boxed{T^{1/2}\cdot T=T^{3/2}.}
\tag{4.621zc}
\]

Thus a local absolute-value treatment of \((h,l)\) saves only
\(T^{1/2}\) from the raw \(HL=T^2\), whereas the hard cell needs the full
\(T\)-saving.  The same missing \(T^{1/2}\) survives.  Any successful
argument must average this near-diagonal incidence over \(X,Y\), retain
the Möbius outer coefficients, or prove cancellation between the signed
phase classes before taking absolute values.

This is not a lower bound for the original signed remainder: its other
\(X,Y\) rows and Möbius coefficients may cancel the packet.  It is a
no-go certificate only for a uniform local \((h,l)\)-completion bound.
The finite helper `bblr_near_diagonal_resonance_certificate` verifies
(4.621zaa)--(4.621zb), the coherent phase arc, and its half-plane lower
bound with exact rational arithmetic.  The helper
`bblr_gap_resonance_coordinates` verifies the full inverse-free split
(4.621za) and records whether \(k=0\) or \(k\ne0\).

This resonance also gives a sharper model for the next analytic input.
With \(Q=Y\asymp T^{3/2}\) and \(C=c\asymp T^{1/2}=Q^{1/3}\), the
outer-coefficient portion has the shifted shape

\[
 \mathfrak C_d(Q,C)
 =\sum_{c\asymp C}\sum_{Y\asymp Q}
   A_d(Y+c)B_d(Y)\Omega_d(c,Y).
\tag{4.621zd}
\]

For every supplied finite labelled BBLR packet, this is now an exact
partition rather than a schematic change of variables.  First convolve all
left and right Type factorizations into \(A_d(X)\) and \(B_d(Y)\), and only
then split by \(c=X-Y\).  For any fixed positive window
\(C_1\le c\le C_2\), finite reindexing gives

\[
 \mathscr S_{\rm BBLR}^{\ne0}
 =\mathscr S_{C_1\le X-Y\le C_2}
  +\mathscr S_{X=Y}
  +\mathscr S_{\rm complement},
\tag{4.621zda}
\]

where

\[
 \mathscr S_{C_1\le X-Y\le C_2}
 =\sum_d\sum_{C_1\le c\le C_2}\sum_Y
   A_d(Y+c)B_d(Y)
   \sum_{h,\delta}\sum_{l\ne0}
   \mathscr W(d,Y+c,Y;h,\delta,l).
\tag{4.621zdb}
\]

No absolute value occurs between the Type sectors, and all
\(h,\delta,l,h\delta,hl\) labels are retained.  The finite helper
`bblr_near_diagonal_outer_correlation_sides` verifies
(4.621zda)--(4.621zdb) exactly.  Its status field
`original_coupled_kernel_stage_exhaustive=False` remains essential:
the identity is exhaustive for the supplied packet, not yet for the
original analytic remainder.  Inside the positive gap window the same
helper also partitions exactly into the principal incidence \(k=0\) and
the nonprincipal determinant family \(k\ne0\), before either family is
majorized.  This is the finite version of “extract the resonant main arc,
then estimate the centered remainder”; neither resulting analytic bound is
being assumed.

If the partial diagonal in (4.621zad) is majorized instead of explicitly
recombined, then after the coherent \((h,l)\)-packet has spent only half
of the required saving, the missing factor is \(C=Q^{1/3}\).  The
resulting conservative model target is

\[
 \boxed{\mathfrak C_d(Q,C)\ll Q^{1+\varepsilon}}
 \qquad(C=Q^{1/3}),
\tag{4.621ze}
\]

against the absolute size \(CQ=Q^{4/3}\).  Equation (4.621ze) is therefore
a fallback sufficient bound, not the preferred treatment of \(k=0\).
It is not yet an exact
replacement gate because the BBLR stage map, all \(d\)-weights and all
Type sectors still have to be recombined.  It does explain why ordinary
averaged Chowla does not finish the argument: even for literal Möbius
coefficients, the quantitative decay in
[Matomäki--Radziwiłł--Tao, Theorem 1.6](https://arxiv.org/abs/1503.05121)
is logarithmic (roughly \(\log\log C/\log C\)), not the power
\(C^{-1}=Q^{-1/3}\) required by (4.621ze).  Moreover the actual
\(A_d,B_d\) in (4.621j) are divisor-convolved outer coefficients, so that
the theorem is not directly applicable even at its stated strength.

### 4.69 Kim's 2026 ternary-correlation theorem enters the shift range but not the gate

The recent circle-method theorem of
[Jiseong Kim, Theorem 1.6](https://arxiv.org/abs/2603.23250) has a Fejér
shift average close to the exact correlation shape in (9.353) of the
Type-I/II note.  It is therefore necessary to audit both its power and its
coefficient class rather than dismiss it from the title alone.

Use (X_0=T^3) and (H_0=T^2=X_0^{2/3}).  In the theorem's
(alpha=0) case, its range and error have the form

\[
 H_0\gg X_0^{1/2+100\varepsilon_K},
 \qquad
 E_K\ll X_0H_0^{1-\varepsilon_K/2}.
\tag{4.622}
\]

The range in (4.622) forces the strict ceiling

\[
 \varepsilon_K<\frac{2/3-1/2}{100}=\frac1{600}.
\tag{4.623}
\]

Measured in the present (T)-exponents, the ambient shifted sum has
exponent (3+2=5), while the coupled target is (9/2).  Even at the
unattained endpoint of (4.623), Kim's error saves only

\[
 \frac{2\varepsilon_K}{2}<\frac1{600},
 \qquad
 \boxed{
 \frac12-\frac1{600}=\frac{299}{600}}
\tag{4.624}
\]

of the required half-power.  Thus its numerical strength is insufficient
even before checking hypotheses.

The coefficient obstruction is independent and decisive.  Definition 1.1
requires the associated twists (L(f,\chi,s)) to be holomorphic in
(Re s>1/2) and to satisfy a critical-line second moment.  For Möbius,
up to the standard imprimitive Euler factors,

\[
 L(\mu,\chi,s)=\sum_{n\ge1}\frac{\mu(n)\chi(n)}{n^s}
 =\frac1{L(s,\chi)}.
\tag{4.625}
\]

Zeros of (L(s,\chi)) produce poles in the required open half-plane
unconditionally.  Assuming GRH moves them to the boundary but does not
create the demanded critical-line (L^2) integral: the square of a simple
reciprocal pole is not locally integrable.  Kim's separate discussion of a
GRH bound for Möbius exponential sums is not an assertion that Möbius lies
in the class of Definition 1.1.

Finally, the dyadically weighted coefficients in (9.352) are not one fixed
multiplicative function.  Full outer-scale recombination can recover a
Möbius coefficient, but that returns exactly the reciprocal-(L) failure
in (4.625).  Consequently

\[
 \boxed{
 \text{Kim 2026: shift length enters; power and coefficient hypotheses fail.}}
\tag{4.626}
\]

The adapter `transition_kim_ternary_correlation_audit` records
(4.622)--(4.624) with exact fractions and keeps separate false flags for
holomorphy, the critical-line second moment, the dyadic multiplicative
coefficient, theorem applicability, and coupled-gate coverage.  This is a
new published-estimate row, not a replacement gate.

### 4.70 Doyle's 2026 short k-free theorem crosses the length line in the wrong direction

The top balanced-variance cell (4.540) has product centre (N=T^2) and
short interval (K=T=N^{1/2}).  Ben Doyle's new
[Lemma 1.2, Theorem 1.7, and Corollary 1.8](https://arxiv.org/abs/2608.16679)
therefore deserve a literal endpoint check.  For (k=2), the middle-part
exponent in that paper is

\[
 \delta_2=\frac{105}{317},
 \qquad
 \frac32\delta_2=\frac{315}{634}
 =0.496845\ldots .
\tag{4.627}
\]

Thus its Möbius corollary applies for
(K\gg N^{315/634+\varepsilon}).  The interval exponent in (4.540)
does enter this range, by the exact margin

\[
 \boxed{\frac12-\frac{315}{634}=\frac1{317}.}
\tag{4.628}
\]

This is genuine length coverage, but not analytic coverage of the gate.
The Möbius conclusion of Theorem 1.7 is the lower bound

\[
 \int_0^1\left|\sum_{N-K<n\le N}\mu(n)e(n\alpha)\right|d\alpha
 \gg K^{1/6},
\tag{4.629}
\]

whereas (4.540) requires an **upper** short-interval (L^2) variance for
the balanced convolution (c_{U,V}).  Reversing (4.629) is impossible.
The estimate which drives Doyle's theorem also concerns the different
middle coefficient

\[
 c_n(y,z)=\sum_{\substack{y<d\le z\\d^2\mid n}}\mu(d),
\tag{4.630}
\]

with one Möbius weight on square divisors.  It is not the two-Möbius
product-divisor coefficient

\[
 c_{U,V}(n)=\sum_{ar=n}\mu(a)\mu(r)U(a/T)V(r/T)
\tag{4.631}
\]

in (4.535).  Therefore neither Lemma 1.2 nor the Möbius (L^1) corollary
can be substituted into (4.540):

\[
 \boxed{
 \text{Doyle 2026: the length threshold enters by }N^{1/317},
 \text{ but conclusion and coefficient both mismatch.}}
\tag{4.632}
\]

The exact adapter `transition_doyle_kfree_moment_audit` records the
fractions in (4.627)--(4.628), the lower-versus-upper direction, and the
square-divisor-versus-balanced-convolution distinction.  It keeps
`theorem_applies_to_actual_packet=False` and
`whole_line_family_covered=False`.  This closes another tempting 2026
paper route without weakening the residual gate.

### 4.71 The 2026 Bessel-Kuznetsov phase transition misses the exact degenerate orbit

Yuhang Shi's recent
[Theorem 1.1](https://arxiv.org/abs/2608.13232) studies the classical
Bessel--Kuznetsov transform of
(phi(x)=W(x)e(alpha x)), with (W) supported on a positive dyadic
interval ([X,2X]).  It proves rapid spectral decay for
(alpha\leq1/(2pi)) and a localized stationary main term above that
threshold.  This is potentially relevant only after checking the actual
Bessel argument of the determinant orbit.

For the ordinary nondegenerate Kloosterman term (S(m_2,m_1;c)), that
argument is proportional to

\[
 x_{\rm Bes}=\frac{4\pi\sqrt{|m_1m_2|}}{c}.
\tag{4.633}
\]

But the exact substitution in (4.134) is

\[
 (m_2,m_1;c)=(0,-h;s),
 \qquad
 S(m_2,m_1;c)=S(0,-h;\delta;s).
\tag{4.634}
\]

Therefore

\[
 \boxed{x_{\rm Bes}=0.}
\tag{4.635}
\]

This is the degenerate Ramanujan/Eisenstein orbit, not a positive-dyadic
Bessel transform.  Consequently there is no actual (alpha) to compare
with (1/(2pi)), and the subcritical rapid-decay conclusion cannot be
inserted into (4.132).

After Cauchy and a second completion, some determinant formulas contain
two nonzero formal Fourier indices.  That does not rescue this application:
Sections 4.15--4.16 and 4.46 already record that no classical
nondegenerate Kuznetsov transform from the entry-weighted QCT kernel has
been derived, and the two Möbius weights remain on matrix entries rather
than the standard Fourier indices.  Thus

\[
 \boxed{
 \text{Shi 2026: a useful transform theorem, but the exact orbit has }
 x_{\rm Bes}=0.}
\tag{4.636}
\]

The adapter `transition_shi_bessel_kuznetsov_audit` records both Fourier
indices, the zero argument, the missing linear-twist identification, and
the missing nondegenerate adapter.  It keeps
`subcritical_rapid_decay_applies=False` and
`whole_line_family_covered=False`.  A different relative trace formula
could still create a nondegenerate transform, but proving that formula is
itself part of the unresolved coupled-kernel problem.

### 4.72 Beatty two-point Chowla is qualitative and fixed-slope

The exact Beatty fiber (4.621zadj16p) makes the closest published
multiplicative-correlation theorem easy to identify.  A scalar projection
of one cluster contains

\[
 c_{b,Q,k}(s)
 =\mu(s)\mu\!\left(
   \left\lfloor
    \left(k+\frac bQ\right)s+\frac{Q-1}{Q}
   \right\rfloor\right),
 \qquad
 \frac{\alpha_2}{\alpha_1}=k+\frac bQ\in\mathbb Q.
\tag{4.637}
\]

Teräväinen--Walker's
[two-point theorem](https://arxiv.org/abs/2303.12574),
arXiv:2303.12574, is genuinely
structurally relevant.  It proves logarithmically averaged independence
for fixed Beatty slopes in the irrational-ratio case and describes a
possible nonzero resonant locus in the rational-ratio Liouville case.
The latter feature is consistent with first extracting the exact
\(\Delta_{\rm Type}=0\) term in (4.621zadj16w-diag), rather than assuming
that every Beatty correlation is centered.

It does not provide the estimate needed here.  Formula (4.637) is a
moving rational slope family with \(Q\asymp T\) and \(b\) ranging over
\(\asymp T\) sectors.  The theorem gives only a qualitative conclusion:
logarithmic limit, not a uniform power-saving estimate.  It neither
supplies the natural
dyadic bound

\[
 \left|\sum_{s\asymp T}c_{b,Q,k}(s)W_{b,Q}(s)\right|
 \ll T^{1/2+\varepsilon}
\tag{4.638}
\]

uniformly in \((b,Q)\), nor its stronger vector-valued cluster-square
version with all \(h,\delta,\nu,\sigma\) packets.  Its proof also allows
fixed Bohr data before the limit; the complexity here grows with \(T\).
Thus it validates the resonant/offdiagonal ordering but does not cover
the \(\Delta_{\rm Type}\ne0\) gate.

The older multiplicative-function theorem of
[Güloğlu--Nevans](https://arxiv.org/abs/0801.2796) assumes a fixed
irrational slope of finite type, while
[Technau's Kloosterman--Beatty theorem](https://arxiv.org/abs/1808.00413)
estimates inverse additive phases on a fixed irrational Beatty set.
Neither theorem accepts the moving rational two-Möbius vector family
(4.637).  The remaining plausible quantitative target is therefore an
average over \(b\), \(Q\), and nonzero \(\Delta_{\rm Type}\), not a
pointwise invocation of an existing Beatty theorem.

### 4.73 Global sector reassembly before the one-factor Type split

The critical condition \(s\le Q\) gives more than a pointwise Beatty
description.  Put

\[
 b_Q(w,s):=\left\lfloor\frac{Qw}{s}\right\rfloor.
\tag{4.639}
\]

Then the nonempty fibers in (4.621zadj16p) form the exact disjoint union

\[
 \boxed{
 \bigsqcup_{0\le b<Q}
 \{w\in\mathbb Z:bs\le Qw<(b+1)s\}
 =\{0,1,\ldots,s-1\}.}
\tag{4.640}
\]

Indeed, consecutive values of \(Qw/s\) differ by at least one, so every
fiber contains at most one integer, while \(b_Q(w,s)\) assigns each
\(0\le w<s\) to exactly one sector.  Restricting to primitive entries
simply adds \((w,s)=1\), since \((ks+w,s)=(w,s)\).

Consequently the complete nonprincipal Type packet can be reassembled
before evaluating its character:

\[
\boxed{
 \begin{aligned}
 \mathcal A_\xi
 ={}-&\sum_s\sum_{\substack{0\le w<s\\(w,s)=1}}
 e\!\left(\frac{\xi b_Q(w,s)}Q\right)
 \mu(s)\mu^2(ks+w)\\
 &\times\sum_{dm=ks+w}\mu(d)\Lambda(m)
 \widetilde G_{s,w;h,\delta,\nu,\sigma},
 \qquad 0<\xi<Q.
 \end{aligned}}
\tag{4.641}
\]

This is (4.621zadj16ab) after summing all sectors and inserting the
harmless original squarefree-support indicator, not a new estimate.
It is nevertheless the correct pre-Cauchy Type identity: the phase label
\(b_Q(w,s)\), both Möbius weights \(\mu(s)\mu(d)\), the prime-bearing
factor \(\Lambda(m)\), the original \(a_{\rm AFE}=h\delta\), and every
vector packet label remain in the same summand.

For a cutoff \(U\ge1\), define Type I by \(\min(d,m)\le U\) and Type II
by \(d,m>U\).  This is an exact partition:

\[
 \mathcal A_\xi=\mathcal A_\xi^{\rm I}
                  +\mathcal A_\xi^{\rm II},
 \qquad \mathcal E_{\rm Type}=0.
\tag{4.642}
\]

On \(dm\asymp T\), the choice \(U=T^{1/3}\) puts every Type-II factor in

\[
 T^{1/3}<d,m\ll T^{2/3}.
\tag{4.643}
\]

There is an additional simplification on the actual mollifier support.
Since \(\mu(ks+w)\ne0\), the numerator is squarefree.  Therefore a divisor
\(m\mid ks+w\) with \(\Lambda(m)\ne0\) is a prime, not a higher prime
power.  The genuine central packet is thus

\[
 \boxed{
 \mu(s)\mu(d)\log p,qquad dp=ks+w,qquad
 T^{1/3}<d,p\ll T^{2/3},}
\tag{4.644}
\]

with the sector character and \(h\delta\) packet still attached.  Hence
the remaining Type-II problem is a vector-valued
Möbius--Möbius--prime dispersion estimate.  Replacing it by arbitrary
three-variable coefficients discards precisely the structure exposed by
the one-factor identity.

In the transition normalization there are \(T\) angular clusters and
\(T\) entries per cluster.  Coherent energy therefore has exponent three,
whereas the required square function has exponent two.  A sufficient
separate pair of estimates is

\[
 \boxed{
 \frac1Q\sum_{0<\xi<Q}\|\mathcal A_\xi^{X}\|_2^2
 \ll_{\varepsilon,W}T^{2+\varepsilon},
 \qquad X\in\{\mathrm I,\mathrm {II}\}.}
\tag{4.645}
\]

Each row of (4.645) must save one full power in energy, equivalently
\(T^{1/2}\) before squaring.  The exact post-Type published-coverage table
is:

| input | matching structure | quantitative saving | coverage of (4.645) |
|---|---|---:|---|
| Teräväinen--Walker, arXiv:2303.12574 | two multiplicative functions on fixed Beatty data | qualitative logarithmic limit | no |
| [Tao--Teräväinen](https://arxiv.org/abs/2107.02158) | quantitative Möbius/\(\Lambda\) Gowers uniformity for fixed-complexity linear systems | \((\log\log T)^{-c}\), power exponent \(0\) | no |
| [Banks--Shparlinski](https://arxiv.org/abs/0708.1015) | primes in a fixed irrational finite-type Beatty sequence | power error in a one-prime problem | no double Möbius and no moving rational family |
| [Lichtman](https://arxiv.org/abs/2009.08969), Theorem 1.1 | \(L^1\) average of scalar shifted-prime Möbius sums | \((\log T)^{-1/3+\delta}\), power exponent \(0\) | no moving Farey/AFE weight, no endpoint \(H\asymp X\), and no vector \(L^2\) half-power |
| [Technau--Zafeiropoulos](https://arxiv.org/abs/1907.06050), Theorem 2.1 and Corollary 4.4 | square-root \(L^2\) error for one fixed arithmetic function in a continuous/metric Beatty slope | structured Sobolev sampling reaches the rational grid with \(T^\varepsilon\) loss, but no slope-independent Hilbert family has been derived from the second Möbius packet | no |
| Kim, arXiv:2603.23250 | ternary shifted correlations | saving \(<T^{1/600}\) in the entering range | short by \(T^{299/600}\), Möbius hypothesis also fails |

Thus (4.644) narrows the coefficient class but does not turn a logarithmic
uniformity theorem into the half-power required by (4.645).  The remaining
analytic target is a joint average over \(\xi,Q\) and the nonzero Type
determinant, with both Möbius signs left inside the operator.

The finite helper `farey_global_mobius_type_partition` verifies
(4.640)--(4.642) simultaneously for all supplied denominators.  It checks
the log identity prime-coordinate by prime-coordinate, records the exact
Type-I and Type-II term lists, and carries the nonzero character,
\(h,\delta,h\delta\), and packet label on every term.  Its
`type_estimate_proved` field remains false: neither (4.643) nor the prime
specialization (4.644) supplies the required half-power cancellation.
The companion `farey_global_type_scale_ledger` records the four factor
ranges and the exact energy/amplitude deficits in (4.645); both Type-bound
flags remain false.

### 4.74 The unit-divisor Type-I face is a moving-weight shifted-prime sum

The most favorable Type-I subpacket is \(d=1\).  It is worth isolating it
because it is the one place where the shifted-prime literature looks
closest to the actual coefficient.  On squarefree support the prime factor
identity gives \(p=ks+w\).  For the unit-slope face \(k=1\), (4.641) becomes

\[
 \boxed{
 \begin{aligned}
 \mathcal A^{\mathrm{I},d=1}_{\xi,k=1}
 ={}-&\sum_w\sum_{\substack{p:\ s=p-w\\0\le w<s\\p\ {\rm prime}}}
 e\!\left(
   \frac{\xi\lfloor Qw/(p-w)\rfloor}{Q}
  \right)\mu(p-w)\log p\\
 &\hspace{36mm}\times
 \widetilde G_{p-w,w;h,\delta,\nu,\sigma}.
 \end{aligned}}
 \tag{4.646}
\]

Thus the Möbius coordinate is exactly a negative shifted-prime coordinate.
This is a genuine exact reduction, but it is not the scalar family in
Lichtman's theorem.  Even if one grants an analogous negative-shift
variant, the coefficient multiplying \(\mu(p-w)\) in (4.646) still
depends jointly on \(p\) and \(w\): both

\[
 b_Q(w,p-w)=\left\lfloor\frac{Qw}{p-w}\right\rfloor
 \quad\hbox{and}\quad
 \widetilde G_{p-w,w;h,\delta,\nu,\sigma}
 \tag{4.647}
\]

move with the shift.  In particular, fixing \(w\) does not fix the Farey
phase.  The finite witness \(Q=11,w=1\) contains

\[
 (s,p,b_Q)=(2,3,5),(6,7,1),(10,11,1).
 \tag{4.648}
\]

Lichtman, arXiv:2009.08969v2, Theorem 1.1 proves, for
\(H=X^\theta\), \(0<\theta<1\),

\[
 \sum_{h\le H}\left|\sum_{p\le X}\mu(p+h)\right|
 \ll_{\theta,\delta}
 \frac{H\pi(X)}{(\log X)^{1/3-\delta}}.
 \tag{4.649}
\]

Its Lemma 6.1 permits a moderate coefficient \(G(n)\), but that \(G\) is
fixed before averaging over \(h\).  It does not permit the moving
\(G_w(n)\) in (4.647).  Three independent theorem-level mismatches remain:

1. (4.649) is an \(L^1\) average over scalar shifts, whereas (4.645) is a
   vector cluster \(L^2\) estimate retaining \(\xi,Q,h,\delta\) and packet
   labels;
2. the full Type-I packet has \(w\asymp p\asymp T\), while the quantitative
   polynomial statement assumes \(H=X^\theta<X\) with fixed
   \(0<\theta<1\);
3. the saving in (4.649) is logarithmic, hence has power exponent \(0\),
   leaving the entire \(T^{1/2}\) unsquared deficit in (4.645).

Consequently even the \(d=1,k=1\) face is not covered by the published
shifted-prime theorem.  This is stronger than the generic observation that
fixed-shift cancellation is open: it identifies the exact favorable
reindexing and shows why the required global weight cannot be discarded.
The helpers farey_type_i_unit_divisor_shifted_prime_reassembly and
lichtman_shifted_prime_type_i_coverage_audit verify (4.646)--(4.648) and
record the norm, range, and half-power deficit.  Their Type-I coverage flags
remain false.

### 4.75 The scalar metric-Beatty surrogate: fixed-\(f\) fails, but structured sampling loses no power

Technau--Zafeiropoulos, arXiv:1907.06050, Theorem 2.1 and Corollary
4.4 give a genuinely square-root-sized discrepancy for one *fixed*
arithmetic function on a Beatty set.  In the notation of their paper the
underlying continuous estimate is

\[
 \int_0^1
 \max_{x\le X}\left|\Sigma_{\lambda^{-1}}^{(\ell)}(f,x)\right|^2
 d\lambda
 \ll (\log\log X)^2\|f\|_{2,X}^2.
 \tag{4.650}
\]

For bounded or prime-logarithmic coefficients, the power exponent on the
right is one.  If one fixed arithmetic function represented every sector,
multiplying by \(Q\asymp X\) slope samples would therefore give total
energy exponent two, exactly the target in (4.645).  This is a numerically
sufficient scalar surrogate, not yet an adapter for the actual packet.

Indeed, the fixed-function hypothesis fails before sampling is considered.
At \(Q=6,k=1\), the two nonempty critical fibers

\[
 (b,s,w,r)=(1,6,1,7),\qquad(2,5,2,7)
 \tag{4.650a}
\]

produce the same Beatty value \(r=ks+w=7\), but their actual coefficients
are

\[
 \mu(6)\mu(7)=-1,\qquad \mu(5)\mu(7)=1.
 \tag{4.650b}
\]

No scalar assignment \(f(7)\) can encode both slopes.  The published
continuous integral keeps \(f\) fixed as the slope varies, so it cannot be
applied to the family \(f_b(r)=\mu(s_b(r))\mu(r)\).  This finite collision
does not rule out a new pair-valued or vector-valued theorem; it rules out
the proposed scalar fixed-\(f\) adapter.

The conclusion, however, is a Lebesgue slope average, not a theorem on the
moving rational grid.  The classical finite trigonometric polynomial
displayed as equation (3.1) in that paper has frequencies

\[
 k=mj,\qquad m\le X+1,\qquad |j|\le\sqrt X,
 \qquad |k|\ll X^{3/2}.
 \tag{4.651}
\]

The sampling obstruction is exact on a uniform \(Q\)-grid.  For
\(F(t)=\sum_k c_ke(kt)\), character orthogonality gives

\[
 \boxed{
 \frac1Q\sum_{b\bmod Q}|F(b/Q)|^2
 =\sum_{\rho\bmod Q}
   \left|\sum_{k\equiv\rho\;(\bmod Q)}c_k\right|^2
 =\sum_k|c_k|^2+
   \sum_{\substack{k_1\ne k_2\\Q\mid k_1-k_2}}
   c_{k_1}\overline{c_{k_2}}.}
 \tag{4.652}
\]

If an alias class contains at most \(L_Q\) frequencies, Cauchy gives

\[
 \frac1Q\sum_{b\bmod Q}|F(b/Q)|^2
 \le L_Q\sum_k|c_k|^2,\qquad
 L_Q\ll1+\frac{X^{3/2}}Q.
 \tag{4.653}
\]

This factor is sharp for unrestricted coefficients: with
\(Q=5\), \(c_1=c_6=c_{11}=1\), the continuous energy is \(3\) and the
normalized grid energy is \(9\).  The actual reciprocal nodes
\(\lambda_b=(1+b/Q)^{-1}\) on the unit-slope face are nonuniform but
\(Q^{-1}\)-separated on a fixed compact interval; the standard
trigonometric large sieve gives
the same generic factor \(1+X^{3/2}/Q\).  Thus, at \(X=Q=T\),

\[
 \boxed{
 E_{\rm continuous}=T^{2+o(1)},\qquad
 E_{\rm sampled}^{\rm generic}=T^{5/2+o(1)},\qquad
 \text{deficit}=T^{1/2}.}
 \tag{4.654}
\]

This is only the arbitrary-bandwidth audit.  It must not be charged to the
Technau--Zafeiropoulos polynomial, whose Fourier coefficients have the
special divisor-convolution form

\[
 F(\lambda)=\sum_{m\leq X}g_m
 \sum_{1\leq |j|\leq J}c_j e(mj\lambda),
 \qquad |c_j|\ll |j|^{-1},\qquad J=X^{1/2}.
 \tag{4.654a}
\]

This structure removes the apparent half-power even on the nonuniform
reciprocal grid.  Let \(\mathcal H\) be a Hilbert space and let
\(\lambda_1,\ldots,\lambda_Q\) be \(h\)-separated in a fixed compact
interval.  For every \(\sigma>1/2\), the scaled Sobolev sampling
inequality gives

\[
 \boxed{
 h\sum_{\beta\leq Q}\|F(\lambda_\beta)\|_{\mathcal H}^{2}
 \ll_\sigma
 \|F\|_{L^2(\mathbb T;\mathcal H)}^2
 +h^{2\sigma}
 \bigl\||D|^\sigma F\bigr\|_{L^2(\mathbb T;\mathcal H)}^2.}
 \tag{4.654b}
\]

Writing

\[
 a_k=\sum_{\substack{mj=k\\m\leq X,\ |j|\leq J}}g_m c_j,
 \tag{4.654c}
\]

divisor Cauchy, valid componentwise in \(\mathcal H\), gives for every
\(\eta>0\)

\[
 \begin{aligned}
 \sum_k\|a_k\|_{\mathcal H}^2
 &\ll_\eta (XJ)^\eta\sum_m\|g_m\|_{\mathcal H}^2,\\
 \sum_k |k|^{2\sigma}\|a_k\|_{\mathcal H}^2
 &\ll_\eta (XJ)^\eta
 \sum_m m^{2\sigma}\|g_m\|_{\mathcal H}^2
 \sum_{1\leq |j|\leq J}|j|^{2\sigma-2}.
 \end{aligned}
 \tag{4.654d}
\]

At the critical scales \(X=Q=T\), \(h\asymp T^{-1}\), and
\(J=T^{1/2}\), take \(\sigma=1/2+\eta\).  Then

\[
 h^{2\sigma}X^{2\sigma}\asymp1,\qquad
 \sum_{j\leq J}j^{2\sigma-2}\ll_\eta J^{2\eta}
 =T^\eta.
\]

Equations (4.654b)--(4.654d) prove

\[
 \boxed{
 \sum_{\beta\leq Q}\|F(\lambda_\beta)\|_{\mathcal H}^{2}
 \ll_{\varepsilon}T^{1+\varepsilon}
 \sum_{m\leq T}\|g_m\|_{\mathcal H}^{2}.}
 \tag{4.654e}
\]

Thus when \(\sum_m\|g_m\|^2=T^{1+o(1)}\), the sampled total energy is
\(T^{2+\varepsilon}\), exactly the target.  The reciprocal nodes
\(\lambda_b=(1+b/Q)^{-1}\) are \(Q^{-1}\)-separated on the relevant
compact interval, so no uniform-grid orthogonality is needed.  The
generic \(T^{1/2}\) line in (4.654) is therefore not an obstruction for
a *fixed Hilbert-valued coefficient family* of the form (4.654a).

For reference, a direct arbitrary-alias treatment would instead ask for

\[
 \boxed{
 \sum_{\rho\bmod Q}
 \left\|\sum_{k\equiv\rho\;(\bmod Q)}
 c_{k;h,\delta,\nu,\sigma}\right\|_2^2
 \ll_{\varepsilon,W}T^\varepsilon
 \sum_k\|c_{k;h,\delta,\nu,\sigma}\|_2^2.}
 \tag{4.655}
\]

All Type sectors and outer packet labels would have to be summed before
(4.655), but (4.654e) shows that this extra alias conjecture is unnecessary
once a valid fixed-coefficient Fourier adapter has been constructed.
The original \(a_{\rm AFE}=h\delta\) and the auxiliary sector character
\(\xi\) are distinct variables in (4.621zadj16u); \(h\delta\) therefore
cannot be counted as an extra interlacing of the rational slope grid
without a new derived identity.  Moreover (4.650) has one coefficient
function on Beatty values, whereas the actual packet retains the second
index Möbius factor and a vector wave packet.

The finite helper farey_scalar_beatty_fixed_coefficient_collision verifies
(4.650a)--(4.650b).  The helper trigonometric_grid_aliasing_sides verifies
(4.652)--(4.653) over exact rational coefficients.  The scale adapter
technau_zafeiropoulos_grid_coverage_audit records the generic bandwidth
audit.  The corrected adapter
structured_beatty_sobolev_sampling_audit records (4.654a)--(4.654e),
supports nonuniform separated nodes and fixed Hilbert coefficients, and
sets generic_bandwidth_alias_loss_is_necessary false.  Both adapters keep
the coupled-gate coverage flag false: the exact map from the moving
two-Möbius Type packet to one fixed \(g_m\) family has not been
constructed.  The only surviving theorem mismatch in this route is now
the coefficient/packet adapter, not rational-grid sampling.
The finite helper beatty_divisor_fourier_coefficient_sides constructs
\(a_k=\sum_{mj=k}g_mc_j\) over exact rational vectors and verifies the
frequency-by-frequency Hilbert divisor-Cauchy majorant used in
(4.654d).

### 4.76 Exact nonprincipal Type Gram with all cross sectors retained

The failed scalar adapter is not needed to state the true finite gate.  Let
\(P\) range over the supplied labelled packets and put

\[
 b(P)=\left\lfloor\frac{Q(n_P-ks_P)}{s_P}\right\rfloor,
 \qquad
 \kappa_M(b,b')=\mathbf1_{b=b'}-\frac1M.
 \tag{4.656}
\]

For a Type factorization \(t=(d,m)\), \(dm=n_P\), retain

\[
 C_{P;(d,m)}=
 c_P\,\mu(s_P)\mu(d)\Lambda(m)\,\widetilde V_P,
 \tag{4.657}
\]

where \(c_P\) contains the signed AFE amplitude and the labels
\((h,\delta,\nu,\sigma)\), in particular the original product
\(a_{\rm AFE}=h\delta\).  Nonprincipal character orthogonality gives the
exact finite Gram

\[
 \boxed{
 \mathcal N_{\ne0}^{\rm Type}
 =\sum_{P,P'}\sum_{dm=n_P}\sum_{d'm'=n_{P'}}
 \kappa_M(b(P),b(P'))
 \langle C_{P;(d,m)},C_{P';(d',m')}\rangle.}
 \tag{4.658}
\]

Classify \(t\) as Type I when \(\min(d,m)\le U\) and as Type II
otherwise.  Without an intervening absolute value, (4.658) has the exact
eight-block split

\[
 \boxed{
 \mathcal N_{\ne0}^{\rm Type}
 =\sum_{X,Y\in\{\mathrm I,\mathrm{II}\}}
 \left(\mathcal N_{X,Y}^{\Delta=0}
       +\mathcal N_{X,Y}^{\Delta\ne0}\right),
 \quad
 \Delta=n_Ps_{P'}-n_{P'}s_P.}
 \tag{4.659}
\]

All four \(X/Y\) blocks, including the mixed I/II and II/I terms, are
retained.  On primitive support \(\Delta=0\) forces one original
\((n,s)\) entry; summing every \(dm=n\) cross factorization then gives
\(-\mu(s)\mu(n)\log n\) on each side by (4.621zadj16z).  Therefore

\[
 \boxed{
 \sum_{X,Y}\mathcal N_{X,Y}^{\Delta=0}
 =\mathcal N_{\Delta=0}^{\rm original\ entry},}
 \tag{4.660}
\]

before Cauchy--Schwarz.  The helper
labelled_type_nonprincipal_determinant_split verifies
(4.656)--(4.660) over exact rational vector packets.  Its fixture includes
two differently labelled packets on \((n,s)=(30,19)\), a second entry
\((35,22)\), common sector \(b=11\), all four Type-pair blocks, and the
nonzero determinants \(\pm5\).  It records every \(h\delta\) and keeps
global_nonzero_determinant_gate_proved false.

Since the original-entry diagonal already has exponent two, a convenient
sufficient estimate for this supplied sector packet is the *joint* gate

\[
 \boxed{
 \mathrm{JNT}_{2}^{\rm abs}:\qquad
 \left|\sum_{X,Y\in\{\mathrm I,\mathrm{II}\}}
 \mathcal N_{X,Y}^{\Delta\ne0}\right|
 \ll_{\varepsilon,W}T^{2+\varepsilon}.}
 \tag{4.661}
\]

No separate bound for an individual Type block is required.  The finite
fixture makes this distinction visible: the four full Type-pair energies
are \(171/5,-342/5,-342/5,1368\), while their nonzero-determinant part is
the signed value \(-2052\).  Taking absolute values blockwise would erase
precisely the cross-sector cancellation retained by (4.661).

The full nonprincipal sum has more structure than its determinant-nonzero
part.  If

\[
 X_b=\sum_{P:\,b(P)=b}c_PA_P\widetilde V_P,
 \qquad A_P=-\mu(s_P)\mu(n_P)\log n_P,
\]

then the character projector gives the exact square identity

\[
 \boxed{
 \mathcal N_{\ne0}^{\rm Type}
 =\sum_b\|X_b\|_2^2-\frac1M\left\|\sum_bX_b\right\|_2^2
 =\frac1M\sum_{0\leq b<c<M}\|X_b-X_c\|_2^2\geq0.}
 \tag{4.662}
\]

Put

\[
 D=\sum_{X,Y}\mathcal N_{X,Y}^{\Delta=0},
 \qquad
 J=\sum_{X,Y}\mathcal N_{X,Y}^{\Delta\ne0}.
 \tag{4.663}
\]

Since \(\mathcal N_{\ne0}^{\rm Type}=D+J\geq0\), the strictly weaker
one-sided gate

\[
 \boxed{
 \mathrm{JNT}_{2}^{+}:\qquad
 J\leq C_1T^{2+\varepsilon}}
 \tag{4.664}
\]

is sufficient after the diagonal estimate
\(D\leq C_0T^{2+\varepsilon}\), because

\[
 \boxed{
 |\mathcal N_{\ne0}^{\rm Type}|
 =D+J\leq(C_0+C_1)T^{2+\varepsilon}.}
 \tag{4.665}
\]

This does not assign a sign to \(J\).  Positivity is used only after every
Type and outer-packet cross term has been restored in the complete
projector energy.  The exact fixture has \(D=16587/5\), \(J=-2052\), and
total \(6327/5\); hence the upper bound \(J\leq0\) holds although
\(|J|\leq0\) does not.  The helper
joint_nonprincipal_one_sided_upper_bound certifies this finite strictness
witness and keeps analytic_one_sided_gate_proved false.

There is also an exact product-coordinate compression which avoids the
fixed-scalar collision (4.657) without pretending that the vector weight
has become scalar.  On primitive support set \(n=rs\), \(r=ks+w\), and
\(A=kQ+b\).  Then

\[
 \boxed{
 \mu(r)\mu(s)=\mu(n),\qquad
 As^2\leq Qn<(A+1)s^2,}
 \tag{4.666}
\]

so for fixed \((n,b)\)

\[
 \sqrt{\frac{Qn}{A+1}}<s\leq\sqrt{\frac{Qn}{A}}.
 \tag{4.667}
\]

If all points on the critical box satisfy \(s\leq CA\), two distinct
points \(s_1<s_2\) obey

\[
 A(s_2-s_1)(s_1+s_2)<s_1^2,
 \qquad s_2-s_1<C.
 \tag{4.668}
\]

Thus there are at most \(C=O_W(1)\) possible denominators, and the packet
has the exact form

\[
 \boxed{
 X_b=\sum_n\mu(n)
 \sum_{\substack{s\mid n,\ (s,n/s)=1\\
                 As^2\leq Qn<(A+1)s^2}}
 B_{b,n,s}.}
 \tag{4.669}
\]

This supplies one fixed scalar arithmetic coefficient \(\mu(n)\) across
the moving slopes and a bounded inner fiber.  However,
\(B_{b,n,s}\) retains the factorization-dependent vector tube, both
tapers, and all \(h\delta\) packet labels.  Therefore (4.669) is a
narrower coefficient class, not an application of a published scalar
Beatty theorem and not a cancellation estimate.  The helper
farey_product_sector_fiber_ledger verifies (4.666)--(4.669) over exact
integer data and keeps cancellation_estimate_proved false.

This is the correct finite adapter after the sector packet has been
supplied.  It is stronger and more faithful than the scalar alias target
(4.655), but it is still not the analytic estimate: even the weaker
one-sided signed sum of the four \(\Delta\ne0\) blocks must be bounded
globally, and the exhaustive map from the original coupled remainder to
the supplied packet family must remain outside any premature triangle
inequality.

### 4.77 The weakest positive gate is a centered moving Beatty--Chowla square

The positive projector identifies an exact positive version of the
one-sided gate.  Let
\(G_{s,w,\lambda}\in\mathcal H\) denote the complete vector attached to
one primitive entry, where \(\lambda\) ranges over every retained
\((h,\delta,\nu,\sigma)\) and Type-factorization label.  Put

\[
 \boxed{
 X_b=\sum_{\substack{s\le Q,\ 0\le w<s,
                     \\ (ks+w,s)=1\\
                     \lfloor Qw/s\rfloor=b}}
       \mu(s)\mu(ks+w)\sum_\lambda G_{s,w,\lambda}.}
 \tag{4.670}
\]

Finite character orthogonality, before any estimate, gives

\[
 \mathcal E_{\ne0}
 =\sum_b\|X_b\|_{\mathcal H}^2
  -\frac1Q\left\|\sum_bX_b\right\|_{\mathcal H}^2.
 \tag{4.671}
\]

Let \(D_{\Delta=0}\ge0\) be the recombined self diagonal and let
\(J_{\Delta\ne0}\) be the signed sum of all four nonzero-determinant
Type blocks.  Since

\[
 \mathcal E_{\ne0}=D_{\Delta=0}+J_{\Delta\ne0},
 \tag{4.672}
\]

one has the exact one-sided chain

\[
 \boxed{
 J_{\Delta\ne0}\le \mathcal E_{\ne0}
 \le \sum_b\|X_b\|_{\mathcal H}^2.}
 \tag{4.673}
\]

Thus the following centered positive square-function gate is sufficient for
\({\rm JNT}_{2}^{+}\):

\[
 \boxed{
 {\rm BC}^{\rm mov,cent}_{\mathcal H}(2):\qquad
 \sum_{b<Q}\|X_b\|_{\mathcal H}^2
 -\frac1Q\left\|\sum_{b<Q}X_b\right\|_{\mathcal H}^2
 \ll_{\varepsilon,W}T^{2+\varepsilon}.}
 \tag{4.674}
\]

The uncentered estimate
\(\sum_b\|X_b\|^2\ll T^{2+\varepsilon}\) is a stronger sufficient
condition, not the weakest gate.  In a scalar projection, the unique
entry in sector \(b\) is

\[
 ks+\left\lceil\frac{bs}{Q}\right\rceil
 =\left\lfloor
   \left(k+\frac bQ\right)s+\frac{Q-1}{Q}
  \right\rfloor,
 \tag{4.675}
\]

so (4.674) contains a centered, power-strength, moving-rational-grid version of
Beatty--Chowla.  Coherent energy has exponent three and the target has
exponent two; the required saving is one full power in energy, or
\(T^{1/2}\) before squaring.

[Crnčević--Hernández--Rizk--Sereesuchart--Tao,
arXiv:2211.15830v4](https://arxiv.org/abs/2211.15830), Theorem B, proves
only a qualitative logarithmic limit for
\(\lambda(n)\lambda(\lfloor\alpha n\rfloor)\) at one fixed irrational
\(\alpha\).  [Teräväinen--Walker,
arXiv:2303.12574v1](https://arxiv.org/abs/2303.12574), Theorem 1.2,
subsumes it, treats two fixed inhomogeneous Beatty slopes, and identifies
the possible rational-ratio resonance.  Neither result supplies a
uniform power saving as \(Q\), \(b\), and the slope move with \(T\), nor
the Hilbert-valued vector square in (4.674).  The rational-resonance
classification supports the ordering used here--extract (4.672) first--
but it does not estimate the remainder.

The finite helper `farey_beatty_chowla_projector_sides` evaluates
(4.670)--(4.673) over exact rational vectors and retains every supplied
packet label and distinguishes the centered projector from the stronger
uncentered sector square.  The scale helper `beatty_chowla_power_gate_audit` records
the remaining half-power before squaring and keeps
`covers_one_sided_joint_type_gate` false.  Therefore (4.674) is now the
most explicit positive sufficient gate, not a proved estimate.

### 4.78 Exact sector Fourier completion closes every jump boundary

The remaining Type packet has an exact additive completion which must be
used with its endpoint convention intact.  For \(0<\xi<Q\), define the
right-continuous step function

\[
 F_{\xi,Q}(x):=e\!\left(\frac{\xi\lfloor Qx\rfloor}{Q}\right),
 \qquad 0\le x<1.
 \tag{4.676}
\]

Its zero Fourier coefficient vanishes.  Every other coefficient vanishes
unless \(a\equiv\xi\pmod Q\), and for \(a=\xi+jQ\)

\[
 \boxed{
 c_{\xi,j}
 =\frac{Q(1-e(-\xi/Q))}{2\pi i(\xi+jQ)}.}
 \tag{4.677}
\]

At continuity points the Fourier series with these coefficients is
pointwise exact.  At a jump the Fourier series returns the midpoint, so
the exact right-continuous identity is

\[
 \boxed{
 F_{\xi,Q}(x)
 =\sum_{j\in\mathbb Z}c_{\xi,j}e((\xi+jQ)x)
 +\frac{1-e(-\xi/Q)}2e(\xi x)
  \mathbf1_{Qx\in\mathbb Z}.}
 \tag{4.678}
\]

Now put \(x=w/s\) and apply the one-factor Type relation
\(dp=ks+w\).  Since \(a=\xi+jQ\) and \(ak\in\mathbb Z\), every continuous
harmonic has the exact phase

\[
 \boxed{
 e\!\left(a\frac ws\right)
 =e\!\left(a\frac{dp}{s}\right).}
 \tag{4.679}
\]

This is a direct linear fraction, not a Kloosterman inverse.  Both
Möbius coefficients and every \(h,\delta,\nu,\sigma\) label remain in
the accompanying vector coefficient.

The correction in (4.678) is completely harmless after primitivity, for
an exact reason.  Set

\[
 \mathcal B_Q:=\{(s,w):1\le s\le Q, 0\le w<s,
                  (ks+w,s)=1, s\mid Qw\}.
\]

Since \((ks+w,s)=(w,s)\), reduction of \(b/Q\) gives the bijection

\[
 \boxed{
 b\longmapsto
 \left(\frac{Q}{(b,Q)},\frac b{(b,Q)}\right),qquad
 \{0,\ldots,Q-1\}\simeq\mathcal B_Q.}
 \tag{4.680}
\]

In particular \(|\mathcal B_Q|=\sum_{s\mid Q}\varphi(s)=Q\), and every
sector contains exactly one primitive jump entry.  If all outer labels
on that original entry are first recombined into \(Y_b\), then

\[
 0\le
 \sum_b\|Y_b\|^2-Q^{-1}\left\|\sum_bY_b\right\|^2
 \le\sum_b\|Y_b\|^2=D_{\partial}\le D_{\rm cont}.
 \tag{4.681}
\]

The scalar jump multiplier in (4.678) has modulus at most one.  Since
\(D_{\rm cont}\ll T^{2+\varepsilon}\) is already the settled diagonal,
the entire Fourier-boundary layer is within target.  Thus the analytic
gate may be restricted to \(s\nmid Qw\); no endpoint error is hidden in
the infinite harmonic expansion.

For the continuous Type-I spectrum, however, an ordinary additive large
sieve still does not close the estimate.  Write
\(s\asymp T^\sigma\), \(Q\asymp T^q\),
\(d\asymp T^\delta\), and \(p\asymp T^{\sigma-\delta}\).  Even after
optimistically separating a common prime coefficient family, Cauchy in
\(s\) followed by the Farey large sieve gives, for one fixed \(d\),

\[
 T^{\sigma-q}
 \bigl(T^{\sigma-\delta}+T^{2\sigma}\bigr)
 T^{\sigma-\delta}.
 \tag{4.682}
\]

At the critical face \(\sigma=q=1\), this has exponent \(3-\delta\).
Even perfect orthogonality among the \(T^\delta\) divisors leaves exponent
three; Cauchy in \(d\) gives \(3+\delta\).  The target exponent is two.
Hence termwise sector-Fourier completion plus the standard additive large
sieve still misses one power in energy, or \(T^{1/2}\) before squaring.
Cancellation must remain joint in the divisor/Möbius or determinant
variables, and possibly between Fourier harmonics.

The helpers `beatty_sector_fourier_type_phase_ledger` and
`primitive_beatty_fourier_boundary_sides` verify (4.679)--(4.681) over
exact integer and rational-vector data.  The latter independently
enumerates both sides of (4.680), recombines repeated packet labels on an
original entry, and proves equality of its sector energy with the
diagonal sub-sum.  The scale helper
`beatty_type_i_additive_large_sieve_audit` records (4.682) and keeps
`standard_additive_large_sieve_covers_type_i` false.

### 4.79 Restore the AFE inverse phase before classifying Type I/II

The additive audit in (4.682) is not the strongest available
classification, because it intentionally ignores an oscillator rather
than taking its absolute value.  Restore

\[
 \alpha=\xi+jQ,\qquad A=h\delta,qquad r=dp=ks+w.
\]

Then the sector and AFE phases recombine exactly as

\[
 \boxed{
 e_s(\alpha w-A\bar r)
 =e_s(\alpha dp-A\bar d\bar p).}
 \tag{4.683}
\]

For fixed \(d\), this is the nonhomogeneous prime-Kloosterman phase

\[
 e_s(Bp+C\bar p),qquad
 B=\alpha d,quad C=-A\bar d,qquad
 (BC,s)=1\Longleftrightarrow(\alpha A,s)=1.
 \tag{4.684}
\]

The identity spends neither \(\mu(s)\), \(\mu(d)\), nor the
factorization \(A=h\delta\).  It therefore gives the correct theorem
class for the continuous packet.

Put \(s=T^\sigma,d=T^u,p=T^{\sigma-u}\).  Korolev's
composite-modulus theorem covers the unit left wing
\(0\leq u<\sigma/4\), with

\[
 \eta_{\rm Kor}(\sigma,u)=
 \begin{cases}
 (\sigma-3u)/35,&0\leq u\leq\sigma/8,\\
 (\sigma/4-u)/7,&\sigma/8\leq u\leq\sigma/4.
 \end{cases}
 \tag{4.685}
\]

For prime \(s\), Fouvry--Kowalski--Michel Theorem 1.5 gives the
limiting left-wing exponent

\[
 \eta_{\rm FKM}(\sigma,u)=\sigma/24-u/6,
 \qquad0\leq u<\sigma/4,
 \tag{4.686}
\]

and its Möbius analogue gives the symmetric prime-modulus right wing.
For the central prime-modulus band, FKM Theorem 1.17 accepts arbitrary
dyadic coefficients.  With \(v=\min(u,\sigma-u)\), its saving is

\[
 \eta_{\rm FKM}^{\rm II}
 =\min\left(\sigma/4,v/2,\sigma/4-v/2\right).
 \tag{4.686a}
\]

This is at most \(\sigma/8\), attained at \(v=\sigma/4\), and it
degenerates to zero at exact balance \(v=\sigma/2\).
The exact coverage table is:

| Type range | composite modulus | prime modulus | coupled status |
|---|---|---|---|
| \(0\leq u<\sigma/4\) | Korolev, max saving \(\sigma/35\) | FKM, limiting max \(\sigma/24\) | below target |
| \(\sigma/4\leq u\leq3\sigma/4\) | no matching bilinear theorem | FKM Theorem 1.17, max \(\sigma/8\), zero at balance | composite and balanced Type II unproved |
| \(3\sigma/4<u\leq\sigma\) | only logarithmic uniform Möbius trace input | FKM Möbius trace | below target |

At the critical point the required amplitude saving is \(1/2\), so the
best one-variable prime-modulus theorem still leaves \(11/24\), and the
uniform composite theorem leaves \(33/70\).  Even the best bilinear
prime slice leaves \(3/8\), while exact balance leaves the full \(1/2\).
The estimates also have no joint moment over \(s,\xi,h,\delta\).
Consequently the corrected surviving
interface is the pre-Cauchy Hilbert-valued bilinear trace square.  With
the coefficients \(c_{\xi,j}\) from (4.677), it is

\[
 \boxed{
 \frac1Q\sum_{\xi=1}^{Q-1}
 \left\|
 \sum_s\mu(s)\sum_{h,\delta}\sum_{dp\asymp s}
 \mu(d)\Lambda(p)\sum_jc_{\xi,j}
 \mathcal W_{s,\xi,j,h,\delta,d,p}
 e_s((\xi+jQ)dp-h\delta\bar d\bar p)
 \right\|_{\mathcal H}^{2}
 \ll T^{2+\varepsilon}.}
 \tag{4.687}
\]

The weight includes \(dp=ks+w\) and \(s\nmid Qw\).  Expanding the norm
restores both Type copies and every reflection-label cross term.  This is
the exact continuous Fourier form of the supplied centered sector gate,
not yet the exhaustive adapter from (4.5).  It is narrower than an
arbitrary coupled kernel, but its central factor band and
composite-modulus aggregation remain unproved.

The exact helper beatty_afe_type_kloosterman_phase_ledger verifies
(4.683)--(4.684).  The Korolev and FKM exponent helpers verify
(4.685)--(4.686), including their strict endpoint and modulus
restrictions.  fkm_prime_modulus_bilinear_type_ii_audit verifies
(4.686a), including its exact balanced degeneration.  All keep the full
coupled-coverage flag false.
