# Conrey equation (41): global argument partition

## 1. Exact target

Put

\[
  \gamma(t)=\eta(1/2+it),\qquad 2\le t\le T.
\]

Conrey's equation (41) uses the assertion that the number of distinct
ordinates satisfying

\[
  \operatorname{Re}\gamma(t)=0,\qquad \gamma(t)\ne0
\]

is bounded below, up to the harmless absolute endpoint loss, by

\[
  \frac1\pi\Delta\arg\gamma-N_{0,\eta}(T).
\tag{1}
\]

The exact finite statement to formalize is therefore

\[
  \#\{t:\operatorname{Re}\gamma(t)=0,\ \gamma(t)\ne0\}
  \ge
  \frac1\pi\Delta\arg\gamma-N_{0,\eta}(T)-1.
\tag{2}
\]

The final `-1` is the single floor/ceiling loss for the two global endpoints;
it is absorbed by Conrey's existing `O(T)` term.  Dropping it as an exact
finite assertion would be false: an argument increase strictly between zero
and `pi` need not cross a half-odd-integer multiple of `pi`.

## 2. Why componentwise summation is insufficient

Let the critical-line zeros of `eta` in `(2,T)` be

\[
  \tau_1<\cdots<\tau_r
\]

with analytic orders `m_1,...,m_r`.  Applying the existing zero-free crossing
theorem separately on the `r+1` complementary components gives one endpoint
rounding loss on every component.  This only yields

\[
  \#\text{crossings}
  \ge \frac1\pi\sum_j\Delta_j-(r+1),
\]

and a later subtraction of the zero multiplicity would charge the same
partition twice.  This is not the structure of (1).

The component lifts must instead be reconciled before the integer levels are
counted.

## 3. Local phase jump at a zero

Near a zero `tau_j` of order `m_j`, analyticity gives

\[
  \gamma(t)=(i(t-\tau_j))^{m_j}h_j(t),
  \qquad h_j(\tau_j)\ne0.
\tag{3}
\]

Choose continuous arguments of `h_j` on a small neighborhood.  The argument
on the component to the right of `tau_j` can then be shifted by an integral
multiple of `2 pi` so that its limiting value is the left limiting value plus
exactly

\[
  m_j\pi.
\tag{4}
\]

Thus the zero contributes a phase bridge of length `m_j pi`.  A half-open
interval of that length contains exactly `m_j` levels of the lattice

\[
  \frac\pi2+\pi\mathbb Z.
\tag{5}
\]

The half-open convention is essential: a closed bridge can contain
`m_j+1` lattice levels when both endpoints lie on the lattice, while an
endpoint level realized on a neighboring nonzero component is already a
genuine real-part crossing and must not be charged to the zero.

## 4. Global level attribution

After aligning all component lifts by (4), insert one artificial phase bridge
at each zero.  The resulting real-valued path is continuous and joins the two
global endpoint arguments.  Every lattice level between those endpoints is
therefore attained by the intermediate value theorem.

Attribute each attained level as follows.

1. If it is attained on a genuine nonzero component, choose a time there.
   The exponential identity shows that the real part of `gamma` vanishes at
   that time.  Distinct lattice levels give distinct times.
2. Otherwise attribute it to the first zero bridge on which it is attained.
   By (5), the bridge at `tau_j` receives at most `m_j` levels.

The global lattice contains at least

\[
  \frac1\pi\Delta\arg\gamma-1
\]

levels.  At most `sum_j m_j=N_{0,eta}(T)` of them are charged to zero bridges.
The remaining levels inject into distinct nonzero real-part crossings, proving
(2).

This is the non-duplicative accounting required by equation (41): zero
multiplicity pays only for phase levels swallowed by the zero bridges, while
endpoint rounding is paid once globally.

### 4.1 Nonmonotone-component correction

No zero-free component argument is known to be monotone, and even its net
endpoint change can be negative.  Therefore the finite gluing statement must
not require a level on a genuine component to lie in the directed interval
`Icc(alpha,beta)`.  The correct component range is the unordered interval

\[
  [[\alpha,\beta]]=[\min(\alpha,\beta),\max(\alpha,\beta)].
\]

The intermediate value theorem then produces the crossing whether the
component lift rises or falls.  For example, a phase chain with vertices
`0,10,-10,5` still covers every level between the global endpoints `0` and
`5`, although its middle component is decreasing.  Any proof that discards
that component because `10>-10` is invalid.

The finite invariant is an alternating chain

\[
  [a_0,b_0],\ [b_0,b_0+m_0\pi),\
  [[a_1,b_1]],\ldots,[[a_r,b_r]],
  \qquad a_{j+1}=b_j+m_j\pi,
\]

where genuine components use closed unordered intervals and zero bridges use
positive half-open intervals.  Repeated use of

\[
  [[x,z]]\subset [[x,y]]\cup[[y,z]]
\]

shows that every global endpoint level lies either on a genuine component or
on a bridge.  At the exceptional far endpoint `b_j+m_j*pi`, the half-open
bridge does not contain the level, but the next genuine component does.  This
is precisely why the half-open convention is compatible with arbitrary
nonmonotone component arguments.

## 5. Lean decomposition

The proof should be split into four reusable layers.

1. **Deleted-level cardinality.**  For the existing global level finset
   `argumentCrossingIndices alpha beta` and any bad-level finset `B`, prove

   \[
     (\beta-\alpha)/\pi-1-\#B
     \le \#(K(\alpha,\beta)\setminus B).
   \]

2. **Order-`m` bridge capacity.**  Prove that a half-open interval of length
   `m*pi` contains exactly `m` half-odd-integer levels.  This must retain the
   half-open endpoint convention explicitly.
3. **Analytic local factorization.**  Specialize the analytic-order API to the
   vertical restriction `t -> eta(1/2+it)` and obtain the phase alignment (4).
4. **Global attribution.**  Build the aligned piecewise phase path, define the
   bad levels charged to bridges, prove their total cardinality is at most
   `N_{0,eta}(T)`, and inject every remaining level into a genuine crossing.

Layers 1 and 2 are now formalized in `MathlibAux/ArgumentCrossing.lean` as
`argumentCrossingIndices_sdiff_card_lower_bound`,
`mem_argumentCrossingBridgeIndices_iff`, and
`argumentCrossingBridgeIndices_card`.  Layer 3 is now formalized for the
actual `eta` by the vertical order factorization, the continuous logarithm of
its regular factor, and `exists_conreyDegreeOneEta_local_argument_bridge`.
The finite cardinality part of Layer 4 is also exact:
`card_biUnion_argumentCrossingBridgeIndices_le` shows that the union of all
local bridge-level sets costs at most the sum of their multiplicities, without
requiring the bridges to be disjoint, and
`argumentCrossingIndices_sdiff_bridgeUnion_card_lower_bound` preserves the
single global endpoint loss after deleting this union.

The abstract gluing part of Layer 4 is now formalized without a monotonicity
assumption.  `ArgumentPhasePartition` records an alternating finite list of
genuine components and aligned half-open order bridges.
`ArgumentPhasePartition.exists_component_or_bridge` proves global coverage,
including the far-endpoint routing described in Section 4.1;
`exists_argumentCrossing_of_level_mem_uIcc` handles both increasing and
decreasing component arguments; and
`ArgumentPhasePartition.exists_injective_component_argumentCrossings` sends
all surviving levels injectively to component-tagged real-part crossings.

The remaining equation-(41) gate is the actual-`eta` specialization: construct
this finite partition from the critical-line divisor, choose compatible lifts
on every complementary interval, and identify the resulting bridge list and
sum of orders with the existing `eta` zero count.  No equation-(41) or Conrey
simple-zero proportion claim should be made before that specialization is
proved.

## 6. Analytic-order specialization on the critical line

Mathlib's exact local-order interface already supplies the algebraic part of
Layer 3.  If `rho=1/2+i*tau` and

\[
  \operatorname{analyticOrderAt}(\eta,\rho)=m<\infty,
\]

then there is a function `h`, analytic at `rho` and nonzero there, such that

\[
  \eta(z)=(z-\rho)^m h(z)
\]

throughout a neighborhood of `rho`.  Restricting this neighborhood identity
along `z=1/2+i*t` gives the exact real-parameter factorization

\[
  \eta(1/2+it)=\bigl(i(t-\tau)\bigr)^m h(1/2+it).
\tag{6}
\]

Continuity and `h(rho) != 0` also make the restricted regular factor nonzero
on a sufficiently small real neighborhood of `tau`.  Thus every local zero
on the critical line is isolated there and its entire singular phase is
carried by the explicit power in (6).

To finish Layer 3, choose a continuous logarithm of the regular factor on that
small interval.  Its argument has the same left and right limit, whereas
`i(t-tau)` changes from argument `-pi/2` to `pi/2`.  The aligned right-hand
lift is therefore the left-hand lift plus exactly `m*pi`.  This final logarithm
and lift-alignment statement is not implied merely by (6) and remains the next
formal checkpoint.

The singular-power part of that statement is now exact.  The definitions
`verticalPowerLeftLog m r` and `verticalPowerRightLog m r` exponentiate, for
`r>0`, to `(-I*r)^m` and `(I*r)^m`, respectively, and Lean proves

\[
  \operatorname{Im}L_{\mathrm{right}}(m,r)
  -\operatorname{Im}L_{\mathrm{left}}(m,r)=m\pi.
\tag{7}
\]

The common `m*log r` term cancels in (7).  It remains to add the same local
continuous logarithm of the regular factor `h` to both sides and connect the
resulting component lifts to the global path.

The regular-factor logarithm is now constructed without choosing the
principal branch.  First, `exists_continuousLogOn_Ioo` proves that every
nonvanishing continuous complex curve on a real open interval has a continuous
lift `ell` through `Complex.exp`; the proof uses convexity of the interval,
contractibility, simple connectedness, and the exponential covering map.

The actual specialization
`exists_conreyDegreeOneEta_regularFactor_continuousLog` then shrinks the
analytic/nonzero neighborhood of `h` to a symmetric interval
`(tau-delta,tau+delta)` and supplies

\[
  e^{\ell(t)}=h(1/2+it)
\]

throughout that interval.  Consequently the local branch-cut problem is
closed.

The final local assembly is now exact in
`exists_conreyDegreeOneEta_local_argument_bridge`.  After one common
shrinking, the two functions

\[
  L_-(r)=L_{\mathrm{left}}(m,r)+\ell(\tau-r),\qquad
  L_+(r)=L_{\mathrm{right}}(m,r)+\ell(\tau+r)
\]

exponentiate to the actual values of `eta` on the two sides of the zero, and

\[
  \operatorname{Im}L_+(r)-\operatorname{Im}L_-(r)\longrightarrow m\pi
  \qquad(r\downarrow0).
\]

Thus Layer 3 is closed without a principal-log branch assumption.  The
remaining work is the actual finite-divisor construction: enumerate the
critical-line zeros, build the zero-free component curves and compatible
endpoint lifts, and instantiate `ArgumentPhasePartition`.  Once instantiated,
the abstract theorem already injects every uncharged global level into a
distinct component-tagged nonzero real-part crossing, and the bridge union is
already bounded by the sum of zero orders even when bridge-level sets overlap.
