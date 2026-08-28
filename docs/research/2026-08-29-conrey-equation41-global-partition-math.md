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
`argumentCrossingBridgeIndices_card`.  Layers 3 and 4, especially the local
analytic phase alignment and the disjoint global attribution, remain the
actual equation-(41) gate.  No equation-(41) or Conrey simple-zero proportion
claim should be made before all four layers are connected to the actual
`eta`.
