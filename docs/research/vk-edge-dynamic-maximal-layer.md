# Dynamic maximal-layer reduction

## Scope

This checkpoint removes the previously explicit outside-band Gaussian-energy
assumption from the dynamic complementary-zero packet reduction at a fixed
height `T`.

For a current absorbed zero set `S`, define the remaining finite-height zeros
by

\[
Z_{S,T}=Z(T)\setminus S.
\]

When this set is nonempty, the module selects its maximal real part
\(\beta_{S,T}\), the full layer at that real part, and the positive gap
\(\Delta_{S,T}\) to the next lower real-part layer.  The selected half-gap
band contains exactly the maximal layer.

## Proved bounds

Every inspected zero outside the half-gap band satisfies

\[
\Re \rho\le \beta_{S,T}-\Delta_{S,T}.
\]

Consequently its normalized moving packet has the pointwise bound

\[
\|P_{\mathrm{out}}(a+t)\|
\le
e^{-\Delta_{S,T}t}
\sum_{\rho\in P_{\mathrm{out}}}
\|c_\rho(a)\|.
\]

At a nonnegative logarithmic center, the frozen coefficients gain another
full-gap factor:

\[
\sum_{\rho\in P_{\mathrm{out}}}\|c_\rho(a)\|
\le
e^{-\Delta_{S,T}a}
\sum_{\rho\in P_{\mathrm{out}}}
\frac{m(\rho)}{|\rho|}.
\]

Combining this with the repository's global reciprocal-zero estimate gives a
single absolute constant `C` such that

\[
\int_{0}^{L} w_m(t)\,\|P_{\mathrm{out}}(a+t)\|^2\,dt
\le
\left[
e^{-\Delta_{S,T}a}
|K|\,C(1+\log(T+6))^2
\right]^2.
\]

The factor `|K|` is retained deliberately: this checkpoint does not assume a
separate duplicate-free theorem for an arbitrary inspected bucket family.

The final endpoint substitutes this bound into the previous full-energy
packet theorem.  If the full moving complementary energy exceeds the
real-band drift budget plus the displayed outside-band budget, then one
nonempty packet on the actual maximal remaining real-part layer can be added
to `S`; the union has strictly larger cardinality.

## Exact boundary

This is a fixed-height reduction.  It does **not** prove that
\(\Delta_{S,T}\) is uniform as `T` grows.  It also does not supply the required
lower bound for the full moving complementary energy.

The next unresolved bridge is therefore:

1. transfer a true normalized explicit-formula residual lower bound to the
   full moving complementary energy;
2. choose a height/center schedule for which
   \(\Delta_{S,T}a\) dominates the logarithmic reciprocal-zero budget, or
   replace this requirement by an injective layer iteration;
3. prove that repeated absorption yields enough distinct zero packets to
   contradict a zero-density upper bound.

No Carlson contradiction, zero exclusion, or RH conclusion is claimed here.
