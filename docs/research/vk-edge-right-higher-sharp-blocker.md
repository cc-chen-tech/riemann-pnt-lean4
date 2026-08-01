# Right-higher Sharp transfer blocker

## What is proved

Let

\[
S_{\mathrm{dir}}(S,T_{\mathrm{old}},\sigma,T)
=
S\cup
\{\rho\in Z(T):\operatorname{Im}\rho\le T_{\mathrm{old}}
  \text{ or }\operatorname{Re}\rho\le\sigma\}.
\]

When the old-height cutoff reaches the positive ordinate of the zero
\(\rho_0\), both \(\rho_0\) and its conjugate belong to
\(S_{\mathrm{dir}}\).  They are therefore absent from the dynamic
complement used by the next directed-growth energy.

The module also proves the exact zero endpoint:

\[
\left[
  \forall\rho\in Z(T),\
  \rho\in S\text{ or }\operatorname{Im}\rho\le T_{\mathrm{old}}
    \text{ or }\operatorname{Re}\rho\le\sigma
\right]
\Longrightarrow
E_{\mathrm{dir}}=0.
\]

Thus positive directed energy already implies the existence of a genuinely
new zero above \(T_{\mathrm{old}}\) and to the right of \(\sigma\).  The
upstream directed-growth module extracts that witness; this branch does not
duplicate that argument.

## Why the current Sharp lower bound does not transfer

The unconditional Sharp lower bound is anchored at the original conjugate
zero pair.  At the coefficient level Lean verifies

\[
2C_{\mathrm{Sharp}}
<
2\varepsilon\,m(\rho_0)^2,
\]

where the right side is the leading ordinary-energy coefficient of that
pair.  Hence the existing lower bound can be carried by the pair alone.
After the directed exclusion set removes the pair, the current theorem gives
no positive lower bound for the remaining energy.

This is a mathematical obstruction, not a missing `simp` lemma.  If no new
higher right-strip zero exists, the remaining energy is exactly zero.

## Minimum missing analytic theorem

The smallest direct input needed by the upstream directed-growth endpoint is
the following theorem shape:

```lean
theorem exists_eventually_rightHigherExclusionFullMovingGaussianSecondMoment_pos
    {epsilon : ℝ} {rho : ℂ} {sigma : ℝ}
    (hepsilon : 0 < epsilon)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hsigma : 1 / 2 < sigma)
    (hsigmaRho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1) :
    ∀ (S : Finset ℂ) (Told : ℝ), rho.im ≤ Told →
      ∀ᶠ Y : ℝ in atTop,
        ∃ T ∈ Set.Icc (Real.exp (Real.log Y / 2))
            (Real.exp (Real.log Y / 2) + 1),
          goodHeight T ∧
          0 <
            dynamicComplementForwardMovingGaussianSecondMoment
              (rightHigherExclusionSet S Told sigma T) T rho.re
              (Real.log Y)
              (dynamicComplementFullBucketSet
                (rightHigherExclusionSet S Told sigma T) T)
              ((epsilon * Real.log Y) ^ 2)
              (epsilon * Real.log Y)
```

This signature is recorded as a research target only.  It is not declared as
a Lean `Prop`, axiom, or theorem in this branch.  Proving it would already
show that the original off-line zero forces another higher right-strip zero.
The explicit-remainder route would require the stronger lower bound exceeding
three times the approximation and closed-term error budgets.

A successful proof must produce energy surviving removal of the original
pair, for example through a detector annihilating that pair, a new arithmetic
correlation, or a lower bound larger than the full pair contribution.

No repeatable growth, Carlson contradiction, zero exclusion, or RH is claimed.
