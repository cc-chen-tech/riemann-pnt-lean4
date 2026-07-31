# Monotone Moving Upper and Signed Omega Unified Design

## Goal

Produce a genuinely variable-exponent unified theorem returning both an
eventual PNT upper bound and a conditional signed oscillation lower bound for
the same actual Chebyshev error.

## Moving upper side

Define an eventual coefficient-mass cap for
`variableBoundaryZeroPackage H beta`. At each natural point, instantiate the
existing Carlson coefficient-mass theorem with exponent `beta(m)`. The fixed
margin and eventual `beta0 <= beta(m)` imply `sigma < beta(m)`, so the cap is
the explicit global Carlson-plus-real constant.

The stack108 residual and this cap give

```text
|relativeChebyshevPsi0Error(m)|
  < (capConstant sigma + eta) * m^(beta(m)-1)
```

eventually.

## Signed lower side

Stack111 transfers independent positive and negative moving-package witnesses
to one `HasFarSignedTargetAmplitudeWitnesses` certificate at
`(c-loss) * x^beta(x)`.

## Claim boundary

The upper conclusion is automatic from analytic inputs. The signed lower
conclusion remains conditional on two moving-package witnesses. This theorem
does not prove anti-cancellation or RH.
