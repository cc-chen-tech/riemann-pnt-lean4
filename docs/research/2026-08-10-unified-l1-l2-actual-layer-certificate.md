# A unified actual-zero layer certificate for L1 upper and L2 lower transfer

## Objective

The upper-bound and oscillation-lower-bound routes should consume the same
actual zeta zero decomposition, but they require different norms:

```text
PNT upper bound:
  linear analytic-multiplicity mass and pointwise triangle inequality;

oscillation complement:
  square analytic-multiplicity mass, Occupancy, and weighted L2.
```

A useful unified abstraction must expose this difference.  An unconstrained
`hkernel` plus a single opaque `densityBound` would hide the central
mathematics.

## Common block geometry

Use a fixed real-part grid and dyadic height shells.  A block is specified by

```text
sigmaLeft <= Re rho < sigmaRight,
T <= |Im rho| < 2*T.
```

The index set contains distinct nontrivial zeta zeros.  Analytic multiplicity
is a weight, not repeated indexing.

The common block certificate records:

```text
zeros            finite distinct-zero block;
sigmaLeft        Carlson threshold;
sigmaRight       pointwise x-growth endpoint;
height           lower dyadic height T;
linearMass       sum multiplicity(rho);
maxMultiplicity  max multiplicity(rho);
squareMass       sum multiplicity(rho)^2 / |rho|^2;
```

The certificate also records the actual-zeta facts that every indexed point is
a nontrivial zero and lies in the displayed block.

## Carlson capacity fields

For

```text
q(sigma) = 4*sigma*(1-sigma),
```

the actual Carlson layer supplies

```text
linearMass
  <= C_count
     * T^q(sigmaLeft)
     * (1 + log T)^4.
```

The local maximum multiplicity theorem supplies

```text
maxMultiplicity
  <= C_mult * (1 + log T).
```

The linear-to-square theorem derives

```text
squareMass
  <= C_count * C_mult
     * T^(q(sigmaLeft)-2)
     * (1 + log T)^5.
```

The square field is derived data.  It must not be postulated independently in
the actual-zeta constructor, because that would sever the audit trail from
Carlson and local multiplicity.

## L1 consumer: PNT upper transfer

For the ordinary explicit-formula zero kernel

```text
K_x(rho) = x^(rho-1) / rho,
```

the block geometry gives

```text
|K_x(rho)|
  <= x^(sigmaRight-1) / T.
```

Therefore

```text
|sum_{rho in block} m(rho) * K_x(rho)|
  <= C_count
     * x^(sigmaRight-1)
     * T^(q(sigmaLeft)-1)
     * (1 + log T)^4.
```

This is an L1 estimate.  It needs neither maximum multiplicity nor Occupancy.
Using the square-mass route here would add avoidable losses.

After setting

```text
T = x^gamma,
```

the polynomial exponent is

```text
E_upper
  = sigmaRight - 1
    + gamma*(q(sigmaLeft)-1).
```

The upper transfer combines these block exponents with the zero-free region,
the explicit contour remainder, and the selected truncation height.

## L2 consumer: oscillation-complement transfer

For the unnormalized oscillation kernel

```text
x^rho / rho,
```

the coefficient square sum in the block satisfies

```text
sum |m(rho) * x^rho / rho|^2
  <= C
     * x^(2*sigmaRight)
     * T^(q(sigmaLeft)-2)
     * (1 + log T)^5.
```

If half-isolated supplies

```text
Occupancy(T)
  <= C_occ * T^theta * (1 + log T)^r,
```

then the weighted block energy is at most

```text
C_L2
  * x^(2*sigmaRight)
  * T^(q(sigmaLeft)-2+theta)
  * (1 + log T)^(5+r).
```

Relative to target amplitude `x^beta/|rho0|`, the right-end normalized energy
exponent on `x <= Y^lambda`, `T=Y^gamma`, is

```text
E_lower_right
  = 2*lambda*(sigmaRight-beta)
    + gamma*(q(sigmaLeft)-2+theta).
```

The left-end version replaces `lambda` by `1` in the first term.

This consumer requires square multiplicity and Occupancy.  It must not infer
either from the L1 upper theorem.

## Finite-cluster deletion is shared

Both consumers may remove the same finite main cluster `S` from a block.

For the L1 consumer, every absolute summand is nonnegative, so deletion cannot
increase the majorant.  For the L2 coefficient mass, every square summand is
nonnegative, so the same is true.

The common certificate should expose monotonicity theorems:

```text
linearMass(block \ S) <= linearMass(block),
squareMass(block \ S) <= squareMass(block).
```

No new Carlson estimate depending on `S` is required.

## Dynamic height is a finite affine minimax problem

After fixing the real grid, every polynomial contribution has an exponent
affine in the height parameters:

```text
e_i(p) = a_i + dot(b_i,p),
```

where `p` may contain

```text
gammaLow,
gammaHigh,
gammaL2Left,
gammaL2Right,
alpha,
d,
lambda.
```

The asymptotic objective is

```text
minimize over feasible p:
  max_i e_i(p).
```

For an upper bound, the active exponents include L1 zero layers and contour
errors.  For an oscillation lower bound, they include normalized L2 energy,
cubic contour loss, real-axis residues, and trivial zeros.

The unified machine should therefore separate:

```text
geometry/capacity:
  produces the finite affine exponent list;

parameter theorem:
  supplies a feasible explicit witness p;

transfer theorem:
  consumes strict negativity and concludes decay.
```

It need not formalize a general linear-programming solver.  Explicit witnesses
are preferable for the current route, but their claimed optimality must be
proved against the finite maximum rather than asserted from inspection.

## Meaning of optimal truncation

There are three distinct notions that must not share one theorem name:

```text
minimal admissible cutoff:
  smallest gamma making every required exponent negative;

balanced cutoff:
  equality point of two competing active exponents;

minimax-optimal cutoff:
  parameter attaining the minimum of the maximum exponent over the full
  feasible polytope.
```

For the right-edge direct-L2 block,

```text
gammaStar
  = 2*lambda*(1-beta)/(2-theta)
```

is only the minimal admissible cutoff at `sigma=1`.  A midpoint between
`gammaStar` and a cap gives a convenient strict margin; it is not automatically
the global minimax optimum once contour and other strips are included.

The final theorem may call a height "optimal" only after all active exponents
and feasible constraints have been included.

## Common facade without an abstract fake kernel

The generic layer certificate may be abstract over a finite index type and
nonnegative masses.  The public PNT facades should nevertheless instantiate it
with concrete actual-zeta kernels:

```text
upper facade:
  x^(rho-1)/rho;

oscillation facade:
  x^rho/rho * C_h(rho);

actual constructor:
  analytic zeta zeros and analytic multiplicity.
```

Any kernel hypothesis remaining in the facade must be a theorem already proved
for one of these concrete kernels.  Users should not be asked to supply an
arbitrary `hkernel` estimate.

## Proposed Lean structures and theorem chain

The design should be represented by equivalents of:

```text
structure ActualZeroDyadicStrip where
  index : Type
  zeros : Finset index
  zero : index -> Complex
  multiplicity : index -> Nat
  sigmaLeft sigmaRight height : Real
  isDistinctZeroBlock : ...
  reBounds : ...
  imBounds : ...

structure ActualCarlsonLayerCertificate
  extends ActualZeroDyadicStrip where
  linearMassBound : ...
  maxMultiplicityBound : ...

theorem ActualCarlsonLayerCertificate.squareMassBound
theorem ActualCarlsonLayerCertificate.deleteLinear
theorem ActualCarlsonLayerCertificate.deleteSquare

theorem actualLayer_l1KernelBound
theorem actualLayer_l2CoefficientMassBound
theorem actualLayer_l2EnergyBound_of_occupancy

structure FiniteAffineExponentCertificate where
  parameters : ...
  exponents : Finset AffineExponent
  strictMargins : forall e in exponents, evaluate e parameters < 0

theorem upperTransfer_of_actualLayers
theorem lowerComplementTransfer_of_actualLayers
```

Repository naming may use existing zero-block types rather than introduce a
parallel structure.  The critical requirement is that both consumers visibly
share the same actual-zero geometry and Carlson linear count.

## Audit ledger

The final upper/lower facade must report:

```text
upper block:
  polynomial exponent sigmaRight-1 + gamma*(q(sigmaLeft)-1),
  log loss 4;

lower L2 block:
  polynomial exponent
    2*endpointScale*(sigmaRight-beta)
      + gamma*(q(sigmaLeft)-2+theta),
  log loss 5+r;

extra multiplicity loss:
  exactly one log in the lower coefficient mass,
  none in the upper L1 block;

critical cases:
  every equality recorded separately from strict decay.
```

## Nonclaims

This design does not claim:

- that the same norm proves both upper and lower estimates;
- that Carlson alone supplies Occupancy;
- that a midpoint cutoff is globally optimal;
- that the upper route reproduces Johnston's best error function without a
  separate minimax calculation;
- that the lower route already closes the actual cubic contour and triangle
  average;
- that a constant-parametric lower transfer proves a strict `pi/2` result
  without an actual-zeta main-energy surplus.
