# VK-edge residual amplification audit

## Scope

This branch asks whether the existing local second-moment theorem forces
zero contributions beyond one selected zeta zero and its conjugate.  It
does not assume that local large values automatically create new zeros.

For a zeta zero

```text
rho = beta + i gamma
```

of analytic multiplicity `m`, the normalized target-pair contribution is

```text
P_rho(y) = -2 m cos(gamma y - arg rho).
```

The residual is

```text
R_rho(y) = normalizedPsiError rho y - P_rho(y).
```

## Exact target-pair budget

The Lean theorem `intervalIntegral_cosineZeroPair_sq` proves

```text
integral_[a,b] P_rho(y)^2 dy
  = 2 m^2 (b-a)
    + (m^2/gamma)
        (sin(2 gamma b - 2 arg rho)
         - sin(2 gamma a - 2 arg rho)).
```

Hence

```text
integral_[a,b] P_rho(y)^2 dy
  <= 2 m^2 (b-a) + 2 m^2 / |gamma|.
```

On the epsilon logarithmic window this is represented by the exact
finite-height coefficient

```text
B_Y = 2 m^2 + 2 m^2 / (|gamma| epsilon log Y).
```

## Residual reverse triangle

`MathlibAux.integral_sq_sub_lower_of_integral_sq_bounds` proves the sharp
Hilbert-space implication

```text
integral F^2 >= A L
integral P^2 <= B L
B < A
--------------------------------
integral (F-P)^2 >= (sqrt A - sqrt B)^2 L.
```

The zeta-specialized endpoints expose this criterion on arbitrary compact
intervals and on epsilon logarithmic windows.

## Obstruction for the current swept theorem

The theorem

```text
centeredSharpenedSweptOrdinaryL2Constant_lt_targetPairHalfEnergy
```

proves

```text
centeredSharpenedSweptOrdinaryL2Constant epsilon rho k
  < epsilon * m^2.
```

The target conjugate pair alone has leading energy

```text
2 * epsilon * m^2 * log Y.
```

Therefore the existing swept lower bound is below one half of the energy
that the selected pair can already supply.  It does not satisfy the
residual criterion and cannot force an additional zero contribution.

The fixed-proportion large-value theorem has the same limitation.  A
single cosine pair already occupies a fixed positive fraction of every
long logarithmic interval above any threshold strictly below its maximum.
Positive measure by itself is therefore not a zero-amplification
mechanism.

## Missing mathematical input

To continue toward a zero-density contradiction, one needs at least one
new theorem of one of the following forms:

1. a local second-moment lower bound with coefficient strictly greater
   than the full target-pair budget `B_Y`;
2. a detector that annihilates the target pair while retaining a nonzero
   arithmetic main term for the classical primes;
3. an arithmetic correlation theorem that excludes the one-frequency
   residual model.

Generic zero-free regions, the existing Carlson upper bound, and the
current explicit-formula lower bound do not provide this input.

## Claim boundary

This branch proves an exact target-pair energy formula, a reusable residual
energy theorem, a conditional zeta residual endpoint, and a formal
obstruction for the existing swept coefficient.

It does not prove:

- positive residual energy unconditionally;
- an additional zeta zero;
- a Carlson zero-density contradiction;
- the Riemann hypothesis.
