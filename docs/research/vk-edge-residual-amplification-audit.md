# VK-edge residual amplification audit

## Scope

This branch studies a cosine model whose parameters are copied from a
selected zeta zero. It does not prove that this model is the actual
explicit-formula contribution of that zero and its conjugate, and it does
not assume that local large values automatically create new zeros.

For a zeta zero

```text
rho = beta + i gamma
```

of analytic multiplicity `m`, the normalized cosine model is

```text
P_rho(y) = -2 m cos(gamma y - arg rho).
```

The residual is

```text
R_rho(y) = normalizedPsiError rho y - P_rho(y).
```

Here "residual" means only this formal difference. No theorem in the branch
identifies it with the sum of other zeros, a contour remainder, or a
truncation error.

## Exact cosine-model budget

The Lean theorem `intervalIntegral_cosinePairModel_sq` proves

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

The model-parameterized endpoints expose this criterion on arbitrary compact
intervals and on epsilon logarithmic windows.

## Obstruction for the current swept theorem

The theorem

```text
centeredSharpenedSweptOrdinaryL2Constant_lt_cosineModelHalfEnergy
```

proves

```text
centeredSharpenedSweptOrdinaryL2Constant epsilon rho k
  < epsilon * m^2.
```

The cosine model alone has leading energy

```text
2 * epsilon * m^2 * log Y.
```

Therefore the existing swept lower bound is below one half of the model
energy budget. It does not satisfy the formal residual criterion. Without
an explicit-formula identification theorem, this comparison makes no claim
about additional zero contributions.

The fixed-proportion large-value theorem has the same limitation.  A
single cosine pair already occupies a fixed positive fraction of every
long logarithmic interval above any threshold strictly below its maximum.
Positive measure by itself is therefore not a zero-amplification
mechanism.

## Missing mathematical input

To continue toward a zero-density contradiction, one needs at least one
new theorem of one of the following forms:

1. a local second-moment lower bound with coefficient strictly greater
   than the full cosine-model budget `B_Y`;
2. a detector that annihilates the cosine model while retaining a nonzero
   arithmetic main term for the classical primes;
3. an arithmetic correlation theorem that excludes the one-frequency
   residual model.

Generic zero-free regions, the existing Carlson upper bound, and the
current explicit-formula lower bound do not provide this input.

## Claim boundary

This branch proves an exact cosine-model energy formula, a reusable
reverse-triangle theorem, a conditional psi-minus-model endpoint, and a
formal model-level obstruction for the existing swept coefficient.

It does not prove:

- that the cosine model is the actual selected zero-pair contribution;
- that the model residual equals other zeros plus analytic remainders;
- positive residual energy unconditionally;
- an additional zeta zero;
- a Carlson zero-density contradiction;
- the Riemann hypothesis.
