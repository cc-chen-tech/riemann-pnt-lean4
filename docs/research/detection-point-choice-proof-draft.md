# L1 detection-point choice: paper proof draft (revised)

## Status

Revised paper-level proof draft for lemma L1 of
`windowed-detector-lean-spec.md`.  **Revision 2 corrects a real error in
revision 1**: the continuous average argument was invalid because
`S(gamma) = sum m/(|rho| |gamma - Im rho|)` is NOT integrable over a window
that contains a zero (logarithmic divergence).  The correct argument is an
explicit `eta`-avoidance construction, and the resulting bound carries a
`T1/H` factor.  The downstream feasibility check (last section) shows L3
still closes with this weaker bound.

## Statement (revised)

Fix `0 < T0`, `1 <= H`, `T1 = T0 + H`, and a finite family of zeros
(multiplicities `m_j`, `|rho_j| >= Im rho_j > 0`, all `Im rho_j <= T1`).
Define, for `gamma` avoiding all `Im rho_j`,

```text
S(gamma) = sum_j m_j / (|rho_j| * |gamma - Im rho_j|).
```

There exists `gamma in [T0, T1]` with

```text
S(gamma) <= C * (1 + log T1)^2 * T1 / (T0 * H),
```

with `C` an absolute constant.  (Revision 1 claimed
`C log^2 T1 / T0`, which is false in general: the optimal avoidance
distance is `eta ~ H / N(T1)`, and the nearest-zero term alone contributes
`~ 1/(T0 eta) ~ T1 log T1/(T0 H)`.)

## Proof

### Step 0: avoidance radius

Let `N0` be an upper bound for the number of zeros with `Im <= T1` counted
with multiplicity (Lean: `exists_card_nontrivialZerosFinset_le_mul_log`,
`N0 = C0 * T1 * (1 + log T1)`).  Put

```text
eta := H / (4 * N0).
```

Each zero occupies the open interval of radius `eta` around its imaginary
part; the union has total length at most

```text
2 * eta * N0 = H / 2 < H,
```

so `[T0, T1]` is not covered: there exists `gamma in [T0, T1]` with
`|gamma - Im rho_j| >= eta` for every `j`.  (Lean: interval covering lemma —
a finite union of open intervals of total length `< H` cannot cover an
interval of length `H`; proof by sorting the centers, or via
`measure_biUnion_finset_le` with the Lebesgue measure of intervals.  The
sorting induction is the portable route.)

### Step 1: dyadic bound for the distance sum

For the `gamma` from Step 0, bound `sum_j 1 / |gamma - Im rho_j|`:

- nearest two zeros (at distance in `[eta, 2 eta)`): at most 2 terms,
  each `<= 1 / eta`, total `<= 2 / eta`;
- dyadic shells `2^k eta <= |gamma - Im rho_j| < 2^(k+1) eta`,
  `k >= 1`, up to height `T1`: each shell contains at most
  `C1 * (2^(k+1) eta * log T1 + log T1)` zeros by the windowed count (I2),
  so the shell contributes at most
  `C1 * (2 log T1 + log T1 / (2^k eta))`;
- summing `k = 1 .. log2(T1 / eta)`:
  `sum_j 1/|gamma - Im rho_j| <= 2/eta + C1' * (log T1 * log(T1/eta) + log T1 / eta)`.

With `1/eta = 4 N0 / H = 4 C0 T1 (1 + log T1) / H` this is

```text
sum_j 1/|gamma - Im rho_j|
  <= C * (T1 (1 + log T1)^2 / H + log T1 * log(T1 / eta)).
```

The second term is `<= C log T1 * (log T1 + log(4 C0 T1^2 log T1 / H))`,
which is dominated by the first term for `H <= T1`.

### Step 2: divide by the height

Since every `|rho_j| >= Im rho_j >= T0/2` for zeros at height around
`T0`... actually the cleanest uniform bound uses only `|rho_j| >= Im rho_j`
and the low part: for `Im rho_j >= T0/2`, `|rho_j| >= T0/2`, so

```text
S(gamma) <= (2/T0) * sum_{Im rho_j >= T0/2} 1/|gamma - Im rho_j|
             + sum_{Im rho_j < T0/2} m_j/(|rho_j| |gamma - Im rho_j|).
```

The low part satisfies `|gamma - Im rho_j| >= T0/2`, hence

```text
low part <= (2/T0) * sum_{Im rho_j < T0/2} m_j/|rho_j|
         <= (2/T0) * C2 log^2 T1                       (I1, global mass)
```

Combining with Step 1 gives the stated bound

```text
S(gamma) <= C * (1 + log T1)^2 * T1 / (T0 * H).
```

(For the high part, `sum 1/|gamma - Im rho_j|` is the Step 1 bound; for
`Im rho_j in [T0/2, T1]` the `1/|rho_j| <= 2/T0` factor applies.)

## Lean inputs (all present in the repository)

- `exists_card_nontrivialZerosFinset_le_mul_log` (GlobalZeroCount): N0.
- `exists_globalReciprocalZeroMultiplicity_le_log_sq` (GlobalZeroCount): I1.
- windowed count (I2): mechanical consequence of
  `RiemannVonMangoldt.AllHeightAsymptotic.exists_abs_riemannZeroCount_sub_mainTerm_le_log`
  and `hasDerivAt_riemannVonMangoldtMainTerm` (subtract heights, bound the
  main-term difference by `H` times a derivative bound).
- interval covering lemma: sorting induction over the finite center set
  (no measure theory needed).
- dyadic summation: `BigOperators` geometric bounds.

## Downstream feasibility check (L3)

The seed response at the aligned frequency is
`x^beta * lam * log X / T0`; the complementary weighted part is at most
`x^(beta - gap) * S(gamma)`.  With the revised bound the comparison reads

```text
x^gap * lam * log X / T0 > C x^0 * (1 + log T1)^2 * T1 / (T0 * H),
i.e.  gap * log X > (1 - h) * gamma * log X + O(log log X)
```

with `H = T^h = X^(gamma h)`, `T1 ~ X^gamma`.  Hence the requirement is
`gap > (1 - h) gamma` (to leading order).  Feasible region: choose
`h` close to 1 and `gamma` close to its lower bound `g = lam (1 - beta)`;
the condition `(1 - h) lam (1 - beta) < beta` holds for every
`beta > 2/3` (e.g. `h = 0.6, lam = 1.1`: `0.44 (1 - beta) < beta` for all
`beta > 0.31`).  L3 therefore still closes.

## Appendix: fully explicit proofs of the two structural lemmas

### Appendix A: the interval covering lemma (target `exists_point_avoiding_small_intervals`)

Claim: for a finite family of open intervals with centers `c_i`, radii
`r_i >= 0`, total length `sum 2 r_i <= H/2`, the interval `[T0, T0+H]`
(`H > 0`) is not covered.

Proof (discrete grid, no measure theory):

- Choose `M = 2n + 1` where `n = I.card`, and the grid points
  `gamma_k = T0 + (k + 1/2) * H / M` for `k = 0, ..., M-1`.
- Every grid point lies in `[T0 + H/(2M), T0 + H - H/(2M)]`, hence in
  `[T0, T0+H]`.
- For each `i`, the interval `(c_i - r_i, c_i + r_i)` contains at most
  `2 r_i * M / H + 1` grid points (spacing `H/M` argument: the grid
  points inside an interval of length `2 r_i` form a consecutive block of
  length at most `2 r_i / (H/M) + 1`).
- If the intervals covered all `M` grid points, double counting gives

```text
M <= sum_i (2 r_i M / H + 1) <= (H/2) * M / H + n = M/2 + n,
```

  i.e. `M <= 2n`, contradicting `M = 2n + 1`.

- Hence some `gamma_k` lies in no interval; it satisfies
  `r_i <= |gamma_k - c_i|` for every `i` (the intervals are open, and the
  grid point is outside each one).

Lean shape: `Finset.card` pigeonhole over the product
`{(i, k) : gamma_k in I_i}`; the per-interval grid bound is an
`Int.ceil`/floor count estimate for an arithmetic progression inside an
interval.  All prerequisites are in Mathlib (`Finset.card_le_card`,
`Nat.cast` manipulation).

### Appendix B: windowed count (target `exists_windowedZeroMultiplicity_le`)

Input: `exists_abs_riemannZeroCount_sub_mainTerm_le_log` gives
`|N(T) - M(T)| <= C0 (1 + log(T + 6))` for all `T` (with `M` the
Riemann–von Mangoldt main term).  Then

```text
N(T0+H) - N(T0)
  = (M(T0+H) - M(T0)) + (N(T0+H) - M(T0+H)) - (N(T0) - M(T0))
  <= |M(T0+H) - M(T0)| + 2 C0 (1 + log(T0+H+6)).
```

`hasDerivAt_riemannVonMangoldtMainTerm` plus the mean value theorem
(`Convex.norm_image_sub_le_of_norm_deriv_le` or `exists_deriv_eq_slope`)
bounds the main-term difference by

```text
|M(T0+H) - M(T0)| <= C1 * H * (1 + log(T0+H+6)),
```

since the main term is `(T/2pi) log(T/2pi) - T/2pi` up to an additive
constant, whose derivative is `(1/2pi) log(T/2pi)`, bounded by
`C1 (1 + log(T+6))` on `[T0, T0+H]`.  This closes the target bound.

Lean shape: apply the two absolute-value bounds plus a derivative bound
for the main term; the mean-value step is the only non-trivial one and is
standard Mathlib convex-analysis material.

## Boundaries

Paper draft (revision 2); nothing is claimed as proved until the Lean
modules exist.  The revision 1 continuous-average route is withdrawn.
