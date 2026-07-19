# Completed L-Function Contour Core Design

## Objective

Extract the reusable analytic core proved by the Riemann-von Mangoldt spike
without expanding the project into a general theory of automorphic or
Dirichlet L-functions. The new layer must express completed/base-function zero
and multiplicity compatibility, prove a generic logarithmic-derivative
rectangle count theorem, and make the existing zeta rectangle theorem an
actual instance of that generic result.

This is the abstraction stage between the completed spike and the later
Riemann-von Mangoldt main-term estimates. It does not prove the final
asymptotic formula.

## Chosen Boundary

Use a lightweight `CompletedLFunctionContourData` record plus a function-level
argument-principle theorem.

The record contains only data already exercised by the zeta spike:

- a base function and a completed function `C -> C`;
- the two real boundaries of a critical strip;
- analyticity of the completed function;
- equality of zero predicates in the open strip;
- equality of analytic orders in the open strip.

Vertical-edge nonvanishing, a finite zero set for a particular rectangle, and
good-height hypotheses remain theorem inputs. They depend on the chosen
L-function and contour and do not belong in the reusable record.

Gamma factors, conductors, root numbers, functional equations, Euler products,
and Dirichlet-series representations are explicitly excluded. Adding them now
would force a second hierarchy before the contour API has a second consumer.

## Public Components

### Completed-function strip data

Create `PrimeNumberTheorem/LFunction/CompletedContourData.lean` with a record
in namespace `PrimeNumberTheorem.LFunction`:

```lean
structure CompletedLFunctionContourData where
  base : C -> C
  completed : C -> C
  leftBoundary : R
  rightBoundary : R
  left_lt_right : leftBoundary < rightBoundary
  analytic_completed : AnalyticOnNhd C completed Set.univ
  completed_eq_zero_iff_base_eq_zero :
    forall {s}, leftBoundary < s.re -> s.re < rightBoundary ->
      completed s = 0 <-> base s = 0
  analyticOrderAt_completed_eq_base :
    forall {s}, leftBoundary < s.re -> s.re < rightBoundary ->
      analyticOrderAt completed s = analyticOrderAt base s
```

The Lean source uses the repository's actual Unicode types and notation. The
ASCII rendering above is only the design signature.

Provide derived lemmas for `analyticOrderNatAt` equality when both analytic
orders are finite. Do not add a custom multiplicity definition: the canonical
quantity remains `analyticOrderNatAt`.

### Generic logarithmic-derivative rectangle count

Create `MathlibAux/LogDerivArgumentPrinciple.lean`. Its main theorem is generic
over an analytic function `f`, a rectangle, a finite set `zeros`, and a natural
multiplicity function. It assumes:

- `f` is analytic on a neighborhood of the closed rectangle;
- inside the closed rectangle, `f z = 0` exactly when `z` is in `zeros`;
- every listed zero lies strictly inside the rectangle;
- `analyticOrderAt f rho = multiplicity rho` for every listed zero.

It proves:

```text
boundaryRectIntegral (logDeriv f)
  = (2 * pi * I) * sum rho in zeros, multiplicity rho.
```

The proof must reuse:

- `ZeroFreeRegion.meromorphicOn_logDeriv_sub_finset_principalParts`;
- `ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_logDeriv_sub_finset_principalParts`;
- `MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn`.

No new residue theorem, contour integral definition, or unproved argument
principle predicate is introduced.

### Zeta instance and compatibility

Extend `PrimeNumberTheorem/RiemannVonMangoldt/CompletedZeta.lean` with
`completedZetaContourData : CompletedLFunctionContourData`, using strip
boundaries `0` and `1` and the theorems already proved by the spike.

Refactor `PrimeNumberTheorem/RiemannVonMangoldt/RectangleCount.lean` so its
main equality invokes the generic logarithmic-derivative rectangle theorem.
The following public theorem signatures must remain unchanged:

- `boundaryRectIntegral_logDeriv_completedZeta_eq_between_sum`;
- `boundaryRectIntegral_logDeriv_completedZeta_eq_zeroCount_sub`.

The zeta module remains responsible for identifying the finite set with
`positiveNontrivialZerosBetween U T`, proving good-height boundary exclusion,
and transferring completed-zeta multiplicities to zeta multiplicities.

## Alternatives Rejected

### Function-level theorem only

This would extract the rectangle proof but leave completed/base compatibility
as zeta-specific lemmas. It is smaller, but it does not provide the requested
completed L-function interface and would duplicate strip compatibility for the
next L-function instance.

### Full L-function hierarchy

Connecting immediately to `StrongFEPair`, Dirichlet characters, Gamma factors,
root numbers, and conductors would maximize theoretical reuse. It also creates
several independent research obligations unrelated to the current
Riemann-von Mangoldt blocker. That work is deferred until the contour record
has a concrete second instance.

## Verification

Add two focused contract modules:

- `Test/CompletedLFunctionContourContract.lean` fixes the record and derived
  multiplicity interfaces;
- `Test/LogDerivArgumentPrincipleContract.lean` fixes the generic rectangle
  theorem signature.

Keep `Test/RiemannVonMangoldtContract.lean` unchanged except for any import
needed to compile the refactored implementation. Rebuild the existing
Riemann-von Mangoldt axiom audit and add the generic theorem to a focused axiom
audit.

Required checks:

```bash
lake -j 1 build PrimeNumberTheorem.LFunction.CompletedContourData
lake -j 1 build MathlibAux.LogDerivArgumentPrinciple
lake -j 1 build Test.CompletedLFunctionContourContract
lake -j 1 build Test.LogDerivArgumentPrincipleContract
lake -j 1 build PrimeNumberTheorem.RiemannVonMangoldt
lake -j 1 build Test.RiemannVonMangoldtContract
lake -j 1 build Test.RiemannVonMangoldtAxiomAudit
```

The changed source must contain no `sorry`, `admit`, or `axiom`. The audited
surface may depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Success Criteria

The abstraction stage is complete only when:

1. the generic theorem compiles independently of zeta;
2. the completed-function record has no zeta-specific fields;
3. the zeta rectangle theorem calls the generic theorem rather than retaining
   a duplicate private regularization proof;
4. all existing zeta theorem signatures and focused contracts still pass;
5. the axiom audit remains within the existing allowlist.

## Next Mathematical Stage

After this abstraction is verified, return to the zeta instance and split the
completed-zeta boundary integral using
`logDeriv_completedZeta_eq_zeta_add_gamma`. The next proof package will have
two independent estimates:

1. an exact Gamma/elementary-factor integral evaluation producing
   `T / (2*pi) * log (T / (2*pi)) - T / (2*pi)` up to `O(1)`;
2. an `O(log T)` estimate for the remaining zeta boundary contribution.

Only after both are proved at good heights should the project extend the
formula to every real height.

The repository already contains two inputs that should be reused directly:

- `HardyTheorem.exists_verticalGammaUnwrappedPhase_sub_thetaModel_tendsto_const_inv`
  gives the vertical Gamma phase as the elementary Stirling model plus a fixed
  constant and an `O(1 / T)` tail;
- `PrimeNumberTheorem.exists_localZeroMultiplicity_le_log_bound` bounds the
  total analytic multiplicity in the fixed-width height window by `O(log T)`.

The latter is reserved for the final passage from good heights to arbitrary
heights. It is not a substitute for controlling boundary argument variation.

For the difficult zeta-boundary term, the existing
`ZeroFreeRegion.exists_analyticOnNhd_primitive_logDeriv_on_ball` and
`ZeroFreeRegion.exists_normalized_analytic_log_primitive_on_ball` provide
branch-free analytic logarithms on individual zero-free balls. The missing
interface is global: compatible continuation along a piecewise rectangle path
and a bound for the total imaginary-part variation. The later boundary module
must make that distinction explicit rather than treating local
`logDeriv` bounds as an argument-variation theorem.

## Non-goals

- the final Riemann-von Mangoldt asymptotic;
- an `O(log T)` zeta boundary estimate in this abstraction branch;
- a Dirichlet L-function instance;
- a `StrongFEPair` adapter;
- a generic Gamma-factor or conductor hierarchy;
- a new zero-free region, zero-density theorem, PNT theorem, or RH result;
- any `def ... : Prop` standing in for an unproved theorem.
