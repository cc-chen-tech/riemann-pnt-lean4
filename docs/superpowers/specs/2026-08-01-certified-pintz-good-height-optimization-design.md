# Certified Pintz Good-Height Optimization

## Scope

Stack119 connects Pintz-style pointwise height optimization to the actual
good-height certificates used by the explicit formula. It stays inside the
`ZeroDensityLayerBudget*` transfer layer. It does not modify the protected
complementary-zero module, VK-edge modules, or the Sharp oscillation chain.

The result is an upper-transfer component. It does not prove an unconditional
signed Omega theorem or RH.

## Mathematical obstruction

An arbitrary finite height grid need not contain an analytic good height.
Consequently, selecting a cost minimizer from such a grid cannot be identified
with the selected height appearing in the actual truncated explicit formula.
Merely packaging an abstract Pintz optimizer and an unrelated good-height
schedule in one structure would leave this gap unchanged.

## Certified candidate family

Fix a positive polynomial exponent `alpha`. A finite nonempty candidate family
consists of uniform natural-point good-height selectors. The family uses a
common explicit-formula constant, so every candidate supplies certificates of
the same quantitative shape.

At scale `x`, candidate `i` is

```text
selection_i.height (x^alpha - 1)
```

once `x^alpha >= 9`. At smaller scales it is regularized to a fixed positive
fallback. This gives an everywhere-positive finite grid while leaving all
eventual analytic statements unchanged.

The lower envelope is regularized in the same way: it is `x^alpha - 1` in the
admissible range and a fixed lower bound otherwise. It tends to infinity and
is below every candidate. Thus the existing dynamic finite-grid optimizer
produces a positive height schedule tending to infinity.

## Theorem chain

1. Construct the regularized candidate height and prove eventual equality with
   `selectedUniformGoodHeight`.
2. Construct a `DynamicFiniteHeightGrid` from the finite candidate family.
3. Define the certified optimal schedule with
   `dynamicFiniteGridOptimalHeight`.
4. Prove exact pointwise cost optimality against every family member.
5. Recover a witnessing selector from optimizer membership.
6. Prove the selected schedule is eventually in
   `[x^alpha - 1, x^alpha]` and is an analytic good height.
7. Prove the selected schedule tends to infinity.
8. At natural samples, recover the actual truncated explicit-formula
   certificate at exactly the selected height.
9. If every candidate satisfies one common visible-zero envelope, prove that
   the selected schedule satisfies the same envelope.

The last two outputs are the bridge required by the existing actual remainder
and Stack118 zero-free-envelope transfers.

## PR boundary

Stack119 contains only the candidate-family construction and structural
inheritance theorems. A follow-up stack may generalize the natural remainder
majorant from one fixed selector to the certified optimizer and then feed that
certificate to Stack118. This separation keeps the first PR auditable and
prevents a large proof from hiding an assumption-equivalence gap.

## Validation

Build only the new implementation module, its contract, and its axiom audit
with the existing overlay and one low-priority Lean process. The accepted axiom
set is the repository baseline: `propext`, `Classical.choice`, and
`Quot.sound`.
