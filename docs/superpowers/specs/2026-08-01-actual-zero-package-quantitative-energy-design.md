# Actual Zero-Package Quantitative Energy

## Objective

Strengthen the existing positive-energy window selection to retain any
prescribed amount strictly below the package diagonal energy.

## Construction

Write the energy as `D - B / L`, where `D` is diagonal energy and `B` is the
finite off-diagonal bound. For a target `d < D`, set `gap = D - d` and choose

`L = max 1 (B / gap + 1)`.

Then `L > 0`, `B / L < gap`, and hence `d < D - B / L`. A direct corollary
retains more than `D / 2` whenever `D > 0`.

## Scope

This is a finite-energy arithmetic lemma. It adds no zero-density, phase,
Carlson, RH, or simultaneous-sign conclusion. Its role is to provide a fixed
positive lower coefficient before choosing a finite boundary capture.
