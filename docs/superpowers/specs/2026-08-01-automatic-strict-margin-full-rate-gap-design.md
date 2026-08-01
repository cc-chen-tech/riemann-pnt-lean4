# Automatic Strict-Margin Full Rate Gap

## Objective

Attach Stack139's normalized full-majorant theorem to the automatically
constructed actual grid from Stack133.

## Output

For every `q > 1` and every good-height selector, the theorem returns an actual
singleton grid with:

- the exact recovered base rate `rStar(b / q)`;
- at least the formal `rStar(b) / q` rate guarantee;
- eventual domination of the real relative PNT error;
- normalized majorant decay for every `slowerRate < grid.baseRate`;
- exclusion of cofinal lower witnesses at that same slower amplitude.

## Claim boundary

The theorem is a square-root-log upper/lower obstruction package. It neither
constructs lower witnesses nor applies at fixed power-scale zero amplitudes,
and it proves no Omega theorem or RH.
