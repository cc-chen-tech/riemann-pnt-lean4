# Explicit Formula Route Toy Experiment

Warning: This is an empirical numerical illustration only, not a proof, and it does not prove `explicit_formula_von_mangoldt`. The toy truncation omits pole, trivial-zero, constant, and convergence terms from the rigorous von Mangoldt explicit formula.

The table compares raw `psi(x) - x` values from the existing PNT
experiment code with a finite sum of paired nontrivial-zero terms
`-2*Re(x^rho/rho)` using rho = 1/2 + i*t. It is intended only as a
dependency-mapping aid for the explicit-formula route.

- x values sampled: 10, 100, 1000, 10000
- positive zero ordinates used: 5
- paired nontrivial zeros used: 10

| x | psi(x) - x | truncated zero contribution | residual | zero pairs |
|---:|---:|---:|---:|---:|
| 10 | -2.16798581949 | -0.595397447954 | -1.57258837154 | 5 |
| 100 | -5.95468877064 | -3.34321991824 | -2.6114688524 | 5 |
| 1000 | -3.31908775282 | -3.21778044546 | -0.10130730737 | 5 |
| 10000 | 13.3966932631 | 27.4544948357 | -14.0578015725 | 5 |

Fixture ordinates used:

- 14.1347251417347
- 21.0220396387716
- 25.0108575801457
- 30.4248761258595
- 32.9350615877392
