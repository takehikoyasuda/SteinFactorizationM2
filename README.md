# YasudaSteinM2

Macaulay2 prototype for the Stein factorization algorithm in Takehiko Yasuda,
*An algorithm for the minimal model program in dimension three*, §4–§5 and
Algorithm 1 (arXiv:2603.13703v2).

The project computes the bigraded Hom module

```text
C = Hom_R(R_{>=r},R)_(0,>=0),
```

constructs its finite presentation over the target coordinate ring `A`,
recovers a graded coordinate algebra for the Stein intermediate, and can build
the connected-fiber graph directly from evaluated Hom generators.

## Requirements

- Macaulay2 1.24.11 or later
- bundled packages `Truncations`, `MinimalPrimes`, `Saturation`

The current development and tests use `/opt/homebrew/bin/M2` on macOS.

## Quick start

From the project root:

```sh
M2 --no-readline --stop -q tests/basic.m2
```

Or run the standard suite:

```sh
./run-tests.sh
```

The twisted-cubic benchmark is slower and uses a supplied experimental
truncation bound; run it separately:

```sh
M2 --no-readline --stop -q tests/blowup-twisted-cubic.m2
```

## Layout

```text
SteinFactorization.m2        reusable implementation
tests/basic.m2               basic and Veronese regression tests
tests/mori-fiber-space.m2    P1 x P2 -> P2 example
tests/blowup-line.m2         Bl_L(P3) divisorial contraction
tests/blowup-twisted-cubic.m2
docs/implementation-plan-ja.md
docs/status-ja.md
benchmarks/
```

## Main API

```m2
data = steinHomData(S, IGraph, d1, d2, c1, c2)
cData = steinCoordinateAlgebra(data, gammaIndex, baseImages)
gData = directSteinGraph(data, cData)
```

For a known or experimental truncation bound:

```m2
data = steinHomDataAtBound(S, IGraph, {r1,r2})
```

For heuristic stabilization using the full finite `A`-module strand:

```m2
result = steinDataByStabilization(
    S, IGraph, startBound, maxSteps, requiredMatches, baseImages, hilbertMax)
```

Stabilization always reports `certifiedBound => false`; finite agreement does
not prove the explicit bound in Corollary 4.3.

## Current status

Implemented:

- Corollary 4.3 shift bound from a bounded minimal free resolution;
- multigraded orthant truncation;
- finite `(0,>=0)`-strand presentation over `A` using `pushForward`;
- coordinate-algebra reconstruction via Lemma 5.2;
- direct graph closure through localization and a weighted Rees parameter;
- regression examples with finite, fiber-type, and divisorial contractions.

Current performance issue:

- deep minimal resolutions can dominate the exact-bound route;
- finite `A`-module generators can be algebraically redundant, making graph
  elimination unnecessarily expensive. Algebra-generator minimization is in
  progress.

## License

No license has been selected yet.

