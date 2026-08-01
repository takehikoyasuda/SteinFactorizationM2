# SteinFactorizationM2

Macaulay2 prototype for the Stein factorization algorithm in Takehiko Yasuda,
*An algorithm for the minimal model program in dimension three*, §4–§5 and
Algorithm 1 ([arXiv:2603.13703v2](https://arxiv.org/abs/2603.13703v2)).

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
IMPLEMENTATION.tex/.pdf      technical note: construction, examples, outputs
tests/basic.m2               basic and Veronese regression tests
tests/global-hom.m2          general bigraded global Hom regression tests
tests/mori-fiber-space.m2    P1 x P2 -> P2 example
tests/blowup-line.m2         Bl_L(P3) divisorial contraction
tests/blowup-twisted-cubic.m2
```

The technical note [IMPLEMENTATION.pdf](IMPLEMENTATION.pdf) describes the
construction, the worked examples, and the actual Macaulay2 output.  It is
written in LaTeX rather than markdown because GitHub's markdown renderer refuses
`\newcommand`, `\operatorname`, `\mathbb`, `\mathcal` and `\tag`, and eats the
backslash in `\,` and `\\`, which between them rule out macros, multi-line
formulas and equation numbers.  Rebuild it with

```sh
pdflatex IMPLEMENTATION.tex      # twice, for the cross-references
```

## Main M2 functions

For arbitrary bigraded (R)-modules (M,N), use:

```m2
data = bigradedGlobalHomData(
    S, M, N, NoverS, d1, d2, c1, c2)
```

Here `NoverS` is the same target module (N), presented as an
`S`-module after restriction along `S -> R`.  The explicit presentation is
needed because Proposition 4.2 reads the shifts in an `S`-free resolution of
(N).  The returned `data` contains the certified bound, both resolutions,
the truncation of (M), and `Hom_R(M_{>=r},N)_{>=0}`.

For the Stein-factorization specialization (M=N=R):

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

Not covered:

- only standard bigraded input is tested. The paper allows weighted
  projective spaces and the construction reads degrees from the ring, but no
  weighted example has been run, and `certifiedHomogeneousGraph` assumes an
  unweighted target;
- `d1,d2,c1,c2` are trusted as given. Note `c1,c2` are the *sums of the
  degrees* of the variables in each block (equal to the variable counts only
  in the standard graded case).

Current performance issue:

- deep minimal resolutions can dominate the exact-bound route;
- finite `A`-module generators can be algebraically redundant, making graph
  elimination unnecessarily expensive. Algebra-generator minimization is in
  progress.

## Use of AI

The code, the tests, and the technical note were written essentially by an AI
system (Claude), with minor edits by the author.  The author has read them and
believes them to be correct, but has not checked every detail.  The algorithm
itself is the one in the paper above and nothing conceptually difficult is
attempted here, and each example is checked automatically against
independently known geometry, so large errors are unlikely — but this is a
research prototype, not verified software.

## License

CC0 1.0 Universal (public domain dedication). See [LICENSE](LICENSE).
