# Manual review

Which pages of the package documentation have been read and accepted, and
against which revision.

Build the pages with `make docs` and open

    doc-build/share/doc/Macaulay2/SteinFactorization/html/index.html

A page is **reviewed** when it has been read in the browser, not merely built.
`make docs` only establishes that the examples run; whether the prose says what
it means to say is what this file records.

## Why the revision matters

A bare tick goes stale without saying so: the node it refers to can be rewritten
the next day and the tick still looks like an endorsement. So each accepted page
carries the commit it was accepted at. When a later commit touches that node,
the entry is stale and the page wants reading again, which is something one can
check rather than remember.

| Page | Source | Reviewed | Notes |
|---|---|---|---|
| `SteinFactorization` (top) | [552](SteinFactorization.m2#L552) | — | Earlier acceptance withdrawn after adding the workflow and assumptions |
| `steinHomData` | [615](SteinFactorization.m2#L615) | — | Earlier acceptance withdrawn after further prose changes |
| `steinCoordinateAlgebra` | [690](SteinFactorization.m2#L690) | — | |
| `directSteinGraph` | [834](SteinFactorization.m2#L834) | — | |
| `blockDegreeData` | [913](SteinFactorization.m2#L913) | — | |
| `steinHomDataAtBound` | [960](SteinFactorization.m2#L960) | — | |
| `steinDataByStabilization` | [1010](SteinFactorization.m2#L1010) | — | |
| `certifiedHomogeneousGraph` | [1081](SteinFactorization.m2#L1081) | — | |
| `certifiedWeightedGraph` | [1140](SteinFactorization.m2#L1140) | — | |
| `selectCertifiedGraphComponent` | [1197](SteinFactorization.m2#L1197) | — | |
| `checkChartwiseInverses` | [1238](SteinFactorization.m2#L1238) | — | Renamed because the old function did not certify a graph projection |
| `evaluateSteinGenerators` | [1289](SteinFactorization.m2#L1289) | — | |
| `bigradedGlobalHomData` | [1341](SteinFactorization.m2#L1341) | — | |
| `Bibliography` | [1404](SteinFactorization.m2#L1404) | — | |

Line numbers move as the documentation is edited; they are a convenience, not a
record.  The page names are what is stable.

## Open questions, not tied to one page

- The documentation is now where the reference material lives, so the overlap
  with Section 2 of `IMPLEMENTATION.tex` wants resolving one way or the other.
- Nothing links a page back to the source that generates it.  M2 prints a
  source location on every page, but it is the position of the `doc` block and
  therefore the same on all fourteen.
- `checkChartwiseInverses` intentionally checks only a cover and inverse map
  pairs.  A genuine chart certificate would need to bind these rings and maps
  to localizations of the source and the graph and verify overlap compatibility.
- The prose interpreting the exact order of generators in
  `evaluateSteinGenerators` can become stale if Macaulay2 changes that order.
