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
| `SteinFactorization` (top) | [571](SteinFactorization.m2#L571) | — | Acceptance at `c624921` withdrawn: the page has since gained an end-to-end example and an assumptions paragraph |
| `steinHomData` | [665](SteinFactorization.m2#L665) | — | Acceptance at `e8dde8a` withdrawn: prose changed after it |
| `steinCoordinateAlgebra` | [756](SteinFactorization.m2#L756) | — | |
| `directSteinGraph` | [940](SteinFactorization.m2#L940) | — | |
| `blockDegreeData` | [1046](SteinFactorization.m2#L1046) | — | |
| `steinHomDataAtBound` | [1095](SteinFactorization.m2#L1095) | — | |
| `steinDataByStabilization` | [1159](SteinFactorization.m2#L1159) | — | |
| `certifiedHomogeneousGraph` | [1260](SteinFactorization.m2#L1260) | — | |
| `certifiedWeightedGraph` | [1335](SteinFactorization.m2#L1335) | — | |
| `selectCertifiedGraphComponent` | [1416](SteinFactorization.m2#L1416) | — | |
| `checkChartwiseInverses` | [1465](SteinFactorization.m2#L1465) | — | Renamed from `certifyChartwiseProjectionIsomorphism`, which claimed more than it checked |
| `evaluateSteinGenerators` | [1538](SteinFactorization.m2#L1538) | — | |
| `bigradedGlobalHomData` | [1599](SteinFactorization.m2#L1599) | — | |
| `Bibliography` | [1671](SteinFactorization.m2#L1671) | — | |

Every page is unreviewed as of the revision applying
[MANUAL-REVISION-PLAN.md](MANUAL-REVISION-PLAN.md).  The two ticks that stood
before it are withdrawn rather than carried over: both pages were edited by
that revision, which is exactly the situation the revision column exists to
make visible.

Line numbers move as the documentation is edited; they are a convenience, not a
record.  The page names are what is stable.

## Open questions, not tied to one page

- The documentation is now where the reference material lives, so the overlap
  with Section 2 of `IMPLEMENTATION.tex` wants resolving one way or the other.
- Nothing links a page back to the source that generates it.  M2 prints a
  source location on every page, but it is the position of the `doc` block and
  therefore the same on all fourteen.
- `checkChartwiseInverses` checks a cover and a list of inverse pairs and says
  so, which is honest but is not the chart certificate the name it used to have
  promised.  A real one would bind each chart's cover element, source
  localization, graph localization, projection and inverse into a single input,
  check the structural maps, and check the overlaps.  That is a design and not a
  repair, and it has not been attempted.
- The `evaluateSteinGenerators` page reads $\gamma=y_1$ and the second evaluated
  generator as $y_0x_1$ off the printed output.  The output is displayed before
  the prose interprets it, so nothing is asserted behind the reader's back, but
  a change in Macaulay2's generator ordering would leave the prose stale without
  failing the build.  No test pins the ordering down.
