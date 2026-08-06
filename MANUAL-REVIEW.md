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
| `SteinFactorization` (top) | [491](SteinFactorization.m2#L491) | ✅ `c624921` | |
| `steinHomData` | [534](SteinFactorization.m2#L534) | ✅ `e8dde8a` | Was one example block covering two paragraphs; split, and `certifiedBound` given the gloss it lacked |
| `steinCoordinateAlgebra` | [596](SteinFactorization.m2#L596) | — | |
| `directSteinGraph` | [674](SteinFactorization.m2#L674) | — | |
| `blockDegreeData` | [741](SteinFactorization.m2#L741) | — | |
| `steinHomDataAtBound` | [788](SteinFactorization.m2#L788) | — | |
| `steinDataByStabilization` | [836](SteinFactorization.m2#L836) | — | Known: the first example block has no prose introducing it, the same fault `steinHomData` had |
| `certifiedHomogeneousGraph` | [891](SteinFactorization.m2#L891) | — | |
| `certifiedWeightedGraph` | [937](SteinFactorization.m2#L937) | — | |
| `selectCertifiedGraphComponent` | [985](SteinFactorization.m2#L985) | — | |
| `certifyChartwiseProjectionIsomorphism` | [1023](SteinFactorization.m2#L1023) | — | |
| `evaluateSteinGenerators` | [1074](SteinFactorization.m2#L1074) | — | |
| `bigradedGlobalHomData` | [1126](SteinFactorization.m2#L1126) | — | |
| `Bibliography` | [1180](SteinFactorization.m2#L1180) | — | |

Line numbers move as the documentation is edited; they are a convenience, not a
record.  The page names are what is stable.

## Open questions, not tied to one page

- The documentation is now where the reference material lives, so the overlap
  with Section 2 of `IMPLEMENTATION.tex` wants resolving one way or the other.
- `IMPLEMENTATION.tex` still records the environment as Macaulay2 1.24.11 with
  timings measured there; the package is now built and tested against 1.26.06.
- `newPackage` supplies no `HomePage`, which is what M2 1.26 is asking for when
  it warns about insufficient citation data.
- Nothing links a page back to the source that generates it.  M2 prints a
  source location on every page, but it is the position of the `doc` block and
  therefore the same on all fourteen.
