# SteinFactorization manual review by ChatGPT

Reviewed revision: `f8473b6` (`manual` branch)

Review date: 2026-08-07

Review target: the Macaulay2 package documentation embedded in
`SteinFactorization.m2`, with `README.md`, `IMPLEMENTATION.tex`, the tests, and
the implementation consulted when checking consistency.  This document is a
review report only; it does not change the package or its manual.

## Summary

The manual is substantially better than a typical prototype manual.  In
particular, it explains why the Corollary 4.3 parameters are inferred from the
ambient ring, why the fourth argument of `bigradedGlobalHomData` is necessary,
why a supplied bound is not certified, and why the section ring can embed the
same Stein intermediate in an unexpected way.  The examples also build
successfully with Macaulay2 1.26.06.

Before treating the manual as reviewed, however, I recommend resolving two
correctness problems:

1. `certifyChartwiseProjectionIsomorphism` does not certify what its name and
   manual page say it certifies, and its returned table contradicts its own
   caveat.
2. The weighted-target example calls a degree-two morphism an isomorphism.

After those, the largest usability improvements would be an end-to-end example
on the package landing page, a systematic description of returned hash-table
keys, and a smaller basic example before the advanced non-free example on the
`steinCoordinateAlgebra` page.

## Verification performed

- Read all fourteen documentation nodes in `SteinFactorization.m2`.
- Compared every documented signature with the implementation.
- Compared the examples and claims with the test files and
  `IMPLEMENTATION.tex`.
- Inspected the recent Git history, including the removal of the redundant
  block-data and base-generator arguments and the rename from `gammaIndex` to
  `evaluationElementIndex`.
- Ran `make docs`.  All documentation examples completed successfully with
  Macaulay2 1.26.06.
- The build still emits the package-metadata warning
  `insufficient citation data: howpublished`; this is already recorded in
  `MANUAL-REVIEW.md`.

## Highest-priority corrections

### 1. `certifyChartwiseProjectionIsomorphism` overstates its certificate

**Priority: critical**

The page says the function checks the projection
`Gamma_h -> Y` chart by chart.  The implementation actually performs two
independent tests:

- the elements in `coverElements` generate a saturated cover of
  `Proj(sourceRing)`;
- every pair in `chartMapPairs` consists of mutually inverse ring maps.

It does not establish any relationship between a cover element and a map pair,
between either ring in a pair and the corresponding localization of
`sourceRing`, or between the pair and the graph returned by
`directSteinGraph`.  It also does not check that `#coverElements ==
#chartMapPairs`.  Thus inverse maps between unrelated rings can pass the test.

There is a direct contradiction in the current result table: the
implementation returns

```m2
"overlapCompatibilityCertified" => true
```

while the page's caveat says that compatibility on overlaps is not checked.
That key must not be `true` under the current implementation.

The page's example also exposes the missing association.  Its prose describes
the first map pair as the chart `y1 != 0`, but the first cover element passed is
`y0`.  The code cannot notice or reject the mismatch.

Recommended resolution:

- If this function is intended only as a small helper, rename it to something
  like `checkInverseRingMapPairsOnProjectiveCover`, remove
  `projectionIsomorphismCertified` and `overlapCompatibilityCertified`, and
  state precisely that the caller is responsible for identifying the rings
  with the relevant charts.
- If it is intended to issue a genuine certificate, redesign each chart input
  to bind together the cover element, the localized source chart, the graph
  chart, the projection map, and its inverse.  Check the number of charts and
  verify the structural maps.  Check overlaps before returning an overlap
  certificate.
- Until the implementation is changed, weaken the page headline and all uses
  of the word "certify".  Add an explicit warning that the routine only checks
  the algebraic inverse identities for caller-supplied map pairs.

This is not merely a documentation refinement: the current manual can cause a
user to interpret a much weaker test as a proof.

### 2. The weighted-target example is not an isomorphism

**Priority: critical**

The `certifiedWeightedGraph` page says:

> The isomorphism P^1 -> P(1,2) given by (r0,r1^2).

This morphism has degree two, not degree one.  Indeed, on the chart where the
weight-one coordinate `x` is nonzero, a coordinate on `P(1,2)` is `u=y/x^2`.
The displayed map sends it to `(r1/r0)^2`, so the induced rational function is
the square of a coordinate on `P^1`.

The same incorrect claim occurs in `tests/weighted.m2` (Test 5).  That test
checks only base-point-freeness, degrees, homogeneity, and primality of the
graph ideal; none of those assertions proves that the map is an isomorphism.

Recommended resolution:

- Keep the example, but call it a degree-two morphism to `P(1,2)`.
- If an isomorphism example is desired, use the map in the opposite direction,
  `P(1,2) -> P^1` given by the equal weighted-degree forms `(y0^2,y1)`, which is
  already used correctly in `tests/weighted.m2`.
- Add one line explaining how to read the weighted target chart; otherwise the
  proportional-degree condition can easily be mistaken for a claim about the
  degree of the morphism.

## API and argument review

### `evaluationElementIndex` should probably not be mandatory in the main path

All examples pass `0` to `steinCoordinateAlgebra`, and the page states that the
resulting subring is independent of the choice.  This makes the second argument
an implementation choice exposed in the most important public call.

Recommended API:

```m2
algebraData = steinCoordinateAlgebra homData
```

The function can choose a suitable nonzero generator internally and record the
choice in `"evaluationElement"` and, if useful, in a new
`"evaluationElementIndex"` key.  An option could preserve expert control:

```m2
steinCoordinateAlgebra(homData, EvaluationElementIndex => 0)
```

`evaluateSteinGenerators` is the lower-level function where an explicit index
is meaningful, so it can retain the argument.  Its page should state the valid
range and the nonzero-element precondition.

### Stabilization controls are better expressed as options

`steinDataByStabilization` has six positional arguments, three of which are
tuning controls rather than mathematical input:

```m2
steinDataByStabilization(S, Igraph, startBound,
    maxSteps, requiredMatches, hilbertMax)
```

This is hard to read at a call site and easy to transpose.  Prefer defaults and
named options for `maxSteps`, `requiredMatches`, and `hilbertMax`.  The manual
should also state that `requiredMatches > maxSteps - 1` can never succeed and
either reject that combination or explain it.

The routine increments only the first coordinate of the bound.  The page says
that it does so, but not why that search direction is appropriate or when the
second coordinate must also change.  Add this limitation to a `Caveat` section.
If no mathematical reason fixes the second coordinate, consider a caller-
supplied sequence of bounds or a search-direction option.

### Arguments that should remain

The recent removals of `d1,d2,c1,c2` and `baseImages` were good: they duplicated
information already determined by the ambient bigrading.  Conversely, the
manual is right to retain and explain:

- `targetModuleOverAmbient` in `bigradedGlobalHomData`, because the bound needs
  an ambient-ring resolution;
- `targetWeights` in `certifiedWeightedGraph`, because inference would hide a
  mistyped coordinate degree;
- the supplied bound in `steinHomDataAtBound`, because using an uncertified
  bound is the purpose of that entry point.

### Related inputs should be validated or described as unchecked

Several public functions accept objects that are required to correspond but do
not verify that correspondence:

- `directSteinGraph` requires `algebraData` to have been constructed from the
  same `homData`;
- `bigradedGlobalHomData` requires `M` and `N` to be modules over the same
  quotient and `NS` to present the same target over `S`;
- `selectCertifiedGraphComponent` requires every candidate to belong to the
  certified product ring;
- `steinHomDataAtBound` expects a two-integer bidegree;
- `steinDataByStabilization` expects a two-entry start bound and a meaningful,
  nonnegative Hilbert cutoff.

Where inexpensive, validate these conditions.  Where equality is difficult to
certify, make the caller's responsibility explicit in `Inputs` or `Caveat`.

## Naming review

Short names are normal in mathematical examples, but several usage lines make
the API harder to understand without rereading the input list.  The following
names would make the manual self-explanatory while leaving the positional API
unchanged:

| Current manual name | Suggested manual name |
|---|---|
| `S` | `ambientRing` |
| `Igraph` | `graphIdeal` |
| `r` | `truncationBound` |
| `NS` | `targetOverAmbient` |
| `hImages` | `coordinateForms` |
| `certified` | `certifiedGraphData` |
| `candidates` | `candidateIdeals` |
| output `i` | `candidateIndex` |

For consistency, choose either `graphIdeal` or `Igraph` throughout.  The code,
README, package pages, and tests currently use `igraph`, `Igraph`, `IGraph`, and
`graphIdeal` for the same concept.

`certifyChartwiseProjectionIsomorphism` is not just long; under the present
implementation it is misleading.  Its rename should follow the resolution of
the critical issue above rather than being a cosmetic abbreviation.

## Manual-wide improvements

### Add a complete first workflow to the landing page

The landing page defines the mathematical object and lists the subnodes, but a
new user must visit three pages and reconstruct the call sequence.  Add a small
end-to-end example using the square map:

```m2
homData = steinHomData(S, graphIdeal)
algebraData = steinCoordinateAlgebra homData
steinGraphData = directSteinGraph(homData, algebraData)
```

Show which three keys contain the principal results: the certified bound, the
coordinate ring of `Z`, and the graph ideal of `h`.  This also establishes the
intended reading order before the reference details.

### Document returned hash tables systematically

Most `Outputs` sections summarize only some keys.  Users must inspect the
implementation to discover the rest, and similarly named keys do not always
mean the same thing.  Add a key/type/meaning table to every hash-table-returning
page, or define shared result-table nodes and link to them.

The most important omissions are:

- `steinHomData`: `resolutionLengthLimit`, `rawHomModule`,
  `evaluationMatrix`, and the distinction between `homModule` and the selected
  strand indices;
- `steinCoordinateAlgebra`: `images`, `extraHomIndices`, `baseInclusion`, and
  `mapToLocalization`;
- `steinDataByStabilization`: the exact structure of each `history` entry and
  the meaning of `consecutiveMatches`;
- graph-building functions: variable counts, maps, source lift, and what each
  Boolean actually certifies;
- `bigradedGlobalHomData`: the exact distinction between the free cover in
  `sourceResolution` and the bounded ambient resolution of the target.

Avoid describing a free cover as a full resolution.  The package page is
careful here, but `README.md` currently says that the result contains "both
resolutions".

### State global mathematical preconditions once

The evaluation argument uses that `R` is a domain, but `steinHomData` does not
test primality and its input description asks only for a bihomogeneous ideal.
The top page calls the graph a variety, which implies the intended assumption,
but this is too indirect for an API precondition.

Add a short "Assumptions" paragraph to the landing page and link to it from the
main entry points.  It should say at least whether the package expects:

- a field as coefficient ring;
- a prime/reduced graph ideal;
- a genuine graph rather than an arbitrary bihomogeneous subscheme;
- projective varieties rather than general schemes;
- any characteristic restrictions.

State which conditions are checked and which are trusted.  In particular,
`evaluateSteinGenerators` should not present injectivity as unconditional for
every ideal accepted by `steinHomData`.

### Separate reference documentation from development commentary

There are several commented-out `Text` blocks in the documentation source.
They do not appear in the built pages but make the source harder to review and
create uncertainty about whether text was intentionally removed or temporarily
disabled.  Delete them after preserving any still-useful rationale in Git
history or in developer comments outside the `doc` block.

The documentation also refers directly to test filenames in several places.
That is useful for developers, but installed-package users may not have the
repository layout at hand.  Give the important mathematical point in the page
itself, then make the repository/test reference supplementary.

## Page-by-page review

### `SteinFactorization` (landing page)

- Good concise definition and good explanation of the two grading blocks.
- Say "geometrically connected fibres" if that is the intended theorem-level
  assertion; the Stacks Project's general Stein factorization theorem uses that
  stronger formulation.
- Define explicitly that the first/source block describes the chosen projective
  embedding of `Y` (or of `Gamma_f`) and the second/target block describes `X`.
  The words "source" and "target" otherwise require the reader to infer which
  of the three spaces is meant.
- Add the end-to-end example and assumptions described above.

### `steinHomData`

- The square-map example is compact, appropriate, and well interpreted.
- Explain the difference between `homModule`, which has been truncated to the
  nonnegative orthant, and the indices selected for the `(0,>=0)` strand.
- List the result keys and types.
- State the cost of the bounded resolution before the example, with a link to
  the supplied-bound alternative.
- Remove the disabled paragraph at the start of the example area or restore it
  as ordinary prose if it still adds information.

### `steinCoordinateAlgebra`

- The current conic-target example is mathematically valuable because it shows
  a non-polynomial base ring and a non-free finite module.  It is too elaborate
  as the first operational example of this central function.
- First continue the square-map example from `steinHomData` in a few lines and
  show `ring` and `definingIdeal`.  Keep the current example as an "advanced
  example: non-free over A" subsection.
- The phrase "the first of these modulo the second" depends on output order.
  Say explicitly `polynomialRing / definingIdeal`.
- The paragraph around `C_n = k[u,v]_{4n}` is dense.  Split it into: what `A`
  is, what `C` is, why two degree-one module generators are missing from `A`,
  and what the presentation columns mean.
- Make `evaluationElementIndex` optional or internal, as discussed above.
- Explain what happens when the chosen index is out of range or the chosen
  element is zero.
- The caveat should say whether "has not been run to completion" means a known
  correctness limitation, an expected timeout, or simply excessive cost.

### `directSteinGraph`

- The construction with the Rees parameter is explained carefully.
- The sentence "Working over R[1/gamma] rather than R is what saturates the
  result" is too compressed.  State exactly with respect to which element or
  irrelevant ideal the output is saturated and what closure is obtained.
- Interpret the displayed graph ideal in the example, not only its homogeneity
  and primality.  A reader should be able to identify which new coordinate is
  the extra Stein generator.
- State that the two input tables must correspond; the implementation currently
  trusts this.
- The output description should list `jointRing`, `graphIdeal`, `graphMap`, and
  the meaning of `saturationByLocalization`.

### `blockDegreeData`

- Both standard and weighted examples are appropriate and clearly motivate why
  the four integers are inferred rather than supplied.
- Say whether the input is required to be a polynomial ring.  The wording says
  merely "bigraded ring", while its role elsewhere is specifically the ambient
  polynomial ring.
- Give the actual output after each example in the explanatory sentence,
  `{1,1,2,2}` and `{1,1,3,2}`, so the page remains understandable when skimmed.
- The page is otherwise close to ready.

### `steinHomDataAtBound`

- The certified/uncertified distinction is excellent and should be preserved.
- State explicitly that `r` must be a two-entry integer list and describe the
  partial order meant by "large enough".
- Consider showing equality with `steinHomData(S,Igraph)#"bound"` in this small
  example.  It would substantiate the prose that `{1,0}` happens to agree.
- "Out of reach" should be quantified or replaced by a reproducible observation
  from the benchmark, since machine-dependent absolute claims age quickly.

### `steinDataByStabilization`

- The example is now properly introduced and clearly says that stabilization
  is evidence rather than proof.
- Move the one-coordinate search limitation into a `Caveat` and explain its
  mathematical motivation.
- Explain why the fingerprint consists of dimension, finitely many Hilbert
  values, and module-generator degrees, and name plausible changes it can miss.
- Explain that `chosenBound` is the last tested bound even when the preceding
  bound is the first member of the matching pair.  The current prose does this
  for the example; it belongs in the general output description too.
- Replace the three positional tuning arguments with options and validate
  impossible combinations.
- "That is the only place it can be checked" is too absolute.  Say instead that
  the example is a sanity check against an independently certifiable case.

### `certifiedHomogeneousGraph`

- The twisted-cubic example is appropriate.
- `hImages` is described as forms "in B/I", while the example passes forms in
  `B` and the implementation reduces them modulo `I`.  Say that representatives
  in `B` are accepted and interpreted in `B/I`.
- Show the immediate handoff to `steinHomData`, since that is the reason this
  helper appears in the package.
- List all returned keys and distinguish the base-point-free check from the
  assertion that the constructed kernel is a graph.

### `certifiedWeightedGraph`

- Correct the false isomorphism claim as described in the critical section.
- Add a failing example with non-proportional degrees; the test suite already
  has a concise one and it directly supports the explanation for requiring
  `targetWeights`.
- As on the homogeneous page, clarify whether coordinate inputs are elements of
  `B` or residue classes in `B/I`.
- Explain what common multiplier `e` means geometrically; proportional weighted
  degrees make the map well-defined but do not determine whether it is finite,
  birational, or an isomorphism.

### `selectCertifiedGraphComponent`

- Explain that candidate generation is not implemented by this package; this
  function only selects among candidates supplied by another computation.
- Rename the usage output from `i` to `candidateIndex` and the inputs in the
  example to `certifiedGraphData` and `candidateIdeals`.
- State that ideals are compared only up to saturation, and therefore the
  returned index identifies a biprojective subscheme rather than literal ideal
  equality.
- Add the requirement that all candidate ideals belong to `productRing`.

### `certifyChartwiseProjectionIsomorphism`

- Do not accept this page as reviewed until the critical certificate problem is
  resolved.
- The current caveat is directionally useful but does not go far enough: the
  function also fails to identify the supplied rings and maps with charts of
  the source and graph.
- Correct the `y0`/`y1` ordering mismatch if the current example is retained.
- A genuine chart example should display, for each cover element, the source
  localization, graph localization, projection, and inverse together.

### `evaluateSteinGenerators`

- The mathematical explanation is one of the clearest pages in the manual.
- Make the domain assumption explicit and say that the function does not check
  it.
- Specify the valid index range and whether the element must be nonzero.
- The exact first generator (`y1`) may depend on generator ordering.  Avoid
  making prose correctness depend on that ordering unless the test suite pins
  it down for supported Macaulay2 versions.
- Consider returning or displaying pairs of each selected Hom degree and its
  evaluated numerator, which would make the output easier to interpret.

### `bigradedGlobalHomData`

- The explanation of the fourth argument is strong and directly answers the
  obvious API question.
- Rename `NS` to `targetOverAmbient` in the usage and example.
- Explain the sign convention in `R^{{1,1}}` and show the expected movement of
  the bound numerically; otherwise the shifted example demonstrates a change
  without teaching the reader how to predict it.
- State that `sourceResolution` records only the free cover requested with
  `LengthLimit => 0`, not a computed tail of the source resolution.
- State whether and how the function checks that `NS` really represents `N`
  after restriction/base change; currently it trusts the caller.

### `Bibliography`

- The Yasuda citation is current as of this review: arXiv v2 is the latest
  listed version, dated 2026-04-04.
- Replace the Stacks Project homepage link with the direct Stein factorization
  section, <https://stacks.math.columbia.edu/tag/03GX>, or the precise theorem
  tag used for the statement.
- Add a DOI or stable journal link for Smith (2000).
- If numbered results are tied deliberately to v2, say so.  Otherwise link the
  versionless arXiv record and record the checked version separately, so a new
  version does not silently change section and proposition numbers.

## Cross-document consistency

Although the package pages were the main target, the following adjacent files
should be kept consistent when the manual is revised:

- `README.md` and `IMPLEMENTATION.tex` still present the explicit
  `evaluationElementIndex` in the main three-call workflow.
- `README.md` describes the general Hom result as containing "both
  resolutions", while the source side is currently only a free cover.
- `README.md` says the weighted tests include "an isomorphism and a degree-two
  map out of P(1,2)"; that statement is correct for the weighted-source tests.
  It should not be used to support the incorrect weighted-target isomorphism
  claim.
- `IMPLEMENTATION.tex` and `MANUAL-REVIEW.md` record Macaulay2 1.24.11 in places,
  while the documentation build used 1.26.06.  Separate the minimum supported
  version from the version used for current timings and accepted output.
- Add `HomePage`/`HowPublished` metadata as appropriate so the successful
  documentation build is warning-free.

## Suggested order of work

1. Resolve the semantics and naming of
   `certifyChartwiseProjectionIsomorphism`; correct its Boolean result keys and
   example.
2. Correct the weighted-target example and corresponding test comments.
3. Decide whether `evaluationElementIndex` remains a required public argument.
4. Add an end-to-end landing-page example and explicit global assumptions.
5. Add hash-table key documentation to every relevant page.
6. Split the `steinCoordinateAlgebra` material into a basic example and an
   advanced non-free example.
7. Convert stabilization tuning parameters to options and document the search
   direction.
8. Apply the smaller naming, bibliography, and cross-document consistency
   improvements.
9. Rebuild with `make docs-all`, reread every rendered page, and update
   `MANUAL-REVIEW.md` with the revision at which each page was accepted.

## Proposed acceptance status

The existing review ledger marks the landing page and `steinHomData` as
reviewed at earlier commits.  Because later commits changed prose in
`steinHomData`, its acceptance revision should be refreshed after rereading the
rendered page.  For this review, no additional page should be marked accepted:
this report identifies recommended changes but intentionally does not modify or
approve the manual itself.
