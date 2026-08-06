needsPackage("SteinFactorization", FileName => "SteinFactorization.m2");

-- Weighted bigraded input.  Only the split into a source block of degrees
-- (positive,0) and a target block of degrees (0,positive) is structural; the
-- degrees inside a block need not be 1.  These tests exercise that, and pin
-- down the two places where the weights actually have to be read: the sums
-- c1,c2 of Corollary 4.3, and the graph construction.

-- run-tests.sh passes --stop, which sets stopIfError and stops `try` from
-- catching anything.  The error-path checks below turn it off for the one call.
errorsOut = f -> (
    stopIfError = false;
    r := try (f(); false) else true;
    stopIfError = true;
    r
    );

-- Test 1: the four numbers of Section 4 are determined by the ambient ring.
sStd = QQ[y0,y1,x0,x1,Degrees=>{{1,0},{1,0},{0,1},{0,1}}];
assert(blockDegreeData sStd == {1,1,2,2});

sWt = QQ[y0,y1,x0,x1,Degrees=>{{1,0},{2,0},{0,1},{0,1}}];
-- c1 is the weight sum 1+2=3, not the variable count 2.
assert(blockDegreeData sWt == {1,1,3,2});

-- A variable in neither block, or in both, is rejected.
sMixed = QQ[y0,y1,Degrees=>{{1,1},{0,1}}];
assert(errorsOut(() -> blockDegreeData sMixed));
sZero = QQ[y0,y1,Degrees=>{{0,0},{0,1}}];
assert(errorsOut(() -> blockDegreeData sZero));

-- Test 2: P(1,2) -> P^1, [y0:y1] |-> [y0^2:y1].
-- y0^2 and y1 span the weighted degree-2 part of k[y0,y1], so f is an
-- isomorphism.  Then Z = Y and g^*O_X(1) = O_{P(1,2)}(2), whose section ring
-- is sum_n k[y0,y1]_{2n}, of dimension n+1 in degree n: a polynomial ring in
-- two variables, so no relations and H(n) = n+1.
use sWt;
iIso = ideal(x0*y1-x1*y0^2);
assert(isHomogeneous iIso);
dIso = steinHomData(sWt,iIso);
assert(dIso#"certifiedBound");
assert(dIso#"bound" == {0,0});
assert(dIso#"steinGeneratorDegrees" == {{0,0}});
cIso = steinCoordinateAlgebra(dIso,0);
assert(numgens(cIso#"definingIdeal") == 0);
assert(dim(cIso#"ring") == 2);
assert(apply({1,2,3},n -> hilbertFunction(n,cIso#"ring")) == {2,3,4});
assert(isPrime((directSteinGraph(dIso,cIso))#"graphIdeal"));

-- Test 3: P(1,2) -> P^1, [y0:y1] |-> [y0^4:y1^2], a degree-2 map.
-- Here the bound is not trivial, so the truncation has work to do.  Now
-- g^*O_X(1) = O_{P(1,2)}(4) = O_{P^1}(2), so the section ring is the second
-- Veronese subring of k[u,v]: one conic relation and H(n) = 2n+1.
use sWt;
iSq = ideal(x0*y1^2-x1*y0^4);
dSq = steinHomData(sWt,iSq);
assert(dSq#"certifiedBound");
assert(dSq#"bound" == {2,0});
assert(dSq#"steinGeneratorDegrees" == {{0,0},{0,1}});
cSq = steinCoordinateAlgebra(dSq,0);
assert(numgens(cSq#"definingIdeal") == 1);
assert(codim(cSq#"definingIdeal") == 1);
assert(dim(cSq#"ring") == 2);
assert(apply({1,2,3},n -> hilbertFunction(n,cSq#"ring")) == {3,5,7});
assert(isPrime((directSteinGraph(dSq,cSq))#"graphIdeal"));

-- Test 4: a weighted source survives the graph construction.  The map
-- P(1,2) -> P^1 given by (r0^2,r1) is the one of Test 2, so the graph it
-- builds must run through the pipeline to the same answers.
sourceWt = QQ[r0,r1,Degrees=>{1,2}];
gWtSource = certifiedWeightedGraph(sourceWt,ideal(0_sourceWt),{r0^2,r1},{1,1});
assert(gWtSource#"basePointFree");
-- The source block keeps its own degrees rather than being flattened to 1.
assert(degrees(gWtSource#"productRing") == {{1,0},{2,0},{0,1},{0,1}});
assert(blockDegreeData(gWtSource#"productRing") == {1,1,3,2});
dFromGraph = steinHomData(gWtSource#"productRing",gWtSource#"graphIdeal");
assert(dFromGraph#"bound" == {0,0});
cFromGraph = steinCoordinateAlgebra(dFromGraph,0);
assert(apply({1,2,3},n -> hilbertFunction(n,cFromGraph#"ring")) == {2,3,4});

-- Test 5: a weighted target.  A morphism to P(a_0,...,a_n) is cut out by forms
-- with deg(h_i) = a_i*e for one common e.  With weights (1,2), (r0,r1^2)
-- defines a degree-two map P^1 -> P(1,2): on the chart y0 != 0, the invariant
-- coordinate y1/y0^2 pulls back to (r1/r0)^2.
sourceStd = QQ[r0,r1];
gWtTarget = certifiedWeightedGraph(sourceStd,ideal(0_sourceStd),{r0,r1^2},{1,2});
assert(gWtTarget#"basePointFree");
assert(degrees(gWtTarget#"productRing") == {{1,0},{1,0},{0,1},{0,2}});
assert(gWtTarget#"targetWeights" == {1,2});
assert(isHomogeneous(gWtTarget#"graphIdeal"));
assert(isPrime(gWtTarget#"graphIdeal"));

-- Coordinates whose degrees are not proportional to the weights are rejected
-- rather than reinterpreted as a map to some other weighted space.
use sourceStd;
assert(errorsOut(() -> certifiedWeightedGraph(sourceStd,ideal(0_sourceStd),{r0,r1},{1,2})));
-- The unweighted wrapper is the all-weights-one case, and still demands that
-- the coordinate degrees agree.
assert(errorsOut(() -> certifiedHomogeneousGraph(sourceStd,ideal(0_sourceStd),{r0,r1^2})));

print("OK weighted: block data read off the ambient ring, weight sums checked.");
print("OK weighted: P(1,2) -> P1 isomorphism, section ring k[u,v].");
print("OK weighted: P(1,2) -> P1 of degree 2, second Veronese subring of k[u,v].");
print("OK weighted: weighted source and weighted target graph construction.");
