needsPackage("SteinFactorization", FileName => "SteinFactorization.m2");

-- A target that is not a projective space, and a strand that is not free.
--
-- Every other test sends Y onto a whole projective space by a coordinatewise
-- power map.  Two things follow that are properties of those examples rather
-- than of the algorithm, and that no other test can therefore see: A comes out
-- a polynomial ring, and C comes out free over it, so strandAPresentation is
-- zero everywhere and the finite A-module machinery is never exercised.
--
--   Y = P^1_{s,t} x P^1_{u,v}  --h-->  Z = P^1_{u,v}  --g-->  X = conic in P^2
--
-- h is the second projection, with P^1 fibers.  X is the conic x0*x2 = x1^2,
-- that is P^1_{u,v} embedded by (u^2,uv,v^2), and g is two-to-one onto it, so
-- f = g o h is given by the quartics (u^4, u^2*v^2, v^4).  Both halves of the
-- factorization do something: a general fiber of f is two disjoint P^1's.
--
-- A is cut out by the equation of the conic, so it is not a polynomial ring.
-- And O_X(1) is O(2) on the P^1 underneath the conic, so A reaches only the
-- monomials of even degree there, while C_n = k[u,v]_{4n} contains the odd
-- ones too.  The two of those in degree one, u*v^3 and u^3*v, are the extra
-- module generators, and they satisfy two relations over A, which is what the
-- presentation matrix records.

sgraph = QQ[y0,y1,y2,y3,x0,x1,x2,
    Degrees=>{{1,0},{1,0},{1,0},{1,0},{0,1},{0,1},{0,1}}];
param = QQ[s,t,u,v,sourceScale,targetScale];
igraph = kernel map(param,sgraph,{
    s*u*sourceScale, s*v*sourceScale, t*u*sourceScale, t*v*sourceScale,
    u^4*targetScale, u^2*v^2*targetScale, v^4*targetScale});
assert(numgens igraph == 8);
assert(codim igraph == 3);
assert(isPrime igraph);

-- Small enough that the Corollary 4.3 bound is computed, not supplied.
d = steinHomData(sgraph,igraph);
assert(d#"certifiedBound");
assert(d#"bound" == {1,0});
assert(d#"steinGeneratorDegrees" == {{0,0},{0,1},{0,1}});

c = steinCoordinateAlgebra(d,0);

-- A is the coordinate ring of the conic, not a polynomial ring.  It keeps the
-- bidegrees of the ambient ring, so its Hilbert function is read at {0,n}.
aa = c#"baseRing";
assert(ideal aa != 0);
assert(numgens ideal aa == 1);
assert(dim aa == 2);            -- the affine cone over the conic
assert(apply({1,2,3},n -> hilbertFunction({0,n},aa)) == {3,5,7});

-- The strand is not free over it, so the presentation carries content: three
-- generators and two relations.
strand = c#"strandAsAModule";
assert(not isFreeModule strand);
assert(c#"strandAPresentation" != 0);
assert(numgens strand == 3);
assert(degrees strand == {{0,0},{0,1},{0,1}});
assert(numcols c#"strandAPresentation" == 2);

-- Z is P^1, and C_n = k[u,v]_{4n} has dimension 4n+1 against 2n+1 for A.
-- Those two Hilbert functions are a second, independent reason the module
-- cannot be free: a free module of rank r on generators of degrees e_i would
-- have dim C_n = sum_i (2(n-e_i)+1) = 2*r*n + (r - 2*sum e_i).  Matching
-- 4n+1 forces r = 2 and then 2*sum e_i = 1, which no integers satisfy.
assert(dim(c#"ring") == 2);
assert(apply({1,2,3},n -> hilbertFunction(n,c#"ring")) == {5,9,13});
assert(isPrime(c#"definingIdeal"));

g = directSteinGraph(d,c);
assert(isHomogeneous(g#"graphIdeal"));
assert(isPrime(g#"graphIdeal"));

-- h is not an isomorphism, which is what separates this from a finite f.
-- Over the point [1:1:1] of X the equations u^4 = u^2*v^2 = v^4 give v^2 = u^2,
-- so two points of Z; the s:t factor is free above each.  A general fiber of
-- f is therefore two disjoint P^1's, and h contracts each of them.
rfiber = QQ[fs,ft,fu];
ifiber = ideal(fu^2-1);
assert(radical ifiber == ifiber);
fiberComponents = minimalPrimes ifiber;
assert(#fiberComponents == 2);
assert(all(fiberComponents,p -> dim(rfiber/p) == 2));

print("OK conic target: A is the conic's coordinate ring, not a polynomial ring.");
print("OK conic target: the strand is not free, so its presentation is nonzero.");
print("OK conic target: H(n) = 4n+1 for C against 2n+1 for A, so Z is P^1 over the conic.");
print("OK conic target: the graph of h is prime and bihomogeneous.");
print("OK conic target: a general fiber of f is two disjoint P^1's, so h contracts.");
