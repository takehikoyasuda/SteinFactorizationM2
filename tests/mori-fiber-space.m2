needsPackage("SteinFactorization", FileName => "SteinFactorization.m2");

-- X=P^1_[s:t] x P^2_x --h--> P^2_x --g--> P^2_y,
-- g([x0:x1:x2])=[x0^2:x1^2:x2^2].
-- A general fiber of f=g o h is four disjoint copies of P^1.

sgraph = QQ[z00,z01,z02,z10,z11,z12,y0,y1,y2,
    Degrees=>{
        {1,0},{1,0},{1,0},{1,0},{1,0},{1,0},
        {0,1},{0,1},{0,1}}];
param = QQ[s,t,x0,x1,x2,sourceScale,targetScale];
graphParametrization = map(param,sgraph,{
    s*x0*sourceScale,s*x1*sourceScale,s*x2*sourceScale,
    t*x0*sourceScale,t*x1*sourceScale,t*x2*sourceScale,
    x0^2*targetScale,x1^2*targetScale,x2^2*targetScale});
igraph = kernel graphParametrization;
assert(numgens igraph == 12);
assert(codim igraph == 4);

d = steinHomData(sgraph,igraph);
assert(d#"bound" == {2,0});
assert(d#"steinGeneratorDegrees" ==
    {{0,0},{0,1},{0,1},{0,1}});

c = steinCoordinateAlgebra(d,0);
jc = c#"definingIdeal";
-- Intermediate is P^2 with its second Veronese section ring.
assert(dim(c#"ring") == 3);
assert(hilbertFunction(1,c#"ring") == 6);
assert(hilbertFunction(2,c#"ring") == 15);
assert(isPrime jc);

gh = directSteinGraph(d,c);
assert(isHomogeneous(gh#"graphIdeal"));
assert(isPrime(gh#"graphIdeal"));
assert(dim(gh#"jointRing"/gh#"graphIdeal") == dim d#"ring");

-- Fiber over [1:1:1].  On x2=1, x0^2=x1^2=1, while [s:t] is free.
rfiber = QQ[fs,ft,fx0,fx1];
ifiber = ideal(fx0^2-1,fx1^2-1);
assert(radical ifiber == ifiber);
fiberComponents = minimalPrimes ifiber;
assert(#fiberComponents == 4);
assert(all(fiberComponents,p -> dim(rfiber/p) == 2));
-- Every component ring is QQ[fs,ft], hence its projective factor is P^1.
assert(all(fiberComponents,p ->
    numgens trim substitute(p,QQ[fs,ft,fx0,fx1]) == 2));

print("OK: input graph has 12 equations and codimension 4.");
print("OK: Stein ring has H(1)=6, H(2)=15, as for the second Veronese of P2.");
print("OK: Stein ring and direct Hom graph are prime.");
print("OK: fiber over [1:1:1] is reduced with four components, each a P1.");
print("Expected connected part: P1xP2 -> P2, a Mori fiber space with K.F=-2.");
