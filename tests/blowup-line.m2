needsPackage("SteinFactorization", FileName => "SteinFactorization.m2");

-- X = Bl_L(P^3), L=V(x0,x1), in its Segre presentation inside P^7.
-- h:X->P^3 is the blow-down and g:P^3->P^3 squares the coordinates.
-- The input f=g o h has 8 disconnected points in a general fiber.

sgraph = QQ[z00,z01,z10,z11,z20,z21,z30,z31,y0,y1,y2,y3,
    Degrees=>{
        {1,0},{1,0},{1,0},{1,0},{1,0},{1,0},{1,0},{1,0},
        {0,1},{0,1},{0,1},{0,1}}];

param0 = QQ[x0,x1,x2,x3,u,v,sourceScale,targetScale];
param = param0/ideal(x0*v-x1*u);
graphParametrization = map(param,sgraph,{
    x0*u*sourceScale,x0*v*sourceScale,
    x1*u*sourceScale,x1*v*sourceScale,
    x2*u*sourceScale,x2*v*sourceScale,
    x3*u*sourceScale,x3*v*sourceScale,
    x0^2*targetScale,x1^2*targetScale,
    x2^2*targetScale,x3^2*targetScale});
igraph = kernel graphParametrization;
assert(numgens igraph == 26);
assert(codim igraph == 7);

d = steinHomData(sgraph,igraph);
assert(d#"bound" == {2,0});
assert(#d#"steinGeneratorIndices" == 8);

c = steinCoordinateAlgebra(d,0);
jc = c#"definingIdeal";
-- C is the second Veronese ring of P^3.  The Hom-as-A-module presentation
-- contains one redundant degree-two algebra generator, hence 11 variables.
assert(numgens ring jc == 11);
assert(dim(c#"ring") == 4);
assert(hilbertFunction(1,c#"ring") == 10);
assert(hilbertFunction(2,c#"ring") == 35);
assert(isPrime jc);

gh = directSteinGraph(d,c);
assert(isHomogeneous(gh#"graphIdeal"));
assert(isPrime(gh#"graphIdeal"));
assert(dim(gh#"jointRing"/gh#"graphIdeal") == dim d#"ring");

-- Independently verify the exceptional divisor of h.
ssource = QQ[q00,q01,q10,q11,q20,q21,q30,q31,
    Degrees=>{{1},{1},{1},{1},{1},{1},{1},{1}}];
sourceMap = map(param,ssource,{
    x0*u,x0*v,x1*u,x1*v,x2*u,x2*v,x3*u,x3*v});
ix = kernel sourceMap;
rx = ssource/ix;
use ssource;
ie = ideal(q00,q01,q10,q11) + ix;
assert(dim rx == 4);             -- projective dimension 3
assert(dim(ssource/ie) == 3);    -- exceptional divisor has dimension 2
assert(degree(ssource/ie) == 2); -- E is the Segre quadric P^1 x P^1

-- Compute an explicit fiber over [1:1:1:1].  On the chart x3=1 the equations
-- are x0^2=x1^2=x2^2=1.  This point avoids the branch coordinate hyperplanes;
-- all eight preimages also avoid L=V(x0,x1), where the blow-down is an
-- isomorphism.  Hence this is also the fiber of f on the blow-up.
rfiber = QQ[fx0,fx1,fx2];
ifiber = ideal(fx0^2-1,fx1^2-1,fx2^2-1);
assert(dim(rfiber/ifiber) == 0);
assert(degree(rfiber/ifiber) == 8);
assert(radical ifiber == ifiber);
fiberPrimes = minimalPrimes ifiber;
assert(#fiberPrimes == 8);
assert(all(fiberPrimes,p -> degree(rfiber/p) == 1));

print("OK: input graph has 26 equations and codimension 7.");
print("OK: Stein ring has H(1)=10, H(2)=35, as for the second Veronese of P3.");
print("OK: Stein ring and direct Hom graph are prime.");
print("OK: exceptional divisor is a degree-2 surface P1xP1.");
print("OK: fiber over [1:1:1:1] is reduced of degree 8 with eight point components.");
print("OK: all eight points avoid L, so the same fiber occurs on Bl_L(P3).");
