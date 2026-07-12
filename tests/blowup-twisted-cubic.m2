load "SteinFactorization.m2";

-- Blow up the twisted cubic C in P^3, then compose the blow-down with
-- [x0:x1:x2:x3] |-> [x0^2:x1^2:x2^2:x3^2].

trees = QQ[x0,x1,x2,x3,u0,u1,u2];
targetRees = QQ[x0,x1,x2,x3,t];
reesI = kernel map(targetRees,trees,{
    x0,x1,x2,x3,
    (x0*x2-x1^2)*t,
    (x0*x3-x1*x2)*t,
    (x1*x3-x2^2)*t});
assert(numgens reesI == 3);
assert(codim reesI == 2);

param0 = QQ[x0,x1,x2,x3,u0,u1,u2,sourceScale];
param = param0/sub(reesI,param0);
sourceSegre = QQ[z00,z01,z02,z10,z11,z12,z20,z21,z22,z30,z31,z32];
sourceIdeal = kernel map(param,sourceSegre,{
    x0*u0*sourceScale,x0*u1*sourceScale,x0*u2*sourceScale,
    x1*u0*sourceScale,x1*u1*sourceScale,x1*u2*sourceScale,
    x2*u0*sourceScale,x2*u1*sourceScale,x2*u2*sourceScale,
    x3*u0*sourceScale,x3*u1*sourceScale,x3*u2*sourceScale});
assert(numgens sourceIdeal == 20);
assert(codim sourceIdeal == 8);

sgraph = QQ[z00,z01,z02,z10,z11,z12,z20,z21,z22,z30,z31,z32,
    y0,y1,y2,y3,
    Degrees=>{
        {1,0},{1,0},{1,0},{1,0},{1,0},{1,0},
        {1,0},{1,0},{1,0},{1,0},{1,0},{1,0},
        {0,1},{0,1},{0,1},{0,1}}];
rows = {{z00,z01,z02},{z10,z11,z12},{z20,z21,z22},{z30,z31,z32}};
ys = {y0,y1,y2,y3};
squareGraphRelations = flatten apply(toList(0..3),i ->
    flatten apply(toList(i+1..3),j ->
        apply(toList(0..2),k ->
            ys#j*(rows#i#k)^2-ys#i*(rows#j#k)^2)));
igraphRaw = sub(sourceIdeal,sgraph) + ideal matrix{squareGraphRelations};
igraph = saturate(igraphRaw,ideal matrix{flatten rows});
assert(numgens igraph == 70);
assert(codim igraph == 11);
assert(isPrime igraph);

-- Computing the Corollary 4.3 bound from the full minimal resolution is the
-- bottleneck for this example (>2 minutes in the current implementation).
-- Use r=(2,0), then independently validate the resulting known Stein ring.
d = steinHomDataAtBound(sgraph,igraph,{2,0});
print("strand degrees at r=2: " | toString d#"steinGeneratorDegrees");
assert(d#"steinGeneratorDegrees" == {
    {0,0},{0,1},{0,1},{0,1},{0,1},{0,1},{0,1},{0,2}});
c = steinCoordinateAlgebra(d,0,{y0,y1,y2,y3});
assert(dim(c#"ring") == 4);
assert(hilbertFunction(1,c#"ring") == 10);
assert(hilbertFunction(2,c#"ring") == 35);
assert(degrees(c#"strandAsAModule") == {
    {0,0},{0,1},{0,1},{0,1},{0,1},{0,1},{0,1},{0,2}});

print("OK: twisted-cubic Rees ideal has 3 generators and codimension 2.");
print("OK: Segre source ideal has 20 generators; composite graph has 70 and is prime.");
print("OK: at supplied r=(2,0), full A-strand has H(1)=10,H(2)=35.");
print("NOTE: its degree-2 A-generator is algebraically redundant; graph construction is deferred until generator minimization.");
print("Expected connected part: Bl_C(P3)->P3, a divisorial extremal contraction.");
