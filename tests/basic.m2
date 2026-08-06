needsPackage("SteinFactorization", FileName => "SteinFactorization.m2");

-- Test 1: identity P^1 -> P^1.
s1 = QQ[y0,y1,x0,x1,Degrees=>{{1,0},{1,0},{0,1},{0,1}}];
iid = ideal(y0*x1-y1*x0);
did = steinHomData(s1,iid);
assert(did#"bound" == {0,0});
assert(did#"steinGeneratorDegrees" == {{0,0}});

-- Test 2: finite square map [s:t] -> [s^2:t^2].
use s1;
isq = ideal(y0^2*x1-y1^2*x0);
dsq = steinHomData(s1,isq);
assert(dsq#"bound" == {1,0});
assert(dsq#"steinGeneratorDegrees" == {{0,0},{0,1}});
csqGeneral = steinCoordinateAlgebra(dsq,0);
assert(codim(csqGeneral#"definingIdeal") == 1);
assert(numgens(csqGeneral#"definingIdeal") == 1);
gsqDirect = directSteinGraph(dsq,csqGeneral);
assert(gsqDirect#"saturationByLocalization");
assert(isPrime(gsqDirect#"graphIdeal"));
-- The graph sits in a product, so its ideal has to be bihomogeneous.  It is
-- only so if the variables for the coordinate algebra are given the bidegrees
-- (0,b_i) of the sections they stand for; reading those degrees off the
-- localization instead loses the grading of its coefficient ring and makes the
-- ideal inhomogeneous.
assert(isHomogeneous(gsqDirect#"graphIdeal"));
assert(drop(degrees(gsqDirect#"jointRing"),gsqDirect#"ambientVariableCount")
    == apply(degrees(csqGeneral#"polynomialRing"),e -> {0,e#0}));

rsq = dsq#"ring";
esq = evaluateSteinGenerators(dsq,0);
lsq0 = rsq[usq,Degrees=>{{-1,0}}];
lsq = lsq0/ideal(usq*y1-1);
psq = QQ[X0,X1,z,Degrees=>{1,1,1}];
phisq = map(lsq,psq,{x0,x1,sub(esq#1,lsq)*usq});
icsq = kernel phisq;
assert(icsq == ideal(X0*X1-z^2));

-- Test 3: finite cubic map [s:t] -> [s^3:t^3].
-- This is more nontrivial: two new degree-one generators are required and
-- Proj C is the twisted cubic, hence still isomorphic to the source P^1.
use s1;
icu = ideal(y0^3*x1-y1^3*x0);
dcu = steinHomData(s1,icu);
assert(dcu#"bound" == {2,0});
assert(dcu#"steinGeneratorDegrees" == {{0,0},{0,1},{0,1}});
ccuGeneral = steinCoordinateAlgebra(dcu,0);
assert(codim(ccuGeneral#"definingIdeal") == 2);
assert(numgens(ccuGeneral#"definingIdeal") == 3);
gcuDirect = directSteinGraph(dcu,ccuGeneral);
assert(gcuDirect#"saturationByLocalization");
assert(isPrime(gcuDirect#"graphIdeal"));

rcu = dcu#"ring";
ecu = evaluateSteinGenerators(dcu,0);
lcu0 = rcu[ucu,Degrees=>{{-2,0}}];
lcu = lcu0/ideal(ucu*y1^2-1);
pcu = QQ[A0,A1,A2,A3,Degrees=>{1,1,1,1}];
-- Images: t^3, s*t^2, s^2*t, s^3 (the order is immaterial).
phicu = map(lcu,pcu,{
    x1,
    sub(ecu#1,lcu)*ucu,
    sub(ecu#2,lcu)*ucu,
    x0
    });
iccu = kernel phicu;
expectedTwistedCubic = ideal(A1^2-A0*A2,A1*A2-A0*A3,A2^2-A1*A3);
assert(iccu == expectedTwistedCubic);

ccu = pcu/iccu;
ax = QQ[p,q,Degrees=>{1,1}];
by = QQ[s,t,Degrees=>{1,1}];
gcuSharp = map(ccu,ax,{A3,A0});
hcuSharp = map(by,ccu,{t^3,s*t^2,s^2*t,s^3});
fcuSharp = map(by,ax,{s^3,t^3});
assert(all(flatten entries vars ax,
    v -> (hcuSharp*gcuSharp)(v) == fcuSharp(v)));
assert(kernel hcuSharp == 0);

-- Full A-strand extraction is invariant for r=2,3; the heuristic stops after
-- one consecutive match and clearly labels the chosen bound non-certified.
use s1;
stabCubic = steinDataByStabilization(
    s1,icu,{1,0},3,1,2);
assert(stabCubic#"stabilized");
assert(stabCubic#"chosenBound" == {3,0});
assert(not stabCubic#"certifiedBound");

-- Automatic graph construction and isomorphism certificate for h.
sourceP1 = QQ[r0,r1,Degrees=>{1,1}];
zeroSourceIdeal = ideal(0_sourceP1);
graphCertificate = certifiedHomogeneousGraph(
    sourceP1,zeroSourceIdeal,{r1^3,r0*r1^2,r0^2*r1,r0^3});
assert(graphCertificate#"basePointFree");
assert(graphCertificate#"projectionIsomorphismCertified");
selectedGraphIndex = selectCertifiedGraphComponent(
    graphCertificate,{graphCertificate#"graphIdeal"});
assert(selectedGraphIndex == 0);

-- Test 4: a genuinely mixed case with positive-dimensional connected fibers.
-- Y=P^1_{s,t} x P^1_{u,v}, embedded by Segre coordinates
--   a=su, b=sv, c=tu, d=tv,
-- and f([s:t],[u:v])=[s^3:t^3].  Its Stein factorization is
--   Y -> P^1_{s,t} -> P^1,
-- where the first map has P^1 fibers and the second map has degree 3.
s2 = QQ[a,b,c,d,x0,x1,
    Degrees=>{{1,0},{1,0},{1,0},{1,0},{0,1},{0,1}}];
param = QQ[ss,tt,uu,vv];
graphParam = map(param,s2,
    {ss*uu,ss*vv,tt*uu,tt*vv,ss^3,tt^3});
imixed = kernel graphParam;
dmixed = steinHomData(s2,imixed);
assert(dmixed#"bound" == {2,0});
assert(dmixed#"steinGeneratorDegrees" == {{0,0},{0,1},{0,1}});
cmixedGeneral = steinCoordinateAlgebra(dmixed,0);
assert(codim(cmixedGeneral#"definingIdeal") == 2);
assert(numgens(cmixedGeneral#"definingIdeal") == 3);
gmixedDirect = directSteinGraph(dmixed,cmixedGeneral);
assert(gmixedDirect#"saturationByLocalization");
assert(isPrime(gmixedDirect#"graphIdeal"));

rmixed = dmixed#"ring";
emixed = evaluateSteinGenerators(dmixed,0);
lm0 = rmixed[um,Degrees=>{{-2,0}}];
lm = lm0/ideal(um*d^2-1);
pm = QQ[M0,M1,M2,M3,Degrees=>{1,1,1,1}];
phim = map(lm,pm,{
    x1,
    sub(emixed#1,lm)*um,
    sub(emixed#2,lm)*um,
    x0
    });
icm = kernel phim;
expectedMixed = ideal(M1^2-M0*M2,M1*M2-M0*M3,M2^2-M1*M3);
assert(icm == expectedMixed);

-- Chart-gluing certificate for the projection Gamma_h -> Y in the mixed
-- example.  The four Segre charts a,b,c,d != 0 cover Y.  On the a,b charts
-- put r=t/s; on c,d put r=s/t.  The three affine twisted-cubic coordinates
-- are r,r^2,r^3, so every graph chart is explicitly the source chart.
bseg0 = QQ[ya,yb,yc,yd,Degrees=>{1,1,1,1}];
bseg = bseg0/ideal(ya*yd-yb*yc);

aa = QQ[ra,wa];
ga0 = QQ[rga,wga,qa1,qa2,qa3];
ga = ga0/ideal(qa1-rga,qa2-rga^2,qa3-rga^3);
fa = map(ga,aa,{rga,wga});
iga = map(aa,ga,{ra,wa,ra,ra^2,ra^3});

ab = QQ[rb,wb];
gb0 = QQ[rgb,wgb,qb1,qb2,qb3];
gbchart = gb0/ideal(qb1-rgb,qb2-rgb^2,qb3-rgb^3);
fb = map(gbchart,ab,{rgb,wgb});
igb = map(ab,gbchart,{rb,wb,rb,rb^2,rb^3});

ac = QQ[rc,wc];
gc0 = QQ[rgc,wgc,qc1,qc2,qc3];
gc = gc0/ideal(qc1-rgc,qc2-rgc^2,qc3-rgc^3);
fc = map(gc,ac,{rgc,wgc});
igc = map(ac,gc,{rc,wc,rc,rc^2,rc^3});

ad = QQ[rd,wd];
gd0 = QQ[rgd,wgd,qd1,qd2,qd3];
gd = gd0/ideal(qd1-rgd,qd2-rgd^2,qd3-rgd^3);
fd = map(gd,ad,{rgd,wgd});
igd = map(ad,gd,{rd,wd,rd,rd^2,rd^3});

mixedChartCertificate = certifyChartwiseProjectionIsomorphism(
    bseg,{ya,yb,yc,yd},{{fa,iga},{fb,igb},{fc,igc},{fd,igd}});
assert(mixedChartCertificate#"projectionIsomorphismCertified");
assert(mixedChartCertificate#"numberOfCharts" == 4);

-- Test 5: P^2 -> P^2, [s:t:u] |-> [s^2:t^2:u^2].
-- The Stein intermediate is P^2 in its quadratic Veronese embedding in P^5.
sp2 = QQ[Y0,Y1,Y2,U0,U1,U2,
    Degrees=>{{1,0},{1,0},{1,0},{0,1},{0,1},{0,1}}];
paramp2 = QQ[ps,pt,pu,lambda,mu];
graphp2 = kernel map(paramp2,sp2,
    {ps*lambda,pt*lambda,pu*lambda,
     ps^2*mu,pt^2*mu,pu^2*mu});
dp2 = steinHomData(sp2,graphp2);
assert(dp2#"bound" == {2,0});
assert(dp2#"steinGeneratorDegrees" ==
    {{0,0},{0,1},{0,1},{0,1}});
cp2 = steinCoordinateAlgebra(dp2,0);
jp2 = cp2#"definingIdeal";
assert(numgens jp2 == 6);
assert(codim jp2 == 3);
assert(degree jp2 == 4);
assert(all(degrees source gens jp2,d -> d == {2}));
-- Hilbert function of the second Veronese of QQ[s,t,u]: H(n)=binomial(2n+2,2).
assert(hilbertFunction(2,cp2#"ring") == 15);
gp2 = directSteinGraph(dp2,cp2);
assert(gp2#"saturationByLocalization");
assert(isPrime(gp2#"graphIdeal"));

-- Test 6: P^2 -> P^2, [s:t:u] |-> [s^3:t^3:u^3].
-- This stresses non-standard output: Hom is minimal as an A-module and returns
-- one degree-two algebraically redundant generator in addition to the ten
-- degree-one generators of the third Veronese ring.
sp2c = QQ[V0,V1,V2,W0,W1,W2,
    Degrees=>{{1,0},{1,0},{1,0},{0,1},{0,1},{0,1}}];
paramp2c = QQ[cs,ct,cu,clambda,cmu];
graphp2c = kernel map(paramp2c,sp2c,
    {cs*clambda,ct*clambda,cu*clambda,
     cs^3*cmu,ct^3*cmu,cu^3*cmu});
dp2c = steinHomData(sp2c,graphp2c);
assert(dp2c#"bound" == {4,0});
assert(#dp2c#"steinGeneratorIndices" == 9);
assert(#select(dp2c#"steinGeneratorDegrees",d -> d == {0,1}) == 7);
assert(#select(dp2c#"steinGeneratorDegrees",d -> d == {0,2}) == 1);
cp2c = steinCoordinateAlgebra(dp2c,0);
assert(dim(cp2c#"ring") == 3);
assert(hilbertFunction(1,cp2c#"ring") == 10);
assert(hilbertFunction(2,cp2c#"ring") == 28);
assert(isPrime(cp2c#"definingIdeal"));
gp2c = directSteinGraph(dp2c,cp2c);
assert(isPrime(gp2c#"graphIdeal"));

print("OK identity: C has one generator over the target data.");
print("OK square map: C is the plane conic X0*X1=z^2.");
print("OK cubic map: C is the twisted cubic.");
print("OK cubic factorization: g o h = f and h# is injective.");
print("OK direct strategy: Hom evaluations produce prime saturated graph closures.");
print("OK mixed example: P1xP1 -> P1 has twisted-cubic Stein intermediate.");
print("OK mixed graph: four affine charts glue and projection Gamma_h -> Y is an isomorphism.");
print("OK P2 square map: Stein ring is the degree-4 Veronese surface (6 quadrics in P5).");
print("OK P2 direct graph: localized Hom construction gives a prime graph closure.");
print("OK P2 cube map: third-Veronese Hilbert values H(1)=10, H(2)=28; ring and graph are prime.");
