needsPackage("SteinFactorization", FileName => "SteinFactorization.m2");

-- Proposition 4.2 / Corollary 4.3 for the diagonal in P1 x P1.
-- The S-module N_S is a presentation of the R-module N after restriction
-- along S -> R; it supplies the ambient S-resolution required by the bound.
S = QQ[y0,y1,x0,x1,
    Degrees=>{{1,0},{1,0},{0,1},{0,1}}];
idiag = ideal(y0*x1-y1*x0);
R = S/idiag;
M = R^1;
N = R^1;
NS = coker gens idiag;

data = bigradedGlobalHomData(S,M,N,NS);
assert(data#"certifiedBound");
assert(data#"bound" == {0,0});
assert(degrees(data#"homModule") == {{0,0}});
assert(hilbertFunction({1,1},data#"homModule") == 3);

-- A shifted source gives a genuinely different M.  The lower degree of its
-- R-free presentation changes the certified truncation corner as in Prop. 4.2.
Mshift = R^{{1,1}};
shiftData = bigradedGlobalHomData(S,Mshift,N,NS);
assert(shiftData#"bound" == {1,1});
assert(shiftData#"certifiedBound");

print("OK general bigraded global Hom: diagonal structure sheaf.");
print("OK general bigraded global Hom: shifted source module.");
