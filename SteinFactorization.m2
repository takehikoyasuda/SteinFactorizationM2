newPackage(
    "SteinFactorization",
    Version => "0.2",
    Date => "7 August 2026",
    Headline => "Stein factorization of a projective morphism given by its graph",
    Authors => {{ Name => "Takehiko Yasuda", Email => "yasuda.takehiko.sci@osaka-u.ac.jp" }},
    HomePage => "https://github.com/takehikoyasuda/SteinFactorizationM2",
    Keywords => { "Algebraic Geometry" },
    PackageExports => { "Truncations", "Saturation", "MinimalPrimes" },
    AuxiliaryFiles => false
    )

export {
    "blockDegreeData",
    "bigradedGlobalHomData",
    "steinHomData",
    "steinHomDataAtBound",
    "evaluateSteinGenerators",
    "steinCoordinateAlgebra",
    "steinDataByStabilization",
    "directSteinGraph",
    "certifiedWeightedGraph",
    "certifiedHomogeneousGraph",
    "selectCertifiedGraphComponent",
    "checkChartwiseInverses"
    }


-- Core implementation of Section 5.1 of Yasuda, arXiv:2603.13703v2
-- (https://arxiv.org/abs/2603.13703v2).
-- Input convention: variables of the source block have degrees (positive,0),
-- variables of the target block have degrees (0,positive).  Only the split into
-- two blocks matters; the degrees within a block need not be 1, so weighted
-- projective spaces are allowed, as in the paper.
-- Corollary 4.3 is stated in terms of the four numbers of Section 4: block s is
-- x_{s,0},...,x_{s,ds}, and cs = sum_t deg(x_{s,t}).  They are not arguments to
-- the bound-computing entry points, because the ambient ring already determines
-- them -- see blockDegreeData.  Note that cs is
-- the weight sum, equal to the variable count only when every weight is 1.

-- The block structure is visible in the ambient degrees: a source variable has
-- degree (positive,0) and a target variable (0,positive).  Returns the four
-- numbers of Section 4, {d1,d2,c1,c2}, so that no caller has to restate them.
blockDegreeData = ambient -> (
    degs := degrees ambient;
    if degreeLength ambient != 2 then
        error "the ambient ring must be bigraded";
    sourceDegs := select(degs,d -> d#1 == 0);
    targetDegs := select(degs,d -> d#0 == 0);
    -- A variable of degree (0,0) would be counted in both blocks, and one with
    -- both components nonzero in neither; either way the counts disagree.
    if #sourceDegs + #targetDegs != #degs then
        error "every variable must have degree (positive,0) or (0,positive)";
    if #sourceDegs == 0 or #targetDegs == 0 then
        error "both blocks must be nonempty";
    if not all(sourceDegs,d -> d#0 > 0) or not all(targetDegs,d -> d#1 > 0) then
        error "variable degrees must be positive in their own block";
    {#sourceDegs-1,
     #targetDegs-1,
     sum apply(sourceDegs,d -> d#0),
     sum apply(targetDegs,d -> d#1)}
    );

componentMax = (ll,k) -> (
    if #ll == 0 then -infinity else max apply(ll,d -> d#k)
    );

componentMin = (ll,k) -> (
    if #ll == 0 then error "cannot take a minimum over an empty list"
    else min apply(ll,d -> d#k)
    );

shiftCoordinateMax = (ff,i,k) -> (
    if i < 0 or i > length ff then -infinity
    else componentMax(degrees ff_i,k)
    );

aPair = (ff,i,j) -> {
    shiftCoordinateMax(ff,i,0),
    shiftCoordinateMax(ff,j,1)
    };

pairMax = ll -> {
    max apply(ll,p -> p#0),
    max apply(ll,p -> p#1)
    };

sourceLowerShift = sourceResolution -> {
    componentMin(degrees sourceResolution_0,0),
    componentMin(degrees sourceResolution_0,1)
    };

bigradedTruncationBound = (ff,d1,d2,c1,c2) -> (
    dsum := d1+d2;
    bb := pairMax {
        aPair(ff,d1+1,d2+1),
        aPair(ff,d1,d2),
        aPair(ff,dsum+1,dsum+1),
        aPair(ff,dsum,dsum)
        };
    {bb#0-c1+1,bb#1-c2+1}
    );

-- Note: the formula specializes to bigradedTruncationBound when M=N=R.
bigradedGlobalHomBound = (sourceResolution,targetAmbientResolution,d1,d2,c1,c2) -> (
    targetPart := bigradedTruncationBound(targetAmbientResolution,d1,d2,c1,c2);
    sourcePart := sourceLowerShift(sourceResolution);
    {targetPart#0-sourcePart#0,targetPart#1-sourcePart#1}
    );

-- Note: supplying targetModuleOverAmbient explicitly ensures that the bound uses the
--       S-free resolution required by Proposition 4.2, rather than an R-free resolution.
bigradedGlobalHomData = (ambient,sourceModule,targetModule,targetModuleOverAmbient) -> (
    if ring sourceModule =!= ring targetModule then
        error "the source and target modules must be over the same ring";
    if ring targetModuleOverAmbient =!= ambient then
        error "the ambient presentation of the target must be over the ambient ring";
    bd := blockDegreeData ambient;
    (d1,d2,c1,c2) := (bd#0,bd#1,bd#2,bd#3);
    -- sourceLowerShift reads the 0th term and nothing else, so the free cover is
    -- the whole of what Proposition 4.2 wants from the source side.  Say so with
    -- LengthLimit: sourceModule lives over a quotient of the ambient ring, where
    -- a free resolution is in general infinite and M2 declines to guess a length.
    sourceResolution := res(sourceModule,LengthLimit=>0);
    maxHomologicalDegree := d1+d2+1;
    targetAmbientResolution := res(targetModuleOverAmbient,
        LengthLimit=>maxHomologicalDegree);
    bound := bigradedGlobalHomBound(sourceResolution,targetAmbientResolution,
        d1,d2,c1,c2);
    truncation := truncate(bound,sourceModule);
    rawHomModule := Hom(truncation,targetModule,MinimalGenerators=>true);
    nonnegativeHom := truncate({0,0},rawHomModule);
    new HashTable from {
        "ambient" => ambient,
        "sourceModule" => sourceModule,
        "targetModule" => targetModule,
        "targetModuleOverAmbient" => targetModuleOverAmbient,
        "sourceResolution" => sourceResolution,
        "targetAmbientResolution" => targetAmbientResolution,
        "resolutionLengthLimit" => maxHomologicalDegree,
        "certifiedBound" => true,
        "bound" => bound,
        "truncation" => truncation,
        "homModule" => nonnegativeHom,
        "rawHomModule" => rawHomModule
        }
    );

isSteinDegree = dd -> (#dd == 2 and dd#0 == 0 and dd#1 >= 0);

-- Note: the bound is computed from the resolution, so certifiedBound is true.
steinHomData = (ambient,igraph) -> (
    if ring igraph =!= ambient then
        error "the graph ideal must belong to the ambient ring";
    bd := blockDegreeData ambient;
    (d1,d2,c1,c2) := (bd#0,bd#1,bd#2,bd#3);
    nn := coker gens igraph;
    -- Corollary 4.3 only reads shifts through homological degree |d|+1.
    -- Avoid asking for any unnecessary tail of the resolution.
    maxHomologicalDegree := d1+d2+1;
    ff := res(nn,LengthLimit=>maxHomologicalDegree);
    rr := ambient/igraph;
    bound := bigradedTruncationBound(ff,d1,d2,c1,c2);
    truncation := truncate(bound,rr^1);
    rawHomModule := Hom(truncation,rr^1,MinimalGenerators=>true);
    nonnegativeHom := truncate({0,0},rawHomModule);
    -- truncate returns a submodule of the ambient module of Hom maps, so its
    -- generator matrix already consists of maps R_{>=r}->R.  No composition
    -- with gens(rawHomModule) is needed.
    evaluationMatrix := gens nonnegativeHom;
    wanted := select(toList(0..numgens(nonnegativeHom)-1),
        i -> isSteinDegree((degrees nonnegativeHom)#i));
    new HashTable from {
        "ambient" => ambient,
        "graphIdeal" => igraph,
        "ring" => rr,
        "resolution" => ff,
        "resolutionLengthLimit" => maxHomologicalDegree,
        "certifiedBound" => true,
        "bound" => bound,
        "truncation" => truncation,
        "homModule" => nonnegativeHom,
        "rawHomModule" => rawHomModule,
        "evaluationMatrix" => evaluationMatrix,
        "steinGeneratorIndices" => wanted,
        "steinGeneratorDegrees" => apply(wanted,i -> (degrees nonnegativeHom)#i)
        }
    );

checkBidegree = (value,label) -> (
    if not instance(value,List) or #value != 2
        or not all(value,n -> instance(n,ZZ)) then
        error(label | " must be a list of two integers");
    );

evaluationElementOf = (homData,evaluationElementIndex) -> (
    generators := gens homData#"truncation";
    if not instance(evaluationElementIndex,ZZ)
        or evaluationElementIndex < 0
        or evaluationElementIndex >= numColumns generators then
        error "the evaluation element index is outside the generator range";
    gamma := generators_(0,evaluationElementIndex);
    if gamma == 0 then error "the chosen evaluation element is zero";
    gamma
    );

-- Note: no free resolution is computed, so certifiedBound is false.
steinHomDataAtBound = (ambient,igraph,bound) -> (
    if ring igraph =!= ambient then
        error "the graph ideal must belong to the ambient ring";
    checkBidegree(bound,"the truncation bound");
    -- The supplied-bound route skips a resolution, not validation of the
    -- bigraded ambient convention used by every later step.
    blockDegreeData ambient;
    rr := ambient/igraph;
    truncation := truncate(bound,rr^1);
    rawHomModule := Hom(truncation,rr^1,MinimalGenerators=>true);
    nonnegativeHom := truncate({0,0},rawHomModule);
    evaluationMatrix := gens nonnegativeHom;
    wanted := select(toList(0..numgens(nonnegativeHom)-1),
        i -> isSteinDegree((degrees nonnegativeHom)#i));
    new HashTable from {
        "ambient" => ambient,
        "graphIdeal" => igraph,
        "ring" => rr,
        "bound" => bound,
        "boundWasSupplied" => true,
        "certifiedBound" => false,
        "truncation" => truncation,
        "homModule" => nonnegativeHom,
        "rawHomModule" => rawHomModule,
        "evaluationMatrix" => evaluationMatrix,
        "steinGeneratorIndices" => wanted,
        "steinGeneratorDegrees" => apply(wanted,i -> (degrees nonnegativeHom)#i)
        }
    );

-- Note: Lemma 5.2 uses psi_i(gamma)/gamma as the corresponding coordinate function.
evaluateSteinGenerators = (homData,evaluationElementIndex) -> (
    evaluationElementOf(homData,evaluationElementIndex);
    ee := homData#"evaluationMatrix";
    apply(homData#"steinGeneratorIndices",i -> ee_(evaluationElementIndex,i))
    );

-- A_(0,n) is spanned by the monomials of S of bidegree (0,n), which are exactly
-- the monomials in the target block.  So A = R_(0,>=0) is generated by the
-- images of the target-block variables, and the ambient ring already says which
-- those are -- no caller has to supply them, and none can supply a set that
-- fails to generate A.  blockDegreeData first, for its check that the variables
-- really do split into the two blocks.
targetBlockGenerators = ambient -> (
    blockDegreeData ambient;
    select(flatten entries vars ambient,q -> (degree q)#0 == 0)
    );

-- Note: the degree-(0,0) Hom generator is the unit and is omitted as an extra algebra generator.
-- TODO: organize the finite A-module presentation of the full strand more completely.
steinCoordinateAlgebra = method()

steinCoordinateAlgebra HashTable := homData -> steinCoordinateAlgebra(homData,0)

steinCoordinateAlgebra(HashTable,ZZ) := (homData,evaluationElementIndex) -> (
    baseGenerators := targetBlockGenerators homData#"ambient";
    rr := homData#"ring";
    tt := homData#"truncation";
    hh := homData#"homModule";
    wanted := homData#"steinGeneratorIndices";
    extra := select(wanted,i -> (degrees hh)#i != {0,0});
    gamma := evaluationElementOf(homData,evaluationElementIndex);
    dg := degree gamma;
    -- getSymbol rather than a bare name: inside a package a bare name would be
    -- an unexported symbol of the package, which a ring may not adopt as a
    -- variable.  The variable is then taken from the ring rather than read back
    -- off the symbol.
    ll0 := rr[getSymbol "steinInverse",Degrees=>{{-dg#0,-dg#1}}];
    inv0 := ll0_0;
    ll := ll0/ideal(inv0*sub(gamma,ll0)-1);
    inv := sub(inv0,ll);
    ee := homData#"evaluationMatrix";
    evals := apply(extra,i -> ee_(evaluationElementIndex,i));
    images := join(
        apply(baseGenerators,q -> sub(q,ll)),
        apply(evals,q -> sub(q,ll)*inv)
        );
    weights := join(
        apply(baseGenerators,q -> {(degree q)#1}),
        apply(extra,i -> {((degrees hh)#i)#1})
        );
    kk := coefficientRing homData#"ambient";
    -- Build A=R_(0,>=0) from the supplied base generators, then implement the
    -- paper's finite A-module strand presentation via pushForward.
    apoly := kk[Variables=>#baseGenerators,
        Degrees=>apply(baseGenerators,q -> {0,(degree q)#1})];
    abaseMap := map(rr,apoly,baseGenerators);
    abaseIdeal := kernel abaseMap;
    aa := apoly/abaseIdeal;
    inclusionAtoR := map(rr,aa,baseGenerators);
    positiveFirstPart := truncate({1,0},hh);
    zeroFirstStrand := hh/positiveFirstPart;
    strandAsAModule := pushForward(inclusionAtoR,zeroFirstStrand);
    pp := kk[Variables=>#images,Degrees=>weights];
    rho := map(ll,pp,images);
    definingIdeal := kernel rho;
    new HashTable from {
        "ring" => pp/definingIdeal,
        "polynomialRing" => pp,
        "definingIdeal" => definingIdeal,
        "mapToLocalization" => rho,
        "localizationPresentation" => ll,
        "evaluationElement" => gamma,
        "homData" => homData,
        "baseGeneratorCount" => #baseGenerators,
        "extraHomIndices" => extra,
        "images" => images,
        "baseRing" => aa,
        "baseInclusion" => inclusionAtoR,
        "zeroFirstStrand" => zeroFirstStrand,
        "strandAsAModule" => strandAsAModule,
        "strandAPresentation" => presentation strandAsAModule
        }
    );

-- Note: matching fingerprints do not constitute a mathematical proof of the bound.
steinFingerprint = (algebraData,hilbertMax) -> (
    cc := algebraData#"ring";
    aaModule := algebraData#"strandAsAModule";
    {
        dim cc,
        apply(toList(0..hilbertMax),i -> hilbertFunction(i,cc)),
        degrees aaModule
        }
    );

-- Note: because only finitely many matches are tested, certifiedBound is always false.
steinDataByStabilization = (
    ambient,igraph,startBound,maxSteps,requiredMatches,hilbertMax) -> (
    checkBidegree(startBound,"the start bound");
    if maxSteps < 2 then error "maxSteps must be at least 2";
    if requiredMatches < 1 then error "requiredMatches must be positive";
    if requiredMatches > maxSteps-1 then
        error "requiredMatches cannot exceed the number of available comparisons";
    if hilbertMax < 0 then error "hilbertMax must be nonnegative";
    history := {};
    previousFingerprint := null;
    consecutiveMatches := 0;
    chosenHomData := null;
    chosenCoordinateData := null;
    stabilized := false;
    counter := 0;
    while counter < maxSteps and not stabilized do (
        bound := {startBound#0+counter,startBound#1};
        hd := steinHomDataAtBound(ambient,igraph,bound);
        cd := steinCoordinateAlgebra(hd,0);
        fp := steinFingerprint(cd,hilbertMax);
        history = append(history,new HashTable from {
            "bound"=>bound,"fingerprint"=>fp,
            "homData"=>hd,"algebraData"=>cd});
        if previousFingerprint =!= null and fp == previousFingerprint then
            consecutiveMatches = consecutiveMatches+1
        else consecutiveMatches = 0;
        previousFingerprint = fp;
        chosenHomData = hd;
        chosenCoordinateData = cd;
        stabilized = consecutiveMatches >= requiredMatches;
        counter = counter+1;
        );
    new HashTable from {
        "stabilized"=>stabilized,
        "certifiedBound"=>false,
        "chosenBound"=>chosenHomData#"bound",
        "homData"=>chosenHomData,
        "algebraData"=>chosenCoordinateData,
        "history"=>history,
        "stepsRun"=>counter,
        "consecutiveMatches"=>consecutiveMatches,
        "hilbertMax"=>hilbertMax,
        "warning"=>"finite stabilization is not a proof of the Corollary 4.3 bound"
        }
    );

-- Method: use a localization and a Rees parameter, then take the kernel of the map.
directSteinGraph = (homData,algebraData) -> (
    if not algebraData#?"homData" or algebraData#"homData" =!= homData then
        error "the algebra data must have been built from this hom data";
    ambient := homData#"ambient";
    rr := homData#"ring";
    pp := algebraData#"polynomialRing";
    ll := algebraData#"localizationPresentation";
    cimages := algebraData#"images";
    avars := flatten entries vars ambient;
    zvars := flatten entries vars pp;
    na := #avars;
    nz := #zvars;
    adegs := degrees ambient;
    zweights := apply(degrees pp,d -> d#0);
    kk := coefficientRing ambient;
    -- The i-th generator of the coordinate algebra is a section of degree
    -- (0,zweights#i), so that is the bidegree its variable carries here.  Do not
    -- read the degree off cimages#i instead: those live in the tower ring
    -- rr[steinInverse], which forgets the grading of its coefficient ring rr and
    -- reports (0,0) for a target coordinate and (-deg gamma) for an evaluated
    -- generator.  With those degrees the graph ideal is not even homogeneous.
    jointDegrees := join(
        adegs,
        apply(zweights,b -> {0,b})
        );
    joint := kk[Variables=>na+nz,Degrees=>jointDegrees];
    target0 := ll[getSymbol "steinGraphParameter",Degrees=>{{0,0}}];
    tpar := target0_0;
    ambientImages := apply(avars,q -> sub(sub(q,rr),ll));
    zimages := apply(toList(0..nz-1),i ->
        sub(cimages#i,target0)*tpar^(zweights#i));
    graphMap := map(target0,joint,join(ambientImages,zimages));
    graphIdeal := kernel graphMap;
    new HashTable from {
        "jointRing" => joint,
        "graphIdeal" => graphIdeal,
        "graphMap" => graphMap,
        "sourceRepresentation" => "Gamma_f (canonically isomorphic to Y)",
        "ambientVariableCount" => na,
        "steinVariableCount" => nz,
        "saturationByLocalization" => true
        }
    );

-- Note: saturation by the irrelevant ideal being the unit ideal certifies base-point-freeness.
--
-- targetWeights gives the target the weighted projective space P(a_0,...,a_n).
-- A morphism into it is cut out by forms with deg(h_i) = a_i*e for one common e,
-- which is the unweighted "all degrees equal" when every a_i is 1.  The weights are
-- required rather than inferred from the degrees of the h_i: inferring them would
-- read a mistyped coordinate as a deliberate weighted target and proceed silently.
certifiedWeightedGraph = (sourcePolynomialRing,sourceIdeal,hImages,targetWeights) -> (
    if degreeLength sourcePolynomialRing != 1 then
        error "the source ring must be singly graded";
    if ring sourceIdeal =!= sourcePolynomialRing then
        error "the source ideal must belong to the source polynomial ring";
    bb := sourcePolynomialRing/sourceIdeal;
    imgs := apply(hImages,q -> sub(q,bb));
    if #imgs == 0 then error "the coordinate list must be nonempty";
    if #targetWeights != #imgs then
        error "there must be one target weight per coordinate";
    if not all(targetWeights,a -> instance(a,ZZ) and a > 0) then
        error "the target weights must be positive integers";
    imageDegrees := apply(imgs,q -> (degree q)#0);
    -- deg(h_i)/a_i must be one and the same e for every i.
    if not all(#imgs,i -> imageDegrees#i % targetWeights#i == 0) then
        error("the coordinate degrees " | toString imageDegrees
            | " are not multiples of the target weights " | toString targetWeights);
    ratios := apply(#imgs,i -> imageDegrees#i // targetWeights#i);
    if not all(ratios,e -> e == ratios#0) then
        error("the coordinate degrees " | toString imageDegrees
            | " are not proportional to the target weights " | toString targetWeights);
    irr := ideal gens bb;
    baseIdeal := ideal imgs;
    basePointFree := saturate(baseIdeal,irr) == ideal(1_bb);
    if not basePointFree then
        error "the coordinates have a projective base locus";
    kk := coefficientRing sourcePolynomialRing;
    ny := numgens sourcePolynomialRing;
    nz := #imgs;
    -- The source block keeps the degrees it has in sourcePolynomialRing, so a
    -- weighted source survives the lift; only the block index is added.
    sourceDegs := apply(degrees sourcePolynomialRing,d -> {d#0,0});
    productRing := kk[Variables=>ny+nz,
        Degrees=>join(sourceDegs,apply(targetWeights,a -> {0,a}))];
    yy := take(flatten entries vars productRing,ny);
    zz := drop(flatten entries vars productRing,ny);
    liftSource := map(productRing,sourcePolynomialRing,yy);
    liftedSourceIdeal := liftSource sourceIdeal;
    -- Kernel/Rees calculation in a target containing the quotient source.  The
    -- parameter carries the target weight, so z_i of degree (0,a_i) has an image
    -- of matching degree.
    target := bb[getSymbol "graphParameter",Degrees=>{{0,1}}];
    gpar := target_0;
    sourceVarsInTarget := apply(flatten entries vars sourcePolynomialRing,
        q -> sub(q,bb));
    graphMap := map(target,productRing,
        join(sourceVarsInTarget,
             apply(nz,i -> imgs#i*gpar^(targetWeights#i))));
    graphIdeal := kernel graphMap;
    new HashTable from {
        "productRing" => productRing,
        "graphIdeal" => graphIdeal,
        "basePointFree" => basePointFree,
        "projectionIsomorphismByConstruction" => true,
        "sourceVariableCount" => ny,
        "targetVariableCount" => nz,
        "targetWeights" => targetWeights,
        "sourceIdealLift" => liftedSourceIdeal
        }
    );

-- The unweighted target P^n is the case where every weight is 1, which is also
-- where the proportionality test reduces to "all coordinate degrees agree".
certifiedHomogeneousGraph = (sourcePolynomialRing,sourceIdeal,hImages) -> (
    certifiedWeightedGraph(sourcePolynomialRing,sourceIdeal,hImages,
        apply(#hImages,i -> 1))
    );

-- Note: candidates are compared after saturation by the biprojective irrelevant ideal.
selectCertifiedGraphComponent = (certified,candidates) -> (
    pp := certified#"productRing";
    if not all(candidates,candidate -> ring candidate === pp) then
        error "every candidate must belong to the certified product ring";
    ny := certified#"sourceVariableCount";
    vv := flatten entries vars pp;
    iy := ideal take(vv,ny);
    iz := ideal drop(vv,ny);
    birr := iy*iz;
    goal := saturate(certified#"graphIdeal",birr);
    hits := select(toList(0..#candidates-1),
        i -> saturate(candidates#i,birr) == goal);
    if #hits != 1 then error("expected exactly one certified graph component, found " | toString #hits);
    hits#0
    );

ringMapsAreInverse = (ff,gg) -> (
    -- ff : A -> B contravariantly, gg : B -> A
    aa := source ff;
    bb := target ff;
    if source gg =!= bb or target gg =!= aa then false else (
        onA := all(flatten entries vars aa,q -> (gg*ff)(q) == q);
        onB := all(flatten entries vars bb,q -> (ff*gg)(q) == q);
        onA and onB
        )
    );

-- This checks only the arithmetic that the caller supplies.  It deliberately
-- makes no claim that the rings are localizations of sourceRing or of a graph.
checkChartwiseInverses = (sourceRing,coverElements,chartMapPairs) -> (
    if #coverElements != #chartMapPairs then
        error "there must be one inverse-map pair per cover element";
    if not all(chartMapPairs,pair -> instance(pair,List) and #pair == 2) then
        error "each chart entry must be a pair of ring maps";
    irr := ideal gens sourceRing;
    coverIdeal := ideal coverElements;
    covers := saturate(coverIdeal,irr) == ideal(1_sourceRing);
    if not covers then error "the supplied affine charts do not cover Proj(sourceRing)";
    localChecks := apply(chartMapPairs,pair -> ringMapsAreInverse(pair#0,pair#1));
    if not all(localChecks,b -> b) then error "at least one ring-map pair is not mutually inverse";
    new HashTable from {
        "coverVerified" => covers,
        "inversePairChecks" => localChecks,
        "numberOfCharts" => #chartMapPairs
        }
    );

beginDocumentation()

doc ///
Node
  Key
    SteinFactorization
  Headline
    Stein factorization of a projective morphism given by its graph
  Description
    Text
      For a projective morphism of algebraic varieties $f\colon Y \to X$, a
      {\em Stein factorization} is a decomposition
      $$Y \xrightarrow{\ h\ } Z \xrightarrow{\ g\ } X$$
      in which $h$ is proper with $h_*\mathcal{O}_Y=\mathcal{O}_Z$ (hence has
      geometrically connected fibres) and $g$ is finite; concretely
      $Z=\operatorname{Spec}_X f_*\mathcal{O}_Y$.  This package turns the
      algorithm of @TO2 {"Bibliography", "Yasuda (2026)"}@, Section 5.1, into an
      executable prototype.

      The input is the graph of $f$ represented as a bigraded projective
      scheme.  If $R=S/I_{\Gamma_f}$, then the variables in the source block
      have degrees $(\ast,0)$ and those in the target block $(0,\ast)$, the
      starred entries being positive; in the standard case they are $(1,0)$
      and $(0,1)$, and allowing larger values is what admits weighted
      projective spaces.  The first block is the ambient space containing $Y$
      (equivalently its graph), and the second contains $X$.
    Text
      The basic workflow consists of three calls.  For the square map of
      $\mathbb{P}^1$:
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      Igraph = ideal(y0^2*x1 - y1^2*x0);
      homData = steinHomData(S, Igraph);
      algebraData = steinCoordinateAlgebra homData;
      graphData = directSteinGraph(homData, algebraData);
      homData#"bound"
      algebraData#"ring"
      graphData#"graphIdeal"
    Text
      {\bf Assumptions.}  The coefficient ring is expected to be a field and
      $I_{\Gamma_f}$ a prime ideal defining the graph of a morphism.  Primality
      and the assertion that the input is a graph are not checked; the domain
      hypothesis is used by the evaluation in Lemma 5.2.  The two-block
      bigrading is checked by the entry points that receive an ambient
      bigraded ring.  No characteristic restriction is imposed by the code.
  Subnodes
    :The three steps of the construction
      steinHomData
      steinCoordinateAlgebra
      directSteinGraph
    :Reading the ambient bigrading
      blockDegreeData
    :Working without a certified bound
      steinHomDataAtBound
      steinDataByStabilization
    :Building and checking input graphs
      certifiedHomogeneousGraph
      certifiedWeightedGraph
      selectCertifiedGraphComponent
      checkChartwiseInverses
    :Underneath the three steps
      bigradedGlobalHomData
      evaluateSteinGenerators
    :Where this comes from
      "Bibliography"

Node
  Key
    steinHomData
  Headline
    the truncated bigraded Hom module of a graph
  Usage
    homData = steinHomData(S, Igraph)
  Inputs
    S:Ring
      the ambient bigraded polynomial ring, the coordinate ring of the product
      of the two (weighted) projective spaces in which the graph sits
    Igraph:Ideal
      the bihomogeneous ideal $I_{\Gamma_f}\subset S$ cutting the graph out of
      that product, so that $R=S/I_{\Gamma_f}$
  Outputs
    :HashTable
      carrying the bound $\mathbf{r}$ and whether it is certified, the ring
      $R$, the truncation $R_{\ge\mathbf{r}}$, the module
      $\operatorname{Hom}_R(R_{\ge\mathbf{r}},R)_{\ge(0,0)}$ together with the
      matrix of its generators, and the indices of those generators lying in
      the $(0,\ge0)$-strand
  Description
    Text
      For a sufficiently large bidegree $\mathbf{r}=(r_1,r_2)$ this computes
      $$C=\operatorname{Hom}_R(R_{\ge\mathbf{r}},R)_{(0,\ge0)}.$$
      The truncation bound $\mathbf{r}$ is obtained from shifts in a bounded
      bigraded free resolution of $R$ over the ambient polynomial ring.  This
      is the computational counterpart of the bound in Corollary 4.3 of
      @TO2 {"Bibliography", "Yasuda (2026)"}@.

      $C$ is the section ring of $Z$ for the polarization pulled back from
      $X$, not for $\mathcal{O}_Z(1)$.  That is worth knowing before reading
      any output off it: a $Z$ which is $\mathbb{P}^1$ can come back as a
      conic.
    Text
      The resolution used for the certified bound is often the expensive part.
      When it is infeasible, @TO steinHomDataAtBound@ accepts a bound without
      claiming that it is large enough.
    Text
      Consider the finite square map $[s:t]\mapsto[s^2:t^2]$ of
      $\mathbb{P}^1$.  Its graph is cut out by one bihomogeneous equation:
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      Igraph = ideal(y0^2*x1 - y1^2*x0);
      homData = steinHomData(S, Igraph);
    Text
      The computed bound, and whether it is certified --- that is, whether it
      was read off a resolution rather than supplied by hand:
    Example
      homData#"bound"
      homData#"certifiedBound"
    Text
      The degrees of the generators of the $(0,\ge0)$-strand:
    Example
      homData#"steinGeneratorDegrees"
    Text
      There are two strand generators: the unit in bidegree $(0,0)$, and one
      further generator in bidegree $(0,1)$.  That extra generator is what
      distinguishes the Stein intermediate $Z$ from $X$.
    Text
      {\bf Principal result keys.}  {\tt "bound"} and
      {\tt "certifiedBound"} record the truncation corner and its status;
      {\tt "ring"} is $R$, {\tt "truncation"} is
      $R_{\ge\mathbf r}$, and {\tt "resolution"} is the bounded ambient
      resolution.  {\tt "homModule"} is the Hom module truncated to the
      nonnegative orthant.  The lists {\tt "steinGeneratorIndices"} and
      {\tt "steinGeneratorDegrees"} select its $(0,\ge0)$-strand, while
      {\tt "evaluationMatrix"} contains the maps to be evaluated.  Other keys
      are working data and may change.
  SeeAlso
    blockDegreeData
    steinCoordinateAlgebra
    steinHomDataAtBound
    bigradedGlobalHomData

Node
  Key
    steinCoordinateAlgebra
    (steinCoordinateAlgebra,HashTable)
    (steinCoordinateAlgebra,HashTable,ZZ)
  Headline
    a graded coordinate algebra for the Stein intermediate
  Usage
    algebraData = steinCoordinateAlgebra homData
    algebraData = steinCoordinateAlgebra(homData, evaluationElementIndex)
  Inputs
    homData:HashTable
      as returned by @TO steinHomData@ or @TO steinHomDataAtBound@
    evaluationElementIndex:ZZ
      which generator of $R_{\ge\mathbf{r}}$ to use as the evaluation element
      $\gamma$, counted from $0$; optional, and $0$ when omitted
  Outputs
    :HashTable
      holding the graded coordinate algebra of $Z$ under {\tt "ring"}, as the
      quotient of the polynomial ring under {\tt "polynomialRing"} --- one
      variable per algebra generator --- by the ideal of relations among those
      generators under {\tt "definingIdeal"}; the same algebra a second time
      as a finite module over $A=R_{(0,\ge0)}$, with its presentation; and the
      localization $R[1/\gamma]$ the computation was carried out in, together
      with $\gamma$ itself under {\tt "evaluationElement"}
  Description
    Text
      The strand $C=\operatorname{Hom}_R(R_{\ge\mathbf{r}},R)_{(0,\ge0)}$ that
      @TO steinHomData@ computes consists of homomorphisms rather than of
      elements of $R$, so it carries no evident multiplication.  It acquires
      one by being realized inside a localization $R[1/\gamma]$ via the map
      $\varphi\mapsto\varphi(\gamma)/\gamma$ for a chosen evaluation element
      $\gamma$; see @TO evaluateSteinGenerators@, where that evaluation is
      described.  This function carries it out and then eliminates, returning
      $C$ as a quotient of a polynomial ring.

      The subring $A=R_{(0,\ge0)}$ is not an argument: it is generated by the
      target-block variables, which the ambient bigrading already identifies.
      The extra evaluated Hom generators are precisely what can make $C$
      larger than $A$ and distinguish $Z$ from the image in $X$.
    Text
      The choice of $\gamma$ does not change the resulting subring, so the
      one-argument form chooses the first generator.  The optional index is
      available when a different localization is useful.
    Text
      {\bf Basic example.}  Continue the square map from @TO steinHomData@:
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      Igraph = ideal(y0^2*x1 - y1^2*x0);
      homData = steinHomData(S, Igraph);
      algebraData = steinCoordinateAlgebra homData;
      algebraData#"ring"
      algebraData#"polynomialRing"
      algebraData#"definingIdeal"
    Text
      Thus $Z\cong\mathbb{P}^1$ appears through its second Veronese ring: the
      first two variables come from $X$, and the third is the extra Hom
      generator satisfying the displayed conic relation.
    Text
      {\bf Principal result keys.}  {\tt "ring"} is the quotient of
      {\tt "polynomialRing"} by {\tt "definingIdeal"}.
      {\tt "images"} gives the corresponding elements of $R[1/\gamma]$.
      {\tt "baseRing"} is $A$, while {\tt "strandAsAModule"} and
      {\tt "strandAPresentation"} give $C$ as a finite $A$-module.
      {\tt "evaluationElement"} records the chosen $\gamma$.
    Text
      {\bf Advanced example: $C$ not free over $A$.}  Take
      $$f\colon Y=\mathbb{P}^1_{s:t}\times\mathbb{P}^1_{u:v}\
      \xrightarrow{\ h\ }\ Z=\mathbb{P}^1_{u:v}\ \xrightarrow{\ g\ }\ X,$$
      with $h$ the second projection and $X$ the conic $x_0x_2=x_1^2$ in
      $\mathbb{P}^2$, onto which $g$ is two-to-one.  So $f$ is given by the
      quartics $u^4,u^2v^2,v^4$, and a general fibre of it is two disjoint
      $\mathbb{P}^1$s, each of which $h$ contracts.  Build the graph, pass it
      to @TO steinHomData@, and pass what that returns to this function:
    Example
      S = QQ[w0,w1,w2,w3,z0,z1,z2,
          Degrees => {{1,0},{1,0},{1,0},{1,0},{0,1},{0,1},{0,1}}];
      auxiliaryRing = QQ[s,t,u,v,a,b];
      Igraph = kernel map(auxiliaryRing, S,
          {s*u*a, s*v*a, t*u*a, t*v*a, u^4*b, u^2*v^2*b, v^4*b});
      homData = steinHomData(S, Igraph);
      algebraData = steinCoordinateAlgebra homData;
    Text
      {\tt S} is the coordinate ring of $\mathbb{P}^3\times\mathbb{P}^2$, the
      $\mathbb{P}^3$ being where $Y$ sits by the Segre embedding.  The
      auxiliary ring is only for writing the graph down: $s,t$ and $u,v$ are
      the coordinates of the two factors of $Y$, while $a$ and $b$ scale the
      two blocks separately, which is what makes the kernel bihomogeneous ---
      the device the parameter $t$ performs in @TO directSteinGraph@.
    Text
      The coordinate algebra of $Z$ is
      {\tt "polynomialRing"} modulo {\tt "definingIdeal"}:
    Example
      algebraData#"polynomialRing"
      algebraData#"definingIdeal"
    Text
      The polynomial ring is generated automatically, so its variables print
      as $p_0,p_1,\dots$; they come in a fixed order, first the target-block
      variables --- which the function reads off the degrees of {\tt S} ---
      and then one variable for each evaluated Hom generator.  (The strand
      generator of bidegree $(0,0)$ is the unit of $C$ and gets no variable of
      its own.)  So here $p_0,p_1,p_2$ are the coordinates of $X$ and
      $p_3,p_4$ are the two evaluated Hom generators.  Those last two are what
      distinguishes $Z$ from $X$: without them the answer would be the conic
      itself.
    Text
      The same $C$ is returned a second time as a module over $A$ rather than
      as a ring.  That is the form in which it is finitely generated, and a
      finite presentation over $A$ is what makes $C$ computable at all;
      @TO pushForward@ produces it.
    Example
      algebraData#"baseRing"
      algebraData#"strandAsAModule"
      algebraData#"strandAPresentation"
    Text
      Neither of the two things on show here is guaranteed.  $A$ is the
      coordinate ring of the conic rather than a polynomial ring, because the
      target is a proper subvariety of $\mathbb{P}^2$; send $Y$ onto a whole
      projective space instead and the target coordinates become
      algebraically independent, so $A$ is free of relations.  And $C$ is not
      free over $A$: $\mathcal{O}_X(1)$ restricted to a conic is
      $\mathcal{O}(2)$ on the $\mathbb{P}^1$ underneath it, so $A$ reaches
      only the monomials of even degree there, while $C_n=k[u,v]_{4n}$
      contains the odd ones too.  The two of those in degree one, $uv^3$ and
      $u^3v$, are the extra module generators, and the two columns of the
      presentation are what they satisfy.  Where the finite part is a
      coordinatewise power map onto a whole projective space --- which is what
      most of the examples in this package are --- the module comes out free
      instead and the presentation is the zero matrix.
    Text
      This example is {\tt tests/conic-target.m2}, where the fibres are
      checked as well.
  Caveat
    A generator of $C$ as a finite $A$-module need not be needed as an algebra
    generator.  When one is redundant the presentation simply carries a
    variable more than necessary --- the quotient ring is still the right one,
    but elimination in @TO directSteinGraph@ becomes more expensive.
    Algebra-generator minimization is not implemented; this is the bottleneck
    in {\tt tests/blowup-twisted-cubic.m2}.
  SeeAlso
    steinHomData
    evaluateSteinGenerators
    directSteinGraph

Node
  Key
    directSteinGraph
  Headline
    the graph of the connected-fiber morphism h
  Usage
    graphData = directSteinGraph(homData, algebraData)
  Inputs
    homData:HashTable
      as returned by @TO steinHomData@ or @TO steinHomDataAtBound@
    algebraData:HashTable
      as returned by @TO steinCoordinateAlgebra@ from that same {\tt homData}
  Outputs
    :HashTable
      holding the bihomogeneous ideal of the graph of $h\colon Y\to Z$ under
      {\tt "graphIdeal"}, inside the ring {\tt "jointRing"} it was computed in
  Description
    Text
      The algebra generators of $Z$ produced by the previous step are elements
      $c_0,\dots,c_N$ of $C$, homogeneous of bidegrees $(0,b_0),\dots,(0,b_N)$.
      Each becomes a homogeneous coordinate $z_i$ on $Z$ carrying the bidegree
      of the $c_i$ it stands for,
      $$J=S[z_0,\dots,z_N],\qquad \deg z_i=(0,b_i),$$
      and the graph is the kernel of
      $$\Phi\colon J\longrightarrow R[1/\gamma][t],\qquad
      \Phi(x)=\bar x\ (x\text{ a variable of }S),\qquad
      \Phi(z_i)=c_i\,t^{b_i}.$$
      So $J$ is the coordinate ring of the product of the two spaces containing
      $\Gamma_f$ with the weighted projective space in which the $z_i$ place
      $Z$; it is weighted exactly when the $b_i$ are not all equal.
    Text
      The parameter $t$ is what forces the answer to be a projective one.
      Writing $F=\sum_\alpha F_\alpha z^\alpha$ with $F_\alpha\in S$,
      $$\Phi(F)=\sum_\alpha \bar F_\alpha\,c^\alpha\,
      t^{\langle b,\alpha\rangle},$$
      and since $t$ is a free variable this vanishes if and only if
      $\sum \bar F_\alpha c^\alpha=0$ separately for each value of
      $\langle b,\alpha\rangle$.  So $t$ admits only those relations that are
      homogeneous in the $z$-degree, which are the ones that survive the
      scaling $\lambda\cdot(z_0,\dots,z_N)=(\lambda^{b_0}z_0,\dots,
      \lambda^{b_N}z_N)$ under which the coordinates of $Z$ are defined.
      Without it the kernel would also record that each $z_i$ equals one
      particular element $c_i$, which is not a statement about $Z$ as a
      projective variety.

      Working over $R[1/\gamma]$ saturates with respect to $\gamma$: the kernel
      describes the graph over $\{\gamma\ne0\}$ and then takes its closure.
      This is not a saturation by the biprojective irrelevant ideal.
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      Igraph = ideal(y0^2*x1 - y1^2*x0);
      homData = steinHomData(S, Igraph);
      algebraData = steinCoordinateAlgebra homData;
      graphData = directSteinGraph(homData, algebraData);
      degrees graphData#"jointRing"
      graphData#"graphIdeal"
      isHomogeneous graphData#"graphIdeal"
      isPrime graphData#"graphIdeal"
    Text
      The joint ring has the four variables of {\tt S} followed by the three
      $z_i$, one for each algebra generator that
      @TO steinCoordinateAlgebra@ used, and each $z_i$ carries the bidegree
      $(0,b_i)$ of the section it stands for.  Reading those degrees off the
      localization instead would lose the grading of its coefficient ring $R$
      and report $(0,0)$ for a target coordinate, leaving the ideal not even
      homogeneous.
    Text
      In the printed ideal the variables after those of {\tt S} are the
      coordinates of $Z$.  Its conic relation presents $Z$, while the mixed
      relations with $y_0,y_1$ describe the graph of $h$.
    Text
      {\bf Principal result keys.}  {\tt "jointRing"} contains the graph ideal
      under {\tt "graphIdeal"}, and {\tt "graphMap"} is the map whose kernel it
      is.  {\tt "saturationByLocalization"} records the construction just
      described; it is not the outcome of an additional test.
  SeeAlso
    steinCoordinateAlgebra
    checkChartwiseInverses

Node
  Key
    blockDegreeData
  Headline
    the four numbers of Section 4, read off the ambient bigrading
  Usage
    bd = blockDegreeData S
  Inputs
    S:Ring
      a bigraded ring in which every variable has degree $(\ast,0)$ or
      $(0,\ast)$, the starred entry positive
  Outputs
    :List
      the four integers $\{d_1,d_2,c_1,c_2\}$: the dimensions $d_s$ of the two
      ambient (weighted) projective spaces, and the sums $c_s$ of the degrees
      of the variables in each block
  Description
    Text
      Corollary 4.3 of @TO2 {"Bibliography", "Yasuda (2026)"}@ is stated in terms
      of four numbers: block $s$ is $x_{s,0},\dots,x_{s,d_s}$, and
      $c_s=\sum_t \deg(x_{s,t})$.  They
      are not arguments to anything public, because the ambient ring already
      determines them; this is the function the entry points call for
      themselves.
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      blockDegreeData S
    Text
      With weights, $c_s$ parts company with the number of variables in the
      block.  Over $\mathbb{P}(1,2)\times\mathbb{P}^1$ the first block still has
      two variables, but $c_1=1+2=3$:
    Example
      Swt = QQ[y0,y1,x0,x1, Degrees => {{1,0},{2,0},{0,1},{0,1}}];
      blockDegreeData Swt
    Text
      The distinction is invisible in the standard examples, and getting it
      wrong would not fail loudly either: Corollary 4.3 subtracts $c_1$, so too
      small a value only enlarges the bound, and the answer would stay correct
      while the computation did more work.  That is why the number is read off
      the ring instead of being asked for.
  Caveat
    A variable of degree $(0,0)$ would belong to both blocks and one with both
    components nonzero to neither; either is an error rather than a silently
    accepted input.
  SeeAlso
    steinHomData

Node
  Key
    steinHomDataAtBound
  Headline
    the truncated bigraded Hom module at a supplied, uncertified bound
  Usage
    homData = steinHomDataAtBound(S, Igraph, r)
  Inputs
    S:Ring
      the ambient bigraded polynomial ring
    Igraph:Ideal
      the bihomogeneous ideal $I_{\Gamma_f}\subset S$
    r:List
      two integers giving the bidegree $\mathbf{r}=(r_1,r_2)$ to truncate at
  Outputs
    :HashTable
      the table @TO steinHomData@ returns, except that {\tt "bound"} is the
      supplied {\tt r}, {\tt "certifiedBound"} is false, and no resolution is
      recorded
  Description
    Text
      Computing the Corollary 4.3 bound means resolving $R$ over the ambient
      polynomial ring out to homological degree $d_1+d_2+1$, and on larger
      inputs that resolution is the bottleneck of the whole construction.  This
      entry point skips it and truncates at a bound the caller supplies.
      Nothing downstream changes: the result feeds
      @TO steinCoordinateAlgebra@ and @TO directSteinGraph@ exactly as before.
      What is lost is the guarantee that $\mathbf{r}$ was large enough.
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      Igraph = ideal(y0^2*x1 - y1^2*x0);
      homData = steinHomDataAtBound(S, Igraph, {1,0});
      homData#"certifiedBound"
      homData#"steinGeneratorDegrees"
      (steinHomData(S, Igraph))#"bound"
    Text
      Here $(1,0)$ happens to be the bound @TO steinHomData@ computes for this
      input, so the two agree; the difference is that nothing in this call
      established that.  In {\tt tests/blowup-twisted-cubic.m2} the source sits
      in $\mathbb{P}^{11}$, the certified bound is out of reach, and
      $\mathbf{r}=(2,0)$ is supplied and then checked against independently
      known geometry instead; its runtime and outcome are recorded in that
      test rather than asserted to be machine-independent.

      For evidence short of a proof that a supplied bound is already large
      enough, see @TO steinDataByStabilization@.
  SeeAlso
    steinHomData
    steinDataByStabilization

Node
  Key
    steinDataByStabilization
  Headline
    heuristic evidence that a supplied bound is already large enough
  Usage
    stab = steinDataByStabilization(S, Igraph, startBound, maxSteps, requiredMatches, hilbertMax)
  Inputs
    S:Ring
      the ambient bigraded polynomial ring
    Igraph:Ideal
      the bihomogeneous ideal $I_{\Gamma_f}\subset S$
    startBound:List
      the bidegree to start from; its first coordinate is what gets incremented
    maxSteps:ZZ
      how many bounds to try at most, at least $2$
    requiredMatches:ZZ
      how many consecutive agreements to insist on, at least $1$
    hilbertMax:ZZ
      how far out to compare Hilbert functions
  Outputs
    :HashTable
      recording whether the answer stabilized, the bound and the two tables
      finally chosen, the full history of the run, and a warning that
      {\tt "certifiedBound"} is false whatever happened
  Description
    Text
      Run @TO steinHomDataAtBound@ and @TO steinCoordinateAlgebra@ at
      $\mathbf{r}, \mathbf{r}+(1,0), \mathbf{r}+(2,0),\dots$ and compare
      consecutive answers.  Two answers count as agreeing when they have the
      same Krull dimension, the same Hilbert values out to {\tt hilbertMax},
      and the same degrees of the strand as an $A$-module.  After
      {\tt requiredMatches} consecutive agreements the search stops.
      The reported {\tt "chosenBound"} is the last bound tested, including the
      final member of the matching run.
    Text
      Take the finite square map $[s:t]\mapsto[s^2:t^2]$ of $\mathbb{P}^1$
      again: start at $(1,0)$, try at most three bounds, and stop after a
      single agreement.
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      Igraph = ideal(y0^2*x1 - y1^2*x0);
      stab = steinDataByStabilization(S, Igraph, {1,0}, 3, 1, 2);
    Text
      Whether it settled, on which bound, and after how many runs:
    Example
      stab#"stabilized"
      stab#"chosenBound"
      stab#"stepsRun"
    Text
      The runs at $(1,0)$ and $(2,0)$ agreed, so the search stopped there.  The
      bound reported is the last one run, not the earliest that agreed.  Here
      $(1,0)$ is the bound @TO steinHomData@ certifies for this input, so the
      heuristic is being checked against an answer that can be had outright;
      this is a sanity check against a case that can also be certified.
    Text
      That the answer stopped moving is evidence and not more than evidence:
      only finitely many bounds were tried, and nothing rules out a later one
      differing.  So {\tt "certifiedBound"} is false however the run came out,
      and the table says so in as many words:
    Example
      stab#"certifiedBound"
      stab#"warning"
  Caveat
    Only the first coordinate of the bound is increased.  This probes the
    source-block cutoff while keeping the target polarization fixed; it cannot
    detect that the second coordinate of {\tt startBound} was too small.
  SeeAlso
    steinHomData
    steinHomDataAtBound

Node
  Key
    certifiedHomogeneousGraph
  Headline
    build the graph of a morphism to projective space after a base-locus check
  Usage
    graphData = certifiedHomogeneousGraph(B, I, hImages)
  Inputs
    B:Ring
      a singly graded polynomial ring
    I:Ideal
      an ideal of {\tt B}, so that the source is $Y=\operatorname{Proj}(B/I)$
    hImages:List
      representatives in {\tt B} of forms of one degree in $B/I$, giving the
      coordinates of $f\colon Y\to\mathbb{P}^n$
  Outputs
    :HashTable
      holding the bigraded product ring under {\tt "productRing"} and the
      bihomogeneous ideal of $\Gamma_f$ under {\tt "graphIdeal"}, ready to hand
      to @TO steinHomData@
  Description
    Text
      The three steps of the construction take the graph as given.  This builds
      one, from a morphism written the way a morphism to $\mathbb{P}^n$ usually
      is: a list of forms of a common degree with no common projective zero.
      Both conditions are checked rather than assumed --- the base locus by a
      saturation, which is what {\tt "basePointFree"} records --- so a mistyped
      coordinate is an error and not a different variety.
    Text
      The twisted cubic, that is $\mathbb{P}^1\to\mathbb{P}^3$ by the cubic
      forms:
    Example
      B = QQ[r0,r1];
      graphData = certifiedHomogeneousGraph(B, ideal(0_B),
          {r1^3, r0*r1^2, r0^2*r1, r0^3});
      graphData#"basePointFree"
      degrees graphData#"productRing"
      graphData#"graphIdeal"
    Text
      The returned pair can be passed directly to the main computation:
    Example
      homData = steinHomData(graphData#"productRing", graphData#"graphIdeal");
      homData#"steinGeneratorDegrees"
    Text
      Only the unit is needed, so $C=A$: $Z$ is the scheme-theoretic image of
      $f$.  Here that image is the twisted cubic, and the closed immersion
      identifies it with $Y$; it is not the ambient $\mathbb{P}^3$.
    Text
      {\tt "basePointFree"} records a saturation check.
      {\tt "projectionIsomorphismByConstruction"} records instead a fact about
      how the graph was constructed, not a second computational certificate.
    Text
      This is the all-weights-one case of @TO certifiedWeightedGraph@, which is
      also where the proportionality test there reduces to ``all coordinate
      degrees agree''.
  SeeAlso
    certifiedWeightedGraph
    steinHomData

Node
  Key
    certifiedWeightedGraph
  Headline
    build the graph of a morphism to a weighted projective space
  Usage
    graphData = certifiedWeightedGraph(B, I, hImages, targetWeights)
  Inputs
    B:Ring
      a singly graded polynomial ring, possibly weighted
    I:Ideal
      an ideal of {\tt B}, so that the source is $Y=\operatorname{Proj}(B/I)$
    hImages:List
      representatives in {\tt B} of the coordinates $h_i$, interpreted in
      $B/I$
    targetWeights:List
      positive integers $a_0,\dots,a_n$ giving the target
      $\mathbb{P}(a_0,\dots,a_n)$
  Outputs
    :HashTable
      the same table @TO certifiedHomogeneousGraph@ returns, with the weights
      under {\tt "targetWeights"}
  Description
    Text
      A morphism into $\mathbb{P}(a_0,\dots,a_n)$ is cut out by forms with
      $\deg(h_i)=a_ie$ for one common $e$, which is the unweighted case when
      every $a_i$ is $1$.  Proportional degrees make the map well defined; they
      say nothing about its degree or whether it is an isomorphism.
    Text
      The degree-two morphism $\mathbb{P}^1\to\mathbb{P}(1,2)$ given by
      $(r_0,r_1^2)$:
    Example
      B = QQ[r0,r1];
      graphData = certifiedWeightedGraph(B, ideal(0_B), {r0,r1^2}, {1,2});
      degrees graphData#"productRing"
      graphData#"graphIdeal"
    Text
      On the chart where the weight-one coordinate $y_0$ is nonzero, the
      invariant coordinate is $y_1/y_0^2$; its pullback is
      $(r_1/r_0)^2$.  Thus this map has degree two, not one.
    Text
      A weighted source survives the construction as well: the source block
      keeps the degrees it had in {\tt B} and only gains the block index, so
      that {\tt "productRing"} is the coordinate ring of a product of two
      weighted projective spaces and @TO blockDegreeData@ reads the weight sums
      off it.
    Text
      The weights are required rather than inferred from the degrees of the
      $h_i$.  Inferring them would read a mistyped coordinate as a deliberate
      weighted target and proceed silently; demanding them turns the same
      mistake into a rejected input.
    Example
      try (certifiedWeightedGraph(B, ideal(0_B), {r0,r1}, {1,2}); "accepted") else "rejected"
  SeeAlso
    certifiedHomogeneousGraph
    blockDegreeData

Node
  Key
    selectCertifiedGraphComponent
  Headline
    pick out the certified graph among a list of candidate ideals
  Usage
    candidateIndex = selectCertifiedGraphComponent(certifiedGraphData, candidateIdeals)
  Inputs
    certifiedGraphData:HashTable
      as returned by @TO certifiedHomogeneousGraph@ or
      @TO certifiedWeightedGraph@
    candidateIdeals:List
      ideals of its {\tt "productRing"}; ideals from another ring are rejected
  Outputs
    candidateIndex:ZZ
      the position of the one candidate that is the certified graph
  Description
    Text
      A component-selection step in the full algorithm produces several
      candidate ideals, of which one is the graph.  This decides which, by
      comparing each candidate with the certified graph after saturating both
      by the biprojective irrelevant ideal $I_YI_Z$ --- the comparison that
      makes two ideals with the same biprojective zero locus count as the same.
    Example
      B = QQ[r0,r1];
      graphData = certifiedHomogeneousGraph(B, ideal(0_B),
          {r1^3, r0*r1^2, r0^2*r1, r0^3});
      P = graphData#"productRing";
      selectCertifiedGraphComponent(graphData,
          {ideal(0_P), graphData#"graphIdeal"})
    Text
      Anything other than exactly one match is an error: no match means the
      certified graph is not among the candidates, and several would mean the
      saturation failed to tell them apart.
  Caveat
    Equality is tested after biprojective saturation.  The selected object is
    therefore a biprojective subscheme, not necessarily the identical ideal.
  SeeAlso
    certifiedHomogeneousGraph
    certifiedWeightedGraph

Node
  Key
    checkChartwiseInverses
  Headline
    check inverse ring maps supplied on a projective cover
  Usage
    checks = checkChartwiseInverses(sourceRing, coverElements, chartMapPairs)
  Inputs
    sourceRing:Ring
      the homogeneous coordinate ring of $Y$
    coverElements:List
      homogeneous elements whose non-vanishing loci cover
      $\operatorname{Proj}$ of it
    chartMapPairs:List
      one pair $\{\varphi,\psi\}$ of ring maps per cover element, going in
      opposite directions
  Outputs
    :HashTable
      recording the cover check and the inverse-pair checks
  Description
    Text
      This helper verifies exactly two statements: the supplied elements cover
      $\operatorname{Proj}(\mathtt{sourceRing})$, and each supplied pair of ring
      maps composes to the identity in both orders.  It returns these under
      {\tt "coverVerified"} and {\tt "inversePairChecks"}.
    Text
      It does not identify the rings with localizations of {\tt sourceRing} or
      of a graph returned by @TO directSteinGraph@.  It also does not check
      compatibility on overlaps.  Those identifications remain part of the
      caller's mathematical argument; consequently this function does not
      claim to certify that a graph projection is an isomorphism.
    Text
      The squaring map of $\mathbb{P}^1$, on its two standard charts.  On
      $y_1\neq0$ the source coordinate is $r=y_0/y_1$ and the graph chart is
      $\{(r,q):q=r^2\}$, whose projection to the $r$-line is inverted by
      $r\mapsto(r,r^2)$; the chart $y_0\neq0$ is the same with $s=y_1/y_0$:
    Example
      Y = QQ[y0,y1];
      A0 = QQ[r]; G0 = QQ[rg,q0]/ideal(q0-rg^2);
      A1 = QQ[s]; G1 = QQ[sg,q1]/ideal(q1-sg^2);
      checks = checkChartwiseInverses(Y, {y1,y0},
          {{map(G0,A0,{rg}), map(A0,G0,{r,r^2})},
           {map(G1,A1,{sg}), map(A1,G1,{s,s^2})}});
      checks#"numberOfCharts"
      checks#"coverVerified"
      checks#"inversePairChecks"
  Caveat
    The order of cover elements and map pairs is trusted, not checked.
  SeeAlso
    directSteinGraph

Node
  Key
    evaluateSteinGenerators
  Headline
    evaluate the strand generators at a generator of the truncation
  Usage
    evals = evaluateSteinGenerators(homData, evaluationElementIndex)
  Inputs
    homData:HashTable
      as returned by @TO steinHomData@ or @TO steinHomDataAtBound@
    evaluationElementIndex:ZZ
      the position, counted from $0$, of $\gamma$ in the list of generators of
      $R_{\ge\mathbf{r}}$; it must be in range and name a nonzero generator
  Outputs
    :List
      the elements $\varphi_i(\gamma)\in R$, one for each generator $\varphi_i$
      of the $(0,\ge0)$-strand
  Description
    Text
      The strand $C$ carries no multiplication of its own, being a module of
      homomorphisms.  Lemma 5.2 of @TO2 {"Bibliography", "Yasuda (2026)"}@ gives
      it one by realizing it inside a localization: fix a nonzero
      $\gamma\in R_{\ge\mathbf{r}}$ and send
      $$\varphi\longmapsto\varphi(\gamma)/\gamma\in R[1/\gamma].$$
      When $R$ is a domain this is injective; that hypothesis is trusted rather
      than checked.  The result does not depend on which $\gamma$ is taken:
      for any other $\gamma'\in R_{\ge\mathbf{r}}$ we have
      $\gamma'\varphi(\gamma)=\varphi(\gamma'\gamma)=\gamma\varphi(\gamma')$,
      whence $\varphi(\gamma)/\gamma=\varphi(\gamma')/\gamma'$.  It therefore
      identifies $C$ with a subring of $R[1/\gamma]$, and that is where the
      multiplication on $C$ comes from.

      This function returns the numerators $\varphi_i(\gamma)$ only.  The
      division is left to @TO steinCoordinateAlgebra@, which builds the
      localization to carry it out in.  What it is for is getting at the
      evaluated generators directly, to feed them to a map into a ring whose
      variables one has named oneself; {\tt tests/basic.m2} identifies the
      Stein intermediates that way.
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      Igraph = ideal(y0^2*x1 - y1^2*x0);
      homData = steinHomData(S, Igraph);
      (gens homData#"truncation")_(0,0)
      evaluateSteinGenerators(homData, 0)
    Text
      So $\gamma=y_1$ here.  The first strand generator is the unit and returns
      $\gamma$ itself; the second returns $y_0x_1$, and the coordinate function
      it stands for is $y_0x_1/y_1$.
  SeeAlso
    steinCoordinateAlgebra
    steinHomData

Node
  Key
    bigradedGlobalHomData
  Headline
    the truncated bigraded Hom module of a pair of modules
  Usage
    data = bigradedGlobalHomData(S, M, N, NS)
  Inputs
    S:Ring
      the ambient bigraded polynomial ring
    M:Module
      the source module, over a quotient $R$ of {\tt S}
    N:Module
      the target module, over the same $R$
    NS:Module
      the same target presented over {\tt S} rather than over $R$; the function
      checks its ambient ring but trusts that it really represents {\tt N}
  Outputs
    :HashTable
      carrying the certified bound, the free cover of {\tt M} and the ambient
      resolution of {\tt N} that it was read off, the truncation
      $M_{\ge\mathbf{r}}$, and
      $\operatorname{Hom}_R(M_{\ge\mathbf{r}},N)_{\ge(0,0)}$
  Description
    Text
      Proposition 4.2 of @TO2 {"Bibliography", "Yasuda (2026)"}@ is stated for a
      pair of modules, and this is that statement.  @TO steinHomData@ is the
      case $M=N=R$, to which the bound formula here specializes.
    Text
      The fourth argument is not redundant.  The bound has to be read off a
      free resolution of the target over the ambient polynomial ring {\tt S},
      not over $R$, where the resolution would in general be infinite; supplying
      {\tt NS} explicitly is what guarantees the right one is used.
    Text
      The source side is different: Proposition 4.2 needs only the lowest
      shift in homological degree $0$, so {\tt "sourceResolution"} is the free
      cover obtained with {\tt LengthLimit=>0}, not a computed resolution tail.
      {\tt "targetAmbientResolution"} is the bounded $S$-free resolution of
      {\tt NS}.
    Text
      The diagonal of $\mathbb{P}^1\times\mathbb{P}^1$, with $M=N=R$:
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      Idiag = ideal(y0*x1 - y1*x0);
      R = S/Idiag;
      NS = coker gens Idiag;
      data = bigradedGlobalHomData(S, R^1, R^1, NS);
      data#"bound"
      data#"certifiedBound"
      degrees data#"homModule"
    Text
      A shifted source is a genuinely different $M$, and the lower shift of its
      $R$-free presentation moves the certified truncation corner, as
      Proposition 4.2 says it should.  In Macaulay2, the generator of
      $R^{\{\{1,1\}\}}$ has degree $(-1,-1)$, so subtracting its lower shift
      raises both entries of the bound by one:
    Example
      shiftData = bigradedGlobalHomData(S, R^{{1,1}}, R^1, NS);
      shiftData#"bound"
  SeeAlso
    steinHomData
    blockDegreeData

Node
  Key
    "Bibliography"
  Headline
    the papers this package implements and builds on
  Description
    Text
      Yasuda, T. (2026).  {\em An algorithm for the minimal model program in
      dimension three}.
      @HREF{"https://arxiv.org/abs/2603.13703v2","arXiv:2603.13703v2"}@

      The paper this package implements, and the one every numbered result
      cited in this documentation belongs to.  The version is fixed at v2 so
      that those numbers remain unambiguous.  Section 5.1 is the algorithm.
      The results the code is organized around are Proposition 4.2, the bound
      for a pair of modules, which is @TO bigradedGlobalHomData@; Corollary
      4.3, its specialization to $M=N=R$, which is the bound
      @TO steinHomData@ computes and whose four numbers
      @TO blockDegreeData@ reads off the ambient ring; and Lemma 5.2, the
      evaluation that gives the strand its multiplication, which is
      @TO evaluateSteinGenerators@.
    Text
      Smith, G. G. (2000).  {\em Computing global extension modules}.  Journal
      of Symbolic Computation {\bf 29}(4--5), 729--746.
      @HREF{"https://doi.org/10.1006/jsco.1999.0399","doi:10.1006/jsco.1999.0399"}@

      The monograded computation of global extension modules that the bigraded
      construction here extends.  What the bigrading buys is the ability to
      hold one degree at $0$ and let the other run, which is what makes the
      $(0,\ge0)$-strand --- and with it the section ring of the Stein
      intermediate --- something one can ask a computer for.
    Text
      The Stacks Project Authors.  {\em Stein factorization}.
      @HREF{"https://stacks.math.columbia.edu/tag/03GX","Tag 03GX"}@

      The definition and the basic properties, in the generality of schemes.
///
