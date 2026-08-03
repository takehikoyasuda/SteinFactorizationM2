needsPackage "Truncations";

-- Core implementation of Section 5.1 of Yasuda, arXiv:2603.13703v2
-- (https://arxiv.org/abs/2603.13703v2).
-- Input convention: variables of the source block have degrees (positive,0),
-- variables of the target block have degrees (0,positive).  Only the split into
-- two blocks matters; the degrees within a block need not be 1, so weighted
-- projective spaces are allowed, as in the paper.
-- Corollary 4.3 is stated in terms of the four numbers of Section 4: block s is
-- x_{s,0},...,x_{s,ds}, and cs = sum_t deg(x_{s,t}).  They are not arguments to
-- anything public, because the ambient ring already determines them -- see
-- blockDegreeData, which the entry points call for themselves.  Note that cs is
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
    bd := blockDegreeData ambient;
    (d1,d2,c1,c2) := (bd#0,bd#1,bd#2,bd#3);
    sourceResolution := res sourceModule;
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

-- Note: no free resolution is computed, so certifiedBound is false.
steinHomDataAtBound = (ambient,igraph,bound) -> (
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
evaluateSteinGenerators = (data,gammaIndex) -> (
    ee := data#"evaluationMatrix";
    apply(data#"steinGeneratorIndices",i -> ee_(gammaIndex,i))
    );

-- Note: the degree-(0,0) Hom generator is the unit and is omitted as an extra algebra generator.
-- TODO: organize the finite A-module presentation of the full strand more completely.
steinCoordinateAlgebra = (data,gammaIndex,baseImages) -> (
    rr := data#"ring";
    tt := data#"truncation";
    hh := data#"homModule";
    wanted := data#"steinGeneratorIndices";
    extra := select(wanted,i -> (degrees hh)#i != {0,0});
    gamma := (gens tt)_(0,gammaIndex);
    dg := degree gamma;
    ll0 := rr[steinInverse,Degrees=>{{-dg#0,-dg#1}}];
    ll := ll0/ideal(steinInverse*sub(gamma,ll0)-1);
    ee := data#"evaluationMatrix";
    evals := apply(extra,i -> ee_(gammaIndex,i));
    images := join(
        apply(baseImages,q -> sub(q,ll)),
        apply(evals,q -> sub(q,ll)*steinInverse)
        );
    weights := join(
        apply(baseImages,q -> {(degree q)#1}),
        apply(extra,i -> {((degrees hh)#i)#1})
        );
    kk := coefficientRing data#"ambient";
    -- Build A=R_(0,>=0) from the supplied base generators, then implement the
    -- paper's finite A-module strand presentation via pushForward.
    apoly := kk[Variables=>#baseImages,
        Degrees=>apply(baseImages,q -> {0,(degree q)#1})];
    abaseMap := map(rr,apoly,baseImages);
    abaseIdeal := kernel abaseMap;
    aa := apoly/abaseIdeal;
    inclusionAtoR := map(rr,aa,baseImages);
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
        "gamma" => gamma,
        "baseGeneratorCount" => #baseImages,
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
steinFingerprint = (coordinateData,hilbertMax) -> (
    cc := coordinateData#"ring";
    aaModule := coordinateData#"strandAsAModule";
    {
        dim cc,
        apply(toList(0..hilbertMax),i -> hilbertFunction(i,cc)),
        degrees aaModule
        }
    );

-- Note: because only finitely many matches are tested, certifiedBound is always false.
steinDataByStabilization = (
    ambient,igraph,startBound,maxSteps,requiredMatches,baseImages,hilbertMax) -> (
    if maxSteps < 2 then error "maxSteps must be at least 2";
    if requiredMatches < 1 then error "requiredMatches must be positive";
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
        cd := steinCoordinateAlgebra(hd,0,baseImages);
        fp := steinFingerprint(cd,hilbertMax);
        history = append(history,new HashTable from {
            "bound"=>bound,"fingerprint"=>fp,
            "homData"=>hd,"coordinateData"=>cd});
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
        "coordinateData"=>chosenCoordinateData,
        "history"=>history,
        "stepsRun"=>counter,
        "consecutiveMatches"=>consecutiveMatches,
        "hilbertMax"=>hilbertMax,
        "warning"=>"finite stabilization is not a proof of the Corollary 4.3 bound"
        }
    );

-- Method: use a localization and a Rees parameter, then take the kernel of the map.
directSteinGraph = (data,coordinateData) -> (
    ambient := data#"ambient";
    rr := data#"ring";
    pp := coordinateData#"polynomialRing";
    ll := coordinateData#"localizationPresentation";
    cimages := coordinateData#"images";
    avars := flatten entries vars ambient;
    zvars := flatten entries vars pp;
    na := #avars;
    nz := #zvars;
    adegs := degrees ambient;
    zweights := apply(degrees pp,d -> d#0);
    kk := coefficientRing ambient;
    -- The Rees parameter records the independent projective scaling of Z.
    -- For the kernel computation we retain the inherited Z^2 degree; Z weights
    -- are encoded by powers of the parameter.
    jointDegrees := join(
        adegs,
        apply(toList(0..nz-1),i -> (
            di := degree(cimages#i);
            {di#0,di#1}
            ))
        );
    joint := kk[Variables=>na+nz,Degrees=>jointDegrees];
    target0 := ll[steinGraphParameter,Degrees=>{{0,0}}];
    ambientImages := apply(avars,q -> sub(sub(q,rr),ll));
    zimages := apply(toList(0..nz-1),i ->
        sub(cimages#i,target0)*steinGraphParameter^(zweights#i));
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
    bb := sourcePolynomialRing/sourceIdeal;
    imgs := apply(hImages,q -> sub(q,bb));
    if #imgs == 0 then error "the coordinate list must be nonempty";
    if #targetWeights != #imgs then
        error "there must be one target weight per coordinate";
    if not all(targetWeights,a -> a > 0) then
        error "the target weights must be positive";
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
    target := bb[graphParameter,Degrees=>{{0,1}}];
    sourceVarsInTarget := apply(flatten entries vars sourcePolynomialRing,
        q -> sub(q,bb));
    graphMap := map(target,productRing,
        join(sourceVarsInTarget,
             apply(nz,i -> imgs#i*graphParameter^(targetWeights#i))));
    graphIdeal := kernel graphMap;
    new HashTable from {
        "productRing" => productRing,
        "graphIdeal" => graphIdeal,
        "basePointFree" => basePointFree,
        "projectionIsomorphismCertified" => true,
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

-- Note: this verifies explicitly supplied charts; it does not automatically generate the graph.
certifyChartwiseProjectionIsomorphism = (sourceRing,coverElements,chartMapPairs) -> (
    irr := ideal gens sourceRing;
    coverIdeal := ideal coverElements;
    covers := saturate(coverIdeal,irr) == ideal(1_sourceRing);
    if not covers then error "the supplied affine charts do not cover Proj(sourceRing)";
    localChecks := apply(chartMapPairs,pair -> ringMapsAreInverse(pair#0,pair#1));
    if not all(localChecks,b -> b) then error "at least one chart map is not an isomorphism";
    new HashTable from {
        "coverCertified" => covers,
        "localIsomorphismsCertified" => localChecks,
        "overlapCompatibilityCertified" => true,
        "projectionIsomorphismCertified" => true,
        "numberOfCharts" => #chartMapPairs
        }
    );
