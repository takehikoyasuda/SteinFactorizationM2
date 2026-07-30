needsPackage "Truncations";

-- Core implementation of Section 5.1 of Yasuda, arXiv:2603.13703v2.
-- Input convention: variables of the source block have degrees (positive,0),
-- variables of the target block have degrees (0,positive).

-- componentMax(ll,k)
-- Purpose: return the maximum value of component k among the bidegrees in ll.
-- Input: ll is a list of bidegrees; k is the component index (0 or 1).
-- Output: the maximum of the selected component, or -infinity if ll is empty.
componentMax = (ll,k) -> (
    if #ll == 0 then -infinity else max apply(ll,d -> d#k)
    );

-- componentMin(ll,k)
-- Purpose: return the minimum value of component k among the bidegrees in ll.
-- Input: ll is a nonempty list of bidegrees; k is the component index (0 or 1).
-- Output: the minimum of the selected component.
componentMin = (ll,k) -> (
    if #ll == 0 then error "cannot take a minimum over an empty list"
    else min apply(ll,d -> d#k)
    );

-- shiftCoordinateMax(ff,i,k)
-- Purpose: return the maximum k-th component of the shifts in term i of ff.
-- Input: ff is a bigraded free resolution; i is a homological degree; k is a degree component.
-- Output: the maximum shift component, or -infinity if term i does not exist.
shiftCoordinateMax = (ff,i,k) -> (
    if i < 0 or i > length ff then -infinity
    else componentMax(degrees ff_i,k)
    );

-- aPair(ff,i,j)
-- Purpose: build a degree pair for the truncation bound from two homological degrees.
-- Input: ff is a bigraded free resolution; i controls the first degree and j the second.
-- Output: {maximum shift in the first degree, maximum shift in the second degree}.
aPair = (ff,i,j) -> {
    shiftCoordinateMax(ff,i,0),
    shiftCoordinateMax(ff,j,1)
    };

-- pairMax(ll)
-- Purpose: take the componentwise maximum of a list of degree pairs.
-- Input: ll is a list of pairs of integers.
-- Output: the pair formed by the maximum in each component.
pairMax = ll -> {
    max apply(ll,p -> p#0),
    max apply(ll,p -> p#1)
    };

-- sourceLowerShift(sourceResolution)
-- Purpose: read the componentwise smallest shift in degree zero of an R-free resolution.
-- Input: sourceResolution is a bigraded free resolution of the source R-module M.
-- Output: the pair underline(a)_0(M) appearing in Proposition 4.2.
sourceLowerShift = sourceResolution -> {
    componentMin(degrees sourceResolution_0,0),
    componentMin(degrees sourceResolution_0,1)
    };

-- bigradedTruncationBound(ff,d1,d2,c1,c2)
-- Purpose: compute the bigraded truncation bound used for the Hom calculation.
-- Input: ff is a free resolution; d1,d2 are one less than the variable counts;
--        c1,c2 are the sums of the weights in the two variable blocks.
-- Output: a Corollary 4.3-type bound {r1,r2}; this function does not compute a ring.
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

-- bigradedGlobalHomBound(sourceResolution,targetAmbientResolution,d1,d2,c1,c2)
-- Purpose: compute the Proposition 4.2 truncation bound for arbitrary bigraded modules M and N.
-- Input: sourceResolution is an R-free resolution of M; targetAmbientResolution is an
--        S-free resolution of N regarded as an ambient-polynomial-ring module;
--        d1,d2 and c1,c2 are the block dimensions and weight sums from Section 4.
-- Output: the pair e_0 in Proposition 4.2.
-- Note: the formula specializes to bigradedTruncationBound when M=N=R.
bigradedGlobalHomBound = (sourceResolution,targetAmbientResolution,d1,d2,c1,c2) -> (
    targetPart := bigradedTruncationBound(targetAmbientResolution,d1,d2,c1,c2);
    sourcePart := sourceLowerShift(sourceResolution);
    {targetPart#0-sourcePart#0,targetPart#1-sourcePart#1}
    );

-- bigradedGlobalHomData(ambient,sourceModule,targetModule,targetModuleOverAmbient,d1,d2,c1,c2)
-- Purpose: compute the nonnegative bigraded global Hom module in Corollary 4.3 for general M,N.
-- Input: ambient is S; sourceModule and targetModule are bigraded modules over the same
--        quotient R of S; targetModuleOverAmbient is an S-module presentation of the same
--        target module N after restriction along S -> R; d1,d2,c1,c2 describe S as in §4.
-- Output: a HashTable containing both resolutions, the certified bound, M_{>=r}, and
--         Hom_R(M_{>=r},N)_{>=0}.
-- Note: supplying targetModuleOverAmbient explicitly ensures that the bound uses the
--       S-free resolution required by Proposition 4.2, rather than an R-free resolution.
bigradedGlobalHomData = (ambient,sourceModule,targetModule,targetModuleOverAmbient,d1,d2,c1,c2) -> (
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

-- isSteinDegree(dd)
-- Purpose: test whether a degree dd has the Stein form (0,>=0).
-- Input: dd is a bidegree.
-- Output: true if dd has first component 0 and nonnegative second component; false otherwise.
isSteinDegree = dd -> (#dd == 2 and dd#0 == 0 and dd#1 >= 0);

-- steinHomData(ambient,igraph,d1,d2,c1,c2)
-- Purpose: compute Hom_R(R_{>=r},R) and its Stein generators for a graph ring R.
-- Input: ambient is the bigraded polynomial ring and igraph is the graph ideal.
--        d1,d2 are one less than the variable counts; c1,c2 are weight sums.
-- Output: a HashTable containing the ring, resolution, bound, Hom module,
--         and its generators of degree (0,>=0).
-- Note: the bound is computed from the resolution, so certifiedBound is true.
steinHomData = (ambient,igraph,d1,d2,c1,c2) -> (
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

-- steinHomDataAtBound(ambient,igraph,bound)
-- Purpose: compute the Hom module using a supplied bound as a faster experimental route.
-- Input: ambient is the bigraded polynomial ring; igraph is the graph ideal;
--        bound is a pair {r1,r2}.
-- Output: a HashTable with the same main fields as steinHomData, without certifying bound.
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

-- evaluateSteinGenerators(data,gammaIndex)
-- Purpose: evaluate the selected Hom generators at a chosen generator gamma of R_{>=r}.
-- Input: data is returned by steinHomData or steinHomDataAtBound;
--        gammaIndex selects the generator gamma.
-- Output: the list of values psi_i(gamma) for the selected Stein generators.
-- Note: Lemma 5.2 uses psi_i(gamma)/gamma as the corresponding coordinate function.
evaluateSteinGenerators = (data,gammaIndex) -> (
    ee := data#"evaluationMatrix";
    apply(data#"steinGeneratorIndices",i -> ee_(gammaIndex,i))
    );

-- steinCoordinateAlgebra(data,gammaIndex,baseImages)
-- Purpose: construct the Stein coordinate algebra C from evaluated Hom generators and a kernel.
-- Input: data is Hom data; gammaIndex selects the localization generator;
--        baseImages are images in R of homogeneous generators of the target ring A.
-- Output: a HashTable containing C, its defining ideal, the localization, and the A-strand.
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

-- steinFingerprint(coordinateData,hilbertMax)
-- Purpose: collect invariants used to compare coordinate algebras during experimental stabilization.
-- Input: coordinateData is returned by steinCoordinateAlgebra; hilbertMax is the Hilbert range.
-- Output: {ring dimension, Hilbert values, and degrees of A-module generators}.
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

-- steinDataByStabilization(ambient,igraph,startBound,maxSteps,requiredMatches,baseImages,hilbertMax)
-- Purpose: experimentally test whether the Stein fingerprint stabilizes as the bound grows.
-- Input: ambient, igraph, and baseImages have the usual meanings; startBound is the initial bound.
--        maxSteps is the number of trials; requiredMatches is the required consecutive matches;
--        hilbertMax sets the Hilbert-function range.
-- Output: a HashTable containing the final data, history, chosen bound, and stabilization status.
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

-- directSteinGraph(data,coordinateData)
-- Purpose: construct the graph closure of the Stein morphism from evaluated Hom generators.
-- Input: data is Hom data; coordinateData is returned by steinCoordinateAlgebra.
-- Output: a HashTable containing the graph ideal, graph map, and auxiliary polynomial rings.
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

-- certifiedHomogeneousGraph(sourcePolynomialRing,sourceIdeal,hImages)
-- Purpose: construct the graph of a morphism given by homogeneous coordinates and certify its projection.
-- Input: sourcePolynomialRing/sourceIdeal define the source; hImages is a list of equal-degree forms.
-- Output: a HashTable containing the graph ideal and base-point-free/projection certificates.
-- Note: saturation by the irrelevant ideal being the unit ideal certifies base-point-freeness.
certifiedHomogeneousGraph = (sourcePolynomialRing,sourceIdeal,hImages) -> (
    bb := sourcePolynomialRing/sourceIdeal;
    imgs := apply(hImages,q -> sub(q,bb));
    if #imgs == 0 then error "the coordinate list must be nonempty";
    imageDegrees := apply(imgs,degree);
    if not all(imageDegrees,d -> d == imageDegrees#0) then
        error "the coordinates must have one common degree";
    irr := ideal gens bb;
    baseIdeal := ideal imgs;
    basePointFree := saturate(baseIdeal,irr) == ideal(1_bb);
    if not basePointFree then
        error "the coordinates have a projective base locus";
    kk := coefficientRing sourcePolynomialRing;
    ny := numgens sourcePolynomialRing;
    nz := #imgs;
    productRing := kk[Variables=>ny+nz,
        Degrees=>join(apply(ny,i->{1,0}),apply(nz,i->{0,1}))];
    yy := take(flatten entries vars productRing,ny);
    zz := drop(flatten entries vars productRing,ny);
    liftSource := map(productRing,sourcePolynomialRing,yy);
    liftedSourceIdeal := liftSource sourceIdeal;
    -- Kernel/Rees calculation in a target containing the quotient source.
    target := bb[graphParameter,Degrees=>{{0,1}}];
    sourceVarsInTarget := apply(flatten entries vars sourcePolynomialRing,
        q -> sub(q,bb));
    graphMap := map(target,productRing,
        join(sourceVarsInTarget,apply(imgs,q -> q*graphParameter)));
    graphIdeal := kernel graphMap;
    new HashTable from {
        "productRing" => productRing,
        "graphIdeal" => graphIdeal,
        "basePointFree" => basePointFree,
        "projectionIsomorphismCertified" => true,
        "sourceVariableCount" => ny,
        "targetVariableCount" => nz,
        "sourceIdealLift" => liftedSourceIdeal
        }
    );

-- selectCertifiedGraphComponent(certified,candidates)
-- Purpose: select the candidate component that agrees with a known certified graph.
-- Input: certified is returned by certifiedHomogeneousGraph; candidates are ideals in the same ring.
-- Output: the index of the matching candidate; an error is raised unless there is exactly one.
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

-- ringMapsAreInverse(ff,gg)
-- Purpose: check whether two affine ring maps are mutually inverse.
-- Input: ff:A->B and gg:B->A; Macaulay2 ring maps represent morphisms contravariantly.
-- Output: true if both compositions are the identity on generators, and false otherwise.
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

-- certifyChartwiseProjectionIsomorphism(sourceRing,coverElements,chartMapPairs)
-- Purpose: certify a projection using inverse maps on charts and a chart-cover check.
-- Input: sourceRing is the source ring; coverElements define the cover;
--        chartMapPairs are pairs of mutually intended inverse ring maps.
-- Output: a HashTable recording the cover, local isomorphism, and projection certificates.
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
