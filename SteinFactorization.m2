needsPackage "Truncations";

-- Core implementation of Section 5.1 of Yasuda, arXiv:2603.13703v2.
-- Input convention: variables of the source block have degrees (positive,0),
-- variables of the target block have degrees (0,positive).

componentMax = (ll,k) -> (
    if #ll == 0 then -infinity else max apply(ll,d -> d#k)
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

isSteinDegree = dd -> (#dd == 2 and dd#0 == 0 and dd#1 >= 0);

-- General front end.  This computes precisely the module occurring in (5.2):
-- Hom_R(R_{>=r},R), together with the indices of its (0,>=0) generators.
-- d1,d2 are one less than the numbers of variables in the two blocks;
-- c1,c2 are the sums of their weights.
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

-- Performance-oriented entry point when a valid Corollary 4.3 bound is known
-- externally or supplied for experimentation.  This skips the often dominant
-- minimal S-free resolution used only to derive the bound.
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

-- Evaluate the selected Hom generators on a chosen generator gamma of R_{>=r}.
-- The returned values are psi_i(gamma); Lemma 5.2 represents the corresponding
-- coordinate functions by psi_i(gamma)/gamma.
evaluateSteinGenerators = (data,gammaIndex) -> (
    ee := data#"evaluationMatrix";
    apply(data#"steinGeneratorIndices",i -> ee_(gammaIndex,i))
    );

-- Construct C from the currently selected degree-(0,>=0) Hom generators by
-- Lemma 5.2.  TODO for full Section 5.1 fidelity: restrict a free R-presentation
-- to an A-presentation of the entire strand, not only minimal R-generators.
-- baseImages are the images in R of homogeneous generators of A.  The first
-- Hom generator of degree (0,0) is the unit and is omitted as redundant.
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

steinFingerprint = (coordinateData,hilbertMax) -> (
    cc := coordinateData#"ring";
    aaModule := coordinateData#"strandAsAModule";
    {
        dim cc,
        apply(toList(0..hilbertMax),i -> hilbertFunction(i,cc)),
        degrees aaModule
        }
    );

-- Heuristic stabilization with the full first-degree-zero A-module strand.
-- Consecutive truncations are compared by dimension, Hilbert values, and the
-- degrees of finite A-module generators.  The result remains non-certified:
-- finite agreement does not prove the explicit Corollary 4.3 bound.
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

-- Direct construction of Gamma_h from the evaluated Hom generators.
-- The source is represented by Gamma_f=Proj(R), canonically isomorphic to Y.
-- We map a polynomial ring in the ambient graph variables and new Z variables
-- to R_gamma[t].  A Z generator of weight w is sent to its evaluated section
-- times t^w.  Taking the kernel contracts from the localization, hence performs
-- the required gamma-saturation automatically and returns the graph closure.
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

-- Construct the graph of a morphism Proj(B)->P^(n-1) given by homogeneous
-- forms of one degree, and certify that projection of the graph to Proj(B)
-- is an isomorphism.  The certificate is base-point-freeness: saturation of
-- the image ideal by the irrelevant ideal is the unit ideal.  The graph ideal
-- is the kernel of k[y,z] -> B[t], z_i |-> h_i*t (the Rees graph).
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

-- Select the unique candidate equal to the certified graph, up to the
-- biprojective irrelevant saturation.  Candidate ideals must live in the same
-- product ring as certified#"graphIdeal".
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

-- Chart-gluing layer for graph morphisms not representable by one homogeneous
-- coordinate list.  Each chart pair consists of mutually inverse affine ring
-- maps (contravariantly representing the projection and its local inverse).
-- Since every local inverse is inverse to the restriction of the same global
-- projection, the inverses agree on overlaps by uniqueness.  The saturation
-- check proves that the selected source charts cover Proj(sourceRing).
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
