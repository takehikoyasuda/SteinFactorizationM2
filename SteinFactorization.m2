newPackage(
    "SteinFactorization",
    Version => "0.1",
    Date => "5 August 2026",
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
    -- Cheap: the two modules Hom is taken between must live over one ring.  That
    -- targetModuleOverAmbient really presents targetModule after restriction is
    -- not checked, and checking it would cost about what this function costs.
    if ring sourceModule =!= ring targetModule then
        error "the source and target modules must be modules over the same ring";
    if ring targetModuleOverAmbient =!= ambient then
        error "the target over the ambient ring must be a module over that ring";
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

-- A bound is a bidegree, and the two entries mean different blocks.  Say so on
-- the way in rather than let a one-entry or three-entry list reach truncate.
checkBidegree = (bound,what) -> (
    if not instance(bound,List) or #bound != 2
        or not all(bound,i -> instance(i,ZZ)) then
        error(what | " must be a list of two integers");
    );

-- Note: no free resolution is computed, so certifiedBound is false.
steinHomDataAtBound = (ambient,igraph,bound) -> (
    checkBidegree(bound,"the truncation bound");
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

-- gamma is a generator of R_{>=r}, named by its position.  Out of range, the
-- bare matrix subscript would report an array index and not say what was wrong;
-- and gamma=0 would make the evaluation of Lemma 5.2 meaningless rather than
-- merely undefined, since the whole point is to divide by it.
evaluationElementOf = (homData,evaluationElementIndex) -> (
    gg := gens homData#"truncation";
    if not instance(evaluationElementIndex,ZZ)
        or evaluationElementIndex < 0
        or evaluationElementIndex >= numColumns gg then
        error("the evaluation element index must be an integer between 0 and "
            | toString(numColumns gg - 1)
            | ", the truncation having that many generators");
    gamma := gg_(0,evaluationElementIndex);
    if gamma == 0 then error "the chosen evaluation element is zero";
    gamma
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

-- Lemma 5.2 says the subring does not depend on which gamma is taken, so the
-- index is an implementation choice and not a mathematical input.  The
-- one-argument form makes it, and the two-argument form is for saying otherwise.
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
    -- n runs give at most n-1 comparisons, so asking for more agreements than
    -- that is asking for a search that cannot succeed however the runs come out.
    if requiredMatches > maxSteps-1 then
        error("requiredMatches " | toString requiredMatches | " cannot be reached in "
            | toString maxSteps | " steps, which admit only "
            | toString(maxSteps-1) | " comparisons");
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
    ambient := homData#"ambient";
    rr := homData#"ring";
    pp := algebraData#"polynomialRing";
    ll := algebraData#"localizationPresentation";
    -- The localization was built as R[1/gamma] for the R of this homData, so its
    -- coefficient ring identifies which homData the algebraData came from.  Two
    -- tables from different runs are the mistake this catches.
    if coefficientRing ll =!= rr then
        error "the algebra data was not built from this hom data";
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
        -- Not the result of a check: the graph of a morphism out of a proper Y
        -- always projects isomorphically to Y, and basePointFree above is what
        -- establishes that there is a morphism here at all.  The name says so.
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
    if not all(candidates,cc -> ring cc === pp) then
        error "every candidate must be an ideal of the certified product ring";
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

-- Note: this checks charts that the caller supplies.  It does not generate them
-- from a graph, and nothing here ties the i-th map pair to the i-th cover
-- element, to a localization of sourceRing, or to the output of
-- directSteinGraph; that identification is the caller's to make.  So the result
-- records the two things actually established -- that the elements cover, and
-- which pairs are mutually inverse -- and nothing beyond them.
checkChartwiseInverses = (sourceRing,coverElements,chartMapPairs) -> (
    if #coverElements != #chartMapPairs then
        error("there must be one map pair per cover element, but "
            | toString(#coverElements) | " cover elements were given with "
            | toString(#chartMapPairs) | " map pairs");
    irr := ideal gens sourceRing;
    coverIdeal := ideal coverElements;
    covers := saturate(coverIdeal,irr) == ideal(1_sourceRing);
    if not covers then error "the supplied affine charts do not cover Proj(sourceRing)";
    localChecks := apply(chartMapPairs,pair -> ringMapsAreInverse(pair#0,pair#1));
    if not all(localChecks,b -> b) then
        error "at least one chart map pair is not a pair of mutually inverse ring maps";
    new HashTable from {
        "coverCertified" => covers,
        "localIsomorphismsCertified" => localChecks,
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
      in which $h$ is proper with $h_*\mathcal{O}_Y=\mathcal{O}_Z$ (so that the
      fibres of $h$ are geometrically connected) and $g$ is finite; concretely
      $Z=\operatorname{Spec}_X f_*\mathcal{O}_Y$.  This package turns the
      algorithm of @TO2 {"Bibliography", "Yasuda (2026)"}@, Section 5.1, into an
      executable prototype.

      The input is the graph of $f$ represented as a bigraded projective
      scheme.  If $R=S/I_{\Gamma_f}$, then the variables in the source block
      have degrees $(\ast,0)$ and those in the target block $(0,\ast)$, the
      starred entries being positive; in the standard case they are $(1,0)$
      and $(0,1)$, and allowing larger values is what admits weighted
      projective spaces.  The two blocks are the two spaces $f$ runs between:
      the first is the (weighted) projective space $Y$ sits in --- so that the
      source block carries the chosen projective embedding of $Y$, and with it
      the polarization everything below is computed for --- and the second is
      the one $X$ sits in.  $Z$ appears in neither; producing it is the point.
    Text
      The construction is three calls.  Take the finite square map
      $[s:t]\mapsto[s^2:t^2]$ of $\mathbb{P}^1$, whose graph is one
      bihomogeneous equation:
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      Igraph = ideal(y0^2*x1 - y1^2*x0);
      homData = steinHomData(S, Igraph);
      algebraData = steinCoordinateAlgebra homData;
      graphData = directSteinGraph(homData, algebraData);
    Text
      Three keys hold the principal results.  The bidegree the Hom module was
      truncated at, which here was read off a resolution rather than guessed:
    Example
      homData#"bound"
    Text
      A graded coordinate algebra for $Z$, as a quotient ring:
    Example
      algebraData#"ring"
    Text
      And the bihomogeneous ideal of the graph of $h\colon Y\to Z$:
    Example
      graphData#"graphIdeal"
    Text
      The pages of @TO steinHomData@, @TO steinCoordinateAlgebra@ and
      @TO directSteinGraph@ take those three steps in turn; the rest of the
      package is either an alternative to the first step or a way of building
      the input to it.
    Text
      {\bf Assumptions.}  The construction takes several things for granted,
      and checks some of them.  The coefficient ring is expected to be a field.
      $I_{\Gamma_f}$ is expected to be prime, so that $R$ is a domain: the
      evaluation of Lemma 5.2 that gives the strand its multiplication is
      injective for that reason and not otherwise, and
      @TO evaluateSteinGenerators@ says where it is used.  The input is
      expected to be the graph of a morphism rather than an arbitrary
      bihomogeneous subscheme of the product.  No restriction is placed on the
      characteristic.

      Of these, only the block structure is checked --- by
      @TO blockDegreeData@, which every entry point calls before doing anything
      else, and which rejects a variable belonging to both blocks or to
      neither.  Primality is not tested, and neither is the claim that the
      input is a graph; both are expensive relative to the rest of the
      computation on the inputs this package is aimed at.  Build the input with
      @TO certifiedHomogeneousGraph@ or @TO certifiedWeightedGraph@ and it is a
      graph by construction, which is the reason those exist.
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
    :Building the input graph, and certifying it
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
      Computing the bound means resolving $R$ over $S$ out to homological
      degree $d_1+d_2+1$, and on larger inputs that resolution is the most
      expensive thing the package does.  @TO steinHomDataAtBound@ is the same
      computation with a bound supplied instead of derived, for inputs where
      this one does not finish.
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
      {\bf The result table.}  These are the keys meant to be read; the
      remainder are working values, and what is in them may change.

      {\tt "bound"} is the bidegree $\mathbf{r}$ truncated at and
      {\tt "certifiedBound"} whether it came from a resolution, which here it
      always did.  {\tt "ring"} is the quotient $R=S/I_{\Gamma_f}$,
      {\tt "truncation"} is $R_{\ge\mathbf{r}}$, and {\tt "resolution"} is the
      bounded $S$-free resolution the bound was read off.
      {\tt "homModule"} is $\operatorname{Hom}_R(R_{\ge\mathbf{r}},R)$
      truncated to the nonnegative orthant, {\tt "evaluationMatrix"} its
      generators as a matrix with one column per generator, and
      {\tt "steinGeneratorIndices"} and {\tt "steinGeneratorDegrees"} say which
      of those generators lie in the $(0,\ge0)$-strand and in what bidegrees.
      The generators of the truncation are what
      @TO evaluateSteinGenerators@ indexes into.

      The two module keys are easy to confuse.  {\tt "homModule"} is truncated
      to the nonnegative orthant $\ge(0,0)$, which is a bigraded module still
      carrying generators of every bidegree $(a,b)$ with $a,b\ge0$;
      $C$ is the strand $a=0$ inside it, and
      {\tt "steinGeneratorIndices"} is how that strand is picked out.  The
      truncation is taken first because the orthant is what
      @TO truncate@ can be asked for, and the strand is selected afterwards.
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
      $\gamma$, counted from $0$; optional, and $0$ if omitted
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

      The subring $A=R_{(0,\ge0)}$ that $C$ is finite over is not an argument.
      A bidegree $(0,n)$ piece of $S$ is spanned by the monomials in the target
      block alone, so $A$ is generated by the images of the target-block
      variables --- the coordinates of $X$ --- and the ambient ring already
      says which variables those are.  Passing them would be passing back what
      @TO blockDegreeData@ has just worked out, and passing anything else would
      be asking for a subring that is not $A$.

      The point of the whole computation is that $C$ is larger than $A$: the
      extra algebra generators are the evaluated Hom generators, and they are
      what distinguishes $Z$ from $X$.
    Text
      Neither is $\gamma$ an argument, in the ordinary case.  The subring
      obtained does not depend on which generator of $R_{\ge\mathbf{r}}$ is
      taken --- only the localization the computation is carried out in does
      --- so the one-argument form makes the choice, taking the first
      generator.  Supply an index to override it.
    Text
      Continue the square map $[s:t]\mapsto[s^2:t^2]$ of $\mathbb{P}^1$ from
      @TO steinHomData@:
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      Igraph = ideal(y0^2*x1 - y1^2*x0);
      homData = steinHomData(S, Igraph);
      algebraData = steinCoordinateAlgebra homData;
      algebraData#"ring"
    Text
      The coordinate algebra is that ring, and it is the quotient
      {\tt "polynomialRing"}$/${\tt "definingIdeal"} of the next two:
    Example
      algebraData#"polynomialRing"
      algebraData#"definingIdeal"
    Text
      $X$ is $\mathbb{P}^1$ here, so $A=k[p_0,p_1]$ is a polynomial ring; the
      third variable $p_2$ is the one evaluated Hom generator, and the single
      relation is what it satisfies over $A$.  That relation is a conic, and
      the $Z$ it presents is a $\mathbb{P}^1$: the algebra is the section ring
      for the polarization pulled back from $X$, which is $\mathcal{O}(2)$
      here, not for $\mathcal{O}_Z(1)$.
    Text
      {\bf The result table.}  These are the keys meant to be read; the
      remainder are working values.  {\tt "ring"} is the coordinate algebra,
      {\tt "polynomialRing"} and {\tt "definingIdeal"} the quotient it is
      presented as, and {\tt "images"} the elements of $R[1/\gamma]$ that the
      variables of {\tt "polynomialRing"} stand for, in the same order ---
      first the target-block coordinates, then the evaluated Hom generators.
      {\tt "baseRing"} is $A$ and {\tt "baseInclusion"} the map $A\to R$;
      {\tt "strandAsAModule"} and {\tt "strandAPresentation"} are $C$ as a
      finite $A$-module and its presentation.  {\tt "evaluationElement"} is the
      $\gamma$ actually used and {\tt "localizationPresentation"} the
      $R[1/\gamma]$ built to divide by it; {\tt "extraHomIndices"} says which
      strand generators got a variable of their own, the unit in bidegree
      $(0,0)$ being the one that does not, and {\tt "mapToLocalization"} is the
      map whose kernel is {\tt "definingIdeal"}.
    Text
      {\bf An advanced example: $C$ not free over $A$.}  Take
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
      The coordinate algebra of $Z$ is again
      {\tt "polynomialRing"}$/${\tt "definingIdeal"}, and this time neither is
      small:
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
      Neither of the two things on show here is guaranteed, and the square map
      above showed neither.  What $A$ is: the coordinate ring of the conic, not
      a polynomial ring, because $X$ is a proper subvariety of $\mathbb{P}^2$
      and its three coordinates satisfy the equation cutting it out.  Send $Y$
      onto a whole projective space instead --- which is what the square map
      does --- and the target coordinates are algebraically independent, so $A$
      comes back free of relations.
    Text
      What $C$ is: the section ring $\bigoplus_n H^0(Z,g^*\mathcal{O}_X(1)^n)$,
      and $Z$ is the $\mathbb{P}^1_{u:v}$ that $h$ projects onto.  Since $g$
      maps it two-to-one onto the conic, $g^*\mathcal{O}_X(1)$ is
      $\mathcal{O}(4)$ on that $\mathbb{P}^1$, so $C_n=k[u,v]_{4n}$.
    Text
      Why $C$ is not free over $A$: $\mathcal{O}_X(1)$ restricted to the conic
      is $\mathcal{O}(2)$ on the $\mathbb{P}^1$ underneath it, so the image of
      $A$ in degree $n$ is spanned by the monomials $A$ can reach, which are
      the $u^iv^j$ of degree $4n$ with $i$ even.  $C_n$ contains the odd ones
      too.  In degree one the two missing monomials are $uv^3$ and $u^3v$, and
      those are the two extra generators of $C$ as an $A$-module.
    Text
      What the presentation says: its two columns are the relations those two
      generators satisfy over $A$.  Where the finite part is a coordinatewise
      power map onto a whole projective space --- which is what most of the
      examples in this package are --- the module comes out free instead and
      the presentation is the zero matrix, as it is for the square map.
    Text
      This example is {\tt tests/conic-target.m2}, where the fibres are
      checked as well.
  Caveat
    A generator of $C$ as a finite $A$-module need not be needed as an algebra
    generator.  When one is redundant the presentation simply carries a
    variable more than necessary; the quotient ring is still the right one.
    What that costs is the next step: @TO directSteinGraph@ eliminates in a
    ring with one variable per algebra generator, and a redundant variable
    enlarges the elimination.  On {\tt tests/blowup-twisted-cubic.m2} it has
    not been run to completion for that reason --- an expected cost rather than
    a known error in the answer.  Minimizing the algebra generators is the
    obvious remedy and is not implemented.
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
      as returned by @TO steinCoordinateAlgebra@ from that same {\tt homData};
      the two must correspond, and that they do is checked by comparing the
      ring $R$ against the one the localization was built over
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
    Text
      Working over $R[1/\gamma]$ rather than $R$ is what saturates the result.
      An $F$ vanishing on $\Gamma_h$ away from $\{\gamma=0\}$ has
      $\gamma^kF=0$ in $R$ for some $k$, and in $R[1/\gamma]$ that says
      $F=0$; so the kernel taken there is already saturated with respect to
      $\gamma$, and what comes back is the closure of the part of the graph
      lying over $\{\gamma\neq0\}$.  Taking the kernel over $R$ instead would
      return an ideal with the same zero locus off $\{\gamma=0\}$ but embedded
      components along it.  Nothing is saturated with respect to the
      biprojective irrelevant ideal; the result table records the one that was
      done under {\tt "saturationByLocalization"}, which is a statement about
      the method and not the outcome of a test.
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
      Reading the ideal takes knowing which variable is which.  The joint ring
      is generated automatically, so all seven print as $p_0,\dots,p_6$: the
      degrees above say that $p_0,p_1$ are the source coordinates $y_0,y_1$ and
      $p_2,p_3$ the target coordinates $x_0,x_1$, and the remaining
      $p_4,p_5,p_6$ are the three $z_i$, in the order
      @TO steinCoordinateAlgebra@ produced its algebra generators --- so
      $p_4,p_5$ stand for the coordinates of $X$ again and $p_6$ for the
      evaluated Hom generator.  That last one is the new coordinate, the one
      that makes this $Z$ rather than $X$.
    Text
      The seven relations then fall into four kinds.  One, $p_1^2p_2-p_0^2p_3$,
      is the equation of $\Gamma_f$ carried over unchanged.  One,
      $p_4p_5-p_6^2$, is the conic that @TO steinCoordinateAlgebra@ returned:
      $Z$ in its own coordinates.  Two, $p_3p_4-p_2p_5$ and its consequences,
      say $[p_4:p_5]=[x_0:x_1]$ --- proportionality rather than equality,
      because the $z_i$ are coordinates on their own projective space.  And the
      two that write $p_6$ down over $Y$, $p_1p_4-p_0p_6$ and $p_0p_5-p_1p_6$,
      are where $h$ itself is recorded: $p_6/p_4=y_0/y_1$, which is the
      coordinate function $y_0x_1/y_1$ divided by $x_0$.
    Text
      {\bf The result table.}  {\tt "jointRing"} is the ring $J$ above,
      {\tt "graphIdeal"} the kernel, and {\tt "graphMap"} the map $\Phi$ it is
      the kernel of.  {\tt "ambientVariableCount"} and
      {\tt "steinVariableCount"} say where the variables of $J$ split into the
      two groups, and {\tt "saturationByLocalization"} is the note above.
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
      $(0,\ast)$, the starred entry positive; in the rest of the package this
      is the ambient polynomial ring, but only the degrees are read, so a
      quotient of one answers as well
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
      the bidegree $\mathbf{r}=(r_1,r_2)$ to truncate at, a list of exactly two
      integers
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

      ``Large enough'' is meant componentwise: Corollary 4.3 produces one
      bidegree, and any $\mathbf{r}$ with $r_1\ge$ its first entry and
      $r_2\ge$ its second does as well, because truncating further only
      removes elements the Hom module was going to ignore.  Componentwise is a
      partial order, so two supplied bounds need not be comparable at all, and
      neither being larger than the other says nothing about either.
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      Igraph = ideal(y0^2*x1 - y1^2*x0);
      homData = steinHomDataAtBound(S, Igraph, {1,0});
      homData#"certifiedBound"
      homData#"steinGeneratorDegrees"
    Text
      Here $(1,0)$ happens to be the bound @TO steinHomData@ computes for this
      input, so the two agree:
    Example
      certifiedData = steinHomData(S, Igraph);
      homData#"bound" == certifiedData#"bound"
    Text
      The difference is that nothing in the call above established that.  In
      {\tt tests/blowup-twisted-cubic.m2} the source sits in
      $\mathbb{P}^{11}$ and the target in $\mathbb{P}^3$, so the resolution
      Corollary 4.3 asks for runs to homological degree
      $d_1+d_2+1=15$ over a ring in sixteen variables and has not been
      computed here;
      $\mathbf{r}=(2,0)$ is supplied and then checked against independently
      known geometry instead.

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
      the bidegree to start from, a list of exactly two integers; its first
      coordinate is what gets incremented
    maxSteps:ZZ
      how many bounds to try at most, at least $2$
    requiredMatches:ZZ
      how many consecutive agreements to insist on, at least $1$ and at most
      {\tt maxSteps}$-1$, since $n$ runs admit only $n-1$ comparisons
    hilbertMax:ZZ
      how far out to compare Hilbert functions, nonnegative
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
    Text
      Those three numbers are a fingerprint and not the answer itself.  They
      are what can be compared cheaply between two runs whose results live in
      different rings: the two coordinate algebras are quotients of polynomial
      rings with possibly different numbers of variables, so they cannot simply
      be tested for equality, while dimension, finitely many Hilbert values and
      module-generator degrees are numbers.  What a fingerprint can miss is
      accordingly anything that leaves all three fixed --- two non-isomorphic
      algebras with the same Hilbert function, or a change first visible in
      degree greater than {\tt hilbertMax}, or a change in the relations that
      does not move the generator degrees.
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
      The runs at $(1,0)$ and $(2,0)$ agreed, so the search stopped there.
      {\tt "chosenBound"} is the last bound run, which is the later member of
      the matching pair and not the earliest bound that agreed; the tables
      returned are that run's.  Here $(1,0)$ is the bound @TO steinHomData@
      certifies for this input, so the heuristic is being run against an answer
      that can also be had outright --- a sanity check on the method, on a case
      where the certified bound is available for comparison.
    Text
      That the answer stopped moving is evidence and not more than evidence:
      only finitely many bounds were tried, and nothing rules out a later one
      differing.  So {\tt "certifiedBound"} is false however the run came out,
      and the table says so in as many words:
    Example
      stab#"certifiedBound"
      stab#"warning"
    Text
      {\bf The result table.}  Besides those two, {\tt "stabilized"} says
      whether the search met its target rather than exhausting
      {\tt maxSteps}, {\tt "stepsRun"} how many bounds were tried,
      {\tt "consecutiveMatches"} how many agreements in a row it ended on, and
      {\tt "chosenBound"}, {\tt "homData"} and {\tt "algebraData"} are the last
      run.  {\tt "history"} is one hash table per run, each with that run's
      {\tt "bound"}, its {\tt "fingerprint"} --- the triple of dimension,
      Hilbert values and module-generator degrees compared above --- and its
      own {\tt "homData"} and {\tt "algebraData"}, so that a run other than the
      last can be taken up if wanted.
  Caveat
    Only the first coordinate of the bound is incremented.  That is the
    direction the truncation actually needs: the strand being computed is
    $(0,\ge0)$, so enlarging $r_2$ discards target-block degrees the answer is
    read off, whereas enlarging $r_1$ discards source-block degrees the strand
    does not see.  Corollary 4.3 moves both coordinates, so a search along the
    first alone is not a search through all bounds it might have produced; if
    the second coordinate of {\tt startBound} is too small, no number of steps
    here will find that out.  Choose it from the geometry, or from a certified
    bound on a smaller instance of the same shape.
  SeeAlso
    steinHomData
    steinHomDataAtBound

Node
  Key
    certifiedHomogeneousGraph
  Headline
    build the graph of a morphism to projective space, with a certificate
  Usage
    graphData = certifiedHomogeneousGraph(B, I, hImages)
  Inputs
    B:Ring
      a singly graded polynomial ring
    I:Ideal
      an ideal of {\tt B}, so that the source is $Y=\operatorname{Proj}(B/I)$
    hImages:List
      forms of one and the same degree, the coordinates $h_i$ of the morphism
      $f\colon Y\to\mathbb{P}^n$; representatives in {\tt B} are what to pass,
      and they are reduced into $B/I$ on the way in
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
      That ideal in that ring is exactly what @TO steinHomData@ takes, which is
      the reason this function is in the package:
    Example
      homData = steinHomData(graphData#"productRing", graphData#"graphIdeal");
      homData#"bound"
      homData#"steinGeneratorDegrees"
    Text
      The strand has only its unit generator, which says that $Z=X$ here: the
      twisted cubic map is a closed immersion, so $f$ is already finite and
      there is nothing for $h$ to contract.  A morphism with connected fibres
      to find is what the examples on the other pages have.
    Text
      This is the all-weights-one case of @TO certifiedWeightedGraph@, which is
      also where the proportionality test there reduces to ``all coordinate
      degrees agree''.
    Text
      {\bf The result table.}  {\tt "productRing"} and {\tt "graphIdeal"} are
      the pair to pass on; {\tt "sourceVariableCount"} and
      {\tt "targetVariableCount"} say where the variables of the product ring
      split, {\tt "targetWeights"} records the weights (all $1$ here), and
      {\tt "sourceIdealLift"} is {\tt I} moved into the product ring.

      Two of the keys are claims, and they are of different kinds.
      {\tt "basePointFree"} is the outcome of a computation: the ideal of the
      $h_i$ is saturated by the irrelevant ideal and the result compared with
      the unit ideal, and a base locus is an error rather than a value of
      {\tt false}.  {\tt "projectionIsomorphismByConstruction"} is not the
      outcome of anything --- the graph of a morphism out of a proper $Y$
      always projects isomorphically to $Y$, and base-point-freeness is what
      says there is a morphism here.  The kernel returned is a graph because it
      was built as one, not because it was tested.
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
      the coordinates $h_i$ of the morphism; as in
      @TO certifiedHomogeneousGraph@, pass representatives in {\tt B} and they
      are reduced into $B/I$
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
      $\deg(h_i)=a_ie$ for one common $e$, which is the unweighted ``all
      degrees equal'' when every $a_i$ is $1$.
    Text
      What the common multiplier $e$ is, geometrically: it is the degree in
      which the $h_i$ are being read as sections, so that the morphism pulls
      $\mathcal{O}(1)$ on the target back to $\mathcal{O}(e)$ on the source.
      That the degrees are proportional to the weights is what makes the
      morphism well defined --- under $r\mapsto\lambda r$ the tuple
      $(h_0,\dots,h_n)$ goes to
      $(\lambda^{a_0e}h_0,\dots,\lambda^{a_ne}h_n)$, which is the weighted
      scaling by $\lambda^e$ --- and it says nothing whatever about whether
      the morphism is finite, birational or an isomorphism.
    Text
      A degree-two morphism $\mathbb{P}^1\to\mathbb{P}(1,2)$, given by
      $(r_0,r_1^2)$:
    Example
      B = QQ[r0,r1];
      graphData = certifiedWeightedGraph(B, ideal(0_B), {r0,r1^2}, {1,2});
      degrees graphData#"productRing"
      graphData#"graphIdeal"
    Text
      Reading a weighted target takes one more step than an unweighted one.
      On the chart $y_0\neq0$ of $\mathbb{P}(1,2)$ the coordinate is not
      $y_1/y_0$, which is not invariant under
      $(y_0,y_1)\mapsto(\lambda y_0,\lambda^2y_1)$, but $u=y_1/y_0^2$.  The map
      above pulls it back to $(r_1/r_0)^2$, the square of a coordinate on
      $\mathbb{P}^1$, so it has degree two.  Equivalently: compose with the
      isomorphism $\mathbb{P}(1,2)\to\mathbb{P}^1$, $[y_0:y_1]\mapsto
      [y_0^2:y_1]$, and the composite is $[r_0:r_1]\mapsto[r_0^2:r_1^2]$.  No
      map of this shape can be an isomorphism: with $e=1$ the composite is
      always $[h_0^2:h_1]$ for a linear $h_0$ and a quadratic $h_1$.  For an
      isomorphism between the two, go the other way, by the equal weighted
      degree forms $(y_0^2,y_1)$ on $\mathbb{P}(1,2)$; that is Test 2 of
      {\tt tests/weighted.m2}.
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
      mistake into a rejected input.  Dropping the square above leaves
      coordinates of degrees $(1,1)$, which are not proportional to $(1,2)$:
    Example
      try (certifiedWeightedGraph(B, ideal(0_B), {r0,r1}, {1,2}); "accepted") else "rejected"
    Text
      Inferred weights would have read that as a perfectly good morphism to
      $\mathbb{P}^1$ instead.
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
      ideals of its {\tt "productRing"}; a candidate belonging to some other
      ring is rejected rather than compared
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

      Producing the candidates is not this function's business, nor any other
      function's here: they come from a decomposition carried out elsewhere,
      and what this package supplies is the certified graph to test them
      against.
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
    Because the comparison is made after saturation, what the returned index
    identifies is a biprojective subscheme and not an ideal.  A candidate
    agreeing with the certified graph away from the irrelevant locus is
    reported as the match even if the two ideals differ.
  SeeAlso
    certifiedHomogeneousGraph
    certifiedWeightedGraph

Node
  Key
    checkChartwiseInverses
  Headline
    check a cover and a list of mutually inverse ring map pairs
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
      opposite directions; there must be as many pairs as cover elements
  Outputs
    :HashTable
      recording that the elements cover, under {\tt "coverCertified"}, and
      which pairs are mutually inverse, under
      {\tt "localIsomorphismsCertified"}
  Description
    Text
      @TO directSteinGraph@ returns the graph of $h\colon Y\to Z$ as an ideal;
      that the projection $\Gamma_h\to Y$ is an isomorphism, so that the ideal
      really does present $h$ as a morphism out of $Y$, is a separate claim.
      One way to establish it is chart by chart, and this is the arithmetic
      part of that argument: it checks that the supplied elements cover
      $\operatorname{Proj}(\mathtt{sourceRing})$, by a saturation, and that in
      each supplied pair the two ring maps compose to the identity in both
      directions.
    Text
      What it does not do is as important.  Nothing here ties the $i$-th map
      pair to the $i$-th cover element, or either ring of a pair to the
      corresponding localization of {\tt sourceRing}, or any of it to the graph
      @TO directSteinGraph@ returned.  Mutually inverse maps between rings that
      have nothing to do with the problem will pass.  Making the
      identification --- these rings are the charts of $Y$ and of $\Gamma_h$,
      and these maps are the projection and its inverse --- is the caller's
      part of the argument, and it is the part that is not checked.  So the
      result is reported as two checks rather than as a certificate, and no key
      of it says that the projection is an isomorphism.
    Text
      The squaring map of $\mathbb{P}^1$, on its two standard charts.  On
      $y_1\neq0$ the source coordinate is $r=y_0/y_1$ and the graph chart is
      $\{(r,q):q=r^2\}$, whose projection to the $r$-line is inverted by
      $r\mapsto(r,r^2)$; the chart $y_0\neq0$ is the same with $s=y_1/y_0$.
      The cover elements are listed in the order the pairs are:
    Example
      Y = QQ[y0,y1];
      A0 = QQ[r]; G0 = QQ[rg,q0]/ideal(q0-rg^2);
      A1 = QQ[s]; G1 = QQ[sg,q1]/ideal(q1-sg^2);
      checks = checkChartwiseInverses(Y, {y1,y0},
          {{map(G0,A0,{rg}), map(A0,G0,{r,r^2})},
           {map(G1,A1,{sg}), map(A1,G1,{s,s^2})}});
      checks#"numberOfCharts"
      checks#"coverCertified"
      checks#"localIsomorphismsCertified"
    Text
      That order is not checked either --- listing the elements the other way
      round would pass just the same.  It is written correctly because the
      reader is meant to follow the argument, not because the function can
      tell.
  Caveat
    Compatibility on overlaps is not checked, and neither is anything relating
    the charts to each other.  Local isomorphisms on a cover do glue to a
    global one when they agree on overlaps, so this is a proper part of that
    argument and not the whole of it.  A worked instance with four charts, for
    the $\mathbb{P}^1\times\mathbb{P}^1\to\mathbb{P}^1$ example whose Stein
    intermediate is the twisted cubic, is in {\tt tests/basic.m2}.
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
      $R_{\ge\mathbf{r}}$; it must be one of $0,\dots,n-1$ for the $n$
      generators that {\tt homData\#"truncation"} has, and the generator it
      names must be nonzero
  Outputs
    :List
      the elements $\varphi_i(\gamma)\in R$, one for each generator $\varphi_i$
      of the $(0,\ge0)$-strand, in the order of
      {\tt homData\#"steinGeneratorDegrees"}
  Description
    Text
      The strand $C$ carries no multiplication of its own, being a module of
      homomorphisms.  Lemma 5.2 of @TO2 {"Bibliography", "Yasuda (2026)"}@ gives
      it one by realizing it inside a localization: fix a nonzero
      $\gamma\in R_{\ge\mathbf{r}}$ and send
      $$\varphi\longmapsto\varphi(\gamma)/\gamma\in R[1/\gamma].$$
      This is injective provided $R$ is a domain: if $\varphi(\gamma)=0$ then
      $\gamma\varphi(\gamma')=\varphi(\gamma'\gamma)=\gamma'\varphi(\gamma)=0$
      for every $\gamma'\in R_{\ge\mathbf{r}}$, and cancelling the nonzero
      $\gamma$ --- which is where the domain hypothesis is used and the only
      place it is --- gives $\varphi=0$.  That $R$ is a domain is the
      standing assumption that $I_{\Gamma_f}$ is prime, described under
      @TO SteinFactorization@; nothing in this package tests it, and on a
      non-prime input the map above may lose information without saying so.
      The evaluation does not depend on which $\gamma$ is taken: for any other
      $\gamma'\in R_{\ge\mathbf{r}}$ we have
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
      the same target presented over {\tt S} rather than over $R$; that it
      really does present {\tt N} after restriction is not checked, and
      checking it would cost about what this function costs
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
      The two sides are resolved to different depths, and the result table
      keeps them apart.  Proposition 4.2 reads shifts out to homological degree
      $d_1+d_2+1$ on the target side, and {\tt "targetAmbientResolution"} is
      that resolution of {\tt NS} over {\tt S}.  From the source side it reads
      only the lowest shift of a free presentation, so {\tt "sourceResolution"}
      is the free cover alone, asked for with {\tt LengthLimit => 0}; it is not
      a computed tail of a resolution of {\tt M}, and over $R$ there would in
      general be no finite one to compute.
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
      Proposition 4.2 says it should.  The bound is the target part minus the
      source part, and the source part is the least shift appearing in the free
      cover.  Macaulay2 writes $R^{\{\{1,1\}\}}$ for the free module whose
      generator sits in degree $(-1,-1)$ --- the superscript is the twist, so
      the sign is opposite to the degree --- and its free cover therefore has
      least shift $(-1,-1)$.  Subtracting that adds $(1,1)$, so the bound
      should come out one higher in each coordinate than the $(0,0)$-shifted
      one above:
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
      cited in this documentation belongs to.  Section 5.1 is the algorithm.
      The results the code is organized around are Proposition 4.2, the bound
      for a pair of modules, which is @TO bigradedGlobalHomData@; Corollary
      4.3, its specialization to $M=N=R$, which is the bound
      @TO steinHomData@ computes and whose four numbers
      @TO blockDegreeData@ reads off the ambient ring; and Lemma 5.2, the
      evaluation that gives the strand its multiplication, which is
      @TO evaluateSteinGenerators@.

      The link is to v2 deliberately.  Every number quoted above is a number in
      v2, and a later version may renumber them; the versionless record is at
      @HREF{"https://arxiv.org/abs/2603.13703","arXiv:2603.13703"}@ and is the
      one to cite for the mathematics.
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
      The Stacks Project Authors.  {\em Stein factorization}, Section 37.53.
      @HREF{"https://stacks.math.columbia.edu/tag/03GX","Tag 03GX"}@

      The definition and the basic properties, in the generality of schemes.
      Theorem 37.53.4 is the statement in the Noetherian case, and it is where
      the fibres of $h$ are said to be geometrically connected rather than
      merely connected.
///
