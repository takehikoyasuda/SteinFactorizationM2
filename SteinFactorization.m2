newPackage(
    "SteinFactorization",
    Version => "0.1",
    Date => "5 August 2026",
    Headline => "Stein factorization of a projective morphism given by its graph",
    Authors => {{ Name => "Takehiko Yasuda", Email => "yasuda.takehiko.sci@osaka-u.ac.jp" }},
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
    "certifyChartwiseProjectionIsomorphism"
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
evaluateSteinGenerators = (homData,gammaIndex) -> (
    ee := homData#"evaluationMatrix";
    apply(homData#"steinGeneratorIndices",i -> ee_(gammaIndex,i))
    );

-- Note: the degree-(0,0) Hom generator is the unit and is omitted as an extra algebra generator.
-- TODO: organize the finite A-module presentation of the full strand more completely.
steinCoordinateAlgebra = (homData,gammaIndex,baseImages) -> (
    rr := homData#"ring";
    tt := homData#"truncation";
    hh := homData#"homModule";
    wanted := homData#"steinGeneratorIndices";
    extra := select(wanted,i -> (degrees hh)#i != {0,0});
    gamma := (gens tt)_(0,gammaIndex);
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
    evals := apply(extra,i -> ee_(gammaIndex,i));
    images := join(
        apply(baseImages,q -> sub(q,ll)),
        apply(evals,q -> sub(q,ll)*inv)
        );
    weights := join(
        apply(baseImages,q -> {(degree q)#1}),
        apply(extra,i -> {((degrees hh)#i)#1})
        );
    kk := coefficientRing homData#"ambient";
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
      in which $h$ is proper with $h_*\mathcal{O}_Y=\mathcal{O}_Z$ (so that $h$
      has connected fibers) and $g$ is finite; concretely
      $Z=\operatorname{Spec}_X f_*\mathcal{O}_Y$.  This package turns the
      algorithm of Yasuda (2026), Section 5.1, into an executable prototype.

      The input is the graph of $f$ represented as a bigraded projective
      scheme.  If $R=S/I_{\Gamma_f}$, then the variables in the source block
      have degrees $(\ast,0)$ and those in the target block $(0,\ast)$, the
      starred entries being positive; in the standard case they are $(1,0)$
      and $(0,1)$, and allowing larger values is what admits weighted
      projective spaces.
  Subnodes
    steinHomData

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
      The truncation bound is obtained from shifts in a bounded bigraded free
      resolution of $R$ over the ambient polynomial ring.  This is the
      computational counterpart of the bound in Corollary 4.3 of Yasuda (2026).

      Those two arguments are all that is needed.  Corollary 4.3 is stated in
      terms of the dimensions $d_s$ of the two ambient projective spaces and
      the sums $c_s$ of the degrees of the variables in each block, but the
      degrees of {\tt S} already determine all four, so they are computed
      rather than passed; see @TO blockDegreeData@.
    Text
      The finite square map $[s:t]\mapsto[s^2:t^2]$ of $\mathbb{P}^1$.  Its
      graph is cut out by one bihomogeneous equation:
    Example
      S = QQ[y0,y1,x0,x1, Degrees => {{1,0},{1,0},{0,1},{0,1}}];
      Igraph = ideal(y0^2*x1 - y1^2*x0);
      homData = steinHomData(S, Igraph);
    Text
      The computed bound and the degrees of the generators of the
      $(0,\ge0)$-strand:
    Example
      homData#"bound"
      homData#"certifiedBound"
      homData#"steinGeneratorDegrees"
    Text
      There are two strand generators: the unit in bidegree $(0,0)$, and one
      further generator in bidegree $(0,1)$.  That extra generator is what
      distinguishes the Stein intermediate $Z$ from $X$.
  SeeAlso
    blockDegreeData
///
