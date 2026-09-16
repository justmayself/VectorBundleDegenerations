newPackage(
        "VectorBundleDegenerations",
        Version => "0.1",
        Date => "",
        Headline => "code from 2025 ICMS workshop on degenerating vector bundles",
        Authors => {
    	    { Name => "Kimuli Philly Ivan", Email => "kpikimuli@gmail.com", HomePage => ""},
    	    { Name => "Diane Maclagan", Email => "d.maclagan@warwick.ac.uk", HomePage => ""},
             { Name => "Mayo Mayo Garcia ", Email => "mayo.mayo-garcia@warwick.ac.uk", HomePage => ""},
            { Name => "Andre Mialebama", Email => "sainteudes@gmail.com", HomePage => ""},
            { Name => "Ignatius Philip Ngwongwo", Email => "igphils.7@gmail.com", HomePage => ""},
	    { Name => "Namanya Caroline", Email => "caronamanya97gmail.com", HomePage => ""},
    	    { Name => "Olasupo Felemu", Email => "ofelemu0@gmail.com", HomePage => ""},
    	    { Name => "Jared Ongaro", Email => "ongaro@uonbi.ac.ke", HomePage => "https://profiles.uonbi.ac.ke/ongaro"},	    
   	    { Name => "Gregory Sankaran", Email => "gksankaran@gmail.com", HomePage => "https://people.bath.ac.uk/masgks"}
	    },
        AuxiliaryFiles => false,
        DebuggingMode => false,
        Reload => true,
        PackageExports =>{"NormalToricVarieties"},
        DebuggingMode => true
        )
				
export {
    -- Types
    "GrobnerFan",
    -- Constructors
    "grobnerFan",
    -- Functions and methods
    "moduleToIdeal","grobnerPolyhedralFan",
    "initialModule","correctionVector",
    "isVectorBundle", "isReflexiveSheaf", "isTorsionFreeSheaf","isEquivariant", "isToricVectorBundle",
    "fakeFan","generateHomogeneousModule", 
    "infoInitialModules","specialSubfan", "equivariantCones",
    --"recoverInformation",
     "degenerateModule", "listCones",
    "saveDegeneration", "fanToString", 
    "latticeInteriorPoint", "displayInformation", "hasDuplicates",
    "fineGrading",
    -- Methods inputs:
    "Random","Correction","TimeSpent"
    -- Hash Table Keys:
    

}

protect DDual
protect noDuplicates
protect conerays
protect coneDim
protect coneSpan
protect infoDegens
protect analyzeDegens
protect allCones
protect summaryStats
protect equivCones
protect intPoint 
protect equivariant
protect degeneration
protect torsionFreeSheaf
protect reflexiveSheaf
protect vectorBundle
protect modulesList
protect notVectorBundle
protect notEquivariant
protect toricVB
protect correctvc

--exportFrom("Polyhedra","maxCones")

-* Code section *-

needsPackage "gfanInterface";
needsPackage "Polyhedra";
-- Used for isReflexiveSheaf and isTorsionFreeSheaf
needsPackage "MinimalPrimes";
needsPackage "WeilDivisors";

---------------------------------------------------------------------------
-- CODE SECTION
---------------------------------------------------------------------------
-*
Given a submodule of a free module over a polynomial ring we can consider 
its initial form with respect to a given weight.
The guiding idea is defining a new type called GrobnerFan where we will store
the fan of possible degenerations. The primary data store is the fan itself,
as this computation can be expensive, and then we will compute further information 
about said degenerations.
*-

---------------------------------------------------------------------------
-- DEFINING NEW TYPE, BASIC CONSTRUCTORS AND GETTERS
---------------------------------------------------------------------------

GrobnerFan = new Type of HashTable
--GrobnerFan.synonym = "fan of Grobner degenerations of a given module"
globalAssignment GrobnerFan


-- Auxiliary function for the contruction of the Grobner fan of a module

--take a submodule of a free module oplus S e_i and return an ideal in the polynomial
--ring S[e_i]

moduleToIdeal = M ->(
    S := ring M;
--    myChar := char S;                                                                      
    E := {};
    G := {};
    m := rank ambient M;
    shifts := degrees ambient M;
    s := #(entries vars(S))_0;
    -- Makes sure the degrees are correct and the output ideal is homogeneous
    degs := apply(degrees(S) ,i->(append(i,0))) | apply(shifts,i->(append(i,1))); 
    k := s+m;
    e := symbol e;
    S2 :=QQ[e_1..e_m];
     R :=QQ[gens(S)|gens(S2), Degrees => degs]; 
    L := entries transpose gens M;
    for i from 0 to #L-1 do (
         U := L_i;
         for j from 0 to #U-1 do (
             E = E|{sub(U_j,R)*R_(s+j)};
         );
         g := sum(E);
         G = G|{g};
         E := {};
     );
     I := ideal(G);
     return I;
);

grobnerPolyhedralFan = M ->(
-- Construction of the Grobner fan
    S := ring M;
    if isPolynomialRing S == false then error("The base ring is expected to be a polynomial ring"); 
    l := numgens(S);
    ---Turn M into an ideal                                                                    
    I := moduleToIdeal(M);
    R := ring I;
    -- We remove the multigrading so as to ease the computations
    R = newRing(R, Degrees =>splice({numgens R :{1}}) );
    I = sub(I, R);
    m := rank ambient M;
    k := numgens(R);
    G := gfan(I);
    --Turn into initial ideal                                                                    
    L := apply(G,i->gfanLeadingTerms(i));
    q := apply(L, monoIdeal-> (
	    ideal select(monoIdeal,j->(
		    t := (exponents(j))_0;		    
		    sum(k-l,i->t_(i+l))==1
	    ))
    ));
    --Combine initial ideals with the same e-linear part
    alreadyDone := {};
    coneToCombine:={};
    for i from 0 to #q-1 do
    (
  	if not isMember(i,alreadyDone) then (
     	tt := q_i;
     	alreadyDone = alreadyDone|positions(q,j->j==tt);
     	coneToCombine = coneToCombine|{positions(q,j->j==tt)};
        )
    );
    combinedCones := apply(coneToCombine,element-> (
      Now := apply(element, i-> (
      	      conei := gfanGroebnerCone(G_i);
               coneFromVData((-1)*rays conei, linealitySpace conei)
	      ));      
      c := first Now;
      for i from 1 to #Now-1 do(c = minkowskiSum(c,Now_i););
      c
    ));
    --Create fan
    F := fan first combinedCones;
    for i from 1 to #combinedCones-1 do (
   	F = addCone(combinedCones_i,F);
    );
    F
)


grobnerFan = method()
grobnerFan (Module, Fan, Ideal) := (M,F,I) ->(
    S := ring M;
    if isPolynomialRing S == false then error("The base ring is expected to be a polynomial ring");
    if  S =!= ring I then error("The module and the ideal need to be defined over the same ring");
    if dim F > numgens S + rank ambient M then error("The dimesion of the fan is not compatible with the module");
    new GrobnerFan from{
        symbol module => M,
        symbol ring => S,
        symbol fan => F,
        symbol ideal => I,
        symbol cache =>new CacheTable
    }
)

-- Consturction when the fan is provided
grobnerFan (Module, Fan) := (M, F) ->(
    S := ring M;
    grobnerFan (M,F, ideal(1_S))
)

grobnerFan (Module, Ideal) := (M, I) ->(
    S := ring M;
    grobnerFan (M,grobnerPolyhedralFan M, I)
)

-- General constructor for any module
grobnerFan Module := M ->( 
    GRF := grobnerFan (M, grobnerPolyhedralFan M);
    GRF   )

-- Constructor for a module over the Cox ring of a toric variety

grobnerFan ( NormalToricVariety, Module, Fan) := (X,M,F)->(
    if ring M =!= ring X then error("The module is not defined over the Cox ring of the toric variety");
    GRF := grobnerFan (M,F, ideal X);
    GRF.cache.variety = X;
    GRF
)

grobnerFan ( NormalToricVariety, Module) := (X,M)->(
    GRF:= grobnerFan (X, M, grobnerPolyhedralFan M);
    GRF
)

net GrobnerFan := GRF -> (
    if GRF.cache.?variety then(
    " Grobner fan of " | net GRF.module |
    "  with " | net GRF.ideal |  " on the toric variety " | toString GRF.cache.variety  
    )else(
    " Grobner fan of " | net GRF.module |
    "  with irrelevant " | net GRF.ideal  )
    )


-- Basic getter funtions

module GrobnerFan :=  GRF -> GRF.module
ring GrobnerFan :=  GRF -> GRF.ring
fan GrobnerFan := GRF -> GRF.fan
ideal GrobnerFan := GRF -> GRF.ideal
rays GrobnerFan := {} >> o -> GRF -> (rays GRF.fan)

variety GrobnerFan := GRF ->(
    if GRF.cache.?variety then( return GRF.cache.variety )
    else(print("The module is not a priori defined over a Cox ring"););
)




------------------------------------------------------------------------------------
-- FUNCTIONS AND METHODS
------------------------------------------------------------------------------------

--------------------------------------------------------
-- COMPUTATION OF INITIAL MODULES
--------------------------------------------------------


-- In order to compute the inital module we neeed a vector whose entries are all positive
-- so we may need to tranlate the given weight by a vector called correction vector.
-- The resulting vector will in the same cone as the starting one and is positive (as long as 
-- the grading is positive)

-- Gives a vector with positive entries that is in the lineality space of the Grobner fan of the module
correctionVector = method();

-- A is the matrix defining the lineality space of the Grobner fan
correctionVector Matrix :=  A ->(
	Q := intersect(coneFromVData(A|(-1*A)) , posOrthant rank target A) ;
	p := latticeInteriorPoint Q;
	if max(p) <= 0 then return {} else return p;
)

correctionVector Module := M ->(
      A := matrix degrees ring (moduleToIdeal M); -- This matrix is sufficient to find a correction vector, the linelity space may be bigger
      use ring M;
correctionVector(A)
)

correctionVector Fan := F -> correctionVector(linSpace F)

correctionVector GrobnerFan := GRF ->(
  if not GRF.cache.?correctvc then(GRF.cache.correctvc = correctionVector (fan GRF););
  GRF.cache.correctvc
)

--TODO consider a version that avoids considering the ideal associated to make it faster
--compute in_{w,s}(M)
-- The code can handle module that are homogenoeus with respect to a positively graded grading
initialModule = method(Options => {Correction =>{}, TimeSpent => 30});

initialModule (Module, List, List):= opts -> (M,w,s)->(
    n:=numgens ring M;
    I:=moduleToIdeal(M);
    degs := degrees ring I;
    SI:=ring I;
    m:=numgens SI - n;
    KI:=coefficientRing SI;
    gensSI := gens SI;
    newW := apply(w,i->-i) | apply(s,i->-i);
    maxWS:=max(w|s);
    vec := opts#Correction;
    if vec === {} then(
      vec = correctionVector(M) ; );
    newW = newW + (maxWS+1)*vec;
    -- degsS:=apply(n,i->({1,0})) | apply(m,i->({0,1})); -- I am changing this to try ease the computation
    newS := KI[gensSI,Weights=>newW,Degrees=>degs];
    newI:=sub(I,newS);
    inI := ideal (1_newS); 
    try(
    alarm max(30, opts#TimeSpent); -- max time that will be spent computing the lead terms in seconds
    inI = leadTerm(1,newI); 
    alarm 0; 
    ) then(
	linearGens:= select(flatten entries gens inI,f->((degree(f))_(-1) ==1));
    moduleGens:=apply(linearGens, g->(
	    C:=coefficients g;
	    apply(m,j->(
		    p:=positions(flatten entries (C_0), i->(first exponents( i))_(n+j)==1);
		    sum(p,l->(sub((flatten entries (C_0))_l,SI_(n+j)=>1)*(flatten entries (C_1))_l))
	    ))
    ));
    return image mingens image map(ambient M, , transpose sub(matrix moduleGens, ring M)))
    else(
	return image matrix{ {0_(ring M)}}); -- We output the zero module if it takes to long
    )



-------------------------------------------------------------------------
-- PROPERTIES CHECK
-------------------------------------------------------------------------

-- COMMUTATIVE ALGEBRA PROPERTIES 

-- Check whether the sheafification of the cokernel of A is a vector bundle on a toric variety
-- Input: A matrix A, list L of fitting ideals of A, and I the irrelevant ideal of the toric variety
-- There are two methods: one computes the radical and the other computes the saturation,
--the second one is more expensive but it works in some of the cases where the first one aborts.

isVectorBundle = method(Options => { Strategy => "radical"});

isVectorBundle (Module, Ideal, ZZ) :=  opts -> (M, I, r) ->(
    p:= false; 
    if opts#Strategy === "radical" then(
    p = (isSubset(I, radical fittingIdeal(r, M))) and (fittingIdeal(r-1, M)== ideal(0_(ring I) ));)
    else(
    p = (saturate( fittingIdeal(r, M)),I)== ideal(1_(ring I)) and (fittingIdeal(r-1, M)== ideal(0_(ring I) ));
    );
    return p;
)

isVectorBundle (Module, NormalToricVariety,ZZ) := opts -> (M, X, r) ->(
  isVectorBundle(M, ideal(X),r)
)

-- We code are not using the previous function because it would lead to redundant computations of fitting ideals
-- we return false or {true, r} where r is the rank of the vector bundle
isVectorBundle(Module, Ideal) := opts -> (M, I) ->(

    m:= rank ambient M;
    Im := fittingIdeal(-1, M);
    I1 := ideal(1_(ring I));
    I0 := ideal(0_(ring I));
    if opts#Strategy === "radical" then(
    for i from 0 to m+1 do(
        IM := fittingIdeal(i, M);
        if (Im == I0) then(
            if isSubset(I, radical IM) then(
                return i;
                exit;
            )
        );    
        Im = IM;  
    );
    return false;
    )
    else(
            for i from 0 to m+1 do(
        IM := fittingIdeal(i, M);
        if (Im == I0) then(
            if saturate(IM,I)== I1 then(
                return i;
                exit;
            )
        );    
        Im = IM;
    
    );
    return false;
    );
)
isVectorBundle (Module, NormalToricVariety) := opts -> (M, X) ->(
  isVectorBundle(M, ideal(X))
)


isTorsionFreeSheaf = method(Options => {Strategy => "radical"})
isTorsionFreeSheaf (Module, Ideal) := opts -> (M, I) ->(
    S:= ring M;
    if S =!= ring I then error("The module and the ideal have to be defined over the same ring");
    if M.cache.?DDual == false then(
    ddual := reflexify( M, ReturnMap => true);
    M.cache.DDual = ddual;);
    if opts#Strategy == "radical" then(
    isSubset(I, radical annihilator ker M.cache.DDual) 
    )else(
      saturate(annihilator ker M.cache.DDual,I)== ideal(1_S)
    )
)

isTorsionFreeSheaf (Module, NormalToricVariety) := opts -> (M, X) ->(
    if ring M =!= ring X then error("The module is not defined over the Cox ring of the toric variety");
    isTorsionFreeSheaf( M, ideal X, Strategy => opts#Strategy)
)



-- isReflexiveSheaf is a pre-existing method with options that we are overwriting
isReflexiveSheaf = method(Options => {Strategy => "radical"})
isReflexiveSheaf (Module, Ideal) := opts -> (M, I) ->(
    S:=ring M;
    if S =!= ring I then error("The module and the ideal have to be defined over the same ring");
    if opts#Strategy == "radical" then(
    return isTorsionFreeSheaf(M, I, Strategy => opts#Strategy) == true and isSubset(I, radical annihilator coker (M.cache.DDual));
    ) else(return isTorsionFreeSheaf(M, I, Strategy => opts#Strategy) == true and saturate( annihilator coker (M.cache.DDual),I)== ideal(1_S);
     );
)

isReflexiveSheaf (Module, NormalToricVariety) := opts ->  (M, X) ->(
    if ring M =!= ring X then error("The module is not defined over the Cox ring of the toric variety");
    isReflexiveSheaf( M , ideal X,  Strategy => opts#Strategy)
)


-- PROPERTIES OF THE FAN

--Decide whether in_{w,s}(M) is homogeneous with respect to the Z^n grading by deg(x_i)=e_i
--Input: cone sigma from the Grobner fan of M, given as a matrix of rays, n=number of gens
-- of ambient polynomial ring 
isEquivariant = method()
isEquivariant (Matrix, ZZ) := (sigma,n) ->(
    nset:=apply(n,i->i);
    dimsigma:=rank sigma^nset;
    if dimsigma==n then true else false
)
isEquivariant (Cone, ZZ) := (C,n) ->(
    L := linealitySpace C;
    A:= rays C| L| -1*L;
    isEquivariant(A,n)
)


--------------------------------------------------------------------------
-- FUNCTIONS TO GENERATE EXAMPLES
--------------------------------------------------------------------------


-- Input: S is the Cox ring of a toric variety and gives a matrix with l rows of homogeneous entries of multidegree d in oplus S(-shifts_i) for i=1,...,m, 
-- where shifts is a list of m elements, and returns the image of the corresponding map from oplus S(-shifts_i) to oplus S(-d)

generateHomogeneousModule  = method(Options => {Random => 0});
-*
generateHomogeneousModule ( Ring, List, ZZ, List) := opts ->(S,shifts, l, d) -> (
    M :={};
    sh := -shifts;
    D :=splice{l:-d};
    if opts#Random == 0 then(
        for i from 0 to #sh-1 do(
        M = M|{for j from 0 to l-1 list sum randomSubset(terms random(d + sh_i,S))};
    );)
    else(
        for i from 0 to #sh-1 do(
        M = M|{for j from 0 to l-1 list sum randomSubset(terms random(d + sh_i,S),opts#Random)};
    )
    );
    if opts#Mode === "matrix" then( return matrix M);
    M= map(S^sh, S^D, matrix M);
    if opts#Mode === "image" then(M= image M ;);
    if opts#Mode === "coker" then(M= coker M ;);
    return M
);

generateHomogeneousModule( Matrix, List) := opts ->(M, d) -> (
    S := ring M;
    l := numgens source M;
    D :=splice{l:-d};
    aux :=apply(entries M, m -> select(m, i -> i != 0 ));
    sh := apply(aux, m -> if m != {} then degree m_0 - d else d);
    M = map(S^sh, S^D, M);
    if isHomogeneous M == false then error "The input matrix is not homogeneous";
    if opts#Mode === "image" then(M= image M ;);
    if opts#Mode === "coker" then(M= coker M ;);
    return M
);
*-
-- We give the ring and the shifts in the target and source to then construct a homogeneous map between them
generateHomogeneousModule ( Ring, List, List) := opts ->(S,target, source) -> (
    M :={};
    s := # source;
    t := # target; 
    if opts#Random == 0 then(
        for j from 0 to t-1 do(
        M = M|{for i from 0 to s-1 list sum randomSubset(terms random(-target_j + source_i,S))};
    );
    )else( 
        for j from 0 to t-1 do(
        M = M|{for i from 0 to s-1 list sum randomSubset(terms random(-target_j + source_i,S), opts#Random)}
    ));
    map(S^(-target), S^(- source), matrix M)
);




-- This fan can sometimes coincide with the Grobner fan of the module,
-- Its purpose is to give a quick approximation of the Grobner fan if grobnerFan takes too long
fakeFan= (M) ->(
    use ring(M);
    lg := flatten entries gens moduleToIdeal M;
    p := newtonPolytope(lg_0);
    for i from 1 to (length lg -1) do(
        p = p + newtonPolytope(lg_i);
        );
    return  normalFan(p);
    )

--------------------------------------------------------------------------------
-- OBTAINING THE DEGENERATIONS IN THE GROBNER FAN
--------------------------------------------------------------------------------



-- Compute the lattice point in the interior of a cone given by its rays,
-- the coordinates are integers
latticeInteriorPoint = method ()
latticeInteriorPoint Cone := (P) ->(
    rp:= rays P;
    l:= entries transpose rp;
    n:=length l;
    C:= toList (rank target rp:0);
    for i from 0 to n-1 do(C=C+l_i);--);
    C= apply(C,c-> truncate (c));-- the solution I found to turn integers in QQ into ZZ
    return C;
)
-*
latticeInteriorPoint Polyhedron := (P) ->(
    rp:= rays P;
    l:= entries transpose rp;
    n:=length l;
    C:= toList (rank target rp:0);
    for i from 0 to n-1 do(C=C+l_i);--);
    C= apply(C,c-> truncate (c));-- the solution I found to turn integers in QQ into ZZ
    return C;
)
*-


infoInitialModules = method(Options => {Strategy => "radical", TimeSpent => 30, Correction => {}});

infoInitialModules (GrobnerFan, List) := opts -> (GRF, conesList) ->(
  if not GRF.cache.?infoDegens then(  
    M := module GRF;
    if isHomogeneous M == false then error "The module is not homogeneous";
    F := fan GRF;
    I := ideal GRF;
    n := numgens(ring M);
    m := rank (ambient M);
    rs:= rays F;
    linsF := linealitySpace F;
    correctv := {};
    if opts#Correction == {} then(
    correctv = correctionVector(GRF);)
    else(correctionVector =opts#Correction; );
    r := isVectorBundle(coker gens M, I, Strategy => opts#Strategy);
    -- Mutable hash table where the information about the degenerations will be stored
    
    data := new HashTable from apply(conesList, c -> (
      rsc:= rs_c;
      cconeSpan := rsc|(linsF |(-1)*linsF);
      cconeDim := dim coneFromVData(cconeSpan) ; 
      cintPoint := latticeInteriorPoint( coneFromVData(cconeSpan));
      cequivariant := isEquivariant(cconeSpan,n);
      cdegeneration := coker gens initialModule(M, take(cintPoint,{0,n-1}), take(cintPoint,{n,n+m-1}), Correction => correctv, TimeSpent => opts#TimeSpent);
      ctorsionFreeSheaf := isTorsionFreeSheaf (cdegeneration,I , Strategy => opts#Strategy);
      creflexiveSheaf := isReflexiveSheaf (cdegeneration, I, Strategy => opts#Strategy);
      cvectorBundle := false; 
      
      if instance(r,ZZ) then( 
          cvectorBundle = isVectorBundle(cdegeneration ,I, r, Strategy => opts#Strategy ); 
      )else(cvectorBundle = false;);
        
        
      
      c => new HashTable from {conerays => rsc, coneSpan => cconeSpan, coneDim =>cconeDim , intPoint => cintPoint, equivariant => cequivariant, degeneration => cdegeneration, torsionFreeSheaf => ctorsionFreeSheaf, reflexiveSheaf => creflexiveSheaf, vectorBundle => cvectorBundle })
    );
    GRF.cache.infoDegens = data;
    msgNet := net("A total of "|toString(#conesList)|" initial modules have been computed");
    border := net concatenate toList((width msgNet + 4):"-");
    messageNet := stack(border, horizontalJoin("| ", msgNet, " |"), border);
    << endl << messageNet << endl << endl;
    GRF.cache.infoDegens;
    );
)

infoInitialModules GrobnerFan := opts -> GRF ->(
    F:= fan GRF;
    linsF := linealitySpace F;
    if not GRF.cache.?allCones then(GRF.cache.allCones = flatten( for i from dim(source linsF) to dim(F) list cones(i,F)););
    infoInitialModules (GRF, GRF.cache.allCones, opts)
)

isToricVectorBundle = method();
isToricVectorBundle (GrobnerFan, List) := (GRF,c) ->(
    if not GRF.cache.?infoDegens then (infoInitialModules GRF;);
  degens :=  GRF.cache.infoDegens ;
  if not isMember(c, keys degens ) then error("Give a cone of the Grobner fan" );
  degens#c#vectorBundle and degens#c#equivariant
) 

isVectorBundle (GrobnerFan, List) := opts -> (GRF,c) ->(
  if not GRF.cache.?infoDegens then (infoInitialModules GRF;);
  degens :=  GRF.cache.infoDegens ;
  if not isMember(c, keys degens ) then error("Give a cone of the Grobner fan" );
  degens#c#vectorBundle
)

isTorsionFreeSheaf (GrobnerFan, List) := opts ->  (GRF,c) -> (
if not GRF.cache.?infoDegens then (infoInitialModules GRF;);
  degens :=  GRF.cache.infoDegens ;
  if not isMember(c, keys degens ) then error("Give a cone of the Grobner fan" );
 degens#c#torsionFreeSheaf  
)

isReflexiveSheaf (GrobnerFan, List) := opts ->  (GRF,c) -> (
if not GRF.cache.?infoDegens then (infoInitialModules GRF;);
  degens :=  GRF.cache.infoDegens ;
  if not isMember(c, keys degens ) then error("Give a cone of the Grobner fan" );
  degens#c#reflexiveSheaf
)

degenerateModule = method()
degenerateModule (GrobnerFan, List) :=  (GRF, c) ->(
  answ:= {};
  if GRF.cache.?infoDegens then(
  degens :=  GRF.cache.infoDegens ;
  if isMember(c, keys degens ) then(
  return degens#c#degeneration;););
    M := module GRF;
    n := numgens(ring M);
    m := rank (ambient M);
    F:= fan GRF;
    rs:= rays F;
    linsF := linealitySpace F;
      rsc:= rs_c;
      cconeSpan := rsc|(linsF |(-1)*linsF);
      correctv := correctionVector(GRF);
      cintPoint := latticeInteriorPoint( coneFromVData(cconeSpan));
      return coker gens initialModule(M, take(cintPoint,{0,n-1}), take(cintPoint,{n,n+m-1}), Correction => correctv, TimeSpent => 3000000);


)
rays (GrobnerFan, List) := {} >> o -> (GRF, c) ->(
    if not GRF.cache.?infoDegens then (infoInitialModules GRF;);
  degens :=  GRF.cache.infoDegens ;
  if not isMember(c, keys degens ) then error("Give a cone of the Grobner fan" );
  degens#c#conerays
)

cone (GrobnerFan, List):= {} >> o -> (GRF,c) ->(
    if not GRF.cache.?infoDegens then (infoInitialModules GRF;);
  degens :=  GRF.cache.infoDegens ;
  if not isMember(c, keys degens ) then error("Give a cone of the Grobner fan" );
  coneFromVData degens#c#coneSpan
)


dim (GrobnerFan, List) := (GRF, c) ->(
    if not GRF.cache.?infoDegens then (infoInitialModules GRF;);
  degens :=  GRF.cache.infoDegens ;
  if not isMember(c, keys degens ) then error("Give a cone of the Grobner fan" );
  degens#c#coneDim
)
isEquivariant (GrobnerFan, List) := (GRF, c) ->(
if not GRF.cache.?infoDegens then (infoInitialModules GRF;);
  degens :=  GRF.cache.infoDegens ;
  if not isMember(c, keys degens ) then error("Give a cone of the Grobner fan" );
  degens#c#equivariant
)

latticeInteriorPoint (GrobnerFan, List) := (GRF, c) -> (
    if not GRF.cache.?infoDegens then (infoInitialModules GRF;);
  degens :=  GRF.cache.infoDegens ;
  if not isMember(c, keys degens ) then error("Give a cone of the Grobner fan" );
  degens#c#intPoint)

--------------------------------------------------------------------
-- ANALYSIS OF THE RESULTS OBTAINED
--------------------------------------------------------------------

-- Takes the output of infoInitialModules and gives a summary of the properties of the degenerations selecting the modules with each property
analyzeDegenerations = method()
analyzeDegenerations GrobnerFan := (GRF)->(
  if GRF.cache.?analyzeDegens then( return GRF.cache.analyzeDegens;);
    A := new MutableHashTable;
    -- In order to use select we need a HashTable...
    if not GRF.cache.?infoDegens then (infoInitialModules GRF;);
  degens :=  GRF.cache.infoDegens ;
    ks := keys degens;
    -- Lists all the modules that appear as degenerations
    AmodulesList := apply(ks, c -> degens#c#degeneration);
    -- Select the cones satisfying a particular condition

    AvectorBundle := select( ks, p -> degens#p#vectorBundle == true);
    
    AtorsionFreeSheaf := select( ks, p -> degens#p#torsionFreeSheaf == true);
    AreflexiveSheaf := select( ks, p -> degens#p#reflexiveSheaf == true);
    AtoricVB := select( ks, p -> degens#p#equivariant == true and degens#p#vectorBundle == true );
    Aequivariant := select( ks, p -> degens#p#equivariant == true);
    tot:= # AmodulesList;
  
    byDimension := (LL)->(tally (apply(LL, p -> degens#p#coneDim) ) );

    AsummaryStats :=  new HashTable from { modulesList =>{tot, byDimension(ks )}, vectorBundle => { # AvectorBundle, byDimension(AvectorBundle)}, reflexiveSheaf => {# AreflexiveSheaf, byDimension(AreflexiveSheaf) }, torsionFreeSheaf =>{# AtorsionFreeSheaf, byDimension(AtorsionFreeSheaf)}, equivariant =>{# Aequivariant,  byDimension(Aequivariant)}, toricVB=>{# AtoricVB, byDimension(AtoricVB)}};
    
    GRF.cache.noDuplicates = # unique ( AmodulesList) == tot;
    GRF.cache.analyzeDegens = new HashTable from {modulesList => AmodulesList, vectorBundle => AvectorBundle , equivariant => Aequivariant, reflexiveSheaf => AreflexiveSheaf, torsionFreeSheaf => AtorsionFreeSheaf, toricVB => AtoricVB, summaryStats => AsummaryStats};
    msgNet := net("The degenerations of "|net coker gens GRF.module|" have been analyzed");
    border := net concatenate toList((width msgNet + 4):"-");
    messageNet := stack(border, horizontalJoin("| ", msgNet, " |"), border);
    << endl << messageNet << endl << endl;
    return GRF.cache.analyzeDegens;
)

-- Given a cones and returns its hash table
recoverInformation = method()
recoverInformation (GrobnerFan, List) := (GRF, L) -> (
    if not GRF.cache.?infoDegens then (infoInitialModules GRF;);
  degens :=  GRF.cache.infoDegens ;
  if not isMember( L,keys degens) then error("The cone is not in the GrobnerFan" );
  degens#L
)

hasDuplicates = GRF -> (  if not GRF.cache.?noDuplicates then(
    analyzeDegenerations GRF;
  );
  not GRF.cache.noDuplicates )


isToricVectorBundle GrobnerFan :=  GRF -> (
  data := analyzeDegenerations(GRF);
  data.toricVB
)
 
isVectorBundle GrobnerFan := opts -> GRF -> (
  data := analyzeDegenerations(GRF);
  data.vectorBundle
)

isTorsionFreeSheaf GrobnerFan := opts ->  GRF -> (
  data := analyzeDegenerations(GRF);
  data.torsionFreeSheaf
)  

isReflexiveSheaf GrobnerFan := opts ->  GRF ->(
  data := analyzeDegenerations(GRF);
  data.reflexiveSheaf
)

degenerateModule GrobnerFan := GRF ->(
  data := analyzeDegenerations(GRF);
  data.modulesList
)

isEquivariant GrobnerFan := GRF -> (
  data := analyzeDegenerations(GRF);
  data.equivariant
)

listCones = GRF ->( 
  F := fan GRF;
  linsF := linealitySpace F;
  if not GRF.cache.?allCones then(GRF.cache.allCones = flatten( for i from dim(source linsF) to dim(F) list cones(i,F)););
  GRF.cache.allCones)


-- This gives the subfan of F given by the modules in LAM
-- It assumes that the input is LAM is a list of hash tables with keys coneId and cone
-- and that said list yields a subfan.
specialSubfan = method(Options => {Strategy => "VectorBundle"})
-*
specialSubfan (Fan, List) := (F, LH)->(
    lin := linealitySpace F;
    G := fan( apply(keys LAM, p -> coneFromVData( LAM#p#conerays | lin |(-1)*lin))); 
    return G;
)
*-

specialSubfan GrobnerFan := opts -> GRF ->(
    GRFnew := grobnerFan( module GRF, fan GRF, ideal GRF);
    if GRF.cache.?variety then( 
      GRFnew.cache.variety =  GRF.cache.variety;
    );
    if not GRF.cache.?infoDegens then (infoInitialModules GRF;);
    degens :=  GRF.cache.infoDegens ;
    if opts#Strategy == "NonEquivariant" then(
    GRFnew.cache.infoDegens = selectKeys( degens , p ->  degens#p#equivariant == false  );
    )else(GRFnew.cache.infoDegens =selectKeys( degens , p ->degens#p#vectorBundle == true ); );
    GRFnew


)

specialSubfan (GrobnerFan, List) := opts ->(GRF, L)-> (

    lin := linealitySpace fan GRF; 
    rs := rays fan GRF;
    fan( apply(L, p -> coneFromVData( rs_p | lin |(-1)*lin))) 

)    


equivariantCones = method()
equivariantCones (Fan, ZZ) := (F,n) ->(
  linsF := linealitySpace F;
  rs := rays F;
  conesList :=flatten( for i from dim(source linsF) to dim(F) list cones(i,F));
  select(conesList, c ->  isEquivariant((rs_c|(linsF |(-1)*linsF)),n))
)
equivariantCones GrobnerFan := GRF ->( 
if not GRF.cache.?equivCones then(GRF.cache.equivCones = equivariantCones(fan GRF, numgens(ring module GRF)););
GRF.cache.equivCones
)

---------------------------------------------------------------------------------
-- RECOVER THE FINE GRADING
---------------------------------------------------------------------------------
fineGrading = method()


fineGrading (Matrix) := (A) ->(
  S := ring A;
  n := numgens S;
  if  all( flatten entries A , p -> # terms p <= 1) != true then( error("The presentation matrix is not equivariant"););

  -- Source degrees
  p := numColumns (A);
  MS := new MutableHashTable from apply(p , j -> {j,{}});
  -- target degrees
  q := numRows (A);
  NS := new MutableHashTable from apply(q , i -> {i,{}});
  aux := apply(entries A, i -> apply( i, j -> exponents j));
  jnew := 0;
  inew := 0; 
  MS#0 = toList(n:0);
-- Track lists of degrees instead of cloning the MutableHashTables
  oldMS := apply(p, j -> MS#j);
  oldNS := apply(q, i -> NS#i);
  currentMS :={};
  currentNS :={};

  while isMember({}, values MS) or isMember({}, values NS) do(
      if oldMS == currentMS and oldNS == currentNS then(
          jnew = min apply(p, j -> if MS#j == {} then( j)else( infinity) );
          if jnew != infinity then( MS#jnew= toList(n:0); )else(
          inew = min apply(q, i -> if NS#i == {} then( i)else( infinity) );
          if inew != infinity then( NS#inew= toList(n:0); );
          );
          
      );

      oldMS = apply(p, j -> MS#j);
      oldNS = apply(q, i -> NS#i);

      for j from 0 to p-1 do(
          for i from 0 to q-1 do(
              if (aux_i)_j != {} then(
                  if NS#i !={} and MS#j == {}  then(MS#j = flatten (aux_i)_j + NS#i );
                  if MS#j !={} and NS#i == {} then(NS#i = - flatten (aux_i)_j + MS#j);
              );
          );
      );
      
      currentMS = apply(p, j -> MS#j);
      currentNS = apply(q, i -> NS#i);

  ); 
  sdegs := - apply(p , j -> MS#j );
  tdegs := - apply(q , i -> NS#i );
  R := newRing( S, Degrees => entries id_(ZZ^(n)));
  phi:= map(R^tdegs,R^sdegs,sub(A, R) );
  if not isHomogeneous phi then (print("The module is not homogeneous with respect to the fine-grading" ););
  phi
) 


-*
fineGrading (Module) := M ->(

  A := presentation M;
  S := ring M;
  n := numgens S;
  if  all( flatten entries A , p -> # terms p <= 1) != true then( error("The presentation matrix is not equivariant"););

  -- Source degrees
  p := numColumns (A);
  MS := new MutableHashTable from apply(p , j -> {j,{}});
  -- target degrees
  q := numRows (A);
  NS := new MutableHashTable from apply(q , i -> {i,{}});
  aux := apply(entries A, i -> apply( i, j -> exponents j));
  jnew := 0;
  inew := 0; 
  MS#0 = toList(n:0);
-- Track lists of degrees instead of cloning the MutableHashTables
  oldMS := apply(p, j -> MS#j);
  oldNS := apply(q, i -> NS#i);
  currentMS :={};
  currentNS :={};

  while isMember({}, values MS) or isMember({}, values NS) do(
      if oldMS == currentMS and oldNS == currentNS then(
          jnew = min apply(p, j -> if MS#j == {} then( j)else( infinity) );
          if jnew != infinity then( MS#jnew= toList(n:0); )else(
          inew = min apply(q, i -> if NS#i == {} then( i)else( infinity) );
          if inew != infinity then( NS#inew= toList(n:0); );
          );
          
      );

      oldMS = apply(p, j -> MS#j);
      oldNS = apply(q, i -> NS#i);

      for j from 0 to p-1 do(
          for i from 0 to q-1 do(
              if (aux_i)_j != {} then(
                  if NS#i !={} and MS#j == {}  then(MS#j = flatten (aux_i)_j + NS#i );
                  if MS#j !={} and NS#i == {} then(NS#i = - flatten (aux_i)_j + MS#j);
              );
          );
      );
      
      currentMS = apply(p, j -> MS#j);
      currentNS = apply(q, i -> NS#i);

  ); 
  sdegs := - apply(p , j -> MS#j );
  tdegs := - apply(q , i -> NS#i );
  R := newRing( S, Degrees => entries id_(ZZ^(n)));
  phi:= map(R^tdegs,R^sdegs,sub(A, R) );
  if not isHomogeneous phi then (print("The module is not homogeneous with respect to the fine-grading" ););
  coker phi
) 
*-
fineGrading Module := M -> fineGrading(presentation M)
fineGrading (GrobnerFan, List) := (GRF, C) ->fineGrading( degenerateModule(GRF, C))

---------------------------------------------------------------------------------
-- SAVING FUNCTIONS
---------------------------------------------------------------------------------


-- Function to save the output of infoInitialModules or the GrobnerFan in a file with descpition text 
-- NOTE: name should be "name.m2" for a m2 file as "name" just gives a .txt file

fanToString = F ->(
    c:=concatenate{"F = fan (",toExternalString (rays F) ,",", toExternalString (linealitySpace F) ,",", toExternalString(maxCones F), ");"};
    return c;
)


saveDegeneration = method();

saveDegeneration (GrobnerFan, String, String) := (GRF, text, name)->(
    pre:=concatenate{"-- ", text, "\n ", fanToString( fan GRF)};
    if GRF.cache.?variety then(
    pre = concatenate{pre,"\n X=", toExternalString variety GRF,"\n S= ring X"  , "\n Q=",  toString module GRF , "\n GRF = grobnerFan(X,Q,F) \n" }
    )
    else(
      pre = concatenate{pre,"\n S=" toExternalString ring GRF,  "\n I=",  toString ideal GRF, "\n Q=",  toString module GRF , "\n GRF = grobnerFan(Q,F,I) \n" }
      );
    if GRF.cache.?infoDegens then(
      pre = concatenate{ pre, "\n use S; \n GRF.cache.infoDegens = " ,toString GRF.cache.infoDegens }
    );
    if GRF.cache.?noDuplicates then(
      pre = concatenate{ pre, "\n GRF.cache.noDuplicates = " , toString GRF.cache.noDuplicates}
    );
    if GRF.cache.?analyzeDegens then(
      pre = concatenate{ pre, "\n use S; \n GRF.cache.analyzeDegens = ", toString GRF.cache.analyzeDegens }
    );
    name << pre <<close

)

saveDegeneration(Fan, String, String) := (F,text, name)->(
    pre:=concatenate{"-- ", text, "\n "};
    s:= " ";
    s= concatenate{pre, fanToString F};
    name << s <<close
)


-------------------------------------------------------------
-- Display information
-------------------------------------------------------------


displayInformation = method()
displayInformation GrobnerFan := GRF -> (
  D := analyzeDegenerations GRF;
  H := D#summaryStats;
  dims := sort toList set flatten apply(values H, v -> keys(v#1));

    -- Column widths
    propWidth := max apply(prepend("Property", apply(keys H, toString)),length );

    totalWidth := max apply(prepend("Total \\ Dim ", apply(keys H, c -> toString (H#c)_0)),length);

    dimWidths := apply(dims, d ->
        max(length toString d,
            max(1, max apply(values H, v ->
                if (v#1)#?d then length toString((v#1)#d) else 0)))
    );

    -- Helper to pad on the right
    padd := (s,w) -> (
        s = toString s;
        s | concatenate apply(w-length s, i -> " ")
    );

    -- Horizontal line
    rule :=
        "+"
        | concatenate apply({propWidth,totalWidth}|dimWidths,
            w -> concatenate apply(w+2, i -> "-") | "+"
        );

    lines := {};

    -- Header
    header :=
        "| " | padd("Property",propWidth)
        | " | " | padd("Total \\ Dim ",totalWidth);

    scan(#dims, i ->
        header = header | " | " | padd(dims#i, dimWidths#i)
    );

    header = header | " |";

    lines = append(lines, rule);
    lines = append(lines, header);
    lines = append(lines, rule);

    -- Rows
    scan({modulesList, torsionFreeSheaf, reflexiveSheaf, vectorBundle,toricVB, equivariant }, k -> (
        v := H#k;
        total := v#0;
        tally := v#1;

        line :=
            "| " | padd(k,propWidth)
            | " | " | padd(total,totalWidth);

        scan(#dims, i -> (
            d := dims#i;
            entry :=
                if total == 0 then ""
                else if tally#?d then tally#d
                else "";
            line = line | " | " | padd(entry, dimWidths#i);
        ));

        line = line | " |";
        lines = append(lines,line);
    ));

    lines = append(lines,rule);

    stack apply(lines, net)
)


    
-* Documentation section *-
beginDocumentation() 


doc ///
  Key
    VectorBundleDegenerations
  Headline
    Groebner degenerations of a module and their vector bundle properties
  Description
    Text
      Given a submodule $Q$ of a free module $F=\bigopus_{i=1}^m S e_i$ over
      a (multigraded) polynomial ring $S = K[x_1,...,x_n]$, this
      package computes the Groebner fan of $Q$, denoted as $\Sigma(Q)$: the fan whose cones correspond
      to the distinct initial modules $\mathrm{in}_{(w,s)}(Q)$ with respect to a weight
       $(w,s)\in \mathbb{R}^n\times \mathbb{R}^m$.
      
      When the module $Q$ is defined over the Cox ring of a (smooth) toric variety $X$,
      each cone $\sigma \in \Sigma(Q)$ corresponds to a degeneration of the coherent sheaf associated to
      $F/Q$, namely, the degeneration is the coherent sheaf associated to $F/\mathrm{in}_{(w,s)}(Q)$
      with $(w,s)$ a point in the relative interior of the cone $\sigma$.

      For each cone of the fan the package can compute the corresponding initial
      module (the "degeneration" of $Q$ along that cone) and tests whether the associated
      sheaf on the toric variety $X$ is a vector bundle, a reflexive sheaf, or a torsion-free
      sheaf, and whether it is necessarily an equivariant with respect to the torus action.  
      This makes it possible to study, for instance, how a vector bundle degenerates and
      possibly find an equivariant vector bundle as a degeneration associated to a cone in the Groebner fan.

      The main type is @TO GrobnerFan@, which packages a module $Q$, the ring it
      lives over, the Grobner fan attached to $Q$ as a polyhedral fan, and the
      toric variety and irrelevant ideal used to test the sheaf-theoretic
      properties. Once a @TO GrobnerFan@ object is built, the study of the degenerations 
      is made with @TO infoInitialModules@ and a summary of the properties is displayed with @TO displayInformation@.
      A saving function, @TO saveDegeneration@, is included as
      some of the computations can be expensive.

      See the tutorial @TO "VectorBundleDegenerations tutorial"@ for a complete worked example and
      "Theoretical background: Grobner fan of a module" for a complete summary of the results used 
      to develop the package.

       
  Acknowledgement
  Contributors
      This is code started to be written during the 2025 ICMS workshop and completed
      by Mayo Mayo Garcia.
  References
      @UL { 
                {"David A. Cox, John B. Little, Hal Schenck, ",
	            HREF("https://dacox.people.amherst.edu/toric.html", 
			EM "Toric varieties"), ", Graduate Studies in
		    Mathematics 124. American Mathematical Society,
		    Providence RI, 2011.  ISBN: 978-0-8218-4817-7"}
      }@
  Caveat
  SeeAlso
  Subnodes
    "VectorBundleDegenerations tutorial"
    "Theoretical background: Grobner fan of a module"
///


doc ///
  Key
    "VectorBundleDegenerations tutorial"
  Headline
    a complete worked example using VectorBundleDegenerations
  Description
    Text
      This tutorial walks through the capabilities of the package on a
      single toy example: build a module over the Cox ring of a smooth toric variety,
      compute its Groebner fan and compute the degenerations at every cone.   
    Text
      @HEADER4 "Step 1: Set up a polynomial ring and a submodule $Q$ of a free module"@
    Example
      X = hirzebruchSurface 2;
      S = ring X
      degrees S
      I = ideal X
      Q = image(map(S^{2:{0, 0}, {-6, -1},{-4,-1}},S^{{-4, -2}}, matrix {{(4/9)*x_0^8*x_1^2+(2/7)*x_0^4*x_3^2+7*x_2^4*x_3^2},{(10/3)*x_0*x_1*x_2^5*x_3+x_0^3*x_2*x_3^2+(3/4)*x_0^2*x_2^2*x_3^2}, {(2/5)*x_1},{- x_3}}))
      
    Text
      @HEADER4 "Step 2: Compute the Groebner fan of $Q$"@
    Text  
      The function @TO grobnerFan@ creates an object of @TO GrobnerFan@ that contains the module, the
      ring, and the fan (computed using @TO grobnerPolyhedralFan@). This object will store more information after applying certain functions in the next steps.
    Example
      GRF = grobnerFan(X,Q)
    Text
      To recover the information initially stored in the type @TO GrobnerFan@ use the following
    Example
      fan GRF
      rays GRF 
      module GRF 
      ring GRF 
      ideal GRF
      variety GRF
    Text
      @HEADER4 "Step 3: Compute the initial modules at every cone of the fan"@
    Text
      In this case, as the module is defined over a toric variety
      @TO infoInitialModules@ computes if they are a vector bundle, a reflexive sheaf, or a torsion-free sheaf.
      This function automatically computes a @TO correctionVector@ using the lineality space of the fan 
      as in order to use compute an initial module we need a point in the cone such that all the entries are 
      positive. The initial modules computed and the information associated to them is stored in the @TO GrobnerFan@
      (see  @TO initialModule@ for more details). 
    Example
       infoInitialModules(GRF);
    Text
      One can now ask for the information of a particular degeneration using 
      @TO degenerateModule@, @TO isTorsionFreeSheaf@, @TO isReflexiveSheaf@,
      @TO isVectorBundle@, @TO isToricVectorBundle@ and  @TO isEquivariant@.
      In this case we want to recover the information for a cone in the fan.
      The list of all the cones can be obtained using @TO listCones@.
    Example
      isMember({0,2}, listCones GRF)
      degenerateModule(GRF, {0,2})
      isTorsionFreeSheaf(GRF, {0,2})
      isReflexiveSheaf(GRF,{0,2})
      isVectorBundle (GRF, {0,2})
      isToricVectorBundle (GRF, {0,2})
      isEquivariant (GRF, {0,2})
    Text
      The point used for computing the degeneration and the cone can also be recovered
      using @TO latticeInteriorPoint@.
    Example
      latticeInteriorPoint(GRF, {0,2})
      cv = correctionVector(GRF)
      initialModule(Q ,{0,0,1,0},{0,-1,1,0}, Correction => cv  )
    Text
      @HEADER4 "Step 4: Aggregate the per-cone information"@
    Text 
      Obtain a table with the information of how many cones give a vector
      bundle, which give a reflexive sheaf, and so on, together with a count
      by cone dimension. 
    Example
      displayInformation GRF
    Text
      It is also possible to recover the lists of cones that satisfy a particular condition. This lists consist of list of intengers corresponding to the rays spanning the cone, considered with the ordering in @TO "Polyhedra::Fan"@.
    Example
      isTorsionFreeSheaf GRF 
      isReflexiveSheaf GRF 
      isVectorBundle GRF
      TVBList = isToricVectorBundle GRF
      isEquivariant GRF
    Text
      Those lists can be used to recover the particular modules easily or recover the complete
      list with all the initial modules that have been computed.
    Example 
      apply(TVBList, C -> degenerateModule( GRF, C) )
    Text
      Alternatively, the list of all the initial modules that have been computed can be recovered as follows:
    Example
      allMods = degenerateModule GRF;
      # allMods
      allMods_42
    Text
      @HEADER4 "Step 5: save the computation"@
    Text 
      The function @TO saveDegeneration@ stores the GrobnerFan with all the cached information (which in this case
      includes all the degenerations, lists of cones satisfying the properties studied) 
      to afile, so it can be reloaded later without having to remake the computations.

      Note that the computation of the @TO grobnerPolyhedralFan@ alone can be expensive, so it can 
      also be saved separately as a string using @TO fanToString@.
    Example
      fanToString (fan GRF)
      saveDegeneration(GRF, "toy example from tutorial", "tutorialExample.m2")
    Text
      @HEADER3 "Other functionalities"@
    Text
      Some of the computation in this package can be expensive, so there are several possible strategies
      that can be taken to mitigate this problem that can help finding particular examples.       
    Text 
      @HEADER4 "Find a subset of the degenerations"@
    Text
      The function @TO infoInitialModules@ allows the possibility of computing the degenerations
      for a subset of the cones instead of all the Grobner fan. Once the function @TO infoInitialModules@ is run on a Grobner fan, the stored information is immutable,
      so it is needed to create a new copy of the GrobnerFan in order to analyze a different set of cones. 
      
      The information displayed will correspond with the list of cones that has been analyzed.

    Example
      GRF'= grobnerFan( X, Q , fan GRF);
      infoInitialModules( GRF', isReflexiveSheaf GRF)
      displayInformation GRF'
    Text 
      @HEADER4 "Focus on equivariant cones"@
    Text
      The function @TO equivariantCones@ returns a list of cones in the Grobner fan for which
      it is guaranteed that the associated sheaf is equivariant as the module can be fine-graded. 
      Moreover, the fine-grading of such modules can be recovered using @TO fineGrading@.

    Example
      GRFeq = grobnerFan(X,Q, fan GRF)
      Leq = equivariantCones GRF;
      infoInitialModules GRFeq
      isToricVectorBundle GRFeq
    Text
      The modules associated to cones for which @TO isEquivariant@ returns true can be fine graded 
      and the method @TO fineGrading@ gives one such grading
    Example
      Qfg = fineGrading ( degenerateModule (GRFeq, {3,6,7}))
      degrees ring Qfg
      isHomogeneous(Qfg)
    Text
      It is also possible to look into the @TO specialSubfan@ of non-equivariant cones as follows:
    Example
      GRFneq = specialSubfan(GRF, Strategy=>"NonEquivariant");
      displayInformation GRFneq

    Text 
      @HEADER4 "Find distinguished subfan of a Grobner fan"@
    Text  
      There are distinguished subfans that can be considered in the Grobner fan (see @TO "Theoretical background: Grobner fan of a module"@) whose structure one may 
      wish to study separately. Here we present the vector bundle subfan of our running example. The method @TO specialSubfan@ returns the vector bundle subfan when 
      applied to a grobner fan and changing the mode it gives the subfan of non-equivariant modules as above.
    Example
      GRFvb = specialSubfan( GRF)
      displayInformation GRFvb
    Text
      It is also possible to find other subfans in a Grobner fan. Given a GrobnerFan and a list of cones it returns the minimal subfan containing those cones.
    Example
      Ftvb = specialSubfan( GRF, isToricVectorBundle( GRF) )
      maxCones Ftvb
      (dim fan GRF) - dim Ftvb
      isPure Ftvb

    Text
      @HEADER4 "Use any fan as Grobner fan"@
    Text
      If the computation of @TO grobnerPolyhedralFan@ takes too long, @TO fakeFan@ can be use to take a fan constructed in a faster way from the generators of the module,
      that can sometimes coincide with the actual Grobner fan. The next example takes the previous fan that contains all the toric vector bundles in the running example.
      The function @TO hasDuplicates@ returns false in this case, which means that no two cones have been associated the same module.
    Example
      GRFtvb = grobnerFan( X, Q, Ftvb)
      displayInformation GRFtvb
      hasDuplicates GRFtvb
    Text
      In this case, the @TO fakeFan@ coincides with the actual @TO grobnerPolyhedralFan@ of the module.
    Example
      fakeFan(Q) == fan GRF 
  Caveat
      The condition of being equivariant is only a necessary condition (see @TO "Theoretical background: Grobner fan of a module"@). That is, if a cone is registered as
      not equivariant, what it means is that the module is not fine-graded, but it can happen that the associated 
      sheaf is equivariant (see @TO isEquivariant@ for more details).
 
  SeeAlso
    "Theoretical background: Grobner fan of a module"
    GrobnerFan
    grobnerFan
    infoInitialModules
    displayInformation
    saveDegeneration
/// 


doc ///
  Key
    "Theoretical background: Grobner fan of a module"
  Headline
    a complete summary of the results used in VectorBundleDegenerations
  Description
    Text
      The goal of what follows is collecting the key results
      used in the implementation of the package.
    Text
      Let $Q$ be a submodule of a free module $F=\bigoplus_{i=1}^m S e_i$ over
      a (multigraded) polynomial ring $S = K[x_1,...,x_n]$. This
      package computes the Groebner fan of $Q$, denoted $\Sigma(Q)$: the fan whose cones correspond
      to the distinct initial modules $\mathrm{in}_{(w,s)}(Q)$ with respect to a weight
      $(w,s)\in \mathbb{R}^n\times \mathbb{R}^m$. After computing said fan, the package also analyzes
      some of the properties of the sheaf associated to a module, if said module is defined over the Cox ring
      of a smooth toric variety.
    Text
      @HEADER3 "Initial module with respect to a weight and the Grobner fan of a module"@
    Text
      Let $S=K[x_1,..,x_n]$ be a polynomial ring graded by $\mathrm{deg}_S: \mathbb{N}^n\rightarrow \mathbb{Z}^d$ and $Q$ a homogeneous submodule of $F=\bigoplus_{i=1}^m S e_i$.
      Let $(w,s)\in \mathbb{R}^n\times \mathbb{R}^m$ and $q=\sum p_i e_i$ where $p_i= \sum \lambda_u x^u$. The @BOLD "initial element"@ of $q$ for $(w,s)$ is
      $$\mathrm{in}_{(w,s)}(q)=\sum_{\substack{w\cdot u+ s_j\\ \text{is minimal}}} \lambda_u x^ue_j$$
      and the @TO initialModule@ of $Q$ for $(w,s)$ is
      $$\mathrm{in}_{(w,s)}(Q)=\langle \mathrm{in}_{(w,s)}(q) : q\in Q\rangle \subseteq F.$$
    Text
      We say $(w,s)$ is equivalent to $(w',s')$ whenever $\mathrm{in}_{(w,s)}(Q)=\mathrm{in}_{(w',s')}(Q)$, and denote by $C_Q[(w,s)]$ the equivalence class of $(w,s)$, calling it the @BOLD "Groebner cone"@ of $Q$ at $(w,s)$. We omit the subscript $Q$ and write $C[(w,s)]$ when there is no possible confusion.
    Text
      @UL{
          "For each (w,s), the set C_Q[(w,s)] is a rational polyhedral cone.",
          "The set $\\Sigma(Q)=\\{\\overline{C_Q[(w,s)]}\\}$ is a rational polyhedral fan with a finite number of cones."
      }@
    Text
      Given a cone $\sigma\in\Sigma(Q)$, we denote by $\mathrm{in}_\sigma(Q):=\mathrm{in}_{(w,s)}(Q)$ for any $(w,s)\in \mathrm{relint}(\sigma)$.
    Text
      Now we give an insight into the construction of the Groebner fan of the module $\Sigma(Q)$, used by @TO grobnerPolyhedralFan@, in terms of the Groebner fan of an ideal.
    Text
      Let $R= S[e_1,...,e_m]$ be a polynomial ring graded by $\mathrm{deg}_R: \mathbb{N}^{n+m}\rightarrow G\oplus\mathbb{Z}$ with $\mathrm{deg}_R(x_i)=(\mathrm{deg}_S(x_i), 0)$ and $\mathrm{deg}_R(e_i)= (\mathrm{deg}_S(e_i),1)$. Given $Q$ as before, we define
      $$I(Q)=\left\langle \sum_{i=1}^m f_ie_i : (f_1,...,f_m)\in Q \right\rangle \subseteq R,$$
      an ideal in $R$ such that $Q\simeq I(Q)_{(\bullet,1)}:=\bigoplus_{(\delta, 1)\in G\oplus \mathbb{Z}}I(Q)_\delta$ (this is ideal computed with @TO moduleToIdeal@).
    Text
      @UL{
          "Each cone $\\sigma \\in \\Sigma(Q)$ is a union of the cones $\\sigma_1,...,\\sigma_k \\in \\Sigma(I(Q))$ such that $\\mathrm{in}_\\sigma(Q)\\simeq \\mathrm{in}_{\\sigma_j}(I(Q))_{(\\bullet,1)}$."      }@
    Text
      @HEADER3 "Properties of sheaves associated to modules in toric varieties"@
    Text
      Let $X_\Sigma$ be a simplicial toric variety and $S=K[x_1,...,x_n]$ its Cox ring (multigraded with respect to $\mathrm{Cl}(X)$).
      Let $B(\Sigma)$ be the irrelevant ideal of $X_\Sigma$.
      Let $Q$ be a submodule of $F=\bigoplus_{i=1}^m S e_i$ and let $P= \langle \bigoplus_{\alpha \in \mathrm{Pic}(X)} Q_\alpha \rangle$
      be a submodule of $Q$ generated in Picard degrees.
    Text
      @UL{
          { TOH isVectorBundle,
            PARA {" The following conditions are equivalent:",
              OL {" $\\widetilde{Q}$ is a vector bundle of rank $r$", "$\\mathrm{Fitt}_{r-1}(P)=0$ and $B(\\Sigma)\\subseteq \\mathrm{rad}(\\mathrm{Fitt}_{r}(P))$", " $\\mathrm{Fitt}_{r-1}(P)= (0)$ and $( \\mathrm{Fitt}_{r}(P): B(\\Sigma)^\\infty )=S$" }}},
          { TOH isReflexiveSheaf,
            PARA {"Let $j:P \\rightarrow P^{\\vee \\vee}$ be the natural map from $P$ to its double dual as an $S$-module. The following conditions are equivalent:",
              OL {"$\\widetilde{Q}$ is a reflexive sheaf", "$\\widetilde{Q}$ is a torsion free sheaf and $B(\\Sigma)\\subseteq \\mathrm{rad}(\\mathrm{Ann}(\\mathrm{Coker}(P)))$", "$\\widetilde{Q}$ is a torsion free sheaf and $( \\mathrm{Ann}(\\mathrm{Coker}(P)): B(\\Sigma)^\\infty )=S$" }}},
          { TOH isTorsionFreeSheaf,
            PARA {"Let $j:P \\rightarrow P^{\\vee \\vee}$ be the natural map from $P$ to its double dual as an $S$-module. The following conditions are equivalent:",
              OL {"$\\widetilde{Q}$ is a torsion-free sheaf", "$B(\\Sigma)\\subseteq \\mathrm{rad}(\\mathrm{Ann}(\\mathrm{Ker}(P)))$", "$( \\mathrm{Ann}(\\mathrm{Ker}(P)): B(\\Sigma)^\\infty )=S$" }}},
          { TOH "Fine-graded modules and equivariant",
            PARA {"If $Q$ is homogeneous with respect to the fine-grading, that is, the grading of $S$ with $\\mathrm{deg}(x_i)=e_i$, the $i$-th standard vector, then $\\widetilde{Q}$ is an equivariant sheaf. The converse does not hold: there are modules that are not fine-graded but still define equivariant sheaves."}}
      }@


    Text
      As it is necessary to consider a submodule generated in Picard degrees, the @TO GrobnerFan@ objects in the package should only be used for @BOLD "smooth"@ toric varieties.
    Text
      @HEADER3 "Properties of the Grobner fan of a module over Cox(X)"@
    Text
      Let $Q$ be a submodule of a free module $F= \bigoplus_{i=1}^m S e_i$ over the Cox ring $S= K[x_1,...,x_n]$ of a smooth toric variety, and $\Sigma(Q)$ its Groebner fan.
    Text
      @UL {
          { TOH specialSubfan,
            PARA {"Let $\\textbf{P}$ be an open property of flat families of sheaves in the sense of [HL10]. The set of cones $\\{\\sigma\\in \\Sigma(Q): \\widetilde{F/\\mathrm{in}_\\sigma(Q)} \\text{ satisfies } \\textbf{P}\\}$ is a subfan of $\\Sigma(Q)$. In particular, $\\textbf{P}$ can be taken to be the property of being a vector bundle, and we denominate this the $\\textit{vector bundle subfan}$."}},
          { TOH isEquivariant,
            PARA {"Let $\\sigma\\in \\Sigma(Q)$ be a cone in the Grobner fan and $\\pi_1:\\mathbb{R}^n\\times\\mathbb{R}^m\\rightarrow \\mathbb{R}^n$ the projection into the first $n$ coordinates. Then $\\mathrm{in}_\\sigma(Q)$ is fine-graded if and only if $\\dim(\\pi_1(\\sigma))=n$. Consequently, the non fine-graded modules form a subfan of $\\Sigma(Q)$, and if $\\dim(\\pi_1(\\sigma))=n$, then the associated sheaf $\\widetilde{F/ \\mathrm{in}_\\sigma(Q)}$ is equivariant."}}
      }@
  References
    Daniel Huybrechts and Manfred Lehn. @ITALIC "The geometry of moduli spaces of sheaves"@. Cambridge Mathematical Library. Cambridge University Press, Cambridge, second edition, 2010.
  SeeAlso
    "VectorBundleDegenerations tutorial"
    GrobnerFan
    initialModule
    moduleToIdeal
    displayInformation
///

-* ============================================================
   TYPE: GrobnerFan, CONSTRUCTOR, AND BASIC GETTERS
   ============================================================ *-

doc ///
  Key
    GrobnerFan
  Headline
    the class of all Grobner fans
  Description
    Text
      Given a submodule $Q$ of a free module $F=\bigopus_{i=1}^m S e_i$ over
      a (multigraded) polynomial ring $S = K[x_1,...,x_n]$, this
      package computes the Groebner fan of $Q$, denoted as $\Sigma(Q)$, has as cones the closures of the sets 
      $$C_Q[(w,s)]= \{(w',s')\in \mathbb{R}^n\times \mathbb{R}^m : \mathrm{in}_{(w',s')}(Q) =\mathrm{in}_{(w,s)}(Q)\},$$
      where $\mathrm{in}_{(w,s)}(Q)= \langle \mathrm{in}_{(w,s)}(q): q\in Q\rangle$
      with $$\mathrm{in}_{(w,s)}(\sum \lambda_{u,i}x^{u}e_i)= \sum_{\substack{w\cdot u+ s_i\\ \text{is minimal}}} \lambda_{u,i} x^ue_i.$$

      This results in a polyhedral fan:
    Example
      S = QQ[a,b,c, Degrees => {{2},{1},{2}}];
      I = ideal(a,b,c);
      Q = image map(S^{{-4}, {0}}, S^{{-6}}, matrix {{b^2+c}, {a^3+b^6}})
      F = grobnerPolyhedralFan(Q)
    Text
      In order to attach to this fan the initial modules that correspond 
      to each of the cones in the fan use @TO GrobnerFan@ use the 
      constructor @TO grobnerFan@.
    Example
      GRF = grobnerFan(Q)
    Text
      The type @TO GrobnerFan@ is designed to study Grobner degenerations of coherent sheaves in toric varieties.
      For this reason, the type stores also an ideal to perform
      the checks of the properties of being a vector bundle, a reflexive sheaf or a torsion-free sheaf. 

      By default, if no ideal is provided, the ideal is 
    Example
      ideal GRF 
    Text
      The rest of the data stored in GrobnerFan can be recovered as follows:
    Example
      module GRF 
      ring GRF 
      fan GRF 
      rays GRF 
      variety GRF
    Text
      When the @TO GrobnerFan@ is constructed for a module defined over 
      the Cox ring of a smooth toric variety $X$ then the ideal stored is
      the irrelevant ideal of $X.
    Example 
      X =  toricProjectiveSpace 1** toricProjectiveSpace 1;
      S = ring X;
      I = ideal X
      Q = image(map(S^{{-3, -1}, 2:{-2, 0}},S^{{-4, -1}},{{(1/10)*x_0+(4/9)*x_1}, {(1/7)*x_0^2*x_2+(1/10)*x_1^2*x_2}, {(1/8)*x_0^2*x_2+2*x_0*x_1*x_2}}))
      GRF2 = grobnerFan(X,Q)
      ideal GRF2 === I
    Text
      For more details on how to use this data type see @TO "VectorBundleDegenerations tutorial"@.
  SeeAlso
    "Theoretical background: Grobner fan of a module"
    grobnerFan
    grobnerPolyhedralFan
    moduleToIdeal
    infoInitialModules
 
///

doc ///
  Key
    grobnerFan
    (grobnerFan, Module, Fan, Ideal)
    (grobnerFan, Module, Fan)
    (grobnerFan, Module, Ideal)
    (grobnerFan, Module)
    (grobnerFan, NormalToricVariety, Module, Fan)
    (grobnerFan, NormalToricVariety, Module)
  Headline
    constructor for the type GrobnerFan
  Usage
    GRF = grobnerFan Q
    GRF = grobnerFan(Q, I)
    GRF = grobnerFan(Q, F)
    GRF = grobnerFan(Q, F, I)
    GRF = grobnerFan(X, Q)
    GRF = grobnerFan(X, Q, F)
  Inputs
    Q:Module
      the module we want to degenerate.
    F:Fan
      the output of @TO grobnerPolyhedralFan@, @TO fakeFan@ or any other compatible fan.
    I:Ideal
      the irrelevant ideal
    X:NormalToricVariety
      the smooth toric variety over whose Cox ring M is defined
  Outputs
    GRF:GrobnerFan
      the Grobner fan of Q
  Description
    Text
      Let $Q$ be a homogeneous module over a (multigraded) polynomial ring $S= K[x_1,...,x_n]$.
      The method computes the Grobner Fan of $Q$ (see @TO GrobnerFan@ and @TO "Theoretical background: Grobner fan of a module"@ for more details).
      There are several ways in which we can construct object of type @TO GrobnerFan@.

      The type contains has three fundamental pieces of information: a module, a fan and an ideal.
    Text
      @HEADER4 "Use case 1: Module"@
    Text
      
      The function takes the module and computes its Grobner Fan using @TO grobnerPolyhedralFan@ and the ideal passed
      is the ideal (1) in the polynomial ring S. In geometric terms this would correspond to considering sheaves
      over affine spaces
    Example
      R = QQ[x,y];
      Q =  image map(R^{{-3}, {-4}, {-2}},R^{2:{-5}},{{(8/9)*x^2+(3/2)*y^2, (1/5)*x^2}, {y, (3/8)*x}, {(10/7)*x^3+(3/7)*x*y^2+(3/8)*y^3, (2/3)*x*y^2}})
      GRF = grobnerFan(Q)
      F = fan GRF
      ideal GRF


    Text
      @HEADER4 "Use case 2: Module and ideal"@
    Text
      When giving the module and the ideal, the fan is computed as using @TO grobnerPolyhedralFan@. The change in ideal changes with respect to 
      which ideal the checks of @TO isVectorBundle@, @TO isReflexiveSheaf@ and @TO isTorsionFreeSheaf@ are done when using, for instance,
      the function @TO infoInitialModules@.

    Example
      I =  ideal(x_R);
      GRF2 = grobnerFan(Q, I)

      degenerateModule (GRF,{}) == degenerateModule (GRF2, {})
      isVectorBundle( degenerateModule(GRF2, {} ), ideal GRF2)
      isVectorBundle( degenerateModule(GRF, {} ), ideal GRF)

    Text
      @HEADER4 "Use case 3: Module and fan"@
    Text
      When giving the module and the fan, ideal is taken to be the ideal (1) in S. The main use of this method is to avoid
      save time as grobnerPolyhedralFan can be an expensive computation. The fan also need not be the true Grobner fan of 
      the module, any fan of the right dimension can be taken as input. This leads to a list of degenerations of the module
      which can contain repeated elements or can be missing some of the Grobner degenerations.
      Note that using @TO fanToString@ we can store the true Grobner fan of the module once has been computed and make the constructor
      be faster.

      In the following example the function @TO hasDuplicates@ returns true which means that there are repeated degenerations.
    Example
      time PF = grobnerPolyhedralFan Q
      time Ffake = fakeFan Q
      F == PF
      F == Ffake
      GRF3 = grobnerFan(Q ,Ffake)
      hasDuplicates GRF3 

    Text
      @HEADER4  "Use case 4: Module, fan and ideal"@
    Text
      The previous three use cases can be combined freely as needed.
    Example
      GRF4 = grobnerFan( Q, Ffake, I)
    Text
      @HEADER4  "Use case 5: Toric variety and module"@
    Text
      When a toric variety and a module are given, the module has to be defined over the Cox ring of the toric variety. 
      The fan taken is the @TO grobnerPolyhedralFan@ of $Q$ and the ideal is the irrelevant ideal of the toric variety.
      The variety is stored and can be recovered as shown in the example below.
    Example
      X =  toricProjectiveSpace 1
      S = ring X;
      I = ideal X;
      Q = image matrix{{x_0+ x_1},{x_0-x_1}}
      GRF5 = grobnerFan (X, Q)
      
      variety GRF5
      variety GRF4
      
    Text
      @HEADER4  "Use case 6: Toric variety, module and fan"@
    Text
      When a toric variety, a module and a fan are given, the module has to be defined over the Cox ring of the toric variety and the ideal is the irrelevant ideal of the toric variety. That is, we can combine the use cases 3 and 5 to have faster ways to obtain lists of degenerations 
      of sheaves in toric varieties.

  SeeAlso
    GrobnerFan
    grobnerPolyhedralFan
    moduleToIdeal
    infoInitialModules
///

doc ///
  Key
    (module, GrobnerFan)
    (ring, GrobnerFan)
    (fan, GrobnerFan)
    (ideal, GrobnerFan)
    (rays, GrobnerFan)
    (variety, GrobnerFan)
  Headline
    getter functions for the type GrobnerFan
  Usage
    module GRF
    ring GRF
    fan GRF
    ideal GRF
    rays GRF
    variety GRF
  Inputs
    GRF:GrobnerFan
      the Grobner fan 
  Description
    Text
      These are the basic getter functions for the fields stored on a
      @TO GrobnerFan@ : the module, its ring, the underlying fan, the
      irrelevant defining ideal(used for the sheaf tests @TO isVectorBundle@, @TO isReflexiveSheaf@ and @TO isTorsionFreeSheaf@ ),
      the rays of the fan, and, when defined over the Cox ring of a toric variety, that
      variety.

      See @TO "VectorBundleDegenerations tutorial"@.
  SeeAlso
    GrobnerFan
    grobnerFan
///

-* ============================================================
   FAN AND IDEAL CONSTRUCTION
   ============================================================ *-

       
doc ///
    Key
      grobnerPolyhedralFan
    Headline
      compute the Grobner fan of a module 
    Usage
      grobnerPolyhedralfan(M)
    Inputs
      Q : Module 
   Outputs
      G: Fan
  Description
      Text
        This function takes a module $Q$ and produces the Grobner fan of
        it.  It is assumed that $Q$ is a submodule of S^m, where S is a (multigraded) polynomial ring
        with n variables, then this a subfan of $\mathbb{R}^n \times \mathbb{R}^m$, with (w,s), (w',s')
        in the same cone of the fan if $\mathrm{in}_{(w,s)}(Q) = \mathrm{in}_{(w',s')}(Q)$.
        See @TO "Theoretical background: Grobner fan of a module"@ for the details.

	The output is a @TO "Polyhedra::Fan"@ in the sense of the @TO "Polyhedra::Polyhedra"@ package.
      Example
        R = QQ[x,y];
	      Q = image(map(R^2,R^2,{{(9/8)*x^2+x*y, (7/4)*x*y+(4/9)*y^2}, {(9/7)*x^3+(1/2)*x^2*y+(1/5)*x*y^2+(2/7)*y^3, 0}}));
	      F = grobnerPolyhedralFan Q;
	      rays F
	      maxCones F
        linealitySpace F
  Caveat
    The fan is build combining the cones of the Grobner fan of ideal obtained applying @TO moduleToIdeal@ to $Q$.
    To get the fan of this ideal @TO "gfanInterface::gfan"@ is used and the computation can become expensive for big examples. 
    For this reason it may be worth saving the output using @TO fanToString@ or using other fans, such as the
    ones obtained with @TO fakeFan@, when using @TO grobnerFan@. Considering fans that are not the Grobner fan of
    the module may help finding degenerations satisfying some desired properties faster. 
  SeeAlso
    grobnerFan
    moduleToIdeal
    fanToString
    fakeFan
///

doc ///
   Key 
      moduleToIdeal 
   Headline 
      turns a submodule of a free module $\bigoplus_{i=1}^m S e_i$ into an ideal in $S[e_1..e_r]$. 
   Usage 
      moduleToIdeal Q 
   Inputs 
      Q: Module
   Outputs 
      I: Ideal
   Description 
	Text 
           Takes a submodule $Q$ of a free module $F=\bigoplus_{i=1}^m S e_i$ where $S=K[x_1,...,x_n]$ is a (multigraded)
           polynomial ring and returns an ideal $I(Q)$ in the polynomial ring $R=S[e_1,...,e_m]$. 
           The ring $Q$ is graded by $\mathrm{deg}_R(x_i)=(\mathrm{deg}_S(x_i),0)$ and $\mathrm{deg}_R(e_i)=(\mathrm{deg}_S(e_i),1)$
           where $\mathrm{deg}_S(e_i)$ is the degree of the i-th basis vector of the ambient free module and the ideal $I(Q)$ is such that 
           $$ Q \simeq \bigoplus_{d\in \mathrm{Im}(\mathrm{deg_S})} I(Q)_{(d,1)}.$$

           
	Example
	   S = QQ[x,y, Degrees => {{3},{4}}];
	   Q = image(map(S^{{-1},{0},{0}}, S^{{-2},{-2}}, matrix {{x,y},{x^2,-y^2},{x*y,x^2+y^2}}))
	   I = moduleToIdeal Q
           R  = ring I
           degrees R
        Text
          This function is both used by @TO grobnerPolyhedralFan@ and @TO initialModule@. 
   SeeAlso
     grobnerPolyhedralFan
     initialModule
///



doc ///
  Key
    correctionVector
    (correctionVector, Fan)
    (correctionVector, Matrix)
    (correctionVector, Module)
    (correctionVector, GrobnerFan)
  Headline
    computes a positive vector in the lineality space of a fan
  Usage
    v = correctionVector F
    v = correctionVector A
    v = correctionVector Q
    v = correctionVector GRF
  Inputs
    F:Fan
      grobnerPolyhedralFan(Q)
    A: Matrix
      linealitySpace(F)
    M: Module
    GRF:GrobnerFan
      the Grobner fan of a module Q
  Outputs
    v:List
  Description
    Text
      In order to compute the initial module of a module $Q$ with respect to some weights, these weights need to be
      are positive integers, and so correctionVector computes a positive vector in the lineality space of a fan,
      so that adding a scalar multiple of it to the weight $(w,s)$ gives a new weight $(w',s'$) such that is positive and the initial
      module is the same, i.e., $\mathrm{in}_{(w,s)}(Q)=\mathrm{in}_{(w',s')}(Q)$.
      This computation can be performed on a fan $F$ using its lineality space, on a matrix $A$ corresponding to the lineality space of said fan,
      on the GrobnerFan $GRF$ applying it to its fan or directly on the module. In the case where of a (multigraded) module the matrix taken is
      the one obtained from the degrees of the ring of $TO moduleToIdeal$ of said module as these form a subset of the vectors in the lineality
      space of its Grobner fan and if the grading is a positive grading (see Definition 8.7 in [MS05]) with values in a torsion free abelian group, they suffice for finding 
      an appropriate vector.
    Example
      S= QQ[x,y,z,Degrees => {{2},{1},{2}}];
      Q = image map(S^{{-4}, {0}}, S^{{-6}}, matrix {{y^2+z}, {x^3+ y^6}})
      v = correctionVector(Q)
      initialModule(Q, {-2,4,-6},{-2,-3} )
    Text
      The other ways of using this method are exemplified below:
    Example
      GRF = grobnerFan Q;
      correctionVector GRF == v 
      F = fan GRF 
      correctionVector F == v
      correctionVector linealitySpace F == v
  References
    Ezra Miller and Bernd Sturmfels. @ITALIC "Combinatorial commutative algebra"@, volume 227 of @ITALIC "Graduate Texts in Mathematics"@. Springer-Verlag, New York, 2005.
  SeeAlso
    initialModule
///


doc ///
  Key
    initialModule
    (initialModule, Module, List, List)
    [initialModule, Correction]
    [initialModule, TimeSpent]
  Headline
    computes the initial module of a module with respect to weight vectors
  Usage
    Q' = initialModule(Q, w, s)
  Inputs
    Q:Module
    w:List
      integer weights for the variables of the polynomial ring
    s:List
      integer weights for the basis of the ambient free module
    Correction => List
      a vector with positive entries in the lineality space of the Groebner fan of M
    TimeSpent => ZZ
      maximum time that will be spent computing the initial module, in seconds
  Outputs
    Q':Module
      the initial module $\mathrm{in}_{(w,s)}(Q)$
  Description
    Text
      Takes a submodule $Q$ of a free module $\bigoplus_{i=1}^m S e_i$ with $S$ a (multigraded) polynomial ring $S= K[x_1,...,x_n]$ and returns the
      initial module $\mathrm{in}_{(w,s)}(Q)$, where $w\in \mathbb{R}^n$ are the weights on
      the variables of the ring, and $s\in\mathbb{R}^m$ are the weights on the basis
      vectors $e_i$. The initial module is taken with respect to the min
      convention, so the initial term of an element is the sum of the terms
      of lowest weight (see @TO "Theoretical background: Grobner fan of a module"@). There is an unchecked assumption that the module is
      homogeneous.
    Text
      The computation internally needs the weight vector to be positive and to stay in
      the same cone in the Groebner fan of the module. A @TO correctionVector@
      is computed automatically, but it can also be provided explicitly
      using the option Correction. The maximum time for the computation is set
      to 30 seconds by default, returning the zero module if the time is
      exceeded. Use TimeSpent to set a longer time limit, in seconds, for the computation.

    Example
      S = QQ[x,y];
      Q = image matrix {{x^2-y^2},{y^2}};
      initialModule(Q, {0,1}, {0,1})
      initialModule(Q, {0,-1}, {1,1})
      initialModule(Q, {0,0}, {0,1})
    Text 
      For homogeneous modules the output is a homogeneous module.
    Example
      S= QQ[x,y,z,Degrees => {{2},{1},{2}}];
      Q1 = image map(S^{{-4}, {0}}, S^{{-6}}, matrix {{y^2+z}, {x^3+ y^6}})
      Q2 = initialModule(Q1, {2,-4,-5}, {-2,2})
      degrees ambient Q2 
      degrees  Q2 
      isHomogeneous Q2

  SeeAlso
    moduleToIdeal
    correctionVector
    degenerateModule
    infoInitialModules
///



doc ///
  Key
    latticeInteriorPoint
    (latticeInteriorPoint, Cone)
    (latticeInteriorPoint, GrobnerFan, List)
  Headline
    computes a lattice interior point of a cone
  Usage
    p = latticeInteriorPoint C
    p = latticeInteriorPoint(GRF, c)
  Inputs
    C:Cone
      
    GRF:GrobnerFan
      a Grobner fan of a module
    c:List
      a cone in the fan of GrobnerFan
  Outputs
    p:List
      a lattice interior point
  Description
    Text
      In order to compute the initial module of a cone in the GrobnerFan of a module
      we need a (positive) lattice point in the cone. The function latticeInteriorPoint 
      gives a lattice point in the interior of the cone (to make it positive we add a vector obtained in @TO correctionVector@).
      
      This function is used internally in @TO infoInitialModules@ to obtain the initial modules on a @TO GrobnerFan@. 
      However, it can be used separately when giving a @TO "Polyhedra::Cone"@ in the sense of the package @TO "Polyhedra::Polyhedra"@ to 
      compute one such point or be used taking as inputs a GrobnerFan and a List corresponding to cone in the fan 
      to recover the point that was used for the computation of the initial module for that cone.
    Example
      A = map(ZZ^4,ZZ^6,{{0, 0, 1, -1, -1, 1}, {1, 0, 1, -1, -1, 1}, {0, 0, 1, 0, -1, 0}, {0, -1, 0, 1, 0, -1}})
      C = coneFromVData A
      latticeInteriorPoint C
    Example
      R = QQ[x,y];
      Q = image(map(R^{{-3}, {-2}},R^{2:{-5}},{{(9/8)*x^2+x*y, (7/4)*x*y+(4/9)*y^2}, {(9/7)*x^3+(1/2)*x^2*y+(1/5)*x*y^2+(2/7)*y^3, 0}}))
      GRF = grobnerFan Q;
      latticeInteriorPoint( GRF, {0,1} )
      ambient Q / initialModule( Q, {0,1},{0,-1}, Correction => correctionVector GRF ) == degenerateModule ( GRF, {0,1})
    Text
      It is no coincide that the two lattice interior points coincide
      as the cones taken are the same.
    Example
      C2 = cone (GRF,{0,1})
      C == C2
      
  SeeAlso
    correctionVector
    initialModule
    infoInitialModules
    cone 
///




doc ///
  Key
    isEquivariant
    (isEquivariant, Matrix, ZZ)
    (isEquivariant, Cone, ZZ)
    (isEquivariant, GrobnerFan, List)
    (isEquivariant, GrobnerFan)
  Headline
    checks if a cone defines an equivariant sheaf
  Usage
    isEquivariant(sigma, n)
    isEquivariant(C, n)
    isEquivariant(GRF, L)
    isEquivariant GRF
  Inputs
    sigma:Matrix
      
    n:ZZ
      number of variables in the ring S 
    C:Cone 
    GRF:GrobnerFan
    L:List
      list representing a cone in GRF
  Outputs
    :Boolean
      if true then the module associated to the cone is equivariant
  Description
    Text 
      This function has two main strategies: projecting a cone 
      to the first n coordinates and check if it is full-dimensional and recover 
      the information of stored in @TO GrobnerFan@.
    
      For the first strategy there are two possible inputs. One takes as input a matrix 
      sigma whose rays span a Grobner cone, and the number n of
      variables of the polynomial ring over which the module is defined. The other one 
      takes a @TO "Polyhedra::Cone"@ and n and performs the same procedure.
    
      The output is true if the projection of the cone
      to the first $n$ coordinates is full-dimensional (so the
      corresponding initial module is homogeneous with respect to
      a $\mathbb{Z}^n$ grading).  If the output is false the module associated to the cone 
      is not fine-graded, but the sheaf associated could still be equivariant.

      See @TO "Theoretical background: Grobner fan of a module"@ for more details.
    Example
      X =  toricProjectiveSpace 1;
      S = ring X;
      Q = image matrix{{x_0+ x_1},{x_0-x_1}}
      GRF = grobnerFan (X, Q)
      F = fan GRF;
      c = (cones( 3, F))_0
      A = rays F;
      LS = linealitySpace F;
      isEquivariant(A_c|LS, 2 )
    Text
      When given a @TO GrobnerFan@ and its degenerations computed using @TO infoInitialModules@ 
      the process will store for each cone whether or not its projection to the first $n$ is 
      full dimensional and we can recover this information without computing it again.

      If @TO infoInitialModules@ has not been computed before, it will be computed automatically.
    Example
      infoInitialModules GRF 
      isEquivariant( GRF,{0})
    Text
      We can also recover the list of all the cones for which isEquivariant evaluates to true.
    Example
      isEquivariant( GRF)
    Text
      Note that the cone {} corresponding to the module $Q$ 
      is not in the list of equivariant cones, because the module is not fine-graded. 
      However the sheaf associated is a vector bundle on $\mathbb{P}^1$, so it is 
      isomorphic to a direct sum of line bundles and thus the associated sheaf is equivariant.
    Example
      degenerateModule(GRF,{})
      isVectorBundle(GRF,{})
  SeeAlso
    infoInitialModules
    isVectorBundle
    isReflexiveSheaf
    isTorsionFreeSheaf
///


doc ///
  Key
    isVectorBundle
    (isVectorBundle, Module, Ideal, ZZ)
    (isVectorBundle, Module, NormalToricVariety, ZZ)
    (isVectorBundle, Module, Ideal)
    (isVectorBundle, Module, NormalToricVariety)
    (isVectorBundle, GrobnerFan, List)
    (isVectorBundle, GrobnerFan)
    [isVectorBundle, Strategy]
  Headline
    decides whether the sheafification of a module is a vector bundle of rank r
  Usage
    isVectorBundle(Q, I, r)
    isVectorBundle(Q, X, r)
    isVectorBundle(Q, I)
    isVectorBundle(Q, X)
    isVectorBundle(Module, Ideal, ZZ, Strategy => "radical")
    isVectorBundle(Module, Ideal, ZZ, Strategy => "saturation") 
    isVectorBundle(GRF, c)
    isVectorBundle GRF
  Inputs
    Q:Module
    I:Ideal
      the irrelevant ideal
    X:NormalToricVariety
    r:ZZ
      the rank
    GRF:GrobnerFan
      the Grobner fan of a module
    c:List
      a cone in  GrobnerFan
    Strategy => String
      specifies if the functions takes the "radical" or the "saturation". By default takes "radical".

  Outputs
    :Boolean
      @TO true@ if it is a vector bundle of rank r, else @TO false@
    :Thing
      the rank of the bundle, or @TO false@
    L:List
      a list of cones in GRF that define vector bundles
  Description
    Text
      This function determines whether the sheafification of a module  over 
      a polynomial ring is a vector bundle of rank
      $r$ on the corresponding toric variety with irrelevant ideal $I$ of a toric 
      variety $X$.  The output is false if the module does not define a vector 
      bundle or the rank $r$ if it does.

      See @TO "Theoretical background: Grobner fan of a module"@ for more details.
    Example
      X = toricProjectiveSpace 1;
      S = ring X;
      I = ideal X
      B = matrix{{x_0^4-x_1^4, x_0^2*x_1^2+4*x_0^4, x_0^3*x_1-14*x_1^4},{x_1, x_0, x_0},{x_0^2-x_1^2, x_0*x_1+4*x_0^2, x_0*x_1+4*x_1^2}};
      Q = image map(S^{0,-1,-2}, S^{-3,-3,-3}, B);
      P = coker map(S^{0,-1,-2}, S^{-3,-3,-3}, B);
      isVectorBundle(Q,I)
      isVectorBundle(P,I)
    Text
      The method comes with two possible modes to do the internal computations. One of 
      the checks is seeing if some power of the irrelevant ideal of the toric variety is 
      contained in the r-th @TO fittingIdeal@ of the module. This can be done taking the 
      radical of the Fitting ideal or considering the saturation.

      By default the mode selected is taking radicals.

      Other ways of performing the computations are collected below:
    Example
      isVectorBundle(Q ,X, Strategy => "radical")
      isVectorBundle(Q ,X, 2, Strategy => "saturation" )
      isVectorBundle(Q ,X, 3, Strategy => "saturation" )
    Text
      If a @TO GrobnerFan@ is given and using @TO infoInitialModules@ the degenerations 
      have already been computed, the information about which cones define vector bundles 
      is stored and can be recovered directly either by inspecting a particular cone or 
      asking for the list of all the cones that define vector bundles. 

      If @TO infoInitialModules@ has not been computed before, it will be computed automatically.

    Example
      use S;
      Q = image matrix{{x_0+ x_1, x_1},{x_0-x_1,x_0},{ x_1, 0}}
      GRF = grobnerFan (X, Q)
      infoInitialModules(GRF)
      isVectorBundle(GRF, {1})
      degenerateModule( GRF, {1})
      isVectorBundle (GRF, {3,5})
      degenerateModule(GRF, {3,5})
      VBlist = isVectorBundle(GRF)
    Text
      When all the initial modules have been computed for the Grobner fan of a module, 
      the list of all the cones defining vector bundles yields a subfan of the 
      Grobner fan (see @TO specialSubfan@). It is possible to obtain it as a Fan or as a GrobnerFan (with the information of the computed degenerations).
    Example 
        FVB = specialSubfan (GRF, VBlist)
        dim FVB == dim fan GRF
        isComplete FVB 

        GRFvb =specialSubfan(GRF)
        displayInformation GRFvb
  Caveat
    Sometimes both taking radical or saturation will lead to an error that aborts 
    the computation for some modules over multigraded rings. It is advised to save 
    the relevant computations before applying this method.

  SeeAlso 
    specialSubfan
    isTorsionFreeSheaf
    isReflexiveSheaf
    isEquivariant
    isToricVectorBundle
    infoInitialModules
///


doc ///
  Key
    isTorsionFreeSheaf
    (isTorsionFreeSheaf, Module, Ideal)
    (isTorsionFreeSheaf, Module, NormalToricVariety)
    (isTorsionFreeSheaf, GrobnerFan, List)
    (isTorsionFreeSheaf, GrobnerFan)
    [isTorsionFreeSheaf, Strategy]
  Headline
    checks if the sheafification of the module is a torsion-free sheaf
  Usage
    isTorsionFreeSheaf(Q, I)
    isTorsionFreeSheaf(Q, X)
    isTorsionFreeSheaf(GRF, c)
    isTorsionFreeSheaf GRF
  Inputs
    Q:Module
      
    I:Ideal
      the irrelevant ideal
    X:NormalToricVariety
      
    GRF:GrobnerFan
      the Grobner fan of a module
    c:List
      a cone in GRF
    Strategy => String
      specifies if the functions takes the "radical" or the "saturation". By default takes "radical".

  Outputs
    :Boolean
    L:List
      list of cones in GRF that define torsion-free sheaves
  Description
    Text
      This function determines whether the sheafification of a module over a polynomial 
      ring is a torsion-free sheaf on the corresponding toric variety with irrelevant 
      ideal $I$ of a toric variety $X$.  The output is true if so and false if not.

      The computation can be made taking radical or taking saturation as explained in @TO "Theoretical background: Grobner fan of a module"@ 
      and for some examples one of the computations can be more convenient than the other. This can be selected using Strategy. 
    Example
      X = toricProjectiveSpace 1;
      S = ring X;
      I = ideal X
      A = matrix{{x_0+ x_1, x_1},{x_0-x_1,x_0},{ x_1, 0}};
      isTorsionFreeSheaf( coker A , I)
      isTorsionFreeSheaf( image A , I, Strategy => "saturation")
    Text
      If a @TO GrobnerFan@ is given and using @TO infoInitialModules@ the degenerations 
      have already been computed, the information about which cones define torsion-free sheaves 
      is stored and can be recovered directly either by inspecting a particular cone or asking 
      for the list of all the cones that define vector bundles. 

      If @TO infoInitialModules@ has not been computed before, it will be computed automatically.

    Example
      Q = image A;
      GRF = grobnerFan (X, Q)
      infoInitialModules(GRF);
      isTorsionFreeSheaf(GRF, {1})
      degenerateModule (GRF, {1})
      isTorsionFreeSheaf(GRF, {3})
      degenerateModule (GRF, {3})
      isTorsionFreeSheaf(GRF)
  Caveat
    Sometimes both taking radical or saturation will lead to an error that aborts 
    the computation for some modules over multigraded rings. It is advised to save 
    the relevant computations before applying this method.
  SeeAlso
    "Theoretical background: Grobner fan of a module"
    infoInitialModules
    isEquivariant
    isReflexiveSheaf
    isVectorBundle
///

doc ///
  Key
    isReflexiveSheaf
    (isReflexiveSheaf, Module, Ideal)
    (isReflexiveSheaf, Module, NormalToricVariety)
    (isReflexiveSheaf, GrobnerFan, List)
    (isReflexiveSheaf, GrobnerFan)
    [isReflexiveSheaf, Strategy]
  Headline
    checks if the sheafification of the module is a reflexive sheaf
  Usage
    isReflexiveSheaf(Q, I)
    isReflexiveSheaf(Q, X)
    isReflexiveSheaf(GRF, c)
    isReflexiveSheaf GRF
  Inputs
    Q:Module
      
    I:Ideal
      the irrelevant ideal
    X:NormalToricVariety
      
    GRF:GrobnerFan
      the Grobner fan of a module
    c:List
      a cone in GRF
    Strategy => String
      specifies if the functions takes the "radical" or the "saturation". By default takes "radical".

  Outputs
    :Boolean
    L:List
      list of cones in GRF that define torsion-free sheaves
  Description
    Text
      This function determines whether the sheafification of a module over a polynomial 
      ring is a reflexive sheaf on the corresponding toric variety with irrelevant ideal $I$ 
      of a toric variety $X$.  The output is true if so and false if not.

      The computation can be made taking radical or taking saturation as explained in @TO "Theoretical background: Grobner fan of a module"@ 
      and for some examples one of the computations can be more convenient than the other. This can be selected using Strategy.
    Example
      X = toricProjectiveSpace 1;
      S = ring X;
      I = ideal X
      A = matrix{{x_0+ x_1, x_1},{x_0-x_1,x_0},{ x_1, 0}};
      isReflexiveSheaf( coker A , I)
      isReflexiveSheaf( image A , I, Strategy => "saturation")
    Text
      If a @TO GrobnerFan@ is given and using @TO infoInitialModules@ the degenerations 
      have already been computed, the information about which cones define reflexive sheaves 
      is stored and can be recovered directly either by inspecting a particular cone or 
      asking for the list of all the cones that define vector bundles. 

      If @TO infoInitialModules@ has not been computed before, it will be computed automatically.

    Example
      Q = image A;
      GRF = grobnerFan (X, Q)
      infoInitialModules(GRF);
      isReflexiveSheaf(GRF, {1})
      degenerateModule (GRF, {1})
      isReflexiveSheaf(GRF, {3})
      degenerateModule (GRF, {3})
      isReflexiveSheaf(GRF)
  Caveat
    Sometimes both taking radical or saturation will lead to an error that aborts 
    the computation for some modules over multigraded rings. It is advised to save 
    the relevant computations before applying this method.
  SeeAlso
    infoInitialModules
    isEquivariant
    isTorsionFreeSheaf
    isVectorBundle
///



doc ///
  Key
    isToricVectorBundle
    (isToricVectorBundle, GrobnerFan, List)
    (isToricVectorBundle, GrobnerFan)
  Headline
    check if the cones define toric vector bundles
  Usage
    isToricVectorBundle(GRF, c)
    isToricVectorBundle GRF
  Inputs
    GRF:GrobnerFan
      the Grobner fan of a module
    c:List
      a cone in GRF
  Outputs
    :Boolean
      output for the first usage case
    L:List
      list of cones in GRF that define torsion-free sheaves
  Description
    Text
      It combines the checks of @TO isVectorBundle@ and @TO isEquivariant@. 
      A @TO GrobnerFan@ is given: the information about which cones define toric 
      vector bundles is stored and can be recovered directly either by inspecting a 
      particular cone or asking for the list of all the cones that define vector bundles. 

      If @TO infoInitialModules@ has not been computed before, it will be computed automatically.

    Example
      X = toricProjectiveSpace 1;
      S = ring X;
      Q = image matrix{{x_0+ x_1, x_1},{x_0-x_1,x_0},{ x_1, 0}}
      GRF = grobnerFan (X, Q)
      infoInitialModules(GRF);
      isToricVectorBundle(GRF, {1})
      degenerateModule (GRF, {1})
      isToricVectorBundle(GRF, {3})
      degenerateModule (GRF, {3})
      isToricVectorBundle(GRF)
  Caveat
    Recall that the test for @TO isEquivariant@ may return false for modules that in fact 
    define equivariant sheaves, that is, it has false negatives. For this reason there may 
    be more cones that define toric vector bundles in the Grobner fan.


  SeeAlso
    infoInitialModules
    isVectorBundle
    isEquivariant
///


doc ///
  Key
    infoInitialModules
    (infoInitialModules, GrobnerFan, List)
    (infoInitialModules, GrobnerFan)
    [infoInitialModules, Strategy]
    [infoInitialModules, TimeSpent]
    [infoInitialModules, Correction]
  Headline
    gives a list of hash tables with the information about the degenerations corresponding to the cones in the Grobner fan of a module
  Usage
    L = infoInitialModules(GRF, conesList)
    L = infoInitialModules(GRF)
  Inputs
    GRF:GrobnerFan
    conesList:List
      list of cones that we want to analyze
    Strategy => String
      specifies the mode passed to isVectorBundle (radical or saturation).  
    TimeSpent => ZZ
      maximum time spent computing each @TO initialModule@
    Correction => List
      correction vector to compute @TO initialModule@

  Description
    Text
      The function takes a @TO GrobnerFan@ GRF of an homogeneous submodule $Q$ of a free module 
      $oplus_{i=1}^m S e_i$, where $S=K[x_1,...,x_n]$ is the Cox ring of the toric variety $X$ or a general (multigraded) polynomial ring and  
      a list of cones of the fan. The function computes the initial modules corresponding to those cones associated the module $oplus_{i=1}^m S e_i/\mathrm{in}_{(w,s)}(Q)$. 
      For each of these modules the method applies @TO isEquivariant@, @TO isVectorBundle@, @TO isReflexiveSheaf@ and @TO isTorsionFreeSheaf@ and associates this information to the cone. The computations of @TO isVectorBundle@, @TO isReflexiveSheaf@ and @TO isTorsionFreeSheaf@ can be made taking radical or taking saturation as explained in @TO "Theoretical background: Grobner fan of a module"@ and for some examples one of the computations can be more convenient than the other. This can be selected using Strategy. 


      If no list is given, the function computes the initial modules for all the cones in the fan.

      The first time the function is run for a GrobnerFan a message saying how many modules have been 
      computed will appear and the information will be stored in the GrobnerFan. 

       
    Example
      S= QQ[x,y,z,Degrees => {{2},{1},{2}}];
      I= ideal(x,y,z);
      Q= image map(S^{{-4}, {0}}, S^{{-6}}, matrix {{y^2+z}, {x^3+ y^6}});
      GRF = grobnerFan(Q, I) 
      infoInitialModules GRF

    Text
      The information per cone can be recovered as follows:
    Example
      degenerateModule(GRF, {0,2})
      isTorsionFreeSheaf(GRF,{0,2})
      isReflexiveSheaf(GRF,{0,2})
      isVectorBundle(GRF,{0,2})
      isToricVectorBundle(GRF,{0,2})
      isEquivariant(GRF,{0,2})
      cone (GRF,{0,2})
      rays(GRF, {0,2})
      dim ( GRF,{0,2})
      latticeInteriorPoint ( GRF, {0,2})
    Text
      To get a summary about the degenerations computed use @TO displayInformation@.
    Example
      displayInformation GRF
    Text
      In the case of a subset of cones the information displayed will correspond to that subset.
    Example
      GRF1 = grobnerFan(module GRF, fan GRF , ideal GRF );
      infoInitialModules(GRF1, cones(4, fan GRF ) , Strategy => "saturation")
      degenerateModule GRF1
      displayInformation GRF1
  Caveat
      All the methods requiring a GrobnerFan and a List will run infoInitialModules if 
      it has not been computed yet. If the computation is done by one of those methods,
      it will compute the degenerations for all the modules in the fan.
    
      Sometimes both taking radical or saturation will lead to an error that aborts 
      the computation for some modules over multigraded rings. It is advised to save 
      the relevant computations before applying this method.

  SeeAlso
    listCones
    correctionVector
    initialModule
    isVectorBundle
    isTorsionFreeSheaf
    isReflexiveSheaf
    isEquivariant
    isToricVectorBundle
    degenerateModule
    latticeInteriorPoint
    fakeFan
    generateHomogeneousModule
///


doc ///
  Key
    degenerateModule
    (degenerateModule, GrobnerFan, List)
    (degenerateModule, GrobnerFan)
  Headline
    recovers the degenerate module 
  Usage
    degenerateModule(GRF, c)
    degenerateModule GRF
  Inputs
    GRF:GrobnerFan
    c:List
      cone in GRF
  Outputs
    M:Module
      degeneration at the cone c
    L:List
      list of all degeneration
  Description
    Text
      This function recovers the initial module at a given cone or the list of all the initial modules
      that has been computed using @TO infoInitialModules@.
    Text
      @HEADER4 "Use case 1: Grobner fan and cone"@
    Text
      The function returns the degenerate module associated to the cone given a list. If @TO infoInitialModules@
      has already been applied, the module is already stored in the @TO GrobnerFan@ and the method outputs it directly. 
      If @TO infoInitialModules@ has not been run or the cone is not in the list of the computed cones, the computaiton is performed finding and interior point in the cone and using @TO initialModule@, but it will not be stored.
 
    Example
      X =  toricProjectiveSpace 1
      S = ring X;
      M = image matrix{{x_0+ x_1},{x_0-x_1}}
      GRF = grobnerFan (X,M);
      listCones GRF
      infoInitialModules(GRF, {{}, {0}, {1}, {2}, {3}})
      
      time degenerateModule( GRF ,{0})
      time degenerateModule ( GRF, {0,2})


      
    Text
      @HEADER4 "Use case 2: Grobner fan"@
    Text
      The function returns the list with all of the initial modules that have been computed when applying @TO infoInitialModules@
    Example
      degenerateModule GRF


  SeeAlso
    infoInitialModules
    fineGrading
///

doc ///
  Key
    (rays, GrobnerFan, List)
    (cone, GrobnerFan, List)
    (dim, GrobnerFan, List)
  Headline
    getter functions for GrobnerFan and a cone
  Usage
    rays(GRF, c)
    cone(GRF, c)
    dim(GRF, c)
  Inputs
    GRF:GrobnerFan
    c:List
      a cone in GRF
  Description
    Text
      These functions recovers the rays, cone and dimension that are computed and stored by @TO infoInitialModules@.
    Example
      X =  toricProjectiveSpace 1
      S = ring X;
      M = image matrix{{x_0+ x_1},{x_0-x_1}}
      GRF = grobnerFan (X,M);
      dim( GRF, {0,2})
      rays(GRF, {0,2})
      cone (GRF, {0,2})
      
      
  SeeAlso
    infoInitialModules
///




doc ///
  Key
    fakeFan
  Headline
    gives a quick approximation of the Grobner fan of a module
  Usage
    F = fakeFan Q 
  Inputs
    Q:Module
  Outputs
    F:Fan
  Description
    Text
      Given a module $Q$, it computes the Minkowski sum of the Newton polytopes of the generators of $Q$
      and returns the normal fan of this polytope.  This can be used as a quick approximation 
      of the Grobner fan of $Q$ if the computation of the Grobner fan takes too long.
      Moreover, if the module is monogenerated it coincides with the Grobner fan of $Q$.
    Example
      S= QQ[x,y,z,Degrees => {{2},{1},{2}}];
      I= ideal(x,y,z);
      Q= image map(S^{{-4}, {0}}, S^{{-6}}, matrix {{y^2+z}, {x^3+ y^6}});
      time F1 = grobnerPolyhedralFan (Q)
      time F2 = fakeFan(Q)
      F1 == F2
    Text
      In general, the fans will not coincide but the computation of the fake fan will be significantly faster
    Example
      use S;
      Q1 = image map(S^{{-4}, {0}}, S^{{-6},{-6}}, matrix {{y^2+z, x-z}, {x^3+ y^6, 2*z^3}});
      time G1 = grobnerPolyhedralFan (Q1)
      time G2 = fakeFan(Q1)
      rays G1== rays G2
///

doc ///
  Key
    fanToString
  Headline
    gives a string with the code to create a fan
  Usage
    s = fanToString(F)
  Inputs
    F:Fan
  Outputs
    s:String
  Description
    Text
      Given a fan F, this function returns a string with the code to create the fan.
      This code is part of the @TO saveDegeneration@ function, but it can be used separately 
      to have executable code for the fan.
    Example
      S = QQ[x,y,z,Degrees => {{2},{1},{2}}];
      I = ideal(x,y,z);
      Q = image map(S^{{-4}, {0}}, S^{{-6}}, matrix {{y^2+z}, {x^3+ y^6}});
      F = grobnerPolyhedralFan Q
      s = fanToString(F)
  SeeAlso
    grobnerPolyhedralFan
    grobnerFan
    fakeFan
    saveDegeneration
///

doc ///
  Key
    specialSubfan
    (specialSubfan, GrobnerFan)
    (specialSubfan, GrobnerFan, List) 
    [specialSubfan, Strategy]
  Headline
    constructs subfans of a Grobner fan from a list of cones 
  Usage
    GRF' = specialSubfan GRF
    F = specialSubfan(GRF, L)
  Inputs
    GRF:GrobnerFan
    L:List
      list of cones 
    Strategy => String
      select between the "VectorBundle" subfan and the "NonEquivariant" subfan
  Outputs
    GRF': GrobnerFan
      either the vector bundle subfan or the subfan of non equivariant modules
    F:Fan
  Description
    Text
      Given a @TO GrobnerFan@ and a list of cones,
      it returns the fan that is the subfan defined by the list. The rays of the new fan 
      are a subset of the rays in the fan of the GrobnerFan. Note that this process is likely to  
      relabel the rays.
    Example
      X = toricProjectiveSpace 2 ** toricProjectiveSpace 1
      S = ring X
      Q = image(map(S^{1:{-3, -1}, 3:{-4, 0}},S^{2:{-4, -1}},{{(1/9)*x_0+3*x_1,0}, {x_4, x_3- x_4}, {9*x_3, (10/7)*x_3+(7/10)*x_4}, {(3/4)*x_4, 0}}))
      GRF = grobnerFan(X,Q)
      F = fan GRF;
      F5  = specialSubfan(GRF, cones(5, F ));
      GRF5 = grobnerFan (X, Q, F5);

      displayInformation GRF
      displayInformation GRF5


    Text
      If the input is only the GrobnerFan then the output is the vector bundle subfan, that is, the subfan where all the cones
      define a vector bundle. If Strategy => "NonEquivariant" is passed, the output is the subfan of modules that are not fine-graded.
    Example
      GRFvb = specialSubfan(GRF)
      displayInformation GRFvb
      Fvb = specialSubfan(GRF, isVectorBundle GRF )

      GRFneq = specialSubfan (GRF, Strategy=> "NonEquivariant")
      displayInformation  GRFneq
      
      Fneq = specialSubfan(GRF, delete( isEquivariant GRF, listCones GRF ) )
      
   
  Caveat
    In order to recover the vector bundle subfan and the non equivariant subfan to return the correct fans, enough degenerations
    need to be computed, meaning, when applying @TO infoInitialModules@, the list should contain all the cones that have the property
    that we are considering. Else, some of the cones could be missing in the output. 
  SeeAlso
    isVectorBundle
    equivariantCones
    isVectorBundle
///


doc ///
  Key
    equivariantCones
    (equivariantCones, Fan, ZZ)
    (equivariantCones, GrobnerFan)
  Headline
    list the equivariant cones
  Usage
    equivariantCones(F, n)
    equivariantCones GRF
  Inputs
    F:Fan
    n:ZZ
      dimension of the space where F is projected
    GRF:GrobnerFan
      
  Outputs
    L:List
      list of cones in the fan
  Description
    Text
      This function takes a fan F or the fan of a Grobner fan GRF and returns the list of cones such that @TO isEquivariant@ returns true,
      that is, the list of cones that when projected into the first n coordinates is n-dimensional.

      This function can be used to give @TO infoInitialModules@ as input so that it only computes degenerations that are given
      by fine-graded modules. 

      
    Example
      S = QQ[x,y,z,Degrees => {{2},{1},{2}}];
      I = ideal(x,y,z);
      Q = image map(S^{{-4}, {0}}, S^{{-6}}, matrix {{y^2+z}, {x^3+ y^6}});
      GRF = grobnerFan (Q)
      Leq = equivariantCones GRF
      infoInitialModules(GRF,Leq )
      isTorsionFreeSheaf GRF
      isReflexiveSheaf GRF
    Text
      This function can also be used to construct the subfan of non-equivariant cones in a Grobner fan faster.
    Example
      time GRF'= grobnerFan( module GRF, fan GRF, ideal GRF);
      time infoInitialModules( GRF', delete(Leq, listCones GRF ))
      time GRFneq = specialSubfan (GRF', Strategy =>"NonEquivariant")
      displayInformation GRFneq
  SeeAlso
    "Theoretical background: Grobner fan of a module"
    listCones
    isEquivariant
    specialSubfan
    infoInitialModules
///



doc ///
  Key
    fineGrading
    (fineGrading, Matrix)
    (fineGrading, Module)
    (fineGrading, GrobnerFan, List)
  Headline
    makes a module fine-graded 
  Usage
    phi = fineGrading A
    Q' = fineGrading Q
    Q' = fineGrading(GRF, c)
  Inputs
    A:Matrix
    Q:Module
    GRF:GrobnerFan
    c:List
      a cone in GRF
  Outputs
    phi:Matrix
      the matrix A fine-graded
    Q':Module
      the module Q fine-graded
  Description
    Text
      Given a homogeneous module $Q$ over a (multigraded) polynomial ring $S$, it returns the 
      same module but fine-graded (if the module $Q$ admits such a grading).

      For instance, if a cone in the Grobner Fan with fan @TO grobnerPolyhedralFan@ satisfies the @TO isEquivariant@ check,
      the module associated can be fine graded.
    Example
      S = QQ[x,y,z,Degrees => {{2},{1},{2}}];
      I = ideal(x,y,z);
      Q = image map(S^{{-4}, {0}}, S^{{-6}}, matrix {{y^2+z}, {x^3+ y^6}});
      GRF = grobnerFan (Q)
      Leq = equivariantCones GRF;
      Q' = degenerateModule(GRF, Leq_0)
      Q1 = fineGrading(Q')
      isHomogeneous Q1
      degrees ring Q1
      phi= fineGrading(presentation Q' )
      
  SeeAlso
    degenerateModule
    isEquivariant
    equivariantCones
    infoInitialModules
///


doc ///
  Key
    displayInformation
    (displayInformation, GrobnerFan)
  Headline
    displays a summary of the properties of a Grobner fan
  Usage
    displayInformation GRF
  Inputs
    GRF:GrobnerFan
  Description
    Text
      This function prints a summary about the properties of the degenerations of a 
      @TO GrobnerFan@ that have been computed by @TO infoInitialModules@.

      It shows the total number of modules, "modulesList"; the total of modules defining torsion-free sheaves, "torsionFreeSheaf";
      the total of modules defining reflexive sheaves, "reflexiveSheaf"; the total of modules defining vector bundles, "vectorBundle";
      the total of modules that are fine-graded and define a vector bundle, (i.e., that are guaranteed to give a toric vector bundle), "toricVB";
      and the total of modules that can be fine-graded (i.e. that satisfy the @TO isEquivariant@ test), "equivariant".

      Each of this counts is also done for each of the relevant dimension of cones in the fan. Note that the dimension of the lineality space 
      of the fan coincides with the minimum dimension appearing in the table (e.g. in the example below the lineality space has dimension 2).
    Example
      X =  toricProjectiveSpace 1
      S = ring X;
      M = image matrix{{x_0+ x_1},{x_0-x_1}}
      GRF = grobnerFan (X,M);
      displayInformation GRF
    Text
      Note that this information not only depends on the list of cones passed to @TO infoInitialModules@, but also on the construction made with @TO grobnerFan@,
      in particular in the choice of the fan taken as input. To help check if the information is affected by possible redundancies, in the case of general fans,
      use @TO hasDuplicates@.
  SeeAlso
    infoInitialModules
    isVectorBundle
    isToricVectorBundle
    isTorsionFreeSheaf
    isReflexiveSheaf
    isEquivariant
    degenerateModule
///

doc ///
  Key
    hasDuplicates
  Headline
    checks if there are repeated degenerations
  Usage
    hasDuplicates GRF
  Inputs
    GRF:GrobnerFan
      
  Outputs
    :Boolean
      true if there are two cones with the same associated module
  Description
    Text
      This function outputs true if there are repeated modules associated to cones in the set of cones of a @TO GrobnerFan@
      for which @TO infoInitialModules@ has been applied.

      If the fan of the GrobnerFan is the @TO grobnerPolyhedralFan@ then hasDuplicates will always return false, but, as 
      the objects of type Grobner Fan can be created with respect to any fan of the appropriate dimension, it can happen 
      that two cones are associated the same module.

      If hasDuplicates returns true, the information in @TO displayInformation@ is affected by this redundancies.

    Example 
      S= QQ[x,y,z,Degrees => {{2},{1},{2}}];
      I= ideal(x,y,z);
      Q = image map(S^{{-4}, {0}}, S^{{-6},{-6}}, matrix {{y^2+z, x-z}, {x^3+ y^6, 2*z^3}});
      F = fakeFan(Q)
      GRF = grobnerFan(Q, I)
      hasDuplicates GRF
      GRF' = grobnerFan(Q,F, I)
      hasDuplicates GRF'
  SeeAlso
    fakeFan


///

doc ///
  Key
    listCones
  Headline
    lists all the cones in the fan of GRF
  Usage
    listCones GRF
  Inputs
    GRF:GrobnerFan
  Outputs
    L:List
  Description
    Text
      This function outputs the list of all the cones in the fan of a Grobner fan.
    Example
      X =  toricProjectiveSpace 1;
      S = ring X;
      Q = image matrix{{x_0+ x_1},{x_0-x_1}};
      GRF = grobnerFan( X, Q)
      listCones GRF 
      rays fan GRF
  SeeAlso
    equivariantCones
    infoInitialModules
    specialSubfan
///

doc ///
  Key
    generateHomogeneousModule
    (generateHomogeneousModule, Ring, List, List)
    [generateHomogeneousModule, Random]
  Headline
    generates a homogeneous module with given shifts and degree
  Usage
    generateHomogeneousModule(S, target, source)
  Inputs
    S:Ring
      graded ring
    target:List
      degree shifts of the target
    source:List
      degree shifts of the source
    Random => ZZ
      bound for the support of the polynomials
  Outputs
    M:Module
      an homogeneous module
  Description
    Text
      This function is a source of examples for the package.

      This method creates a homogeneous map between a source and target, so the input is a (multigraded) polynomial ring, a list of shifts for the target module and the list of shifts of the source module. The option Random allows the user to set a bound on the number of monomials in the support of each 
      of the entries of the matrix (this is generally helps making the computations for the @TO grobnerPolyhedralFan@ faster).
    Example
        S =  QQ[x_0..x_4, Degrees => {{1, 0}, {1, 0}, {0, 1}, {0, 1}, {0, 1}}];

        A = generateHomogeneousModule(S, {{0,1}, {2,0}}, splice{2:{4,1}})
        
        Q = coker generateHomogeneousModule(S, splice{3:{0,0}, 1:{2,0}}, {{4,1}, {5,2}}, Random => 2)
        
        

    
///


doc ///
  Key
    saveDegeneration
    (saveDegeneration,GrobnerFan, String, String)
    (saveDegeneration, Fan, String, String)
  Headline
    saves a GrobnerFan or a Fan in a file with description text 
  Usage
    saveDegeneration(GRF, text, name)
    saveDegeneration(F, text, name)
  Inputs
    GRF:GrobnerFan
    text:String
      description of the file
    name:String
      name of the file
    F:Fan
      output of grobnerPolyhedralFan
  Description
    Text
      This function takes a @TO GrobnerFan@ or a @TO fan@ and saves it in a file with the 
      given name and description.  If the file name is "name.m2" it can be loaded directly
      and recover all the information stored (see Step 5 in @TO "VectorBundleDegenerations tutorial"@).
///

       
-* Test section *-

-- Test 0: initialModule and its current options
TEST ///
S = QQ[x,y];
M = image matrix {{x^2+y^2,x^2},{x^2-y^2,y^2}};
cv = correctionVector M;

M1 = initialModule(M,{0,1},{0,2},Correction => cv, TimeSpent => 30);

assert(instance(M1,Module));
assert(ring M1 === S);
assert(isHomogeneous M1);
assert(M1 =image(map(S^2,S^{2:{-2}},{{x^2, y^2}, {0, x^2}})))
assert(numgens M1 == 2);

M2 = initialModule(M,{-2,-1},{-2,0});
assert(M1==M2);
///

-- Test 1: moduleToIdeal
TEST ///
S = QQ[x,y];
M = image matrix {{x,y},{x^2,y^2}};
I = moduleToIdeal M;
R = ring I;

assert(instance(I,Ideal));
assert(numgens ring I == numgens S + rank ambient M);
assert(R =!= S);
assert(degrees R== {{1, 0}, {1, 0}, {0, 1}, {0, 1}} )
assert(gens I ==  matrix {{x^2*R_3+x*R_2, x^2*R_3+y^2*R_3+x*R_2+y*R_2}})
///

-- Test 2: grobnerPolyhedralFan and fakeFan
TEST ///
S = QQ[x,y];
M = image matrix {{x^2+y^2,x^2},{x^2-y^2,y^2}};

F = grobnerPolyhedralFan M;
FF = fakeFan M;

assert(instance(F,Fan));
assert(instance(FF,Fan));
assert(dim F == dim FF);
assert( F == fan (map(ZZ^4,ZZ^6,{{0, 0, 0, 0, 0, 0}, {-1, 1, 0, 0, -1, 1}, {0, 0, 0, 0, 0, 0}, {-2, -2, -1, 1, 2,2}}),map(ZZ^4,ZZ^2,{{1, 0}, {1, 0}, {0, 1}, {0, 1}}),{{1,5},{1,2},{0,2},{0,4},{3,5},{3,4}}))
assert( FF == fan (map(ZZ^4,ZZ^5,{{0, 0, 0, 0, 0}, {1, 0, 0, -1, -1}, {0, 1, 0, 3, 2}, {0, 0, 1, 1, 2}}),map(ZZ^4,ZZ^2,{{1, 0},{1, 0}, {0, 1}, {0, 1}}),{{0,2},{2,4},{3,4},{0,1},{1,3}}))

///

-- Test 3: generateHomogeneousModule 
TEST ///
S = QQ[x_0..x_4, Degrees => {{1,0},{1,0},{0,1},{0,1},{0,1}}];

A = generateHomogeneousModule(S,{{0,1},{2,0}},splice{{3,4},{4,1}},Random => 2);
assert(instance(A,Matrix));
assert(isHomogeneous A);
assert(numRows A == 2);
assert(numColumns A == 2);
assert(# terms A_(0,0)<= 2)
assert( ring A === S)
///

-- Test 4: correctionVector 
TEST ///
S = QQ[x,y];
M = image matrix {{x^2+y^2,x^2},{x^2-y^2,y^2}};
F = grobnerPolyhedralFan M;
GRF = grobnerFan(M,F);

cvM = correctionVector M;
cvF = correctionVector F;
cvG = correctionVector GRF;

assert(instance(cvM,List));
assert(cvM == cvF and cvM == cvG )
assert(#cvM == numgens S + rank ambient M);
assert(cvM == {1,1,1,1})
///

-- Test 5: isVectorBundle, isTorsionFreeSheaf and isReflexiveSheaf
TEST ///
X = toricProjectiveSpace 1;
S = ring X;
M = coker matrix{{x_0+ x_1},{x_0-x_1}};
I = ideal (x_0 +1);

assert(isVectorBundle(M,I) == false);
assert(isVectorBundle(M,I,1) == false);
assert(isVectorBundle(M,X) == 1);
assert(isVectorBundle(M,X,2) == false);

assert(isTorsionFreeSheaf(M,I, Strategy => "saturation") == true);
assert(isTorsionFreeSheaf(M,X) == true);

assert(isReflexiveSheaf(M,I, Strategy =>"radical") == false);
assert(isReflexiveSheaf(M,X) == true);
///

-- Test 6: isEquivariant on Matrix and Cone
TEST ///
Afull = id_(ZZ^2);
Azero = matrix{{0,0},{0,0}};
A  =matrix{{1,0,0},{0,1,0},{1,1,0}}

assert(isEquivariant(Afull,2) == true);
assert(isEquivariant(Azero,2) == false);
assert(isEquivariant(A,2) == true);
assert(isEquivariant(A,3) == false);

C = coneFromVData(matrix{{1,0,0},{0,1,0},{1,1,0}});
assert(isEquivariant(C,2) == true);
assert(isEquivariant(C,3) == false);
///

-- Test 7: all GrobnerFan constructors and basic getters
TEST ///
S = QQ[x,y];
M = image matrix {{x^2+y^2,x^2},{x^2-y^2,y^2}};
I = ideal(x,y);
F = grobnerPolyhedralFan M;
FF = fakeFan M

GRF = grobnerFan(M,F,I);
GRF2 = grobnerFan(M,FF);
GRF3 = grobnerFan(M,I);
GRF4 = grobnerFan M;

scan({GRF,GRF2,GRF3,GRF4}, G -> (
    assert(class G === GrobnerFan);
    assert(module G === M);
    assert(ring G === S);
    assert(instance(fan G,Fan));
    assert(instance(ideal G,Ideal));
    assert( keys G.cache == {});
));

assert(ideal GRF === I);
assert(ideal GRF2 === ideal(1_S));
assert( fan GRF2 == FF )
assert(fan (GRF) ==  F);
assert(fan (GRF3) ==  F);
assert(fan GRF4 ==  F);
///

-- Test 8: toric GrobnerFan constructor with toric variety and variety getter
TEST ///
X = hirzebruchSurface 1;
S = ring X;
M = image map(S^{{-2, -5}, {-3, -5}},S^{{-6, -8}, {-4, -6}},{{(1/10)*x_0^6*x_1^2*x_3, (4/3)*x_0^2*x_1*x_2}, {(5/2)*x_0*x_1^3*x_2^5, (8/3)*x_1*x_2^2}});
F = grobnerPolyhedralFan M;

G = grobnerFan(X,M,F);
G1 = grobnerFan(X,M);
scan( {G,G1}, GRF ->(
  assert(class GRF === GrobnerFan);
  assert(module GRF === M);
  assert(ring GRF === S);
  assert(fan GRF == F);
  assert(ideal GRF === ideal X);
  assert(variety GRF === X);
  assert(ring variety(GRF) === S);
)
)
///

-- Test 9: infoInitialModules and methods taking GrobnerFan and List
TEST ///
X = toricProjectiveSpace 1 ** toricProjectiveSpace 2;
S = ring X;
I = ideal X;

M = image(map(S^{{0,0},3:{-2,0}},S^{{-4,-1}},
    {{(3/5)*x_0*x_1^3*x_3},
     {(10/9)*x_1^2*x_2},
     {(7/3)*x_0^2*x_3},
     {(1/10)*x_0^2*x_2}}));

GRF = grobnerFan(X,M);

infoInitialModules GRF;
assert(# keys GRF.cache == 4);
assert(listCones(GRF) ==  {{}, {0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}});



-- Test the (GrobnerFan,List) overload on a fresh GrobnerFan, since the
-- current implementation deliberately does nothing once infoDegens is cached.
GRFsingle = grobnerFan(X,M,fan GRF);
infoInitialModules(GRFsingle,{{0}}, Strategy => "saturation");
assert(# keys GRFsingle.cache == 3);
MM = degenerateModule(GRFsingle,{1,2,3})
assert(MM ==cokernel(map(S^{{0, 0}, 3:{-2, 0}},S^{{-4, -1}},{{0}, {S_1^2*S_2}, {0}, {0}})));

C={1,2,3}

DM = degenerateModule(GRF,C);
assert(DM == MM );

assert(rays(GRF,C)==matrix {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}, {0, 0, 0}, {0, 0, 0}, {0, 0, 0}, {0, -1, 0}, {1, -1, 0}, {0, -1, 1}} );
assert( rays (cone(GRF,C)) == matrix {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}, {0, 0, 0}, {0, 0, 0}, {0, 0, 0}, {0, -1, 0}, {1, -1, 0}, {0, -1, 1}});
assert(dim(GRF,C)== 9);
assert(latticeInteriorPoint(GRF,C)==  {0, 0, 0, 0, 0, 0, -1, 0, 0});
assert(isEquivariant(GRF,C)== true);
assert(isVectorBundle(GRF,C) == false);
assert(isTorsionFreeSheaf(GRF,C)== false);
assert(isReflexiveSheaf(GRF,C)== false);
assert(isToricVectorBundle(GRF,C)== false);

assert(correctionVector(GRF) == {5, 4, 5, 2, 1, 3, 9, 10, 7});

-- The current fineGrading(GrobnerFan,List) overload.
FG = fineGrading(GRF,C);
Rfg = ring FG;
assert(degrees Rfg =={{1, 0, 0, 0, 0}, {0, 1, 0, 0, 0}, {0, 0, 1, 0, 0}, {0, 0, 0, 1, 0}, {0, 0, 0, 0, 1}}  )
assert(FG == cokernel(map(Rfg^{{0, 0, 0, 0, 0}, {0, 2, 1, 0, 0}, 2:{0, 0, 0, 0, 0}},Rfg^1,{{0}, {x_1^2*x_2}, {0}, {0}})));
assert(isHomogeneous FG);
///

-- Test 10: methods taking GrobnerFan after analyzeDegenerations
TEST ///
X = toricProjectiveSpace 1;
S = ring X;
M = image matrix{{x_0+ x_1},{x_0-x_1}};

GRF = grobnerFan(X,M);
displayInformation GRF

assert(# keys GRF.cache == 6)

mods = degenerateModule GRF;
use S;
assert(mods_4 ==   cokernel(map(S^2,S^{{-1}},{{x_0}, {x_0}})));
assert(#mods == #listCones GRF and # mods == 9);

vb = isVectorBundle GRF;
tf = isTorsionFreeSheaf GRF;
rf = isReflexiveSheaf GRF;
eq = isEquivariant GRF;
tvb = isToricVectorBundle GRF;
eq2 = equivariantCones GRF;

assert(# vb == 1);
assert( tf == {{}});
assert(rf == {{}});
assert(eq =={{1, 2}, {1, 3}, {0}, {1}, {0, 2}, {0, 3}} );
assert(set eq == set eq2)
assert(tvb == {});

assert(hasDuplicates GRF == false );
///

-- Test 11: equivariantCones and specialSubfan
TEST ///
      X = hirzebruchSurface 2;
      S = ring X
      degrees S
      I = ideal X
      Q = image(map(S^{2:{0, 0}, {-6, -1},{-4,-1}},S^{{-4, -2}}, matrix {{(4/9)*x_0^8*x_1^2+(2/7)*x_0^4*x_3^2+7*x_2^4*x_3^2},{(10/3)*x_0*x_1*x_2^5*x_3+x_0^3*x_2*x_3^2+(3/4)*x_0^2*x_2^2*x_3^2}, {(2/5)*x_1},{- x_3}}))
      
GRF = grobnerFan(X,Q);
F = fan GRF;

L1 = equivariantCones(F,numgens S);
L2 = equivariantCones GRF;


assert(L2 == L1 and # L1 ==47 and L1_43 == {0, 2, 4, 6, 7, 8});
scan(L2,C -> assert(isEquivariant(GRF,C) == true));
assert(# keys GRF.cache == 5);

L = listCones GRF;

SF = specialSubfan GRF;
SFn = specialSubfan(GRF,Strategy => "NonEquivariant");
SFlist = specialSubfan(GRF,take(L,2));

assert(instance(SF,GrobnerFan));
assert( fan SF ==fan (map(ZZ^8,ZZ^9,{{0, 0, 0, 0, 0, 0, 0, 0, 0}, {0, 0, 0, 0, 0, 0, 0, 0, 0}, {1, 0, 0, -1, 1, -1, 0, 0, 0}, {0, 0, 0, -3, 4, 2, -1, 0, 0}, {0, 0, 0, 0, 0, 0, 0, 0, 0}, {-1, 1, 0, -2, -9,3, 0, -1, 0}, {0, 0, 1, -10, 0, 0, -2, -1, 0}, {0, 0, 0, -7, -4, -2, -1, -1, 1}}),map(ZZ^8,ZZ^3,{{0, 1, 0}, {-1, -6, 1}, {0, 1, 0}, {-1, -4, 1}, {1, 0, 0}, {1, 0, 0}, {0, 2, 1}, {0, 0, 1}}),{{0,1,2,4,5,8},{0,1,2,6,8},{1,2,3,5,6,8},{2,3,4,5,7,8},{0,1,3,4,5,6,7,8},{0,1,2,3,4,5,6,7},{0,2,4,6,7,8},{2,3,6,7,8}}))
assert(instance(SFn,GrobnerFan));
assert (fan SFn== fan (map(ZZ^8,ZZ^9,{{0, 0, 0, 0, 0, 0, 0, 0, 0}, {0, 0, 0, 0, 0, 0, 0, 0, 0}, {1, 0, 0, -1, 1, -1, 0, 0, 0}, {0, 0, 0, -3, 4, 2, -1, 0, 0}, {0, 0, 0, 0, 0, 0, 0, 0, 0}, {-1, 1, 0, -2, -9, 3, 0, -1, 0}, {0, 0, 1, -10, 0, 0, -2, -1, 0}, {0, 0, 0, -7, -4, -2, -1, -1, 1}}),map(ZZ^8,ZZ^3,{{0, 1, 0}, {-1, -6, 1}, {0, 1, 0}, {-1, -4, 1}, {1, 0, 0}, {1, 0, 0}, {0, 2, 1}, {0, 0, 1}}),{{0,1,2,4,5,8},{0,1,2,6,8},{1,2,3,5,6,8},{2,3,4,5,7,8},{0,1,3,4,5,6,7,8},{0,1,2,3,4,5,6,7},{0,2,4,6,7,8},{2,3,6,7,8}}))
assert(SFlist == fan (map(ZZ^8,ZZ^1,{{0}, {0}, {1}, {0}, {0}, {-1}, {0}, {0}}),map(ZZ^8,ZZ^3,{{0, 1, 0}, {-1, -6, 1}, {0, 1, 0}, {-1, -4, 1}, {1, 0, 0}, {1, 0, 0}, {0, 2, 1}, {0, 0, 1}}),{{0}}));
///

-- Test 13: fineGrading(Module) on an equivariant module
TEST ///
X = toricProjectiveSpace 3;
S = ring X;
M = coker(map(S^{2:{-5}, {-4}},S^{2:{-7}},
    {{0,x_1^2},
     {0,0},
     {x_1^2*x_3,7*x_0*x_1*x_3}}));

H = fineGrading M;

assert(instance(H,Module));
assert(isHomogeneous H);
assert(numgens ring H == numgens S);
assert(degrees ring H == {{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}});
///

end
