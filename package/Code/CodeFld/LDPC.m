freeze;

intrinsic TannerGraph(C::Code) -> Grph
{For an LDPC code C, return its Tanner graph. If there are n
variables and m checks, then the graph has n+m nodes,
the first n of which are the variable nodes.}
    require IsLDPC(C) : "Must be an LDPC code";

    H := LDPCMatrix(C);
    m := Nrows(H);
    n := Ncols(H);
    Gph := Graph<n+m| { <n+i, { j : j in Support(H, i) }> 
					    : i in [1..m] } >;
    return Gph;
end intrinsic;

intrinsic LDPCGirth(C::Code) -> RngIntElt
{For an LDPC code C, return the girth of its Tanner graph.}
    require IsLDPC(C) : "Must be an LDPC code";

    return Girth(TannerGraph(C));
end intrinsic;

intrinsic LDPCCode(H::MtrxSprs) -> Code
{Given a sparse binary matrix H, return the LDPC code which 
has H as its parity check matrix.}
    require CoefficientRing(H) eq GF(2) : "Must be binary";

    C := Dual(LinearCode(Matrix(H)));
    AssignLDPCMatrix(~C, H);

    return C;
end intrinsic;
 
intrinsic GallagerCode(n::RngIntElt,a::RngIntElt,b::RngIntElt) -> Code
{Return a random (a,b)-regular LDPC code of length n, using
Gallager's original method of construction.};

    requirege n, 1;
    requirege a, 1;
    requirege b, 1;
    require IsZero(n mod a) : "a must divide n";

    F := GF(2);

    M := ZeroMatrix(GF(2), Ceiling(n/a), n);
    for i in [1..Ceiling(n/a)] do
        for j in [(i-1)*a+1..Min(n,i*a)] do
            M[i][j] := 1;
        end for;
    end for;

    S := Sym(n);
   
    G := M;
    for j in [1..b-1] do
        G := VerticalJoin(G, M*PermutationMatrix(F, Random(S)) );
    end for;

    C := Dual(LinearCode(G));
    AssignLDPCMatrix(~C, SparseMatrix(G));
    return C;
end intrinsic;


intrinsic MargulisCode(p::RngIntElt)-> Code
{Return the (3,6)-regular binary LDPC code of length 2(p^3-p)
using the group-based construction of Margulis};

    requirege p, 2;
    require IsPrime(p) : "p must be prime";

    Z := Integers();
    A := Matrix(Z, 2,2, [1,2,0,1]);
    B := Matrix(Z, 2,2, [1,0,2,1]);

    G := SL(2, p);
    S1 := {G| A^2, A*B*A^-1, B };
    S2 := {G| A^-2, A*B^(-1)*A^-1, B^-1};

    verts := {@ <g, i> : g in G, i in [1..3] @};
    Gph := Graph<verts| 
            { < <g, 1>, { <g*s, 3> : s in S1 }> : g in G},
            { < <g, 2>, { <g*s, 3> : s in S2 }> : g in G} >;

        //first 2#G represent the check nodes
    H := SparseMatrix(GF(2), #G, 2*#G,
        [ <v[2]-2*#G, v[1], 1>
            where v := Sort([Index(TerminalVertex(e)),Index(InitialVertex(e))])
                                                : e in Edges(Gph) ] );

    C := Dual(LinearCode(Matrix(H)));
    AssignLDPCMatrix(~C, H);

    return C;
end intrinsic;


intrinsic RegularLDPCEnsemble(n::RngIntElt, a::RngIntElt, b::RngIntElt)->Code
{Return a random code from the ensemble of (a,b)-regular binary LDPC codes.};

    require a gt 1 and b gt 1 : "Weights must be greater than 1";
    requirege n,1;
    require IsDivisibleBy(a*n, b) : "No regular LDPC code exists with those parameters";

    Sa := [ 0 : i in [1..a-1]] cat [1];
    Sb := [ 0 : i in [1..b-1]] cat [1];

    return IrregularLDPCEnsemble(n, Sa, Sb);
end intrinsic;


intrinsic IrregularLDPCEnsemble(n::RngIntElt, Sc::SeqEnum, 
                                           Sv::SeqEnum) -> Code
{Given (unnormalized) degree distributions for check and vertex weights,
return an LDPC code from the corresponding ensemble
of length n.
Note that the distributions will not be
matched perfectly unless everything is in complete balance.}

    Univs := { FldRe, FldRat, RngInt };
    requirege n,1;
    require Type(Universe(Sv)) in Univs and Type(Universe(Sc)) in Univs : 
       "Input sequences must be over the reals, the rationals, or the integers";

	//i implemented this with the inputs round the other way, so
	//this is just a switch hack..
    RowPercs := Sv;
    ColPercs := Sc;

    // We know the number of columns, so first work out the column weight
    // distribution that we will use.  Each potential weight w_i will get
    // at least Floor(n*p_i) columns, and may get one more if there are
    // extras, with priority going to those with larger fractional values
    // of n*p_i.
    ColSum := &+ColPercs;
    NormCols := [ c/ColSum : c in ColPercs ];	// normalised proportions
    cdist := [ Floor(n*p) : p in NormCols ];
    needed := n - &+cdist;
    if needed gt 0 then
	// sort by fractional parts and take the largest needed values
	remainders := [ <n*NormCols[w] - cdist[w], w> : w in [1 .. #NormCols] ];
	remainders := Reverse(Sort(remainders));
	extra := [ t[2] : t in remainders[[1..needed]] ];
	for x in extra do
	    cdist[x] +:= 1;
	end for;
    end if;
    assert &+cdist eq n;

    // An occupied position is called a "socket" in the following, mostly
    // abbreviated to "sock".
    check_weights := &cat[ [ w : i in [1..cdist[w]] ] : w in [1..#cdist] ];
    CheckSocks := &cat[
	[ v : i in [1..check_weights[v]] ] : v in [1..#check_weights]
    ];
    Num_Socks := #CheckSocks;

    // Now assign each socket to a row ("variable").  This is more
    // complicated than the column case since it is the number of sockets
    // that are limited, not the number of rows, and it may not be possible
    // to do a proper packing.  Here we use weighted probabilities for the
    // rows, reflecting the probability of an occupied socket belonging to
    // a row of that weight.
    rowinds := [1..#RowPercs];
    WeightedRowSum := &+[ RowPercs[w]*w : w in rowinds ];
    NormRows := [ RowPercs[w]*w/WeightedRowSum : w in rowinds ];
    rdist := [ Floor(Num_Socks*NormRows[w]/w) : w in rowinds ];
    needed := Num_Socks - &+[ rdist[w]*w : w in rowinds ];
    if needed gt 0 then
	// sort by fractional parts
	remainders := [ <Num_Socks*NormRows[w] - w*rdist[w], w> : w in rowinds ];
	remainders := Reverse(Sort(remainders));
	extra := [];
	for t in remainders do
	    w := t[2];
	    if w le needed then
		Append(~extra, w);
		needed -:= w;
	    end if;
	end for;

	// Give any unhandled remainder its own row.  I'm not in love
	// with this option, but nor am I that fond of alternatives.
	// Frankly, callers should spend a little effort to make the
	// parameters exact enough to never be needed.
	if needed gt 0 then
	    assert needed le #rowinds;
	    Append(~extra, needed);
	end if;
	for x in extra do
	    rdist[x] +:= 1;
	end for;
    end if;

    var_weights := &cat[ [ w : i in [1..rdist[w]] ] : w in [1..#rdist] ];
    VarSocks := &cat[
	[ v : i in [1..var_weights[v]] ] : v in [1..#var_weights]
    ];
    Num_Vars := #var_weights;

        //now select a random permutation, but hack it to avoid redundancy
    S := Sym(Num_Socks);
    pm := Random(S);
    repeat
        changed := false;

	for v in [1..Num_Vars] do
	    cols := {};
	    vpos := { k : k in [1..Num_Socks] | VarSocks[k] eq v };
	    for k in vpos do
		if CheckSocks[k^pm] in cols then
		    newpos := Random({1..Num_Socks} diff vpos);
		    pm := (S!(k, newpos))*pm;
		    changed := true;
		end if;
		Include(~cols, CheckSocks[k^pm]);
	    end for;
	end for;

    until not changed;

    H := SparseMatrix(GF(2), Num_Vars, n,
              [ <VarSocks[i], CheckSocks[i^pm], 1> : i in [1..Num_Socks] ]);

    C := Dual(LinearCode(Matrix(H)));
    AssignLDPCMatrix(~C, H);

    return C;
end intrinsic;


intrinsic IsRegularLDPC(C::Code) -> BoolElt, RngIntElt,RngIntElt
{Returns true if C is an LDPC code and has regular column and
row weights. If true, the row and column weights are also returned.};

    require IsLDPC(C) : "C must be an LDPC code";

    H := LDPCMatrix(C);

    RW := RowWeights(H);
    RWs := Seqset(RW);
    CW := ColumnWeights(H);
    CWs := Seqset(CW);
    if #RWs ne 1 or #CWs ne 1 then
	return false,0,0;
    else
	return true, Representative(RWs),Representative(CWs);
    end if;

end intrinsic;
    
    //format is < threshold, [ <v_deg, p>, ... ], [ <c_deg, p>,...] >
DegreeDistributions := [
<0.9114,
[ <2, 0.38354>, <3, 0.04237>, <4, 0.57409> ],
[ <5, 0.24123>, <6, 0.75877> ] >,
<0.9194,
[ <2, 0.32660>, <3, 0.11960>, <4, 0.18393>, <5, 0.36988> ],
[ <6, 0.78555>, <7, 0.21445> ] >,
<0.9304,
[ <2, 0.33241>, <3, 0.24632>, <4, 0.11014>, <6, 0.31113>],
[ <6, 0.76611>, <7, 0.23389> ] >,
<0.9424,
[ <2, 0.31570>, <3, 0.41672>, <7, 0.43810> ],
[ <6, 0.43810>, <7, 0.56190> ] >,
<0.9497,
[ <2, 0.30013>, <3, 0.28395>, <8, 0.41592> ],
[ <6, 0.22919>, <7, 0.77081> ] >,
<0.9540,
[ <2, 0.27684>, <3, 0.28342>, <9, 0.43974> ],
[ <6, 0.01568>, <7, 0.85244>, <8, 0.13188> ] >,
<0.9558,
[ <2, 0.25105>, <3, 0.30938>, <4, 0.00104>, <10,0.43853> ],
[ <7, 0.63676>, <8, 0.36324> ] >,
<0.9572,
[ <2, 0.23882>, <3, 0.29515>, <4, 0.03261>, <11,0.43342> ],
[ <7, 0.43011>, <8, 0.56989> ] >,
<0.9580,
[ <2, 0.24426>, <3, 0.25907>, <4, 0.01054>, <5, 0.05510>, <8, 0.01455>,
  <10,0.01275>, <12,0.40373> ],
[ <7, 0.25475>, <8, 0.73438>, <9, 0.01087> ] >,
<0.9622,
[ <2, 0.23802>, <3, 0.20997>, <4, 0.03492>, <5,0.12015>,<7,0.01587>,
  <14,0.00480>, <15,0.37627> ],
[ <8, 0.98013>, <9, 0.01987> ] >,
<0.9649,
[ <2, 0.21991>, <3, 0.23328>, <4, 0.02058>, <6, 0.08543>, <7, 0.06540>,
  <8, 0.04767>, <9, 0.01912>, <19,0.08064>, <20,0.22798> ],
[ <8, 0.64854>, <9, 0.34747>, <10,0.00399> ] >,
<0.9690,
[ <2, 0.19606>, <3, 0.24039>, <6, 0.00228>, <7, 0.05516>, <8, 0.16602>,
  <9, 0.04088>, <10,0.01064>, <28,0.00221>, <30,0.28636> ],
[ <8, 0.00749>, <9, 0.99101>, <10,0.00150> ] >,
<0.9718,
[ <2, 0.17120>, <3, 0.21053>, <4, 0.00273>, <7, 0.00009>, <8, 0.15269>,
  <9, 0.09227>, <10,0.02802>, <15,0.01206>, <30,0.07212>, <50,0.25830> ],
[ <9, 0.33620>, <10,0.08883>, <11,0.57497> ] >
			];

intrinsic GoodLDPCEnsemble(i::RngIntElt) -> FldReElt, SeqEnum[FldReElt], SeqEnum[FldReElt]
{Returns the published threshold and density distributions of good
irregular LDPC code ensembles which have been published in the 
literature. They occur in no particular order.};

    requirege i, 1;
    require i le #DegreeDistributions : "Index",i,"is greater than the number of ensembles in the database -",#DegreeDistributions;

    V := DegreeDistributions[i];
    threshold := V[1];

    weights := V[2];
    Sv := [0.0 : i in [1..weights[#weights][1]]];
    for w in weights do
	Sv[w[1]] := w[2];
    end for;

    weights := V[3];
    Sc := [0.0 : i in [1..weights[#weights][1]]];
    for w in weights do
	Sc[w[1]] := w[2];
    end for;

    return threshold, Sv, Sc;
end intrinsic;

//////////////////////////////////////////////////////////
//this is the density evolution functions
//for the binary symmetric channel

//Actually not 100% sure about these irregular functions,
//so rather than feeding the regular ones into it (like it should be)
//i'll leave them seperate for the moment...

intrinsic DensityEvolutionBinarySymmetric(Sv::SeqEnum[FldReElt], Sc::[FldReElt],
						    p0::FldReElt) -> BoolElt
{Evolve the ensemble of irregular LDPC codes on the binary
symmetric channel
using probability p0, determining if p0 lies below the
threshold.};

    require p0 gt 0 and p0 le 1 : "p0 must define a valid channel";
    //requirege dv, 2;
    //requirege dc, dv;
    require {x ge 0 : x in Sc cat Sv} eq {true}: "Densities must be non-negative";
    require &+Sc gt 0 and &+Sv gt 0 : "Distributions must be non-zero";
    require IsZero(Sc[1]) and IsZero(Sv[1]) : "1-weights must be zero";

    incr := 0.00001;
    MaxStationary := 200;
    Stationary := 0;
    NextTarget := 100;

    totv := &+Sv;
    Sv := [ x/totv : x in Sv];
    totc := &+Sc;
    Sc := [ x/totc : x in Sc];

    pl := p0;
    while true do
	pl1 := pl;
	pl := 0.0;
	c_val1 := &+[ Sc[i]* (1+(1-2*pl1)^(i-1)) : i in [2..#Sc]];
	c_val2 := &+[ Sc[i]* (1-(1-2*pl1)^(i-1)) : i in [2..#Sc]];
	
	pl := &+[ Sv[i] *( p0 - p0*((1/2)*(c_val1))^(i-1)
			 + (1-p0)*((1/2)*(c_val2))^(i-1) ) : i in [2..#Sv]];

	    //is it tending to zero?
	    //will determine by chooing an increment, then noting
	    //how many iterations go past until it decreases by that
	    //increment.
	if pl lt NextTarget then
	    NextTarget := pl - incr;
	    if NextTarget le 0 then
		return true;
	    end if;
	    Stationary := 0;
	else
	    Stationary +:= 1;
	    if Stationary ge MaxStationary then
		return false;
	    end if;

	end if;

    end while;
end intrinsic;


intrinsic LDPCBinarySymmetricThreshold(Sv::SeqEnum[FldReElt], Sc::SeqEnum[FldReElt]
					: Precision := 0.0001) -> FldReElt
{Determine the threshold over the binary symmetric channel of 
the irregular LDPC ensemble.};

    require {x ge 0 : x in Sc cat Sv} eq {true}: "Densities must be non-negative";
    require &+Sc gt 0 and &+Sv gt 0 : "Distributions must be non-zero";
    require IsZero(Sc[1]) and IsZero(Sv[1]) : "1-weights must be zero";

	//do divide and conquer to find the threshold
    epL := 0.01;
    while not DensityEvolutionBinarySymmetric(Sv, Sc, epL) do
	epL /:= 2;
    end while;

    epU := 2*epL;
    while DensityEvolutionBinarySymmetric(Sv, Sc, epU) do
	epU *:= 2;
    end while;

    while epU - epL ge Precision do
	epM := (epL + epU) / 2;
	if DensityEvolutionBinarySymmetric(Sv, Sc, epM) then
	    epL := epM;
	else
	    epU := epM;
	end if;
    end while;

    return epL;
end intrinsic;


intrinsic DensityEvolutionBinarySymmetric(dv::RngIntElt, dc::RngIntElt, 
						    p0::FldReElt) -> BoolElt
{Evolve the ensemble of (v,c)-regular LDPC codes on the binary
symmetric channel
using probability p0, determining if p0 lies below the
threshold.};

    require p0 gt 0 and p0 le 0.5 : "p0 must define a valid channel";
    requirege dv, 2;
    requirege dc, dv;

    incr := 0.00001;
    MaxStationary := 200;
    Stationary := 0;
    NextTarget := 100;

    pl := p0;
    while true do
	pl1 := pl;
	pl := p0 - p0*((1/2)*(1+(1-2*pl1)^(dc-1)))^(dv-1)
	     + (1-p0)*((1/2)*(1-(1-2*pl1)^(dc-1)))^(dv-1);

	    //is it tending to zero?
	    //will determine by chooing an increment, then noting
	    //how many iterations go past until it decreases by that
	    //increment.
	if pl lt NextTarget then
	    NextTarget := pl - incr;
	    if NextTarget le 0 then
		return true;
	    end if;
	    Stationary := 0;
	else
	    Stationary +:= 1;
	    if Stationary ge MaxStationary then
		return false;
	    end if;

	end if;

    end while;
end intrinsic;

intrinsic LDPCBinarySymmetricThreshold(dv::RngIntElt, dc::RngIntElt 
					: Precision := 0.0001) -> FldReElt
{Determine the threshold over the binary symmetric channel of 
the (dv,dc)-regular LDPC ensemble.};
    requirege dv, 2;
    requirege dc, dv;

	//do divide and conquer to find the threshold
    epL := 0.01;
    while not DensityEvolutionBinarySymmetric(dv, dc, epL) do
	epL /:= 2;
    end while;

    epU := 2*epL;
    while DensityEvolutionBinarySymmetric(dv, dc, epU) do
	epU *:= 2;
    end while;

    while epU - epL ge Precision do
	epM := (epL + epU) / 2;
	if DensityEvolutionBinarySymmetric(dv, dc, epM) then
	    epL := epM;
	else
	    epU := epM;
	end if;
    end while;

    return epL;
end intrinsic;

intrinsic LDPCEnsembleRate(Sv::SeqEnum[FldReElt], Sc::SeqEnum[FldReElt])->FldReElt
{Return the rate of codes in an LDPC ensemble defined by the 
given density distributions. Note that this function just
weights the input densities, so it may give results
greater than 1.};
    require {x ge 0 : x in Sc cat Sv} eq {true}: "Densities must be non-negative";
    require &+Sc gt 0 and &+Sv gt 0 : "Distributions must be non-zero";
    require IsZero(Sc[1]) and IsZero(Sv[1]) : "1-weights must be zero";

	//first normalize
    totv := &+Sv;
    Sv := [x/totv : x in Sv];
    totc := &+Sc;
    Sc := [x/totc : x in Sc];

    weightv := &+[ Sv[i] * i : i in [1..#Sv]];
    weightc := &+[ Sc[i] * i : i in [1..#Sc]];

    return weightv / weightc;
end intrinsic;

intrinsic LDPCEnsembleRate(v::RngIntElt, c::RngIntElt)->FldReElt
{Return the rate of a (v,c)-regular LDPC code.
Note that this function just weights the input densities, 
so it may give results greater than 1.};
    requirege v, 2;
    requirege c, v;
    Sv := [0.0 : i in [1..v-1]] cat [1.0];
    Sc := [0.0 : i in [1..c-1]] cat [1.0];
    return LDPCEnsembleRate(Sv, Sc);
end intrinsic;
