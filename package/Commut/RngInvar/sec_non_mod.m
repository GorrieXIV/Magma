freeze;

/*
NON-MODULAR SECONDARY INVARIANTS

Gregor Kemper, Sep 2006.
Installed and somewhat hacked by Allan Steel.
*/

/*******************************************************************************
			    Hilbert Numerator
*******************************************************************************/

intrinsic HilbertNumerator(R::RngInvar) -> RngUPol
{The numerator of the Hilbert series of R, with respect to the primary
invariants}
    prim := PrimaryInvariants(R);
    H := HilbertSeries(R);
    t := Parent(H).1;
    f := Numerator(&*[1-t^TotalDegree(f): f in prim] * HilbertSeries(R));
    if Sprint(Parent(f).1) eq "$.1" then
	_<t> := Parent(f);
    end if;
    return f;
end intrinsic;

/*******************************************************************************
			    Irreducible secondaries
*******************************************************************************/

/*
Should be run when calling IrreducibleSecondaryInvariants(R) in
non-modular case. Should also be made available to the user because of
its optional arguments.
*/

IrreducibleSecondaryInvariantsNonModular:=function(R:
    primideal:="standard",returnsecs:=false,
    verb:=GetVerbose("Invariants"),linconst:="depends",blockratio:=1.0);
/*
Compute irreducible secondary invariants for a finite group in the non-modular
case. R is an invariant ring. If returnsecs is true, secondary invariants will
also be computed and returned. verb is the verbosity level. linconst is a
constant for the reciprocal cost of linear algebra. linconst := 0 means that 
the Reynolds operator is always chosen for computing invariants,
lincost := Infinity() means the linear algebra method is always chosen.
Output: 1. a sequence of minimal irreducible secondary invariants; 2. a 
sequence of polynomials in a polynomial ring with so many indeterminates as
there are irreducible secondaries, representing the secondary invariants as
products of irreducible secndaries; 3. if requiered, a sequence of secondary
invariants.
*/

    if not GroupType(R) in {"permutation group","finite matrix group"} then
        error "Group must be finite for this algorithm";
    end if;
    T0:=Cputime(); T1:=0; T2:=0;
    P:=PolynomialRing(R);
    K:=CoefficientRing(P);
    n:=Rank(P);
    G:=Group(R);
    if Characteristic(K) ne 0 and IsDivisibleBy(#G,Characteristic(K)) then
        error "This algorithm ony applies to the non-modular case";
    end if;
    prim:=PrimaryInvariants(R);
    if verb gt 0 then 
        print "Number of secondary invariants:",
	    &*[TotalDegree(f):f in prim]/#G;
    end if;
    if primideal cmpeq "standard" then
        I:=EasyIdeal(PrimaryIdeal(R));
	PI:=Generic(I);
	Iinit:=ideal<PI | [LeadingMonomial(f):
	    f in GroebnerBasis(EasyIdeal(PrimaryIdeal(R)))]>;
    else
        I:=EasyIdeal(primideal);
	PI:=Generic(I);
	Iinit:="don't use";
    end if;
    H<t>:=HilbertSeries(R);
    // H<t>:=Numerator(&*[1-t^TotalDegree(f): f in prim] * HilbertSeries(R));
    H<t>:=HilbertNumerator(R);
    if verb in {1,2} then print "Hilbert series numerator:",H; end if;
    
    // initialize
    invsec:=[P|]; // irreducible secondaries
    ninvsec:=[PI|]; // their normal forms w.r.t. I; elements of PI
    sec:= [P!1]; // secondary invariants (if required by returnsecs)
    nsec:=[PI!1]; // their normal forms w.r.t. I; elements of PI
    sect:=[K!1]; // their representation as products of irreducible secs
    Pt:=K; // the polynomial ring in which elts from sect live

    for d:=1 to Degree(H) do
        if Coefficient(H,d) eq 0 then continue d; end if;
        if verb gt 1 then
	    print "Do secondaries of degree",d;
	    Td:=Cputime();
	end if;
	if verb gt 2 then print "H =",H; end if;
	if verb gt 1 then T:=Cputime(); end if;
	prods:={t*Pt.i: t in sect, i in [1..#invsec] |
	    WeightedDegree(t) + WeightedDegree(Pt.i) eq d};
	prods:=SetToSequence(prods);
	bs:=Round(blockratio*Coefficient(H,d)+1);
	// blocksize; so many products of old secondaries will be dealt
	// with in one cohort ("block"); value is set heuristically
	blocks:=[[prods[i*bs+j]: j in [1..bs]]: i in [0..(#prods div bs)-1]]
	    cat [[prods[j]: j in [bs*(#prods div bs)+1..#prods]]];
	if verb gt 1 then
	    print "Time for listing products of old secondaries:",Cputime()-T;
	    T:=Cputime(); // Not sure this will ever take much time
	end if;
	nsecd:=[]; // the normal forms of secodaries of degree d
	IndentPush();
	for b in blocks do
	    i:=Position(blocks,b);
	    if verb gt 2 then
	        print "Do product",bs*(i-1)+1,"...",bs*i,"of",
	            #prods,". Currently have",#nsecd,"invariants from",
		    Coefficient(H,d),"of degree",d;
	    end if;
	    cand:=[]; tcand:=[]; ijcand:=[];
	    if verb gt 2 then T1:=Cputime(); end if;
	    for t in b do
	        for s in Factorization(t) do
	            i:=Position(sect,t div s[1]);
		    if i eq 0 then continue s; end if;
		    j:=Position([Pt.k: k in [1..Rank(Pt)]],s[1]);
		    break;
		end for;
		c:=nsec[i]*ninvsec[j];
	        Append(~cand,c);
		Append(~ijcand,[i,j]);
		// to produce the actual secondary if needed
		Append(~tcand,t);
	    end for;
	    if verb gt 2 then
	        print "Time for products of normal forms:",Cputime()-T1;
		T1:=Cputime();
	    end if;
	    //cand:=[NormalForm(f,I): f in cand];
// printf "d: %o, cand len: %o\n", d, #cand; time
	    cand:=NormalForm(cand,I);
	    if verb gt 2 then
	        print "Time for normal forms:",Cputime()-T1;
	    end if;
	    l:=[i: i in [1..#cand] | cand[i] ne 0];
// printf "non-zero l (%o): %o\n", #l, l;
	    cand:=[cand[i]: i in l];
	    tcand:=[tcand[i]: i in l];
	    ijcand:=[ijcand[i]: i in l];
	    if verb gt 2 then T1:=Cputime(); end if;
	    l:=HomogeneousModuleTestBasis([PI.1^(d+1)],[PI!1] cat nsecd,cand);
// printf "HomogeneousModuleTestBasis l (%o): %o\n", #l, l;
	    if verb gt 2 then
	        print "Time for selecting linearly independent:",Cputime()-T1;
	    end if;
	    nsecd:=nsecd cat [cand[i]: i in l];
	    nsec:=nsec cat [cand[i]: i in l];
	    sect:=sect cat [tcand[i]: i in l];
	    if returnsecs then
	        ijcand:=[ijcand[i]: i in l];
		if verb gt 2 then T1:=Cputime(); end if;
		sec:=sec cat [sec[p[1]]*invsec[p[2]] : p in ijcand];
	        if verb gt 2 then
		    print "Time for forming secondaries:",Cputime()-T1;
		end if;
	    end if;
	    if #nsecd eq Coefficient(H,d) then break; end if;
	end for;
	IndentPop();
	if verb gt 1 then print "Time for all blocks:",Cputime()-T; end if;
	if verb gt 2 then print ""; end if;
	if #nsecd eq Coefficient(H,d) then
	    if verb gt 1 then print "Found secondaries of degree",d; end if;
	    if verb gt 2 then print ""; end if;
	    continue d;
	end if;
	
	m:=Coefficient(H,d)-#nsecd;
	if verb gt 1 then
	    print "Need to find",m,"new invariants of degree",d;
	end if;
	if not linconst cmpeq "depends" then C:= linconst;
	elif Type(K) eq Type(GF(2)) then C:=50.0;
	elif K cmpeq Rationals() then C:=10.0;
	else C:=0.1;
	end if;
	// These settings for the " linear algebra constant" are pretty
	// arbitrary. Same for setting the probablity of finding a good
	// invariant from applying the Reynolds
	prob:=0.3;
	if Binomial(n+d-1,n-1)^2 gt C*m*#G/#Generators(G)/prob then
	// use the Reynolds operator for producing invariants
	    if verb gt 1 then
	        "Use Reynolds operator";
		T1:=Cputime();
	    end if;

	    if 1 eq 1 and Iinit cmpne "don't use" then
		mons:=MonomialsOfDegree(P,d, ChangeUniverse(Basis(Iinit), P));
	    else
		mons:=MonomialsOfDegree(P,d);
		if Iinit cmpne "don't use" then
		    mons:=[t: t in mons | not PI!t in Iinit];
		end if;
		mons:=SetToSequence({t: t in mons});
	    end if;

	    // No idea why, but this sometimes brings mons in a luckier order
	    if verb gt 1 then 
	        "Time for computing monomials:",Cputime()-T1;
	        "Number of monomials:",#mons;
		T1:=Cputime();
	    end if;
	    IndentPush();
	    for t in mons do
	        if verb gt 2 then
		    print "Try",Position(mons,t),"th monomial of",#mons,
		        ". Currently have",#nsecd,"invariants from",
		        Coefficient(H,d),"of degree",d;
		    T2:=Cputime();
		end if;
		if Type(G) eq GrpPerm then
		    cand:=&+Orbit(G,t);
		else cand:=ReynoldsOperator(t,G);
		end if;
		if verb gt 2 then
		    print "Reynolds time:",Cputime()-T2;
		    T2:=Cputime();
		end if;
		// artificially use normal form of sequence
		ncand:=NormalForm([PI!cand],I)[1];
		// ncand:=NormalForm(PI!cand,I);
		if ncand eq 0 then
		    if verb gt 2 then
		        print "Time for testing invariant:",Cputime()-T2;
		    end if;
		    continue t;
		end if;
		tr:=HomogeneousModuleTest([PI.1^(d+1)],[PI!1] cat nsecd,ncand);
		if verb gt 2 then
		    print "Time for testing invariant:",Cputime()-T2;
		end if;
		if not tr then
		    scale := 1/LeadingCoefficient(cand);
		    if not IsOne(scale) then
			cand := scale * cand;
			ncand := scale * ncand;
		    end if;
		    Append(~invsec,cand);
		    Append(~ninvsec,ncand);
		    Append(~nsec,ncand);
		    Append(~nsecd,ncand);
		    if returnsecs then Append(~sec,cand); end if;
		    if Coefficient(H,d) eq #nsecd then
		        if verb gt 2 then
			    print "Have",#nsecd,"invariants from",
			        Coefficient(H,d),"of degree",d;
			end if;
		        break;
		    end if;
		end if;
	    end for;
	    IndentPop();
	    if verb gt 1 then
	        print "Time for Reynolds applications:",Cputime()-T1;
	    end if;
	else
	// Use linear algebra to produce invariants
	    if verb gt 1 then T1:=Cputime(); end if;
	    inv:=InvariantsOfDegree(R,d);
	    if verb gt 1 then
	        print "Time for homogeneous invariants:",Cputime()-T1;
		T1:=Cputime();
	    end if;
	    //ninv:=[NormalForm(PI!f,I): f in inv];
	    ninv:=NormalForm([PI!f: f in inv],I);
	    inv:=[inv[i]: i in [1..#inv] | ninv[i] ne 0];
	    ninv:=[f: f in ninv | f ne 0];
	    IndentPush();
	    l:=HomogeneousModuleTestBasis([PI.1^(d+1)],[PI!1] cat nsec,ninv);
	    IndentPop();
	    invsec:=invsec cat [inv[i]: i in l];
	    ninvsec:=ninvsec cat [ninv[i]: i in l];
	    nsec:=nsec cat [ninv[i]: i in l];
	    nsecd:=nsecd cat [ninv[i]: i in l];
	    if returnsecs then
	        sec:=sec cat [inv[i]: i in l];
	    end if;
	    if verb gt 1 then
	        print "Time for picking new invariants:",Cputime()-T1;
	    end if;
	end if;
	if verb gt 2 then
	    print "Have",#nsecd,"invariants from",Coefficient(H,d),
	        "of degree",d;
	end if;
	if #nsecd ne Coefficient(H,d) then
	    error "Didn't get the correct number of invariants";
	end if;
	if #sect eq 1 then
	    Pt:=PolynomialRing(K,[TotalDegree(g): g in invsec]);
	    sect:=[Pt!1] cat [Pt.i: i in [1..#ninvsec]];
	elif #nsec gt #sect then
	    Pt0:=Pt;
	    Pt:=PolynomialRing(K,[TotalDegree(g): g in ninvsec]);
	    phi:=hom<Pt0->Pt | [Pt.i: i in [1..Rank(Pt0)]]>;
	    sect:=[phi(t): t in sect] cat [Pt.i: i in [Rank(Pt0)+1..#ninvsec]];
	end if;
	if verb gt 1 then print "Time for degree",d,":",Cputime()-Td; end if;
	if verb gt 2 then print ""; end if;
    end for;

    if not assigned R`IrreducibleSecondaryInvariants then
        R`IrreducibleSecondaryInvariants:=invsec;
    end if;
    if not assigned R`SymbolicSecondaryInvariants then
        R`SymbolicSecondaryInvariants:=sect;
    end if;

    if returnsecs then
        if not assigned R`SecondaryInvariants then
	    R`SecondaryInvariants:=sec;
	end if;
	return invsec,sect,sec;
    else
        return invsec,sect;
    end if;
end function;

/*
Should be run when calling SecondaryInvariants(R) in
non-modular case. Should also be made available to the user because of
its optional arguments.
*/
intrinsic SecondaryInvariantsNonModular(R::RngInvar:
    primideal:="standard",verb:=GetVerbose("Invariants"),
    linconst:="depends",blockratio:=1.0
) -> [], []
{Compute secondary invariants for an invariant ring of a finite group in
the non-modular case.}

/*
Compute secondary invariants for a finite group in the non-modular case.
Input as in IrreducibleSecondaryInvariantsNonModular. Output: 1. sequence of
secondary invariants; 2. a sequence giving their representation as products of
irreducible secondaries (see IrreducibleSecondaryInvariantsNonModular)
*/

    invsec,sect,sec:=IrreducibleSecondaryInvariantsNonModular(R:
        primideal:=primideal,returnsecs:=true,verb:=verb,linconst:=linconst,
	blockratio:=blockratio);

    return sec,sect;
end intrinsic;

intrinsic IrreducibleSecondaryInvariants(R::RngInvar:
    primideal:="standard",
    verb:=GetVerbose("Invariants"),linconst:="depends",blockratio:=1.0) -> []
{Compute irreducible secondary invariants for S}

    if assigned R`IrreducibleSecondaryInvariants then
        return R`IrreducibleSecondaryInvariants;
    end if;

    if IsModular(R) then
	return InternalIrreducibleSecondaryInvariants(R);
    end if;

    IS := IrreducibleSecondaryInvariantsNonModular(
	R: primideal:=primideal,linconst:=linconst,blockratio:=blockratio
    );
    return IS;

end intrinsic;
