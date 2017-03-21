freeze;
 
///////////////////////////////////////////////////////////////////////
// make_cydb.m
///////////////////////////////////////////////////////////////////////

/*
This is an attempt to list, in a reasonably systematic way, Calabi--Yaus
that have a single curve in their basket.

We do NOT copy the K3/Fano method of enumerating great lists of baskets
since there are no known bounds on such lists (and in any case they
would have to be huge).

Notation
--------
	B = basket
	C = unique curve in the basket
	r = tranverse index of C
	t = index of C
	Bp = points in B

	u = u(B) = sum of indexes in Bp and r

Method
------
We decide in advance values of p1 = h^0(A) and p2 = h^0(2A) that
we are interested in.

The parameter u is the main bounding parameter we use to
guide the search: we work by increasing u = 2,3,...
This also bounds t.

For each u:
    -- work through r = 2..u
    for each r:
	-- find finite number of possible tranverse types of C
	-- find finite number of possible t
	-- find finite number of necessary point baskets that demand t
	-- find finite number of optional dissident points
	-- find finite number of isolated points
	-- combine all the possibilities above into a basket B with u(B) = r
	for each B:
	    -- find values of N that give integral Hilbert series  ?? infinite
	    for each N:
		-- make a fano X
		-- if X has lowish codimension then print it to a file.

This method involves considerable waste.  It regularly recalculates
lists of possible point singularities.  But it never holds very much
information at any one time.
*/

forward calc_u,diss_at_most,isol_sings;
intrinsic Main(u::RngIntElt,p1::RngIntElt,p2::RngIntElt)
{}
    filename := "/home/gavin/Winter2003/GrdRngNew/Examples/main_test";
    maxc := 5;
    SetLogFile(filename);
    for r in [2..u] do
print "==========================",r;
	B1 := Step1(r,u);	
	// list of baskets with nec dissident pts curves with t assigned
// at this point the denom of degC is bounded
	for b in B1 do
	    ub := calc_u(b);
	    C := Curves(b)[1];
	    C`d := 1 / (TransverseIndex(C) * Index(C));		// THINK
	    C`N := 0;
	    C`raw := false;
	    for k in [0..u-ub] do
		extra_diss := diss_at_most(C,k);
		for Pdiss in extra_diss do
		    isol := isol_sings(u-ub-calc_u(Pdiss));
print "---------------- #isol =",#isol;
		    for Pisol in isol do
print "doing",Pisol;
			B := Basket(Points(b) cat Points(Pdiss)
						cat Points(Pisol),[C]);
print "^";
			N0,delN := FindN(p1,p2,B,1);
print "^";
// print "FindN:",N0,delN;
			for N in [N0-delN*3..N0+delN*3 by delN] do
print "^^^^^^^^^^^^",N;
			    ChangeN(~B,N,1);
// THINK:  i haven't yet found the degree of C
			    X := CalabiYau(p1,p2,B);
			    if Codimension(X) le maxc
				    and CheckCodimension(X) then
				X;
			    end if;
			end for;
		    end for;
		end for;
	    end for;
	end for;
    end for;
end intrinsic;

function diss_at_most(C,k)
    result := [ EmptyBasket() ];
    poss := PossibleSimpleCanonicalDissidentPoints(C);
    inds := [ Index(p) : p in poss ];
    if #inds eq 0 then
	return result;
    end if;
    R := PolynomialRing(Rationals(),inds);
    for j in [2..k] do
	combs := [ Exponents(m) : m in MonomialsOfWeightedDegree(R,j) ];
	result cat:=
		[ Basket(&cat[ [poss[i] : j in [1..E[i]]] : i in [1..#poss]])
			: E in combs ];
    end for;
    return result;
end function;

function isol_sings(k)
    result := [ Parent(EmptyBasket()) | ];
    poss := &cat[ IsolatedGorensteinSingularitiesOfIndex(r) : r in [2..k] ];
    inds := [ Index(p) : p in poss ];
    if #inds eq 0 then
	return result;
    end if;
    R := PolynomialRing(Rationals(),inds);
    combs := [ Exponents(m) : m in MonomialsOfWeightedDegree(R,k) ];
    result cat:= [ Basket(&cat[ [poss[i] : j in [1..E[i]]] : i in [1..#poss]])
			: E in combs ];
    return result;
end function;

intrinsic Step1(r::RngIntElt,u::RngIntElt) -> SeqEnum
{}
    baskets := [ PowerStructure(GRBskt) | ];
    if IsEven(r) then
	half := Integers()!(r/2);
    else
	half := Integers()!((r-1)/2);
    end if;
    trans_types := [ Point(r,[a,r-a]) : a in [1..half] | GCD(a,r) eq 1 ];
    curves := [ RawCurve(p) : p in trans_types ];

    u1 := u - r;
    // bound t by u1		 THINK:  this bound is potty?
    poss_t := [ t : t in [2..2^Round(u1/2)] |
	    &+[ Integers() | f[1]^f[2] : f in Factorization(t) ] le u1 ];
    for C in curves do
// print "******",C;
	Cnew := RawCurve(TransverseType(C));
	Cnew`t := 1;
	Append(~baskets,Basket([Cnew]));
	for t in poss_t do
	    Cnew := RawCurve(TransverseType(C));
	    Cnew`t := t;
	    // THINK:  most of these collections of points don't work.
	    // can i eliminate them in advance for simple numerical reasons?
	    pts := [ P : P in SimpleCanonicalDissidentPoints(Cnew) |
		    &+[ Index(p) : p in P ] le u1 ];
// print t,pts;
	    for P in pts do
		Append(~baskets,Basket(P,[Cnew]));
	    end for;
	end for;
    end for;

    return baskets;
end intrinsic;

intrinsic Step2(p::GRPtS,t::RngIntElt) -> SeqEnum
{}
    C := RawCurve(p);
    C`t := t;
    pts := SimpleCanonicalDissidentPoints(C);
    if #pts eq 0 then
	return [ Basket([C]) ];
    else
	return [ Basket(P,[C]) : P in pts ];
    end if;
end intrinsic;

function calc_u(B)
    if Type(B) eq SeqEnum then
	return &+[Integers()|Index(p):p in B];
    else
	return &+[Integers()|Index(p):p in Points(B)] +
		&+[Integers()|TransverseIndex(C):C in Curves(B)];
    end if;
end function;

