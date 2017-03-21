freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    SCHOOF ELKIES ATKIN ALGORITHM                   //
//                             David Kohel                            //
//                   Based on code of Richard Rannard                 //
//                   with input from Reynald Lercier                  //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare verbose SEA, 5;

import "trace_table.m": TraceTableTrace;
//import "canonlift.m":        CanonicalLiftTraceChar2;

forward KroneckerCount, CMTrace, SSTrace, TraceToOrder, VerifyOrder;

// The constants enum_limit and bsgs_limit control the switches for 
// enumeration -- actually Kronecker sums -- and the generic abelian 
// group machinery.  Currently the latter is too eratic without
// specific control over the p-rank r, 1 <= r <= 2.  A careful use
// of the Weil pairing should make this algorithm efficient for the
// middle range, but it is currently deactivated.   

enum_limit := 3200; 
bsgs_limit := enum_limit;
P_ADIC_LIM := 1000;

// Set some constants which determine the relative priorities for 
// considering a new prime, processing an atkin prime, or processing
// a prime power.

prime_fact := 8;  
atkin_fact := 1;  
power_fact := 12; 

intrinsic SEA(E::CrvEll :
    Al := "Default", MaxSmooth := Infinity(), AbortLevel := 0,
    UseSEA := false)
    -> RngIntElt
    {The order of E using the methods of Schoof, Elkies, and Atkin
      or Canonical Lift Methods for characteristic 2.}

    VerboseLevel := GetVerbose("ECPointCount");
    if VerboseLevel ne 0 then
	SetVerbose("SEA", Min(GetVerbose("SEA"),VerboseLevel+1));
    end if;

    FF := BaseRing(E); 
    require Type(FF) eq FldFin : 
        "Curve must be defined over a finite field."; 
    require Type(Al) eq MonStgElt and Al in {"Enumerate","BSGS","Default"}:
        "Parameter Al must be one of \"Enumerate\", \"BSGS\" or \"Default\""; 
    require Type(AbortLevel) eq RngIntElt and AbortLevel in {0,1,2} : 
        "Parameter AbortLevel must be 0, 1, or 2."; 
    require Type(MaxSmooth) in {Infty,RngIntElt} and MaxSmooth ge 1:
        "Parameter MaxSmooth must be a positive integer."; 
    p := Characteristic(FF);
    q := #FF;

    if Al eq "Enumerate" or (Al eq "Default" and q lt enum_limit) then 
	vprint SEA: "Enumerating the points on the curve."; 
	return KroneckerCount(E);
	/*
    elif Al eq "BSGS" or (Al eq "Default" and q lt bsgs_limit) then
	vprint SEA: "Computing order from group structure."; 
	gens := { Random(E) : i in [1..2] };
	WeilBound := Ceiling(2*Sqrt(q));
	repeat
	    Include(~gens,Random(E));
	    n := #GenericAbelianGroup( E :
	        ComputeStructure := true,
		UseGenerators := true,
		Generators := gens );
	    t := q+1-n;	 
	until Abs(t) lt WeilBound;
	return n;
	*/
    end if; 

    // Put curve in standard form, and look for a smaller field 
    // over which E is defined.

    twist := 1;

    jE := jInvariant(E);
    min_deg := Degree(MinimalPolynomial(jE, PrimeField(Parent(jE))));
    ext_deg := Degree(FF, PrimeField(FF)) div min_deg;

    if ext_deg ne 1 then
	if jE eq 0 then
	    return q+1-CMTrace(E,-3);
	elif jE eq 12^3 then
	    return q+1-CMTrace(E,-4);
	end if;
        K := sub< FF | min_deg >;

	E1 := EllipticCurveWithjInvariant(K!jE);
        E1 := SimplifiedModel(E1);
	if not IsIsomorphic(E,EllipticCurveWithjInvariant(jE)) then
	    twist *:= -1;
	end if;
	vprint SEA, 2: "Order to be computed over smaller field", K;
        if #K lt enum_limit then 
            vprint SEA: "Enumerating points over the smaller field."; 
	    n := KroneckerCount(E1);
	    vprintf SEA:
	        "Found %o points over the subfield of size %o^%o\n",
 	        n, p, Degree(K);
	    tr := #K + 1 - n;
            ord := TraceToOrder(tr,#K,ext_deg,twist);
	    /*require VerifyOrder(E,ord): 
                "\n\n*** Computed order", ord, "is wrong. ***\n";*/
            return ord;
	end if;
    else
	E1 := SimplifiedModel(E); 
    end if;

    // use canonical lift or p-adic deformation methods
    if (p le P_ADIC_LIM) and (jInvariant(E) ne 0) and
		(jInvariant(E) ne 1728) then
	if (p le 7) then
	    UseCL := true;
	elif p eq 13 then
	    UseCL := (jInvariant(E) ne 5);	
	else
	    UseCL := ((p lt 37) or (p in \[41,47,59,71] )) and (min_deg ge 3);
	end if;

	if UseCL and (not UseSEA) then
	    vprint SEA: "Using canonical lift algorithm";

	    // "SST" addition **********
	    tr := ((p le 13) and (p ne 11)) select
		ECCanonicalLiftTraceGenus0(E1) else
		ECCanonicalLiftTraceGen(E1);
	    ord := TraceToOrder(tr,p^min_deg,ext_deg,twist); 
	    /*require VerifyOrder(E,ord): 
		"\n\n*** Computed order", ord, "is wrong. ***\n";*/
	    return ord;
	    // End "SST" addition ******
	end if;

	if (not UseSEA) and (min_deg ge Ceiling(40*Log(10,Log(10,p)))+4) then
	    vprint SEA: "Using p-adic deformation algorithm";
	    tr := ECDeformationTrace(E1);
	    ord := TraceToOrder(tr,p^min_deg,ext_deg,twist); 
	    return ord;
	end if;
    end if;

    // If min_deg = 1 and ext_deg > 1, then call back internally so
    // as not to miss the internal BSGS over GF(p)
    if (min_deg eq 1) and (ext_deg gt 1) then
	n := #E1;
	vprintf SEA:
	     "Found %o points over the subfield of size %o^%o\n",
 	        n, p, Degree(K);
	tr := #K + 1 - n;
        ord := TraceToOrder(tr,#K,ext_deg,twist);
        return ord;
    end if;	

    // Check for class number one j-invariants. 
    j := jInvariant(E1); 
    j_list := [ FF | 0, 54000, -12288000, 1728, 287496, -3375, 
                8000, -32768, -884736, -884736000, -147197952000, 
                -262537412640768000 ];
    if j in j_list then  
       D_list := [-3,-12,-27,-4,-16,-7,-8,-11,-19,-43,-67,-163]; 
       D := D_list[Index(j_list,j)]; 
       tr := CMTrace(E1,D); 
       ord := TraceToOrder(tr,p^min_deg,ext_deg,twist); 
       /*require VerifyOrder(E,ord): 
            "\n\n*** Computed order", ord, "is wrong. ***\n";*/
       return ord;
    end if; 

    // Check for supersingular curves.
    if IsProbablySupersingular(E1) then  
        // This catches all supersingular curves, but in
        // theory could include an ordinary curve. 
        // In practice the possibility is negligible. 

        tr := SSTrace(E1); 
        if tr ne twist then 
            ord := TraceToOrder(tr,p^min_deg,ext_deg,twist); 
            /*require VerifyOrder(E,ord): 
                "\n*** Computed order", ord, "is wrong. ***\n";*/
            return ord;
        end if; 
	vprint SEA:
	    "Found ordinary curve in supersingular routine!!!\n",
            "Continuing...";
    end if;          

    tr := TraceTableTrace( E1,
  	      prime_fact, atkin_fact, power_fact : 
	      MaxSmooth := MaxSmooth,
	      AbortLevel := AbortLevel );
    if tr eq (p^min_deg+1) then
	// The point group failed the smoothness test.
        vprint SEA, 2: "Failed smoothness bound.";
	return 0;
    end if;
    ord := TraceToOrder(tr,p^min_deg,ext_deg,twist);
    return ord;
end intrinsic;

intrinsic SEA(PS::SetPtEll :
    Al := "Default", MaxSmooth := Infinity(), AbortLevel := 0,
    UseSEA := false)
    -> RngIntElt
    {The order of E using the methods of Schoof, Elkies, and Atkin
      or Canonical Lift Methods for characteristic 2.}
    E := Scheme(PS);
    require E eq Curve(PS) : "SEA may not be used on subgroup schemes";
    K := BaseRing(E);
    n := SEA(E : Al := Al, MaxSmooth := MaxSmooth, AbortLevel := AbortLevel,
                               UseSEA := UseSEA);
    tr := #K + 1 - n;
    return TraceToOrder(tr, #K, Degree(Ring(PS)) div Degree(K), 1);
end intrinsic;

function TraceToOrder(tr,pr,ext_deg,twist)
    if ext_deg eq 1 then return pr + 1 - twist*tr; end if;
    P := PolynomialRing(Integers());
     char_poly := (P.1)^2 - tr*(P.1) + pr;
    if IsIrreducible(char_poly) then
      K<frob> := NumberField( (P.1)^2 - tr*(P.1) + pr );
      return Integers()!Norm(frob^ext_deg - twist); 
    else 
      root := Roots(char_poly)[1][1];
      return pr^ext_deg + 1 - 2 * twist * (root^ext_deg);
    end if; 
end function;

function VerifyOrder(E,ord)
    for i in [1..3] do
        P := Random(E); 
        if not IsIdentity(ord*P) then return false; end if; 
    end for;
    return true;
end function;

function KroneckerCount(E)
   if Characteristic(BaseRing(E)) eq 2 then
      a1, a2, a3, a4, a6 := Explode(Eltseq(E));
      n := 1;
      P := PolynomialRing(BaseRing(E));
      y := P.1;
      for x in BaseRing(E) do
	 t := (a1*x + a3)^2;
	 if t eq 0 then
	    n +:= 1;
	 else
	    c := (((x + a2)*x + a4)*x + a6)/t;
	    if AbsoluteTrace(c) eq 0 then
	       n +:= 2;
	    end if;
	 end if;
      end for;
   else
      E := SimplifiedModel(E);
      _, a2, _, a4, a6 := Explode(Eltseq(E));
      n := 1;
      for x in BaseRing(E) do
	 t := ((x + a2)*x + a4)*x + a6;
	 if t eq 0 then
	    n +:= 1;
	 elif IsSquare(t) then
	    n +:= 2;
	 end if;
      end for;
   end if;
   return n;
end function;

function CMTrace(E,D) 
    // Returns the number of points on the curve E with exact  
    // complex multiplication by an order of discriminant D. 
 
    q := #BaseRing(E); 
    p := Characteristic(BaseRing(E));
    f := Valuation(q,p);
    DK := FundamentalDiscriminant(D); 
    _, m := IsSquare(D div DK);   
    if KroneckerSymbol(DK,p) ne 1 then 
        vprint SEA: "Supersingular elliptic curve."; 
        // Could treat here, but...
        return SSTrace(E); 
    end if; 
    P := PolynomialRing(Integers()); X := P.1;
    S := sub< MaximalOrder( QuadraticField(DK) ) | m >;
    _, X1 := NormEquation(S, p : Factorization := [<p,1>] ); 
    x1 := X1[1];
    G, h := UnitGroup(S); 
    U := { h(g) : g in G }; 
    vprintf SEA, 2: "Discriminant of endomorphism ring = %o, ", D;
    vprintf SEA, 2: "having conductor %o.\n", m;
    x2 := Conjugate(x1);
    frob_vals := { u * x1^r * x2^(f-r) : u in U, r in [0..f div 2] }; 
    trace_vals := SetToSequence({ Trace(x) : x in frob_vals });
    vprint SEA, 3: "Frobenius candidates", frob_vals;
    vprint SEA, 2: "Checking", #trace_vals, "possible trace values.";
    F := QuadraticTwist(E);
    vprint SEA, 3 : "Initial CM trace candidates:", trace_vals;
    for i in [1..16] do 
        // Should exit after first iteration.
        P1 := Random(E); Q1 := (q+1)*P1; 
        P2 := Random(F); Q2 := (q+1)*P2; 
        for t in trace_vals do 
            if Q1 ne t*P1 or Q2 ne -t*P2 then 
                Exclude(~trace_vals,t); 
            end if; 
        end for; 
        if #trace_vals eq 1 then 
            return trace_vals[1]; 
        end if;  
    end for; 
    print "Remaining CM trace candidates:", trace_vals;
    error "Failed to find unique trace of CM curve:", E;
end function; 

function SSTrace(E) 
    // The trace of Frobenius on the known supersingular curve E. 
 
    j := jInvariant(E); 
    q := #BaseRing(E); 
    p := Characteristic(BaseRing(E));  
    e := Valuation(q,p) mod 2;  
    _, r := IsSquare(q div p^e); 
 
    // Let i, w be primitive 4th and 6th roots of unity (i^2 = -1,  
    // w^3 = -1). Then the possibilities for Frobenius, Frob, and  
    // its trace, t, are: 
    //  
    //        { -r*sqrt(-q),r*sqrt(-q)  t = 0,       (any p) 
    // Frob = { -r*(1+i),r*(1+i)        t = -2*r,2*r (p = 2) 
    //        { -r*(1+w),r*(1+w)        t = -3*r,3*r (p = 3) 
    //              
    // where q = r^2*p (e = 1), or  
    //  
    //        { -r,r            t = -2*r,2*r (any p) 
    // Frob = { -r*i,r*i        t = 0    (p mod 4 ne 1 && j = 12^3)   
    //        { -r*w,r*w,       t = -r,r (p mod 3 ne 1 && j = 0) 
    //             -r*w^2,r*w^2    
    //  
    // where q = r^2 (e = 0). 
    // --D. Kohel
    
    if p eq 2 then // j = 0 = 12^3 
        if e eq 1 then 
            trace_vals := [-2*r,0,2*r]; 
        else // e eq 0 
            trace_vals := [-2*r,-r,0,r,2*r]; 
        end if;   
    elif p eq 3 then // j = 0 = 12^3 
        if e eq 1 then 
            trace_vals := [-3*r,0,3*r]; 
        else // e eq 0 
            trace_vals := [-2*r,-r,0,r,2*r]; 
        end if;  
    elif j eq 0 then  
        if (p mod 3) eq 1 then 
            vprint SEA: "Illegal ordinary curve in SSPointCount."; 
            return 1; 
        elif e eq 1 then 
            return 0; 
        else // e eq 0 
            trace_vals := [-2*r,-r,r,2*r]; 
        end if;   
    elif j eq 12^3 then  
        if (p mod 4) eq 1 then 
            vprint SEA: "Illegal ordinary curve in SSPointCount."; 
            return 1; 
        elif e eq 1 then 
            return 0; 
        else // e eq 0 
            trace_vals := [-2*r,0,2*r]; 
        end if;   
    elif e eq 1 then 
        return 0; 
    else // e eq 0 
        trace_vals := [-2*r,2*r]; 
    end if; 
    for i in [1..15] do 
        P := Random(E); 
        for t in trace_vals do 
            if not IsIdentity((q+1-t)*P) then 
                Exclude(~trace_vals,t); 
            end if; 
        end for; 
        if #trace_vals eq 1 then 
            return trace_vals[1]; 
        end if;  
    end for; 
    vprint SEA:
        "Illegal ordinary curve in SSPointCount or really bad luck."; 
    return 1; 
end function; 
