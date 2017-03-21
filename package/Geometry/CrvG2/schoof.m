freeze;

///////////////////////////////////////////////////////////////////////////
//
// JacSchoof: compute the cardinality of J mod r.
//   J: the Jacobian of the genus 2 hyperelliptic curve
//   r: an integer, we do the Schoof step for the r-torsion divisors
//
// P. Gaudry (March 2001)
//
///////////////////////////////////////////////////////////////////////////
// 
// Things TO DO to gain speed:
//   1) Use Brent & Kung only when it is better
//   2) Try to always apply fast resultant computations
//
// Other things TO DO :
//   1) split the main function in several smaller functions.
//   2) add a test that everything is ok after resultant computations
//      and if not, try again with the naive way (just to be on the safe side)
//
///////////////////////////////////////////////////////////////////////////
/*
CHANGES:
 
 
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
                 fix Curve
  ------------------------------------------------------------------*/
 
 
 
 
 


/*
///////////////////////////////////////////////////////////////////////////
// Degrees of the involved polynomials (generic case) :

r        3        5        7       11        13	       	   r
----------------------------------------------------------------------
D0	 17    	  49   	   97	   241	     		   2*r^2-1
D1     	 16 	  48 	   96	   240			   2*r^2-2
d2	 15    	  47   	   95  	   239 	       	       	   2*r^2-3
Eps0	 25 	  73 	   145	   361			   3*r^2-2
Eps1	 24       72       144     360                     3*r^2-3
Denom	 25       73   	   145 	   361 	       	       	   3*r^2-2
Res1	 240	  2256 	   9120	   57360       	       	   4*r^4-10*r^2+6
Res2	 720	  6768	   27360   172080		   12*r^4-30*r^2+18
Res	 80	  624 	   2400	   14640		   r^4-1
----------------------------------------------------------------------
*/


/*
//// BUGs to FIX: (seems to work now...)


Fq := GF(11^5);
PP := PolynomialRing(Fq); x := PP.1;
f:=x^5 + Fq.1^134541*x^4 + Fq.1^129052*x^3 + Fq.1^16536*x^2 + Fq.1^70676*x + Fq.1^111711;
t, H := IsHyperellipticCurve([f,0]);
J := Jacobian(H);
SetSeed(1, 3299);
nj3 := JacSchoof(7, J);

*/

// Record format to store everything which is needed during the computation.
JacSchRecFormat := recformat <
    J : JacHyp,                          // the Jacobian
    q : RngIntElt,                       // size of finite field
    r : RngIntElt,                       // the modulo
    Res : RngUPolElt,                    // the resultant we are factoring
    DegAlreadyTested : RngIntElt,        // how many factors already tested
    D0 : RngUPolElt, D1 : RngUPolElt, d2 : RngUPolElt, // division polynomials
    Eps0 : RngUPolElt, Eps1 : RngUPolElt, Denom : RngUPolElt,
    TableA : Tup,                        // table of what is known
                                         // about (a_1,a_2)  mod r
    finished : BoolElt,                  
    NbCandidates : RngIntElt,            // how many values or #J mod r are
                                         // currently possible
    Generators : List >;                 // generators of the subgroup we
					 // already explored.


// the forwards...
forward TheSolution;
forward UpdateTable;
forward UpdateTableTheta;
forward IsFinished;
forward PurgeRes;
forward AddAllCombination;
forward CleanWhenFailed;
forward UpdateFinished;
forward Resultant1;
forward Resultant2;
forward FastEvaluate;
forward FastInterpolate;

import "formalarithg2.m" : DivDoubleFormal, DivAddFormal,
    DivFrobeniusFormal, DivMultFormal, DivNegateFormal, DivIsZeroFormal;

import "divpoljac.m" : DeltaDivPol, EpsilonDivPol;

import "cardmod3.m" : CardJacMod3;

///////////////////////////////////////////////////////////////////////////
//
// The main function. Compute #J mod r.
// the vararg AlwaysRes2 is a flag that can be switched of to test another
// strategy (may be faster for r=3)
// 
///////////////////////////////////////////////////////////////////////////

// intrinsic JacSchoof(r::RngIntElt, J::JacHyp : AlwaysRes2 := true,
//                     Huge := false) -> RngIntElt
//     { Compute the value of #J mod r, where J is the jacobian of a
//     hyperelliptic curve of genus 2 of the form y^2 = x^5 + ... over a finite
//     field of odd characteristic p.  r should be a prime different from p.}

function JacSchoof(r, J : AlwaysRes2 := true, Huge := false) 
    // initialisation and requirements:
    f, h := HyperellipticPolynomials(Curve(J));
    PP := Parent(f);
    x := PP.1;
    Fq := BaseRing(J);
    q := #Fq;

/*
    require h eq 0 and Degree(f) eq 5 and Coefficient(f, 5) eq 1 :
        "The curve should have an equation of the form y^2 = x^5 + ...";
    require IsFinite(Fq) : "Works only over a finite field";
    require IsPrime(r) : "Only implemented for prime r";
    require r ne Characteristic(Fq) :
        "Use Cartier-Manin operator instead of Schoof";
    require r ne 2 : "Use TwoTorsionSubgroupOrder instead of Schoof";
    require r le 17 or Huge : "Your value of r is too big...
    If you really want to play with huge examples, switch on the `Huge' flag.";
*/
    assert h eq 0 and Degree(f) eq 5 and Coefficient(f, 5) eq 1;
    assert IsFinite(Fq) and IsPrime(r);
    assert r ne Characteristic(Fq);
    assert r ne 2;
    assert r le 17 or Huge;

    if r eq 3 and (q mod 3) eq 2 then
	vprintf JacHypCnt, 3 : "Try using the modular polynomial\n";
	Try := CardJacMod3(J);
	if #Try ne 1 then
	    vprintf JacHypCnt, 3 : "Failed !\n";
	else
	    vprintf JacHypCnt, 3 : "Success !\n";
	    vprintf JacHypCnt, 3 : "Value of #J mod 3 is %o\n", Try[1];
	    return Try[1];
	end if;
    end if;
	    
    JacSchRec := rec<JacSchRecFormat |
        J := J,
	q := q,
	r := r,
	DegAlreadyTested := 0,
	Res := PP!1,
	TableA := <[[1 : i in [1..r]] : j in [1..r]], r^2>,
	finished := false,
	NbCandidates := r,
	Generators := [* *] >;

    //////////////////////////////////////////////////////////////////////
    //  compute divisions polynomials and normalize them
    //////////////////////////////////////////////////////////////////////
    // Compute D0, D1, d2
    d0, d1, d2 := DeltaDivPol(J, r);
    d2 := d2 div f;
    D1 := 2*d1+x*d2;
    D0 := x^2*d2+4*x*d1+16*d0*f;
    // Simplify the D's if f is a factor.
    while true do
	quo0, rem := Quotrem(D0, f);
	if rem ne 0 then break; end if;
	quo1, rem := Quotrem(D1, f);
	if rem ne 0 then break; end if;
	quo2, rem := Quotrem(d2, f);
	if rem ne 0 then break; end if;
	D0 := quo0;
	D1 := quo1;
	d2 := quo2;
    end while;
    // compute the Epsilon division polynomial
    eps0, eps1, denom := EpsilonDivPol(J, r);
    // normalize the Epsilon division polynomial
    Eps0 := 4*f*eps0+x*eps1;
    Eps1 := -eps1;
    Denom := 4*f*denom;

    JacSchRec`D0   := D0;   JacSchRec`D1   := D1;   JacSchRec`d2    := d2;
    JacSchRec`Eps0 := Eps0; JacSchRec`Eps1 := Eps1; JacSchRec`Denom := Denom;

    //////////////////////////////////////////////////////////////////////
    //  compute the first resultant
    //////////////////////////////////////////////////////////////////////
    PPP<x1,x2> := PolynomialRing(BaseRing(PP), 2);
    hom1 := hom < PP -> PPP | x1>;
    hom2 := hom < PP -> PPP | x2>;
    E1 := hom1(D1)*hom2(d2) - hom2(D1)*hom1(d2);
    E2 := hom1(D0)*hom2(d2) - hom2(D0)*hom1(d2);
    // Divide E1 and E2 by x1-x2
    E1 div:= x1-x2;
    E2 div:= x1-x2;

    GcdE1E2 := GCD(E1, E2);
    if GcdE1E2 ne 1 then
	vprintf JacHypCnt, 3 :  "E1 and E2 have a non-trivial GCD: try to take advantage of this info\n";
	E1 div:= GcdE1E2;
	E2 div:= GcdE1E2;
	// deal with the torsion points described by this GCD:
	// note: it is not necessary, but it may speed-up the computations
	fact := {};
	for ff in Factorization(GcdE1E2) do
	    if not IsUnivariate(ff[1]) then
		vprintf JacHypCnt, 3 :  "factor %o is not univariate: skip it!\n", ff[1];
	    else
		Include(~fact, PP!UnivariatePolynomial(ff[1]));
	    end if;
	end for;
	fact := SetToSequence(fact);
	IndentPush();
	UpdateTableTheta(~JacSchRec, fact);
	IndentPop();
	if IsFinished(JacSchRec) then
	    return TheSolution(JacSchRec);
	end if;
    end if;

    Delta := Degree(D1)*Degree(d2); // The degree of the resultant we search
    timeRes1 := Cputime();
    if #Fq le Delta+1+Degree(d2) or GcdE1E2 ne 1
	or Degree(D1) le Degree(d2) then  // TODO: maybe one can handle
	                                  // the last case with fast
	                                  //resultant but...
	// the base field is too small for evaluate/interpolate
	// compute E1, E2
	vprintf JacHypCnt, 3 :  "Computing the resultant 1, naive way ...\n";
	Res1 := PP!UnivariatePolynomial(Resultant(E1, E2, x2));
	// Divide the powers of d2 which could appear in Res1
	while true do
	    quo, rem := Quotrem(Res1, d2);
	    if rem eq 0 then Res1 := quo;
	    else break;
	    end if;
	end while;
	// Divide the powers of f which could appear in Res
	while true do
	    quo0, rem := Quotrem(Res1, f);
	    if rem ne 0 then break; end if;
	    Res1 := quo0;
	end while;
    else
	vprintf JacHypCnt, 3 :  "Computing the resultant 1, via evaluate/interpolate...\n";
	Res1 := Resultant1(D0, D1, d2);
    end if;
    timeRes1 := Cputime()-timeRes1;
    vprintf JacHypCnt, 3 :  "done in %o sec\n", timeRes1;
    vprintf JacHypCnt, 3 :  "the resultant 1 is of degree %o\n",Degree(Res1);
    JacSchRec`Res := Res1;
    
    HasComputedRes2 := false;

    //////////////////////////////////////////////////////////////////////
    //  squarefree factorization of the first resultant
    //////////////////////////////////////////////////////////////////////
    sqff_Res1 := SquareFreeFactorization(Res1);
    if #sqff_Res1 gt 1 then
	vprintf JacHypCnt, 3 :  "Found square factors.\n";
	vprintf JacHypCnt, 3 :  "First of all, compute the second resultant, to clean the mess...\n";
	Delta := 2*(Degree(D1)-1)*(Max(Degree(Eps0),Degree(Eps1))-1);

	timeRes2 := Cputime();
	
	E3 := hom1(Eps1)*hom2(Eps0) - hom2(Eps1)*hom1(Eps0);
	E3 div:= x1-x2;
	GcdE1E3 := GCD(E1, E3);
	if GcdE1E3 ne 1 then
	    vprintf JacHypCnt, 3 :  "E1 and E3 have a non-trivial GCD: cannot use fast resultant\n";
	    E1 div:= GcdE1E3;
	    E3 div:= GcdE1E3;
	end if;

	if #Fq le Delta+1+Degree(Eps1)+Degree(d2)
	    or GcdE1E2 ne 1 or GcdE1E3 ne 1
	    or Degree(D1) le Degree(d2) or Degree(Eps0) le Degree(Eps1)
	    then
	    // the base field is too small for evaluate/interpolate
	    // compute E1, E3
	    vprintf JacHypCnt, 3 :  "Computing the resultant 2, naive way ...\n";
	    Res2 := PP!UnivariatePolynomial(Resultant(E1, E3, x2));
	else
	    vprintf JacHypCnt, 3 :  "Computing the resultant 2, via evaluate/interpolate...\n";
	    Res2 := Resultant2(Eps0, Eps1, D1, d2);
	end if;
	timeRes2 := Cputime()-timeRes2;
	vprintf JacHypCnt, 3 :  "done in %o sec\n", timeRes2;
	vprintf JacHypCnt, 3 :  "the resultant 2 is of degree %o\n",Degree(Res2);

	timeGCD := Cputime();
	vprintf JacHypCnt, 3 :  "Computing the gcd of the 2 resultants...\n";
	JacSchRec`Res := GCD(JacSchRec`Res, Res2);
	timeGCD := Cputime()-timeGCD;
	vprintf JacHypCnt, 3 :  "done in %o sec\n", timeGCD;
	vprintf JacHypCnt, 3 :  "the gcd is of degree %o\n", Degree(JacSchRec`Res);
	
	sqff_Res := SquareFreeFactorization(JacSchRec`Res);
	
	vprintf JacHypCnt, 3 :  "Separate the factors ...\n";
	sqfact := [];
	for ff in sqff_Res do
	    if ff[2] ge 2 then
		sqfact cat:= [fff[1] : fff in Factorization(ff[1])];
	    end if;
	end for;
	// Reverse(~sqfact);
	IndentPush();
	UpdateTable(~JacSchRec, sqfact, true);
	IndentPop();
	if IsFinished(JacSchRec) then
	    return TheSolution(JacSchRec);
	end if;

	HasComputedRes2 := true;

    end if;
    
    
    //////////////////////////////////////////////////////////////////////
    //  compute X^q mod Res
    //////////////////////////////////////////////////////////////////////
    timeXqModRes := Cputime();
    vprintf JacHypCnt, 3 :  "Computing X^q mod Res...\n";
    XqModRes := Modexp(x, q, JacSchRec`Res);
    timeXqModRes := Cputime()-timeXqModRes;
    vprintf JacHypCnt, 3 :  "done in %o sec\n", timeXqModRes;

    // use the first factors that we discovered (if ever!)
    ddf_degree_1 := GCD(XqModRes-x, JacSchRec`Res);
    if Degree(ddf_degree_1) ge 1 then
	vprintf JacHypCnt, 3 :  "Found %o factors of degree 1...\n", Degree(ddf_degree_1);
	vprintf JacHypCnt, 3 :  "Separate the factors ...\n";
	tps := Cputime();
	fact := EqualDegreeFactorization(ddf_degree_1, 1, XqModRes mod ddf_degree_1);
	vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;
	IndentPush();
	UpdateTable(~JacSchRec, fact, false);
	IndentPop();
	if IsFinished(JacSchRec) then
	    return TheSolution(JacSchRec);
	end if;
    end if;


    //////////////////////////////////////////////////////////////////////
    //  if X^q mod Res1 is costly, compute the second resultant
    //////////////////////////////////////////////////////////////////////
    CoeffXover := 0;
    if (CoeffXover*timeXqModRes gt timeRes1 or AlwaysRes2)
	and not HasComputedRes2 then
	Delta := 2*(Degree(d1)-1)*(Max(Degree(eps0),Degree(eps1))-1);

	E3 := hom1(Eps1)*hom2(Eps0) - hom2(Eps1)*hom1(Eps0);
	E3 div:= x1-x2;
	GcdE1E3 := GCD(E1, E3);
	if GcdE1E3 ne 1 then
	    vprintf JacHypCnt, 3 :  "E1 and E3 have a non-trivial GCD: cannot use fast resultant\n";
	    E1 div:= GcdE1E3;
	    E3 div:= GcdE1E3;
	end if;
	
	timeRes2 := Cputime();
	if #Fq le Delta+1+Degree(Eps1)+Degree(d2)
	    or GcdE1E3 ne 1 or GcdE1E2 ne 1
	    or Degree(D1) le Degree(d2) or Degree(Eps0) le Degree(Eps1)
	    then
	    // the base field is too small for evaluate/interpolate
	    // compute E1, E3
	    vprintf JacHypCnt, 3 :  "Computing the resultant 2, naive way ...\n";
	    Res2 := PP!UnivariatePolynomial(Resultant(E1, E3, x2));
	else
	    vprintf JacHypCnt, 3 :  "Computing the resultant 2, via evaluate/interpolate...\n";
	    Res2 := Resultant2(Eps0, Eps1, D1, d2);
	end if;
	timeRes2 := Cputime()-timeRes2;
	vprintf JacHypCnt, 3 :  "done in %o sec\n", timeRes2;
	vprintf JacHypCnt, 3 :  "the resultant 2 is of degree %o\n",Degree(Res2);
	HasComputedRes2 := true;
	
	timeGCD := Cputime();
	vprintf JacHypCnt, 3 :  "Computing the gcd of the 2 resultants...\n";
	JacSchRec`Res := GCD(JacSchRec`Res, Res2);
	timeGCD := Cputime()-timeGCD;
	vprintf JacHypCnt, 3 :  "done in %o sec\n", timeGCD;
	vprintf JacHypCnt, 3 :  "the gcd is of degree %o\n", Degree(JacSchRec`Res);
	XqModRes := XqModRes mod JacSchRec`Res;
    end if;

    //////////////////////////////////////////////////////////////////////
    // if possible, initiate the Brent and Kung computations.
    // MEMLIMIT is the maximal amount of MB that we allow ourselves to
    // allocate for precomputations
    // TODO : finish this part!
    //////////////////////////////////////////////////////////////////////

    MEMLIMIT := 200;

    B := Degree(JacSchRec`Res) div 2;
    l := Isqrt(B);
    m := Ceiling(B/l);
    MemRequired := Ceiling(((l+m)*(Degree(JacSchRec`Res)+1)*Ceiling(Log(2^32, q)))/10^6*4);
    if MemRequired ge MEMLIMIT then
	vprintf JacHypCnt, 3 :  "Not enough memory to use Brent & Kung strategy.\n";
	vprintf JacHypCnt, 3 :  "You may consider changing the parameter MEMLIMIT.\n";
	useBK := false;
    else
	vprintf JacHypCnt, 3 :  "I hope you have %o MB available on your machine!\n", MemRequired;
	useBK := true;
//	useBK := false;
    end if;
    if not useBK then
	// naive way of factoring step by step
	degree := 1;
	xqd := XqModRes;  // contains the value of x^(q^degree) mod Res
	finished := false;
	while Degree(JacSchRec`Res) gt 0 do
	    degree +:= 1;
	    vprintf JacHypCnt, 3 :  "Compute the factors of degree %o (deg Res = %o)...\n",
	        degree, Degree(JacSchRec`Res);
	    tps := Cputime();
	    xqd := Modexp(xqd, q, JacSchRec`Res);
	    ddf_degree_d := Gcd(xqd-x, JacSchRec`Res);
	    vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;
	    if Degree(ddf_degree_d) ge 1 then
		vprintf JacHypCnt, 3 :  "Found %o factors of degree %o...\n",
		Degree(ddf_degree_d) div degree, degree;
		vprintf JacHypCnt, 3 :  "Separate the factors ...\n";
		tps := Cputime();
		fact := EqualDegreeFactorization(ddf_degree_d, degree, XqModRes mod ddf_degree_d);
		vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;

		IndentPush();
		UpdateTable(~JacSchRec, [ff[1] : ff in fact], false);
		IndentPop();
		if IsFinished(JacSchRec) then
		    return TheSolution(JacSchRec);
		end if;
	    end if;
	    if degree gt Degree(JacSchRec`Res)/2 then
		// the remaining factor has to be irreducible
		if Degree(JacSchRec`Res) gt 0 then
		    vprintf JacHypCnt, 3 :  "The last part of Res is irreducible.\n";
		    JacSchRec`Res := Normalize(JacSchRec`Res);
		    IndentPush();
		    UpdateTable(~JacSchRec, [JacSchRec`Res], false);
		    IndentPop();
		    if IsFinished(JacSchRec) then
			return TheSolution(JacSchRec);
		    end if;
		end if;
		JacSchRec`Res := Parent(JacSchRec`Res)!1;
	    end if;
	end while;
    else
	// BK strategy:
	t := Ceiling(Sqrt(Degree(JacSchRec`Res)));
	vprintf JacHypCnt, 3 :  "Setup the first BK ...\n"; tps := Cputime();
	XqModRes mod:= JacSchRec`Res;
	BKSetup := ModularCompositionSetup(XqModRes, JacSchRec`Res, t);
	vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;

	FIRST_BOUND := 8;   // TODO : adjust this bound !
//	FIRST_BOUND := 3;
	Tableh := [XqModRes];
	xqd := XqModRes;
	degree := 1;
	for i := 2 to FIRST_BOUND do
	    degree +:= 1;
	    vprintf JacHypCnt, 3 :  "Compute the factors of degree %o (deg Res = %o)...\n",
	        degree, Degree(JacSchRec`Res); tps := Cputime();
	    xqd := ModularCompositionApply(xqd, BKSetup, JacSchRec`Res, t);
	    ddf_degree_d := Gcd(xqd-x, JacSchRec`Res);
	    vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;
	   
	    if Degree(ddf_degree_d) ge 1 then
		vprintf JacHypCnt, 3 :  "Found %o factors of degree %o...\n",
		    Degree(ddf_degree_d) div degree, degree;
		vprintf JacHypCnt, 3 :  "Separate the factors ...\n";
		tps := Cputime();
		fact := EqualDegreeFactorization(ddf_degree_d, degree,
		    Tableh[1] mod ddf_degree_d);
		vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;

		IndentPush();
		UpdateTable(~JacSchRec, fact, false);
		IndentPop();
		if IsFinished(JacSchRec) then
		    return TheSolution(JacSchRec);
		end if;

		// WARNING: here I rely on something which is not documented!
		// namely that BKSetup is an array of polynomials mod Res.
		for j := 1 to #BKSetup do
		    BKSetup[j] mod:= JacSchRec`Res;
		end for;
		for j := 1 to #Tableh do
		    Tableh[j] mod:= JacSchRec`Res;
		end for;
	    end if;
	    
	    if degree gt Degree(JacSchRec`Res)/2 then
		// the remaining factor has to be irreducible
		if Degree(JacSchRec`Res) gt 0 then
		    vprintf JacHypCnt, 3 :  "The last part of Res is irreducible.\n";
		    JacSchRec`Res := Normalize(JacSchRec`Res);
		    IndentPush();
		    UpdateTable(~JacSchRec, [JacSchRec`Res], false);
		    IndentPop();
		    if IsFinished(JacSchRec) then
			return TheSolution(JacSchRec);
		    end if;
		end if;
		CleanWhenFailed(~JacSchRec);
		if IsFinished(JacSchRec) then
		    return TheSolution(JacSchRec);
		end if;
		vprintf JacHypCnt, 3 :  "unable to conclude!!!!!\n";
		assert(false);
		return [-1];
	    end if;

	    Append(~Tableh, xqd mod JacSchRec`Res);
	end for;

	vprintf JacHypCnt, 3 :  "Beginning the second phase of Shoup algorithm...\n";
	tps:=Cputime();
	
	BKSetup2 := ModularCompositionSetup(Tableh[FIRST_BOUND],
	                                   JacSchRec`Res, t);
        vprintf JacHypCnt, 3 :  "setup done in %o sec\n", Cputime()-tps;

	xqd := Tableh[FIRST_BOUND];
	for j := 2 to FIRST_BOUND do
	    vprintf JacHypCnt, 3 :  "Compute X^q^i with i= %o (deg Res = %o)...\n",
	        j*FIRST_BOUND, Degree(JacSchRec`Res); tps := Cputime();
	    xqd := ModularCompositionApply(xqd, BKSetup2, JacSchRec`Res, t);
	    vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;

	    vprintf JacHypCnt, 3 :  "Compute Ij...\n"; tps := Cputime();
	    Ij := PP!1;
	    for i := 1 to FIRST_BOUND do
		Ij := (Ij * (xqd-Tableh[i])) mod JacSchRec`Res;
	    end for;
	    vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;

	    vprintf JacHypCnt, 3 :  "Compute the GCD...\n"; tps := Cputime();
	    thegcd := GCD(Ij, JacSchRec`Res);
	    vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;

	    if Degree(thegcd) ne 0 then
		vprintf JacHypCnt, 3 :  "the degree of the GCD is %o.\n", Degree(thegcd);
		for i := 1 to FIRST_BOUND do
		    if Degree(thegcd) eq 0 then break; end if;
		    igcd := GCD(xqd-Tableh[i], thegcd);
		    if Degree(igcd) ne 0 then
			degree := j*FIRST_BOUND-i;
			thegcd div:= igcd;
			vprintf JacHypCnt, 3 :  "Found %o factors of degree %o...\n",
			Degree(igcd) div degree, degree;
			vprintf JacHypCnt, 3 :  "Separate the factors ...\n";
			tps := Cputime();
			fact := EqualDegreeFactorization(igcd, degree,
			Tableh[1] mod igcd);
			vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;

			IndentPush();
			UpdateTable(~JacSchRec, fact, false);
			IndentPop();
			if IsFinished(JacSchRec) then
			    return TheSolution(JacSchRec);
			end if;
			
			for l := 1 to #BKSetup2 do
			    BKSetup2[l] mod:= JacSchRec`Res;
			end for;
		    end if;
		    if  j*FIRST_BOUND-i gt Degree(JacSchRec`Res)/2 then
			// the remaining factor has to be irreducible
			if Degree(JacSchRec`Res) gt 0 then
			    vprintf JacHypCnt, 3 :  "The last part of Res is irreducible.\n";
			    JacSchRec`Res := Normalize(JacSchRec`Res);
			    IndentPush();
			    UpdateTable(~JacSchRec, [JacSchRec`Res], false);
			    IndentPop();
			    if IsFinished(JacSchRec) then
				return TheSolution(JacSchRec);
			    end if;
			end if;
			CleanWhenFailed(~JacSchRec);
			if IsFinished(JacSchRec) then
			    return TheSolution(JacSchRec);
			end if;
			vprintf JacHypCnt, 3 :  "unable to conclude!!!!!\n";
			assert(false);
			return [-1];
		    end if;
		end for;
		assert Degree(thegcd) lt 1;
	    end if;
	end for;
	assert HasComputedRes2;
	
	SECOND_BOUND := Isqrt(Degree(JacSchRec`Res) div 2);
	assert SECOND_BOUND gt FIRST_BOUND;

	vprintf JacHypCnt, 3 :  "Starting a second Shoup with full degree.\n";
	for l := 1 to #BKSetup do
	    BKSetup[l] mod:= JacSchRec`Res;
	end for;
	for l := 1 to #Tableh do
	    Tableh[l] mod:= JacSchRec`Res;
	end for;
	xqd := Tableh[FIRST_BOUND];
	for i := FIRST_BOUND+1 to SECOND_BOUND do
	    vprintf JacHypCnt, 3 :  "Compute X^q^%o (deg Res = %o)...\n",
	        i, Degree(JacSchRec`Res); tps := Cputime();
	    xqd := ModularCompositionApply(xqd, BKSetup, JacSchRec`Res, t);
	    vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;
	   
	    if i gt FIRST_BOUND^2 then
		vprintf JacHypCnt, 3 :  "Compute the gcd...\n"; tps := Cputime();
		ddf_degree_d := Gcd(xqd-x, JacSchRec`Res);
		vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;
	    else
		ddf_degree_d := PP!0;
	    end if;
	    
	    if Degree(ddf_degree_d) ge 1 then
		vprintf JacHypCnt, 3 :  "Found %o factors of degree %o...\n",
		    Degree(ddf_degree_d) div i, i;
		vprintf JacHypCnt, 3 :  "Separate the factors ...\n";
		tps := Cputime();
		fact := EqualDegreeFactorization(ddf_degree_d, i,
		    Tableh[1] mod ddf_degree_d);
		vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;

		IndentPush();
		UpdateTable(~JacSchRec, fact, false);
		IndentPop();
		if IsFinished(JacSchRec) then
		    return TheSolution(JacSchRec);
		end if;

		// WARNING: here I rely on something which is not documented!
		// namely that BKSetup is an array of polynomials mod Res.
		for j := 1 to #BKSetup do
		    BKSetup[j] mod:= JacSchRec`Res;
		end for;
		for j := 1 to #Tableh do
		    Tableh[j] mod:= JacSchRec`Res;
		end for;
	    end if;
	    
	    if i gt Degree(JacSchRec`Res)/2 then
		// the remaining factor has to be irreducible
		if Degree(JacSchRec`Res) gt 0 then
		    vprintf JacHypCnt, 3 :  "The last part of Res is irreducible.\n";
		    JacSchRec`Res := Normalize(JacSchRec`Res);
		    IndentPush();
		    UpdateTable(~JacSchRec, [JacSchRec`Res], false);
		    IndentPop();
		    if IsFinished(JacSchRec) then
			return TheSolution(JacSchRec);
		    end if;
		end if;
		CleanWhenFailed(~JacSchRec);
		if IsFinished(JacSchRec) then
		    return TheSolution(JacSchRec);
		end if;
		vprintf JacHypCnt, 3 :  "unable to conclude!!!!!\n";
		assert(false);
		return [-1];
	    end if;

	    Append(~Tableh, xqd mod JacSchRec`Res);
	end for;

	vprintf JacHypCnt, 3 :  "Beginning the second phase of the second Shoup algorithm...\n";
	tps:=Cputime();
	
	BKSetup2 := ModularCompositionSetup(Tableh[SECOND_BOUND],
	                                   JacSchRec`Res, t);
        vprintf JacHypCnt, 3 :  "setup done in %o sec\n", Cputime()-tps;

	xqd := Tableh[SECOND_BOUND];
	for j := 2 to SECOND_BOUND do
	    vprintf JacHypCnt, 3 :  "Compute X^q^i with i= %o (deg Res = %o)...\n",
	        j*SECOND_BOUND, Degree(JacSchRec`Res); tps := Cputime();
	    xqd := ModularCompositionApply(xqd, BKSetup2, JacSchRec`Res, t);
	    vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;

	    vprintf JacHypCnt, 3 :  "Compute Ij...\n"; tps := Cputime();
	    Ij := PP!1;
	    for i := 1 to SECOND_BOUND do
		Ij := (Ij * (xqd-Tableh[i])) mod JacSchRec`Res;
	    end for;
	    vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;

	    vprintf JacHypCnt, 3 :  "Compute the GCD...\n"; tps := Cputime();
	    thegcd := GCD(Ij, JacSchRec`Res);
	    vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;

	    if Degree(thegcd) ne 0 then
		vprintf JacHypCnt, 3 :  "the degree of the GCD is %o.\n", Degree(thegcd);
		for i := 1 to SECOND_BOUND do
		    if Degree(thegcd) eq 0 then break; end if;
		    igcd := GCD(xqd-Tableh[i], thegcd);
		    if Degree(igcd) ne 0 then
			degree := j*SECOND_BOUND-i;
			thegcd div:= igcd;
			vprintf JacHypCnt, 3 :  "Found %o factors of degree %o...\n",
			Degree(igcd) div degree, degree;
			vprintf JacHypCnt, 3 :  "Separate the factors ...\n";
			tps := Cputime();
			fact := EqualDegreeFactorization(igcd, degree,
			Tableh[1] mod igcd);
			vprintf JacHypCnt, 3 :  "done in %o sec\n", Cputime()-tps;

			IndentPush();
			UpdateTable(~JacSchRec, fact, false);
			IndentPop();
			if IsFinished(JacSchRec) then
			    return TheSolution(JacSchRec);
			end if;
			
			for l := 1 to #BKSetup2 do
			    BKSetup2[l] mod:= JacSchRec`Res;
			end for;
		    end if;
		    if  j*SECOND_BOUND-i gt Degree(JacSchRec`Res)/2 then
			// the remaining factor has to be irreducible
			if Degree(JacSchRec`Res) gt 0 then
			    vprintf JacHypCnt, 3 :  "The last part of Res is irreducible.\n";
			    JacSchRec`Res := Normalize(JacSchRec`Res);
			    IndentPush();
			    UpdateTable(~JacSchRec, [JacSchRec`Res], false);
			    IndentPop();
			    if IsFinished(JacSchRec) then
				return TheSolution(JacSchRec);
			    end if;
			end if;
			CleanWhenFailed(~JacSchRec);
			if IsFinished(JacSchRec) then
			    return TheSolution(JacSchRec);
			end if;
			vprintf JacHypCnt, 3 :  "unable to conclude!!!!!\n";
			assert(false);
			return [-1];
		    end if;
		end for;
		assert Degree(thegcd) lt 1;
	    end if;
	end for;
    end if;

    // the remaining factor has to be irreducible
    if Degree(JacSchRec`Res) gt 0 then
	vprintf JacHypCnt, 3 :  "The last part of Res is irreducible.\n";
	JacSchRec`Res := Normalize(JacSchRec`Res);
	IndentPush();
	UpdateTable(~JacSchRec, [JacSchRec`Res], false);
	IndentPop();
	if IsFinished(JacSchRec) then
	    return TheSolution(JacSchRec);
	end if;
    end if;
    CleanWhenFailed(~JacSchRec);
    if IsFinished(JacSchRec) then
	return TheSolution(JacSchRec);
    end if;
    vprintf JacHypCnt, 3 :  "unable to conclude!!!!!\n";
    assert(false);
    return [-1];
end function;


function IsFinished(JacSchRec)
    return JacSchRec`finished;
end function;


procedure UpdateFinished(~JacSchRec)
    if JacSchRec`finished then return; end if;
    r := JacSchRec`r;
    q := JacSchRec`q;
    TableA := JacSchRec`TableA;
    if TableA[2] eq 1 or JacSchRec`DegAlreadyTested eq (r^4-1) then
	JacSchRec`finished := true;
    end if;
    // Check the possible cardinalities with the remaining pairs
    SNJ := {};
    for i := 0 to r-1 do
	for j := 0 to r-1 do
	    if TableA[1][i+1][j+1] eq 0 then continue;
	    else
		a1 := i; a2 := j;
		Include(~SNJ, (q^2+q*a1+a2+a1+1) mod r);
	    end if;
	end for;
    end for;
    vprintf JacHypCnt, 3 :  "The possible values for |J| are %o\n", SNJ;
    JacSchRec`NbCandidates := #SNJ;
    if #SNJ eq 1 then 
	JacSchRec`finished := true;
    end if;
end procedure;
	

function TheSolution(JacSchRec)
    r := JacSchRec`r;
    q := JacSchRec`q;

    assert(JacSchRec`finished);
    
    if JacSchRec`NbCandidates ne 1 then
	CleanWhenFailed(~JacSchRec);
    end if;
    if JacSchRec`NbCandidates ne 1 then
	vprintf JacHypCnt, 3 :  "unable to conclude!!!!!\n";
	assert(false);
	return [-1];
    end if;
    TableA := JacSchRec`TableA;
    for i := 0 to r-1 do
	for j := 0 to r-1 do
	    if TableA[1][i+1][j+1] eq 0 then continue;
	    else a1 := i; a2 := j; break;
	    end if;
	end for;
    end for;
    return (q^2+q*a1+a2+a1+1) mod r;
end function;


procedure CleanWhenFailed(~JacSchRec)
    r := JacSchRec`r;
    q := JacSchRec`q;
    PP := PolynomialRing(ResidueClassRing(r)); Z := PP.1;
    TableA := JacSchRec`TableA;
    SetPol := [];
    TheGCD := PP!0;
    for i := 0 to r-1 do
	for j := 0 to r-1 do
	    if TableA[1][i+1][j+1] eq 0 then
		continue;
	    else
		a1 := i; a2 := j;
		Pol := Z^4+a1*Z^3+a2*Z^2+q*a1*Z+q^2;
		vprintf JacHypCnt, 3 :  "%o\n", Factorization(Pol);
		Append(~SetPol, Pol);
		TheGCD := GCD(TheGCD, Pol);
	    end if;
	end for;
    end for;
    vprintf JacHypCnt, 3 :  "The GCD of these possibilities is %o\n", TheGCD;
    SetFact := { ff[1] : ff in Factorization(TheGCD) };
    Candid := [];
    for Pol in SetPol do
	factPol := { ff[1] : ff in Factorization(Pol) };
	if factPol subset SetFact then
	    vprintf JacHypCnt, 3 :  "%o\n", Pol;
	    Append(~Candid, Pol);
	end if;
    end for;
    assert #Candid ge 1;
    if #Candid gt 1 then
	vprintf JacHypCnt, 3 :  "Cannot conclude!\n";
    end if;
    for i := 0 to r-1 do
	for j := 0 to r-1 do
	    JacSchRec`TableA[1][i+1][j+1] := 0;
	end for;
    end for;
    for Pol in Candid do
	a1 := Integers()!Coefficient(Pol, 3);
	a2 := Integers()!Coefficient(Pol, 2);
	JacSchRec`TableA[1][a1+1][a2+1] := 1;
    end for;
    JacSchRec`TableA[2] := #Candid;
    SNJ := {};
    for i := 0 to r-1 do
	for j := 0 to r-1 do
	    if JacSchRec`TableA[1][i+1][j+1] eq 0 then continue;
	    else
		a1 := i; a2 := j;
		Include(~SNJ, (q^2+q*a1+a2+a1+1) mod r);
	    end if;
	end for;
    end for;
    vprintf JacHypCnt, 3 :  "The possible values for |J| are %o\n", SNJ;
    JacSchRec`NbCandidates := #SNJ;
    UpdateFinished(~JacSchRec);
end procedure;


procedure TestWithADivisor(~JacSchRec, Div, ~factorList)
    r := JacSchRec`r;
    q := JacSchRec`q;
    Fq := BaseRing(JacSchRec`J);
    Jext := Parent(Div);
        
    // Precompute some divisors:
    timePrec := Cputime();
    vprintf JacHypCnt, 3 :  "Precomputing some divisors...\n";
    FrDiv1 := Frobenius(Div,    Fq);
    FrDiv2 := Frobenius(FrDiv1, Fq);
    FrDiv3 := Frobenius(FrDiv2, Fq);
    FrDiv4 := Frobenius(FrDiv3, Fq);
    A := ((q^2) mod r)*Div + FrDiv4;
    B := (q mod r)*FrDiv1 + FrDiv3;
    timePrec := Cputime() - timePrec;
    vprintf JacHypCnt, 3 :  "done  in %o sec\n", timePrec;
    // Use some kind of BSGS:
    timeTest := Cputime();
    vprintf JacHypCnt, 3 :  "Testing all the pairs...\n";
    IndentPush();
    LHS := A; SetLHS := [ A ];
    for a1 := 1 to r-1 do
	LHS +:= B;
	Append(~SetLHS, LHS);
    end for;
    MFrD2 := -FrDiv2;
    RHS := Jext!0;
    for a1 := 0 to r-1 do
	if RHS eq SetLHS[a1+1] then
	    vprintf JacHypCnt, 3 :  "remaining candidate: (%o, %o)\n", a1, 0;
	else
	    if (JacSchRec`TableA[1][a1+1][1]) eq 1 then
		JacSchRec`TableA[2] -:= 1;
		JacSchRec`TableA[1][a1+1][1] := 0;
	    end if;
	end if;
    end for;
    for a2 := 1 to r-1 do
	RHS +:= MFrD2;
	for a1 := 0 to r-1 do
	    if RHS eq SetLHS[a1+1] then
		vprintf JacHypCnt, 3 :  "remaining candidate: (%o, %o)\n", a1, a2;
	    else
		if (JacSchRec`TableA[1][a1+1][a2+1]) eq 1 then
		    JacSchRec`TableA[1][a1+1][a2+1] := 0;
		    JacSchRec`TableA[2] -:= 1;
		end if;
	    end if;
	end for;
    end for;
    IndentPop();
    timeTest := Cputime() - timeTest;
    vprintf JacHypCnt, 3 :  "done  in %o sec\n", timeTest;
    vprintf JacHypCnt, 3 :  "We have now %o choices\n", JacSchRec`TableA[2];

    UpdateFinished(~JacSchRec);
    if IsFinished(JacSchRec) then return; end if;

    if #JacSchRec`Generators eq 3 then
	Append(~JacSchRec`Generators, Div);
	vprintf JacHypCnt, 3 :  "We have now tested generators of the complete r-torsion group.\n";
	JacSchRec`finished := true;
	return;
    end if;
    
    //////////////////////////////////////////////////////////////////
    // Use the divisor to find other r-torsion elements and eliminate
    // the corresponding factors in Res
    //////////////////////////////////////////////////////////////////
    
    vprintf JacHypCnt, 3 :  "Purging Res using subgroup generating by the divisor...\n";
    timePurge := Cputime();
    PurgeRes(~JacSchRec, ~factorList, Div);
    Append(~JacSchRec`Generators, Div);
    vprintf JacHypCnt, 3 :  "Nb of generators: %o\n", #JacSchRec`Generators;
    timePurge := Cputime()- timePurge;
    vprintf JacHypCnt, 3 :  "done  in %o sec\n", timePurge;
    UpdateFinished(~JacSchRec);
end procedure;


procedure TestWithAFormalDivisor(~JacSchRec, Div, f, FX1, ~factorList)
    r := JacSchRec`r;
    q := JacSchRec`q;
    Fq := BaseRing(JacSchRec`J);
    
    // Precompute some divisors:
    timePrec := Cputime();
    vprintf JacHypCnt, 3 :  "Precomputing some divisors...\n";
    FrDiv1 := DivFrobeniusFormal(Div, f, FX1, Fq);
    FrDiv2 := DivFrobeniusFormal(FrDiv1, f, FX1, Fq);
    FrDiv3 := DivFrobeniusFormal(FrDiv2, f, FX1, Fq);
    FrDiv4 := DivFrobeniusFormal(FrDiv3, f, FX1, Fq);
    A := DivAddFormal( DivMultFormal(((q^2) mod r), Div, f, FX1),
                       FrDiv4, f, FX1);
    B := DivAddFormal( DivMultFormal((q mod r), FrDiv1, f, FX1),
                       FrDiv3, f, FX1);
    timePrec := Cputime() - timePrec;
    vprintf JacHypCnt, 3 :  "done  in %o sec\n", timePrec;
    // Use some kind of BSGS:
    timeTest := Cputime();
    vprintf JacHypCnt, 3 :  "Testing all the pairs...\n";
    IndentPush();
    LHS := A; SetLHS := [ A ];
    for a1 := 1 to r-1 do
	LHS := DivAddFormal(LHS, B, f, FX1);
	Append(~SetLHS, LHS);
    end for;
    MFrD2 := DivNegateFormal(FrDiv2, f, FX1);
    RHS := [Parent(Div[1])!1, 0];
    for a1 := 0 to r-1 do
	if RHS eq SetLHS[a1+1] then
	    vprintf JacHypCnt, 3 :  "remaining candidate: (%o, %o)\n", a1, 0;
	else
	    if (JacSchRec`TableA[1][a1+1][1]) eq 1 then
		JacSchRec`TableA[2] -:= 1;
		JacSchRec`TableA[1][a1+1][1] := 0;
	    end if;
	end if;
    end for;
    for a2 := 1 to r-1 do
	RHS := DivAddFormal(MFrD2, RHS, f, FX1);
	for a1 := 0 to r-1 do
	    if RHS eq SetLHS[a1+1] then
		vprintf JacHypCnt, 3 :  "remaining candidate: (%o, %o)\n", a1, a2;
	    else
		if (JacSchRec`TableA[1][a1+1][a2+1]) eq 1 then
		    JacSchRec`TableA[1][a1+1][a2+1] := 0;
		    JacSchRec`TableA[2] -:= 1;
		end if;
	    end if;
	end for;
    end for;
    IndentPop();
    timeTest := Cputime() - timeTest;
    vprintf JacHypCnt, 3 :  "done  in %o sec\n", timeTest;
    vprintf JacHypCnt, 3 :  "We have now %o choices\n", JacSchRec`TableA[2];
    UpdateFinished(~JacSchRec);
end procedure;


procedure UpdateTable(~JacSchRec, factorList, squarefact)
    while #factorList gt 0 do
	factor := factorList[#factorList];
	Prune(~factorList);
	while true do
	    quo0, rem := Quotrem(JacSchRec`Res, factor);
	    if rem ne 0 then break; end if;
	    JacSchRec`Res := quo0;
	end while;
	vprintf JacHypCnt, 3 :  "Deal with factor %o...\n", factor;
	if squarefact then
	    vprintf JacHypCnt, 3 :  "(appears several times in Res)\n";
	end if;
	q := JacSchRec`q;
	r := JacSchRec`r;
	Fq := BaseRing(Parent(factor));
	J := JacSchRec`J;
	f := HyperellipticPolynomials(Curve(J));
	D0   := JacSchRec`D0;   D1   := JacSchRec`D1;
	d2   := JacSchRec`d2;	Eps0 := JacSchRec`Eps0;
	Eps1 := JacSchRec`Eps1; Denom := JacSchRec`Denom;

	//////////////////////////////////////////////////////////////////////
	// Build the divisor corresponding to factor
	//////////////////////////////////////////////////////////////////////
	// build X1 over Fq1
	if Degree(factor) eq 1 then
	    X1 := -Coefficient(factor, 0);
	    Fq1 := Fq;
	else
	    Fq1<t> := ext<Fq | factor>;
	    X1 := t;
	end if;

	// build X2 over Fq1
	vprintf JacHypCnt, 3 :  "build X2...\n";
	if squarefact and Degree(factor) eq 1 then
	    SetX2 := [X1];
	else
	    PPFq1 := PolynomialRing(Fq1); Z := PPFq1.1;
	    EE1 := Evaluate(D1, X1)*Evaluate(d2, Z)
	    - Evaluate(D1, Z)*Evaluate(d2,X1);
	    EE1 := EE1 div (X1-Z);
	    EE2 := Evaluate(D0, X1)*Evaluate(d2, Z)
	    - Evaluate(D0, Z)*Evaluate(d2,X1);
	    EE2 := EE2 div (X1-Z);
	    vprintf JacHypCnt, 3 :  "compute the GCD...\n";
	    timeGCD := Cputime();
	    TheGCD := GCD(EE1, EE2);  
	    timeGCD := Cputime()-timeGCD;
	    vprintf JacHypCnt, 3 :  "done in %o sec.\n", timeGCD;
	    
	    if Degree(TheGCD) eq 1 then
		assert Coefficient(TheGCD, 1) eq 1;
		SetX2 := [-Coefficient(TheGCD, 0)];
	    else
		roots_TheGCD := Roots(TheGCD);
		if #roots_TheGCD eq 0 then
		    vprintf JacHypCnt, 3 :  "this is a parasite solution: skip it.\n";
		    continue;
		else
		    vprintf JacHypCnt, 3 :  "Warning: %o values of X2\n", #roots_TheGCD;
		    SetX2 := [rr[1] : rr in roots_TheGCD];
		end if;
	    end if;
	end if;

	for XX2 in SetX2 do
	    X1 := Fq1!X1;
	    X2 := XX2;
	    // first check that it is not a parasite:
	    EE3 := Evaluate(Eps1, X1)*Evaluate(Eps0, X2)
	    - Evaluate(Eps1, X2)*Evaluate(Eps0,X1);
	    if EE3 ne 0 then
		vprintf JacHypCnt, 3 :  "this is a parasite solution: skip it.\n";
		continue;
	    end if;
	    // build Y1 and Y2 over Fq2
	    Y2OverY1 := (Evaluate(Eps1, X2)*Evaluate(Denom,X1));
	    if Y2OverY1 eq 0 then
		HasY2OverY1 := false;
		vprintf JacHypCnt, 3 :  "we can not compute Y2/Y1...\n";
	    else
		Y2OverY1 := -Evaluate(Eps1, X1)*Evaluate(Denom, X2)/Y2OverY1;
		HasY2OverY1 := true;
		vprintf JacHypCnt, 3 :  "computed Y2/Y1.\n";
	    end if;
	    
	    vprintf JacHypCnt, 3 :  "build Yi...\n";
	    timeBuildYi := Cputime();
	    FX1 := Evaluate(f, X1);
	    t1, Y1 := IsSquare(FX1);
	    timeBuildYi := Cputime()-timeBuildYi;
	    vprintf JacHypCnt, 3 :  "IsSqr done in %o sec.\n", timeBuildYi;
	    if t1 or Degree(factor) le 4 or not HasY2OverY1 then
		// build Y1:
		if t1 then
		    Fq2 := Fq1;
		else
		    // make a unique extension instead of a tower ?
		    // according to Allan, this is not necessary...
		    vprintf JacHypCnt, 3 :  "have to go to an extension...\n";
		    timeBuildYi := Cputime();
		    Fq2 := ext<Fq1|2>;
		    X1 := Fq2!X1;
		    X2 := Fq2!X2;
		    FX1 := Evaluate(PolynomialRing(Fq2)!f, X1);
		    t1, Y1 := IsSquare(FX1);
		    assert(t1);
		    timeBuildYi := Cputime()-timeBuildYi;
		    vprintf JacHypCnt, 3 :  "done in %o sec.\n", timeBuildYi;
		end if;
		
		// build Y2
		if HasY2OverY1 then 
		    Y2 := Fq2!Y2OverY1*Y1;
		elif squarefact and Degree(factor) eq 1 then
		    Y2 := Y1;
		else
		    FX2 := Evaluate(f, X2);
		    t2, Y2 := IsSquare(FX2);
		    if not t2 then
			vprintf JacHypCnt, 3 :  "this is a strange case... can not build Y2.\nSkip it.\n";
			continue;
		    end if;
		end if;
		// Build the two divisors Div1 and Div2 over Fq2
		PPext := PolynomialRing(Fq2); X := PPext.1;
		Jext := BaseChange(J, Fq2);
		Div1 := Jext ! [X-X1, Y1];
		Div2 := Jext ! [X-X2, Y2];
		// Check that Div1+Div2 is of r-torsion (should be!)
		vprintf JacHypCnt, 3 :  "Checking that we get a r-torsion divisor...\n";
		timeCheck := Cputime();
		Div := Div1 + Div2;
		if IsZero(Div) or not IsZero(r*Div) then
		    vprintf JacHypCnt, 3 :  "Your curve is highly non-generic ;-)...\n";
		    continue;
		end if;

		if squarefact then 
		    JacSchRec`DegAlreadyTested +:= 2*Degree(factor);
		else
		    JacSchRec`DegAlreadyTested +:= Degree(factor);
		end if;
		    
		timeCheck := Cputime() - timeCheck;
		vprintf JacHypCnt, 3 :  "done  in %o sec\n", timeCheck;
		TestWithADivisor(~JacSchRec, Div, ~factorList);
	    else
		// HERE WE DON'T BUILD THE EXTENSION FOR Y:
		// we use formal representation with FX1
		// the polynomialRing is PPFq1<Z>
		assert HasY2OverY1;
		vprintf JacHypCnt, 3 :  "Using the formal expression of divisors instead of the extension\n";

		Div1 := [Z-X1, 1];
		Div2 := [Z-X2, Y2OverY1];
		vprintf JacHypCnt, 3 :  "Checking that we get a r-torsion divisor...\n";
		timeCheck := Cputime();
		Div := DivAddFormal(Div1, Div2, f, FX1);
		if DivIsZeroFormal(Div)
		    or not DivIsZeroFormal(DivMultFormal(r, Div, f, FX1)) then
		    vprintf JacHypCnt, 3 :  "Your curve is highly non-generic ;-)...\n";
		    continue;
		end if;
		
		if squarefact then 
		    JacSchRec`DegAlreadyTested +:= 2*Degree(factor);
		else
		    JacSchRec`DegAlreadyTested +:= Degree(factor);
		end if;
		
		timeCheck := Cputime() - timeCheck;
		vprintf JacHypCnt, 3 :  "done  in %o sec\n", timeCheck;
		
		TestWithAFormalDivisor(~JacSchRec, Div, f, FX1, ~factorList);
	    end if;

	    if IsFinished(JacSchRec) then
		return;
	    end if;
	end for;
    end while;
end procedure;


procedure UpdateTableTheta(~JacSchRec, factorList)
    while #factorList gt 0 do
	factor := factorList[#factorList];
	Prune(~factorList);
	vprintf JacHypCnt, 3 :  "Deal with factor %o...\n", factor;
	
	q := JacSchRec`q;
	r := JacSchRec`r;
	Fq := BaseRing(Parent(factor));
	J := JacSchRec`J;
	f := HyperellipticPolynomials(Curve(J));
	D0   := JacSchRec`D0;   D1   := JacSchRec`D1;
	d2   := JacSchRec`d2;	Eps0 := JacSchRec`Eps0;
	Eps1 := JacSchRec`Eps1; Denom := JacSchRec`Denom;
	
	//////////////////////////////////////////////////////////////////////
	// Build the divisor corresponding to factor
	//////////////////////////////////////////////////////////////////////
	// build X1 over Fq1
	if Degree(factor) eq 1 then
	    X1 := -Coefficient(factor, 0);
	    Fq1 := Fq;
	else
	    Fq1<t> := ext<Fq | factor>;
	    X1 := t;
	end if;
	
	vprintf JacHypCnt, 3 :  "build Y1...\n";
	timeBuildY1 := Cputime();
	FX1 := Evaluate(f, X1);
	t1, Y1 := IsSquare(FX1);
	timeBuildY1 := Cputime()-timeBuildY1;
	vprintf JacHypCnt, 3 :  "IsSqr done in %o sec.\n", timeBuildY1;
	if t1 or Degree(factor) le 4 then
	    // build Y1:
	    if t1 then
		Fq2 := Fq1;
	    else
		vprintf JacHypCnt, 3 :  "have to go to an extension...\n";
		timeBuildYi := Cputime();
		Fq2 := ext<Fq1|2>;
		X1 := Fq2!X1;
		FX1 := Evaluate(PolynomialRing(Fq2)!f, X1);
		t1, Y1 := IsSquare(FX1);
		assert(t1);
		timeBuildYi := Cputime()-timeBuildYi;
		vprintf JacHypCnt, 3 :  "done in %o sec.\n", timeBuildYi;
	    end if;
	    
	    // Build the two divisors Div1 over Fq2
	    PPext := PolynomialRing(Fq2); X := PPext.1;
	    Jext := BaseChange(J, Fq2);
	    Div := Jext ! [X-X1, Y1];
	    // Check that Div is of r-torsion (should be!)
	    vprintf JacHypCnt, 3 :  "Checking that we get a r-torsion divisor...\n";
	    timeCheck := Cputime();
	    if IsZero(Div) or not IsZero(r*Div) then
		vprintf JacHypCnt, 3 :  "Your curve is highly non-generic ;-)...\n";
		continue;
	    end if;
	    timeCheck := Cputime() - timeCheck;
	    vprintf JacHypCnt, 3 :  "done  in %o sec\n", timeCheck;
	    TestWithADivisor(~JacSchRec, Div, ~factorList);
	else
	    // HERE WE DON'T BUILD THE EXTENSION FOR Y:
	    // we use formal representation with FX1
	    // the polynomialRing is PPFq1<Z>
	    vprintf JacHypCnt, 3 :  "Using the formal expression of divisors instead of the extension\n";
	    PPFq1 := PolynomialRing(Fq1); Z := PPFq1.1;
	    Div := [Z-X1, 1];
	    vprintf JacHypCnt, 3 :  "Checking that we get a r-torsion divisor...\n";
	    timeCheck := Cputime();
	    if DivIsZeroFormal(Div)
		or not DivIsZeroFormal(DivMultFormal(r, Div, f, FX1)) then
		vprintf JacHypCnt, 3 :  "Your curve is highly non-generic ;-)...\n";
		continue;
	    end if;
	    
	    timeCheck := Cputime() - timeCheck;
	    vprintf JacHypCnt, 3 :  "done  in %o sec\n", timeCheck;
	    
	    TestWithAFormalDivisor(~JacSchRec, Div, f, FX1, ~factorList);
	end if;

	if IsFinished(JacSchRec) then
	    return;
	end if;
    end while;
end procedure;


// Addition in the Jacobian when J is defined over Fq,
// but D1 and D2 are defined over (distinct) extensions of Fq

function MyDivAdd(D1, D2, Fq)
    Fq1 := BaseRing(Parent(D1));
    Fq2 := BaseRing(Parent(D2));
    if #Fq1 eq #Fq2 then
	Embed(Fq1, Fq2);
	return D1 + Parent(D1)!D2;
    end if;
    deg1 := Degree(Fq1, Fq);
    deg2 := Degree(Fq2, Fq);
    deg := LCM(deg1, deg2);
    if deg eq deg1 then
	Fq := Fq1;
	Embed(Fq2, Fq1);
	DD1 := D1;
	DD2 := Parent(D1)!D2;
    elif deg eq deg2 then
	Fq := Fq2;
	Embed(Fq1, Fq2);
	DD2 := D2;
	DD1 := Parent(D2)!D1;
    else
	Fq := ext <Fq | deg>;
	Embed(Fq1, Fq);
	Embed(Fq2, Fq);
	J := BaseChange(Parent(D1), Fq);
	DD1 := J! D1;
	DD2 := J! D2;
    end if;
    return DD1 + DD2;
end function;


procedure PurgeRes(~JacSchRec, ~factorList, Div)
    DD := Div;
    Gen := JacSchRec`Generators;
    AddAllCombination(~JacSchRec, ~factorList, DD, Gen);
    if JacSchRec`DegAlreadyTested ge JacSchRec`r^4-1 then
	return;
    end if;
    for i := 2 to JacSchRec`r-1 do
	DD := MyDivAdd(Div, DD, BaseRing(JacSchRec`J));
	AddAllCombination(~JacSchRec, ~factorList, DD, Gen);
	if JacSchRec`DegAlreadyTested ge JacSchRec`r^4-1 then
	    return;
	end if;
    end for;
end procedure;

// TODO: improve this ?  (avoid factorization?)

procedure AddAllCombination(~JacSchRec, ~factorList, DD, Gen)
    Fq := BaseRing(JacSchRec`J);
    if #Gen eq 0 then
/*	tps := Cputime();
	firstfact := GCD(JacSchRec`Res, DD[1]);
	vprintf JacHypCnt, 3 :  "GCD done in %o sec\n", Cputime()-tps;
	if Degree(firstfact) eq 0 then return; end if;
	*/ firstfact := DD[1];
	tps := Cputime();
	fact := Factorization(firstfact);
	vprintf JacHypCnt, 3 :  "factorization done in %o sec\n", Cputime()-tps;
	fact := [ff[1] : ff in fact];
	if BaseRing(Parent(DD[1])) ne Fq then
	    newfact := [];
	    for ff in fact do
		if Degree(ff) eq 1 then
		    cc := -Coefficient(ff, 0);
		    Append(~newfact, MinimalPolynomial(cc, Fq));
		else
		    Fq2<t> := ext < BaseRing(Parent(ff)) | ff >;
		    Append(~newfact, MinimalPolynomial(t, Fq));
		end if;
	    end for;
	    fact := newfact;
	end if;
	for fac in fact do
	    qq, rr := Quotrem(JacSchRec`Res, fac);
	    if (rr eq 0) and (Degree(qq) lt Degree(JacSchRec`Res)) then
		vprintf JacHypCnt, 3 :  "eliminate a factor of degree %o in Res...\n", Degree(fac) ;
		JacSchRec`Res := qq;
		JacSchRec`DegAlreadyTested +:= Degree(fac);
		if JacSchRec`DegAlreadyTested ge JacSchRec`r^4-1 then
		    return;
		end if;
	    end if;
	    Idx := Index(factorList, fac);
	    if Idx ne 0 then
		vprintf JacHypCnt, 3 :  "eliminate a factor in factorList...\n";
		Remove(~factorList, Idx);
	    end if;
	end for;
	vprintf JacHypCnt, 3 :  "purge done in %o sec\n", Cputime()-tps;
    else
	g := Gen[#Gen];
	Prune(~Gen);
	AddAllCombination(~JacSchRec, ~factorList, DD, Gen);
	for i := 1 to JacSchRec`r-1 do
	    DD := MyDivAdd(g, DD, Fq);
	    AddAllCombination(~JacSchRec, ~factorList, DD, Gen);
	end for;
    end if;
end procedure;


///////////////////////////////////////////////////////////////////////////
// Assume: Deg(d0)=Deg(d1)+1=Deg(d2)+2
//
// return the resultant Res( E1, E2, x2), where
//    E1:=( d1(x1)*d2(x2)-d1(x2)*d2(x1) ) / (x1-x2);
//    E2:=( d0(x1)*d2(x2)-d0(x2)*d2(x1) ) / (x1-x2);
// we eliminate the power of d2 which appears in the result.

// intrinsic Resultant1(d0:: RngUPolElt, d1::RngUPolElt, d2::RngUPolElt)
//               -> RngUPolElt
function Resultant1(d0, d1, d2)
    PowerOfd2 := Degree(d2);
    Delta := Degree(d1)*Degree(d2); // The degree of the resultant we search
    PP := Parent(d0);
    x := PP.1;
    Fq := BaseRing(PP);
    tps_total := Cputime();
  
    tps_eval := 0;
    tps_resultant := 0;
  
    Abscissae := [];
    Ordinates := [];
    // Evaluate the resultant at Delta+1 random points
    repeat xi := Random(Fq); until xi ne 0;
    error if #Fq le Delta+Degree(d2)+1,
"the base field is not large enough for interpolation / evaluation technique";
    for i := 1 to Delta+1 do
	tps := Cputime();
	d2i := Evaluate(d2, xi);
	while (d2i eq 0) do
	    vprintf JacHypCnt, 3 :  "root of d2... skipping\n";
	    if PrimeField(Fq) eq Fq then
		xi := xi+1;
	    else
		xi := xi*PrimitiveElement(Fq);
	    end if;
	    d2i := Evaluate(d2, xi);
	end while;
	d0i := Evaluate(d0, xi);
	d1i := Evaluate(d1, xi);
	E1i := d1i*d2-d1*d2i;
	E2i := d0i*d2-d0*d2i;
	E1i := Quotrem(E1i, x-xi);
	E2i := Quotrem(E2i, x-xi);
	tps_eval +:= Cputime()-tps;
	tps := Cputime();
	Ri := Resultant(E1i, E2i)/(d2i^PowerOfd2);
	tps_resultant +:= Cputime()-tps;
	Append(~Abscissae, xi);
	Append(~Ordinates, Ri);
	if PrimeField(Fq) eq Fq then
	    xi := xi+1;
	else
	    xi := xi*PrimitiveElement(Fq);
	end if;
    end for;
    
    // Reconstruct the resultant by interpolation
    tps := Cputime();
    Res := FastInterpolate(Abscissae, Ordinates);
    tps_interp := Cputime()-tps;
    vprintf JacHypCnt, 3 :
        "eval: %o, result: %o, interp: %o\n",
    tps_eval, tps_resultant, tps_interp;
    vprintf JacHypCnt, 3 : "total: %o\n", Cputime()-tps_total;
    return Res;
end function;


///////////////////////////////////////////////////////////////////////////
// Assume: Deg(d1)=Deg(d2)+1
//         Deg(eps0)=?
//         Deg(eps1)=?
// return the resultant Res( E1, E3, x2), where
//    E1:=( d1(x1)*d2(x2)-d1(x2)*d2(x1) ) / (x1-x2);
//    E3:=( eps1(x1)*eps0(x2)-eps0(x1)*eps1(x2) ) / (x1-x2);

// intrinsic Resultant2(eps0::RngUPolElt, eps1::RngUPolElt,
//                      d1::RngUPolElt, d2::RngUPolElt) -> RngUPolElt

function Resultant2(eps0, eps1, d1, d2)
    Delta := 2*(Degree(d1)-1)*(Max(Degree(eps0),Degree(eps1))-1);
    // (A bound for) the degree of the resultant we search
    PP := Parent(d1);
    x := PP.1;
    Fq := BaseRing(PP);
    tps_total := Cputime();
    tps_eval := 0;
    tps_resultant := 0;
  
    Abscissae := [];
    Ordinates := [];
    // Evaluate the resultant at Delta+1 random points
    repeat xi := Random(Fq); until xi ne 0;
    error if #Fq le Delta+1 + Degree(eps1) + Degree(d2),
"the base field is not large enough for interpolation / evaluation technique";
    for i := 1 to Delta+1 do
	tps := Cputime();
	d2i := Evaluate(d2, xi);
	eps1i := Evaluate(eps1, xi);
	while (d2i eq 0) or (eps1i eq 0) do
	    vprintf JacHypCnt, 3 :  "root of d2 or esp1... skipping\n";
	    if PrimeField(Fq) eq Fq then
		xi := xi+1;
	    else
		xi := xi*PrimitiveElement(Fq);
	    end if;
	    d2i := Evaluate(d2, xi);
	    eps1i := Evaluate(eps1, xi);
	end while;
	d1i := Evaluate(d1, xi);
	eps0i := Evaluate(eps0, xi);
	E1i := -d1i*d2+d1*d2i;
	E2i := -eps1i*eps0+eps1*eps0i;
	E1i := Quotrem(E1i, x-xi);
	E2i := Quotrem(E2i, x-xi);
	tps_eval +:= Cputime()-tps;
	tps := Cputime();
	Ri := Resultant(E1i, E2i);
	tps_resultant +:= Cputime()-tps;
	Append(~Abscissae, xi);
	Append(~Ordinates, Ri);
	if PrimeField(Fq) eq Fq then
	    xi := xi+1;
	else
	    xi := xi*PrimitiveElement(Fq);
	end if;
    end for;

    // Reconstruct the resultant by interpolation
    tps := Cputime();
    Res := FastInterpolate(Abscissae, Ordinates);
    tps_interp := Cputime()-tps;
    vprintf JacHypCnt, 3 :
        "eval: %o, result: %o, interp: %o\n",
	tps_eval, tps_resultant, tps_interp;
    vprintf JacHypCnt, 3 : "total: %o\n", Cputime()-tps_total;
    return Res;
end function;




///////////////////////////////////////////////////////////////////////////
//
//  Fast Evaluation / Interpolation
//  Following functions have been written by G. Lecerf
//  (only very slightly modified)
//
///////////////////////////////////////////////////////////////////////////

//  The algorithm are POL.EVAL and POL.INTERP
//  from BINI and PAN, "Polynomial and Matrix Computations", volume 1,
//    "Fundamental Algorithms", Birkh\"auser, 1994
//
// POL.EVAL and POL.INTERP methods are described p.25.
//
// Complexity: M(n)Log(n), where n is either the number of points to
//   interpolate or evaluate.
//
// By Gr\'egoire LECERF
// 1999, Laboratoire GAGE, Ecole polytechnique
// 91128 Palaiseau France.
//
// Gregoire.Lecerf@gage.polytechnique.fr
//

// THRESHOLD for divide and conquer: do not divide when less than THRESHOLD.
THRESHOLD:=7;

FanIn:=function(x)
//~~~~~~~~~~~~~~~~
     /*
       intput: x is a sequence of numbers in a fields

       output: a sequence l of sequences of the divide and conquer products
                 T-x[i]

       let m=#l, n=#x, r=THRESHOLD, then

       l[m] = [ (T-x[1])...(T-x[r]), ..., (T-x[r*(i-1)+1])...(T-x[r*i]),
                     (T-x[r*i+1])...(T-x[n])]
       l[m-1] = [ l[m][1]*l[m][2], l[m][3]*l[m][4], .... ]
         ...
       l[1] = (T-x[1])...(T-x[n])
     */

     n:=#x;

     UP := PolynomialAlgebra(Universe(x)); T := UP.1;
     a:=n div THRESHOLD;

     L:=[ &*[T-x[i] : i in [THRESHOLD*j+1..(j+1)*THRESHOLD]]: j in [0..a-1]];

     if n gt THRESHOLD*a then
       Append(~L,&*[T-x[i] : i in [THRESHOLD*a+1..n]]);
       a+:=1;
     end if;

     l:=[* L *];

     while a gt 1 do
       last:=L[a];
       b := a div 2;
       L:= [ L[2*i+1]*L[2*(i+1)] : i in [0..b-1]];
       if (a mod 2 ) eq 1 then
         Append(~L,last);
         b+:=1;
       end if;
       a:=b;
       Append(~l,L);

     end while;

     return(Reverse([z : z in l]));
end function;



SubFastEvaluate:=function(p,x,fanin)
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

     /*
       p is a polynomial over a field F
       x is a sequence of elements in F

       return the sequence of values [p(z) : z in x];

       if deg(p)+1 = #x = n , the complexit is 
      */

  L:=[p];

  for Q in fanin do
    L:=[L[((j-1) div 2)+1] mod Q[j]: j in [1..#Q]];
  end for;

  i:=1;
  l:=[];
  n:=#x; // (NOT NEC.) Degree(p)+1;!!!
  for q in L do
    d:=THRESHOLD;
    for j := i to Min(n,i+d-1) do
      Append(~l,Evaluate(q,x[j]));
    end for;
    i+:=d;
  end for;

  return(l);
end function;

function FastEvaluate(p, x)
  return(SubFastEvaluate(p,x,FanIn(x)));
end function;


function FastInterpolate(x, r)
  n:=#x;
  fanin:=FanIn(x);

  L:=fanin[1];
  w:=SubFastEvaluate(Derivative(L[1]),x,fanin);

  p:=[r[i]/w[i] : i in [1..#r]];

  F:=fanin[#fanin];

  P:=[];
  i:=0;
  for f in F do
    Append(~P,Interpolation(
         [x[i+j]: j in [1..Degree(f)]],
         [p[i+j]*Evaluate(Derivative(f),x[i+j]): j in [1..Degree(f)]]));
    i+:=Degree(f);
  end for;

  p:=[e : e in P];

  for k:=1 to #fanin-1 do
    F:=fanin[#fanin-k+1];
    last:=p[#p];
    p:= [ p[2*i+1]*F[2*(i+1)] + F[2*i+1]*p[2*(i+1)] : i in [0..(#F div 2)-1]];
    if (#F mod 2 ) eq 1 then
      Append(~p,last);
    end if;

  end for;

  return(p[1]);
end function;
