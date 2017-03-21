freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    
//  Counting point in genus 2                                             
//
//  P. Gaudry (March 2001)
//                                                                    
////////////////////////////////////////////////////////////////////////
//
//  non-exported function:
//     JacobianOrderGenus2 (J::JacHyp) -> RngIntElt
//  (used by Order() )
//
///////////////////////////////////////////////////////////////////////
//
//  This file contains things to mix all the algorithms, and tries to
//  always choose the best strategy.
//  (Tuning can be done with the functions at the end of the file)
//
///////////////////////////////////////////////////////////////////////

/*
CHANGES:

   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
                 fix Curve

   2004-03: Mike Harrison
   Removed the code at the start of JacobianOrderGenus2 to check
   for small field size (for naive count) and to check for
   definition over a smaller field. These operations are now
   performed earlier in the Hyperelliptic Curve and Jacobian code.

  ------------------------------------------------------------------*/




/* FIXME:

The following curve is *very* pathological: its jacobian is the
product of two supersingular elliptic curves (j=1728 & 287496).
The group is the direct product of the two ell curves -> very low
exponent.  

f:=x^5+(p-5)/2*x^4+2*(p+13)/9*x^3+(p-11)/6*x^2+2*(p+1)/3*x+(2*p-1)/9;

where p = 3 mod 4.

#Jac = (p+1)^2 = p^2 + 2*p + 1
EulerFactor = (T^2 + p)^2

Goal: the program should pass this curve!

*/

// forwards ...
forward COST_SCHOOF;
forward COST_CM;
forward COST_SQRT;
forward COST_TTM;

// imports : get functions from various files:
//////////////////////////////////////////////

// generic computations:
import "../CrvHyp/jac_count.m" : NaiveEuler,
    TwoTorsionSubgroupOrder, GetBounds, JacobianOrderSquareRoot, Shanks;

// Schoof computations:
import "schoof.m" : JacSchoof;

// Two-Tate Module:
import "twotorsionlift.m" : InitTwoTateModule, TTMNextSmallestDegree,
    ClimbTwoTateModuleNext, ExtractInfoFromTTM;




///////////////////////////////////////////////////////////////////////////
//
//  Main function: JacobianOrderGenus2
//     (called by 'Order')
//
///////////////////////////////////////////////////////////////////////////

// intrinsic JacobianOrderGenus2(J::JacHyp) -> RngIntElt
//     { The order of the Jacobian J of genus 2 defined over a finite field. }

function JacobianOrderGenus2(J : ShanksLimit := 10^12,
                                 CartierManinLimit := 5*10^5,
	                         UseSchoof := true,
	                         UseHalving := true)
    assert IsFinite(BaseField(J));
    assert Dimension(J) eq 2;

    Fq := BaseRing(J);
    q := #BaseRing(J);
    p := Characteristic(Fq);
    n := Degree(Fq);

    // if small group, then naive (because it's difficult to obtain
    // proven results with Shanks' method)
    // use also naive if no addition law is implemented
    if J`Type eq 0 or (q^2) le 20000 then //should never happen now!!
        J`EulerFactor := NaiveEuler(Curve(J),1);
	NJ := &+ Coefficients(J`EulerFactor);
    else
	// Simplify the model of the curve if necessary (and if possible!)
	f, h := HyperellipticPolynomials(Curve(J));
	if IsEven(q) then
	    HasSchoof := false;
	    HasCM := false;
	    Jmod := J;
	else
	    x := Parent(f).1;
	    F := f+h^2/4;
	    if Degree(F) eq 6 then
		t, x0 := HasRoot(F);
		if t then
		    repeat
			beta := Random(Fq);
		    until beta ne x0 and Evaluate(F, beta) ne 0;
		    F := &+[ Coefficient(F, i)*(x0*x-beta)^i*(x-1)^(6-i) :
		    i in [0..6] ];
		    assert Degree(F) eq 5;
		else
		    HasSchoof := false;
		    HasCM := false;
 		end if;
	    end if;
	    if Degree(F) eq 5 then
		if Coefficient(f, 5) ne 1 then
		    F := &+[ Coefficient(F, i)/Coefficient(F, 5)^(6-i)*x^i :
		    i in [0..6] ];
		end if;
		HasSchoof := true;
		HasCM := true;
	    end if;
	    Jmod := Jacobian(HyperellipticCurve(F));
	end if;
	
	// Get bounds
	lB, uB := GetBounds(Jmod);
	vprintf JacHypCnt : "bounds are: %o, %o.\n", lB, uB;
	
	// Find modular information
	NJ2 := TwoTorsionSubgroupOrder(Jmod);
	if NJ2 eq 1 then
	    N0 := 1;
	    m := 2;
	else
	    N0 := 0;
	    m := NJ2;
	end if;
	vprintf JacHypCnt : "2-torsion gives: %o mod %o.\n", N0, m;

	next_l := 3;
	if p eq next_l then next_l := 5; end if;

	if HasSchoof and UseSchoof then
	    cost_next_l := COST_SCHOOF(next_l, q);
	else
	    cost_next_l := 2^200;
	end if;
	if HasCM and p le CartierManinLimit then
	    cost_CM := COST_CM(p, q);
	else
	    cost_CM := 2^200;
	end if;
	cost_sqrt := COST_SQRT(q, uB-lB, m);

	if HasSchoof and UseHalving then
	    vprintf JacHypCnt : "Initiate 2-Tate module...\n";
	    vtime JacHypCnt : TTM := InitTwoTateModule(Jmod);
	    cost_TTM := COST_TTM(q, TTMNextSmallestDegree(TTM));
	else
	    cost_TTM := 2^200;
	end if;

	// this table is meant to compare our runtime estimations and
	// the real time they took:
	// each entry is of the form < "...", data, est_cost, real_cost >
	CheckEstimate := [];
		
	repeat
	    vprintf JacHypCnt : "expected cost of sqrt   : %o\n", cost_sqrt;
	    vprintf JacHypCnt : "expected cost of CM     : %o\n", cost_CM;
	    vprintf JacHypCnt : "expected cost of schoof : %o\n", cost_next_l;
	    vprintf JacHypCnt : "expected cost of halving: %o\n", cost_TTM;
	    themin, min := Min([cost_next_l, cost_CM, cost_sqrt, cost_TTM]);
	    error if themin ge 2^200, "example too large\n";
            if min eq 4 then
		deg, rk := TTMNextSmallestDegree(TTM);
		if rk lt 2^Valuation(m, 2) and 3*cost_TTM gt cost_sqrt then
		    min := 3;
		end if;
	    end if;
	    case min:
	        when 1:
		    vprintf JacHypCnt : "Use Schoof algorithm with l=%o\n", next_l;
		    tps := Cputime();
		    IndentPush();
		    if next_l eq 3 then
			NJl := JacSchoof(next_l, Jmod : AlwaysRes2:=false);
		    else
			NJl := JacSchoof(next_l, Jmod);
		    end if;
		    IndentPop();
		    vprintf JacHypCnt : "done in %o sec\n", Cputime()-tps;
		    Append(~CheckEstimate, <"Schoof", next_l, cost_next_l, Cputime()-tps>);
		    assert GCD(next_l, m) eq 1;
		    N0 := CRT([N0, NJl], [m, next_l]);
		    m *:= next_l;
		    repeat
			next_l := NextPrime(next_l);
		    until next_l ne p;
		    cost_next_l := COST_SCHOOF(next_l, q);
		    cost_sqrt := COST_SQRT(q, uB-lB, m);
                when 2:
		    vprintf JacHypCnt : "Use Cartier-Manin\n";
		    tps := Cputime();
		    IndentPush();
		    Zp := EulerFactorModChar(Jmod);
		    Jp := Evaluate(Zp, 1) mod p;
		    IndentPop();
		    vprintf JacHypCnt : "done in %o sec\n", Cputime()-tps;
		    Append(~CheckEstimate, <"C-M", q, cost_CM, Cputime()-tps>);
		    N0 := CRT( [N0, Jp], [m, p] );
		    m *:= p;
		    cost_CM := 2^200;
		    cost_sqrt := COST_SQRT(q, uB-lB, m);
	        when 3:
		    vprintf JacHypCnt : "Use sqrt algorithm\n";
		    tps := Cputime();
		    IndentPush();
		    t, NJ := JacobianOrderSquareRoot(Jmod, lB, uB, N0, m 
		                  : BPAThreshold := ShanksLimit);
		    IndentPop();
		    vprintf JacHypCnt : "done in %o sec\n", Cputime()-tps;
		    Append(~CheckEstimate, <"Sqrt", (uB-lB) div m, cost_sqrt, Cputime()-tps>);
		    if not t then
			NJ := Shanks(Jmod, lB, uB);
		    end if;
		    break;
		when 4:
		    vprintf JacHypCnt : "Use halving algorithm\n";
		    tps := Cputime();
		    IndentPush();
		    ClimbTwoTateModuleNext(~TTM);
		    Jr, r := ExtractInfoFromTTM(TTM);
		    IndentPop();
		    vprintf JacHypCnt : "done in %o sec\n", Cputime()-tps;
		    Append(~CheckEstimate, <"Halve", deg, cost_TTM, Cputime()-tps>);
		    if 2^Valuation(m, 2) lt r then
			vprintf JacHypCnt : "Got new information!\n";
			m_coprime_2 := m div 2^Valuation(m, 2);
			N0 := CRT([N0 mod m_coprime_2, Jr], [m_coprime_2, r]);
			m := m_coprime_2*r;
			cost_sqrt := COST_SQRT(q, uB-lB, m);
		    else
			vprintf JacHypCnt : "No new information...\n";
		    end if;
		    cost_TTM := COST_TTM(q, TTMNextSmallestDegree(TTM));
		end case;
	until false;
    end if;
    
    // store results
    J`Order := NJ;

/*  don't do it here: should store something somewhere, and do this computation
    only if necessary.
    
    // store also the result for the curve on Fq and Fq2
    tps := Cputime();
    H := Curve(J);
    if not assigned H`Cardinalities then
	H`Cardinalities := [];
    end if;
    if not IsDefined(H`Cardinalities, 1)
	or not IsDefined(H`Cardinalities, 2) then 
	if IsDefined(H`Cardinalities, 1) then
	    s1 := q+1-H`Cardinalities[1];
	    s2 := NJ-(1+q^2)+s1*(1+q);
	    H`Cardinalities[2] := 2*s2 -s1^2+(q^2+1);
	elif IsDefined(H`Cardinalities, 2) then
	    s2 := (H`Cardinalities[2]+s1^2-(q^2+1)) div 2;
	    s1 := (NJ-(1+q^2)) div (1+q);
	    H`Cardinalities[1] := q+1-s1;
	else
	    lbs1 := Ceiling((q^2+1-NJ-6*q)/(q+1));
	    ubs1 := Floor((q^2+1-NJ+6*q)/(q+1));
	    Jext := BaseExtend(J, 2);
	    P := Random(Jext);
	    FrP := Frobenius(P, Fq);
	    q2P := q^2*P;
	    qFrP := q*FrP;
	    Fr2P := Frobenius(FrP, Fq);
	    Fr3P := Frobenius(Fr2P, Fq);
	    Fr4P := Frobenius(Fr3P, Fq);
	    SetPair := [];
	    for s1 := lbs1 to ubs1 do
		s2 := NJ-(1+q^2)+s1*(1+q);
		if Fr4P - s1*Fr3P + s2*Fr2P -s1*qFrP + q2P eq Jext!0 then
		    Append(~SetPair, [s1, s2]);
		end if;
	    end for;
	    if #SetPair eq 1 then
		s1 := SetPair[1][1];
		s2 := SetPair[1][2];
		H`Cardinalities[1] := q+1-s1;
		H`Cardinalities[2] := 2*s2 -s1^2+(q^2+1);
	    end if;
	end if;
    end if;
    vprintf JacHypCnt : "Computed the cardinalities of the curve in %o sec.\n", Cputime()-tps;
*/

    vprint JacHypCnt : "Stat about our estimates:", CheckEstimate;

    return NJ;
end function;


///////////////////////////////////////////////////////////////////////////
//
// the following functions are important:
//   they return an estimation of the cost of various strategies.
// the crossovers between all of them are difficult to tune.
//
// FIRST ATTEMPT:
// the unit of time for our estimation is the cost of a base-field
// multiplication. We assume that cost(Inv)=10*cost(Mult), so that
// cost (op in Jac) = 40.
//
// remark: this choice seems to be not too bad:
// we do not take into account the log q factor in schoof , since it
// become important for field sizes which are not yet reachable.
//
///////////////////////////////////////////////////////////////////////////

function COST_SCHOOF(l, q)
    if IsEven(q) then return 2^200; end if; // schoof not available 
    COST_FOR_3 := 15*10^5;
    case l :
        when 3 : return COST_FOR_3 div 3; // to take into account modpol
	when 5 : return 35*COST_FOR_3;
	when 7 : return 500*COST_FOR_3;
	when 11 : return 18000*COST_FOR_3;
	when 13 : return 50000*COST_FOR_3;
        else return 2^200;
    end case;
end function;


function COST_SQRT(q, width, m)
    return 40*2*Isqrt(width div m);
end function;


function COST_CM(p, q)
    if p ne q and p le 10^8 then  // absolute bound for Cartier-Manin
	if p le 503 then
	    return 0;
	elif p le 1009 then
	    return Floor(p*Log(2, p)^2);
	elif p le 5003 then
	    return Floor(3*p*Log(2, p)^2);
	else
	    return Floor(4*p*Log(2, p)^2);
	end if;
    else
	return 2^200;
    end if;
end function;


function COST_TTM(q, deg)
    if deg cmpeq Infinity() then
	return 2^200;
    end if;
    COST_FOR_1 := 10*10^5;
    case deg :
        when 1  :  return COST_FOR_1;
	when 2  :  return 10*COST_FOR_1;
	when 3  :  return 15*COST_FOR_1;
	when 4  :  return 30*COST_FOR_1;  // reference
	when 5  :  return 30*COST_FOR_1;
	when 6  :  return 60*COST_FOR_1;
	when 8  :  return 90*COST_FOR_1;
	when 10 :  return 135*COST_FOR_1;
	when 12 :  return 210*COST_FOR_1;
	when 16 :  return 360*COST_FOR_1;
	when 20 :  return 675*COST_FOR_1;
	// The default is not well tuned. Should run a lot of big
	// examples to know what to put here:
        else       return Ceiling( ((deg/20.0)^2.5)*675*COST_FOR_1 ) ; 
    end case;
end function;

