freeze;
 
//////////////////////////////////////////////////////////////////////////////
//		Hilbert series computations for CY
// cyhilb.m
// 10 May 2002 GB
//////////////////////////////////////////////////////////////////////////////

/*
Hilbert series is
	P(t) = 1 + p1*t + p2*t^2 + ...
	     = t*(t^2+4*t+1)/(1-t)^4 * (D^3/6) + t/(1-t)^2 * (Dc2/12)
		- point contributions
		- curve contributions
curves:	C = [r,a],d,N,tau
		m-th contribution = (m * Bi[i] * d)  +  Ri[i]
	where i is m mod r and Bi,Ri are computed with C.

In particular
	p1 = (D^3/6) + (Dc2/12)
		- points[1]
		- Bi[1] * d + Ri[1]
	p2 = 8*(D^3/6) + 2*(Dc2/12)
		- points[2]
		- 2 * Bi[2] * d + Ri[2]
so
	D^3 = p2 - 2*p1
		- 2*points[1] + points[2]
		- 2*curves[1] + curves[2]
	Dc2/12 = 8*p1 - p2
		+ 8 * points[1] - points[2]
		+ 8 * curves[1] - curves[2].

Better would be to determine N,tau from sufficiently many of the pi.
*/


//////////////////////////////////////////////////////////////////////////////
//		RR contributions from basket singularities
// These formulas are by Anita Buckley.
// They are skew-palindromes so code could be shortened.
//////////////////////////////////////////////////////////////////////////////

forward contributions, Rcontributions, Bcontributions;
function buckley(p1,p2,B)
    K := RationalFunctionField(Rationals());
    t := K.1;
    A3,Ac := P1P2toA3Ac2over12(p1,p2,B);

    Psm := 1 + A3/6*t*(1+4*t+t^2)/(1-t)^4 + Ac * t/(1-t)^2;

    Ppoints := [ K | &+[ coeffs[i]*t^i : i in [1..r-1] ] / (1 - t^r)
	    where r is Index(p)
	    where coeffs is contributions(p) : p in Points(B) ];

    Pcurves := [ K |
	&+[ K |
	 (- Degree(C) * ( 1/(1-t^r)*i*Bi[i] + r*t^r/(1-t^r)^2*Bi[i] )
		     + (1/(1-t^r))*Ri[i] )
		     * t^i : i in [1..r-1] ]
	    where r is TransverseIndex(C)
	    where Bi is Bcontributions(C)
	    where Ri is Rcontributions(C) : C in Curves(B) ];

    h := Psm + &+Ppoints + &+Pcurves;

    S := PowerSeriesRing(Rationals(),LCM([Index(p):p in Points(B)]));
    return &and[IsCoercible(Integers(),c) : c in Coefficients(S!h)],h;
end function;

forward recip, bar;
// The s contributions to RR for multiples A,2A,...,sA of the polarising divisor
// A coming from the point singularity p
function contributions(p)
    s := Index(p);
    a := Polarisation(p);
    n := Eigenspace(p);
    K := FiniteField(1009);
    ep := RootOfUnity(s,K);
    C0 := [ Parent(ep) | ];
    for m in [1..s-1] do
	C0[m] := 1/s *
	&+[ Parent(ep) |
	    ((ep^i)^(-n*m)-1) / ( &*[ (ep^i)^a[k] - 1 : k in [1..3] ] )
	    : i in [1..s-1]
	    | &and[ (ep^i)^a[k] - 1 ne 0 : k in [1..3]] ];
    end for;

    // Completion:
    // the answer is in the finite field, but we want it in Q=Rationals();
    // but we know that the entries of C0 are always of the from
    //    h/s^k for some integers h,k with k>=0.    THINK: is this true?
    // so we just search through these systematically.
    C1 := [Rationals()|];
    for i in [1..s-1] do
	a := C0[i];         // this is in K;  which rational is it?
	if a eq K!0 then
	    C1[i] := 0;
	    continue i;
	end if;
	depth := 0;
	found := false;
	repeat
	    depth +:= 1;
	    for j in [1..depth] do
		// we compare a with j/s^(depth-j)
		if a eq K ! (j/s^(depth-j)) then
		    C1[i] := j/s^(depth-j);
		    found := true;
		    break j;
		end if;
		if -a eq K ! (j/s^(depth-j)) then
		    C1[i] := -j/s^(depth-j);
		    found := true;
		    break j;
		end if;
	    end for;
	until found;
    end for;
    return C1 cat [Rationals()|0];
end function;

function Rcontributions(C)
    r := Index(TransverseType(C));
    a := Polarisation(TransverseType(C))[1];
    b := recip(a,r);
    Bi := [ bar(i*b,r) * (r - bar(i*b,r)) / (2*r) : i in [1..r-1] ] cat [0];
    Nt := MagicNumber(C);
    Ri := [ (r-2*bar(i*b,r))/(6*r) * Nt * Bi[i] : i in [1..r-1] ] cat [0];
    return Ri,Bi;
end function;

function Bcontributions(C)
    r := Index(TransverseType(C));
    a := Polarisation(TransverseType(C))[1];
    b := recip(a,r);
    Bi := [ bar(i*b,r) * (r - bar(i*b,r)) / (2*r) : i in [1..r-1] ] cat [0];
    return Bi;
end function;

function bar(a,r)
    // the least residue mod r
    return Integers() ! (Integers(r) ! a);
end function;

function recip(a,r)
    // inverse mod r
    return Integers() ! ((Integers(r) ! a)^-1);
end function;


//////////////////////////////////////////////////////////////////////////////
//		Translation between invariants
//////////////////////////////////////////////////////////////////////////////

intrinsic P1P2toA3Ac2over12(P1::RngIntElt,P2::RngIntElt,B::GRBskt)
                        -> FldRatElt,FldRatElt
{The values A^3 and A*c_2/12 for a polarised Calabi-Yau X,A having P1,P2
as given and baskets of point and curve singularities B}
	// compute point corrections to P1, P2
    pBconts := [ contributions(p) : p in Points(B) ];
    pcorr1 := &+[ Rationals() | C[1] : C in pBconts ];
    pcorr2 := &+[ Rationals() | C[2] : C in pBconts ];
	// compute curve corrections to P1, P2
    ccorr1 := &+[Rationals()|
	Bcontributions(C)[1]*Degree(C) - Rcontributions(C)[1]
				: C in Curves(B) ];
    ccorr2 := &+[Rationals()|
	2*Bcontributions(C)[2]*Degree(C) - Rcontributions(C)[2]
				: C in Curves(B) | TransverseIndex(C) ne 2 ];
	// rearrange P(t)
    corr1 := pcorr1 - ccorr1;
    corr2 := pcorr2 - ccorr2;
    A3 := P2 - 2*P1 + 2*corr1 - corr2;
    Ac := 1/6 * (8*P1 - P2 - 8*corr1 + corr2);
    return A3,Ac;
end intrinsic;

