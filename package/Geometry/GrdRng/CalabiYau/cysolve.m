freeze;
 
///////////////////////////////////////////////////////////////////////
//		Solving for the invariants of Calabi-Yaus
// GB Sept 2003
///////////////////////////////////////////////////////////////////////

import "cyhilb.m": buckley,contributions,Bcontributions;

/*
The basic numerical invariants of a Calabi--Yau that we use are:
    A3 = A^3,
    Ac = (1/12) * A * c_2(X),
    and for each curve C in the basket
	deg(C) = A * C,
	magic(C) = N_C / tau_C
where N_C is something to do with the normal bundle of C in X and
tau_C is something to do with the possible dissident points along C
as defined next.

Definition.
If C has generically index r transverse sections and dissident
points P_1,...P_k, with P_i of index r*tau_i then the INDEX, tau_C,
of C is LCM(tau_1,...tau_k).
Note that tau_C is not bounded above, but it can take only finitely
many values if one knows the points in the basket.
So we assume that we know the value of tau for each curve.

The unknowns are the values of deg(C) and N_C.
Note that the denominator of deg(C) is bounded by and divides
(so we can assume it is equal to)
	TransverseIndex(C) * Index(C)
and that deg(C) is strictly positive.
So define
	d_C = deg(C) * TransverseIndex(C) * Index(C).

We want to solve for
	d_C > 0 integral
	N_C integral
for each curve C, and so that also A3 > 0.

Buckley's RR formula is of the following kind:
    Hilbert series of R(X,A)
	= 1 + p1*t + p2*t^2 + p3*t^3 + ...
	= formula involving the invariants d_C, N_C.
The point is that these invariants appear linearly in each coefficient of
this formula.  The Hilbert series coefficients p1,p2,...  are certainly
non-negative integers satisfying some elementary conditions (and some
non-elementary ones too, presumably) so can be easily generated as part
of a search.

Given values of p1,... ps, and a basket B of points and RAW curves
(that is, curves without degree or N already assigned), the intrinsic
here attempts to solve for all the invariants and return all small solutions.

Possible extras:
    -- keep hold of deg,N for those curves for which is is known.
*/


//////////////////////////////////////////////////////////////////////////////
//              Compatibility checks
//////////////////////////////////////////////////////////////////////////////

intrinsic IsCompatible(B::GRBskt) -> BoolElt
{}
    Bp := Points(B);
    Bc := Curves(B);
    // Check that the points do not lie on 2-diml (or bigger) singular loci.
    // i.e. in 1/r(a1,...an), no two ai can share the same common factor with r.
    for p in Bp do
	r := Index(p);
	gcds := [ g : a in Polarisation(p) | g ne 1 where g is GCD(r,a) ];
	for i in [1..#gcds] do
	    for j in [i+1..#gcds] do
		require GCD(gcds[i],gcds[j]) eq 1:
		    "The dimension of the singular locus is bigger than 1 at",p;
	    end for;
	end for;
    end for;

    // Now check that for each nonisolated point p there is a curve C on
    // which it can lie as a dissident (or even generic?) point.
    for p in Bp do
	r := Index(p);
	if not IsIsolated(p) then
	    for a in Polarisation(p) do
		h := GCD(r,a);
		if h ne 1 then
		    poss_C := [ C : C in Bc | TransverseIndex(C) eq h
				and Index(C) mod (r div h) eq 0 ];
		    require #poss_C gt 0:
			"No curve contains the singularity",p;
		end if;
	    end for;
	end if;
    end for;

    // Now check that for every curve C which has Index(C) > 1 there are
    // suitable point singularities to account for that.
    Bc1 := [ C : C in Bc | Index(C) gt 1 ];
    for C in Bc1 do
	r := TransverseIndex(C);
	t := Index(C);
	points_on_C := [ p : p in Bp |
		Index(p) mod r eq 0 and r in Polarisation(p) ];
	// THINK: not quite the right condition:  need some product
	// from the seq below to be equal to t.  Given condition is weaker.
	require &*[Integers()| Index(p) div r : p in points_on_C ] mod t eq 0:
			"Not enough points lie on the curve singularity",C;
    end for;
    return true;
end intrinsic;


//////////////////////////////////////////////////////////////////////////////
//              Finding values for N
//////////////////////////////////////////////////////////////////////////////

/*
I assume that values for N giving an integral Hilbert series are
exactly { N0 + k*n : n in ZZ } for some N0,k.
Given that, I find N0 and k by increasing N from 0 upwards until I
have found two values, N0,N1.  Then I return N0, N1-N0.
*/
intrinsic FindN(X::GRCY,i::RngIntElt:MaximumN:=100) -> RngIntElt,RngIntElt
{}
    V := InitialCoefficients(X);
    return FindN(V[1],V[2],Basket(X),i: MaximumN:=MaximumN);
end intrinsic

intrinsic FindN(p1::RngIntElt,p2::RngIntElt,B::GRBskt,i::RngIntElt:
                MaximumN:=100) -> RngIntElt,RngIntElt
{The first nonnegative value of N_Ci (where Ci is the i-th curve of the
basket) together with the distance between successive values of N_Ci
(Return 0,0 if no solutions below MaximumN)}
    K := RationalFunctionField(Rationals());
    t := K.1;
    valuesN := [ Integers() | ];
    Bp := Points(B);
    Bc := Curves(B);
    require i ge 1 and IsDefined(Bc,i): "Argument i must be the index " *
            "of a curve in the sequence of curves of the basket B";
    Ci := Bc[i];
    done := false;
    first_pass := true;
    N := 0;
    repeat
        C := ChangeN(Ci,N);
        Bc1 := Bc;
        Bc1[i] := C;
        B1 := Basket(Bp,Bc1);
        if first_pass and buckley(p1,p2,B1) then
            N0 := N;
            first_pass := false;
        elif buckley(p1,p2,B1) then
            k := N - N0;
            done := true;
        end if;
        if N eq MaximumN and not done then
            if first_pass then
                return 0,0;
            else
                return N0,0;
            end if;
        end if;
        N +:= 1;
    until done;
    return N0,k;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Solving for a single curve
///////////////////////////////////////////////////////////////////////

intrinsic SolveForInvariants(B::GRBskt) -> SeqEnum
{}
    Bp := Points(B);
    Bc := Curves(B);
    result := [ Parent([1,2]) | ];
    require #Bc le 1: "Only works with <= 1 curves in the basket";

    if #Bc eq 1 then
	// Step 1:  find suitable values for t_C
	C := Bc[1];
	curves := [ Parent(C) | ];
	inds := FindIndexes(B);
	for t in inds do
	    C1 := C;
	    C1`t := t;
	    bool := IsCompatible(Basket(Bp,[C1]));
	    if bool then
		Append(~curves, C1);
	    end if;
	end for;
    end if;
print curves;
    return result;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//			
///////////////////////////////////////////////////////////////////////

forward rcontributions;
intrinsic SolveForInvariants(V::SeqEnum,B::GRBskt) -> SeqEnum
{}
// Ouput:  a sequence deg1, magic1, deg2, magic2, ... degr, magicr, A3, Ac
// that results in a Hilbert series with leading coefficients V.

    // first solve for all linear terms in RR using V
    Q := Rationals();
    Bp := Points(B);
    Bc := Curves(B);
    n := 2 + 2 * #Bc;

    // We just want to solve the linear algebra problem of deciding
    // whether V is the coeffs of a hilbert series for suitable choice of
    // invariants: A^3, A*c_2(X) and degC = AC, magic(C) for each curve C.
    // Rather than doing any work, we make a polynomial ring whose variables
    // are these invariants, compute RR using the usual formulas and then
    // equate solutions to the values of V.
    R := PolynomialRing(Q,n);
    A3 := R.(n-1);
    Ac := R.n;
    K := RationalFunctionField(R);
    t := K.1;

    // First make the hilbert series with variable entries for the invariants.
    // This repeats Buckley's formula from cyhilb.m
    Psm := 1 + A3/6*t*(1+4*t+t^2)/(1-t)^4 + Ac * t/(1-t)^2;
    Ppoints := [ K | &+[ coeffs[i]*t^i : i in [1..r-1] ] / (1 - t^r)
            where r is Index(p)
            where coeffs is contributions(p) : p in Points(B) ];
    Pcurves := [ K | ];
    for i in [1..#Bc] do
        C := Bc[i];
        Rdeg := R.(2*i-1);
        RNt := R.(2*i);
        term := &+[ K |
         (- Rdeg * ( 1/(1-t^r)*i*Bi[i] + r*t^r/(1-t^r)^2*Bi[i] )
                     + (1/(1-t^r))*Ri[i] )
                     * t^i : i in [1..r-1] ]
            where r is TransverseIndex(C)
            where Bi is Bcontributions(C)
            where Ri is rcontributions(C,RNt);
        Append(~Pcurves,term);
    end for;
    h := Psm + &+Ppoints + &+Pcurves;

    // get the first #V coefficients of h as a power series (ignoring 1)
    QR := FieldOfFractions(R);
    S<s> := PowerSeriesRing(QR: Precision:=#V+2);
    coeffs := Coefficients(S!h)[2..#V+1];
    ChangeUniverse(~coeffs,R);

    // solve for values of the invariants so that these coeffs equal V
    consts := [ &+[Q|m:m in Terms(f)|TotalDegree(m) eq 0] : f in coeffs ];
    Vnew := [ V[i] - consts[i] : i in [1..#V] ];
    M := Matrix([[MonomialCoefficient(f,R.i):f in coeffs] : i in [1..n] ]);
print M,Vnew;
    VV := VectorSpace(Q,NumberOfRows(M));
    WW := VectorSpace(Q,NumberOfColumns(M));
    phi := hom< VV -> WW | M >;
    require (WW ! Vnew) in Image(phi): "No solution for given coefficients";
    invts := (WW!Vnew) @@ phi;
    require &and [ invts[2*i-1] gt 0 : i in [1..#Bc] ]:
		"Numerical solution requires curves of nonpositive degree:" *
		" kernel dimension is",Dimension(Kernel(phi));

end intrinsic;

/*
To make a calabi--yau with the return data: if Q is one of the sequences
of data in the output sequence, then do

    Bc := Curves(B);
    Bc1 := [ Curve(Q[2*i-1],TransverseType(Bc[i]),Q[2*i]) : i in [1..#Bc] ];
    B1 := Basket(Points(B),Bc1);
    X := CYCreate0(B1,V);
    X`A3 := Q[#Q-1];
    X`Ac := Q[#Q];
*/


///////////////////////////////////////////////////////////////////////
//			Auxiliary functions
///////////////////////////////////////////////////////////////////////

function bar(a,r)
    // the least residue mod r
    return Integers() ! (Integers(r) ! a);
end function;

function recip(a,r)
    // inverse mod r
    return Integers() ! ((Integers(r) ! a)^-1);
end function;

// THINK: i'm recomputing this every time!
function rcontributions(C,RNt)
    r := Index(TransverseType(C));
    a := Polarisation(TransverseType(C))[1];
    b := recip(a,r);
    Bi := [ bar(i*b,r) * (r - bar(i*b,r)) / (2*r) : i in [1..r-1] ] cat [0];
    Ri := [ (r-2*bar(i*b,r))/(6*r) * RNt * Bi[i] : i in [1..r-1] ] cat [0];
    return Ri;
end function;














/*
// THINK: holding old version temporarily.
forward rcontributions;
intrinsic MakeCalabiYau(V::SeqEnum,B::GRBskt) -> GRCY
{The polarised Calabi--Yau X,A with initial Hilbert series coefficients
V = [p1,p2,...pn] and basket B:  only the tranverse type of curves C in
B is used, and both degC=AC and magic=N/tau are deduced from RR}
    // first solve for all linear terms in RR using V
    Q := Rationals();
    Bp := Points(B);
    Bc := Curves(B);
    n := 2 + 2 * #Bc;

    // whether V is the coeffs of a hilbert series for suitable choice of
    // invariants: A^3, A*c_2(X) and degC = AC, magic(C) for each curve C.
    // Rather than doing any work, we make a polynomial ring whose variables
    // are these invariants, compute RR using the usual formulas and then
    // equate solutions to the values of V.
    R := PolynomialRing(Q,n);
    A3 := R.(n-1);
    Ac := R.n;
    K := RationalFunctionField(R);
    t := K.1;

    // First make the hilbert series with variable entries for the invariants.
    // This repeats Buckley's formula from cyhilb.m
    Psm := 1 + A3/6*t*(1+4*t+t^2)/(1-t)^4 + Ac * t/(1-t)^2;
    Ppoints := [ K | &+[ coeffs[i]*t^i : i in [1..r-1] ] / (1 - t^r)
            where r is Index(p)
            where coeffs is Contributions(p) : p in Points(B) ];
    Pcurves := [ K | ];
    for i in [1..#Bc] do
        C := Bc[i];
        Rdeg := R.(2*i-1);
        RNt := R.(2*i);
        term := &+[ K |
         (- Rdeg * ( 1/(1-t^r)*i*Bi[i] + r*t^r/(1-t^r)^2*Bi[i] )
                     + (1/(1-t^r))*Ri[i] )
                     * t^i : i in [1..r-1] ]
            where r is TransverseIndex(C)
            where Bi is BContributions(C)
            where Ri is rcontributions(C,RNt);
        Append(~Pcurves,term);
    end for;
    h := Psm + &+Ppoints + &+Pcurves;

    // get the first #V coefficients of h as a power series (ignoring 1)
    QR := FieldOfFractions(R);
    S<s> := PowerSeriesRing(QR: Precision:=#V+2);
    coeffs := Coefficients(S!h)[2..#V+1];
    ChangeUniverse(~coeffs,R);

    // solve for values of the invariants so that these coeffs equal V
    consts := [ &+[Q|m:m in Terms(f)|TotalDegree(m) eq 0] : f in coeffs ];
    Vnew := [ V[i] - consts[i] : i in [1..#V] ];
    M := Matrix([[MonomialCoefficient(f,R.i):f in coeffs] : i in [1..n] ]);
print M,Vnew;
    VV := VectorSpace(Q,NumberOfRows(M));
    WW := VectorSpace(Q,NumberOfColumns(M));
    phi := hom< VV -> WW | M >;
    require (WW ! Vnew) in Image(phi): "No solution for given coefficients";
    invts := (WW!Vnew) @@ phi;
    require &and [ invts[2*i-1] gt 0 : i in [1..#Bc] ]:
		"Numerical solution requires curves of nonpositive degree:" *
		" kernel dimension is",Dimension(Kernel(phi));

    // finally, make the calabi--yau with this data
    curves := [ Curve(invts[2*i-1],TransverseType(Bc[i]),invts[2*i])
			: i in [1..#Bc] ];
    B := Basket(Bp,curves);
    X := CYCreate0(B,V);
    X`A3 := invts[n-1];
    X`Ac := invts[n];
    return X;
end intrinsic;
*/

