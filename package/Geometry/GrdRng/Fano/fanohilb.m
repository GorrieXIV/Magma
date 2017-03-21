freeze;
 
/////////////////////////////////////////////////////////////////////
//		Hilbert series of Fano 3-folds
// Formula due to Kaori Suzuki
//		math.AG/0210309,  page 2.
// GB May 2002, Dec 2002, Sept 2003
/////////////////////////////////////////////////////////////////////


/////////////////////////////////////////////////////////////////////
//			Hilbert series
/////////////////////////////////////////////////////////////////////

forward contribution,contributions,fano_Ac,fano_degree,fano_degree_g;

// The Hilbert series of a Fano 3-fold of Fano index f >= 1,
// genus g and basket B.
//    require f ge 1: "The Fano index f must be at least 1";
function fano_hilbert_series_g(g,f,B)
    K := RationalFunctionField(Rationals());
    t := K.1;
    deg := fano_degree_g(g,f,B);
    Ac := fano_Ac(f,B);
    // Formula for RR by Kaori Suzuki
    I := 1/(1-t);
    II := (1/12 * deg / (1-t)^4 ) *
        ((f^2 + 3*f + 2)*t + (-2*f^2 + 8)*t^2 + (f^2 - 3*f + 2)*t^3);
    III := Ac * t/(1-t)^2;
    Psm := I + II + III;
    Psings := [ K | &+[ coeffs[i]*t^i : i in [1..r-1] ] / (1 - t^r)
		where r is Index(p)
		where coeffs is contributions(f,p) : p in Points(B) ];
    return Psm + &+Psings,deg,Ac;
end function;

// The Hilbert series of a Fano 3-fold of Fano index f >= 3 and basket B.
//    require f ge 3: "Include arguments (g,f,B) when f <= 2";
function fano_hilbert_series(f,B)
    K := RationalFunctionField(Rationals());
    t := K.1;
    deg := fano_degree(f,B);
    Ac := fano_Ac(f,B);
    // Formula for RR by Kaori Suzuki
    I := 1/(1-t);
    II := (1/12 * deg / (1-t)^4 ) *
        ((f^2 + 3*f + 2)*t + (-2*f^2 + 8)*t^2 + (f^2 - 3*f + 2)*t^3);
    III := Ac * t/(1-t)^2;
    Psm := I + II + III;
    Psings := [ K | &+[ coeffs[i]*t^i : i in [1..r-1] ] / (1 - t^r)
		where r is Index(p)
		where coeffs is contributions(f,p) : p in Points(B) ];
    return Psm + &+Psings,deg,Ac;
end function;

// RR formula for Fano 3-folds of Fano index f >= 3 and basket B.
//    require f ge 3: "Include arguments (g,f,B) when f <= 2";
function fano_rr(f,B,n)
    // Formula for RR by Kaori Suzuki
    I := 1;
    II := 1/12 * fano_degree(f,B) * n * (n + f) * (2*n + f);
    IIa := (2*n/f);
    III := -(2*n/f) * fano_Ac(f,B) *
	&+[ Rationals() | (r^2 - 1) / (12*r) where r is Index(p)
			: p in B ];
    IV := &+[ contribution(f,p,n) : p in Points(B) ];
    return Integers() ! (I + II + IIa + III + IV);
end function;


/////////////////////////////////////////////////////////////////////
//		Calculate the numbers appearing in RR
/////////////////////////////////////////////////////////////////////

// The number (1/12) * A * c_2(X)
function fano_Ac(f,B)
    sumpart := &+[ Rationals() | (r^2-1)/(12*r) where r is Index(p)
			 : p in Points(B) ];
    return (2-sumpart)/f;
end function;

function fano_degree(f,B)
    // this one assumes f >= 3
    factor := 12/((f-1)*(f-2));
    c2_part := fano_Ac(f,B);
    periodic := &+[ Rationals() | contribution(f,p,-1) : p in Points(B) ];
    return factor * (1 - c2_part + periodic);
end function;

function fano_degree_g(g,f,B)
    // this one assumes f >= 1
    if f in {1,2} then
        periodic := &+[ Rationals() | contribution(f,p,1) : p in Points(B) ];
        rest_of_A3 := 1 + fano_Ac(f,B) + periodic;
        return (g - rest_of_A3) * 12/((f+1)*(f+2));
    else
	return fano_degree(f,B);
    end if;
end function;


/////////////////////////////////////////////////////////////////////
//			Auxiliary functions
/////////////////////////////////////////////////////////////////////

// The first r contributions to RR for nA (n modulo r) coming from the
// singularity p = 1/r(a,b,c) and n = 1,...,r-1.

function contributions(f,p)
    r := Index(p);
    return [ contribution(f,p,n) : n in [1..r-1] ];
end function;

// The corrections to RR for nA (n modulo r) coming from the
// singularity p = 1/r(a,b,c).
forward i_is, inv, bar;
function contribution(f,p,n)
    r := Index(p);
    if (n mod r) eq 0 then
	return (Rationals() ! 0);
    end if;
    P := TerminalPolarisation(p);		// P is [f,a,b] where b = r - a.
    a := inv(P[1],r) * P[2] mod r;	// if p=1/r(f,a0,b0), I want a = a0/f
    i := i_is(f,r,n);
    b := inv(a,r);
    first := -i*(r^2-1)/(12*r);
    if i in {0,1} then
        extra := 0;
    else
        extra := &+[ bar(b*j,r)*(r-bar(b*j,r))/(2*r) : j in [0..i-1] ];
    end if;
    return first + extra;
end function;

function i_is(f,r,n)
    h,u,v := XGCD(f,r);
    return (-n*u) mod r;
end function;

bar := func< m,r | m mod r >;

inv := func< a,r | i_is(a,r,1) >;

