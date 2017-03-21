freeze;

///////////////////////////////////////////////////////////////////////////
//  
//  Arithmetic for genus 2 curves 
//  we assume that we know only the *square* of the ordinate
//
//  P. Gaudry (March 2001)
//
///////////////////////////////////////////////////////////////////////////
//
//  More precisely, we are given a (fixed) scalar FX
//  the divisor are given in the form < u(x), Y*v(x) > where
//  u(x) and v(x) are defined over the base field, and
//  Y is an algebraic element defined by Y^2 = FX
// 
///////////////////////////////////////////////////////////////////////////
/*
CHANGES:
 
 
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
                 fix Curve
  ------------------------------------------------------------------*/
 
 
 


// Assume char != 2 and equation of the form y^2 = f(x) with deg f = 5.

/* test example

Fq := GF(13);
PP := PolynomialRing(Fq); x := PP.1;
f := x^5+RandPoly(PP,4);
J := Jacobian(HyperellipticCurve(f));

P := Random(Curve(J));
xP := P[1];
yP := P[2];

Dinit := Random(J);

D := [ Dinit[1], Dinit[2]/yP ];

DivMultFormal(#J, D, f, Evaluate(f, xP));

*/


forward DivDoubleCantorFormal;
forward DivAddCantorFormal;



///////////////////////////////////////////////////
//
// Doubling
//
//////////////////////////////////////////////////

// Generically takes 30 Mult and 2 Inv
//   (2 more Mult if f(x) is not monic)

// intrinsic DivDoubleFormal(D::SeqEnum, f::RngUPolElt, FX::.) -> SeqEnum

function DivDoubleFormal(D, f, FX)
    if Degree(D[1]) ne 2 then return DivDoubleCantorFormal(D, f, FX); end if;
    
    u1:=Coefficient(D[1],1);
    u2:=Coefficient(D[1],0);
    v1:=Coefficient(D[2],1);
    v2:=Coefficient(D[2],0);
    assert(Degree(f) eq 5);
    x:=Parent(D[1]).1;
    if Coefficient(f,5) eq 1 then
	f5u1:=u1; f5u2:=u2;
    else
	f5u1:=Coefficient(f,5)*u1; f5u2:=Coefficient(f,5)*u2;
    end if;
    
    w := v1^2*FX;
    r := (u2*w) + FX*(-(u1*v1*v2)+v2^2);
    
    if (r eq 0) then      // One point has order 2, double the other one.
	//     printf "not implemented\n";
	return DivDoubleCantorFormal(D, f, FX); 
    end if;
    
    /* k = (f-v^2)/u, exact division. */
    k1 := Coefficient(f,4)-f5u1;
    k2 := Coefficient(f,3)-k1*u1-f5u2;
    k3 := Coefficient(f,2)-w-k1*u2-k2*u1;
    
    /* i = 1/v mod u. */
    
    q := 1/r;
    
    i0 := -q*v1;
    i1 := q*(v2 - u1*v1);
    
    /* j = k mod u. */
    p := k1-f5u1;
    j0 := k2-f5u2-p*u1;
    j1 := k3-p*u2;
    
    /* t = i.j, by Karatsuba. */
    t0 := i0*j0;
    t2 := i1*j1;
    t1 := ((i0+i1)*(j0+j1))-t0-t2;
    
    /* s = t/2 mod u. */
    s0 := (t1-t0*u1)/2;
    s1 := (t2-t0*u2)/2;
    
    if (s0 eq 0) then
	return DivDoubleCantorFormal(D, f, FX);
    end if;
    
    /* l = (k-2.s.v)/u, exact division. */
    l1 := k1-2*s0*v1*FX-f5u1;
    
    /* U := s^2, Karatsuba. */
    U0 := FX*s0^2;
    U2 := FX*s1^2;
    U1 := FX*(s0+s1)^2-U0-U2;
    
    /* U := U-l. */
    U1 := U1-Coefficient(f, 5);
    U2 := U2-l1;
    
    /* W := s.u, Karatsuba. */
    W1 := s0*u1;
    W3 := s1*u2;
    W2 := (s0+s1)*(u1+u2)-W1-W3;
    W0 := s0;
    W1 := W1+s1;
    
    /* W := W+v */
    W2 := W2+v1;
    W3 := W3+v2;
    
    /* Make U monic. */
    I := 1/U0;
    
    U0 := 1;
    U1 := I*U1;
    U2 := I*U2;
    
    /* V = -W mod U, Karatsuba. */
    T0 := U1*W0;
    W1 := W1-T0;
    T2 := U2*W1;
    T1 := (U1+U2)*(W0+W1)-T0-T2;
    V0 := T1-W2;
    V1 := T2-W3;
    
    return [x^2+U1*x+U2, V0*x+V1];
end function;



///////////////////////////////////////////////////////////////////////////
//
// Adding
// 
///////////////////////////////////////////////////////////////////////////

// Generically takes 27 Mult and 2 Inv
//   (1 more Mult if f(x) is not monic)

// intrinsic DivAddFormal(D::SeqEnum, E::SeqEnum, f::RngUPolElt, FX::.) -> SeqEnum
function DivAddFormal(D, E, f, FX)
    if Degree(D[1]) ne 2 or Degree(E[1]) ne 2 then
	return DivAddCantorFormal(D, E, f, FX);
    end if;
    
    Du1 := Coefficient(D[1], 1);
    Du2 := Coefficient(D[1], 0);
    Dv1 := Coefficient(D[2], 1);
    Dv2 := Coefficient(D[2], 0);
    Eu1 := Coefficient(E[1], 1);
    Eu2 := Coefficient(E[1], 0);
    Ev1 := Coefficient(E[2], 1);
    Ev2 := Coefficient(E[2], 0); 

    assert(Degree(f) eq 5);
    f5:=Coefficient(f,5);
    if f5 eq 1 then
	Du1f5:=Du1; 
    else
	Du1f5:=f5*Du1;
    end if;
    x := Parent(D[1]).1;
    
    /* Common subexpressions: */
    de := Du1*Eu1;
    t := Du2 - de + Eu1^2 - Eu2;
    
    /* Resultant: */
    r := Du2*(t-Eu2) + Eu2*(Du1^2-de+Eu2);
    
    if r eq 0 then return DivAddCantorFormal(D, E, f, FX); end if;

    /* Inverse of D.u modulo E.u: */
    // idu := ((Eu1 - Du1)*x + t)/r;
    ir := 1/r;
    
    idu1 := (Eu1-Du1)*ir;
    idu0 := t*ir;
     
    /* Use modular inverse: */
    //s = (E.v-D.v)*idu mod E.u 
    
    // first compute (E.v-D.v)*idu by Karatsuba:
    al := (Ev1-Dv1); be := Ev2-Dv2;
    s2 := al*idu1; s0 := be*idu0;
    s1 := (al+be)*(idu1+idu0) - s0 - s2;
    
    // reduce mod E.u
    s0 -:= Eu2*s2;
    s1 -:= Eu1*s2;
    
    /* Exact division:  k = (f-D.v^2)/D.u    Free! */
    k2 := Coefficient(f,4)-Du1f5;
    //     k1 :=   ; k0 :=

    /* Common subexpression: su = s*D.u      3 P */
    su3 := s1;  // useless
    su2 := s1*Du1;  // need still to add s0
    su0 := s0*Du2;
    su1 := (s0+s1)*(Du1+Du2) - su0 - su2;
    su2 +:= s0;
     
    /* Exact division: nu = (s*(su+2*D.v)-k)/E.u      S + 6 P */
    // let th = s*(su+2*D.v)-k
    th4 := FX*s1^2;
    th3 := FX*s1*(s0+su2)-f5;
    th2 := FX*(s0*su2+s1*(su1+2*Dv1))-k2;

    // divide:
    nu2 := th4;
    nu1 := th3-th4*Eu1;
    nu0 := th2-th4*Eu2-nu1*Eu1;
    
    /* Make nu monic   I + 2 P  */
    if nu2 eq 0 then return DivAddCantorFormal(D, E, f, FX); end if;
    inu2 := 1/nu2;
    nu0 *:= inu2;
    nu1 *:= inu2;
     
    /* Reduce nv:  nv = (su+D.v) mod nu          3 P */
    // use Karatsuba
    cc := nu1*su3;
    be := su2-cc;
    nv0 := be*nu0;
    nv1 := (su3+be)*(nu0+nu1)-cc-nv0;
    // subtract the product to the dividend
    nv0 := su0+Dv2-nv0;
    nv1 := su1+Dv1-nv1;
    // Negate nv
    nv0 := -nv0;
    nv1 := -nv1;

    return [x^2+nu1*x+nu0, nv1*x+nv0];
end function;


//intrinsic DivFrobeniusFormal(D::SeqEnum, f::RngUPolElt, FX::., Fq::FldFin
//    : Check := true) -> SeqEnum
function DivFrobeniusFormal(D, f, FX, Fq : Check := true)
    q := #Fq;
    assert IsOdd(q);
    
    if Check then
	for x in Eltseq(f) do
	    assert x^q eq x;
	end for;
    end if;
    
    a := D[1]; b := D[2];
    
    A := Parent(a) ! [ x^q : x in Eltseq(a) ];
    B := Parent(b) ! [ x^q : x in Eltseq(b) ];

    B *:= FX^((q-1) div 2);
    return [A, B];
end function;


///////////////////////////////////////////////////////////////////////////
//
// Cantor's algorithm, for non-generic operations
//
///////////////////////////////////////////////////////////////////////////

function DivCompose(D1, D2, f, FX)
    a1 := D1[1];
    a2 := D2[1];
    b1 := D1[2];
    b2 := D2[2];
    d0, h1, h2 := XGCD(a1, a2);
    if (Degree(d0) gt 0) then
	s := b1+b2;
	if s eq 0 then 
	    d := d0; l := 1; h3 := 0;
	else
	    d, l, h3 := XGCD(d0, s);
	end if;
	h1 *:= l;
	h2 *:= l;
	a := (a1*a2) div (d^2);
	if (Degree(a) lt 1) then 
	    return [Parent(D1[1])| 1, 0];
	end if;
	b := ( ((h1*a1*b2+h2*a2*b1+h3*(b1*b2*FX+f)/FX) div d) mod a );
    else
	a := a1*a2;
	if (Degree(a) lt 1) then 
	    return [Parent(D1[1])| 1, 0];
	end if;
	b := (h1*a1*b2+h2*a2*b1) mod a;
    end if;
    return [a, b];
end function;

function DivReduce(D, f, FX)
    /* Reduce the divisor D */
    g := Degree(f) div 2;
    a := D[1]; b := D[2];
    while Degree(a) gt g do
	a := (f - FX*b*b) div a;
	b := (-b) mod a;
    end while;
    if Degree(a) lt 1 then
	return [Parent(D[1])| 1, 0];
    end if;
    a := a/LeadingCoefficient(a);
    return [a, b];
end function;

function DivIsZeroFormal(D)
    return D[1] eq 1 and D[2] eq 0;
end function;
    
function DivAddCantorFormal(D1, D2, f, FX)
    if DivIsZeroFormal(D1) then 
	return D2;
    end if;
    if DivIsZeroFormal(D2) then 
	return D1;
    end if;
    return DivReduce(DivCompose(D1, D2, f, FX), f, FX);
end function;
 
// intrinsic DivNegateFormal(D1::SeqEnum, f::RngUPolElt, FX::.) -> SeqEnum
//     { Opposite of a divisor on the jacobian }
function DivNegateFormal(D1, f, FX)
    return [D1[1], -D1[2]];
end function;
 
// intrinsic DivDoubleCantorFormal(D::SeqEnum, f::RngUPolElt, FX::.) -> SeqEnum
//     { Double of a divisor on the jacobian }
function DivDoubleCantorFormal(D, f, FX)
    return DivAddCantorFormal(D, D, f, FX);
end function;

// intrinsic DivMultFormal(k::RngIntElt, D::SeqEnum, f::RngUPolElt, FX::.) -> SeqEnum
//     { Compute k times a divisor on the jacobian }
function DivMultFormal(k, D, f, FX)
    if (k eq 0) then
	return [Parent(D[1])| 1, 0];
    elif (k lt 0) then
	return DivNegateFormal(DivMultFormal(-k, D, f, FX), f, FX);
    end if;
    D1 := D; D2 := [Parent(D[1])| 1, 0];
    m := k;
    while m gt 0 do
	if IsOdd(m) then D2 := DivAddFormal(D1, D2, f, FX); end if;
	m := m div 2;
	D1 := DivDoubleFormal(D1, f, FX);
    end while;
    return D2;
end function;


function DivMultCantorFormal(k, D, f, FX)
    if (k eq 0) then
	return [Parent(D[1])| 1, 0];
    elif (k lt 0) then
	return DivNegateFormal(DivMultCantorFormal(-k, D, f, FX), f, FX);
    end if;
    D1 := D; D2 := [Parent(D[1])| 1, 0];
    m := k;
    while m gt 0 do
	if IsOdd(m) then D2 := DivAddCantorFormal(D1, D2, f, FX); end if;
	m := m div 2;
	D1 := DivDoubleCantorFormal(D1, f, FX);
    end while;
    return D2;
end function;

