freeze;
////////////////////////////////////////////////////////////////////////////
//    Functions to perform GHS Weil descent on ordinary elliptic          //
//            curves in characteristic 2. mch - 06/06                     //
////////////////////////////////////////////////////////////////////////////

function to_ArtinSchreier(E,c)
    // get E to form y^2+xy = x^3+ax^2+bcx
    E1,mp := SimplifiedModel(E);
    rt := Root(1/jInvariant(E),2);
    E2 := EllipticCurve([BaseRing(E)|1,aInvariants(E1)[2],0,rt,0]);
    mp := mp*Isomorphism(E1,E2,[0,0,rt,1]);
    return E2,mp,rt/c;
end function;

function abc_GHSCheck(a,b,c,k)
    k0 := PrimeField(k);
    if (Trace(a,k0) ne 0) and (Trace(c,k) eq 0) and (Trace(b,k) eq 0) then
	return false;
    else
	return true;
    end if;
end function;

intrinsic WeilDescentGenus(E::CrvEll, k::FldFin, c::FldFinElt) -> RngIntElt
{ E/K an ordinary elliptic curve over a characteristic 2 finite field.
  k a subfield of K. Returns the genus of the GHS Weil descent curve
  associated to E and the parameter c of K}
    K := BaseRing(E);
    require Type(K) eq FldFin :
		"Elliptic curve must be defined over a finite field";
    require Parent(c) eq K:
	"The third argument must belong to the constant field of the first";
    require c ne 0:
	"The third argument must be non-zero";
    k0 := PrimeField(k);
    require (#k0 eq 2) and (PrimeField(K) eq k0):
		"The base field must have characteristic 2";
    require IsDivisibleBy( Degree(K, k0), Degree(k, k0) ):
       "Second argument k must be a subfield of the constant field of the first";
    require jInvariant(E) ne 0:
		"Elliptic curve must have non-zero j-invariant";
    Embed(k,K);

    E1,mp,b := to_ArtinSchreier(E,c);
    a := aInvariants(E1)[2];
    require abc_GHSCheck(a,b,c,k):
	"GHS descent trace conditions are not satisfied by the data";
    Eas := ArtinSchreierExtension(c,a,b);
    return WeilDescentGenus(Eas,k);
end intrinsic;

intrinsic WeilDescentDegree(E::CrvEll, k::FldFin, c::FldFinElt) -> RngIntElt
{ E/K an ordinary elliptic curve over a characteristic 2 finite field.
  k a subfield of K. Returns the y-degree of the GHS Weil descent curve
  associated to E and the parameter c of K}
    K := BaseRing(E);
    require Type(K) eq FldFin :
		"Elliptic curve must be defined over a finite field";
    require Parent(c) eq K:
	"The third argument must belong to the constant field of the first";
    require c ne 0:
	"The third argument must be non-zero";
    k0 := PrimeField(k);
    require (#k0 eq 2) and (PrimeField(K) eq k0):
		"The base field must have characteristic 2";
    require IsDivisibleBy( Degree(K, k0), Degree(k, k0) ):
       "Second argument k must be a subfield of the constant field of the first";
    require jInvariant(E) ne 0:
		"Elliptic curve must have non-zero j-invariant";
    Embed(k,K);

    E1,mp,b := to_ArtinSchreier(E,c);
    a := aInvariants(E1)[2];
    require abc_GHSCheck(a,b,c,k):
	"GHS descent trace conditions are not satisfied by the data";
    Eas := ArtinSchreierExtension(c,a,b);
    return WeilDescentDegree(Eas,k);
end intrinsic;

function GHSDivisorMapHyp(a,b,c,J,JK,F,n)
/*
   here, we produce the degree 0 divisor class on J = Jac(C),
   C hyperelliptic char 2, which is the sum of K/k conjugates
   of the point on JK=Jac(C_K) whose "finite" part is given
   by the divisor which is the common zeros of a,b+cy where
   a,b,c in K[x] and K[x][y]/(weierstrass eqn of C) is the
   coord ring of C. F gives the frobenius map on K(x) [fixing x]
   and n = [K:k]
*/
    Kx<x> := Parent(a);
    C := Curve(J);
    f,h := HyperellipticPolynomials(C);

    // first get ideal [a,b+cy] in form t*[r,y+s] - can
    // ignore t up to rational equivalence.
    t,seq := XGCD([a,b-c*(Kx!h),c]);
    if Degree(t) gt 0 then
	a := a div t; b := b div t; c := c div t;
    end if;
    s := seq[3]*b+seq[2]*c*(Kx!f);
    r := GCD([a,Kx!f+s*Kx!h-s^2,b-s*c]);
    s := s mod r;
    assert IsEven(Degree(r));
     // may need to do some reduction
    g := Genus(C);
    while Degree(s) gt (g+1) do
	r := (s^2-(Kx!h)*s-Kx!f) div r;
	r := r/(LeadingCoefficient(r));
	s := ((Kx!h)-s) mod r;
    end while;
    pt := elt<JK|r,-s>;

    // now do trace by binary powering
    bits := Reverse(Prune(Intseq(n,2)));
    Q := pt; m := 1;
    for bit in bits do
	r := Q[1]; s := Q[2]; d := Q[3];
	for i in [1..m] do
	    r := F(r); s := F(s);
	end for;
	Q +:= elt<JK|r,s,d>;
	m *:= 2;
	if bit eq 1 then
	    Q := elt<JK|F(Q[1]),F(Q[2]),Q[3]> + pt;
	    m +:= 1;
	end if;
    end for;
    pt := Q;
/*
    r := pt[1]; s := pt[2]; d := pt[3];	
    for i in [1..n-1] do
	r := F(r); s := F(s);
	pt +:= elt<JK|r,s,d>;
    end for;
*/

    // transfer to J
    k := BaseRing(C);
    kx := PolynomialRing(k);
    r := pt[1]; s := pt[2]; d := pt[3];
    rc := Coefficients(r);
    assert &and[e in k: e in rc];
    r := kx!rc;
    sc := Coefficients(s);
    assert &and[e in k: e in sc];
    s := kx!sc;

    return elt<J|r,s,d>;

end function;

function MakeHyperEllipticCurve(C,g)
/*
    When a GHS descent AlFF C is of degree 2 and of genus g >= 2
    (=> char = 2), it is hyperelliptic and this function finds
    and returns a standard Weierstrass model, Chyp, for C.
    The two will be isomorphic over the base field k(x) of C.
    If C.1 is the generator of C over k(x), then the y variable
    of Cyp will correspond to Y=a+b*C.1 for some a,b in k[x].
    Y (which determines the isomorphism) is also returned.
*/
    assert (Degree(C) eq 2) and (g ge 2);
    O := MaximalOrderFinite(C);
    B := Basis(O);
    assert (#B eq 2) and (C!(B[1]) eq 1);
    Y := C!(B[2]);
    f,h := Explode(Coefficients(MinimalPolynomial(Y)));
    Kz := BaseRing(C);
    R := RingOfIntegers(Kz);
    f := R!f; h := R!h;
    assert Degree(h) le g+1;
    d := Degree(f);
    while (d gt 2*Degree(h)) and IsEven(d) do
	c := LeadingCoefficient(f);
	c1 := Sqrt(c);
	Y +:= c1*Kz!((R.1)^(d div 2));
	f +:= c*(R.1)^d+h*c1*(R.1)^(d div 2);
	d := Degree(f);
    end while;
    assert d le 2*(g+1);
    assert (Degree(h) eq g+1) or (d eq 2*g+1);
    Chyp := HyperellipticCurve(f,h);
    return Chyp,Y;
end function;

function MakeDivisorMapForHyp(E,E_mp,b,data)
/*
   When p=2 and the Artin-Schreier AlFF E1 has GHS
   descent to a degree 2 curve, this function finds
   a hyperelliptic model Chyp for the descent curve /k
   and rather than computing maps on divisors it gives
   the induced map on divisor classes as a map from the
   rational points of an elliptic curve E/K with function
   field isomorphic to E1 to the jacobian of Chyp.
   
   data is the GHS data record for E1 and k.

   E_mp should be an isomorphism from E to an elliptic
   curve with equation y^2+xy=x^3+ax^2+bcx, where the
   Artin-Schreier equation of E1 is Y^2+Y=c/X+a+b*X.

   If Chyp/k has odd genus and no rational points at
   infinity then no group law currently exists in
   Magma, and false is returned. Otherwise, true,
   the divisor map and Jac(C) are returned. 
*/
    K := data`K;
    Kzt := data`Kztildef;
    //Cztp := data`Cztildeprim;
    Cztpr := data`Cztildeprimrat;
    kzt := BaseRing(Cztpr);
    mp := data`CztildetoCztildeprim;
    X := Evaluate(data`mztildex,Kzt.1);
    Y := data`yred+data`ASRed;
    xflip := data`xflip;
    if xflip then 
	X := (1/b)*X;
    else
	X := b*X;
    end if;

    Chyp,Y1 := MakeHyperEllipticCurve(Cztpr,data`g);
    N := NumberOfPointsAtInfinity(Chyp);
    if IsOdd(data`g) and (N eq 0) then return false,_,_; end if;
    // in fact 1st cond is superfluous(?) - N eq 0 or 2 => g odd
    u,v := Explode(Eltseq(Y1));

    X := mp(X); Y := mp(Y);
    Y := es[1]+es[2]*(Parent(Y).1-Kzt!u)/(Kzt!v) where es is Eltseq(Y);
    PK := PolynomialRing(K);
    X := PK!(Eltseq(X)[1]);
    Y1,Y2 := Explode(ChangeUniverse(Eltseq(X*Y),PK));
 
    J := Jacobian(Chyp);
    JK := Jacobian(BaseChange(Chyp,K));

    FrobK := map<K->PK|x :-> PK!((data`FrobK)(x))>;
    F := hom<PK->PK|FrobK,[PK.1]>;
    n := data`n;

    //need to handle the non-trival point of order 2 specially.
    // -the image in JK actually lies in J and is:
    //  N=1 : J![h,0,g] (g = 2^r)
    //  N=2 :  (p,q points at inf)  ((g+1)/2)*(p-q) (g = 2^r-1)
    // [in the latter case this is ord 2 so order of p,q irrelevant]
    P2 := hm(G.1) where G,hm := TwoTorsionSubgroup(E);
    if IsEven(n) then // image killed in the trace in either case
	P2im := J!0;
    elif N eq 1 then
	assert IsEven(data`g);
	_,h := HyperellipticPolynomials(Chyp);
	assert Degree(h) eq data`g;
	P2im := elt<J|h,Parent(h)!0>;
    else
	assert (N eq 2) and IsOdd(data`g);
	pts_inf := Setseq(PointsAtInfinity(Chyp));
	P2im := ((1+data`g) div 2)*(J![[pts_inf[1]],[pts_inf[2]]]);
    end if; 
/*
     // find a point on E != 0 or P2
    pt := P2;
    while (pt eq P2) or (pt eq E!0) do
	pt := Random(E);
    end while;
     // image P2 = image(pt+P2)-image(pt);
    P2im := J!0;
    for i in [0..1] do
	x1,y1 := Explode(Eltseq(E_mp(pt+(i*P2))));
	if xflip then
	    jpt := GHSDivisorMapHyp(X-(1/x1),Y1-y1*X^2,Y2,J,JK,F,n);
	else
	    jpt := GHSDivisorMapHyp(X-x1,Y1-y1,Y2,J,JK,F,n);
	end if;
	P2im +:= (-1)^(i+1) *jpt;
    end for;
*/

    if xflip then
      div_map := function(x)
	if (not(Type(x) eq PtEll)) or (Curve(x) ne E) or
		(Ring(Parent(x)) ne BaseRing(E)) then
	    Traceback();
	    error "Argument must be a rational point on the curve";
	end if;
	if (x eq E!0) then
	    return J!0;
	elif (x eq P2) then
	    return P2im;
	else
	    x1,y1 := Explode(Eltseq(E_mp(x+P2)));
	    return
	      GHSDivisorMapHyp(X-(1/x1),Y1-y1*X^2,Y2,J,JK,F,n);
	end if;
      end function;
    else
      div_map := function(x)
	if (not(Type(x) eq PtEll)) or (Curve(x) ne E) or
		(Ring(Parent(x)) ne BaseRing(E)) then
	    Traceback();
	    error "Argument must be a rational point on the curve";
	end if;
	if (x eq E!0) then
	    return J!0;
	elif (x eq P2) then
	    return P2im;
	else
	    x1,y1 := Explode(Eltseq(E_mp(x)));
	    return
	      GHSDivisorMapHyp(X-x1,Y1-y1,Y2,J,JK,F,n);
	end if;
      end function;
    end if;

    return true,div_map,J;
end function;

function EtoEasDivisorMap(P,b,c,Eas)
    Ofin := MaximalOrderFinite(Eas);
    Oinf := MaximalOrderInfinite(Eas);
    X := Eas!(BaseField(Eas).1);
    if P eq Curve(P)!0 then
	Ifin := ideal<Ofin|1>;
	Iinf := ideal<Oinf|(Eas.1)/X>;
    else
	x,y := Explode(Eltseq(P));
	Ifin := ideal<Ofin|[b*X-x,b*X*Eas.1-y]>;
	Iinf := ideal<Oinf|1>;
    end if;
    return Divisor(Ifin,Iinf);
end function;

function FtoFaDivisor(D,F,Fa,phi)
    Ifin,Iinf := Ideals(D);
    Bfin := [phi(F!b) : b in Generators(Ifin)];
    Binf := [phi(F!b) : b in Generators(Iinf)];
    Ifin := ideal<MaximalOrderFinite(Fa)|Bfin>;
    Iinf := ideal<MaximalOrderInfinite(Fa)|Binf>;
    return Divisor(Ifin,Iinf);
end function;

intrinsic WeilDescent(E::CrvEll, k::FldFin, c::FldFinElt :
	HyperellipticImage := true) -> CrvPln, Map
{E/K an ordinary elliptic curve over a characteristic 2 finite field.
 k a subfield of K. Function calculates a plane curve model C for
 the GHS Weil Descent associated to E and the parameter c in K.
 Also returned is the divisor map taking points of E (considered
 as degree 1 divisors) to the corresponding divisor on C - unless
 HyperellipticImage is true (the default),the degree of C is
 2 and the Jacobian of C, J, has a group law. In this case,C
 is returned as a hyperelliptic curve and the map is from points
 of E (considered as degree 0 divisor CLASSES) to J, the image
 again representing the image divisor CLASS.}
    K := BaseRing(E);
    require Type(K) eq FldFin :
		"Elliptic curve must be defined over a finite field";
    require Parent(c) eq K:
	"The third argument must belong to the constant field of the first";
    require c ne 0:
	"The third argument must be non-zero";
    k0 := PrimeField(k);
    require (#k0 eq 2) and (PrimeField(K) eq k0):
		"The base field must have characteristic 2";
    require IsDivisibleBy( Degree(K, k0), Degree(k, k0) ):
       "Second argument k must be a subfield of the constant field of the first";
    require jInvariant(E) ne 0:
		"Elliptic curve must have non-zero j-invariant";
    Embed(k,K);

    // handle trivial K=k case
    if Degree(K, k0) eq Degree(k, k0) then
	return E,IdentityMap(E);
    end if;

    E1,E_mp,b := to_ArtinSchreier(E,c);
    a := aInvariants(E1)[2];
    require abc_GHSCheck(a,b,c,k):
	"GHS descent trace conditions are not satisfied by the data";

    Eas := ArtinSchreierExtension(c,a,b);
    F,div_map := WeilDescent(Eas,k);

    data := Eas`datalist[1];
    if HyperellipticImage and (data`d eq 2) then
 	ok,hyp_map,J := MakeDivisorMapForHyp(E,E_mp,b,data);
	if ok then
	    return Curve(J),hyp_map;
	end if;
    end if;

    // get a plane curve <-> F and translate div_map
    //  won't be sophisticated! Use the same base variable
    //  x,and minimal multiple of y*poly in x that is
    //  integral over x..
    Ofin := MaximalOrderFinite(F);
    kx := BaseRing(F);
    R := RingOfIntegers(kx);
    den := R!Denominator(F.1,Ofin);
    eqn := MinimalPolynomial((kx!den)*(F.1));
    d := data`d;
    assert d eq Degree(eqn);
    fs := ChangeUniverse(Coefficients(eqn),R);
    Ry<x,y> := PolynomialRing(k,2);
    hm := hom<R->Ry|[Ry.1]>;
    Ca := Curve(Spec(Ry),&+[hm(fs[i+1])*y^i: i in [0..d]]);
    Ka := FunctionField(Ca);
    Fa,ff_map := AlgorithmicFunctionField(Ka);

    L := [ff_map(Ka!(y/hm(den))),ff_map(Ka!x)];
    boo,phi := HasMorphismFromImages(FunctionFieldCategory())
		  (F,Fa,L);
    C := ProjectiveClosure(Ca);
    d_map := function(x)
	if (not(Type(x) eq PtEll)) or (Curve(x) ne E) or
		(Ring(Parent(x)) ne BaseRing(E)) then
	    Traceback();
	    error "Argument must be a rational point on the curve";
	end if;
        D := div_map(EtoEasDivisorMap(E_mp(x),b,c,Eas));
	return CurveDivisor(C,FtoFaDivisor(D,F,Fa,phi));
    end function;
    return C,d_map;
end intrinsic;
