freeze;
 
////////////////////////////////////////////////////////////////////
///       Heights on elliptic curves over number fields           //
//                      Martine Girard                            //
//                  girard@maths.usyd.edu.au                      //
//                 with contributions by                          //
//                      David R. Kohel                            //
//                  kohel@maths.usyd.edu.au                       //
//                                                                //
//      Uses the paper of Silverman                               //
//      "Computing heights on elliptic curves"                    //
//      Math Comp 51 (1988) p 339-358                             //
//      The height we define is twice Silverman's                 //
////////////////////////////////////////////////////////////////////


declare attributes CrvEll:
    BadPlaces;

declare attributes SetPtEll:
    circular_ref,
    BadPlaces,
    Translations,
    Order; // MW 12 Apr 2011

declare verbose Height, 3;


PREC:=Precision;

procedure retain_attributes(PS)
// Ensures that the given pointset (of an elliptic curve) retains any
// attributes set on it, by ensuring that it cannot be deleted.  This
// is done by storing a reference to itself on itself.  Yes, this is bad.

    if not assigned PS`circular_ref then
	E := Scheme(PS);
	if Parent(E!0) ne PS then	// base pointsets do not need this
	    PS`circular_ref := PS;
	end if;
    end if;
end procedure;

function compute_translation(binvs)
    C := ComplexField();
    P := PolynomialRing(C);
    x := P.1;
    b2,b4,b6,b8 := Explode(binvs);
    f := 4*x^3 + b2*x^2 + 2*b4*x + b6;
    m,e := MantissaExponent(Min({ Real(r[1]) : r in Roots(f) }));
    r := e le 0 select -100 else (Floor(m - 1/2)*10^(e - Sign(m)));
    return r;
end function;

procedure assure_translations(EK, binv_conj)
    if not assigned EK`Translations then
	S := [];
/*
	r1,r2 := Signature(Ring(EK));
	for i in [1..r1] cat [r1+1..r1+2*r2 by 2] do
	    r0 := compute_translation([b[i] : b in binv_conj]);
	    Append(~S, r0);
	end for;
*/
for i in [1..#binv_conj[1]] do
	    r0 := compute_translation([b[i] : b in binv_conj]);
	    Append(~S, r0);
	end for;

	EK`Translations := S;
	retain_attributes(EK);
    end if;
end procedure;

function IsExtension(L, K)
    bool,S := ExistsCoveringStructure(K, L);
    if not bool then return false; end if;
    return S cmpeq L;
end function;

function bad_places_curve(E)
    K := BaseRing(E);
    if not assigned E`BadPlaces then
	E`BadPlaces := Support(Divisor(Discriminant(E)));
    end if;
    return E`BadPlaces;
end function;

function bad_places_curve_ext(E, L)
    K := BaseRing(E);
    if L cmpeq K then return BadPlaces(E); end if;

    EL := E(L);
    if not assigned EL`BadPlaces then
        EL`BadPlaces := Support(Divisor(L!Discriminant(E)));
	retain_attributes(EL);
    end if;
    return EL`BadPlaces;
end function;

intrinsic BadPlaces(E::CrvEll[FldRat]) -> SeqEnum
{The places of bad reduction for (the given model of) the elliptic curve E}
 L:=ext<Rationals()|PolynomialRing(Rationals()).1 : DoLinearExtension, Global>;
 E`BadPlaces:=bad_places_curve(ChangeRing(E,L)); return E`BadPlaces;
end intrinsic;

intrinsic BadPlaces(E::CrvEll[FldNum]) -> SeqEnum
{"}
    return bad_places_curve(E);
end intrinsic;

intrinsic BadPlaces(E::CrvEll[FldNum], L::FldNum) -> SeqEnum
{The places of bad reduction for (the given model of) the elliptic curve E}
    require IsExtension(L, BaseRing(E)) :
	"Field given must be an extension of the base field of the curve";
    return bad_places_curve_ext(E, L);
end intrinsic;

intrinsic BadPlaces(E::CrvEll[FldRat], L::FldNum) -> SeqEnum
{"} 
    return bad_places_curve_ext(E, L);
end intrinsic;

intrinsic NaiveHeight(x::FldElt : Precision:=30) -> FldReElt
{The logarithmic height of an element in a number field or a function field}

    K := (Parent(x));
    pr:=Precision; 
    R := RealField(pr);
   
    if ISA(Type(K), FldAlg) and IsAbsoluteField(K) then
      old_prec := GetKantPrecision();
      SetKantPrecision(Precision + 20);
      h := R! AbsoluteLogarithmicHeight(x);
      SetKantPrecision(old_prec);
      return h;
    elif ISA(Type(K), FldAlg) then
        xden := ideal< Integers(K) | 1, x >;
        hf := - Log(R! Norm(xden));
	r1,r2 := Signature(K);
        xcoords := Conjugates(x : Precision:=pr);
	hi := &+[ (i le r1 select 1 else 2) * Log(Max(Abs(xcoords[i]), R!1)) 
		: i in [1..r1] cat [r1+1..r1+2*r2 by 2] ];
	h := (hf + hi) / Degree(K);
    elif Type(K) eq FldRat then
	h := Log(R!Max(Abs(Numerator(x)), Abs(Denominator(x))));
    elif ISA(Type(K), FldFunG) then
        h := Max(0, Degree(x)); // TO DO: change this to be the absolute height?
    else
	require false : "Argument must be defined over a global field";
    end if;
    return h;
end intrinsic;

intrinsic NaiveHeight(P::PtEll) -> FldReElt
{The naive height (the logarithmic height of the x-coordinate) 
of the given point P on an elliptic curve defined over a number field,
or a function field.}
    return NaiveHeight(P[1]);
end intrinsic;


function ArchimedianLocalHeight(binvs, x, prec)
// {Local height at an Archimedean place}

    b2,b4,b6,b8 := Explode(binvs);
    disc := -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6;
    adisc := Abs(disc);

    H := Max([4, Abs(b2), 2*Abs(b4), 2*Abs(b6), Abs(b8)]);
    N0 := 7 + 4/3*Log(H);
    if adisc lt 1 then N0 -:= Log(adisc); end if;
    N := Ceiling(5*prec/3 + 1/2 + 3/4*Log(N0));
    vprint Height, 2 : "Precision =", prec;
    vprint Height, 2 : "x :=", x;
    vprint Height, 2 : "Using", N, "terms in height computation";

    bb2 := b2 - 12;
    bb4 := b4 - b2 + 6;
    bb6 := b6 - 2*b4 + b2 - 4;
    bb8 := b8 - 3*b6 + 3*b4 - b2 + 3;
    bbinvs := [bb2, bb4, bb6, bb8];

    bvals := [ bbinvs, [], binvs ];
    if Abs(x) ge 1/2 then
	t := 1/x;
	nlbeta := 1;
    else
	t := 1/(x+1);
	nlbeta := -1;
    end if;
    vprint Height, 2 : "t :=", t;

    lambda := -Log(Abs(t));
    mu := 0;
    for n in [0..N] do
	vprint Height, 2 : "Start of loop: n =", n;

	b2,b4,b6,b8 := Explode(bvals[nlbeta + 2]);

	vprint Height, 2 : "beta :=", Sign(nlbeta + 1);
	vprint Height, 2 : "t :=", t;

	w := 4*t + b2*t^2 + 2*b4*t^3 + b6*t^4;
	z := 1 - b4*t^2 - 2*b6*t^3 - b8*t^4;

	vprint Height, 2 : "w :=", w;
	vprint Height, 2 : "z :=", z;
/*
	if GetVerbose("Height") ge 3 then
	    "RelativePrecision(t) =", Precision(t);
	    "RelativePrecision(w) =", Precision(w);
	    "RelativePrecision(z) =", Precision(z);
	    "RelativePrecision(Abs(z)) =", Precision(Abs(z));
	end if;
*/
	if Abs(w) le 2*Abs(z) then
	    delta0 := z;
	else
	    delta0 := z + nlbeta*w;
	    nlbeta *:= -1;
	end if;

	vprint Height, 2 : "delta0 :=", delta0;
/*
	if GetVerbose("Height") ge 3 then
	    initprec := RelativePrecision(delta0);
	    "RelativePrecision(delta0) =", initprec;
	end if;
*/
	t := w / delta0;

	vprint Height, 2 : "t := w/delta0 =", t;
/*
	if GetVerbose("Height") ge 3 then
	    finprec := RelativePrecision(t);
	    "RelativePrecision(t) =", finprec;
	    "!!!!!!!!!!!!!!!!!!!!!!! Precision loss:", initprec-finprec;
	end if;
*/
	delta := Log(Abs(delta0))/4^n;
        mu +:= delta;

	vprint Height, 2 : "delta =", delta;
        vprint Height, 2 : "mu =", mu;
    end for;
    vd := -Log(adisc);
    height := lambda + mu/4 + vd/6;
    return height;
end function;

function InfiniteHeightContribution(P, prec, extra)
    E := Scheme(P);
    K := Ring(Parent(P));
    EK := E(K);

    origprec := GetKantPrecision();
//    SetKantPrecision(K, Ceiling(prec+extra));

//    r1,r2 := Signature(K);
//    binv_conj := [ Conjugates(K!b) : b in bInvariants(E) ];
IP:=InfinitePlaces(K);
binv_conj:=[[Evaluate(K!b,ip) : ip in IP] : b in bInvariants(E)];
    assure_translations(EK, binv_conj);

    hi := 0;
//    xcoords := Conjugates(P[1]);
xcoords:=[Evaluate(K!P[1],ip) : ip in IP];
/*
    for i in [1..r1] cat [r1+1..r1+2*r2 by 2] do
	if i le r1 then
	    j := i;
	    np := 1;
	else
	    j := (i + r1 + 1) div 2;
	    np := 2;
	end if;
	vprint Height : InfinitePlaces(K)[j];

	binvs := [ b[i] : b in binv_conj ];
	b2,b4,b6,b8 := Explode(binvs);
	r0 := EK`Translations[j];

	b8 +:= b2*r0^3 + 3*b4*r0^2 + 3*b6*r0 + 3*r0^4;
	b6 +:= b2*r0^2 + 2*b4*r0 + 4*r0^3;
	b4 +:= 6*r0^2 + b2*r0;
	b2 +:= 12*r0;
	binvs := [ b2, b4, b6, b8 ];
	x := xcoords[i] - r0;
	hi +:= np*ArchimedianLocalHeight(binvs, x, prec);
    end for;
*/
for ip in [1..#IP] do vprint Height : IP[ip];
	binvs := [ b[ip] : b in binv_conj ];
        wt:=IsReal(IP[ip]) select 1 else 2;
	b2,b4,b6,b8 := Explode(binvs);
	r0 := EK`Translations[ip];

	b8 +:= b2*r0^3 + 3*b4*r0^2 + 3*b6*r0 + 3*r0^4;
	b6 +:= b2*r0^2 + 2*b4*r0 + 4*r0^3;
	b4 +:= 6*r0^2 + b2*r0;
	b2 +:= 12*r0;
	binvs := [ b2, b4, b6, b8 ];
	x := xcoords[ip] - r0;
	hi +:= wt*ArchimedianLocalHeight(binvs, x, prec);
    end for;

//    SetKantPrecision(K, origprec);
    return RealField(prec)!hi;
end function;



intrinsic LocalHeight(P::PtEll[FldNum], pp::PlcNumElt :
				    Extra := 8, Precision := 0) -> FldReElt
{Local height of the point P}
    E := Scheme(P);
    K := Ring(Parent(P));
    require K cmpeq NumberField(pp) :
        "Argument 1 must be defined over the number field of argument 2";
    require Type(Precision) eq RngIntElt and Precision ge 0 :
        "Parameter Precision must be an integer at least equal to 4";
/*
    require IsAbsoluteField(K) :
        "Argument 2 must be defined over an absolute field";
*/
    extra := Extra;
origprec:=PREC(RealField());
    prec := Precision eq 0 select origprec else Max(4, Precision);
SetDefaultRealFieldPrecision(prec+extra);

    EK := E(K);
    retain_attributes(EK);
    if IsInfinite(pp) then
	x := Evaluate(P[1], pp : Precision := prec);
	binvs := [ Evaluate(b, pp : Precision := prec) : b in bInvariants(E) ];
	b2,b4,b6,b8 := Explode(binvs);
	if assigned EK`Translations then
	    r1,r2 := Signature(K);
	    i := Index(InfinitePlaces(K), pp);
	    // i := [ i : i in [1..r1+r2] | pp eq InfinitePlaces(K)[i] ][1];
	    r0 := EK`Translations[i];
	else
	    r0 := compute_translation(binvs);
	end if;
	b8 +:= b2*r0^3 + 3*b4*r0^2 + 3*b6*r0 + 3*r0^4;
	b6 +:= b2*r0^2 + 2*b4*r0 + 4*r0^3;
	b4 +:= 6*r0^2 + b2*r0;
	b2 +:= 12*r0;
	binvs := [b2,b4,b6,b8];
	x -:= r0;
	height := ArchimedianLocalHeight(binvs, x, prec+extra);
    else
	// Finite place:
	vprint Height : pp;
	E, trans := MinimalModel(E, Ideal(pp));
	P := trans(P);
	a1,a2,a3,a4,a6 := Explode(ChangeUniverse(aInvariants(E), K));
	b2,b4,b6,b8 := Explode(ChangeUniverse(bInvariants(E), K));
	c4 := K!cInvariants(E)[1];
	delta := K!Discriminant(E);
	vd := Valuation(delta, pp);
	vc4 := Valuation(c4, pp);
	x := P[1];
	y := P[2];
        f2 := Valuation(2*y + a1*x + a3, pp);
	f3 := Valuation(3*x^4 + b2*x^3 + 3*b4*x^2 + 3*b6*x + b8, pp);
	if Valuation(3*x^2 + 2*a2*x + a4 - a1*y, pp) le 0 or f2 le 0 then
	    lambda := Max(0, -Valuation(x, pp));
	    vprintf Height : "%o, nonsingular reduction: %o\n", pp, lambda;
	elif vd gt 0 and vc4 eq 0 then
	    assert(vd gt 0);
	    alpha := Min(1/2, f2/vd);
	    lambda := vd*alpha*(alpha - 1);
	    vprintf Height : "%o, multiplicative reduction: %o\n", pp, lambda;
	elif vd gt 0 and vc4 gt 0 then
	    assert(vd gt 0);
	    if f3 ge 3*f2 then
		lambda := -2*f2/3;
	    else
		lambda := -f3/4;
	    end if;
	    vprintf Height : "%o, additive reduction: %o\n", pp, lambda;
	end if;
	lambda +:= vd/6;

	logp := Log(Generator(Integers() meet Ideal(pp)));
	height := lambda * logp;
    end if;

SetDefaultRealFieldPrecision(origprec);
    return RealField(prec)!height;
end intrinsic;

intrinsic Height(P::PtEll[FldNum] : Precision := 27, Extra := 8) -> FldReElt
{The canonical height of the given point
 (on an elliptic curve over a number field). 
This is the absolute, logarithmic x-coordinate height.}

    // torsion check
    Q:=P+P; if IsId(Q) or IsId(Q+P) then return RealField()!0; end if;
    /* think this is only needed if 2-torsion or 3-torsion? */
    // if Order(P) ne 0 then return RealField()!0; end if;

    E := Scheme(P);
    K := Ring(Parent(P));

/*
    require IsAbsoluteField(K) : // not sure why? -- slow in any case
	"Argument 1 must be defined over an absolute field";
*/
    require Type(Precision) eq RngIntElt and Precision ge 0 :
        "Parameter Precision must be an integer at least equal to 4";

    prec := Precision;
    extra := Extra;
origprec:=PREC(RealField());
SetDefaultRealFieldPrecision(prec+extra);

    x := P[1];
    y := P[2];
    x_denom_inv := ideal< Integers(K) | 1, x >;
    hf := &+[ RealField() |
		AbsoluteDegree(pp)*LocalHeight(P, pp : Precision := prec+extra)
		+ Valuation(x_denom_inv, pp)*Log(AbsoluteNorm(Ideal(pp)))
	    : pp in BadPlaces(E,K) ];
    hi := InfiniteHeightContribution(P, prec, extra);
    height := (-Log(AbsoluteNorm(x_denom_inv)) + hf + hi) / AbsoluteDegree(K);
SetDefaultRealFieldPrecision(origprec);

    return RealField(prec)!height;
end intrinsic;

intrinsic HeightPairing(P::PtEll, Q::PtEll : Precision:=27) -> RngElt
{The height pairing (h(P+Q)-h(P)-h(Q))/2 for points P and Q on an elliptic curve}
    return (Height(P+Q : Precision:=Precision) - 
            Height(P   : Precision:=Precision) - 
            Height(Q   : Precision:=Precision)) / 2;
end intrinsic;

// added MW 20 Jan 2007 revised 25 May 2009

intrinsic HeightPairingMatrix(A::[PtEll] : Precision:=27, Extra:=8) -> AlgMatElt
{The height pairing matrix for the given sequence of points on an elliptic curve}
 n:=#A;
 if n eq 0 then return Matrix(RealField(Precision), 0, []); end if;
 Ht:=Height;
 h:=[Ht(A[i] : Precision:=Precision, Extra:=Extra) : i in [1..n]];
 v:=[[(Ht(A[i]+A[j] : Precision:=Precision, Extra:=Extra)-h[i]-h[j])/2 :
      i in [1..j-1]] cat [h[j]] : j in [1..n]];
 return SymmetricMatrix(&cat v); end intrinsic;

function gcd_bound_on_order(pt) // K is not Q // 12 Apr 2011
 K:=Ring(Universe([pt])); E:=Curve(pt); OK:=Integers(K); e:=0;
 E:=BaseChange(E,K); E:=IntegralModel(CubicModel(E)); c:=0; g:=0; PR:=[];
 D:=Discriminant(E); p:=2; _,a2,_,a4,a6:=Explode(aInvariants(E)); L:=1000;
 while #PR le 100 do PR:=PrimesUpTo(L,K : coprime_to:=D); L:=L*2; end while;
 while c le 5 do P:=PR[1]; assert Valuation(D,P) eq 0; Remove(~PR,1);
  u:=Norm(P); if IsEven(u) then continue; end if; // p-torsion needs
  _,mp:=ResidueClassField(OK,P); e:=e+1;          // prime not above p
  n:=#EllipticCurve([0,mp(a2),0,mp(a4),mp(a6)]);
  h:=Gcd(n*u^(100-e),g); if g eq h then c:=c+1; else c:=0; end if; g:=h;
 if g le 16 then return g; end if; end while; return g; end function;

// unclear whether reductions mod primes or curve arithmetic is faster
// coiuld depend on the base ring
intrinsic Order(P::PtEll : BSGSLimit:=256) -> RngIntElt
{The order of a point on an elliptic curve (0 if the order is infinite).}

 // TO DO: should require ISA FldAlg or FldFunG (?)

 if IsId(P) then return 1; end if; /* could also use x-coords only, etc. */
 PS:=Parent(P);
 if not assigned PS`Order then PS`Order:=AssociativeArray(PS); end if;
 if P in Keys(PS`Order) then return PS`Order[P]; end if;
 BS:=[P,P+P]; if IsId(BS[2]) then PS`Order[P]:=2; return 2; end if;
 BS cat:=[BS[2]+P]; if IsId(BS[3]) then PS`Order[P]:=3; return 3; end if;
 GS:=[BS[3]+P]; if IsId(GS[1]) then PS`Order[P]:=4; return 4; end if; 
 GS cat:=[gs+GS[1] : gs in GS];
 if IsId(GS[2]) then PS`Order[P]:=8; return 8; end if;
 GS cat:=[gs+GS[2] : gs in GS];
 if IsId(GS[3]) then
  if IsId(GS[1]+BS[2]) then PS`Order[P]:=6; return 6;
  else PS`Order[P]:=12; return 12; end if; end if;
 if IsId(GS[4]) then PS`Order[P]:=16; return 16; end if;
 M:=Set(BS) meet Set(GS);
 if #M ne 0 then u:=Random(M);
  b:=Explode([i : i in [1..#BS] | BS[i] eq u]);
  g:=Explode([i : i in [1..#GS] | GS[i] eq u]); o:=4*g-b; D:=Divisors(o);
 for d in D do
  if IsId(d*P) then PS`Order[P]:=d; return d; end if; end for; end if; 
 if ISA(Type(BaseRing(Curve(P))),FldNum) then g:=gcd_bound_on_order(P);
  if g le 16 then PS`Order[P]:=0; return 0; end if; end if; F:=Ring(Parent(P));
 if BSGSLimit le 16 or Type(F) eq FldRat then return 0; end if;
 vprint Height: "[Height] If not infinite, order is bigger than 16";
 if ISA(Type(F),FldFunG) or IsAbsoluteField(F) then
  vprint Height: "Checking height";
  ht:=Height(P); if ht gt 0.001 then PS`Order[P]:=0; return 0; end if;
  vprint Height: "Height looks near 0 -- another round of baby/giant steps";
  end if;
 BS cat:=[GS[1]]; BS cat:=[bs+GS[1] : bs in BS];
 BS cat:=[bs+GS[2] : bs in BS];
 assert #BS eq 16; GS:=[BS[16]]; Prune(~BS);
 GS cat:=[gs+GS[1]: gs in GS];
 if IsId(GS[2]) then PS`Order[P]:=32; return 32; end if;
 GS cat:=[gs+GS[2]: gs in GS]; GS cat:=[gs+GS[4]: gs in GS];
 GS cat:=[gs+GS[8]: gs in GS];
 assert #GS eq 16; G:=[i : i in [1..#GS] | IsId(GS[i])];
 if #G ne 0 then o:=16*G[1]; D:=Divisors(o);
  for d in D do if IsId(d*P) then return d; end if; end for; end if; 
 M:=Set(BS) meet Set(GS);
 if #M ne 0 then u:=Random(M);
  b:=Explode([i : i in [1..#BS] | BS[i] eq u]);
  g:=Explode([i : i in [1..#GS] | GS[i] eq u]); o:=16*g-b; D:=Divisors(o);
  for d in D do if IsId(d*P) then PS`Order[P]:=d; return d; end if; end for;
 end if; 

 B := TorsionBound(Parent(P),20);
 for d in Divisors(B) do
  if IsId(d*P) then
   return d;
  end if;
  return 0;
 end for;

end intrinsic;
