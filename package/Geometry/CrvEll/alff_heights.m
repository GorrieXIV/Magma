freeze;
 
////////////////////////////////////////////////////////////////////
//        Heights on elliptic curves over function fields         //
//                       Martine Girard                           //
//                    girard@maths.usyd.edu.au                    //
//                       May 2004                                 //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic LocalHeight(P::PtEll[FldFunG], p::PlcFunElt : Precision := 0)
							    -> FldRatElt
{Local height of a point on an elliptic curve over a function field}
// The Precision parameter is ignored but retained to avoid special
// cases in HeightPairing() and similar routines.

    E := Scheme(P);
    require FunctionField(p) eq BaseRing(E) :
        "Point must lie on a curve defined over the function field of the place";

    a1,a2,a3,a4,a6 := Explode(aInvariants(E));
    b2,b4,b6,b8 := Explode(bInvariants(E));
    c4,_ := Explode(cInvariants(E));
    Delta := Discriminant(E);
    x := P[1];
    y := P[2];
    v := Valuation(Delta, p);
    c := Floor(v/12);

    // bug fix 28 jan 2006 by Jasper:
    m:=Min([(Valuation(a1,p)-c)*12, (Valuation(a2,p)-2*c)*6, (Valuation(a3,p)-3*c)*4,
            (Valuation(a4,p)-4*c)*3, (Valuation(a6,p)-6*c)*2]);
    if m lt 0 then c+:=Floor(m/12); end if;

    vd := v - 12*c;
    f2 := Valuation(2*y + a1*x + a3, p) - 3*c;
    f3 := Valuation(3*x^4 + b2*x^3 + 3*b4*x^2 + 3*b6*x + b8, p) - 8*c;
    if Valuation(3*x^2 + 2*a2*x + a4 - a1*y, p) - 4*c le 0 or f2 le 0 then
	lambda := Max(0, -(Valuation(x, p) - 2*c));
	vprintf Height : "at %o, nonsingular reduction: %o\n", p, lambda;
    elif Valuation(c4, p) - 4*c eq 0 then
	assert(vd gt 0);
	alpha := Min(1/2, f2/vd);
	lambda := vd*alpha*(alpha - 1);
	vprintf Height : "at %o, multiplicative reduction: %o\n", p, lambda;
    else
	assert(vd gt 0);
	if f3 ge 3*f2 then
	    lambda := -2*f2/3;
	else
	    lambda := -f3/4;
	end if;
	vprintf Height : "at %o, additive reduction: %o\n", p, lambda;
    end if;
    return lambda + vd/6;
end intrinsic;

intrinsic Height(P::PtEll[FldFunG] : Precision := 0) -> FldRatElt
{The canonical height of the given point (on an elliptic curve over a function field).}
// The Precision parameter is ignored but retained to avoid special
// cases in HeightPairing() and similar routines.

    Q := Rationals();
    if IsId(P) then return Q!0; end if;

    D := Discriminant(Scheme(P));
    poles := IsZero(P[1]) select [] else Poles(P[1]);    
    
    // places := SequenceToSet(Poles(D) cat Zeroes(D) cat poles);
    // This is wrong in characteristic 3: for y^2=x^3+ax+b, 
    // it misses places where b has a pole, 
    // Sometimes these need to be included, 
    // eg y^2=x^3-x+t^2, P = [0,t], over F_3(t).
    //                              ---- Steve
    E := Scheme(P);
    if Type(BaseRing(E)) eq FldFunRat then 
       badplaces := &cat[ Zeroes(pl) : pl in BadPlaces(E) ];
    else 
       badplaces := BadPlaces(E);
    end if;
    places := SequenceToSet( Poles(D) cat Zeroes(D) cat poles cat badplaces );
    height := &+[ Rationals() | Degree(p)*LocalHeight(P, p) : p in places ]; 
    return Q!height;
end intrinsic;

