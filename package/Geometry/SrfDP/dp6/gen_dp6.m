freeze;

////////////////////////////////////////////////////////////////////////////
////    Functions to generate Degree 6 Del Pezzos from tori.            ////
////       mch - 05/06                                                  ////
////////////////////////////////////////////////////////////////////////////

intrinsic Degree6DelPezzoType2_1(K::FldNum,pt::Pt) -> Sch
{ Returns a degree 6 Del Pezzo surface containing point pt and 
  with a torus derived from K/k (a quadratic extension) as the
  connected automorphism group.}
    require Degree(K) eq 2:
	"First argument should be a quadratic extension of its base field.";
    k := BaseField(K);
    P6 := Scheme(pt);
    require IsAmbient(P6) and IsOrdinaryProjective(P6) and
		 (Ring(Parent(pt)) eq k):
	"Second argument must be a point of P^6 over the base field",
	 " of the first argument";
    if BaseRing(P6) cmpne k then P6 := ChangeRing(P6,k); end if;
    pt := Coordinates(pt);
    pt0 := pt[1];
    Remove(~pt,1);
    require pt0 ne 0:
	"Second argument cannot have zero as first coordinate.";
    require not((pt[1] eq 0) or (pt[2] eq 0) or 
			&or[(pt[i] eq 0) and (pt[i+1] eq 0) : i in [3,5]]):
	"Second argument not a valid point for this torus action.";
 
    y := K.1;
    c,b := Explode(Coefficients(MinimalPolynomial(y)));

    My := Matrix(k,2,2,[0,-c,1,-b]);
    R := PolynomialRing(k,2);
    RF := FieldOfFractions(R);
    u := R.1+R.2*ChangeRing(My,R);
    nrm := Determinant(u);
    u2 := ChangeRing(u,RF);
    u2i := u2^-1;
    M6 := DiagonalJoin(DiagonalJoin(u2,u2i),DiagonalMatrix([RF!nrm,1/(RF!nrm)]));
    elts := [RF!pt0] cat Eltseq(M6*Matrix(RF,6,1,pt));

    mp := map<Spec(R)->P6| elts>;
    X := Image(mp);
    return X;

end intrinsic;

intrinsic Degree6DelPezzoType2_2(K::FldNum,pt::Pt) -> Sch
{ Returns a degree 6 Del Pezzo surface containing point pt and 
  with a torus derived from K/k (a quadratic extension) as the
  connected automorphism group.}
    require Degree(K) eq 2:
	"First argument should be a quadratic extension of its base field.";
    k := BaseField(K);
    P6 := Scheme(pt);
    require IsAmbient(P6) and IsOrdinaryProjective(P6) and
		 (Ring(Parent(pt)) eq k):
	"Second argument must be a point of P^6 over the base field",
	 " of the first argument";
    if BaseRing(P6) cmpne k then P6 := ChangeRing(P6,k); end if;
    pt := Coordinates(pt);
    pt0 := pt[1];
    Remove(~pt,1);
    require pt0 ne 0:
	"Second argument cannot have zero as first coordinate.";
    require not(&or[(pt[i] eq 0) and (pt[i+1] eq 0) : i in [1,3,5]]):
	"Second argument not a valid point for this torus action.";

    y := K.1;
    c,b := Explode(Coefficients(MinimalPolynomial(y)));

    My := Matrix(k,2,2,[0,-c,1,-b]);
    R := PolynomialRing(k,2);
    RF := FieldOfFractions(R);
    u := R.1+R.2*ChangeRing(My,R);
    nrm := Determinant(u);
    u2 := ChangeRing(u,RF);
    u2i := u2^-1;
    u22 := 1/(RF!nrm) * u2^2;
    M6 := DiagonalJoin(DiagonalJoin(u2,u2i),u22);
    elts := [RF!pt0] cat Eltseq(M6*Matrix(RF,6,1,pt));

    mp := map<Spec(R)->P6| elts>;
    X := Image(mp);
    return X;

end intrinsic;

intrinsic Degree6DelPezzoType2_3(K::FldNum,pt::Pt) -> Sch
{ Returns a degree 6 Del Pezzo surface containing point pt and 
  with a torus derived from K/k (a quadratic extension) as the
  connected automorphism group.}
    require Degree(K) eq 2:
	"First argument should be a quadratic extension of its base field.";
    k := BaseField(K);
    P6 := Scheme(pt);
    require IsAmbient(P6) and IsOrdinaryProjective(P6) and
		 (Ring(Parent(pt)) eq k):
	"Second argument must be a point of P^6 over the base field",
	 " of the first argument";
    if BaseRing(P6) cmpne k then P6 := ChangeRing(P6,k); end if;
    pt := Coordinates(pt);
    pt0 := pt[1];
    Remove(~pt,1);
    require pt0 ne 0:
	"Second argument cannot have zero as first coordinate.";
    require not(&or[(pt[i] eq 0) and (pt[i+1] eq 0) : i in [1,3,5]]):
	"Second argument not a valid point for this torus action.";

    y := K.1;
    c,b := Explode(Coefficients(MinimalPolynomial(y)));

    My := Matrix(k,2,2,[0,-c,1,-b]);
    R := PolynomialRing(k,2);
    RF := FieldOfFractions(R);
    u := R.1+ChangeRing(My,R);
    v := R.2+ChangeRing(My,R);
    nrm1 := Determinant(u);
    nrm2 := Determinant(v);
    u2 := 1/(RF!nrm1)*ChangeRing(u^2,RF);
    v2 := 1/(RF!nrm2)*ChangeRing(v^2,RF);
    M6 := DiagonalJoin(DiagonalJoin(u2,v2),u2*v2);
    elts := [RF!pt0] cat Eltseq(M6*Matrix(RF,6,1,pt));

    mp := map<Spec(R)->P6| elts>;
    X := Image(mp);
    return X;

end intrinsic;

intrinsic Degree6DelPezzoType3(K::FldNum,pt::Pt) -> Sch
{ Returns a degree 6 Del Pezzo surface containing point pt and 
  with a torus derived from K/k (a cubic extension) as the
  connected automorphism group.}
    require Degree(K) eq 3:
	"First argument should be a cubic extension of its base field.";
    k := BaseField(K);
    P6 := Scheme(pt);
    require IsAmbient(P6) and IsOrdinaryProjective(P6) and
		 (Ring(Parent(pt)) eq k):
	"Second argument must be a point of P^6 over the base field",
	 " of the first argument";
    if BaseRing(P6) cmpne k then P6 := ChangeRing(P6,k); end if;
    pt := Coordinates(pt);
    pt0 := pt[1];
    Remove(~pt,1);
    require pt0 ne 0:
	"Second argument cannot have zero as first coordinate.";
    require not(&or[&and[pt[i+j] eq 0 : j in [0..2]] : i in [1,4]]):
	"Second argument not a valid point for this torus action.";

    y := K.1;
    c,b,a := Explode(Coefficients(MinimalPolynomial(y)));
    My := Matrix(k,3,3,[0,0,-c,1,0,-b,0,1,-a]);
    My2 := My^2;
    R := PolynomialRing(k,3);
    RF := FieldOfFractions(R);
    u := R.1+R.2*ChangeRing(My,R)+R.3*ChangeRing(My2,R);
    nrm := Determinant(u);
    u3 := ChangeRing(u^3,RF)*(1/RF!nrm);
    u3i := u3^(-1);
    elts := [RF!pt0] cat Eltseq(DiagonalJoin(u3,u3i)*Matrix(RF,6,1,pt));

    mp := map<Proj(R)->P6| elts>;
    X := Image(mp);
    return X;

end intrinsic;

intrinsic Degree6DelPezzoType6(K::FldNum,pt::Pt) -> Sch
{ Returns a degree 6 Del Pezzo surface containing point pt and 
  with a torus derived from K/k (a sextic extension) as the
  connected automorphism group.}
    require Degree(K) eq 6:
	"First argument should be a sextic extension of its base field.";
    k := BaseField(K);
    y := K.1;
    f := MinimalPolynomial(K.1);
    a := Coefficient(f,4)/2;
    require (Degree(f) eq 6) and (Coefficient(f,5) eq 0) and
	(Coefficient(f,3) eq 0) and (Coefficient(f,1) eq 0) and
	  (Coefficient(f,2) eq a^2):
	"Field generator of first argument must have minimal\n",
	"polynomial of the form x^6+2*a*x^4+a^2*x^2-d.";
    d := -Coefficient(f,0);
    // f = x^6+2a*x^4+a^2*x^2-d

    P6 := Scheme(pt);
    require IsAmbient(P6) and IsOrdinaryProjective(P6) and
		 (Ring(Parent(pt)) eq k):
	"Second argument must be a point of P^6 over the base field",
	 " of the first argument";
    if BaseRing(P6) cmpne k then P6 := ChangeRing(P6,k); end if;
    pt := Coordinates(pt);
    pt0 := pt[1];
    require pt0 ne 0:
	"Second argument cannot have zero as first coordinate.";
    Remove(~pt,1);
    pt := [p/pt0: p in pt];
    require not(&and[pt[i] eq 0 : i in [1,6]]):
	"Second argument not a valid point for this torus action.";

    A6 := AffinePatch(P6,7);
    P := CoordinateRing(A6);
    P1 := PolynomialRing(k);
    K3 := ext<k|P1.1^3+2*a*P1.1^2+a^2*P1.1-d>;
    Embed(K3,K,y^2);
    K2 := ext<k|P1.1^2-d>;
    Embed(K2,K,y^3+a*y);

    PK := PolynomialRing(K3,6);
    Q := (PK.1+K3.1*PK.3+K3.1^2*PK.5)^2 - K3.1*(PK.2+K3.1*PK.4+K3.1^2*PK.6)^2;
    Q -:= PK!Evaluate(Q,pt);
    Qs := [ &+[Eltseq(LeadingCoefficient(t))[i]*
	   Monomial(P,Exponents(t)): t in Terms(Q)] : i in [1..3] ];
    PK := PolynomialRing(K2,6);
    C := Determinant(&+[PK.(i+1)*ChangeRing(M^i,PK):i in [0..5]])
	where M is Matrix(K2,3,3,[0,0,K2.1,1,0,-K2!a,0,1,0]);
    C -:= PK!Evaluate(C,pt);
    Cs := [ &+[Eltseq(LeadingCoefficient(t))[i]*
           Monomial(P,Exponents(t)): t in Terms(C)] : i in [1..2] ];

    Xa := Scheme(A6,Cs cat Qs);
    return ProjectiveClosure(Xa);

end intrinsic;

intrinsic Degree6DelPezzoType4(K::FldNum,K1::FldNum,pt::Pt) -> Sch
{ Returns a degree 6 Del Pezzo surface containing point pt and 
  with a torus derived from K/k & K1/k (distinct quadratic extensions)
  as the connected automorphism group.}
    k := BaseField(K);
    require (Degree(K) eq 2) and (Degree(K1) eq 2) and (BaseField(K1) cmpeq k):
	"First 2 arguments should be quadratic extensions of the same base field.";
    require IsIrreducible(PolynomialRing(K)!MinimalPolynomial(K1.1)) :
	"First 2 arguments must be distinct fields.";
    P6 := Scheme(pt);
    require IsAmbient(P6) and IsOrdinaryProjective(P6) and
		 (Ring(Parent(pt)) eq k):
	"Third argument must be a point of P^6 over the base field",
	 " of the first argument";
    if BaseRing(P6) cmpne k then P6 := ChangeRing(P6,k); end if;
    pt := Coordinates(pt);
    pt0 := pt[1];
    require pt0 ne 0:
	"Third argument cannot have zero as first coordinate.";
    Remove(~pt,1);
    require not(&and[pt[i] eq 0 : i in [1,4]] or 
	((pt[5] eq 0) and (pt[6] eq 0))):
	"Third argument not a valid point for this torus action.";

    y := K1.1;
    k := BaseField(K);
    f1,e1 := Explode(Coefficients(MinimalPolynomial(y)));

    z := K.1;
    f,e := Explode(Coefficients(MinimalPolynomial(z)));

    R<a,b,c,d> := PolynomialRing(k,4);

    M1 := Matrix(R,2,2,[a,-f*b,b,a-e*b]);
    M2 := Matrix(R,2,2,[c,-f*d,d,c-e*d]);
    M4 := VerticalJoin(HorizontalJoin(M1,-f1*M2),HorizontalJoin(M2,M1-e1*M2));

    M2 := Matrix(R,2,2,[a,-f1*b,b,a-e1*b]);

    R<a,b> := PolynomialRing(k,2);

    nrm := -e1^2*e*a*b + e1^2*f*b^2 + e1^2*a^2 + e1*f1*e*b - 2*e1*f1*a - e1*e^2*a*b^2 +
    e1*e*f*b^3 + 3*e1*e*a^2*b - 2*e1*f*a*b^2 - 2*e1*a^3 + f1^2 + f1*e^2*b^2 -
    2*f1*e*a*b - 2*f1*f*b^2 + 2*f1*a^2 + e^2*a^2*b^2 - 2*e*f*a*b^3 - 2*e*a^3*b +
    f^2*b^4 + 2*f*a^2*b^2 + a^4;

    vec1 := [
    e1^3*e*b - e1^3*a + e1^2*f1 + e1^2*e^2*b^2 - 4*e1^2*e*a*b + e1^2*f*b^2 +
        3*e1^2*a^2 - e1*f1*e*b - e1*f1*a - 2*e1*e^2*a*b^2 + 2*e1*e*f*b^3 +
        5*e1*e*a^2*b - 3*e1*f*a*b^2 - 3*e1*a^3 - f1^2 - f1*e^2*b^2 + 2*f1*e*a*b
        + e^2*a^2*b^2 - 2*e*f*a*b^3 - 2*e*a^3*b + f^2*b^4 + 2*f*a^2*b^2 + a^4,
    e1^3*b + e1^2*e*b^2 - 2*e1^2*a*b - 3*e1*f1*b - e1*e*a*b^2 + e1*f*b^3 +
        e1*a^2*b - 2*f1*e*b^2 + 4*f1*a*b,
    e1^2*e*b - e1^2*a + e1*f1 + e1*e^2*b^2 - 4*e1*e*a*b + e1*f*b^2 + 3*e1*a^2 -
        2*f1*a - 2*e^2*a*b^2 + 2*e*f*b^3 + 4*e*a^2*b - 2*f*a*b^2 - 2*a^3,
    e1^2*b + e1*e*b^2 - 2*e1*a*b - 2*f1*b - 2*e*a*b^2 + 2*f*b^3 + 2*a^2*b
    ];

    vec2 := [
    e1^4 + 2*e1^3*e*b - 4*e1^3*a - 3*e1^2*f1 + e1^2*e^2*b^2 - 6*e1^2*e*a*b +
        2*e1^2*f*b^2 + 6*e1^2*a^2 - 4*e1*f1*e*b + 8*e1*f1*a - 2*e1*e^2*a*b^2 +
        2*e1*e*f*b^3 + 6*e1*e*a^2*b - 4*e1*f*a*b^2 - 4*e1*a^3 + f1^2 -
        f1*e^2*b^2 + 6*f1*e*a*b - 2*f1*f*b^2 - 6*f1*a^2 + e^2*a^2*b^2 -
        2*e*f*a*b^3 - 2*e*a^3*b + f^2*b^4 + 2*f*a^2*b^2 + a^4,
    e1^3 + 2*e1^2*e*b - 4*e1^2*a - 2*e1*f1 + e1*e^2*b^2 - 6*e1*e*a*b +
        2*e1*f*b^2 + 6*e1*a^2 - 2*f1*e*b + 4*f1*a - 2*e^2*a*b^2 + 2*e*f*b^3 +
        6*e*a^2*b - 4*f*a*b^2 - 4*a^3
    ];

    // if g=K.1, g1=K1.1 and l=a+b*g+g1 , G(K.K1/K) = <s> then
    //   Norm(K.K1/k)(l) = nrm &
    //   s(l)/l = (v1+v2*g+v3*g1+v4*g*g1)/nrm where vec1 = [v1,v2,v3,v4] &
    //   Norm(K.K1/K1)(s(l)/l) eq (w1+g1*w2)/nrm where vec2 := [w1,w2]

    M4 := Matrix(R,4,4,[Evaluate(x,vec1):x in Eltseq(M4)]);
    M2 := Matrix(R,2,2,[Evaluate(x,vec2 cat [0,0]):x in Eltseq(M2)]);
    M6 := DiagonalJoin(M4,M2);
    elts := [pt0*nrm] cat Eltseq(M6*Matrix(R,6,1,pt));

    mp := map<Spec(R)->P6| elts>;
    X := Image(mp);
    return X;

end intrinsic;

