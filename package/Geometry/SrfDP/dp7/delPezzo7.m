// *********************************************************************
// * Package: delpezzo7.mag                                            *
// * =============================                                     *
// *                                                                   *
// * Author: Josef Schicho                                             *
// *                                                                   *
// * Email : Josef.Schicho@oeaw.ac.at                                  *
// *                                                                   *
// * Date  : ?? 2009                                                   *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Lie algebra method for Del Pezzo surfaces of degree 7,          *
// *   including singular cases.                                       *
// *                                                                   *
// *                                                                   *
// *********************************************************************
freeze;

intrinsic ParametrizeDegree7DelPezzo(X::Sch) -> MapIsoSch
{
Find a parametrization of Del Pezzo surface of degree 7 anticanonically embedded in 7-dimensional projective space. X may be singular (degenerate case).
}

  require IsOrdinaryProjective(X) and (Dimension(Ambient(X)) eq 7):
	"A variety in 7-dimensional projective space expected.";
  Qs := DefiningEquations(X);
  if (#Qs ne 14) or &or[TotalDegree(f) ne 2 : f in Qs] then
	Saturate(~X);
	I := Ideal(X);
	Qs := [ p : p in Basis(I) | TotalDegree(p) eq 2 ];
  end if;
  Q := BaseRing(X);
  R := Generic(Ideal(X));
  V8 := VectorSpace(Q,8);

  vprint ParamDP: "Computing Lie algebra.";
  vtime ParamDP: Repr := myFindLieAlgebra(Ideal(Qs));
  L := Domain(Repr);
  P2 := ProjectiveSpace(BaseRing(X),2);
  Par<s,t,u> := CoordinateRing(P2);

  if (Dimension(L) eq 4) then
  // the nonsingular case: blowup at 2 points
  // which may be in an algebraic extension

    nr := Nilradical(L);
    assert Dimension(nr) eq 2;
    t1 := L!Basis(nr)[1]; t2 := L!Basis(nr)[2];

    // compute an element that acts trivial on the nilradical
    adL := AdjointRepresentation(L);
    adt1 := -adL(t1);
    adt2 := -adL(t2);
    sys := HorizontalJoin(adt1,adt2);
    rhs := HorizontalJoin(-t1,-t2);
    draw := Solution(sys,rhs);
    d := L!draw[1];

    // compute a nice abelian subalgebra acting on the nilradical
    add := -adL(d);
    space2 := Eigenspace(add,0);
    space1 := sub<VectorSpace(Rationals(),4)|draw>;
    space := Complement(space2,space1);
    assert Dimension(space) eq 1;
    r:= L!Basis(space)[1];
    adr := -adL(r);
    r := r-Trace(adr)/Trace(add)*d;

    // make the basis of the Nilradical nice
    t1 := r*t2;

    // in the algebra <d,r>, r is the root of a
    a := Solution(r*t1,t2)[1][1];

    standardpar := [ Par | u^3, s*u^2, t*u^2, s^2*u, s*t*u, t^2*u,
        s*(s^2-a*t^2), t*(s^2-a*t^2)];
    inv := Transpose(Matrix([V8.2,V8.3,V8.1]));

    T1 := Repr(t1); T2 := Repr(t2);
    T1t := Transpose(T1); T2t := Transpose(T2);
    D := Repr(d);
    Dt := Transpose(D);
    space := Eigenspace(Dt,-7/4);
    assert Dimension(space) eq 1;

    v1 := Basis(space)[1];
    v2 := v1 * T1t;
    v3 := v1 * T2t;
    v4 := 1/2 * v1 * T1t * T1t;
    v5 := v1 * T1t* T2t;
    v6 := 1/2 * v1 * T2t * T2t;
    v7 := 1/6 * v1 * T1t * T1t * T1t;
    v8 := -1/6/a * v1 * T2t * T2t * T2t;

  else
  // singular surface: one of the points blown up is infinitely near
    standardpar := [Par| u^3, s*u^2, t*u^2, s^2*u, s*t*u, t^2*u, s^3, s^2*t];
    inv := Transpose(Matrix([V8.2,V8.3,V8.1]));

    error if Dimension(L) ne 5,
	"The variety is not Del Pezzo surface of degree 7",
	"  - the Lie algebra does not have the expected structure.";

    // The Lie algebra is supposed to be the one of triangular matrices

    adL := AdjointRepresentation(L);

    nr := Nilradical(L);
    assert Dimension(nr) eq 3;

    // compute a vectorspace of diagonal elements
    space1 := Image(Morphism(L,L));
    space2 := Image(Morphism(nr,L));
    space := Complement(space1,space2);
    ar1 := L!Basis(space)[1];
    space1 := Eigenspace(adL(ar1),0);
    space := Complement(space1,space1 meet space2);
    ar1 := L!Basis(space)[1];
    ar2 := L!Basis(space)[2];

    // compute a diagonal element with trace 0 (unique up to scaling)
    a1 := Trace(ar2)*ar1-Trace(ar1)*ar2;
    ada1 := -adL(a1);

    // Eigenspace decomposition of a1.
    // a1 is also normed.
    // The two elements b1,b2 can only be distinguished by their representation!
    ev := Eigenvalues(ada1);
    ep := Maximum([v[1] : v in ev]);
    em := Minimum([v[1] : v in ev]);
    a1 := a1/ep; ada1 := -adL(a1);
    space := Eigenspace(ada1,1);
    assert Dimension(space) eq 1;
    b1 := L!Basis(space)[1];
    space := Eigenspace(ada1,-1);
    assert Dimension(space) eq 1;
    b2 := L!Basis(space)[1];
    if (Rank(Repr(b1)) eq 5) then
      swap := b1; b1 := b2; b2 := swap; a1 := -a1;
    end if;

    // c is the generator of the centre of the nilradical
    c := b1*b2;

    // Second diagonal matrix, chosen orthogonal to b1
    adb1 := -adL(b1);
    space := Eigenspace(ada1,0) meet Eigenspace(adb1,0);
    assert (Dimension(space) eq 2);
    a2 := L!Basis(space)[1];
    if IsZero(a2*b2) then
      a2 := L!Basis(space)[2];
    end if;
    a2 := a2/Trace(a2);

    // get canonical basis for representation
    A1t := Transpose(Repr(a1));
    A2t := Transpose(Repr(a2));
    B1t := Transpose(Repr(b1));
    B2t := Transpose(Repr(b2));
    Ct := Transpose(Repr(c));

    // get module basis proper
    space := Eigenspace(A2t,7/8);
    assert Dimension(space) eq 1;

    v1 := Basis(space)[1];
    v2 := v1 * B2t;
    v3 := v2 * B1t;
    v4 := 1/2 * v2 * B2t;
    v5 := v4 * B1t;
    v6 := 1/2 * v5 * B1t;
    v7 := 1/3 * v4 * B2t;
    v8 := v7 * B1t;

  end if;

  Rows := [v1,v2,v3,v4,v5,v6,v7,v8];
  M := Matrix(Rows);
  Mi := M^-1*inv;
  para := Eltseq(Vector(standardpar) * ChangeRing(M,Par));
  back := Vector([R.i: i in [1..8]]) * ChangeRing(Mi,R);
  parai := Eltseq(back);
  phi := map<P2 -> X | para, parai: Check:=false, CheckInverse:=false>;

  return phi;

end intrinsic;
