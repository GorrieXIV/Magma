// *********************************************************************
// * Package: delpezzo8.mag                                     *
// * =============================                                     *
// *                                                                   *
// * Author: Josef Schicho                                             *
// *                                                                   *
// * Email : Josef.Schicho@oeaw.ac.at                                  *
// *                                                                   *
// * Date  : September 2009                                            *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Lie algebra method for Del Pezzo surfaces of degree 8,          *
// *   including singular cases.                                       *
// *   Partly adapted from the original code of Willem & Janka.        *
// *   Improved version using new functionality of HasRationalPoint.   *
// *                                                                   *
// *                                                                   *
// *********************************************************************
freeze;

function BasicCheck(I)
    H,d := HilbertPolynomial(EasyIdeal(I));
    return (Coefficients(H) eq [Rationals()|1,4,4]) and (d eq 0);
end function;

// ======================
// = Exported functions =
// ======================

intrinsic ParametrizeDegree8DelPezzo(X::Sch) -> BoolElt,MapIsoSch
{ find a parametrization of Del Pezzo surface of degree 8
  anticanonically embedded in 8-dimensional projective space.
  X may be singular (degenerate case).}

// adapted from package by Willem and Janka
  require IsOrdinaryProjective(X) and (Dimension(Ambient(X)) eq 8):
	"A variety in 8-dimensional projective space expected.";
  Qs := DefiningEquations(X);
  I := Ideal(X);
  if (#Qs ne 20) or &or[TotalDegree(f) ne 2 : f in Qs] then
	Saturate(~X);
	I := Ideal(X);
	Qs := [ p : p in Basis(I) | TotalDegree(p) eq 2 ];
  end if;
  //require BasicCheck(I):
  //	"Scheme is not a degree 8 Del Pezzo.";
  R<z1,z2,z3,z4,z5,z6,z7,z8,z9> := Generic(I);
  Q := CoefficientRing(I);
  V9 := VectorSpace(Q,9);
  P2 := ProjectiveSpace(Q,2);
  Par<s,t,u> := CoordinateRing(P2);
  Repr := myFindLieAlgebra(Ideal(Qs));
  L := Domain(Repr);
  assert (Dimension(L) ge 6);

  _, ls := HasLeviSubalgebra(L);

  if (Dimension(ls) eq 3) and (Dimension(L) eq 7) then 
  // singular Del Pezzo surface
    standardpar := [ Par |
      s^4,s^3*t,s^2*t^2,s*t^3,t^4,s^2*t*u,s*t^2*u,t^3*u,t^2*u^2];
    inv := Transpose(Matrix([V9.2,V9.3,V9.6]));

    nr := Nilradical(L);
    isom, CB := FindXYH(ls);
    if not isom then
      return false, _;
    end if;

    x := CB[1];
    y := CB[2];
    h := CB[3];
    space := Eigenspace(Transpose(Repr(L!h)), 4);
    assert (Dimension(space) eq 1);
    max_weight_vec := Basis(space)[1];

    adL := AdjointRepresentation(L);
    adh := -adL(L ! h);
    space := Eigenspace(adh, -2) meet Image(Morphism(nr,L));
    assert (Dimension(space) eq 1);
    z := L!Basis(space)[1];
    Z := Repr(z);

    tY := Transpose(Repr(L!y));
    tZ := Transpose(Repr(L!z));

    v1 := max_weight_vec;
    v2 := v1 * tY;
    v3 := 1/2 * v2 * tY;
    v4 := 1/3 * v3 * tY;
    v5 := 1/4 * v4 * tY;
    v6 := v1 * tZ;
    v7 := v2 * tZ;
    v8 := v3 * tZ;
    v9 := 1/2 * v6 * tZ;

  elif (Dimension(ls) eq 3) and (Dimension(L) eq 6) then
  // blowup of a point in P2

    standardpar := [Par| s^2*t,s^2*u,s*t^2,s*t*u,s*u^2,t^3,t^2*u,t*u^2,u^3];
    inv := Transpose(Matrix([V9.3,V9.6,V9.7]));

    // using the Nilradical to compute a Chevalley basis
    nr := Nilradical(L);
    wj := ZeroMatrix(Q,3,3);
    for i := 1 to 3 do
      c1 := Eltseq(nr ! (ls.i * nr.1));
      c2 := Eltseq(nr ! (ls.i * nr.2));
      wj[i][1] := c1[1];
      wj[i][2] := c2[1];
      wj[i][3] := c1[2];
    end for;
    rT := wj^-1;
    h := &+[rT[1][k]*ls.k : k in [1..3]];
    x := &+[rT[2][k]*ls.k : k in [1..3]];
    y := &+[rT[3][k]*ls.k : k in [1..3]];


    tY := Transpose(Repr(L!y));

    space := Eigenspace(Transpose(Repr(L!h)), 3);
    assert Dimension(space) eq 1;
    max_weight_vec := Basis(space)[1];

    adL := AdjointRepresentation(L);
    adh := -adL(L ! h);
    ady := -adL(L ! y);

    space := Eigenspace(adh, -1) meet Eigenspace(ady, 0);
    c := Basis(space)[1];
    E12 := Repr(c);
    tE12 := Transpose(E12);

    v6 := max_weight_vec;
    v7 := v6 * tY;
    v8 := 1/2 * v7 * tY;
    v9 := 1/3 * v8 * tY;
    v3 := 2 * v6 * tE12;
    v4 := v3 * tY;
    v5 := 1/2 * v4 * tY;
    v1 := v3 * tE12;
    v2 := v1 * tY;

  else
  // P1 x P1 or a twist thereof
    error if Dimension(ls) ne 6,
	"The variety is not Del Pezzo surface of degree 8",
	"  - the Lie algebra does not have the expected structure.";
    dsd := DirectSumDecomposition(L);
    if (#dsd eq 2) then
      // direct product surface  
      standardpar := [Par | u^4,     s*u^3,   s^2*u^2,
                          t*u^3,   s*t*u^2,   s^2*t*u,
                        t^2*u^2, s*t^2*u,     s^2*t^2];
      inv := Transpose(Matrix([V9.2,V9.4,V9.1]));

      isom, CB1 := FindXYH(dsd[1]);
      x1 := CB1[1]; y1 := CB1[2]; h1 := CB1[3];
      if not isom then
        return false, _;
      end if;
      tH1 := Transpose(Repr(L!h1));
      tY1 := Transpose(Repr(L!y1));

      isom, CB2 := FindXYH(dsd[2]);
      x2 := CB2[1]; y2 := CB2[2]; h2 := CB2[3];
      if not isom then
        return false, _;
      end if;
      tH2 := Transpose(Repr(L!h2));
      tY2 := Transpose(Repr(L!y2));

      space := Eigenspace(tH1, 2) meet Eigenspace(tH2, 2);

      max_weight_vec := Basis(space)[1];
      v1 := max_weight_vec;
      v2 := 1/2 * v1 * tY1;
      v3 := 1/4 * v2 * tY1;
      v4 := 1/2 * v1 * tY2;
      v5 := 1/2 * v4 * tY1;
      v6 := 1/4 * v5 * tY1;
      v7 := 1/4 * v4 * tY2;
      v8 := 1/4 * v5 * tY2;
      v9 := 1/4 * v6 * tY2;

    else 
    // sphere (anticanonically embedded)
    // we need to compute the parameter "radius^2" a
      An:= MatrixAlgebra( Rationals(), 6 );
      ad:= sub< An | [ AdjointMatrix( L, L.i ) : i in [1..6]] >;
      centralizer:= Centralizer( An, ad );
      mp := MinimalPolynomial(Basis(centralizer)[1]);
      if (Degree(mp) eq 1) then
        mp := MinimalPolynomial(Basis(centralizer)[2]);
      end if;
      D := Discriminant(mp);
      a := SquarefreeFactorization(Numerator(D)*Denominator(D));
      standardpar := [ Par | u^4, s*u^3, t*u^3, s^2*u^2, s*t*u^2, t^2*u^2,
        s*u*(s^2-a*t^2), t*u*(s^2-a*t^2), (s^2-a*t^2)^2];
      inv := Transpose(Matrix([V9.2,V9.3,V9.1]));

      U := PolynomialRing(Q);
      pol := U.1^2-a;
      E<alpha> := ext<Q | pol>;

      LE, phi := ChangeRing(L, E);
      dsd := DirectSumDecomposition(LE)[1];      
      _, CB:= FindXYH(dsd);
      x := CB[1]; y := CB[2]; h := CB[3];

      Hre := L![Eltseq(Eltseq(LE!h)[i])[1] : i in [1..6]]; 
      Him := L![Eltseq(Eltseq(LE!h)[i])[2] : i in [1..6]]; 
      Yre := L![Eltseq(Eltseq(LE!y)[i])[1] : i in [1..6]]; 
      Yim := L![Eltseq(Eltseq(LE!y)[i])[2] : i in [1..6]]; 

      tHre := Transpose(Repr(Hre));
      tHim := Transpose(Repr(Him));
      tYre := Transpose(Repr(Yre));
      tYim := Transpose(Repr(Yim));

      space := Eigenspace(tHre,2);
      assert Dimension(space) eq 1;

      v1 := Basis(space)[1];
      v2 := v1 * tYre;
      v3 := a * v2 * tHim;
      v4 := 1/2 * v2 * tYre;
      v5 := -a * v2 * tYim;
      v6 := -1/2 * a * v3 * tYim;
      v7 := 1/3 * v4 * tYre;
      v8 := -a * v4 * tYim;
      v9 := 1/4 * v8 * tYim;

    end if;
  end if;

  Rows := [v1,v2,v3,v4,v5,v6,v7,v8,v9];
  M := Matrix(Rows);
  Mi := M^-1*inv;
  para := Eltseq(Vector(standardpar) * ChangeRing(M,Par));
  back := Vector([R.i: i in [1..9]]) * ChangeRing(Mi,R);
  parai := Eltseq(back);
  phi := map<P2 -> X | para, parai: Check:=false, CheckInverse:=false>;

  return true,phi;

end intrinsic;

