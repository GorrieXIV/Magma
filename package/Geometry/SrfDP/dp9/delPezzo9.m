freeze;

////////////////////////////////////////////////////////////////////////////////
///        PARAMETRISATION OF DEGREE 9 DEL PEZZO SURFACES                     //
//                Main function.  J. Pilnikova.                               //
////////////////////////////////////////////////////////////////////////////////

import "csaDeg3.m": 
  CyclicAlgebra,
  MinimalLeftIdeal,
  SplitAlgebra; 

function BasicCheck(I)
    H,d := HilbertPolynomial(EasyIdeal(I));
    return (Coefficients(H) eq [Rationals()|1,9/2,9/2]) and (d eq 0);
end function;

intrinsic ParametrizeDegree9DelPezzo(X::Sch) -> BoolElt, MapIsoSch
{ Determines whether a Del Pezzo surface of degree 9
  anticanonically embedded in 9-dimensional projective space over the rationals
  is parametrizable over the rationals. If so, also returns a parametrization.}

  require (BaseRing(X) eq Rationals()): "A variety defined over rationals expected.";
  require IsOrdinaryProjective(X) and (Dimension(Ambient(X)) eq 9):
	"A variety in 9-dimensional projective space expected.";
  Qs := DefiningEquations(X);
  if (#Qs ne 27) or &or[TotalDegree(f) ne 2 : f in Qs] then
	Saturate(~X);
  end if;
  I := Ideal(X);
  require BasicCheck(I):
	"Scheme is not a degree 9 Del Pezzo.";

  vprint ParamDP: "Computing Lie algebra.";
  vtime ParamDP: rep := myFindLieAlgebra(I);
  L := Domain(rep);
  bLrep := [rep(b) : b in Basis(L)];
  if (Dimension(L) ne 8) then
    error "The variety is not Del Pezzo surface of degree 9",
        " -- the Lie algebra does not have the correct dimension";
  end if;
  vprint ParamDP: "Computing associative algebra.";
  vtime ParamDP: A, rMapM := FindAsocAlgebraRep(L);

  // SRD - 03/13 - Use more efficient lattice methods to split
  // the algebra.
  A1,mAtoA1 := Algebra(A);
  AA := AssociativeAlgebra(A1);

  vprintf ParamDP : "Maximal order: "; 
  vtime ParamDP :
  OAA := MaximalOrder(AA);

  if Discriminant(OAA) ne 1 then
    return false, _;
  end if;

  vprintf ParamDP : "Trivializing: "; 
  vtime ParamDP :
  triv := TrivializeNew(AA, Basis(OAA));

  // Now just need to convert the inverse of triv into a matrix
  // rM expressing triv^-1 w.r.t. standard basis of M3 and
  // basis of A.
  M3 := Codomain(triv);
  mat := Matrix([Eltseq(triv(AA!(mAtoA1(b)))) : b in Basis(A)]);
  rMapM := (mat^-1)*rMapM;

/*
  //  identifying M3 - beginning
  if (Degree(A) gt 3) then
    r := Basis(A)[1];
    if r in Centre(A) then
      r := Basis(A)[2];
    end if;

    vprint ParamDP: "Transforming to cyclic algebra.";
    vtime ParamDP: bool, a, b := CyclicAlgebra(A, r);
    if bool then
      beta := (b*b*b)[1][1];
      poly := MinimalPolynomial(a);
      K<y> := NumberField(poly);
      vprint ParamDP: "Solving cubic norm equation.";
      vtime ParamDP: is_split, sol := NormEquation(K, 1/beta);
      if is_split then
        n := sol[1][1] + sol[1][2]*a + sol[1][3]*a^2;
        bool, inv_b := IsInvertible(b);
        sn := b * n * inv_b;
        e := 1 + n*b + n*sn*b^2;
        leftI := [e, a*e, a^2*e];
      else
	return false,_;
      end if;
    else
      // a is a zero divisor
      leftI := MinimalLeftIdeal(A, a);
    end if;

    M3 := MatrixAlgebra(Rationals(), 3);

    rM := SplitAlgebra(A, leftI);
    rMapM := rM*rMapM;
  else
    M3 := A;
  end if;
  //  identifying M3 - end
*/
  //TestAssocIsomorphism(M3, A, rM);
  //TestLieIsomorphism(M3, L, rMapM);

  h1 := M3 ! [1,0,0, 0,-1,0, 0,0,0];
  h2 := M3 ! [0,0,0, 0,1,0, 0,0,-1];
  ya := M3 ! [0,0,0, 1,0,0, 0,0,0];
  yb := M3 ! [0,0,0, 0,0,0, 0,1,0];
  yab := M3 ! [0,0,0, 0,0,0, 1,0,0];

  outM := MatrixAlgebra(Rationals(), 9) ! 0;
  outM[1][1] := -1;
  outM[5][5] := -1;
  outM[9][9] := -1;

  outM[2][4] := -1;
  outM[4][2] := -1;
  outM[3][7] := -1;
  outM[7][3] := -1;
  outM[6][8] := -1;
  outM[8][6] := -1;

  c := Vector(Coordinates(M3, h1)) * rMapM;
  H1 := &+[c[k]*bLrep[k] : k in [1..8]];
  c := Vector(Coordinates(M3, h2)) * rMapM;
  H2 := &+[c[k]*bLrep[k] : k in [1..8]];
  space := Eigenspace(Transpose(H1), 3) meet NullSpace(Transpose(H2));

  if (Dimension(space) eq 0) then
    rMapM := outM*rMapM;

    c := Vector(Coordinates(M3, h1)) * rMapM;
    H1 := &+[c[k]*bLrep[k] : k in [1..8]];
    c := Vector(Coordinates(M3, h2)) * rMapM;
    H2 := &+[c[k]*bLrep[k] : k in [1..8]];
    space := Eigenspace(Transpose(H1), 3) meet NullSpace(Transpose(H2));
  end if;

  if (Dimension(space) ne 1) then
    error "Parametrization not found.",
       "The variety is probably not Del Pezzo surface of degree 9";
  end if;

  max_weight_vec := Basis(space)[1];

  c := Vector(Coordinates(M3, ya)) * rMapM;
  Ya := &+[c[k]*bLrep[k] : k in [1..8]];
  c := Vector(Coordinates(M3, yb)) * rMapM;
  Yb := &+[c[k]*bLrep[k] : k in [1..8]];
  c := Vector(Coordinates(M3, yab)) * rMapM;
  Yab := &+[c[k]*bLrep[k] : k in [1..8]];

  tYa := Transpose(Ya);
  tYb := Transpose(Yb);
  tYab := Transpose(Yab);

  v1 := max_weight_vec;
  v4 := v1 * tYa / 3;
  v9 := v1 * tYab / 9;
  v7 := v4 * tYa / 6;
  v10 := v4 * tYab / 9;
  v6 := v9 * tYab / 18;
  v2 := v7 * tYa / 9;
  v5 := v7 * tYab / 9;
  v8 := v6 * tYa / 3;
  v3 := v6 * tYab / 27;

  M := Matrix([v1,v2,v3,v4,v5,v6,v7,v8,v9,v10]);

  //tidy M
  M := LCM([Denominator(e) : e in Eltseq(M)])*M;
  M := (1/GCD([Numerator(e) : e in Eltseq(M)]))*M;

  Par<s,t,u> := PolynomialRing(BaseRing(X), 3);
  T := [s^3, t^3, u^3, s^2*t, t^2*u, u^2*s, s*t^2, t*u^2, u*s^2, s*t*u];
  Ti := [[1,4,9],[7,2,5],[6,8,3]];

  //  now the parametrization is:  T * M

  Y := [ Polynomial(row,T) : row in RowSequence(Transpose(M)) ];

  // and the inverse parametrisation(s) are M^-1 * Ti

  R := CoordinateRing(Ambient(X));
  tMi := Transpose(M^-1);
    // tidy tMi
  tMi := LCM([Denominator(e) : e in Eltseq(tMi)])*tMi;
  tMi := (1/GCD([Numerator(e) : e in Eltseq(tMi)]))*tMi;
    // seq = the linear polynomials in the row vector (R.1,..,R.10)*(M^-1)
  seq := [Polynomial(row,[R.i : i in [1..10]]) : row in RowSequence(tMi)];
  Yi := [[seq[j] : j in e] : e in Ti];

  //  Y is the parametrization
  //  check it:
  phi := hom<Generic(I) -> Par | 
    Y[1], Y[2], Y[3], Y[4], Y[5], Y[6], Y[7], Y[8], Y[9], Y[10]>;
  ok := true;
  for i := 1 to #Basis(I) do
    if (phi(Basis(I)[i]) ne 0) then
      ok := false;
      break i;
    end if;
  end for;
  if not ok then 
    error "Parametrization not found.",
       "The variety is probably not the blowup of the projective plane";
  end if;

  return true, iso<Proj(Par)->X|Y,Yi : Check := false>;

end intrinsic;

