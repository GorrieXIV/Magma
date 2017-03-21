freeze;
// W.A. de Graaf & J. Pilnikova.

intrinsic ParametrizeAnticanonicalP1xP1(I::RngMPol: 
  precomputedLie := false, pLrep := 0, pL := 0, 
  Diag := false) -> SeqEnum
{}

  if not precomputedLie then

    vprint ParamDP: "Computing the Lie algebra.";
    vtime ParamDP: Lrep, L := FindLieAlgebra(I);
    if (Dimension(L) ne 6) then
      error "The variety is not anticanonically embedded P1xP1",
           "  - the Lie algebra does not have the correct dimension";
    end if;

  else 
    Lrep := pLrep;
    L := pL;
  end if;


  dsd := DirectSumDecomposition(L);
  if (#dsd ne 2) or ((#dsd eq 2) and (Dimension(dsd[1]) ne 3)) then
    error "The variety is not anticanonically embedded P1xP1",
       "  - the Lie algebra does not decompose into two 3-dimensional ideals.";
  end if;

  if Diag then
    x1,y1,h1 := FindChevalleyBasisDiagonal(dsd[1]);
  else
    x1,y1,h1 := FindChevalleyBasis(dsd[1]);
  end if;
  if (x1 eq 0) then
    //print "The variety is not anticanonically embedded P1xP1";
    //print "  - the Lie algebra is not split.";
    return [ ];
  end if;
  c:= Eltseq(L ! h1);
  H1 := &+[c[k]*Basis(Lrep)[k] : k in [1..6]];
  c:= Eltseq(L ! y1);
  Y1 := &+[c[k]*Basis(Lrep)[k] : k in [1..6]];
  c:= Eltseq(L ! x1);
  X1 := &+[c[k]*Basis(Lrep)[k] : k in [1..6]];

  if Diag then
    x2,y2,h2 := FindChevalleyBasisDiagonal(dsd[2]);
  else
    x2,y2,h2 := FindChevalleyBasis(dsd[2]);
  end if;
  if (x2 eq 0) then
    //print "The variety is not anticanonically embedded P1xP1";
    //print "  - the Lie algebra is not split.";
    return [ ];
  end if;
  c:= Eltseq(L ! h2);
  H2 := &+[c[k]*Basis(Lrep)[k] : k in [1..6]];
  c:= Eltseq(L ! y2);
  Y2 := &+[c[k]*Basis(Lrep)[k] : k in [1..6]];
  c:= Eltseq(L ! x2);
  X2 := &+[c[k]*Basis(Lrep)[k] : k in [1..6]];

  space := Eigenspace(Transpose(H1), 2) meet Eigenspace(Transpose(H2), 2);
  if (Dimension(space) ne 1) then
    //print "The variety is not anticanonically embedded P1xP1";
    //print "  - the module is not as expected.";
    return [ ];
  end if;
  max_weight_vec := Basis(space)[1];

  tY1 := Transpose(Y1);
  tY2 := Transpose(Y2);

  v1 := max_weight_vec;
  v2 := 1/2 * v1 * tY1;
  v3 := 1/4 * v2 * tY1;
  v4 := 1/2 * v1 * tY2;
  v5 := 1/2 * v4 * tY1;
  v6 := 1/4 * v5 * tY1;
  v7 := 1/4 * v4 * tY2;
  v8 := 1/4 * v5 * tY2;
  v9 := 1/4 * v6 * tY2;

  M := Matrix([v1,v2,v3,v4,v5,v6,v7,v8,v9]);

  Par<s,t,u> := PolynomialRing(RationalField(), 3);
  T := [u^4,     s*u^3,   s^2*u^2,
        t*u^3,   s*t*u^2, s^2*t*u,
        t^2*u^2, s*t^2*u, s^2*t^2];
  //  now the parametrization of sbs is:  T * M

  X := [ Par | ];
  for i := 1 to 9 do
    X[i] := 0;
    for j := 1 to 9 do
      X[i] +:= T[j]*M[j][i];
    end for;
  end for;

  //  check the parametrization
  phi := hom<Generic(I) -> Par | 
    X[1], X[2], X[3], X[4], X[5], X[6], X[7], X[8], X[9]>;
  ok := true;
  for i := 1 to #Basis(I) do
    if (phi(Basis(I)[i]) ne 0) then
      ok := false;
      break i;
    end if;
  end for;
  if not ok then 
    error "Parametrization not found.",
        "The variety is probably not anticanonically embedded P1xP1";
  end if;

  return X;

end intrinsic;


