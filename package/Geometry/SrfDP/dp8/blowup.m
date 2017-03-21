freeze;
// W.A. de Graaf & J. Pilnikova.

intrinsic ParametrizeBlowup(I::RngMPol: precomputedLie := false, pLrep := 0, pL := 0) 
 					-> SeqEnum
{}

  if not precomputedLie then

    vprint ParamDP:  "Computing the Lie algebra";
    vtime ParamDP: Lrep, L := FindLieAlgebra(I);
    if (Dimension(L) ne 6) then
      error "The variety is not the blowup of the projective plane",
          " -- the Lie algebra does not have the correct dimension";
    end if;

  else 
    Lrep := pLrep;
    L := pL;
  end if;


  b, ls := HasLeviSubalgebra(L);
  if (not b) or (b and Dimension(ls) ne 3) then
    error "The variety is not the blowup of the projective plane",
         "  - the Lie algebra does not have the expected structure.";
  end if;
  nr := Nilradical(L);

  T := MatrixAlgebra(Rationals(), 3) ! 0;
  for i := 1 to 3 do
    c1 := Eltseq(nr ! (Basis(ls)[i] * Basis(nr)[1]));
    c2 := Eltseq(nr ! (Basis(ls)[i] * Basis(nr)[2]));
    T[i][1] := c1[1];
    T[i][2] := c2[1];
    T[i][3] := c1[2];
  end for;
  rT := T^-1;
  h := &+[rT[1][k]*Basis(ls)[k] : k in [1..3]];
  x := &+[rT[2][k]*Basis(ls)[k] : k in [1..3]];
  y := &+[rT[3][k]*Basis(ls)[k] : k in [1..3]];
  if ((x*y ne h) or (h*x ne 2*x) or (h*y ne -2*y)) then
    error "The variety is not the blowup of the projective plane",
             "  - the levi subalgebra is not split.";
  end if;

  c:= Eltseq(L ! h);
  H := &+[c[k]*Basis(Lrep)[k] : k in [1..6]];
  c:= Eltseq(L ! y);
  Y := &+[c[k]*Basis(Lrep)[k] : k in [1..6]];
  c:= Eltseq(L ! x);
  X := &+[c[k]*Basis(Lrep)[k] : k in [1..6]];

  space := Eigenspace(Transpose(H), 3);
  if (Dimension(space) ne 1) then
    error "The variety is not the blowup of the projective plane",
               "  - the module is not as expected.";
  end if;
  max_weight_vec := Basis(space)[1];

  adL := AdjointRepresentation(L);

  tY := Transpose(Y);

  adh := -adL(L ! h);
  ady := -adL(L ! y);

  space := Eigenspace(adh, -1) meet Eigenspace(ady, 0);
  c := Basis(space)[1];
  E12 := &+[c[k]*Basis(Lrep)[k] : k in [1..6]];
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
  
  M := Matrix([v1,v2,v3,v4,v5,v6,v7,v8,v9]);

  Par<s,t,u> := PolynomialRing(RationalField(), 3);
  T := [s^2*t, s^2*u, 
	 s*t^2, s*t*u, s*u^2,
	 t^3, t^2*u, t*u^2, u^3];

  //  now the parametrization of the blowup is:  T * M

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
         " The variety is probably not the blowup of the projective plane";
  end if;

  return X;

end intrinsic;
