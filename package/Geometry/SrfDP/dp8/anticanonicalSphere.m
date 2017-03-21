freeze;
// W.A. de Graaf & J. Pilnikova.

//  #######################################################
//  ##  input: irreducible quadratic polynomial over Q
//  ##  output: a quadratic poly with as small coeffs
//  ##          as possible defining the same 
//  ##          field extension as input
//  #######################################################
function MinimizeMinpoly(mp)

  if not (LeadingCoefficient(mp) eq 1) then
    mp := mp/LeadingCoefficient(mp);
  end if;
  linC := Coefficient(mp,1); 
  absC := Coefficient(mp,0); 

  Q := PolynomialRing(Rationals()); x := Q.1;
  shift := linC/2;
  mp := (x-shift)^2 + linC*(x-shift) + absC;

  newAbsC := Coefficient(mp, 0);

  nA := Numerator(newAbsC);
  dA := Denominator(newAbsC);
  abs := dA*nA;
  absFac := Factorization(abs);
  if newAbsC gt 0 then
    newAbsC := 1;
  else
    newAbsC := -1;
  end if; 
  for i := 1 to #absFac do
    if absFac[i][2] mod 2 eq 1 then
      newAbsC *:= absFac[i][1];
    end if;
  end for;
  mp := x^2 + newAbsC;

  return mp;
  
end function;



//  #######################################################
//  ##  finds an isomorphism of the surface given by f
//  ##  and P1xP1 over a field extension
//  #######################################################
function ParametrizeAnticanonicalOverExtension(I: 
  precomputedLie := false, pLrep := 0, pL := 0)

  if not precomputedLie then

    vprint ParamDP: "Computing the Lie algebra.";
    vtime ParamDP: Lrep, L := FindLieAlgebra(I);
    if (Dimension(L) ne 6) then
      error "The variety is not anticanonically embedded sphere",
            " -- the Lie algebra does not have the correct dimension";
    end if;

  else 
    Lrep := pLrep;
    L := pL;
  end if;


  dsd := DirectSumDecomposition(L);
  if #dsd ne 1 then 
    error "The variety is not anticanonically embedded sphere",
            "  - the Lie algebra is not simple over the rationals.";
  end if;

  An:= MatrixAlgebra( Rationals(), 6 );
  ad:= sub< An | [ AdjointMatrix( L, L.i ) : i in [1..6]] >;
  centralizer:= Centralizer( An, ad );
  mp := MinimalPolynomial(Basis(centralizer)[1]);
  if (Degree(mp) eq 1) then
    mp := MinimalPolynomial(Basis(centralizer)[2]);
  end if;

  mp := MinimizeMinpoly(mp);

  E<w> := NumberField(mp);

  LE, phi := ChangeRing(L, E);
  LrepE, phi := ChangeRing(Lrep, E);

  dsd := DirectSumDecomposition(LE);
  if #dsd ne 2 then
    error "The variety is not anticanonically embedded sphere",
        "  - the Lie algebra doesn't decompose into two ideals over the centroid.";
  end if;

  vprint ParamDP: "Identifying sl2 (1)";
  x1,y1,h1 := FindChevalleyBasisQuad(dsd[1]);
  if (x1 eq 0) then
    //print "The variety is not anticanonically embedded sphere";
    //print "  - the Lie algebra doesnot split over the centroid.";
    return [];
  end if;
  c:= Eltseq(LE ! h1);
  H1 := &+[c[k]*Basis(LrepE)[k] : k in [1..6]];
  c:= Eltseq(LE ! y1);
  Y1 := &+[c[k]*Basis(LrepE)[k] : k in [1..6]];
  c:= Eltseq(LE ! x1);
  X1 := &+[c[k]*Basis(LrepE)[k] : k in [1..6]];

  vprint  ParamDP: "Identifying sl2 (2)";
  x2,y2,h2 := FindChevalleyBasisQuad(dsd[2]);
  if (x2 eq 0) then
    //print "The variety is not anticanonically embedded sphere";
    //print "  - the Lie algebra doesnot split over the centroid.";
    return [ ];
  end if;
  c:= Eltseq(LE ! h2);
  H2 := &+[c[k]*Basis(LrepE)[k] : k in [1..6]];
  c:= Eltseq(LE ! y2);
  Y2 := &+[c[k]*Basis(LrepE)[k] : k in [1..6]];
  c:= Eltseq(LE ! x2);
  X2 := &+[c[k]*Basis(LrepE)[k] : k in [1..6]];

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

  Par<s0,s1, t0,t1> := PolynomialRing(E, 4);
  T := [s0^2*t0^2,  s0^2*t0*t1,  s0^2*t1^2,
        s0*s1*t0^2, s0*s1*t0*t1, s0*s1*t1^2,
        s1^2*t0^2,  s1^2*t0*t1,  s1^2*t1^2];
  //  now the parametrization of sbs is:  T * M

  X := [ Par | ];
  for i := 1 to 9 do
    X[i] := 0;
    for j := 1 to 9 do
      X[i] +:= T[j]*M[j][i];
    end for;
  end for;

  return X;

end function;



function AnticanonicalIntersectConjugates(prm)

  pe := PrimitiveElement(CoefficientRing(Parent(prm[1])));
  mp := MinimalPolynomial(pe);
  if not (LeadingCoefficient(mp) eq 1) then
    mp := mp/LeadingCoefficient(mp);
  end if;

  discr := pe;
  linC := Coefficient(mp,1);
  if linC ne 0 then discr := pe + linC/2; end if;

  PrmSpace<a,b,c> :=  PolynomialRing(CoefficientRing(Parent(prm[1])), 3);
  RR<t0,t1,tt0,tt1> := PolynomialRing(PrmSpace, 4);

  phi := hom<Parent(prm[1]) -> RR | t0, t1, a+discr*b, c>;
  psi := hom<RR -> RR | tt0, tt1, 0,0>;

  p := [RR | ];
  for i := 1 to 9 do 
    p[i] := phi(prm[i]); 
    cf := Coefficients(p[i]);
    mn := Monomials(p[i]);
    np := RR ! 0;
    for j := 1 to #mn do
      cff := Coefficients(cf[j]);
      mnn := Monomials(cf[j]);
      npp := PrmSpace ! 0;
      for k := 1 to #mnn do
        coef := Trace(cff[k]) - cff[k];
        npp := npp + coef*mnn[k];
      end for;
      np := np + npp*mn[j];
    end for;
    p[i+9] := psi(np);
  end for;

  T := ZeroMatrix(PrmSpace, 9, 6);
  for i := 1 to 9 do
    cf := Coefficients(p[i]);
    mn := Monomials(p[i]);
    for j := 1 to #mn do
      if mn[j] eq t0^2 then T[i][1] := cf[j];
      elif mn[j] eq t0*t1 then T[i][2] := cf[j];
      elif mn[j] eq t1^2 then T[i][3] := cf[j];
      end if;
    end for;
    cf := Coefficients(p[i+9]);
    mn := Monomials(p[i+9]);
    for j := 1 to #mn do
      if mn[j] eq tt0^2 then T[i][4] := cf[j];
      elif mn[j] eq tt0*tt1 then T[i][5] := cf[j];
      elif mn[j] eq tt1^2 then T[i][6] := cf[j];
      end if;
    end for;
  end for;

  ns := NullSpace(Transpose(T));
  if #Basis(ns) ne 1 then
    //print "Dimension of solution space not 1! It is", #Basis(ns);
  end if;
  bv := Basis(ns)[1];

  preX := [ PrmSpace | ];
  for i := 1 to 9 do
    preX[i] := T[i][1]*bv[1] + T[i][2]*bv[2] + T[i][3]*bv[3];
  end for;
  cfs := Coefficients(preX[1]);
  coords := Eltseq(cfs[1]);
  if coords[2] ne 0 then
    for i := 1 to 9 do
      preX[i] := discr*preX[i];
    end for;
  end if;

  Par<U,V,W> := PolynomialRing(Rationals(), 3);
  map := hom< PrmSpace -> Par | U,V,W>;

  X := [ Par | ];
  for i := 1 to 9 do
    X[i] := map(preX[i]);
  end for;

  return X;

end function;



intrinsic ParametrizeAnticanonicalSphere(I::RngMPol: 
  precomputedLie := false, pLrep := 0, pL := 0) -> SeqEnum
{}

  vprint ParamDP: "Parametrizing over extension...";
  prm1 := ParametrizeAnticanonicalOverExtension(I: 
    precomputedLie := precomputedLie, pLrep := pLrep, pL := pL);
  if (prm1 eq [ ]) then
    return [ ];
  end if;

  //  ##  begin write output
  //  Write(outputFile, 
  //    "Intermediate parametrization");
  //  Write(outputFile, "over the splitting field: ");
  //  Write(outputFile, CoefficientRing(Parent(prm1[1])));
  //  Write(outputFile, prm1);
  //  Write(outputFile, "\n............................\n");
  //  ##  end write output

  vprint ParamDP: "Intersecting conjugates...";
  prm2 := AnticanonicalIntersectConjugates(prm1);

  //  check the parametrization
  phi := hom<Generic(I) -> Parent(prm2[1]) | 
    prm2[1], prm2[2], prm2[3], prm2[4], prm2[5], prm2[6], prm2[7], prm2[8], prm2[9]>;
  ok := true;
  for i := 1 to #Basis(I) do
    if (phi(Basis(I)[i]) ne 0) then
      ok := false;
      break i;
    end if;
  end for;
  if not ok then 
    error "Parametrization not found.",
          "The variety is probably not anticanonically embedded sphere";
  end if;

  return prm2;

end intrinsic;
