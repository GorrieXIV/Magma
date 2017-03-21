freeze;
// W.A. de Graaf & J. Pilnikova.

import "csaDeg2.m": 
  CyclicAlgebra,
  MinimalLeftIdeal,
  SplitAlgebra;


mat_rep2 := function( L )

  // L is a central simple Lie algebra of dim 3; we try to find a
  // faithful rep such that its enveloping algebra has dimension 4.

  H := CartanSubalgebra( L );

  ad := AdjointMatrix(L, H.1);
  f := MinimalPolynomial(ad);
  fac := [ u[1] : u in Factorization( f )];

  F := CoefficientField(L);
  if (#fac eq 2) then
    if Degree(fac[1]) eq 2 then F := NumberField(fac[1]);
    else F := NumberField(fac[2]); 
    end if;
  end if;

  // T will be the multiplication table of L

  bp:= BasisProducts( L );
  T:= [ ];
  for i in [1..#bp] do
    for j in [1..#bp[i]] do
      cf:= Eltseq( bp[i][j] );
      for k in [1..#cf] do
        if not IsZero( cf[k] ) then
          Append( ~T, <i,j,k,cf[k]> );
        end if;
      end for;
    end for;
  end for;

  // K is the same as L, but then over F

  K:= LieAlgebra< F, 3 | T >;

  cf := Coordinates(L, H.1);
  K`CartanSubalgebra := sub< K | [elt<K|cf[1],cf[2],cf[3]>] >;
  x,y,h := ChevalleyBasis(K); h := -h;
  //print "Crisis Chevalley Basis algorithm (extension)";
  //xx, yy, hh := CrisisChevalleyBasis(K);
  //x := [xx]; y := [yy]; h := [hh];

  // x,y,h is now a Chevalley basis of L, realizing the
  // isomorphism to sl_3

  bas:= [ ];
  bas cat:= [ Vector( Eltseq( x[1] ) ) ];
  bas cat:= [ Vector( Eltseq( y[1] ) ) ];
  bas cat:= [ Vector( Eltseq( h[1] ) ) ];

  V:= VectorSpace( F, 3 );
  B:= VectorSpaceWithBasis( [ V!u : u in bas ] );
  mats:= [
    Matrix( [[0,1],[0,0]] ),
    Matrix( [[0,0],[1,0]] ),
    Matrix( [[1,0],[0,-1]] ) ];

  // r is a faithful representation of L over F

  r:= function( v )

    cf:= Coordinates( B, V!(Eltseq(v)) );
    return &+[ cf[i]*mats[i] : i in [1..3] ];
  end function;

  // we construct the list of matrices corresponding to the
  // basis elements of L, where we `blow up' every entry.

  ee:= [ r(Basis(K)[i]) : i in [1..3] ];

  bF:= Basis(F);
  deg:= #bF;
  res:= [ ];
  for m in ee do
    mat:= ScalarMatrix( CoefficientField(L), 2*deg, 0 );
    for i in [1..2] do
      for j in [1..2] do

        a:= [ Eltseq( m[i][j]*bF[k] ) : k in [1..#bF] ];
            
        for u in [1..deg] do
          for v in [1..deg] do
            mat[(i-1)*deg+u][(j-1)*deg+v]:= a[u][v];
          end for;
        end for;
      end for;
    end for; 
    Append( ~res, mat );
  end for;       

  return res;

end function;


//  ############################################################
//  ##  Chevalley basis of an algebra L over a number field K
//  ##  which isomorphic to sl2(K)
//  ##  algorithm: reduction to (relative) norm equation over K
//  ############################################################
intrinsic FindChevalleyBasisQuad(L::AlgLie) -> 
  AlgLieElt, AlgLieElt, AlgLieElt
{ find a Chevalley basis of sl2 over quadratic extension of rationals
  by reducing to a relative norm equation}

  CS := CartanSubalgebra(L);

  //  whether CS is is split
  mp := MinimalPolynomial(L ! CS.1);
  fac := [ u[1] : u in Factorization(mp) ];
  splits := true;
  for i := 1 to #fac do
     if Degree(fac[i]) gt 1 then
       splits := false;
       break i;
     end if;
  end for;

  if splits then 
    xx, yy, hh := ChevalleyBasis(L);
    return xx[1], yy[1], -hh[1];
  end if;

  F := CoefficientField(L);

  s := mat_rep2( L );

  MatA := MatrixAlgebra(F, Nrows(s[1]));
  A := sub< MatA | [MatA!a : a in s] >;
  //  mapM je matica zobrazenia L -> A
  mapM := KMatrixSpace(F, 3,4) ! 0;

  for i := 1 to 3 do
    mapM[i] := Vector(Coordinates(A, A!s[i]));
  end for;

  if (Nrows(s[1]) gt 2) then

    r := Basis(A)[1];
    if r in Center(A) then
      r := Basis(A)[2];
    end if;

    bool, a, b := CyclicAlgebra(A, r);
    if bool then
      beta := (b*b)[1][1];
      poly := MinimalPolynomial(a);
      K<y> := NumberField(poly);
      vprint ParamDP: "Solving norm equation";
      vtime ParamDP: is_split, sol := NormEquation(K, 1/beta);
      if is_split then
        coords := Eltseq(sol[1]);
        n := coords[1] + coords[2]*a;
        e := 1 + n*b;
        LI := [e, a*e];
      end if;
    else
      // a is a zero divisor
      LI := MinimalLeftIdeal(A, a);
    end if;

    if is_split then
      M2 := MatrixAlgebra(F, 2);
      rM2 := SplitAlgebra(A, LI);
      //TestIsomorphism(M2, A, rM2);

      cx := Vector(Coordinates(M2, M2 ! [0,1,0,0])) * rM2;
      cy := Vector(Coordinates(M2, M2 ! [0,0,1,0])) * rM2;
      ch := Vector(Coordinates(M2, M2 ! [1,0,0,-1])) * rM2;
      c := Solution(mapM, [cx,cy,ch]);

      ChX := &+[c[1][k]*Basis(L)[k] : k in [1..3]];
      ChY := &+[c[2][k]*Basis(L)[k] : k in [1..3]];
      ChH := &+[c[3][k]*Basis(L)[k] : k in [1..3]];
    end if;

  else
    is_split := true;

    cx := Vector(Coordinates(A, A![0,1,0,0]));
    cy := Vector(Coordinates(A, A![0,0,1,0]));
    ch := Vector(Coordinates(A, A![1,0,0,-1]));
    c := Solution(mapM, [cx,cy,ch]);

    ChX := &+[c[1][k]*Basis(L)[k] : k in [1..3]];
    ChY := &+[c[2][k]*Basis(L)[k] : k in [1..3]];
    ChH := &+[c[3][k]*Basis(L)[k] : k in [1..3]];
  end if;

  if not is_split then
    ChX := L ! 0;
    ChY := L ! 0;
    ChH := L ! 0;
  end if;

  return ChX, ChY, ChH; 

//end function;
end intrinsic;


function CheckChevalleyBasisRep(x,y,h)

  if x*y - y*x ne h then
    return false;
  end if;

  if h*x - x*h ne 2*x then
    return false;
  end if;

  if h*y - y*h ne -2*y then
    return false;
  end if;

  return true;

end function;


function CheckChevalleyBasis(x,y,h)

  if x*y ne h then
    return false;
  end if;

  if h*x ne 2*x then
    return false;
  end if;

  if h*y ne -2*y then
    return false;
  end if;

  return true;

end function;


