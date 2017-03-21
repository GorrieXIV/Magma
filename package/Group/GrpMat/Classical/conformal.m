freeze;

/*****************************************************
  Conformal versions of the classical groups

  May 2011 Don Taylor

  $Id: conformal.m 43900 2013-07-16 02:57:11Z don $

  History:
    Moved from group.m on 2011-05-10 (DET)

    Matrix groups moved from Derek Holt's code 
    in GrpPerm/max/conformal.m on 2011-05-16 (DET)

    Abbreviations for ConformalOrthogonalGroup[Plus|Minus| ]
    are now in the bind/c.b and so the wrappers for
    CO etc have been removed.  2013-07-05 (DET)

    All conformal group intrinsics taking a matrix as their only
    argument have been moved to the file variants.m, which is
    NOT yet listed in the spec file.  2013-07-05 (DET).

    If J is the matrix of an alternating form, say, the same
    effect can be obtained by the code:
        V := SymplecticSpace(J);
        G := SimilarityGroup(V);


******************************************************/
/* 
  Classical group name	        Abbreviation   Kleidman-Liebeck symbol
  
  ConformalUnitaryGroup           CU             Delta
  ConformalSpecialUnitaryGroup    CSU
  ConformalSymplecticGroup        CSp            Delta = GSp(2m,q)
  ConformalOrthgonalGroup         CO             Delta = GO^0(n,q)
  ConformalOrthgonalGroupPlus     COPlus         Delta = GO^+(n,q)
  ConformalOrthgonalGroupMinus    COMinus        Delta = GO^-(n,q)

  The intrinsics
  
    ConformalUnitaryGroup    alias CU
    ConformalSymplecticGroup alias CSp

  are defined at the C level for arguments:
    (n::RngIntElt, K::FldFin)
    (n::RngIntElt, q::RngIntElt)
    (V::ModTupRng)

*/

import "../../GrpPerm/max/classicals.m": NormSpMinusSp, NormGOMinusGO, GOMinusSO;


// ========================================================
//
// Conformal unitary groups
//


// raise every element of matrix A to q-th power
// also defined in "../../GrpPerm/max/superfield.m": MatToQ;
frobenius := func< A,q | Parent(A)![ x^q : x in Eltseq(A)] >;

// From Derek Holt ( /GrpPerm/max/conformal.m )
intrinsic CSU(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal special unitary group CSU(d,q)}
  local w, mform, trans, W, Y, zpow, ypow, gen;
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  
  if GCD(q-1,d) eq 1 then return G where G := SU(d,q); end if;
  
  mform := Matrix(GF(q^2),d,d, [<i,d+1-i,1>:i in [1..d]]);
  trans := CorrectForm(mform,d,q^2,"unitary");
  w := PrimitiveElement(GF(q^2));
  W := GL(d,q^2)!ScalarMatrix(GF(q^2),d,w);
  Y := DiagonalMatrix(GF(q^2),[w^(q-1)] cat [1:i in [1..d-1]]);
  Y := trans * Y * trans^-1; //Y is generator of GU/SU
  zpow := (q-1) div GCD(d,q-1);
  ypow := (-d * zpow div (q-1));
  gen := W^zpow * Y^ypow;
  if gen * mform * Transpose(frobenius(gen,q)) eq mform then //fixes form already
    return S where S := SU(d,q);
  else
    return S where S := sub< SL(d,q^2) | SU(d,q), W^zpow * Y^ypow >;
  end if;
end intrinsic;

// ========================================================
//
// Conformal orthogonal groups
//
// ---------------------------------------------------------
//
// COPlus
//
function COPlusFunc(d, q)   
  assert IsEven(d);

  gop := GOPlus(d,q);
  cofacord := FactoredOrder(gop)*Factorization(q-1);
  z:= PrimitiveElement(GF(q));
  extragen := IsEven(q) select ScalarMatrix(d, z) else
    DiagonalMatrix([z : i in [1..d div 2]] cat [1 : i in [1..d div 2]]);
  C := sub<GL(d,q) | gop, extragen >;
  C`Order := cofacord;
  C`IsClassical := true;
  C`ClassicalName := "ConformalOrthogonalPlus";
  C`ClassicalNameShort := "CO+";
  C`QuadraticForm := QuadraticFormPlus(d, GF(q));
  C`SesquilinearForm := SymmetricBilinearFormPlus(d, GF(q));
  C`ClassicalForms := 1;
  C`IsStandardClassical := true;

  return C;
end function;

intrinsic ConformalOrthogonalGroupPlus(d::RngIntElt, q::RngIntElt) -> GrpMat
{The conformal orthogonal matrix group CO+(d,q)}
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  require IsPrimePower(q) : "Invalid field size";
  return COPlusFunc(d,q);
end intrinsic;

intrinsic ConformalOrthogonalGroupPlus(d::RngIntElt, K::FldFin) -> GrpMat
{The conformal orthogonal matrix group CO+(d,K)}
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  G := COPlusFunc(d,#K);
  return ChangeRing( G, K );
end intrinsic;

intrinsic ConformalOrthogonalGroupPlus(V::ModTupFld) -> GrpMat
{The conformal orthogonal matrix group CO+(V)}
  d := Dimension(V);  K := BaseRing(V);
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  G := COPlusFunc(d,#K);
  return ChangeRing( G, K );
end intrinsic;

// From Derek's file max/conformal.m
intrinsic CGOPlus(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal orthogonal group of plus type}
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    return S where S := sub< GL(d,q) | GOPlus(d,q), ScalarMatrix(d,w) >
            where w := PrimitiveElement(GF(q));
  else
    return S where S := sub< GL(d,q) | GOPlus(d,q), NormGOMinusGO(d,q,1) >;
  end if;
end intrinsic;

intrinsic CSOPlus(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal special orthogonal group of plus type}
  local W, X, Y, Z, gens, hd;
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    if GCD(d,q-1) ne 1 then
      return S where S := sub< SL(d,q) | SOPlus(d,q), ScalarMatrix(d,w^p) >
            where w := PrimitiveElement(GF(q)) where p := (q-1) div GCD(d,q-1);
      else return S where S := SOPlus(d,q);
    end if;
  end if;

  Z := ScalarMatrix(GF(q),d,w) where w:=PrimitiveElement(GF(q));
  hd := d div 2;
  X := GOMinusSO(d,q,1);
  Y := NormGOMinusGO(d,q,1);
  //Normaliser in SL is generated by SO together with elements
  //X^x Y^y Z^z with x(q-1)/2 + yd/2 + zd = 0 mod q-1
  W := Matrix(Integers(),4,1,[(q-1) div 2, hd, d, q-1]);
  N := Nullspace(W);
  gens := [ X^n[1] * Y^n[2] * Z^n[3] : n in Generators(N) ];
  return sub< SL(d,q) | SOPlus(d,q), gens >;
end intrinsic;


// ---------------------------------------------------------
//
// COMinus
//

//This function makes matrix entries that are needed for the
//conformal orthogonal group = normaliser of GOMinus in GL.
function GetAandB(q)
  z:= PrimitiveElement(GF(q));
  for a in GF(q) do
    bool, b:= IsSquare(z - a^2);
    if bool then return a, b; end if;
  end for;
  error "couldn't find a and b in GF(", q, ")";
end function;

function COMinusFunc(d, q)
  assert IsEven(d);

  z:= PrimitiveElement(GF(q));
  G := GL(d,q);
  gom:= GOMinus(d, q);
  cofacord := FactoredOrder(gom)*Factorization(q-1);
 
  if IsEven(q) then
    prim_scal:= G!ScalarMatrix(d, z);
    C := sub<G|gom, prim_scal>;
    C`Order := cofacord;
    return C;
  else
    b, form:= SymmetricBilinearForm(gom);
    // this matrix would conjugate gom into a group preserving
    // the diagonal form given in Kleidman and Liebeck.
    mat:= G!CorrectForm(form, d, q, "orth-");

    a, b:= GetAandB(q);  
    if IsOdd((d*(q-1)) div 4) then
      delta:= G!Matrix(GF(q), d, d,
         &cat[[<2*i+1, 2*i+1, a>, <2*i+1, 2*i+2, b>,
           <2*i+2, 2*i+1, b>, <2*i+2, 2*i+2, -a>] : i in [0..((d div 2)-1)]]);
    else
      delta:= G!Matrix(GF(q), d, d,
         &cat[[<2*i+1, 2*i+1, a>, <2*i+1, 2*i+2, b>,
           <2*i+2, 2*i+1, b>, <2*i+2, 2*i+2, -a>] : i in [0..((d div 2)-2)]]
         cat [<d-1, d, 1>, <d, d-1, z>]);
    end if;
    C := sub<G| gom, delta^(mat^-1)>;
  end if;
  C`Order := cofacord;
  C`IsClassical := true;
  C`ClassicalName := "ConformalOrthogonalMinus";
  C`ClassicalNameShort := "CO-";
  C`QuadraticForm := QuadraticFormMinus(d, GF(q));
  C`SesquilinearForm := SymmetricBilinearFormMinus(d, GF(q));
  C`ClassicalForms := 1;
  C`IsStandardClassical := true;
  return C;
 
end function;
  
intrinsic ConformalOrthogonalGroupMinus(d::RngIntElt, q::RngIntElt) -> GrpMat
{The conformal orthogonal matrix group CO-(d,q)}
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  require IsPrimePower(q) : "Invalid field size";
  return COMinusFunc(d,q);
end intrinsic;

intrinsic ConformalOrthogonalGroupMinus(d::RngIntElt, K::FldFin) -> GrpMat
{The conformal orthogonal matrix group CO-(d,K)}
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  G := COMinusFunc(d,#K);
  return ChangeRing( G, K );
end intrinsic;

intrinsic ConformalOrthogonalGroupMinus(V::ModTupFld) -> GrpMat
{The conformal orthogonal matrix group CO-(V)}
  d := Dimension(V);  K := BaseRing(V);
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  G := COMinusFunc(d,#K);
  return ChangeRing( G, K );
end intrinsic;


// From Derek's file max/conformal.m
intrinsic CGOMinus(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal orthogonal group of minus type}
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    return S where S := sub< GL(d,q) | GOMinus(d,q), ScalarMatrix(d,w) >
            where w := PrimitiveElement(GF(q));
  else
    return S where S := sub< GL(d,q) | GOMinus(d,q), NormGOMinusGO(d,q,-1) >;
  end if;
end intrinsic;

intrinsic CSOMinus(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal special orthogonal group of minus type}
  local W, X, Y, Z, gens, hd;
  require IsEven(d) : "Argument 1 must be even";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if IsEven(q) then
    if GCD(d,q-1) ne 1 then
      return S where S := sub< SL(d,q) | SOMinus(d,q), ScalarMatrix(d,w^p) >
            where w := PrimitiveElement(GF(q)) where p := (q-1) div GCD(d,q-1);
      else return S where S := SOMinus(d,q);
    end if;
  end if;

  Z := ScalarMatrix(GF(q),d,w) where w:=PrimitiveElement(GF(q));
  hd := d div 2;
  X := GOMinusSO(d,q,-1);
  Y := NormGOMinusGO(d,q,-1);
  //Normaliser in SL is generated by SO together with elements
  //X^x Y^y Z^z with x(q-1)/2 + yd/2 + zd = 0 mod q-1
  W := Matrix(Integers(),4,1,[(q-1) div 2, hd, d, q-1]);
  N := Nullspace(W);
  gens := [ X^n[1] * Y^n[2] * Z^n[3] : n in Generators(N) ];
  return sub< SL(d,q) | SOMinus(d,q), gens >;
end intrinsic;


// ---------------------------------------------------------
//
// CO
//
function COFunc(d, q)
  assert IsOdd(d);

  if d eq 1 then
    C := GL(d,q);
    C`Order := q-1;
  else
    go := (d ne 1) select GO(d,q) else GL(d,q);
    ndx := IsOdd(q) select (q-1) div 2 else q-1;
    C := q gt 3 select sub<GL(d, q)| go, ScalarMatrix(d, PrimitiveElement(GF(q)))> else go;
    C`Order := FactoredOrder(go)*Factorization(ndx);
  end if;
  C`IsClassical := true;
  C`ClassicalName := "ConformalOrthogonal";
  C`ClassicalNameShort := "CO";
  C`QuadraticForm := QuadraticForm(d, GF(q));
  C`SesquilinearForm := SymmetricBilinearForm(d, GF(q));
  C`ClassicalForms := 1;
  C`IsStandardClassical := true;
  return C;
end function;
  
intrinsic ConformalOrthogonalGroup(d::RngIntElt, q::RngIntElt) -> GrpMat
{The conformal orthogonal group in odd dimension over the field of q elements}
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsOdd(d) : "Invalid dimension -- should be odd";
  require IsPrimePower(q) : "Invalid field size";
  return COFunc(d,q);
end intrinsic;

intrinsic ConformalOrthogonalGroup(d::RngIntElt, K::FldFin) -> GrpMat
{The conformal orthogonal group in odd dimension over the field K}
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsOdd(d) : "Invalid dimension -- should be odd";
  G := COFunc(d,#K);
  return ChangeRing( G, K );
end intrinsic;

intrinsic ConformalOrthogonalGroup(V::ModTupFld) -> GrpMat
{The conformal orthogonal matrix group CO(V)}
  d := Dimension(V);  K := BaseRing(V);
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsOdd(d) : "Invalid dimension -- should be odd";
  G := COFunc(d,#K);
  return ChangeRing( G, K );
end intrinsic;


// From Derek's file max/conformal.m
intrinsic CGO(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal orthogonal group in odd dimension}
  require IsOdd(d) : "Argument 1 must be odd";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if q gt 3 then
    return S where S := sub< GL(d,q) | GO(d,q), ScalarMatrix(d,w) >
            where w := PrimitiveElement(GF(q));
  else return G where G := GO(d,q);
  end if;
end intrinsic;

intrinsic CSO(d:: RngIntElt, q:: RngIntElt) -> GrpMat
{Conformal special orthogonal group in odd dimension}
  require IsOdd(d) : "Argument 1 must be odd";
  require IsPrimePower(q) : "Argument 2 is not a prime power";
  if GCD(d,q-1) gt 1 then
    return S where S := sub< SL(d,q) | SO(d,q), ScalarMatrix(d,w^p) >
            where w := PrimitiveElement(GF(q)) where p := (q-1) div GCD(d,q-1);
  else return G where G := SO(d,q);
  end if;
end intrinsic;

