freeze;

// Title: Conjugacy Classes in Finite Symplectic Groups
// Full documentation in the file: SpConjugacy.pdf
// Author: Don Taylor
// Project start: August 2015
// ====================================================
/*
    $Id: SpConjugacy.m 52564 2016-05-12 05:24:20Z don $
*/
//==============================================================================
import "common.m" : convert, allPartitions, signedPartitionsSp, primaryParts,
   stdJordanBlock, centralJoin, getSubIndices, restriction, homocyclicSplit,
   type1Companion;

type2Companion := function( f )
  error if f ne DualPolynomial(f), "polynomial must be *-symmetric";
  e := Degree( f );
  error if IsOdd(e), "degree must be even";
  d := e div 2;
  a := Coefficients( f )[2..d+1];
  C := ZeroMatrix( BaseRing(f), e, e );
  for i := 1 to d-1 do
    C[i,i+1] := 1;
    C[d+1,i+1] := a[i];
    C[d+i+1,d+i] := 1;
    C[e-i+1,e] := -a[i];
  end for;
  C[d,e] := -1;
  C[d+1,1] := 1;
  C[d+1,e] := -a[d];
  return C;
end function;

type3CompanionS := func< a0, i | DiagonalJoin(B, B^-1) where
    B is stdJordanBlock(i, -a0) >;

type3CompanionO := function(a0, c, sgn)
  F := Parent( a0 );
  B := stdJordanBlock(c,F!1);
  X := -a0*DiagonalJoin(B,B^-1);
  a := IsEven(c) select -F!2 else F!2;
  if (sgn lt 0) then a *:= Nonsquare(F); end if;
  for i := 1 to c do X[c,c+i] := IsOdd(i) select a else -a; end for;
  return X;
end function;

type1Matrix := function(f, plist)
  factors := Factorisation(f);
  h := factors[1][1];
  assert f eq h*factors[2][1];
  X := ZeroMatrix( BaseRing(f), 0, 0 );
  for mu in plist do
    e, m := Explode(mu);
    for i := 1 to m do X := centralJoin(X, type1Companion(h^e)); end for;
  end for;
  return X;
end function;

type2Matrix := function(f, plist)
  X := ZeroMatrix( BaseRing(f), 0, 0 );
  for mu in plist do
    e, m := Explode(mu);
    for i := 1 to m do X := centralJoin(X, type2Companion( f^e )); end for;
  end for;
  return X;
end function;

isSignedPartition := func< pi |
  forall{ mu : mu in pi |IsEven(mu[1]) or (IsEven(mu[2]) and mu[1] gt 0)} >;

type3Matrix := function(f, plist)
  assert Degree(f) eq 1;
  error if not isSignedPartition( plist ), "not a signed partition";
  a0 := Coefficient(f,0);
  F := BaseRing(f);
  q := #F;
  X := ZeroMatrix( F, 0, 0 );
  for mu in plist do
    e, m := Explode(mu);
    if IsOdd( e ) then
      for i := 1 to (m div 2) do
        X := centralJoin( X, type3CompanionS( a0, e ) );
      end for;
    else
      c := Abs(e) div 2;
      X := ((q mod 4 eq 1) or (m mod 4 eq 0))
        select centralJoin(X, type3CompanionO(a0, c, e))
        else centralJoin(X, type3CompanionO(a0, c, -e));
      for i := 2 to m do
        X := centralJoin(X, type3CompanionO( a0, c, 1));
      end for;
    end if;
  end for;
  return X;
end function;


//==============================================================================
intrinsic RepresentativeMatrixSp( inv::SetIndx[Tup] ) -> GrpMatElt
{A representative of the symplectic conjugacy class with
 invariant inv}
 F := BaseRing(Parent(inv[1][1]));
 X := ZeroMatrix( F, 0, 0 );
 for polpart in inv do
   f, plist := Explode(polpart);
   if (Degree(f) eq 1) then
     X := centralJoin(X, type3Matrix(f, plist));
   elif IsIrreducible(f) then
     X := centralJoin(X, type2Matrix(f, plist));
   else
     X := centralJoin(X, type1Matrix(f, plist));
   end if;
 end for;
 return SymplecticGroup(Nrows(X),F)!X;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassInvariantsSp( d::RngIntElt, q::RngIntElt ) -> SeqEnum
{ The conjugacy class invariants for the symplectic group
  Sp(d,q) }
  require IsOdd(q): "q must be odd";
  F := GF(q);
  pols := &cat[ StarIrreduciblePolynomials(F,i) : i in [1..d] ];
  parts := allPartitions(d);
  sparts := signedPartitionsSp(d);
  oldinv := [ [] : n in [1..d] ];
  inv := oldinv;
  for f in pols do
    fparts := (Degree(f) eq 1) select sparts else parts;
    for n := 0 to d-1 do
      dimleft := d-n;
      if Degree(f) le dimleft then
        multleft := dimleft div Degree(f);
        for i := 1 to multleft do
          for param in ((n ne 0) select oldinv[n] else [ {@ @}]) do
            for part in fparts[i] do
              Append( ~inv[n+Degree(f)*i], Include(param,<f,part>) );
            end for;
          end for;
        end for;
      end if;
    end for;
    oldinv := inv;
  end for;
  return inv[d];
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic UnipotentInvariantsSp( d::RngIntElt, q::RngIntElt ) -> SeqEnum
{ The invariants for the unipotent conjugacy classes in the
  symplectic group Sp(d,q) }
  require IsOdd(q) : "q must be odd";
  t := PolynomialRing(GF(q)).1;
  return [ {@ <t - 1, part> @} : part in signedPartitionsSp(d)[d] ];
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassRepresentativesSp( d::RngIntElt, q::RngIntElt :
   Unipot := false ) -> SeqEnum, SeqEnum
{ Representatives for the conjugacy classes of the symplectic
  group Sp(d,q).  If Unipot is true, return only unipotent
  classes.  The second return value is the sequence of class
  invariants. }
  require IsOdd(q) : "q must be odd";
  invar := (Unipot) select UnipotentInvariantsSp(d,q) else ClassInvariantsSp(d,q);
  return [SymplecticGroup(d,q) | RepresentativeMatrixSp(mu) : mu in invar], invar;
end intrinsic;
//------------------------------------------------------------------------------

A_fn := function(f, e, m, q)
  d := Degree(f);
  if IsIrreducible(f) then
    if d eq 1 then
      if IsOdd(e) then
        val := OrderSp(m,q);
      else
        if IsOdd(m) then
          val := OrderGO(m,q);
        elif (e lt 0) then
          val := OrderGOMinus(m,q);
        else
          val := OrderGOPlus(m,q);
        end if;
      end if;
    else
      val := OrderGU(m,q^(d div 2));
    end if;
  else
    val := OrderGL(m,q^(d div 2));
  end if;
  return val;
end function;

kappa := function(plist, d)
  val := 0;
  for mu in plist do
    e, m := Explode(mu);
    val +:= (Abs(e)-1)*m^2;
    if d eq 1 and IsEven(e) then val +:= m; end if;
  end for;
  for i := 1 to #plist-1 do
    e := Abs(plist[i][1]);
    m := plist[i][2];
    for j := i+1 to #plist do val +:= 2*e*m*plist[j][2]; end for;
  end for;
  val *:= d;
  assert IsEven(val);
  return val div 2;
end function;

B_fn := function(pol_part)
  f, plist := Explode(pol_part);
  q := #BaseRing(f);
  d := Degree(f);
  return q^kappa(plist,d) * &*[A_fn(f,mu[1],mu[2],q) : mu in plist];
end function;


//==============================================================================
intrinsic CentraliserOrderSp( inv :: SetIndx[Tup] ) -> RngIntElt
{The order of the centraliser of any element in the symplectic
 group whose conjugacy invariant is inv}
 return &*[ B_fn(pol_part) : pol_part in inv ];
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassesSp(d::RngIntElt,q::RngIntElt) -> SeqEnum
{The conjugacy classes of Sp(d,q)}
  ord := OrderSp(d,q);
  return Sort([car<Integers(),Integers(),Sp(d,q)>|
    < Order(M), ord div CentraliserOrderSp(mu), M > :
        mu in ClassInvariantsSp(d,q) | true
        where M is RepresentativeMatrixSp(mu) ]);
end intrinsic;
//------------------------------------------------------------------------------

attachSign := function(D,g,f,mu)
  F := BaseRing(g);
  a0 := Evaluate(f,0);
  e, m := Explode(mu);
  A := g + ScalarMatrix(F,Nrows(g),a0);
  D0 := sub< D | [v*A : v in Basis(D)] >;
  E := [v : v in ExtendBasis(D0,D) | v notin D0];
  delta := (g - g^-1)^(e-1);
  B := Matrix(F,#E,#E,[DotProduct(D!(u*delta),v) : u,v in E ]);
  assert Determinant(B) ne 0;
  sq, _ := IsSquare(Determinant(B));

  if (#F mod 4 eq 3) and (m mod 4 eq 2) then sq := not sq; end if;
  return sq select mu else < -e,m>;
end function;


//==============================================================================
intrinsic ConjugacyInvariantSp( g :: GrpMatElt ) -> SetIndx[Tup]
{ The conjugacy class invariant of the symplectic matrix g }
  F := BaseRing(g);
  std := StandardAlternatingForm(Nrows(g),F);
  require g*std*Transpose(g) eq std :
    "matrix is not in the standard symplectic group";
  _, T, pFact := PrimaryRationalForm(g);
  V := SymplecticSpace(std);
  pols, parts, bases := primaryParts(pFact);
  inv := {@ @};
  for i := 1 to #pols do
    f := pols[i];
    plist := convert(parts[i]);
    if Degree(f) eq 1 then
      base := bases[i];

      gg := restriction(g,[T[j] : j in base]);
      d := #base;
      B := Matrix(F,d,d, [DotProduct(V!T[r],V!T[s]) : r, s in base]);
      W := SymplecticSpace(B);
      D := homocyclicSplit(gg,W);
      for j := 1 to #plist do
        if IsEven(plist[j][1]) then
          plist[j] := attachSign(D[j],gg,f,plist[j]);
        end if;
      end for;
    end if;
    Include(~inv, <f, plist> );
  end for;
  return inv;
end intrinsic;
//------------------------------------------------------------------------------

