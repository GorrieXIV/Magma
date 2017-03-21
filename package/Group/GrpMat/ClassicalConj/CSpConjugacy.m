freeze;

// Title: Conjugacy Classes in Conformal Symplectic Groups
// Full documentation in the file: CSpConjugacy.pdf
// Author: Don Taylor
// Project start: October 2015
// ====================================================
/*
   $Id: CSpConjugacy.m 52455 2016-04-28 05:17:05Z don $ 
*/
//==============================================================================
import "common.m" : convert, allPartitions, signedPartitionsSp,
   stdJordanBlock, centralJoin,
   getSubIndices, restriction, homocyclicSplit;


//==============================================================================
intrinsic PhiDual(f :: RngUPolElt, phi :: FldFinElt) -> RngUPolElt
{The phi-dual of the polynomial f}
  eseq := Coefficients(f);
  require eseq[1] ne 0 : "Polynomial must have non-zero constant term";
  dseq := [ eseq[i]*phi^(i-1) : i in [1..#eseq] ];
  return dseq[1]^-1 * Parent(f)!Reverse(dseq);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic PhiIrreduciblePolynomials(F :: FldFin, d :: RngIntElt) -> SeqEnum[Tup]
{All pairs <phi,pols> where pols is the sequence of all monic
 polynomials of degree d with no proper phi-symmetric factor}

  P := PolynomialRing(F); t := P.1;

  monicIrreducibles := func< n |
    (n eq 1) select [ t - a : a in F | a ne 0 ]
    else Setseq(AllIrreduciblePolynomials(F,n)) >;

  hatPoly := function(g, phi)
    R := RationalFunctionField(F); x := R.1;
    return P!( x^Degree(g) * Evaluate( R!g, x + phi/x ) );
  end function;

  multGrp := [ phi : phi in F | phi ne 0 ];
  m := #multGrp;
  polseq := [];
  if d eq 1 then
    for i := 1 to m do
      phi := multGrp[i];
      flag, lambda := IsSquare(phi);

      polseq[i] := flag select <phi,Sort([t + lambda, t - lambda])> else <phi, [] >;
    end for;
  elif IsEven(d) then
    allhalf := monicIrreducibles(d div 2 );
    for i := 1 to m do
      phi := multGrp[i];
      pols := {@ @};
      if d eq 2 then
        if not IsSquare(phi) then Include(~pols, t^2 - phi); end if;
        if not IsSquare(-phi) then Include(~pols, t^2 + phi); end if;
      end if;
      pols join:= {@ f : g in allhalf | IsIrreducible(f) where f is hatPoly(g,phi) @}
          join {@ g*gphi : g in allhalf | g ne gphi where gphi is PhiDual(g, phi) @};
      polseq[i] := < phi, IndexedSetToSequence(pols) >;
    end for;
  end if;
  return polseq;
end intrinsic;
//------------------------------------------------------------------------------

primaryPhiParts := function(phi, pFact)
  P := Parent(pFact[1][1]);
  pols := [P|  ];
  parts := [];
  duals := [P| ];
  rows := [];
  j := 1;
  rownum := 0;
  for i := 1 to #pFact do
    f := pFact[i][1]; ndx := pFact[i][2];
    if f eq PhiDual(f,phi) then
      if j eq 1 or pols[j-1] ne f then
        pols[j] := f;
        parts[j] := [];
        rows[j] := [];
        j +:= 1;
      end if;
      Append(~parts[j-1], ndx);
      r := j - 1;
    elif f notin duals then // skip if in duals
      h := PhiDual(f,phi);
      if IsEmpty(duals) or h ne duals[#duals] then
        Append(~duals,h);
        pols[j] := h*f;
        parts[j] := [];
        rows[j] := [];
        j +:= 1;
      end if;
      Append(~parts[j-1], ndx);
      r := j - 1;
    else
      h := PhiDual(f,phi);
      r := Index(pols,f*h);
    end if;
    m := Degree(f)*ndx;
    rows[r] cat:= [rownum + i : i in [1..m]];
    rownum +:= m;
  end for;
  return pols, parts, rows;
end function;

type1Companion := function(phi,h)
  d := Degree(h);
  A := CompanionMatrix(h);
  Lambda := ZeroMatrix(BaseRing(h),d,d);
  for i := 1 to d do Lambda[i,d-i+1] := 1; end for;
  return DiagonalJoin(A,phi*Lambda*Transpose(A^-1)*Lambda);
end function;

type2Companion := function(phi, f, i)
  error if f ne PhiDual(f,phi), "polynomial must be phi-symmetric";
  error if not IsIrreducible(f), "polynomial must be irreducible";
  t := Parent(f).1;
  error if IsDivisibleBy(t^2 - phi,f) and IsOdd(i), "power must be even";
  h := f^i;
  e := Degree(h);
  d := e div 2;
  a := Coefficients(h)[2..d+1];
  C := ZeroMatrix( BaseRing(h), e, e );
  psi := phi^(1-d);
  for i in [1..d-1] do
    C[i,i+1] := 1;
    C[d+1,i+1] := phi*a[i];
    C[d+i+1,d+i] := phi;
    C[e-i+1,e] := -psi*a[i];
  end for;
  C[d,e] := -phi^-d;
  C[d+1,1] := phi^(d+1);
  C[d+1,e] := -psi*a[d];
  return C;
end function;

type3CompanionS := function(phi, f, i)
  a0 := Coefficient(f,0);
  C := (Degree(f) eq 1) select stdJordanBlock(i,-a0) else CompanionMatrix(f^i);
  d := Nrows(C);
  Lambda := ZeroMatrix(BaseRing(f),d,d);
  for i := 1 to d do Lambda[i,d-i+1] := 1; end for;
  return DiagonalJoin(C,phi*Lambda*Transpose(C^-1)*Lambda);
end function;

type3CompanionO := function(lambda, c, flag)
  F := Parent(lambda);
  B := stdJordanBlock(c,F!1);
  g := lambda*DiagonalJoin(B,B^-1);
  a := IsEven(c) select -F!2 else F!2;
  if (not flag) then a *:= Nonsquare(F); end if;
  for i := 1 to c do g[c,c+i] := IsOdd(i) select a else -a; end for;
  return g;
end function;

type3CompanionOext := function(phi, c, flag)
  F := Parent(phi);
  C := Matrix(F,2,2,[0,1,phi,0]); // companion matrix for $t^2 - \phi$
  B := stdJordanBlock(c,F!1);
  X11 := KroneckerProduct(B,C);
  X22 := KroneckerProduct(B^-1,C);
  if flag then
    M := IdentityMatrix(F,2);
  else
    t := PolynomialRing(F).1;
    E<tau> := ext< F | t^2 - phi >;
    alpha := Nonsquare(E);
    M := Matrix(F,2,2,[Eltseq(alpha,F),Eltseq(alpha*tau,F)]);
  end if;
  S := ZeroMatrix(F,c,c);
  for i := 1 to c do S[c,i] := IsOdd(i) select 1 else -1; end for;
  X12 := KroneckerProduct(S,M);
  return BlockMatrix(2,2,[[X11,X12],[ZeroMatrix(F,2*c,2*c),X22]]);
end function;


//==============================================================================
intrinsic ClassInvariantsCSp(d :: RngIntElt, q :: RngIntElt) -> SeqEnum
{The conjugacy class invariants for the conformal symplectic
  group CSp(d,q), q odd}
  require IsOdd(q) : "q must be odd";
  F := GF(q);
  t := PolynomialRing(F).1;
  polseq := [];
  mgrp := [ x[1] : x in PhiIrreduciblePolynomials(F,1) ];
  X := [PhiIrreduciblePolynomials(F,i) : i in [1] cat [2..d by 2] ];
  for i := 1 to q-1 do polseq[i] := &cat[x[i][2] : x in X]; end for;
  parts := allPartitions(d);
  sparts := signedPartitionsSp(d);
  inv := [];

  isOtype := function(mu)
    for lambda in mu do
      e, m := Explode(lambda);
      if IsEven(e) and IsOdd(m) then return true, (e gt 0); end if;
    end for;
    return false, _;
  end function;

  for i := 1 to q - 1 do
    phi := mgrp[i];
    fseq := polseq[i];

    Xi := [ [] : n in [1..d] ];
    prevXi := Xi;
    prevTags := Xi;
    tags := Xi;
    for f in fseq do
      fparts := IsDivisibleBy(t^2 - phi,f) select sparts else parts;
      deg := Degree(f);
      for n := 0 to d-1 do
        dimleft := d-n;
        if deg le dimleft then
          for i := 1 to dimleft div deg do
            pol_parts := ((n ne 0) select prevXi[n] else [ {@ @}]);
            taglist := ((n ne 0) select prevTags[n] else [ false ]);
            for j := 1 to #pol_parts do
              pol_part := pol_parts[j];
              tagged := taglist[j];
              for mu in fparts[i] do

                accept := true;
                newtag := false;
                if deg eq 1 then
                  if tagged then
                    newtag := true;
                  else
                    otype, tag := isOtype(mu);
                    if otype then
                      if tag then newtag := true; else accept := false; end if;
                    end if;
                  end if;
                end if;

                if accept then
                  Append(~Xi[n+deg*i], Include(pol_part,<f,mu>));
                  Append(~tags[n+deg*i], newtag);
                end if;

              end for;
            end for;
          end for;
        end if;
      end for;
      prevXi := Xi;
      prevTags := tags;
    end for;
    inv cat:= [ <phi,xi> : xi in Xi[d] ];
  end for;
  return inv;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic RepresentativeMatrixCSp(inv :: Tup) -> GrpMatElt
{A representative of the conjugacy class with invariant inv
 in the conformal symplectic group}
  phi, Xi := Explode(inv);
  F := Parent(phi);
  q := #F;
  t := PolynomialRing(F).1;
  X := ZeroMatrix(F, 0, 0);
  for polpart in Xi do
    f, plist := Explode(polpart);

    if IsDivisibleBy(t^2 - phi, f) then
      for term in plist do
        e, m := Explode(term);

        if IsOdd(e) then
          assert IsEven(m);
          for i := 1 to m div 2 do
            X := centralJoin(X,type3CompanionS(phi,f,e));
          end for;

        else
         flag := Sign(e) gt 0;
         c := Abs(e) div 2;
         if Degree(f) eq 1 then
           lambda := - Coefficient(f,0);
           X := ((q mod 4 eq 1) or (m mod 4 eq 0))
             select centralJoin(X,type3CompanionO(lambda,c,flag))
               else centralJoin(X,type3CompanionO(lambda,c,not flag));
           for i := 2 to m do
             X := centralJoin(X,type3CompanionO(lambda,c,true));
           end for;
         else
           X := (IsOdd(m) and (q mod 4 eq 1))
             select centralJoin(X,type3CompanionOext(phi,c,not flag))
               else centralJoin(X,type3CompanionOext(phi,c,flag));
           for i := 2 to m do
             X := centralJoin(X,type3CompanionOext(phi,c,true));
           end for;
         end if;
       end if;
     end for;

   elif IsIrreducible(f) then
     for mu in plist do
       e, m := Explode(mu);
       for i := 1 to m do X := centralJoin(X,type2Companion(phi,f,e)); end for;
     end for;

   else
     h := Factorisation(f)[1][1];
     assert f eq h*Factorisation(f)[2][1];
     for mu in plist do
       e, m := Explode(mu);
       for i := 1 to m do X := centralJoin(X,type1Companion(phi,h^e)); end for;
     end for;
   end if;
 end for;
 return ConformalSymplecticGroup(Nrows(X),F)!X;
end intrinsic;
//------------------------------------------------------------------------------

A_fn := function(phi, f, d, m)
  q := #BaseRing(f);
  deg := Degree(f);
  t := Parent(f).1;
  if IsIrreducible(f) then
    if IsDivisibleBy(t^2 - phi, f) then
      if IsOdd(d) then val := OrderSp(m,q^deg);
      else
        if IsOdd(m) then val := OrderGO(m,q^deg);
        elif (d lt 0) then val := OrderGOMinus(m,q^deg);
        else val := OrderGOPlus(m,q^deg); end if;
      end if;
    else val := OrderGU(m,q^(deg div 2)); end if;
  else val := OrderGL(m,q^(deg div 2));  end if;
  return val;
end function;

kappa := function(phi, plist, f)
  t := Parent(f).1;
  val := 0;
  for mu in plist do
    d, m := Explode(mu);
    val +:= (Abs(d)-1)*m^2;
    if IsDivisibleBy(t^2-phi,f) and IsEven(d) then val +:= m; end if;
  end for;
  r := #plist;
  for i := 1 to r-1 do
    d := Abs(plist[i][1]);
    m := plist[i][2];
    for j := i+1 to r do val +:= 2*d*m*plist[j][2]; end for;
  end for;
  val *:= Degree(f);
  assert IsEven(val);
  return val div 2;
end function;

otype := function(inv)
  phi, xi := Explode(inv);
  F := Parent(phi);
  t := PolynomialRing(F).1;
  q := #F;
  tp := false;
  for pol_part in xi do
    f, mu := Explode(pol_part);
    if IsDivisibleBy(t^2 - phi,f) and Degree(f) eq 1 then
      for lambda in mu do
        e, m := Explode(lambda);
        tp or:= IsEven(e) and IsOdd(m);
      end for;
    end if;
  end for;
  return tp select (q - 1) div 2 else q - 1;
end function;

B_fn := function(phi,pol_part)
  f, partn := Explode(pol_part);
  q := #BaseRing(f);
  return q^kappa(phi,partn,f) * &*[A_fn(phi,f,mu[1],mu[2]) : mu in partn];
end function;


//==============================================================================
intrinsic CentralizerOrderCSp(inv :: Tup) -> RngIntElt
{The order of the centralizer of any element in the symplectic
 group whose conjugacy invariant is inv}
  phi, xi := Explode(inv);
  return  otype(inv) * &*[ B_fn(phi,pol_part) : pol_part in xi ];
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic CentraliserOrderCSp(inv :: Tup) -> RngIntElt
{The order of the centraliser of any element in the symplectic
 group whose conjugacy invariant is inv}
  phi, xi := Explode(inv);
  return  otype(inv) * &*[ B_fn(phi,pol_part) : pol_part in xi ];
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassRepresentativesCSp(d :: RngIntElt, q :: RngIntElt)
  -> SeqEnum, SeqEnum
{Representatives for the conjugacy classes of the conformal
  symplectic group CSp(d,q). The second return value is the
  sequence of class invariants.}
  require IsOdd(q) : "q must be odd";
  invar := ClassInvariantsCSp(d,q);
  return [CSp(d,q) | RepresentativeMatrixCSp(mu) : mu in invar], invar;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassesCSp(d :: RngIntElt,q :: RngIntElt) -> SeqEnum
{The conjugacy classes of CSp(d,q)}
  ord := OrderCSp(d,q);
  return Sort([car<Integers(),Integers(),CSp(d,q)>|
    < Order(M), ord div CentraliserOrderCSp(mu), M > :
        mu in ClassInvariantsCSp(d,q) | true
        where M is RepresentativeMatrixCSp(mu) ]);
end intrinsic;
//------------------------------------------------------------------------------

attachSign1 := function(D,g,f,e,m)
  F := BaseRing(g);
  lambda := Evaluate(f,0);
  A := g + ScalarMatrix(F,Nrows(g),lambda);
  D0 := sub< D | [v*A : v in Basis(D)] >;
  E := [v : v in ExtendBasis(D0,D) | v notin D0];
  delta := (g - lambda^2*g^-1)^(e-1);
  B := Matrix(F,#E,#E,[DotProduct(D!(u*delta),v) : u,v in E ]);
  assert Determinant(B) ne 0;
  sq, _ := IsSquare(Determinant(B));

  if (#F mod 4 eq 3) and (m mod 4 eq 2) then sq := not sq; end if;
  return sq select e else -e;
end function;

attachSign2 := function(D,g,f,e,m)
  F := BaseRing(g);
  phi := -Evaluate(f,0);
  A := g*g - ScalarMatrix(F,Nrows(g),phi);
  D0 := sub< D | [v*A : v in Basis(D)] >;
  L := [v : v in ExtendBasis(D0,D) | v notin D0];
  L2 := [L[i] : i in [1..#L by 2]];
  delta := (g - phi*g^-1)^(e-1);
  E<tau> := ext< F | f >;

dotprod := function(u,v)
  w := D!(u*delta);
  a := DotProduct(w,v);
  b := phi^-1*DotProduct(w,D!(v*g));
  return E![a,b];
end function;

  B := Matrix(E,#L2,#L2,[dotprod(u,v) : u,v in L2 ]);
  assert Determinant(B) ne 0;
  sq, _ := IsSquare(Determinant(B));

  return sq select e else -e;
end function;


//==============================================================================
intrinsic ConjugacyInvariantCSp(g :: GrpMatElt) -> SetIndx[Tup]
{The conjugacy class invariant of the conformal symplectic
 matrix g}
  F := BaseRing(g);
  t := PolynomialRing(F).1;
  n := Nrows(g);
  std := StandardAlternatingForm(n,F);
  stdg := g*std*Transpose(g);
  phi := stdg[1,n];
  require stdg eq phi*std :
    "matrix is not in the standard conformal symplectic group";
  _, T, pFact := PrimaryRationalForm(g);
  V := SymplecticSpace(std);
  pols, parts, bases := primaryPhiParts(phi,pFact);
  inv := {@ @};

  scanning := true;
  invert := false;

  for i := 1 to #pols do
    plist := convert(parts[i]);
    f := pols[i];
    if IsDivisibleBy(t^2 - phi, f) then
      base := bases[i];

      gg := restriction(g,[T[j] : j in base]);
      d := #base;
      B := Matrix(F,d,d, [DotProduct(V!T[r],V!T[s]) : r, s in base]);
      W := SymplecticSpace(B);
      D := homocyclicSplit(gg,W);

      for j := 1 to #plist do
        e, m := Explode(plist[j]);
        if IsEven(e) then
          if Degree(f) eq 1 then
            e := attachSign1(D[j],gg,f,e,m);

            if IsOdd(m) then
              if scanning then scanning := false; invert := e lt 0; end if;
              if invert then e := -e; end if;
            end if;
          else
            e := attachSign2(D[j],gg,f,e,m);
          end if;
          plist[j] := <e,m>;
        end if;
      end for;
    end if;
    Include(~inv, <f, plist>);
  end for;
  return <phi,inv>;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ExtendedSp(n :: RngIntElt, q :: RngIntElt, m :: RngIntElt)
   -> GrpMat
{The subgroup of CSp(n,q) that contains Sp(n,q) as a subgroup
 of index m}
  require IsEven(n) : "invalid dimension---should be even";
  require m gt 0 : "the index should be positive";
  divides, r := IsDivisibleBy(q - 1, m);
  require divides : "the index should divide q - 1";
  if m eq 1 then G := Sp(n,q);
  elif m eq q - 1 then G := CSp(n,q);
  else
    F := GF(q);
    xi := PrimitiveElement(F)^r;
    A := IdentityMatrix(F,n);
    for i := 1 to n div 2 do A[i,i] := xi; end for;
    G := sub< CSp(n,q) | Sp(n,q), A >;
    G`Order := OrderSp(n,q) * m;
  end if;
  return G;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic IndexOfSp(G :: GrpMat) -> RngIntElt
{The index of the symplectic group in G}
  F := BaseRing(G);
  require ISA(Type(F), FldFin) : "the base field should be finite";
  require IsSymplecticGroup(G) : "G should contain the symplectic
    group and be a subgroup of the conformal symplectic group";
  n := Dimension(G);
  std := StandardAlternatingForm(n,F);
  ndx := [];
  for g in Generators(G) do
    stdg := g*std*Transpose(g);
    phi := stdg[1,n];
    require stdg eq phi*std : "G should be a subgroup of the
      standard conformal symplectic group";
    Append(~ndx, Order(phi));
  end for;
  return LCM(ndx);
end intrinsic;
//------------------------------------------------------------------------------

extendByScalar := function(inv,zeta)
  F := Parent(zeta);
  P<t> := PolynomialRing(F);
  if zeta eq F!1 then return < F!1, inv >; end if;
  newinv := {@ @};
  for polpart in inv do
    f, mu := Explode(polpart);
    ff := zeta^Degree(f)*Evaluate(f,zeta^-1*t);
    Include(~newinv,<ff,mu>);
  end for;
  return newinv;
end function;


//==============================================================================
intrinsic ClassInvariantsExtSp(d :: RngIntElt, q :: RngIntElt, m :: RngIntElt)
  -> SeqEnum
{The conjugacy class invariants for the extended symplectic
  group ExtendedSp(d,q,m) of index m, q odd}
  if m eq q - 1 then return ClassInvariantsCSp(d,q); end if;
  if m eq 1 then return ClassInvariantsSp(d,q); end if;
  require IsOdd(q) : "q must be odd";
  require m gt 0 : "the index should be positive";
  divides, r := IsDivisibleBy(q - 1, m);
  require divides : "the index should divide q - 1";

  F := GF(q);
  xi := PrimitiveElement(F);
  if IsEven(r) then
    s := r div 2;
    X := ClassInvariantsSp(d,q);
    invList := [];
    for i := 1 to m do
      zeta := xi^(s*i);
      for inv in X do
        Append(~invList, < zeta^2,extendByScalar(inv,zeta)>);
      end for;
    end for;
  else
    mgrp := { xi^(r*i) : i in [1..m] };
    invList := [ nu : nu in ClassInvariantsCSp(d,q) | nu[1] in mgrp ];
  end if;
  return invList;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassRepresentativesExtSp(d :: RngIntElt, q :: RngIntElt, m :: RngIntElt)
  -> SeqEnum, SeqEnum
{Representatives for the conjugacy classes of the extended
  symplectic group ExtendedSp(d,q,m) of index m. The second
  return value is the sequence of class invariants.}
  require IsOdd(q) : "q must be odd";
  if m eq q - 1 then return ClassRepresentativesCSp(d,q); end if;
  if m eq 1 then return ClassRepresentativesSp(d,q); end if;
  invar := ClassInvariantsExtSp(d,q,m);
  return [ExtendedSp(d,q,m) | RepresentativeMatrixCSp(mu) : mu in invar], invar;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassesExtSp(d :: RngIntElt,q :: RngIntElt, m :: RngIntElt) -> SeqEnum
{The conjugacy classes of ExtendedSp(d,q,m)}
  if m eq q - 1 then return ClassesCSp(d,q); end if;
  if m eq 1 then return ClassesSp(d,q); end if;
  require IsOdd(q) : "q must be odd";
  require m gt 0 : "the index should be positive";
  divides, r := IsDivisibleBy(q - 1, m);
  require divides : "the index should divide q - 1";

  xi := PrimitiveElement(GF(q));
  cc := [car<Integers(),Integers(),ExtendedSp(d,q,m)>| ];
  if IsEven(r) then
    alpha := xi^(r div 2);
    X := ClassInvariantsSp(d,q);
    ord := OrderSp(d,q);
    invList := [];
    for i := 1 to m do
      zeta := alpha^i;
      for inv in X do
        mu := extendByScalar(inv,zeta);
        g := RepresentativeMatrixCSp(<zeta^2,mu>);
        Append(~cc, < Order(g), ord div CentraliserOrderSp(inv), g >);
      end for;
    end for;
  else
    ord := OrderCSp(d,q);
    mgrp := { xi^(r*i) : i in [1..m] };
    X := ClassInvariantsCSp(d,q);
    for inv in X do
      if inv[1] in mgrp then
        g := RepresentativeMatrixCSp(inv);
        Append(~cc, < Order(g), ord div CentraliserOrderCSp(inv), g >);
      end if;
    end for;
  end if;
  return Sort(cc);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic InternalClassesExtendedSp(G :: GrpMat) -> BoolElt
{Internal function: attempt to assign the conjugacy classes of
 the extended symplectic group.  Return true if successful}
  try
    m := IndexOfSp( G );
  catch e
    return false;
  end try;

  if assigned G`Classes then return true; end if;
  d := Degree(G);
  q := #BaseRing(G);
  if IsOdd( q ) then
    vprint Classes: "assigning symplectic classes";
    G`Classes := ClassesExtSp(d,q,m);
    return true;
  end if;
  return false;
end intrinsic;
//------------------------------------------------------------------------------

/*
intrinsic InternalClassesExtendedSp(G::GrpMat) -> BoolElt
{Attempt to assign the conjugacy classes of CSp(d,q). Return true if successful}
  try
    m := IndexOfSp(G);
  catch e
    return false;
  end try;

  // Currently only for CSp and Sp over fields of odd characteristic
  d := Degree(G); 
  q := #BaseRing(G);  
  if IsOdd(q) then
    if assigned G`Classes then return true; end if;
    if m eq q-1 then
        vprint Classes: "assigning CSp classes";
      G`Classes := ClassesCSp(d,q);
      return true;
    elif m eq 1 then
        vprint Classes: "assigning Sp classes";
      G`Classes := ClassesSp(d,q);
      return true;
    end if;
  end if;
  
  return false;    
end intrinsic;
*/

