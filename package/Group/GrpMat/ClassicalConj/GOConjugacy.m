freeze;

// Title: Conjugacy Classes in Finite Orthogonal Groups
// Full documentation in the file: GOConjugacy.pdf
// Author: Don Taylor
// Project start: December 2015
// ====================================================
/*
    $Id: GOConjugacy.m 52234 2016-03-18 02:36:06Z don $
*/
//==============================================================================
import "common.m" : convert, allPartitions, primaryParts, stdJordanBlock,
   centralJoin, getSubIndices, restriction, homocyclicSplit, type1Companion;

isSignedPartition := func< pi |
  forall{ lambda : lambda in pi | IsOdd(lambda[1]) or (IsEven(lambda[2]) and lambda[1] gt 0) } >;

addSignsO := function(plist)
  slist := [];
  for pi in plist do
    if forall{ mu : mu in pi | IsOdd(mu[1]) or IsEven(mu[2])} then
      ndx := { i : i in [1..#pi] | IsOdd(pi[i][1]) };
      for S in Subsets(ndx) do
        lambda := pi;
        for i in S do
          mu := pi[i];
          lambda[i] := < -mu[1],mu[2] >;
        end for;
        Append(~slist,lambda);
      end for;
    end if;
  end for;
  return slist;
end function;

signedPartitionsO := func< d | [ addSignsO(plist) : plist in allPartitions(d) ] >;

invToWitt := function(q,inv)
  qmod4 := q mod 4 eq 1;

  W := AbelianGroup(GrpAb,qmod4 select [2,2] else [4]);
  w := W!0;
  omega := qmod4 select W.1 + W.2 else 2*W.1;
  for pol_part in inv do
    f, lambda := Explode(pol_part);
    d := Degree(f);
    if IsIrreducible(f) then
      for mu in lambda do
        e, m := Explode(mu);
        if d eq 1 then

          if IsEven(m) then
            if e lt 0 then w +:= omega; end if;
          else

            if e gt 0 then w +:= W.1;
            else w +:= qmod4 select W.2 else 3*W.1;
            end if;
          end if;
        else
          w +:= e*m*omega;
        end if;
      end for;
    end if;
  end for;
  return w;
end function;

theSign := function(q,inv)
  w := invToWitt(q,inv);
  W := Parent(w);
  return w in {W!0,W.1} select 1 else -1;
end function;

classInvariantsO := function(d, q)
  error if IsEven(q), "q must be odd";
  pols := &cat[ StarIrreduciblePolynomials(GF(q),i) : i in [1..d] ];
  parts := allPartitions(d);
  sparts := signedPartitionsO(d);
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
end function;


//==============================================================================
intrinsic ClassInvariantsGO(d :: RngIntElt, q :: RngIntElt) -> SeqEnum
{The conjugacy class invariants for the orthogonal group
 GO(d,q)}
  require IsOdd(d) : "d should be odd";
  return [ xi : xi in classInvariantsO(d,q) | theSign(q,xi) eq 1 ];
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassInvariantsGOPlus(d :: RngIntElt, q :: RngIntElt) -> SeqEnum
{The conjugacy class invariants for the orthogonal group
 GOPlus(d,q)}
  require IsEven(d) : "d should be even";
  return [ xi : xi in classInvariantsO(d,q) | theSign(q,xi) eq 1 ];
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassInvariantsGOMinus(d :: RngIntElt, q :: RngIntElt) -> SeqEnum
{The conjugacy class invariants for the orthogonal group
 GOMinus(d,q)}
  require IsEven(d) : "d should be even";
  return [ xi : xi in classInvariantsO(d,q) | theSign(q,xi) eq -1 ];
end intrinsic;
//------------------------------------------------------------------------------

type2CompanionEven := function(f,e);
  assert IsEven(e);
  r := e div 2;
  n := r*Degree(f);
  F := BaseRing(f);
  A := CompanionMatrix(f^r);
  L := StandardSymmetricForm(n,F);
  S := ZeroMatrix(F,n,n);
  S[n-1,n] := 1; S[n,n-1] := -1;
  AL := Transpose(A^-1)*L;
  return BlockMatrix(2,2,[A,S*AL,0,L*AL]);
end function;

type2CompanionOdd := function(f,e);
  assert IsOdd(e);
  k := BaseRing(f);
  f := f^e;
  n := Degree(f);
  delta := Nonsquare(k);
  if n eq 2 then
    a1 := Coefficient(f,1);
    d := Sqrt(delta*(a1^2 - 4));
    return Matrix(2,2, [k| -a1/2, d/(2*delta), d/2, -a1/2]);
  end if;

  r := n div 2 - 1;
  as := Coefficients(f);
  tau := &+[ as[r-2*i+1] : i in [0..r div 2] ];
  nu := as[r+2] + 2 * &+[ as[r+2-2*i] : i in [1..(r+1) div 2] ];
  b0 := (nu+2*tau)^-1;
  gamma := (nu - 2*tau)*b0;
  bs := [ (i gt 2) select as[i]*b0 + Self(i-2) else
        (i eq 2) select as[2]*b0 else b0 : i in [1..r]];

  C := ZeroMatrix(k,n,n);
  for i := 1 to r-1 do C[i,i+1] := 1; end for;
  C[r,n] := 1/b0;
  C[r+1,r+1] := 1;
  C[r+1,n] := (-1)^r/(2*b0);
  C[r+2,r+2] := -1;
  C[r+2,n] := -(-1)^r*gamma/(2*b0);
  for i := 1 to r do C[r+3,i] := bs[i]; end for;
  C[r+3,r+1] := -(-1)^r;
  C[r+3,r+2] := (-1)^r;
  C[r+3,n] := -tau;
  for i := 2 to r do
    C[r+2+i,r+1+i] := 1;
    C[r+2+i,n] := -bs[r+2-i]/b0;
  end for;

  assert exists(a,b){<x,y> : x,y in k | x ne 0 and y ne 0 and x*x - y*y*gamma eq 2};
  c := Sqrt(delta/gamma);
  T := IdentityMatrix(k,n);
  T[r+1,r+1] := a; T[r+1,r+2] := b;
  T[r+2,r+1] := b*c*gamma; T[r+2,r+2] := a*c;
  return T*C*T^-1, C;
end function;

type3CompanionS := func< a0, e | DiagonalJoin(B, B^-1) where
    B is stdJordanBlock(e, -a0) >;

type3CompanionO := function(a0, e)
  assert IsOdd(e);
  c := (Abs(e) - 1) div 2;
  F := Parent( a0 );
  if c eq 0 then return Matrix(F,1,1, [-a0]); end if;
  b := F!1;
  B := stdJordanBlock(c,b);
  X := -a0*DiagonalJoin(<B,Matrix(1,1,[b]),B^-1>);
  a := a0/2;
  if (e lt 0) then
    b := Nonsquare(F);
    a *:= b;
  end if;
  X[c,c+1] := 1;
  for i := 1 to c do
    X[c,c+1+i] := IsOdd(i) select a else -a;
    X[c+1,c+1+i] := IsOdd(i) select -b else b;
  end for;
  return X;
end function;

wittSum := function(F,d1,d2)
  if d1 eq 0 then d := d2;
  elif d2 eq 0 then d := d1;
  elif #F mod 4 eq 1 then
    d := case< [d1,d2] |
      [1,1]: 0, [-1,-1]: 0, [1,-1]: 2, [-1,1]: 2,
      [1,2]: -1, [2,1]: -1, [-1,2]: 1, [2,-1]: 1,
      [2,2]: 0, default:  "error">;
  else
    d := case< [d1,d2] |
      [1,1]: 2, [-1,-1]: 2, [1,-1]: 0, [-1,1]: 0,
      [1,2]: -1, [2,1]: -1, [-1,2]: 1, [2,-1]: 1,
      [2,2]: 0, default: "error">;
  end if;
  return d;
end function;

wittTransform := function(F,d1,d2)
  if d1 eq 0 then return IdentityMatrix(F,Abs(d2)); end if;
  if d2 eq 0 then return IdentityMatrix(F,Abs(d1)); end if;
  if #F mod 4 eq 1 then
    i := Sqrt(-F!1);
    delta := Nonsquare(F);
    X := case< [d1,d2] |
      [1,1]: Matrix(F,2,2,[F| 1,i,1/2,-i/2]),
      [-1,-1]: Matrix(F,2,2,[F| 1,i,1/(2*delta),-i/(2*delta)]),
      [1,-1]: Matrix(F,2,2,[F| 1,0,0,i]),
      [-1,1]: Matrix(F,2,2,[F| 0,1,i,0]),
      [1,2]: Matrix(F,3,3,[F| 1,i,0, 0,0,i, 1/2,-i/2,0]),
      [2,1]: Matrix(F,3,3,[F| 1,0,i, 0,i,0, 1/2,0,-i/2]),
      [-1,2]: Matrix(F,3,3,[F|1,0,1, 0,1,0, 1/(2*delta),0,-1/(2*delta)]),
      [2,-1]: Matrix(F,3,3,[F| 0,1,1, 1,0,0, 0,-1/(2*delta),1/(2*delta)]),
      [2,2]: Matrix(F,4,4,[F| 1,0,i,0, 0,1,0,i, 0,-1/(2*delta),0,i/(2*delta), 1/2,0,-i/2,0]),
      default:  "error">;
  else
    assert exists(x,y){ <x,y> : x,y in F | x ne 0 and y ne 0 and x*x + y*y eq -1 };
    X := case< [d1,d2] |
      [1,1]: IdentityMatrix(F,2),
      [-1,-1]: Matrix(F,2,2,[F| x,y, y,-x]),
      [1,-1]: Matrix(F,2,2,[F| 1,1,1/2,-1/2]),
      [-1,1]: Matrix(F,2,2,[F| 1,1,-1/2,1/2]),
      [1,2]: Matrix(F,3,3,[F| x,y,1, y,-x,0, -x/2,-y/2,1/2]),
      [2,1]: Matrix(F,3,3,[F| x,y,1, y,-x,0, -x/2,-y/2,1/2]),
      [-1,2]: Matrix(F,3,3,[F|1,1,0, 0,0,1, -1/2,1/2,0]),
      [2,-1]: Matrix(F,3,3,[F| 1,0,1, 0,1,0, 1/2,0,-1/2]),
      [2,2]: Matrix(F,4,4,[F| x,y,1,0, y,-x,0,1, -y/2,x/2,0,1/2, -x/2,-y/2,1/2,0]),
      default:  "error">;
  end if;
  return X;
end function;

almostADPerm := function(m1,m2,n1,n2)
  X := [ i : i in [1..m1] ] cat [ 2*m1+n1+i : i in [1..m2] ] cat
      [ m1+i : i in [1..n1] ] cat [ 2*m1+n1+m2+i : i in [1..n2]] cat
      [ 2*m1+n1+m2+n2+i : i in [1..m2] ] cat [ m1+n1+i: i in [1..m1] ];
  return Sym(2*m1+n1+2*m2+n2)!X;
end function;

oTransform := func< F,mA,mB,dA,dB | DiagonalJoin(<Z,wittTransform(F,dA,dB),Z>)
    where Z is IdentityMatrix(F,mA+mB)>;

orthogonalJoin := function(A,B,dA,dB : Form := false)
  rA := Nrows(A); rB := Nrows(B);
  if rA eq 0 then return B; end if;
  if rB eq 0 then return A; end if;
  if dA eq 0 then return centralJoin(A,B); end if;
  if dB eq 0 then return centralJoin(B,A); end if;
  nA := Abs(dA); nB := Abs(dB);
  mA := (rA - nA) div 2; mB := (rB - nB) div 2;
  F := BaseRing(A);
  pi := almostADPerm(mA,mB,nA,nB);
  C0 := DiagonalJoin(A,B);
  C := Matrix(F,n,n, [C0[i^pi,j^pi] : i,j in [1..n]]) where n is rA+rB;
  X := oTransform(F,mA,mB,dA,dB);
  return (Form) select X*C*Transpose(X) else X*C*X^-1;
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
  F := BaseRing(f);
  X := ZeroMatrix( F, 0, 0 );
  wCode := 0;
  for mu in plist do
    e, m := Explode(mu);
    d := 2*(e mod 2);
    t2c := IsEven(e) select type2CompanionEven else type2CompanionOdd;
    for i := 1 to m do
      X := orthogonalJoin(X,t2c(f,e),wCode,d);
      wCode := wittSum(F,wCode,d);
    end for;
  end for;
  return X,wCode;
end function;

type3Matrix := function(f, plist)
  assert Degree(f) eq 1;
  assert isSignedPartition(plist);
  a0 := Coefficient(f,0);
  F := BaseRing(f);
  q := #F;
  X := ZeroMatrix( F, 0, 0 );
  wCode := 0;
  for mu in plist do
    e, m := Explode(mu);

    if IsEven( e ) then
      for i := 1 to (m div 2) do
        X := centralJoin( type3CompanionS(a0,e), X);
      end for;
    else

      ae := Abs(e);
      r := (m - 1) div 2;
      mPlus := type3CompanionO(a0,ae);
      mMinus := type3CompanionO(a0,-ae);

      Y := (q mod 4 eq 1) select orthogonalJoin(mPlus,mPlus,1,1)
           else orthogonalJoin(mPlus,mMinus,1,-1);
      for i := 1 to r do X := centralJoin(Y,X); end for;
      if IsOdd(m) then
        if e gt 0 then
          X := orthogonalJoin(X,mPlus,wCode,1);
          wCode := wittSum(F,wCode,1);
        else
          X := orthogonalJoin(X,mMinus,wCode,-1);
          wCode := wittSum(F,wCode,-1);
        end if;
      else
        if e gt 0 then
          X := centralJoin(Y,X);
        else
          Y := (q mod 4 eq 3) select orthogonalJoin(mPlus,mPlus,1,1)
               else orthogonalJoin(mPlus,mMinus,1,-1);
          X := orthogonalJoin(X,Y,wCode,2);
          wCode := wittSum(F,wCode,2);
        end if;
      end if;
    end if;
  end for;
  return X,wCode;
end function;


//==============================================================================
intrinsic RepresentativeMatrixO( inv::SetIndx[Tup] ) -> GrpMatElt
{A representative of the conjugacy class in the orthogonal
 group with invariant inv}
  F := BaseRing(Parent(inv[1][1]));
  X := ZeroMatrix(F,0,0);
  wCode := 0;
  for polpart in inv do
    f, plist := Explode(polpart);
    if (Degree(f) eq 1) then
      Y, d := type3Matrix(f,plist);
      X := orthogonalJoin(X, Y, wCode, d);
      wCode := wittSum(F,wCode,d);
    elif IsIrreducible(f) then
      Y, d := type2Matrix(f, plist);
      X := orthogonalJoin(X, Y, wCode, d);
      wCode := wittSum(F,wCode,d);
    else
      X := centralJoin(type1Matrix(f, plist), X);
    end if;
  end for;

  n := Nrows(X);
  if IsOdd(n) then
    q := #F;
    assert theSign(q,inv) eq 1;
    r := (n - 1) div 2;
    if (q mod 8) in [1,7] then // 2 is a square
      T := IdentityMatrix(F,n);
      T[r+1,r+1] := Sqrt(F!2);
    else
      delta := Nonsquare(F);
      a := Sqrt(2*delta);
      S := ScalarMatrix(r,delta);
      T := DiagonalJoin(<S,Matrix(1,1,[a]),IdentityMatrix(F,r)>);
    end if;
    X := T^-1*X*T;
  end if;

  return GL(n,F)!X;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassRepresentativesGO(d::RngIntElt, q::RngIntElt)
   -> SeqEnum, SeqEnum
{ Representatives for the conjugacy classes of the orthogonal
  group GO(d,q). The second return value is the sequence of
  class invariants. }
  require IsOdd(q) : "q must be odd";
  invar := ClassInvariantsGO(d,q);
  return [GO(d,q) | RepresentativeMatrixO(mu) : mu in invar], invar;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassRepresentativesGOPlus(d::RngIntElt, q::RngIntElt)
   -> SeqEnum, SeqEnum
{ Representatives for the conjugacy classes of the orthogonal
  group GOPlus(d,q). The second return value is the sequence
  of class invariants. }
  require IsOdd(q) : "q must be odd";
  invar := ClassInvariantsGOPlus(d,q);
  return [GOPlus(d,q) | RepresentativeMatrixO(mu) : mu in invar], invar;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassRepresentativesGOMinus(d::RngIntElt, q::RngIntElt)
   -> SeqEnum, SeqEnum
{ Representatives for the conjugacy classes of the orthogonal
  group GOMinus(d,q). The second return value is the sequence
  of class invariants. }
  require IsOdd(q) : "q must be odd";
  invar := ClassInvariantsGOMinus(d,q);
  return [GOMinus(d,q) | RepresentativeMatrixO(mu) : mu in invar], invar;
end intrinsic;
//------------------------------------------------------------------------------

attachSign := function(D,g,f,mu)
  F := BaseRing(g);
  e, m := Explode(mu);
  n := e*m*Degree(f);
  B := Matrix(F,n,n,[DotProduct(u,v) : u,v in Basis(D) ]);
  assert Determinant(B) ne 0;
  disc, _ := IsSquare(Determinant(B));

  if ((#F mod 4 eq 3) and (n mod 4 in {2,3})) then disc := not disc; end if;
  return disc select mu else < -e,m>;
end function;


//==============================================================================
intrinsic ConjugacyInvariantO(g :: GrpMatElt : Minus := false) -> SetIndx[Tup]
{ The conjugacy class invariant of the orthogonal matrix g }
  F := BaseRing(g);
  n := Nrows(g);
  Q := StandardQuadraticForm(n,F : Minus := Minus, Variant := "Revised");
  if IsOdd(n) then
    error if Minus, "Minus option not available in odd dimensions";

    Q := 2*Q;
  end if;
  V := QuadraticSpace(Q);
  require IsIsometry(V,g) :
    "matrix is not in the standard orthogonal group";
  _, T, pFact := PrimaryRationalForm(g);
  pols, parts, bases := primaryParts(pFact);
  inv := {@ @};
  for i := 1 to #pols do
    f := pols[i];
    plist := convert(parts[i]);
    if Degree(f) eq 1 then
      base := bases[i];

      g_ := restriction(g,[T[j] : j in base]);
      d := #base;
      Q := ZeroMatrix(F,d,d);
      for b := 1 to d-1 do
        Q[b,b] := QuadraticNorm(V!T[base[b]]);
        for c := b+1 to d do
          Q[b,c] := DotProduct(V!T[base[b]],V!T[base[c]]);
        end for;
      end for;
      Q[d,d] := QuadraticNorm(V!T[base[d]]);
      W := QuadraticSpace(Q);
      D := homocyclicSplit(g_,W);
      for j := 1 to #plist do
        if IsOdd(plist[j][1]) then
          plist[j] := attachSign(D[j],g_,f,plist[j]);
        end if;
      end for;
    end if;
    Include(~inv, <f, plist> );
  end for;
  return inv;
end intrinsic;
//------------------------------------------------------------------------------

A_fn := function(f, e, m, q)
  d := Degree(f);
  if IsIrreducible(f) then
    if d eq 1 then
      if IsEven(e) then val := OrderSp(m,q);
      else
        if IsOdd(m) then val := OrderGO(m,q);
        elif (e lt 0) then val := OrderGOMinus(m,q);
        else val := OrderGOPlus(m,q);
        end if;
      end if;
    else val := OrderGU(m,q^(d div 2));
    end if;
  else val := OrderGL(m,q^(d div 2));
  end if;
  return val;
end function;

kappa := function(plist, d)
  val := 0;
  for mu in plist do
    e, m := Explode(mu);
    val +:= (Abs(e)-1)*m^2;
    if d eq 1 and IsEven(e) then val -:= m; end if;
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
intrinsic CentraliserOrderO( inv :: SetIndx[Tup] ) -> RngIntElt
{The order of the centraliser of any element in the orthogonal
 group whose conjugacy invariant is inv}
 return &*[ B_fn(pol_part) : pol_part in inv ];
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassesGO(d :: RngIntElt, q :: RngIntElt) -> SeqEnum
{The conjugacy classes of GO(d,q)}
  ord := OrderGO(d,q);
  return Sort([car<Integers(),Integers(),GO(d,q)> |
    < Order(M), ord div CentraliserOrderO(mu), M > :
        mu in ClassInvariantsGO(d,q) | true
        where M is RepresentativeMatrixO(mu) ]);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassesGOPlus(d :: RngIntElt, q :: RngIntElt) -> SeqEnum
{The conjugacy classes of GOPlus(d,q)}
  ord := OrderGOPlus(d,q);
  return Sort([car<Integers(),Integers(),GOPlus(d,q)> |
    < Order(M), ord div CentraliserOrderO(mu), M > :
        mu in ClassInvariantsGOPlus(d,q) | true
        where M is RepresentativeMatrixO(mu) ]);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ClassesGOMinus(d :: RngIntElt, q :: RngIntElt) -> SeqEnum
{The conjugacy classes of GOMinus(d,q)}
  ord := OrderGOMinus(d,q);
  return Sort([car<Integers(),Integers(),GOMinus(d,q)> |
    < Order(M), ord div CentraliserOrderO(mu), M > :
        mu in ClassInvariantsGOMinus(d,q) | true
        where M is RepresentativeMatrixO(mu) ]);
end intrinsic;
//------------------------------------------------------------------------------

