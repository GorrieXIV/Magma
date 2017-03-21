freeze;

/************************************************************************\
*  Minimisation of Genus One Models over Q (of degrees n = 2,3,4 and 5)  *
*  Author: T. Fisher (based on joint work with J. Cremona and M. Stoll)  *
*  Date: 22nd July 2008                                                  *
*  Version for n = 5 is not yet proven to work in all cases              *
*  This file also contains an intrinsic "GenusOneModel" that takes as    *
*    input n and P, and computes a minimal genus one model of degree n   * 
*    for (E,[(n-1)0+P]) where P in E(Q).                                 *
\************************************************************************/

// Tom, April 2010 
//   * converted to use new TransG1 type
//   * added the following (so can delete file "t3minimisation.m")
// intrinsic Minimise(C::RngMPolElt) -> RngMPolElt, Tup
// intrinsic pMinimise(C::RngMPolElt, p::RngIntElt) -> RngMPolElt, AlgMatElt
// intrinsic CubicFromPoint(E::CrvEll, P::PtEll) -> RngMPolElt, MapSch, Pt

declare attributes ModelG1 : GlobalLevel;

declare verbose Minimisation,3;

MC := MonomialCoefficient;
MD := MonomialsOfDegree;
Diag := DiagonalMatrix;
Id := IdentityMatrix;
Char := Characteristic;
Deriv := Derivative;
MAT := func<R,n,Q|Matrix(R,n,n,[Deriv(Deriv(Q,i),j): i,j in [1..n]])>;

function RationalGCD(S)
   R := Universe(S);
   if Type(R) in {RngInt,FldRat} then
     Z := Integers();
     Q := Rationals();
     d := LCM([Z| Denominator(Q!x): x in S | x ne 0]);
     return R!(GCD([Z| x*d : x in S])/d);
   elif ISA(Type(FieldOfFractions(R)), FldFunRat) then
     Q := FieldOfFractions(R);
     Z := Integers(Q);
     d := LCM([Z| Denominator(Q!x) : x in S | x ne 0]);
     return Q!(GCD([Z| x*d : x in S])/d);
   end if;
end function;

PRIM := func<seq|[Integers()|x/d: x in seq] where d is RationalGCD(seq)>;

function MySaturate(mat)
  n := Nrows(mat);
  D := DiagonalMatrix([RationalGCD(Eltseq(mat[i])): i in [1..n]]);
  mat := D^(-1)*mat;
  L := Lattice(mat);
  L1 := PureLattice(L);
  return D*Matrix(Rationals(),n,n,[Coordinates(L1,L!mat[i]): i in [1..n]]);
end function;

function CoeffMatrix(polys,d)
  R := Universe(polys);
  mons := MD(R,d);
  return Matrix(BaseRing(R),#polys,#mons,[MC(f,mon): mon in mons,f in polys]);
end function;  

function GlobalLevel(phi) 
  vprintf Minimisation,1 : "Computing the invariants\n";
  if assigned phi`GlobalLevel then 
    return phi`GlobalLevel;
  end if;
  E := Jacobian(phi);
  _,iso := MinimalModel(E);
  u := IsomorphismData(iso)[4];
// When n = 5, we compensate for the fact "Jacobian" uses the 
// cInvariants (instead of the aInvariants).
  if Degree(phi) eq 5 then u := 6*u; end if;
  ans := Integers(Parent(u))!(1/u);
  if Degree(phi) eq 5 then 
    phi`GlobalLevel := ans;
  end if;
  return ans;
end function;

function LevelDataFldNum(phi, primes)
  assert Degree(phi) ne 5;
  E := Jacobian(phi);
  c4,c6 := Explode(cInvariants(phi));
  data := [];
  for p in primes do 
    v := Floor(Min(Valuation(c4,p)/4, Valuation(c6,p)/6));
    assert v ge 0;
    if v ne 0 and Minimum(p) in {2,3} then
      vprintf Minimisation: "Minimal model of Jacobian at prime of norm %o ... ", Norm(p);
      vtime Minimisation:
      _,iso := MinimalModel(E,p);
      u := IsomorphismData(iso)[4];
      v := -Valuation(u,p);
    end if;
    Append(~data, <p,v>);
  end for;
  return data;
end function;

function LevelDataFldFun(phi : primes:=[])
  R := Integers(BaseRing(phi));
  data := [];
  c4,c6 := Explode(cInvariants(phi));
  if IsEmpty(primes) then
    G4 := GCD(R!c4, R!c6);
    primes := [tup[1] : tup in Factorization(G4)];
  end if;
  if Characteristic(BaseRing(phi)) notin {2,3} then
    for p in primes do
      v := Floor(Min(Valuation(c4,p)/4, Valuation(c6,p)/6));
      Append(~data, <p,v>);
    end for;
  else
    assert Degree(phi) ne 5;
    E := Jacobian(phi);
    for p in primes do 
      v := Floor(Min(Valuation(c4,p)/4, Valuation(c6,p)/6));
      if v gt 0 then
        vprintf Minimisation: "Minimal model of Jacobian at prime of degree %o ... ", Degree(p);
        vtime Minimisation:
        _,iso := MinimalModel(E,p);
        u := IsomorphismData(iso)[4];
        v := -Valuation(u,p);
      end if;
      Append(~data, <p,v>);
    end for;
  end if;
  return data;
end function;

function MultipleRoots(F,m) 
// Find roots of F of multiplicity at least m
  k := BaseRing(F);
  if Char(k) gt m then
    for i in [2..m] do 
      F := GCD([F,Deriv(F)]); 
    end for;
    rts := [rt[1]: rt in Roots(F)];
  else
    rts := [rt[1]: rt in Roots(F)| rt[2] ge m];
  end if;
  return rts;
end function;

function PrettyFactorization(F) 
// Only used for verbose printing 
  P<t> := Parent(F);
  if F eq 0 or Degree(F) eq 0 then return Sprint(F); end if;
  ff := Factorization(F);
  str := "";
  for i in [1..#ff] do
    f := ff[i];
    if (f[1] eq t) or (#ff eq 1 and f[2] eq 1) then 
      str cat:= Sprint(f[1]);
    else
      str cat:= ("(" cat Sprint(f[1]) cat ")");
    end if;
    if f[2] ne 1 then 
      str cat:= ("^" cat Sprint(f[2]));
    end if;
    if i lt #ff then str cat:= "*";end if;
  end for;
  return str;
end function;

/* uses obselete syntax
function PrettySubstitution(tr)
// Only used for verbose printing 
  R<x,z> := PolynomialRing(Rationals(),2);
  S := PolynomialRing(R); y := S.1;
  mons := [x^2,x*z,x^2];
  rr := &+[tr[2][i]*mons[i]: i in [1..3]];
  return "y <- " cat Sprint((1/tr[1])*y + rr);
end function;
*/

//////////////////////////////////////////////////////////////
//                      Case n = 2                          //
//////////////////////////////////////////////////////////////

function _BaseField(phi)
  Z := BaseRing(phi);
  t := Type(Z);
  if t in {RngInt,FldRat} then
    Q := Rationals();
  elif ISA(t, FldAlg) or ISA(t, RngOrd) then
    Q := NumberField(Z);
  else // FldFunRat
    Q := FieldOfFractions(Z);
  end if;
  return Q;
end function;

function RepeatedRoot(F,d);
  assert Degree(F) le d;
  m := Floor(d/2) + 1;
// Finds the m-fold root of F, where the latter is given as
// a univariate polynomial, but viewed as a binary form 
// of degree d. 
  error if F eq 0, "Error: Reduced polynomial should be non-zero.";
  vprintf Minimisation,3 : "F = %o\n",PrettyFactorization(F);
  if Degree(F) le d - m then 
    ans := [1,0];
  else 
    rts := MultipleRoots(F,m);
    if #rts eq 0 then return false,_; end if;
    ans := [rts[1],1];
  end if;
  return true,ans;
end function;

function PolynomialQ1(phi,p,pi:res:=0)
  if res cmpeq 0 then
    k, res := ResidueClassField(p);
  else
    k := Codomain(res);
  end if;
  P := PolynomialRing(k); t := P.1;
  seq := Eltseq(phi);
  if #seq eq 5 then 
    if forall{x : x in seq | res(x) eq 0} then 
      seq := [x/pi: x in seq];
    end if;
    F := &+[res(seq[i+1])*t^(4-i): i in [0..4]];
    dd := 4;
  else   
    assert IsEven(Norm(p));
    l,m,n,a,b,c,d,e := Explode(ChangeUniverse(seq,k));
    dd := 2;
    F := l*t^2 + m*t + n;
    if F eq 0 then F := b*t^2 + d; end if;
    if F eq 0 then 
      F := &+[res(seq[i+4]/2)*t^(4-i): i in [0..4]];
      dd := 4;
    end if;
  end if;
  return F,dd; 
end function;

function SaturateWithCrossTerms(phi)
// Apply y-substitutions to a genus one model of degree 2,
// with the aim of decreasing the level at p = 2.
// Returns (P,Q) with either v(P,Q) = 0, or v(P) > 0 and v(Q) = 1.
  Q := Rationals();  
  _,tr := IsTransformation(2,<1,[0,0,0],Id(Q,2)>);
  while true do
    seq := ChangeUniverse(Eltseq(phi),Integers());
    vP := Minimum([Valuation(seq[i],2): i in [1..3]]);
    vQ := Minimum([Valuation(seq[i],2): i in [4..8]]);
    vPQ := Minimum(2*vP,vQ);
    if vPQ eq 0 and forall{i : i in [1,2,3,5,7] | seq[i] mod 2 eq 0} then 
      _,tr1 := IsTransformation(2,<1,[seq[i] mod 2: i in [4,6,8]],Id(Q,2)>);
    else
      if vPQ lt 2 then break; end if;
      _,tr1 := IsTransformation(2,<1/(2^Floor(vPQ/2)),[0,0,0],Id(Q,2)>); 
    end if;
    phi := tr1*phi;
    tr := tr1*tr;
  end while;
  // vprintf Minimisation,3 : "y-substitution: %o\n",PrettySubstitution(tr);
  return phi,tr,1;
end function;

//////////////////////////////////////////////////////////////
//                      Case n = 3                          //
//////////////////////////////////////////////////////////////

function SingularLocusThree(V,phi);
// Computes the singular locus of a ternary cubic.
// The answer is returned as a subspace of V = k^3.
  F := Equation(phi);
  k := CoefficientRing(phi);
  R<x,y,z> := PolynomialRing(phi);
  error if Discriminant(phi) ne 0,
    "Error: Reduced cubic should be singular.";
  error if cInvariants(phi) ne [0,0],
    "Error: Reduced cubic should be a null-form.";
  error if F eq 0, "Error: Reduced cubic should be non-zero.";
  eqns := [F] cat [Derivative(F,i): i in [1..3]];
  gcd := GCD(eqns);
  if TotalDegree(gcd) gt 0 then
    f := Factorization(gcd)[1][1];
    assert TotalDegree(f) eq 1;
    vprintf Minimisation,3 : "Singular locus is { %o = 0 }.\n",f;
    U := sub<V|V![MC(f,R.i): i in [1..3]]>;
  else
    PP := Points(Scheme(Proj(R),eqns));
    assert #PP eq 1;
    vprintf Minimisation,3 : "Singular locus is { %o }.\n",PP[1];
    mat := Matrix(k,3,1,Eltseq(PP[1]));
    km := KernelMatrix(mat);
    assert Nrows(km) eq 2;
    U := sub<V|[V!km[i]: i in [1..2]]>;
  end if;
  return U;
end function;
  
//////////////////////////////////////////////////////////////
//                      Case n = 4                          //
//////////////////////////////////////////////////////////////

function KernelOfQuadric(V,Q)
// V is a copy of the k-vector space k^d.
// Q is a homogeneous form of degree 2 in k[x_1,..,x_d].
// We compute ker(Q), i.e. the subspace of V where Q and all its
// partial derivatives vanish.
  k := BaseField(V);
  d := Dimension(V);
  mat := MAT(k,Dimension(V),Q);
  km := KernelMatrix(mat);
  n := Nrows(km);
  if Char(k) eq 2 and n ge 1 then
    R := PolynomialRing(k,n);
    subst := [&+[km[i,j]*R.i: i in [1..n]]: j in [1..d]];
    Q1 := Evaluate(Q,subst);
    if Q1 ne 0 then  
      f := SquareRoot(Q1);
      mat1 := Matrix(k,n,1,[MC(f,R.i): i in [1..n]]);
      km := KernelMatrix(mat1)*km;
    end if;
  end if;
  return sub<V|[V!km[i]: i in [1..Nrows(km)]]>;
end function;

function DeterminantPolynomial(phi4,t)
// The polynomial whose roots correspond to singular quadrics
// (with suitable modifications in characteristic 2)
  k := CoefficientRing(phi4);
  P := Parent(t);
  if Char(k) ne 2 then 
    M := [MAT(P,4,Q): Q in Equations(phi4)];
    return Determinant(t*M[1]+M[2]),4;
  else 
    phi2 := DoubleGenusOneModel(phi4);
    l,m,n,a,b,c,d,e := Explode(Eltseq(phi2));
    f := l*t^2 + m*t + n;
    return (f ne 0 select f else b*t^2 + d),2;
  end if;
end function;

function SubDiscriminantThree(Q)
// Find a non-zero 3 by 3 "sub-discriminant" of the quadric Q.
  R := Parent(Q);
  for i in [1..4] do
    x,y,z := Explode([R.j : j in [1..4]| j ne i]);
    a,b,c := Explode([MC(Q,mon): mon in [x^2,y^2,z^2]]);
    d,e,f := Explode([MC(Q,mon): mon in [y*z,z*x,x*y]]);
    Delta3 := 4*a*b*c - a*d^2 - b*e^2 - c*f^2 + d*e*f;
    if Delta3 ne 0 then return Delta3; end if;
  end for;
  return 0;
end function;

function SpanOfSingularLocusInternal(V,quads,F,d) 
  assert Degree(F) le d;
  m := Floor(d/2) + 1;
// Finds the m-fold root of F, where the latter is given as
// a univariate polynomial, but viewed as a binary form 
// of degree d. Then lets Q1,Q2 be a basis for the pencil
// of quadrics, where Q2 corresponds to this root, and
// returns the linear span of (ker(Q2) meet {Q1 = 0}),
// as a subspace of V = k^4.
  if Degree(F) le (d - m) then 
    Q2,Q1 := Explode(quads);
  else 
    rts := MultipleRoots(F,m);
    if #rts eq 0 then return false,_; end if;
    Q1,Q2 := Explode(quads);   
    Q2 := rts[1]*Q1 + Q2;
  end if;
  k := BaseRing(Universe(quads));
  U := KernelOfQuadric(V,Q2);
  mat := Matrix(Basis(U));
  d := Nrows(mat);
  R := PolynomialRing(k,d);
  subst := [&+[mat[i,j]*R.i: i in [1..d]]: j in [1..4]];
  Q1 := Evaluate(Q1,subst);
  if Q1 ne 0 then
    ff := Factorization(Q1);
    if ff[1,2] eq 2 then // Q1 restricted to ker(Q2) has rank 1
      mat1 := Matrix(k,d,1,[MC(ff[1,1],R.i): i in [1..d]]);
      mat := KernelMatrix(mat1)*mat;
      U := sub<V|[V!mat[i]: i in [1..d-1]]>;
    end if;
  end if;
  return true,U;
end function;

function SpanOfSingularLocus(V,phi);
// Computes the span of the singular locus of a quadric intersection.
// The answer is returned as a subspace of V = k^4.
  quads := Equations(phi);
  k := CoefficientRing(phi);
  R := PolynomialRing(phi);
  error if Discriminant(phi) ne 0,
    "Error: Reduced quadric intersection should be singular.";
  error if cInvariants(phi) ne [0,0],
    "Error: Reduced quadric intersection should be a null-form.";
  error if GCD(quads) ne 1,
    "Error: Reduced quadrics should be coprime.";
  U := &meet[KernelOfQuadric(V,q): q in quads];
  P := PolynomialRing(k); t := P.1;
  common_nullity := Dimension(U);
  vprintf Minimisation,3 : "Common Nullity = %o\n",common_nullity;
  error if common_nullity gt 2, 
    "Error : Common nullity =",common_nullity," Please report";
  case common_nullity :
    when 0:
      F,d := DeterminantPolynomial(phi,t);
      vprintf Minimisation,3 : "F = %o\n",PrettyFactorization(F);
      if F eq 0 then 
        Q1,Q2 := Explode(quads);
        UU := [KernelOfQuadric(V,q): q in [Q1,Q2,Q1+Q2]];
        U := &+[U : U in UU | Dimension(U) eq 1];
      else
        flag,U := SpanOfSingularLocusInternal(V,quads,F,d);
        assert flag;
      end if;
    when 1 :
      Q1,Q2 := Explode(Equations(ChangeRing(phi,P)));
      F := SubDiscriminantThree(t*Q1+Q2);
      error if F eq 0, 
        "Error: Generic rank is less than 3. Please report.";
      vprintf Minimisation,3 : "F = %o\n",PrettyFactorization(F);
      flag,Unew := SpanOfSingularLocusInternal(V,quads,F,3);
      if flag then U := Unew; end if;
  end case;
  vprintf Minimisation,3 : 
    "Span of singular locus has basis \n%o\n",Matrix(Basis(U));  
  return U;
end function;

//////////////////////////////////////////////////////////////
//                      Case n = 5                          //
//////////////////////////////////////////////////////////////

function GetQuadrics(phi,p,irreg)
  cc := p^irreg;
  quads := [(1/cc)*q : q in Equations(phi)];
  if irreg gt 0 then 
    R := PolynomialRing(phi);
    Q := Rationals();
    M := Matrix(phi);
    mat := Matrix(Q,5,25,[[MC(M[i,r],R.s): r,s in [1..5]]: i in [1..5]]);
    mat := MySaturate(mat);
    quads := [&+[mat[i,j]*quads[i]: i in [1..5]]: j in [1..5]];
  end if;
  return quads;
end function;

function SpanOfSingularLocusFive(quads)
  R := Universe(quads);
  k := CoefficientRing(R);
  J := Matrix(R,5,5,[Deriv(q,i): i in [1..5],q in quads]);
  I := ideal<R|quads cat Minors(J,3)>;
  ff := MinimalBasis(Radical(I));
  ff := [f : f in ff | TotalDegree(f) eq 1];
  mat := Matrix(k,#ff,5,[MC(f,R.i): i in [1..5],f in ff]);
  vprintf Minimisation,3 :
    "Singular locus defined by linear forms\n%o\n",mat;
  return mat;
end function;

//////////////////////////////////////////////////////////////
//                   Cases n = 2,3,4,5                      //
//////////////////////////////////////////////////////////////

function _Valuation(x, p)
  if Type(p) eq RngIntElt then
    return Valuation(x, p : Check:=false);
  else
    return Valuation(x, p);
  end if;
end function;

function _SquareFree(x : primes:=[])
  t := Type(x);
  if t in {RngIntElt,FldRatElt} then
    return SquareFree(x);
  elif t eq RngUPolElt then
    fact, c := Factorization(x);
    r := c * &* [Parent(x)| t[1] : t in fact | IsOdd(t[2])];
    s := &* [Parent(x)| t[1]^(t[2] div 2) : t in fact];
    assert x eq r*s^2;
    return r, s;
  end if;
end function;

function reduce(x, I)
  _, modI := quo<Order(I)|I>;
  return x @modI @@modI;
end function;

// an element with the same valuation as I at all prime divisors of I and J
// (avoids factoring)

function weak_approximation(I, J)
  O := Order(I);
  if O!1 in I then
    return O!1;
  end if;
  assert not IsZero(I);
  _,x := TwoElementNormal(I);
assert x*O + I^2 eq I;
  I2J := I^2 meet J;
  if O!1 notin J then
    bI := Basis(I);
    while x*O + I2J ne I do 
      x +:= Random(bI);
    end while;
  end if;
  return reduce(x, I2J);
end function;

function SaturateModel(phi : primes:=[])
// n = 2  : makes GCD(coeffs) square-free
// n = 3  : makes GCD(coeffs) = 1
// n = 4  : makes quadrics linearly indep. mod p for all p.
// n = 5  : makes Pfaffians linearly indep. mod p for all p.
  Q := _BaseField(phi);
  case Degree(phi) :
    when 2:
      if #Eltseq(phi) eq 5 then 
        if Type(Q) in {FldRat,FldFunRat} then
          d := RationalGCD(Eltseq(phi));
          a1,a2 := _SquareFree(Numerator(d));
          b1,b2 := _SquareFree(Denominator(d));
          tr := <b1*b2/a2,Id(Q,2)>;
        else // FldNum case
          G := ideal<Integers(Q)|Eltseq(phi)>;
          s := WeakApproximation(primes, [-(Valuation(G,p) div 2) : p in primes]);
          tr := <s,Id(Q,2)>;
        end if;
      else
        return SaturateWithCrossTerms(phi);
      end if;
    when 3:
      tr := <1/RationalGCD(Eltseq(phi)),Id(Q,3)>;
    when 4:  
      tr := <MySaturate(CoeffMatrix(Equations(phi),2))^(-1),Id(Q,4)>;
      vprintf Minimisation,3 : 
        "Change of basis for space of quadrics \n%o\n",tr[1];
    when 5:
      mat := MySaturate(CoeffMatrix(Equations(phi),2));
      d1 := RationalGCD(Eltseq(mat));
      mat := (1/d1)*mat;
      _,tr := IsTransformation(5,<Transpose(mat),Id(Q,5)>);
      phi := tr*phi;
      d2 := RationalGCD(Eltseq(phi));
      irreg := Integers()!(d1*Determinant(mat)/d2^2);
      _,tr1 := IsTransformation(5,<Id(Q,5),(1/d2)*Id(Q,5)>);
      vprintf Minimisation,3 : 
        "Change of basis for space of quadrics \n%o\n",tr[1];
      vprintf Minimisation,3 : 
        "Irregularity = %o\n",Factorization(irreg);
      return tr1*phi,tr1*tr,irreg;
  end case;
  flag,tr := IsTransformation(Degree(phi),tr);
  assert flag;
  return tr*phi,tr,1;
end function;

// 'primes' (for the FldNum case) is the list of all primes we don't want to mess up

function MinimiseInternal(phi,tr,leveldata,tflag : primes:=[], uniformizers:=[])
  Q := _BaseField(phi);
  Z := Integers(Q);
  FldNumCase := ISA(Type(Q), FldAlg); // only allowed for n = 2
  if #uniformizers eq 0 then
    assert not FldNumCase;
    uniformizers := [tup[1] : tup in leveldata];
  else 
    assert #uniformizers eq #leveldata;
  end if;
  n := Degree(phi);
  assert n in {2,3,4,5};
  maxsteps := case< n | 2:2, 3:4, 4:5, 5:6, default:0 >;// a guess when n = 5
  idqtrans := case< n | 4:Id(Q,2), 5:Id(Q,5), default:1 >;
  vprintf Minimisation,1 : "Level = %o\n", 
     FldNumCase select [<Norm(t[1]),t[2]>: t in leveldata] else leveldata;
  vprintf Minimisation,2 : 
     "Notation: \"/\" = level decreases  \".\" = level preserved\n";
  failedprimes := [];
  for i := 1 to #leveldata do 
    if n eq 5 then 
      p,level,irreg := Explode(leveldata[i]); 
    else
      p,level := Explode(leveldata[i]);
    end if;
if level gt 0 then
    vprintf Minimisation,1 : "Minimising at p = %o (level = %o)\n",p,level;
    IndentPush();
    pi := uniformizers[i];
    k,res := ResidueClassField(p);
    V := VectorSpace(k,n);
    R := PolynomialRing(k,n);
    nsteps := 0;
    oldphi := phi;  
    _,tr0 := IsTransformation(n,<idqtrans,Id(Q,n)>);
    while level gt 0 do
      if n in {3,4} then 
        seq := ChangeUniverse(Eltseq(phi),k);
        phibar := GenusOneModel(n,seq:PolyRing:=R);
      end if;
      case n :
        when 2 :
          F,d := PolynomialQ1(phi,p,pi:res:=res);
          flag,rr := RepeatedRoot(F,d);
          if not flag then 
            vprintf Minimisation,2 : 
              " no triple root => minimal at level %o\n",level; 
            error if not IsEven(Norm(p)), "Error:  Null-form without triple root.";
            failedprimes cat:= [<p,level>]; 
            break;
          end if;
          mat := Matrix(k,1,2,[-rr[2],rr[1]]);
        when 3 :         
          U := SingularLocusThree(V,phibar);
          mat := Matrix(Basis(U));
        when 4 :
          f := GCD(Equations(phibar));
          if TotalDegree(f) eq 1 then
            vprintf Minimisation,3 : "GCD = %o\n",f;
            mat := Matrix(k,1,4,[MC(f,R.i): i in [1..4]]);
          else
            U1 := SpanOfSingularLocus(V,phibar);
            mat := Matrix(Basis(U1));
            mat := KernelMatrix(Transpose(mat));
          end if;
        when 5 :
	  quads := ChangeUniverse(GetQuadrics(phi,p,irreg),R);
          vprintf Minimisation,3 :
            "Space of quadrics has dimension %o\n",Rank(CoeffMatrix(quads,2));
          mat := SpanOfSingularLocusFive(quads);
      end case;
      q := Nrows(mat); 
      assert q lt n;
      if FldNumCase then // can't call Smith
        assert n eq 2 and q eq 1;
        // find matrix over Z with unit determinant and
        // with second column orthogonal to mat (mod p)
        if mat[1,2] eq 0 then
          mat := Matrix(Q, 2, 2, [1, 0, 0, 1]);
        elif mat[1,1] eq 0 then
          mat := Matrix(Q, 2, 2, [0, 1, 1, 0]);
        else
          B := Z! mat[1,2]@@res;
          D := Z! -mat[1,1]@@res;
          while ideal<Z|B,D> ne 1*Z do
            B +:= Random(Basis(p));
          end while;
          BC := CRT(B*Z, D*Z, Z!0, Z!-1);
          C := BC div B;
          A := (1+BC) div D;
          mat := Matrix(Q, 2, 2, [A, B, C, D]);
          assert IsUnit(Z!Determinant(mat));
        end if;
      else
        if Type(Z) eq RngInt then
          matZ := ChangeRing(mat,Z);
        else
          matZ := Matrix(Z, Ncols(mat), [x@@res: x in Eltseq(mat)]);
        end if;
        _,_,mat := SmithForm(matZ);
      end if;
      dd := [i le q select pi else 1 : i in [1..n]];
      M := Diag(Q,dd)*Transpose(mat); 
      vprintf Minimisation,3 : 
        "Change of co-ordinates on P^%o\n%o\n",n-1,M;
      _,tr1 := IsTransformation(n,<idqtrans,M>);
//[Valuation(c,p) : c in Eltseq(phi)];
      phi := tr1*phi; 
      if tflag then tr0 := tr1*tr0; end if;
      phi,tr1,globirreg := SaturateModel(phi : primes:=primes);
      if tflag then tr0 := tr1*tr0; end if;
//[Valuation(c,p) : c in Eltseq(phi)];
      ch := q + _Valuation(ScalingFactor(tr1), p);
      if n eq 5 then 
        newirreg := Valuation(globirreg,p:Check:=false);
        ch := ch - 2*(newirreg - irreg);
        irreg := newirreg;
      end if;
      level +:= ch;
      if ch gt 0 then
        if FldNumCase then // this can happen, evidently
          vprintf Minimisation,2 : " => minimal at level %o\n",level;
          phi := oldphi;
          failedprimes cat:= [<p,level>];
          break;
        else
          error "In Minimise, the level increased.\n"*
                "Please send this example to magma-bugs@maths.usyd.edu.au";
        end if;
      end if;
      vprintf Minimisation,3 : "Level decreases by %o   (",-ch;
      if ch lt 0 then
        nsteps := 0;
        oldphi := phi;
        if tflag then tr := tr0*tr; end if;
        _,tr0 := IsTransformation(n,<idqtrans,Id(Q,n)>);
        vprintf Minimisation,2 :"/";
      else
        nsteps +:= 1;
        vprintf Minimisation,2 :".";
      end if;
      vprintf Minimisation,3 : ")\n";
      if nsteps ge maxsteps then
        vprintf Minimisation,2 : " => minimal at level %o\n",level;
        phi := oldphi;
        failedprimes cat:= [<p,level>];
        break;
      end if;
    end while;
    if level eq 0 then
      vprintf Minimisation,2 : "  => level 0 \n";
    end if;
    IndentPop();
end if; // level gt 0
  end for;
  return phi,tr,failedprimes;
end function;

function MyFactorization(n,plist)
  t := Type(n);
  if t eq FldRatElt then
    n := Integers()! n;
  elif ISA(t, FldFunGElt) then
    n := Integers(Parent(n))! n;
  end if;
  if #plist ne 0 then 
    plist := Sort(SetToSequence(SequenceToSet(plist)));
    return [<p,_Valuation(n,p)>: p in plist];
  else 
    vprintf Minimisation,1 : "Factoring the level\n";
    return Factorization(n);
  end if;
end function; 

// uniformizer of the ith prime that is coprime to the other primes, 
// with any extra stuff in the denominator
function MyUniformizer(primes, i)
  u := WeakApproximation(primes, [j eq i select 1 else 0 : j in [1..#primes]]);
  return u;
end function;

/////////////////////////////////////////////////////////////////////////
//       The main intrinsic                                            //
/////////////////////////////////////////////////////////////////////////

// Implemented over number fields only for degree 2 models without crossterms.
// If UsePrimes is specified, the model will be minimised only at these primes, 
// and will get worse at other primes (which cannot be specified).  
// If UsePrimes is [], the model will be minimised everywhere (or if not possible
// due to class group constraints, everywhere except some ClassGroupPrimes).

forward MinimiseGlobally;

intrinsic Minimise(model::ModelG1:
  Transformation := true,
  CrossTerms := false,
  UsePrimes := [],
  ClassGroupPrimes := [] )  
  -> ModelG1, TransG1, SetEnum
{A minimal model of the given genus one model.  Implemented for models 
of degree 2,3,4 or 5 over Q, and for models of degree 2 over number fields.
Also returns the transformation (unless Transformation := false),
and the set of primes p where the minimal model has positive level. 
If UsePrimes is specified, the model is minimised only at these primes.
In the number field case, a globally minimal model may not exist, but
the returned model is as close to minimal as possible (in particular, 
if ClassGroupPrimes are specified, it is minimal at all other primes).}

  R := CoefficientRing(model);
  n := Degree(model);
  require n in {2,3,4,5} : "Model must have degree 2,3,4 or 5.";
  require Discriminant(model) ne 0 : "Model is singular";

  FldNumCase := n eq 2 and (ISA(Type(R), FldAlg) or ISA(Type(R), RngOrd));
  FldFunCase := n eq 2 and (ISA(Type(R), FldFunRat) or ISA(Type(R), RngUPol));
  require Type(R) in {FldRat, RngInt} or FldNumCase or FldFunCase
    : "Model must be defined over the rationals, or (for models of degree 2)"*
      " a number field or a univariate rational function field";

  if FldNumCase then
    K := NumberField(R);
    require IsAbsoluteField(K): "Not implemented for models over relative number fields";
    require not CrossTerms : "CrossTerms not allowed in the number field case";
    if UsePrimes cmpeq [] then
      // returns minmodel, tr, failed_primes, non_min_primes
      return MinimiseGlobally(model : ClassGroupPrimes:=ClassGroupPrimes);
    end if;
    Uniformizers := [MyUniformizer(UsePrimes,i) : i in [1..#UsePrimes]];
    phi := ChangeRing(model,K);
  elif FldFunCase then
    phi := ChangeRing(model,FieldOfFractions(R));
  else
    phi := ChangeRing(model,Rationals());
    if assigned model`GlobalLevel then
      phi`GlobalLevel := model`GlobalLevel;
    end if;
  end if;

  vprintf Minimisation, 1 :"Minimising a genus one model of degree %o\n",n;
  if n eq 2 then 
    phi,tr1 := RemoveCrossTerms(phi); 
    phi,tr2 := SaturateModel(phi : primes:=UsePrimes);
    tr := tr2*tr1;
  else
    phi,tr,irreg := SaturateModel(phi);
  end if;
  if n eq 5 then // only over Q
    globlev := GlobalLevel(phi)/irreg^2;
    ff := MyFactorization(globlev,UsePrimes);
    leveldata := [<f[1],f[2],Valuation(irreg,f[1]:Check:=false)>: f in ff];
  elif FldNumCase then
    leveldata := LevelDataFldNum(phi,UsePrimes);
  elif FldFunCase then
    leveldata := LevelDataFldFun(phi : primes:=UsePrimes);
  else
    leveldata := MyFactorization(GlobalLevel(phi),UsePrimes);
  end if;
  phi,tr,leveldata := MinimiseInternal(phi,tr,leveldata,Transformation : primes:=UsePrimes, 
                                       uniformizers:=(FldNumCase select Uniformizers else []) );
  failedprimes := {f[1]: f in leveldata};
  if n eq 2 and CrossTerms then 
    vprintf Minimisation,1 : "Final stage : introducing cross terms\n";
    _,idtrans := IsTransformation(2,<1,[0,0,0],Id(Rationals(),2)>);
    phi := idtrans*phi; 
    ld2 := [pr : pr in leveldata | pr[1] eq 2];
    level := #ld2 ne 0 select ld2[1][2] else 0;
    phi,tr1 := SaturateModel(phi);
    tr := tr1*tr;
    level +:= Valuation(ScalingFactor(tr1),2);
    vprintf Minimisation,1 : 
      "Making a y-substutition => level = %o\n",level;
    if level gt 0 then 
      phi,tr,ld2 := MinimiseInternal(phi,tr,[<2,level>],Transformation : primes:=UsePrimes);
      level := #ld2 ne 0 select ld2[1][2] else 0;
    end if;
    if level eq 0 then Exclude(~failedprimes,2); end if;
  end if;
  if #failedprimes gt 0 then
    vprintf Minimisation,1 : 
      "Minimal model has positive level at primes %o.\n",failedprimes;
  else
    vprintf Minimisation,1 : "Model has level 0 at all primes.\n";
  end if;

  if Transformation then
    return phi,tr,failedprimes;
  else
    return phi,_,failedprimes;
  end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
//       Global minimisation over number fields                        //
//       Steve Donnelly, April 2010                                    //
/////////////////////////////////////////////////////////////////////////

// Representative of the class c in Domain(mCl), as a combination of elements of S

function representative(c, mCl, S);
  Cl := Domain(mCl);
  if c eq Cl.0 then
    return c@mCl, [0 : s in S]; // trivial ideal
  end if;
  ZS := FreeAbelianGroup(#S);
  im := [s@@mCl : s in S];
  ZStoCl := hom< ZS -> Cl | im >;
  bool, v := HasPreimage(c, ZStoCl);
  error if not bool, "The given primes do not generate a large enough subgroup";
  v := Eltseq(v);
  v := [v[i] mod Order(im[i]) : i in [1..#S]];
  return &* [S[i]^v[i] : i in [1..#S]], v;
end function;

// Matrix in SL(2,R) congruent to the given Us modulo the given factors

function approximate_SL2(Us, factors)
  I := &* factors;
  R := Order(I);
  elts := [* Eltseq(U) : U in Us *];
  crt := [R| CRT([R| elts[i][j] : i in [1..#factors]], factors) : j in [1..4]];
  U := Matrix(R, 2, crt);
  // U is only defined mod I, so can change it
assert ideal<R|U[1,1],U[2,1]> + I eq 1*R;
  while ideal<R|U[1,1],U[2,1]> ne 1*R do
    i := Random(1,2);
    U[i,1] +:= Random(Basis(I));
  end while;
  error if Determinant(U) - 1 notin I,
       "Matrices should have determinant 1 modulo the corresponding ideal";
  s11,s12 := Explode(Representation(R!1, [U[1,1],U[2,1]]));
assert s11*U[1,1] + s12*U[2,1] eq 1;
  s21,s22 := Explode(Representation(R!1, [-s12,s11]));
  S1 := Matrix(R, 2, [s11,s12,s21,s22]);
assert Determinant(S1) eq 1;
  U1 := S1*U;
  S2 := Matrix(R, 2, [1,0,-U1[2,1],1]);
  U2 := S2*U1;
assert U2[1,1] eq 1 and U2[2,1] eq 0 and U2[2,2] - 1 in I;
  U2[2,2] := 1;
  Ua := S1^-1 * S2^-1 * U2;
  assert Determinant(Ua) eq 1;
  assert &and [x in I : x in Eltseq(U-Ua)];
  return Ua;
end function;

// Matrix that globally does the same minimisation that M does 
// locally at divisors of I.  
// Result is D*U2 where Det(U2) = 1 and Det(D) + I = Det(M) + I
// (so M = U1*D*U2 for some U1 invertible in R/I)

function global_transformation(M, det)

  assert Determinant(M) ne 0;
  assert Nrows(M) eq 2;

  R := Integers(Parent(det));
  Det := det*R;
  assert IsIntegral(Det);
  if Minimum(Det) eq 1 then // TO DO: correct, surely?
    assert det eq 1;
    return IdentityMatrix(R, 2);
  end if;

  fact := Factorization(Det);
  primes := [t[1] : t in fact];
  factors := [t[1]^t[2] : t in fact];

  maps := [* *];
  U2s := [];
  Ds := [];
  for tup in fact do
    p, e := Explode(tup);
    pprec := 10 + Valuation(det,p);
    Rp, mRp := Completion(R, p : Precision:=pprec);
    Append(~maps, mRp);
    Mp := Matrix(Rp, 2, [x@mRp : x in Eltseq(M)]);

    D, iU1, iU2 := SmithForm(Mp);
    U2 := iU2^-1;
assert IsUnit(Determinant(U2));
assert &and [IsWeaklyZero(x) : x in Eltseq(iU1^-1*D*U2 - Mp)];
    // fudge so U2 has determinant 1
    F2 := IdentityMatrix(Rp,2);
    F2[2,2] := Determinant(U2);
    U2 := F2^-1 * U2;
    D := D * F2;
assert Determinant(U2) eq Rp!1;
assert BaseRing(U2) eq Rp;
assert &and [IsWeaklyZero(d) : d in [D[1,2],D[2,1]]];
    Append(~U2s, Matrix(R, 2, [x@@mRp : x in Eltseq(U2)]) );
    Append(~Ds, [R| D[1,1]@@mRp, D[2,2]@@mRp] );
  end for;

  U2a := approximate_SL2(U2s, factors);

  vals1 := [Valuation(Ds[i][1],primes[i]) : i in [1..#primes]];
  if forall{v : v in vals1 | v eq 0} then
    Da := DiagonalMatrix([R| 1, det]);
  else
    d1_idl := &* [primes[i]^vals1[i] : i in [1..#primes]];
    assert det in d1_idl;
    bool, d1 := IsPrincipal(d1_idl);
    if bool then
      Da := DiagonalMatrix([R| d1, det div d1]);
    else
      // Need b,c in Det and d1,d2 generating the right ideals in R/Det
      // with d1*d2 - b*c = det
      d1 := weak_approximation(d1_idl, det*R);
      // Choose b in Det such that (d1,b) = (d1) + Det
      b := weak_approximation(det*R, d1*R);
      // Choose d2 congruent to det/d1 mod b
      _, modb := quo<R|b*Det>;
      d2 := ((det@modb) / (d1@modb)) @@modb;
      c := R!( (d1*d2 - det)/b );
      Da := Matrix(R, 2, [d1, b, c, d2]);
assert b in Det;
assert c in Det;
assert d1*R + Det eq d1_idl;
    end if;
  end if;

  return Da*U2a;
end function;

function easy_factors(N, e)
  f, _, u := Factorization(N : ECMLimit:=5000+500*e, MPQSLimit:=0, Proof:=false);
  F := [t[1] : t in f];
  if assigned u then
//printf "unfactored (with effort %o):\n%o\n", e, Seqset(u);
    return F, Setseq(Seqset(u));
  else
    return F, [];
  end if;
end function;

function MinimiseGlobally(phi : ClassGroupPrimes:=[])

  K := NumberField(BaseRing(phi));
  ZK := Integers(K);
  PI := PowerIdeal(ZK);
  PIF := PowerIdeal(FieldOfFractions(ZK));
  one := 1*ZK;

  if IsEmpty(ClassGroupPrimes) then
    Cl, mCl := ClassGroup(ZK);
    ClassGroupPrimes := &join {{t[1] : t in Factorization(c@mCl)} : c in Generators(Cl)};
  end if;
  if Type(ClassGroupPrimes) in {SetEnum,SetIndx} then 
    ClassGroupPrimes := Setseq(ClassGroupPrimes);
  end if;

  phi0 := phi;
  // clear cross terms, if any
  phi, tr0 := RemoveCrossTerms(phi); 
  // clear denoms (TO DO: optimally)
  denom := Denominator(ideal<ZK|Eltseq(phi)>);
  d1, d2 := Squarefree(denom); 
  assert denom eq d1 * d2^2;
  tr0`Scalar *:= d1*d2;
  phi := GenusOneModel([(d1*d2)^2*c : c in Eltseq(phi)]);
assert phi eq tr0 * phi0;
assert forall{c: c in Eltseq(phi) | IsIntegral(c)};

  // Determine primes where level could be > 0 
  // TO DO: save more effort in factoring 
  c4,c6 := Explode(cInvariants(phi));
  if c4 eq 0 then 
    // handle j = 0 carefully 
    // (we care about these curve, for instance in EllipticCurveSearch)
    // Currently, only minimise at prime factors we can find
    assert IsIntegral(c6);
    qs, rs := easy_factors(Minimum(c6*ZK), 10);
    if not IsEmpty(rs) then
      printf "WARNING: Not minimising at (unknown) primes dividing\n%o\n", rs;
    end if;
    primes := [PI| t[1] : t in Decomposition(ZK,q), q in qs];
  else
    G4 := ideal<ZK | c4, c6 >;
    G2 := ideal<ZK | Basis(G4^2) cat [c6] > / G4;
    _ := Factorization(G2); // this stores factors, doesn't it?
    primes := [PI| t[1] : t in Factorization(G4)]; 
  end if;
  primes := [PI| p : p in primes | c4 in p^4 and c6 in p^6];
  primes cat:= [p : p in ClassGroupPrimes | p notin primes];

  if IsEmpty(primes) then
    vprint Minimisation: "Model is already minimal";
    return phi, tr0, [PI|], [PI|];
  end if;

  // Minimise locally to determine level and local transformations
  vprint Minimisation: "Minimising locally at bad primes to determine level...";
  IndentPush();
  assert not IsEmpty(primes); // otherwise infinite loop!
  phi_loc, tr_loc, failed_primes := Minimise(phi : UsePrimes:=primes);
  IndentPop();
  mu_loc := tr_loc`Scalar;
  T_loc := ChangeRing(tr_loc`Matrix, ZK);
  det_loc := Determinant(T_loc);
  levels := [-Valuation(mu_loc,p)-Valuation(det_loc,p) : p in primes];
  assert &and [v ge 0: v in levels];
  level := &* [PI| primes[i]^levels[i] : i in [1..#primes]];
  vprint Minimisation: "Level is", [<Norm(primes[i]),levels[i]> : i in [1..#primes]];

  if level eq one then
    vprint Minimisation: "Model is already minimal";
    return phi, tr0, failed_primes, [PI|];
  end if;

assert &and [Valuation(mu_loc,p) + Valuation(det_loc,p) eq -Valuation(level,p) : p in primes];

  // CLASS GROUP OBSTRUCTION to global minimisation.  

  // Let mu_idl and det_idl be the obvious ideals (supported in primes).
  // Note that mu_idl*det_idl eq level^-1.
  // We must choose (principal) mu and det in mu_idl and det_idl, but
  // we may first adjust these as follows: 
  // (mu_idl, det_idl) defines a class in (Cl + Cl)/{(h,-h) : h in H} 
  // where H is the subgroup 2*Cl + <irregular primes>.
  // We wish to make the index (mu*det)/level^-1 as small as we can.
  // Current procedure (we prefer to make det small): let m and d be 
  // the classes of mu_idl^-1 and det_idl^-1; adjust everything using 
  // the action of H to make d nice; take M and D integral ideals in 
  // the classes of m and d; then M*mu_idl and D*det_idl are principal.

  // Identify the irregular bad primes (TO DO)
  irreg_primes := [PI| ];

  classes := [p@@mCl : p in primes];
  mu_vals := [Valuation(mu_loc,p) : p in primes];
  det_vals := [Valuation(det_loc,p) : p in primes];
  mu_idl := &* [PIF| primes[i]^mu_vals[i] : i in [1..#primes] | mu_vals[i] ne 0];
  det_idl := &* [PIF| primes[i]^det_vals[i] : i in [1..#primes] | det_vals[i] ne 0];
  m := - &+ [Cl| mu_vals[i]*classes[i] : i in [1..#primes]];
  d := - &+ [Cl| det_vals[i]*classes[i] : i in [1..#primes]];

  // choose rep for D (which will be the extra factor in det)
  H := sub< Cl | [2*Cl.i : i in [1..Ngens(Cl)]] cat [p@@mCl : p in irreg_primes] >;
  ClH, modH := quo<Cl|H>;
  S := [p : p in ClassGroupPrimes | p notin irreg_primes];
  D, vD := representative(d@modH, Inverse(modH)*mCl, S);
  assert Seqset(vD) subset {0,1};
  // choose which irreg_primes to adjust by
  h := d - D@@mCl; assert h in H;
  Cl2, mod2 := quo<Cl|2*Cl>;
  I, vI := representative(h@mod2, Inverse(mod2)*mCl, irreg_primes);
  assert Seqset(vI) subset {0,1};
  Itriv := I eq one;
  if h in 2*Cl then assert Itriv; end if;
  // choose which square ideal to adjust by 
  // (any representative ideal will do; don't need to use ClassGroupPrimes, 
  // but the primes used must be included in our 'primes')
  j2 := h - I@@mCl;
  two := hom< Cl->Cl | [2*Cl.i : i in [1..Ngens(Cl)]] >;
  bool, j := HasPreimage(j2, two); assert bool;
  J := j@mCl;
  if not {t[1] : t in Factorization(J)} subset primes then
    J := representative(j, mCl, ClassGroupPrimes);
  end if;
  Jtriv := J eq one;
  if j2 eq Cl.0 then assert Jtriv; end if;

  if not (Itriv and Jtriv) then
    vprint Minimisation: "Swapping factors between mu and det ideals:";
  end if;
  if not Itriv then
    vprint Minimisation: "'Nonregular primes' of norms", [Norm(irreg_primes[i]) : i in [1..#vI] | vI[i] ne 0];
    error "Not implemented yet"; // TO DO
  end if;
  if not Jtriv then
    vprint Minimisation: "Square of ideal of norm", Norm(J);
    jj := WeakApproximation(primes, [Valuation(J,p) : p in primes]);
    mu_idl /:= J^2; 
    det_idl *:= J^2;
    mu_loc /:= jj^2;
    T_loc *:= jj;
    det_loc *:= jj^2;
assert mu_idl*det_idl eq level^-1;
assert det_loc eq Determinant(T_loc);
assert det_loc in det_idl;
assert d-2*j eq -(Denominator(det_idl)*det_idl)@@mCl;
  end if;

assert &and [Valuation(mu_idl,p) + Valuation(det_idl,p) eq -Valuation(level,p) : p in primes];
assert &and [Valuation(mu_loc,p) + Valuation(det_loc,p) eq -Valuation(level,p) : p in primes];

  m := - (Denominator(mu_idl)*mu_idl) @@mCl;
  M := m @mCl;
  bool, mu := IsPrincipal(M*mu_idl); assert bool;
  bool, det := IsPrincipal(D*det_idl); assert bool;

  non_min_primes := [PI| p : p in primes | Valuation(M,p) ne 0 or Valuation(D,p) ne 0];
  if not IsEmpty(non_min_primes) then
    vprintf Minimisation: "Class group obstruction to global minimal model:\n"*
                          "level will have extra factors of norm %o and %o\n", Norm(M), Norm(D);
  end if;

  // Get global matrix approximating T_loc, with determinant = det.
  // Wrinkle: we haven't put the D factor in T_loc, but global_transformation
  // will put it in T anyway (when it chooses d2)
  T := global_transformation(T_loc, det);
  assert Determinant(T) eq det;
  _,tr := IsTransformation(2, <mu,T>);
  minphi := tr * phi;
  tr := tr * tr0;
assert minphi eq tr * phi0;
assert &and [IsIntegral(x) : x in Eltseq(minphi)];

  if IsVerbose("Minimisation") then
    "Original c-invariants:";
    c4,c6 := Explode(cInvariants(phi0));
    c4 eq 0 select 0 else [<Norm(t[1]),t[2]> : t in Factorization(c4*ZK)];
    c6 eq 0 select 0 else [<Norm(t[1]),t[2]> : t in Factorization(c6*ZK)];
    "Minimised c-invariants:";
    c4,c6 := Explode(cInvariants(minphi));
    c4 eq 0 select 0 else [<Norm(t[1]),t[2]> : t in Factorization(c4*ZK)];
    c6 eq 0 select 0 else [<Norm(t[1]),t[2]> : t in Factorization(c6*ZK)];
  end if;

  return minphi, tr, failed_primes, non_min_primes;
  
end function;

/////////////////////////////////////////////////////////////////////////
//       Alternative treatment of (globally) soluble models            //
/////////////////////////////////////////////////////////////////////////

function IntegralGenusOneModel(eqns)
  RZ := Universe(eqns);
  case Rank(RZ) :
    when 2 : 
      P,Q := Explode(eqns);
      coeffs1 := [MC(P,RZ.1^(2-i)*RZ.2^i): i in [0..2]];
      coeffs2 := [MC(Q,RZ.1^(4-i)*RZ.2^i): i in [0..4]];
      model := GenusOneModel(2,coeffs1 cat coeffs2);
    when 3 : 
      model := GenusOneModel(eqns[1]);
    when 4 : 
      model := GenusOneModel(eqns);
    when 5 :
      RQ := PolynomialRing(Rationals(),5);
      eqns := ChangeUniverse(eqns,RQ);
      model := GenusOneModel(eqns);
      coeffs := PRIM(Eltseq(model));
      model := GenusOneModel(5,coeffs:PolyRing:=RZ);
  end case;
  return model;
end function;

function WeierstrassEquations(E,n)
  assert n in {3,4,5,6};
  R<x,y,z> := PolynomialRing(Integers(),3); 
  if n eq 3 then 
    return [Evaluate(Equation(E),[y,z,x])],[z,x,y];
  end if;
  ainv := ChangeUniverse(aInvariants(E),Integers());
  a1,a2,a3,a4,a6 := Explode(ainv);
  case n :
    when 4 :
      RR<x0,x2,x3,x4> := PolynomialRing(Integers(),4);
      ff := [z^2,x*z,y*z,x^2];
      quads := [ x0*x4 - x2^2,
	x3^2 + a1*x2*x3 + a3*x0*x3 - (x2*x4 + a2*x0*x4 + a4*x0*x2 + a6*x0^2)];
    when 5 :
      RR<x0,x2,x3,x4,x5> := PolynomialRing(Integers(),5);
      ff := [z^2,x*z,y*z,x^2,x*y];
      quads := [ x0*x4 - x2^2,x0*x5 - x2*x3,x2*x5 - x3*x4,
	x3^2 + a1*x0*x5 + a3*x0*x3 - (x2*x4 + a2*x0*x4 + a4*x0*x2 + a6*x0^2),
        x3*x5 + a1*x2*x5 + a3*x2*x3 - (x4^2 + a2*x2*x4 + a4*x2^2 + a6*x0*x2)];
    when 6 :
      RR<x0,x2,x3,x4,x5,x6> := PolynomialRing(Integers(),6);
      ff := [z^3,x*z^2,y*z^2,x^2*z,x*y*z,x^3];
      quads := [ x0*x4 - x2^2,x0*x5 - x2*x3,x0*x6 - x2*x4,
        x2*x5 - x3*x4,x2*x6 - x4^2,x3*x6 - x4*x5,
        x3^2 + a1*x0*x5 + a3*x0*x3 - x0*(x6 + a2*x4 + a4*x2 + a6*x0),
        x3*x5 + a1*x2*x5 + a3*x2*x3 - x2*(x6 + a2*x4 + a4*x2 + a6*x0),
	x5^2 + a1*x3*x6 + a3*x2*x5 - x4*(x6 + a2*x4 + a4*x2 + a6*x0)];
  end case;
  return quads,ff;
end function;

function GenusOneModelFromPoint(n,eqns,pt)
  assert forall{f: f in eqns| Evaluate(f,pt) eq 0};
  target := Proj(Universe(eqns))!([1] cat [0: i in [1..n]]);
  vprintf Minimisation,1 : "Moving P to %o\n",target;
  _,_,mat := SmithForm(Matrix(1,n+1,pt));
  matdual := Transpose(mat^(-1));
  eqns := [q^matdual : q in eqns];
  pt := [mat[n+1,j]: j in [2..n+1]]; 
  vprintf Minimisation,1 : "Projecting away from %o\n",target;
  R := PolynomialRing(Integers(),n);
  S := PolynomialRing(R); t := S.1;
  subst := [t] cat [R.i : i in [1..n]];
  eqns := [Evaluate(q,subst): q in eqns];
  if n eq 2 then 
    f1,f2,f3 := Explode([Coefficient(eqns[1],i): i in [2,1,0]]);
    eqns := [f2,-f1*f3];
    yy := mat[3,1]*Evaluate(f1,pt);
  else
    gg := [Coefficient(f,1): f in eqns];
    hh := [Coefficient(f,0): f in eqns];
    if n eq 3 then
      eqns := [gg[1]*hh[2]-gg[2]*hh[1]];  
    else
      km := KernelMatrix(CoeffMatrix(gg,1)); 
      eqns := [&+[km[i,j]*hh[j]: j in [1..#hh]]: i in [1..Nrows(km)]];
    end if;
  end if;
  vprint Minimisation,1 : "Performing some ad hoc reduction";
  submat := Matrix(n,n+1,[mat[i,j]: i in [1..n+1],j in [2..n+1]]);
  _,T := LLL(submat);
  Tinv := T^(-1);
  eqns := [q^Tinv : q in eqns];
  pt := [&+[T[i,j]*pt[j]: j in [1..n]]: i in [1..n]];
  if n in {4,5} then 
    _,U := LLL(CoeffMatrix(eqns,2));
    eqns := [&+[U[i,j]*eqns[j]: j in [1..#eqns]]: i in [1..#eqns]];
  end if;
  vprintf Minimisation,1 : "Re-writing as a genus one model\n";
  model := IntegralGenusOneModel(eqns);
  if n eq 2 then 
    rr := [-Floor(seq[i]/2): i in [1..3]] where seq is Eltseq(model);
    _,tr := IsTransformation(2,<1,rr,Id(Integers(),2)>);
    model := tr*model;
    yy := yy - rr[1]*pt[1]^2 - rr[2]*pt[1]*pt[2] - rr[3]*pt[2]^2;
    pt := pt cat [yy];
  end if;
  if n eq 5 then
    quads := Equations(model);
    assert (eqns eq quads) or (eqns eq [-q: q in quads]);
  end if;
  return model,pt;
end function;

intrinsic GenusOneModel(n::RngIntElt,P::PtEll:NoReduction := false)
  -> ModelG1, Pt
{Given a point P on an elliptic curve E over Q, and n = 2,3,4 or 5, maps E to P^\{n-1\} via the complete linear system |(n-1).O+P| and returns the corresponding genus one model of degree n. The formulae used give a genus one model that is minimised and is close to being reduced. Finally the function Reduce is called (unless NoReduction = true). The second returned value is a point on the covering curve that maps down to P (or -P).}
  E := Curve(P);
  K := BaseRing(E);
  require K cmpeq Rationals() 
    : "Elliptic curve must be defined over the rationals";
  K := Ring(Parent(P));
  require K cmpeq Rationals() 
    : "Point must be defined over the rationals";
  vprintf Minimisation, 1 :"Computing a minimal genus one model of degree %o\n",n;
  require n in {2,3,4,5} : "Model must have degree 2,3,4 or 5.";
  if P eq E!0 then 
    error "Point given is the identity - use GenusOneModel(n,E) instead";
  end if;
  E,iso := MinimalModel(E);
  P := iso(P);
  eqns,ff := WeierstrassEquations(E,n+1);
  pt := PRIM([Evaluate(f,Eltseq(P)): f in ff]);
  vprintf Minimisation, 1 :
    "We embed E in P^%o via the linear system |%o.0|\n",n,n+1;
  model,pt := GenusOneModelFromPoint(n,eqns,pt);
  model := ChangeRing(model,Rationals());  
  vprintf Minimisation, 1 : "Model has coefficients\n%o\n",Eltseq(model);
  if not NoReduction then 
    model,tr := Reduce(model);
    if n eq 2 then yy := pt[3]; end if;
    T := Transpose(tr`Matrix)^(-1);
    pt := [&+[T[i,j]*pt[j]: j in [1..n]]: i in [1..n]];
    cc := RationalGCD(pt);
    pt := [x/cc: x in pt];
    if n eq 2 then
      rr := tr`Shift;
      yy := yy/cc^2 - rr[1]*pt[1]^2 - rr[2]*pt[1]*pt[2] - rr[3]*pt[2]^2;
      pt := pt cat [yy];
    end if;
  end if;
  vprintf Minimisation, 1 :"Checking the invariants\n";
  error if cInvariants(model) ne cInvariants(E),
    "Model is not minimal. Please report";
  P := Curve(model)!pt; 
  return model,P;
end intrinsic;

///////////////////////////////////////////////////////////

// new intrinsics to replace those in "t3minimisation.m"

intrinsic Minimise(C::RngMPolElt) -> RngMPolElt, Tup
{Minimise the ternary cubic form C (which should have rational coefficients).
 Returns the minimised form, and a matrix M and scaling factor c to specify the transformation
 (such that the minimised cubic is c times the original cubic evaluated at [x,y,z]*M).}

  P3 := Parent(C);
  require Rank(P3) eq 3: "Form must be ternary.";
  require forall{m : m in Monomials(C) | TotalDegree(m) eq 3}:
          "Polynomial must be a cubic form.";
  require BaseRing(P3) cmpeq Rationals():
          "Form must live in polynomial ring over the rationals.";
  model := GenusOneModel(C);
  model1, tr := Minimise(model);
  require model1 eq tr*model : 
    "Failed to correctly record the transformation";
  return P3!Equation(model1), Tuple(tr);
end intrinsic;

intrinsic pMinimise(C::RngMPolElt, p::RngIntElt) -> RngMPolElt, AlgMatElt
{Minimise the integral ternary cubic Form C at the prime p.
 Returns the minimised form and the transformation.}
  P3 := Parent(C);
  require Rank(P3) eq 3: "Form must be ternary.";
  require forall{m : m in Monomials(C) | TotalDegree(m) eq 3}:
          "Polynomial must be a cubic form.";
  require BaseRing(P3) cmpeq Rationals():
          "Form must live in polynomial ring over the rationals.";
  model := GenusOneModel(C);
  model1, tr := Minimise(model:UsePrimes:=[p]);
  require model1 eq tr*model : 
    "Failed to correctly record the transformation";
  return P3!Equation(model1), Tuple(tr);
end intrinsic;

// Convert (E, P) --> (C, pt') where E is an elliptic curve/Q with
// a rational point pt and C is the corresponding plane cubic, with a
// rational point pt' that maps to pt on E.
intrinsic CubicFromPoint(E::CrvEll, P::PtEll) -> RngMPolElt, MapSch, Pt
{Given an elliptic curve and a point on it, find the corresponding
 3-covering as a ternary cubic, together with the covering map, and 
 a point on the cubic that maps to the given point on E.}
  if IsCoercible(E,P) then P := E!P; end if;
  require Curve(P) eq E : "P must be a point in E";
  if P eq E!0 then 
    model := GenusOneModel(3,E);
    Q := Curve(model)![0,1,0];
  else
    model,Q := GenusOneModel(3,P);
  end if;
  C, _, pi := nCovering(model : E:=E);
  Q := C!Eltseq(Q);
  if pi(Q) ne P then 
    pi := pi*MultiplicationByMMap(E,-1);
  end if;
  assert pi(Q) eq P;
  return C, pi, Q;
end intrinsic;

