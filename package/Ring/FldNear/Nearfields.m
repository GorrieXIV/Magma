freeze;
/*
  Finite nearfields and projective planes
  
  February 2012 Don Taylor

  $Id: Nearfields.m 41440 2012-12-05 03:45:26Z don $

  An example of user-defined types
*/


declare type Nfd;

declare attributes Nfd:
    gf,          // Underlying finite field
    prim,        // Primitive element of the underlying field
    p,           // Characteristic of the underlying finite field
    q,           // Order of the kernel of the nearfield
    matgrp,      // The matrix group of units of the nearfield
    sz,          // The size of the base field of "matgrp"
    psi,         // Homomorphism from "matgrp" to the nearfield
    phi;         // Bijection between field and vector space


declare type NfdElt;

declare attributes NfdElt:
    parent,      // Parent of element
    elt,         // Element (as an element of the corresponding finite field)
    log;         // Logarithm of the element, when a unit, otherwise -1

 declare type NfdDck [NfdElt]: Nfd;


 declare attributes NfdDck:
    h, v,        // $(p,h,v)$ is a Dickson triple
    twist,       // sequence twisted residues mod v
    rho;         // sequence of Frobenius powers

 declare type NfdZss [NfdElt]: Nfd;

 declare attributes NfdZss:
    ndx,         // The index of the irregular nearfield
    mu;          // Associative array mapping vectors to matrices

isDicksonPair := func< q, v |
  IsPrimePower(q) and forall{ r : r in PrimeBasis(v) | q mod r eq 1 } and
    ((q mod 4 eq 1) or (v mod 4 ne 0)) >;


//==============================================================================
intrinsic DicksonPairs(p::RngIntElt, hlo::RngIntElt,  hhi::RngIntElt,
                         vlo::RngIntElt, vhi::RngIntElt) -> []
{List the Dickson pairs (q, v) for prime p, where hlo and hhi
 are the lower and upper bounds on h and vlo, vhi
 are the lower and upper bounds on v}

  require IsPrime(p): "p must be prime";
  pairs := [];
  for h := hlo to hhi do
    for v := vlo to vhi do
      if isDicksonPair(p^h,v) then
         Append(~pairs, [p^h, v]);
      end if;
    end for;
  end for;

  return pairs;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic DicksonPairs(p::RngIntElt, h1::RngIntElt, v1::RngIntElt) -> []
{List the Dickson pairs (p^h, v) for prime p, where h1 and v1
 are upper bounds on h and v}
 return DicksonPairs(p,1,h1,1,v1);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic DicksonTriples(p::RngIntElt, hb::RngIntElt, vb::RngIntElt) -> []
{List the Dickson triples (p,h,v) for prime p, where
 hb and vb are bounds on h and v}

  require IsPrime(p): "p must be prime";
  triples := [];
  for h := 1 to hb do
    for v := 1 to vb do
      if isDicksonPair(p^h,v) then
        Append(~triples, [p, h, v]);
      end if;
    end for;
  end for;

  return triples;

end intrinsic;
//------------------------------------------------------------------------------

good_exponent := function(q,v,e)
  m := (q^v - 1) div v;
  m_ := &*{ r : r in PrimeDivisors(m) | not IsDivisibleBy(e,r) };
  return e + m_*v;
end function;


nearField := function(q,v,K,zeta : LargeMatrices := false)
  _, p, h := IsPrimePower(q);
  sz := LargeMatrices select p else q;
  L := GF(sz);
  E, phi := VectorSpace(K,L);
  twist := [ 0 : j in [1..v]];
  rho := twist;
  for i := 1 to v do
    s := ((q^i-1) div (q-1)) mod v;
    twist[s+1] := i;
    rho[s+1] := q^i;
  end for;

  NF := New(NfdDck);
  NF`p     := p;
  NF`h     := h;
  NF`v     := v;
  NF`q     := q;
  NF`gf    := K;
  NF`sz    := sz;
  NF`phi   := phi;
  NF`prim  := zeta;
  NF`twist := twist;
  NF`rho   := rho;

  return NF;

end function;


//==============================================================================
intrinsic DicksonNearfield(q::RngIntElt, v::RngIntElt : Variant := 1,
         LargeMatrices := false) -> NfdDck
{Create a Dickson nearfield from the Dickson pair (q,v)}

  require isDicksonPair(q,v):
       Sprintf("(%o, %o) is not a Dickson pair", q, v );
  e := (v eq 1) select 1 else Integers()!Variant mod v;
  require IsCoprime(v,e): "Variant must be coprime to v";
  if e ne 1 then
    e := good_exponent(q,v,e);
  end if;

  K := GF(q^v);
  return nearField(q,v,K,PrimitiveElement(K)^e :
     LargeMatrices := LargeMatrices);

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic NumberOfVariants(q::RngIntElt,v::RngIntElt) -> RngIntElt
{The number of non-isomorphic nearfields with
 Dickson pair (q,v)}
  require isDicksonPair(q, v):
        Sprintf("(%o, %o) is not a Dickson pair", q, v );
  if v eq 1 then return 1; end if;
  _, p, h := IsPrimePower(q);
  return EulerPhi(v) div Order(ResidueClassRing(v)!p);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic NumberOfVariants(N::NfdDck) -> RngIntElt
{The number of variants of the Dickson nearfield N}
  return EulerPhi(N`v) div Order(ResidueClassRing(N`v)!N`p);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic VariantRepresentatives(q::RngIntElt,v::RngIntElt) -> SeqEnum
{Representatives for the variant parameter of nearfields with
  Dickson pair (q,v)}
  require isDicksonPair(q,v):
       Sprintf("(%o, %o) is not a Dickson pair", q, v );
  if v eq 1 then return [ 1 ]; end if;
  _, p, h := IsPrimePower(q);
  R := ResidueClassRing(v);
  U,f := UnitGroup(R);
  X := {@ f(u) : u in U @};
  pi := R!p;
  t := [ x*pi : x in X ];
  S := Sym(X);
  P := sub<S|t>;
  reps := OrbitRepresentatives(P);
  return [r[2] : r in reps];
end intrinsic;
//------------------------------------------------------------------------------

irrNF := function(ndx)

 A := Matrix(2,2,[0,1,-1,0]);
 case ndx:
    when 1:
      p := 5;
      B := Matrix(2,2,[1,-2,-1,-2]);
    when 2:
      p := 11;
      B := Matrix(2,2,[1,5,-5,-2]);
      C := Matrix(2,2,[4,0,0,4]);
    when 3:
      p := 7;
      B := Matrix(2,2,[1,3,-1,-2]);
    when 4:
      p := 23;
      B := Matrix(2,2,[1,-6,12,-2]);
      C := Matrix(2,2,[2,0,0,2]);
    when 5:
      p := 11;
      B := Matrix(2,2,[2,4,1,-3]);
    when 6:
      p := 29;
      B := Matrix(2,2,[1,-7,-12,-2]);
      C := Matrix(2,2,[16,0,0,16]);
    when 7:
      p := 59;
      B := Matrix(2,2,[9,15,-10,-10]);
      C := Matrix(2,2,[4,0,0,4]);
    else:
      error "Index out of range 1..7";
  end case;
  if ndx in [1,3,5] then
    return p, sub<GL(2,p) | A, B >;
  else
    return p, sub<GL(2,p) | A, B, C >;
  end if;
end function;


//==============================================================================
intrinsic ZassenhausNearfield(n::RngIntElt) -> NfdZss
{Create the irregular nearfield number n)}

  requirerange n, 1, 7;
  p, S := irrNF(n);
  K := GF(p,2);
  E, phi := VectorSpace(K,PrimeField(K));

  mu := AssociativeArray(E);
  omega := phi(K!1);
  for x in S do mu[omega*x] := x; end for;

  NF := New(NfdZss);
  NF`ndx    := n;
  NF`p      := p;
  NF`q      := p;
  NF`gf     := K;
  NF`prim   := PrimitiveElement(K);
  NF`sz     := p;
  NF`phi    := phi;
  NF`mu     := mu;
  NF`matgrp := S;
  NF`psi    := map< S -> NF | x :-> (omega*x)@@phi, y :-> mu[phi(y`elt)] >;

  return NF;

end intrinsic;
//------------------------------------------------------------------------------

sameNF := "Elements must belong to the same nearfield";
procedure op_mutate(~x, ~y, op) op(~x`elt, ~y`elt); end procedure;


//==============================================================================
intrinsic '+' (x::NfdElt, y::NfdElt) -> NfdElt
{x + y}
  require x`parent eq y`parent: sameNF;
  return Element(x`parent,x`elt+y`elt);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic '+:=' (~x::NfdElt, ~y::NfdElt)
{x +:= y}
  require x`parent eq y`parent: sameNF;
  op_mutate(~x, ~y, '+:=');
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic '-' (x::NfdElt, y::NfdElt) -> NfdElt
{x - y}
  require x`parent eq y`parent: sameNF;
  return Element(x`parent,x`elt-y`elt);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic '-' (x::NfdElt) -> NfdElt
{-x}
  return Element(x`parent,-x`elt);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic '-:=' (~x::NfdElt, ~y::NfdElt)
{x +:= y}
  require x`parent eq y`parent: sameNF;
  op_mutate(~x, ~y, '-:=');
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic '*' (n::RngIntElt, y::NfdElt) -> NfdElt
{Left scalar multiple of a nearfield element y}
  N := y`parent;
  m := n mod N`p;
  return Element(N, m*y`elt);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic '*' (x::NfdElt, n::RngIntElt) -> NfdElt
{Right scalar multiple of a nearfield element x}
  N := x`parent;
  m := n mod N`p;
  return Element(N, m*x`elt);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic '*:=' (~x::NfdElt, ~y::NfdElt)
{x *:= y}
  require x`parent eq y`parent: sameNF;
  op_mutate(~x, ~y, '*:=');
end intrinsic;
//------------------------------------------------------------------------------

reg_mult := function(N,w,u)

  v := N`v;
  if v eq 1 then return w*u; end if;
  q := N`q;
  s := Log(N`prim,u) mod N`v;
  e := N`rho[s+1];

  return w^e*u;

end function;

irreg_mult := function(N,w,u);
  phi := N`phi;
  A := N`mu[phi(w)];
  B := N`mu[phi(u)];
  return (phi(N`gf!1)*A*B)@@phi;
end function;


//==============================================================================
intrinsic '*' (x::NfdElt, y::NfdElt) -> NfdElt
{x * y}
  require x`parent eq y`parent: sameNF;

  N := x`parent;
  K := N`gf;
  w := x`elt;
  u := y`elt;
  if IsZero(w) or IsZero(u) then return Zero(N); end if;
  if IsOne(w) then return y; end if;
  if IsOne(u) then return x; end if;
  pr := New(NfdElt);
  pr`parent := N;
  pr`elt := Type(N) eq NfdDck select reg_mult(N,w,u) else irreg_mult(N,w,u);
  return pr;

end intrinsic;
//------------------------------------------------------------------------------

reg_inv := function(N,x)
  v := N`v;
  if v eq 1 then return x`elt^-1; end if;
  q := N`q;
  z := N`prim;
  s := Log(z,x`elt);
  e := N`rho[s mod v + 1];
  r := Solution(e,-s,q^v-1);
  return z^r;
end function;

irreg_inv := function(N,x)
  phi := N`phi;
  A := N`mu[phi(x`elt)];
  return (phi(N`gf!1)*A^-1)@@phi;
end function;


//==============================================================================
intrinsic Inverse(x::NfdElt) -> NfdElt
{x^-1}
  require not IsZero(x): "Cannot invert the zero element";

  N := x`parent;
  inv := New(NfdElt);
  inv`parent := N;
  inv`elt := Type(N) eq NfdDck select reg_inv(N,x) else irreg_inv(N,x);
  return inv;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic '/' (x::NfdElt, y::NfdElt) -> NfdElt
{The quotient x/y of nearfield elements x and y}

  require x`parent eq y`parent: sameNF;
  return x*Inverse(y);

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic '^' (x::NfdElt, n::RngIntElt) -> NfdElt
{The n-th power of nearfield element x}

  t := Identity(x`parent);
  if n lt 0 then x := Inverse(x); n := -n; end if;
  while n gt 0 do
    if IsOdd(n) then
      t *:= x;
      if n eq 1 then break; end if;
    end if;
    x *:= x;
    n := n div 2;
  end while;
  return t;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic '^' (x::NfdElt, y::NfdElt) -> NfdElt
{The conjugate of x by y}

  return Inverse(y)*x*y;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic PrintNamed(N::NfdDck, level::MonStgElt, name::MonStgElt)
{Print description of the nearfield N}
  msg :=
    Sprintf("Nearfield %o of Dickson type defined by the pair",
    name);
  if level eq "Minimal" then
    printf msg * " (%o, %o)", N`q, N`v;
  elif level eq "Magma" then
    printf "DicksonNearfield(%o,%o)", N`q,N`v;
  else
    printf msg * " (%o, %o)\nOrder = %o", N`q ,N`v,#N;
  end if;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic PrintNamed(N::NfdZss, level::MonStgElt, name::MonStgElt)
{Print description of the nearfield N}
  msg :=
    Sprintf("Irregular nearfield %o with Zassenhaus number",
    name);
  if level eq "Minimal" then
    printf msg * " %o", N`ndx;
  elif level eq "Magma" then
    printf "ZassenhausNearfield(%o)", N`ndx;
  else
    printf msg * " %o\nOrder = %o", N`ndx, #N;
  end if;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic  '#' (N::Nfd) -> RngIntElt
{Cardinality of the nearfield N}
  return #(N`gf);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic  Cardinality(N::Nfd) -> RngIntElt
{Cardinality of the nearfield N}

  return #(N`gf);

 end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Parent(x::NfdElt) -> Nfd
{Return the parent of the nearfield element x}
  return x`parent;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Print(x::NfdElt)
{Print a nearfield element x}
  printf "%o", x`elt;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Hash(x::NfdElt) -> RngIntElt
{Return the hash value for a nearfield element x}

  return Hash(Parent(x)`gf);

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic '!' (N::Nfd, x::FldFinElt) -> NfdElt
{Coerce a finite field element x into the nearfield N}
  return Element(N,x);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Element(N::Nfd, x::FldFinElt) -> NfdElt
{Create a nearfield element from a finite field element}

  flag, y := IsCoercible(N`gf,x);
  require flag: "Finite field element is not in the carrier" *
    " set of the nearfield";
  X := New(NfdElt);
  X`parent := N;
  X`elt    := y;
  return X;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic IsCoercible(N::Nfd, x::Any) -> BoolElt, Any
{True iff the finite field element x is coercible
 into the nearfield N}

  M := Parent(x);
  if Type(M) eq Type(N) and M eq N then
    return true, x;
  end if;
  flag, y := IsCoercible(N`gf,x);
  if flag then
    return true, Element(N,y);
  else
    return false, "Illegal coercion";;
  end if;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ElementToSequence(x::NfdElt) -> []
{Create a sequence from an element x of a nearfield}

    return ElementToSequence(x`elt);

 end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic 'in'(x::Any, N::Nfd) -> BoolElt
{True iff the element x is in the nearfield N}

  M := Parent(x);
  return Type(M) eq Type(N) and M eq N;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Random(N::Nfd) -> NfdElt
{Create a random element of the nearfield N}

  X        := New(NfdElt);
  X`parent := N;
  X`elt    := Random(N`gf);
  return X;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Identity(N::Nfd) -> NfdElt
{Create the multiplicative identity of the nearfield N}

  X        := New(NfdElt);
  X`parent := N;
  X`elt    := (N`gf)!1;
  return X;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Zero(N::Nfd) -> NfdElt
{Create the additive identity of the nearfield N}

  X        := New(NfdElt);
  X`parent := N;
  X`elt    := (N`gf)!0;
  return X;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic IsZero(x::NfdElt) -> BoolElt
{True if x is the additive identity of the nearfield N}

  return x`elt eq (x`parent`gf)!0;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic IsIdentity(x::NfdElt) -> BoolElt
{True if x is the multiplicative identity of the nearfield N}

  return x`elt eq (x`parent`gf)!1;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic 'eq' (x::NfdElt, y::NfdElt) -> BoolElt
{x eq y}

  require x`parent eq y`parent: sameNF;
  return x`elt eq y`elt;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic 'ne' (x::NfdElt, y::NfdElt) -> BoolElt
{x ne y}

  require x`parent eq y`parent: sameNF;
  return x`elt ne y`elt;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic IsUnit(x::NfdElt) -> BoolElt
{True if the nearfield element x is a unit}

  return x`elt ne (x`parent`gf)!0;

end intrinsic;
//------------------------------------------------------------------------------

matrixUnitGroup := function(N)
  K := N`gf;
  z := K.1;
  v := N`v;
  phi := N`phi;
  zeta := N`prim;
  E := Image(phi);
  n := Dimension(E);
  F<x> := BaseRing(E);
  basis := [Element(N,z^i) : i in [0..n-1]];
  a := Element(N,zeta^v);
  A := Matrix(F,n,n,[phi((x*a)`elt) : x in basis]);
  b := Element(N,zeta);
  B := Matrix(F,n,n,[phi((x*b)`elt) : x in basis]);
  G := sub< GL(E) | A, B >;
  G`Order := #N-1;

  q := N`q;
  psi_inv := function(y)
    s := Log(zeta,y`elt);
    t := s mod v + 1;
    i := N`twist[t];
    e := N`rho[t];
    j := (s - (e-1) div (q-1)) div v;
    return B^i*A^j;
  end function;

  omega := phi(K!1);
  psi := map< G -> N | x :-> (omega*x)@@phi, y :-> psi_inv(y) >;

  return G, psi;
end function;


//==============================================================================
intrinsic UnitGroup(N::Nfd) -> GrpMat, Map
{The unit group of the nearfield N returned as
 a matrix group M and a map from M to N}

  if not assigned N`matgrp then
    U, psi := matrixUnitGroup(N);
    N`matgrp := U;
    N`psi := psi;
  end if;
  return N`matgrp, N`psi;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic UnitGroup(`GrpPerm, N::Nfd) -> GrpPerm
{The unit group of the nearfield N returned as
 a permutation group}
  U := UnitGroup(N);
  require #U le 10^8 : "Unit group is too large to construct as a
  permutation group";
  _, H, _ := CosetAction(U,sub<U|>);
  return H;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic UnitGroup(`GrpPC, N::NfdDck) -> GrpPC
{The unit group of the nearfield N returned as a PC-group}
  U := UnitGroup(N);
  LMGInitialise(U);
  _, pcg, _ := LMGSolubleRadical(U);
  return pcg;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic UnitGroup(`GrpPC, N::NfdZss) -> GrpPC
{The unit group of the nearfield N returned as a PC-group}
  require N`ndx in [1..4]: "Unit group not soluble";
  U := UnitGroup(N);
  LMGInitialise(U);
  _, pcg, _ := LMGSolubleRadical(U);
  return pcg;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Order(x::NfdElt) -> RngIntElt
{Order of the unit x of a nearfield}
  require IsUnit(x): "Attempting to find the order of a non-unit";
  N := x`parent;
  one := Identity(N);
  if x eq one then return 1; end if;
  n := #N-1;
  ord := 1;
  facts := Factorisation(n);
  for term in facts do
    p, e := Explode(term);
    y := x^(n div p^e);
    f := 0;
    while y ne one do
      y := y^p;
      f +:= 1;
    end while;
    ord *:= p^f;
  end for;

  return ord;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic AffineGroup(N::Nfd) -> GrpMat
{The sharply two-transitive affine group associated with a
 nearfield, returned as a matrix group}

  U := UnitGroup(N);
  F := BaseRing(U);
  one := Matrix(F,1,1,[1]);
  gens := [DiagonalJoin(U.i,one) : i in [1..Ngens(U)]];
  n := Dimension(U);
  C := DiagonalJoin(U!1,one);
  C[n+1,1] := 1;
  Append(~gens,C);
  G := sub<GL(n+1,F) | gens >;
  G`Order := #N*(#N-1);

  return G;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic AffineGroup(`GrpPerm, N::Nfd) -> GrpPerm
{The sharply two-transitive affine group associated with a
 nearfield, returned as a permutation group}

  G := AffineGroup(N);
  S := sub<G | [G.i : i in [1..Ngens(G)-1]] >;
  require Index(G, S) le 10^7 :
             "Degree of permutation group is too large";
  _, H, _ := CosetAction(G, S);
  H`Order := #N*(#N-1);
  return H;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic AffineGroup(`GrpPC, N::NfdDck) -> GrpPC
{The sharply two-transitive affine group associated with a
 regular nearfield, returned as a PC-group}
  A := AffineGroup(N);
  LMGInitialise(A);
  _, pcg, _ := LMGSolubleRadical(A);
  return pcg;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic AffineGroup(`GrpPC, N::NfdZss) -> GrpPC
{The sharply two-transitive affine group associated with an
 irregular nearfield, returned as a PC-group}
  require N`ndx in [1..4]: "Unit group not soluble";
  A := AffineGroup(N);
  LMGInitialise(A);
  _, pcg, _ := LMGSolubleRadical(A);
  return pcg;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic PrimeField(N::Nfd) -> FldFin
{Return the prime field of the nearfield N}

  return GF(N`p);

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Kernel(N::Nfd) -> FldFin
{Return the kernel of the nearfield N as a finite field}

  return GF(N`q);

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ExtendedUnitGroup(N :: NfdDck) -> GrpMat
{The extended unit group of a Dickson nearfield}
  U, _ := UnitGroup(N);
  z := (N`gf).1;
  q := N`q;
  phi := N`phi;
  n := Dimension(U);
  C := Matrix(n,n,[phi(z^(q*i)) : i in [0..n-1]]);
  G := sub< GL(n,BaseRing(U))| U, C >;
  G`Order := Order(U)*N`v;
  return G;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic 'eq' (N::NfdDck, M::NfdDck) -> BoolElt
{N eq M}
  q := N`q;
  v := N`v;
  if q ne M`q or v ne M`v then return false; end if;
  m := (q^v-1) div v;
  return (N`prim)^m eq (M`prim)^m;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic 'eq' (N::NfdZss, M::NfdZss) -> BoolElt
{N eq M}
  return N`ndx eq M`ndx;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic 'ne' (N::NfdDck, M::NfdDck) -> BoolElt
{N ne M}
  q := N`q;
  v := N`v;
  if q ne M`q or v ne M`v then return true; end if;
  m := (q^v-1) div v;
  return (N`prim)^m ne (M`prim)^m;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic 'ne' (N::NfdZss, M::NfdZss) -> BoolElt
{N ne M}
  return N`ndx ne M`ndx;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic IsIsomorphic(N1::NfdDck, N2::NfdDck) -> BoolElt, Map
{Test whether the regular nearfields N1 and N2 are
 isomorphic.  If they are, return an isomorphism}
  q := N1`q;
  v := N1`v;
  if q ne N2`q or v ne N2`v then
    return false, _;
  end if;
  m := (q^v - 1) div v;
  d1 := (N1`prim)^m;
  d2 := (N2`prim)^m;
  if MinimalPolynomial(d1) ne MinimalPolynomial(d2) then
    return false, _;
  end if;
  s := Log(d1,d2);
  _,t,_ := XGCD(s,q^v-1);
  return true, map<N1->N2 |
        x :-> Element(N2,((x`elt)^s)), y :-> Element(N1,((y`elt)^t)) >;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic AutomorphismGroup(N::NfdDck) -> GrpPerm, Map
{The automorphism group A of the regular nearfield N and
 a map giving the action of A on N}
  if #N eq 9 then return Sym(3),_; end if;
  v := N`v;
  g := Order(ResidueClassRing(v)!N`p);
  ord := v*N`h div g;
  A := CyclicGroup(ord);
  psi := map< car<A,N> -> N | pi :-> Element(N,(pi[2]`elt^(N`p^(g*alpha))))
       where alpha is (1^pi[1]-1) mod ord >;
  return A,psi;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic AutomorphismGroup(N::NfdZss) -> GrpPerm
{The automorphism group A of the irregular nearfield N and
 a map giving the action of A on N}
  order := [4, 2, 3, 1, 5, 2, 1];
  return CyclicGroup(order[N`ndx]);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic SubConstr(N::NfdDck, E::SeqEnum) -> NfdDck, Map
{The sub-nearfield of the Dickson nearfield N generated by E}
  if #E gt 0 and (Type(E[1]) ne NfdElt or E[1]`parent ne N) then
    return "elements on RHS must be in the nearfield", _;
  end if;
  v := N`v;
  h := N`h;
  L, g := sub< N`gf | [e`elt : e in E] >;
  _, p, lambda := IsPrimePower(#L);
  I := (#N - 1) div (p^lambda - 1);
  if I eq 0 then I := v; end if;
  k := GCD(h*I,lambda);
  w := lambda div k;
  K := GF(p^lambda);
  zeta := K!(N`prim^I);
  M := nearField(p^k,w,K,zeta : LargeMatrices := N`sz eq p);
  f := map< M -> N | x :-> Element(N,(g(x`elt))) >;
  return M, f;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic SubConstr(N::NfdDck, x::Any) -> NfdDck, Map
{The sub-nearfield of the Dickson nearfield N generated by x}
  if (Type(x) ne NfdElt) or (x`parent ne N) then
    return "the element must belong to the nearfield", _;
  end if;
  return SubConstr(N,[x]);
end intrinsic;
//------------------------------------------------------------------------------

multiplicationTable := function( N )
  A := AssociativeArray();
  K := N`gf;
  for x in K do for y in K do
      A[<x,y>] := (Element(N,x)*Element(N,y))`elt;
  end for; end for;
  return A;
end function;


//==============================================================================
intrinsic ProjectivePlane( N::Nfd : Check := false) -> PlaneProj, PlanePtSet, PlaneLnSet
{The finite projective plane coordinatised by the nearfield N}
  K := N`gf;
  pts := {@ [K| 1,x,y] : x,y in K @} join
         {@ [K| 0,1,y] : y in K @} join {@ [K| 0,0,1] @};
  lset := {@ @};
  M := multiplicationTable(N);

  for m in K do
    for b in K do
      ln := { Index(pts,[K|1,x,M[<x,m>]+b]) : x in K };
      Include(~ln,Index(pts,[K| 0,1,m]) );
      Include(~lset,ln);
    end for;
  end for;

  for c in K do
    ln := { Index(pts,[K| 1,c,y]) : y in K };
    Include(~ln, Index(pts,[K| 0,0,1]) );
    Include(~lset,ln);
  end for;

  ln := { Index(pts,[K| 0,1,y]) : y in K };
  Include(~ln,Index(pts,[K| 0,0,1]));
  Include(~lset,ln);

  return FiniteProjectivePlane< #pts | lset : Check := Check>;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic HughesPlane( N::Nfd : Check := false) -> PlaneProj, PlanePtSet, PlaneLnSet
{The Hughes plane based on the nearfield N }
  if Type(N) eq NfdDck then
    require N`v eq 2 :
       "the nearfield must have rank 2 over its kernel";
  end if;
  K := N`gf;
  points := {@ [K| 1,x,y] : x,y in K @} join
         {@ [K| 0,1,y] : y in K @} join {@ [K| 0,0,1] @};
  M := multiplicationTable(N);

  normalise := function(v)
    if not IsZero(v[1]) then 
      a := Element(N,v[1])^-1;
      b := a`elt; 
      return [K| 1,M[<v[2],b>],M[<v[3],b>]]; 
    end if;
    if not IsZero(v[2]) then 
      a := Element(N,v[2])^-1;
      return [K| 0,1,M[<v[3],a`elt>]]; 
    end if;
    return [K|0,0,1];
  end function;

  apply := func< v,A |
    [ &+[ M[<A[i,j],v[j]>] : j in [1..#v]] : i in [1..#v]] >;

  lines := {@ @};
  ln := { [K| 1,-1,z] : z in K };
  Include(~ln, [K| 0,0,1] );
  line := { Index(points,v) : v in ln };
  Include(~lines, line);

  f := N`prim;
  ln := { [K| 1,-1-M[<f,z>],z] : z in K };
  Include(~ln, normalise([K| 0,f,-1]) );
  line := { Index(points,v) : v in ln };
  Include(~lines, line);

  n := #points;
  S := Sym(n);
  gens := [S|];
  for g in Generators(GL(3,N`q)) do
   perm := [];
   for i := 1 to n do
     v := normalise(apply(points[i],g));
     Append(~perm,Index(points,v));
   end for;
   Append(~gens,S!perm);
 end for;

  H := sub< S | gens >;
  L := &join[ ln^H : ln in lines ];

  return FiniteProjectivePlane< n | L : Check := Check >;

end intrinsic;
//------------------------------------------------------------------------------

