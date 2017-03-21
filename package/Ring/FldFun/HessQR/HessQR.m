freeze;
//

declare type RngExtVIdl;

declare attributes RngExtVIdl:
     Parent,
     Element;


/* ExtV:
   From Florian Hess's PhD, page 29 ff (2.10 ...)
   Let R be a Dedekind ring (although, I think Z is what I have in mind)
   Define R<x> \subset Q(R)(x) as follows
     R<x> := \{ f/g \in Q(R)(x) | cont f/ cont g \subseq R\}
   and
     cont (f) = ideal<R| coeffs. from f>
     Q(R) the field of fractions of R
   
   This is a PID. Any ideal in R<x> be be generated by a polynomial
   of degree <= 1. Furthermore, it can be represented by an ideal
   of R.

   What we need is
     - ideal operations in R<x> 
     - Round2 over R<x>
     - some details.

*/       

intrinsic Generators(A::RngInt) -> []
  {The generators of the ideal A.}
  return [Generator(A)];
end intrinsic;

intrinsic Factorisation(A::RngInt) -> []
  {The ideal factorisation of the ideal A.}
  return [< ideal<Z|x[1]>, x[2]> : x in Factorisation(Generator(A))] 
    where Z := Integers();
end intrinsic;
    
// Accoring to FH: the ideal groups of R and R<x> are isomorphic, the
// ideal A in R is mapped onto a PID generated by a polynomial with
// content A.
// Reversely, I think, given a PID in R<x>, I can find the preimage in 
// R by just computing the contents...
// This will be used as the main algorithmic tool.
intrinsic Ideal(l::RngExtVElt) -> RngExtVIdl
  {The principal ideal generated by l}
  // integral ideals only - ideal<Z|3> / ideal<Z|4> dies.
  I := New(RngExtVIdl);
  I`Parent := Parent(l);
  a := Content(l);
  a := Generators(a);
  assert #a le 2;
  I`Element := Parent(I)!Polynomial(a);
  return I;
end intrinsic;

intrinsic '+'(A::RngExtVIdl, B::RngExtVIdl) -> RngExtVIdl
  {The sum (gcd) of A and B.}
  a := Content(A`Element) + Content(B`Element);
  I := New(RngExtVIdl);
  I`Parent := A`Parent;
  a := Generators(a);
  assert #a le 2;
  I`Element := Parent(A)!Polynomial(a);
  return I;
end intrinsic;

intrinsic Ideal(l::[RngExtVElt]) -> RngExtVIdl
  {The ideal generated by the elements in l}
  return &+ [ Ideal(x) : x in l];
end intrinsic;

intrinsic Gcd(A::RngExtVIdl, B::RngExtVIdl) -> RngExtVIdl
  {The sum (gcd) of A and B.}
  return A+B;
end intrinsic;

intrinsic Print(x::RngExtVIdl, level::MonStgElt)
   {}
   printf "%o", x`Element;
end intrinsic;

intrinsic 'in'(x::., X::RngExtV) -> BoolElt
   {Returns true if x is in X.}
   return false;
end intrinsic;

intrinsic Parent(x::RngExtVIdl) -> RngExtV
   {}
   return x`Parent;
end intrinsic;

intrinsic Content(x::RngExtVElt) -> .
  {The content of x as an ideal of the coefficient ring}
  n := Numerator(x);
  d := Denominator(x);
  return ideal<CoefficientRing(n) | Eltseq(n)> 
       / ideal<CoefficientRing(n) | Eltseq(d)>;
end intrinsic;

intrinsic GCD(x::RngExtVElt, y::RngExtVElt) -> RngExtVElt
  {The GCD of x and y}
  H := Parent(x);
  // if H is defined over an Euc, then H is Euc as well
  // clumsy, but by the above reasoning...
  c := Content(x) + Content(y);
  c := Generators(c);
  assert #c le 2;
  return Parent(x)!Polynomial(c);
end intrinsic;

intrinsic Factorisation(A::RngExtVIdl) -> []
  {The factorisation of A}
  a := Content(A`Element);
  a := Factorisation(a);
  return [ < Ideal(Parent(A)!Generators(x[1])), x[2]> : x in a];
end intrinsic;

intrinsic Factorisation(A::RngExtVElt) -> []
  {The factorisation of the principal ideal generated by A}
  return Factorisation(Ideal(A));
end intrinsic;

/* we need to work in R<x> orders, ie. free R<x> modules in some
   function field F.
   An order here is a RngExtVExt
   We distinguish two types:
     EquationOrder (given via a polynomial AND a map from
       the FoF of the equation order into some function field
       (and back))  
     Extension (given via a basis transformtation wrt some smaller
       order.
*/
declare type RngExtVExt;
declare attributes RngExtVExt: 
  Type, /* string: EqOrd, ExtOrd */
  Base, /* the base ExtV ring */  
  Map,  /* to the function field */
  Trafo, Den, /* Matrix/Den = transformation to new order */  
  iTrafo, iDen, /* the inverses of Trafo/den */  
  SubOrd, /* the smaller order... */
  EqOrd;  /* all the way down */  

intrinsic Print(x::RngExtVExt, level::MonStgElt)
  {}
  if x`Type eq "EqOrd" then
    x`EqOrd`Map;
  else
    "Extension by", x`Trafo, "*1/", x`Den, "of", x`SubOrd;
  end if;
end intrinsic;

intrinsic EquationOrder(R::RngExtV, F::RngFunOrd) -> RngExtVExt
  {The equation order over R defined by the defining polynomial of F.}
  A := New(RngExtVExt);
  A`Type := "EqOrd";
  A`Base := R;
  A`Map := F;
  A`EqOrd := A;
  return A;
end intrinsic;

intrinsic '!'(R::FldFunRat, f::RngExtVElt) -> FldFunRatElt
  {}
  return (R!Numerator(f))/(R!Denominator(f));
end intrinsic;

intrinsic Matrix(K::FldFunRat, M::AlgMatElt[RngExtV]) -> Mtrx
  {The matrix M coerced over F}
  return Matrix(K, Nrows(M), Ncols(M), [K!x : x in Eltseq(M)]);
end intrinsic;

intrinsic FieldOfFractions(R::RngExtV) -> Fld
  {The field of fractions of R, usually a rational function field.}
  return Parent(Numerator(R.1)/Denominator(R.1));
end intrinsic;

intrinsic MyExtOrder(A::RngExtVExt, M::Mtrx, d::RngElt:Simplify := false, iTrafo := false, iDen := false) -> RngExtVExt
  {}
  K := FieldOfFractions(CoefficientRing(M));
  M := Matrix(K, M);
  d := K!d;
  if iTrafo cmpeq false then 
    iM := M^-1;
  else
    iM := iTrafo;
  end if;
  B := New(RngExtVExt);
  B`Type := "ExtOrd";
  B`Base := A`Base;
  if A`Type eq "EqOrd" then
    B`EqOrd := A;
    B`SubOrd := A;
    B`Trafo := M;
    B`iTrafo := iM;
    B`Den := d;
    B`iDen := 1/d;
  else
    B`EqOrd := A`EqOrd;
    if Simplify then
      B`SubOrd := A`SubOrd;
      B`Trafo := M*A`Trafo;
      B`iTrafo := A`iTrafo*iM;
      B`Den := d*A`Den;
      B`iDen := (1/d)*A`iDen;
    else
      B`SubOrd := A;
      B`Trafo := M;
      B`Den := d;
      B`iTrafo := iM;
      B`iDen := 1/d;
    end if;
  end if;
  return B;
end intrinsic;

intrinsic SimplifyOrder(A::RngExtVExt) -> RngExtVExt
  {For a chain of orders, A extending B extending ... extending C, return A as a direct extension of C.}
  if A`Type eq "EqOrd" then
    return A;
  end if;
  M := A`Trafo;
  iM := A`iTrafo;
  d := A`Den;
  id := A`iDen;
  A := A`SubOrd;
  while A`Type ne "EqOrd" do
    M := M*A`Trafo;
    iM := A`iTrafo * iM;
    d := d*A`Den;
    id := id*A`iDen;
    A := A`SubOrd;
  end while;
  
  return MyExtOrder(A, M, d:iTrafo := iM, iDen := id);
end intrinsic;

intrinsic ResidueClassField(p::RngExtVIdl) -> Fld, Map
  {The residue class field of the prime ideal p.}
  H := Parent(p);
  R := CoefficientRing(H);
  if R eq Integers() then
    function preIm(y)
      n := Numerator(y);
      d := Denominator(y);
      n := Polynomial(Integers(), Eltseq(n));
      d := Polynomial(Integers(), Eltseq(d));
      return (H!n)/(H!d);
      // I hope that denominators of rational function field elements
      // are always normlized to be monic => content should be 1 and
      // the divison exact.
    end function;
    C := FunctionField(ResidueClassField(Integers(), Content(p`Element)));
    mC := map<Parent(p) -> C | x:-> (C!Numerator(x))/(C!Denominator(x)),
                               y:-> preIm(y)>;
    return C, mC;
  else
    error "not implemented (yet)";
  end if;
end intrinsic;

intrinsic ResidueClassField(R::RngExtV, p::RngExtVIdl) -> Fld, Map
  {The residue class field of the prime ideal p.}
  return ResidueClassField(p);
end intrinsic;

function ExtVEltToFldFun(a, A)
  while A`Type eq "ExtOrd" do
    a := Matrix(CoefficientRing(A`Trafo), a);
    a := a*A`Trafo;
    a := a/A`Den;
    A := A`SubOrd;
  end while;
  return A`Map!Eltseq(a*d)/d where d := LCM([Denominator(x) : x in Eltseq(a)]);
end function;

function ExtVEltFromFldFun(a, A)
  a := Matrix([Eltseq(a)]);
  lA := [];
  while A`Type ne "EqOrd" do
    Append(~lA, A);
    A := A`SubOrd;
  end while;
  for i := #lA to 1 by -1 do
    a := Matrix(CoefficientRing(lA[i]`iTrafo), a);
    a := a*lA[i]`iTrafo;
    a := a/lA[i]`iDen;
  end for;
  return a;
end function;

function ExtVEltMult(a, b, A)
  a := ExtVEltToFldFun(a, A);
  b := ExtVEltToFldFun(b, A);
  return ExtVEltFromFldFun(a*b, A);
end function;

intrinsic BaseRing(R::RngExtV) -> RngUPol
  {The base (coefficient) ring of R.}
  return CoefficientRing(Numerator(R.1));
end intrinsic;
intrinsic Generators(a::RngExtVIdl) -> RngExtVElt
  {Generators for the ideal a as a sequence.}
  return [a`Element];
end intrinsic;
intrinsic Generator(a::RngExtVIdl) -> RngExtVElt
  {A generator for the principal ideal a.}
  return a`Element;
end intrinsic;
intrinsic IsPrincipalIdealDomain(R::RngExtV) -> BoolElt
  {Tests if R is a PID.}
  // stricly only true if the coefficient ring is Dedekind - which I cannot
  // test.
  return true;
end intrinsic;
intrinsic IsPrincipal(a::RngExtVIdl) -> BoolElt, RngExtVElt
  {Tests if the ideal a is principal.}
  return true, Generator(a);
end intrinsic;

intrinsic pRadical(A::RngExtVExt, p::RngExtVIdl) -> Mtrx
  {Computes a basis for the p-radical of A}

  k, mk := ResidueClassField(p);
  n := Degree(A`EqOrd`Map);

  K := CoefficientRing(A`EqOrd`Map);

  b := [M[i] : i in [1..n]] where M := IdentityMatrix(K, n);
  A := [ Eltseq(Matrix(k, ExtVEltMult(i, j, A))) : i, j in b];
  A := Algebra<k, n|A>;
  J := JacobsonRadical(A);
  b := Basis(J);
  ChangeUniverse(~b, A);
  g := [];
  for i in b do
    e := Eltseq(i);
    e := [ x@@mk : x in e];
    Append(~g, e);
  end for;
  for i in [1..n] do
    e := Generator(p)*IdentityMatrix(Parent(p), n)[i];
    Append(~g, Eltseq(e));
  end for;
  g := Matrix(g);
  g := EchelonForm(g);
  g := Submatrix(g, 1, 1, n, n);
  assert Determinant(g) ne 0;
  return g;
end intrinsic;

intrinsic Degree(A::RngExtVExt) -> RngIntElt
  {The degree of the finite extension A}
  return Degree(A`EqOrd`Map);
end intrinsic;

intrinsic CoefficientRing(A::RngExtVExt) -> RngExtV
  {The coefficient ring of A.}
  return A`Base;
end intrinsic;

function ExtVEltRepMat(a, H)
  K := CoefficientRing(H`EqOrd`Map);
  M := IdentityMatrix(K, Degree(H));
  M := Matrix([ ExtVEltMult(a, M[i], H) : i in [1..Degree(H)]]);
  return Matrix(CoefficientRing(H), M);
end function;

intrinsic Matrix(K::FldFunRat, m::ModMatRngElt[RngExtV]) -> Mtrx
  {The vector space element m over the extended valuation ring as a matrix over K}
  return Matrix(K, Nrows(m), Ncols(m), [K!x : x in Eltseq(m)]);
end intrinsic;

intrinsic 'div'(a::RngExtVElt, b::RngExtVElt) -> RngExtVElt
  {Exact division of a by b}
  return a/b;
end intrinsic;

intrinsic MultiplicatorRing(g::Mtrx, A::RngExtVExt) -> RngExtVExt
  {The ring of multipliers of the ideal represented by the bais matrix g in A.}
  // g is the basis of an ideal in A (the rows of g are basis elements)
  //
  // same as for number fields:
  // - invert the basis g (pseudo-invert?)
  // - get the representation matrices for the basis elements of g
  // - assemble them in a big matrix
  // - hermite reduce
  // - invert (?)
  // - multiply with the basis matrix

  K := CoefficientRing(A`EqOrd`Map);
  n := Degree(A);
  gi, d := PseudoInverse(g);
  assert g*gi eq d*IdentityMatrix(CoefficientRing(g), n);
  m := [];
  for i in [1..n] do
    e := Matrix(FieldOfFractions(K), Matrix([Eltseq(g[i])]));
    r := ExtVEltRepMat(e, A);
    r := r*gi;
    r := Matrix(Nrows(r), Ncols(r), [x / d : x in Eltseq(r)]);
    Append(~m, Transpose(r));
  end for;
  m := Matrix(m);
  m := EchelonForm(m);
  m := Submatrix(m, 1, 1, n, n);
  mi, dm := PseudoInverse(m);
  assert m*mi eq dm*IdentityMatrix(CoefficientRing(g), n);
  g := Gcd(Eltseq(mi) cat [dm]);
  if g ne 1 then
    mi := Matrix(Nrows(mi), Ncols(mi), [x/g : x in Eltseq(mi)]);
    dm := dm/g;
  end if;
  if g eq 1 and mi eq 1 then
    return A;
  else
    return  MyExtOrder(A, Transpose(mi), dm:Simplify);
  end if;
end intrinsic;

intrinsic 'eq'(A::RngExtVExt, B::RngExtVExt) -> BoolElt
  {Tests if A equals B}
  if not A`EqOrd cmpeq B`EqOrd then
    return false;
  end if;
  if A`Type eq "ExtOrd" then
    T := A`Trafo;
    d := A`Den;
    A := A`SubOrd;
    while A`Type ne "EqOrd" do
      T := T*A`Trafo;
      d := d*A`Den;
      A := A`SubOrd;
    end while;
  else
    T := false;
    d := 1;
  end if;
  if B`Type eq "ExtOrd" then
    iT := B`iTrafo;
    d := d*B`iDen;
    B := B`SubOrd;
    while B`Type ne "EqOrd" do
      iT := B`iTrafo*iT;
      d := d*B`iDen;
      B := B`SubOrd;
    end while;
    if T cmpne false then
      T := T*iT;
    else
      T := iT;
    end if;
  end if;
  if T cmpeq false then
    return true;
  end if;

  T := Matrix(FieldOfFractions(CoefficientRing(A`EqOrd`Map)), T)/d;
  return T eq 1;
end intrinsic;


intrinsic IntegralClosure(R::RngExtV, F::FldFun) -> Rng
  {The integral closure of R in V}

  f := DefiningPolynomial(F);
  // here we assume that f is monic and integral wrt. to the ExtV 
  // object. In particular, if f is monic and integral over Z[x] it should
  // work.

  f := Eltseq(f);
  f := [R!x : x in f];
  f := Polynomial(f);
  d := Discriminant(f);
  d := Factorisation(d);
  a := EquationOrder(R, EquationOrderFinite(F));
  for P in d do
    if P[2] le 1 then continue; end if;
    repeat
      e := a;
      a := MultiplicatorRing(pRadical(e, P[1]), e);
    until e eq a;
  end for;
  return a;
end intrinsic;  

intrinsic Basis(A::RngExtVExt) -> []
  {The basis of A as elements in the function field.}
  n := Degree(A);  
  M := IdentityMatrix(CoefficientRing(A`EqOrd`Map), n);  
  b := [];
  F := FunctionField(A`EqOrd`Map);
  for i in [1..n] do  
    Append(~b, F!Eltseq(ExtVEltToFldFun(M[i], A)));
  end for;
  return b;
end intrinsic;

intrinsic Basis(A::RngExtVExt, F::Rng) -> []
  {The basis of A as elements in F}
  return ChangeUniverse(Basis(A), F);
end intrinsic;

function H1(M, R) 
//intrinsic H1(M::Mtrx, R::Rng) -> Mtrx, Mtrx
//  {}
  // M over a rational function field, return the HNF over the Ring
  FM := CoefficientRing(M);
  try
    M := Matrix(R, M);
    d := 1;
  catch e
    // OK, simple coercion does not work, we'll have to work.
    if Type(R) eq RngUPol then
      F := FieldOfFractions(R);
      d := 1;
      for i in Eltseq(M) do
        d := Lcm(d, Denominator(F!i));
      end for;
      M := Matrix(R, d*M);
    elif Type(R) eq RngExtV then
      d := 1;
      F := FunctionField(CoefficientRing(R));
      m := [];
      for i in Eltseq(M) do
        Append(~m, Denominator(F!i));
      end for;
      d := Lcm(m);
      d := FM!d;
      m := [];
      for i in Eltseq(M) do
        Append(~m, R!(i*d));
      end for;
    else
      error "non-supported ring type";
    end if;
    M := Matrix(Nrows(M), Ncols(M), m);
  end try;

  N, T := EchelonForm(M);
  N := Matrix(FM, N);
  return N/d, T;
end function;

intrinsic 'meet'(A::RngExtVExt, B::RngFunOrd) -> Mtrx, RngExtVExt, RngFunOrd
  {The intersection of the rings A and B, computed as base changes for A (returned as the 2nd value) and B (3rd value) such that the bases are diagonal to each oher (1st value)}
 
  F := FunctionField(B);
  MA := Matrix([Eltseq(x) : x in Basis(A)]);
  MB := Matrix([Eltseq(x) : x in Basis(B, F)]);
  M := MA*MB^-1;
  TA := false;
  TB := false;
  repeat
    M, T := H1(M, A`Base);
    if TA cmpeq false then
      TA := T;
    else
      TA := T*TA;
    end if;
    if IsDiagonal(M) then break; end if;
    M, T := H1(Transpose(M), CoefficientRing(B));
    M := Transpose(M);
    if TB cmpeq false then
      TB := Transpose(T);
    else
      TB := TB*Transpose(T);
    end if;
  until IsDiagonal(M);
  if TA cmpeq false then
    TA := IdentityMatrix(CoefficientRing(A), Degree(A));
  end if;
  if TB cmpeq false then
    TB := IdentityMatrix(CoefficientRing(B), Degree(B));
  end if;

  //Order(B, TB^-1, 1) and MyExtOrder(A, TA, 1)
  //should have the same basis (well diagonal to each other possibly)
  //TODO: prove that is works. If it terminates, then the result is correct..
  return M, MyExtOrder(A, TA, 1), Order(B, TB^-1, CoefficientRing(B)!1);
end intrinsic;


/*
 <example>
   R := ExtendedValuationRing(Integers());
   F := FunctionField(Polynomial([PolynomialRing(Rationals())| [-1], [0, 0, 0, -4], [1]]));

   A := EquationOrder(R, EquationOrderFinite(F));
   p := Ideal(R!2);
   Nr := pRadical(A, p);
   a := MultiplicatorRing(Nr, A);
   n := pRadical(a, p);
   MultiplicatorRing(n, a);

   I := IntegralClosure(R, F);
   M := MaximalOrderFinite(F);
   d, i1, m1 := I meet M;
   Basis(i1);
   Basis(m1, F);
*/ 

