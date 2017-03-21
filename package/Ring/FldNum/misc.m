freeze;

intrinsic CoefficientRing(K::FldAlg) -> Rng
{The base field of K}
  return CoefficientField(K);
end intrinsic;

intrinsic IsNumberField(K) -> BoolElt
{Returns true iff K is a number field}
  return ISA(Category(K), FldNum);
end intrinsic;

intrinsic IsAlgebraicField(K) -> BoolElt
{Returns true iff K is an algebraic field}
  return ISA(Category(K), FldAlg);
end intrinsic;

intrinsic AbsoluteBasis(O::RngOrd) -> []
  {A Z-basis for O}
  return AbsoluteBasis(1*O);
end intrinsic;

/*
intrinsic Flat(a::FldAlgElt) -> [ ]
{The coefficients of a wrt. a Q-basis for its parent}
  c := Eltseq(a);
  while Universe(c) cmpne Rationals() do
    c := &cat [ Eltseq(a) : a in c];
  end while;
  return c;
end intrinsic;
*/

intrinsic IsSquarefree(I :: RngOrdIdl) -> BoolElt
{True iff the ideal I has no repeated factors}
  fact := Factorization(I);
  sf := forall{tup : tup in fact | tup[2] eq 1};
  return sf;
end intrinsic;

intrinsic DecompositionGroup(p :: RngOrdIdl:Partial := false) -> GrpPerm
{Computes the decomposition group of p.}
  M := Order(p);
  K := NumberField(M);

  // redo: if the automorphisms are known, use them!
  require IsAbsoluteField(K) and (Partial or IsNormal(K)): 
                 "K must be a absolute normal field";

  require IsPrime(p) : "p must be a prime ideal";
  // redo: require only p-maximal
  require MaximalOrder(K) eq M : "ideal and field are not compatible";

  G, M, L := AutomorphismGroup(K:Partial := Partial);
  U := sub<G| { x : x in G | ideal<Order(p)|L(x)(Generators(p))> eq p } >;

  return U;
  
end intrinsic;

intrinsic RamificationGroup(p :: RngOrdIdl, i:: RngIntElt) -> GrpPerm
{Computes the i-th ramification group of p (lower index).}
  M := Order(p);
  K := NumberField(M);

  require i ge -1 : "i must be >= -1";
  // redo: if the automorphisms are known, use them!
  require IsAbsoluteField(K) and IsNormal(K): 
                 "K must be a absolute normal field";

  require IsPrime(p) : "p must be a prime ideal";
  O := Order(p);
  // redo: require only p-maximal
  require MaximalOrder(K) eq O : "ideal and field are not compatible";

  G, _, L := AutomorphismGroup(K);
    
  U := sub<G| { x : x in G | 
        forall{y : y in Basis(O, O) | Valuation(O!(L(x)(y))-y, p) ge i+1} } >;

  return U;
  
end intrinsic;

intrinsic RamificationGroup(p :: RngOrdIdl) ->GrpPerm 
{Computes the ramification group of p.}
  return RamificationGroup(p, 1);
end intrinsic;  

intrinsic InertiaGroup(p :: RngOrdIdl) -> GrpPerm
{Computes the inertia group of p.}
  return RamificationGroup(p, 0);
end intrinsic;  

to_field := function(K, U:Partial := false)
  if Type(K) eq FldCyc and Type(U) eq GrpAb then
    G, Map:= CyclotomicAutomorphismGroup(K);
    mG, G := CosetAction(G, sub<G|>);
    U := U@mG;
    Map := Inverse(mG) * Map;
  else
    G,_, Map:= AutomorphismGroup(K:Partial := Partial);
  end if;
  pe := PrimitiveElement(K);
  if not IsSimple(K) then
    f, GG := CosetAction(G, sub<G|>);
    Map := Inverse(f)*Map;
    G := GG;
    U := f(U);
  end if;
  assert IsTransitive(G);
  rt := [pe@(g@Map) where _, g := IsConjugate(G, 1, i) : i in [1..#G]];

  if G eq U then
    i := SLPolynomialRing(Integers(), Degree(G));
    i := &+ [i.j : j in [1..Degree(G)]];
  else
    i := RelativeInvariant(G, U);
  end if;
  t := Polynomial([0,1]);
  all_t := {t};
  a,b := GetSeed();
  SetSeed(1,1);
  repeat
    r := { Evaluate(i, 
       [Evaluate(t, x) : x in PermuteSequence(rt, u)]) :
                                         u in Transversal(G, U)};
    repeat
      t := Polynomial([Random(2) : x in all_t] cat [1]);
    until t notin all_t;
    Include(~all_t, t);
  until #r eq #G div #U;
  SetSeed(a,b);
  f := &*[Polynomial([-s, 1]) : s in r];
  if #G eq Degree(K) then
    f := Polynomial(BaseField(K), f);
  else
    c := sub<K|Eltseq(f):Optimize>;
    f := Polynomial(c, f);
  end if;
  if not exists(x){x : x in r | sub<G| [g : g in G | x@(g@Map) eq x]> eq U} then
    error "cannot find correct embedding";
  end if;
  k := NumberField(f:Check := false);
  Embed(k, K, x);
  if #G ne Degree(K) then
    k := AbsoluteField(k);
    Embed(k, K, K!k.1);
  end if;

  return k;
end function;

intrinsic FixedField(K :: FldCyc, U :: GrpAb) -> FldNum, Map
{For a subgroup U of the CyclotomicAutomorphismGroup of K, compute the field fixed by U}
  
  // redo: if the automorphisms are known, use them!

  G := CyclotomicAutomorphismGroup(K);
  require U subset G: "U must be a subgroup of the (cyclotomic) automorphism group of K";
  if G eq U then
    return Rationals();
  elif Order(U) eq 1 then
    return K;
  end if;
  return to_field(K, U);
end intrinsic;


intrinsic FixedField(K :: FldAlg, U :: GrpPerm: Partial := false) -> FldNum, Map
{For a subgroup U of the AutomorphismGroup of K, compute the field fixed by U}
  
  // redo: if the automorphisms are known, use them!
  require IsAbsoluteField(K) and (Partial or IsNormal(K)): 
                 "K must be an absolute normal field";

  G := AutomorphismGroup(K:Partial := Partial);
  require U subset G: "U must be a subgroup of the automorphism group of K";
  if G eq U  and #G eq Degree(K) then
    return Rationals();
  elif Order(U) eq 1 then
    return K;
  end if;
  return to_field(K, U:Partial := Partial);
end intrinsic;

intrinsic FixedGroup(K :: FldAlg, L :: [FldAlgElt]:Partial := false) -> GrpPerm
{For elements L of K, compute the subgroup U of the automorphism group of K that fixes all elements of L}
  
  // redo: if the automorphisms are known, use them!
  require IsAbsoluteField(K) and (Partial or IsNormal(K)): 
                 "K must be an absolute normal field";

/*
  G, _, map := AutomorphismGroup(K:Partial := Partial);
*/
  G, _, map := AutomorphismGroup(K);
  s := Set(L);
  if Type(K) eq FldCyc then
    s := {x/Eltseq(x:Sparse)[1][1] : x in s | x ne 0};
  else
    s := {x/Eltseq(x)[1] : x in s | x ne 0};
  end if;

  //TODO: the map(x) part is expensive (according to profile), so
  // that the "optimized version" below looses because of the larger
  // number of calls to map(x)
  // maybe store them?
  return sub<G | [ x : x in G | forall{pe : pe in s | map(x)(pe) eq pe} ]>;
  F := G;
  for x in s do
    F meet:= FixedGroup(K, x:Aut := <G, 1, map>,Partial := Partial);
    if #F eq 1 then
      return F;
    end if;
  end for;
  return F;

end intrinsic;

intrinsic FixedGroup(K :: FldAlg, a:: FldAlgElt:Aut := false, Partial := false) -> GrpPerm
{For an element a of K, compute the subgroup U of the automorphism group of K that fixes it}
  
  // redo: if the automorphisms are known, use them!
  require IsAbsoluteField(K) and (Aut cmpne false or Partial or IsNormal(K)): 
                 "K must be an absolute normal field";

  if Aut cmpne false then
    G, _, map := Explode(Aut);
  else
    G, _, map := AutomorphismGroup(K:Partial := Partial);
  end if;
  return sub<G | [ x : x in G | map(x)(a) eq a ]>;
end intrinsic;

intrinsic FixedGroup(K :: FldAlg, k :: FldAlg:Partial := false) -> GrpPerm
{For a subfield k of K, compute the subgroup U of the automorphism group of K that fixes it}
  
  // redo: if the automorphisms are known, use them!
  require IsAbsoluteField(K) and (Partial or IsNormal(K)): 
                 "K must be an absolute normal field";
  
  pe := K!PrimitiveElement(k);
  return FixedGroup(K, pe:Partial := Partial);
end intrinsic;

intrinsic FixedGroup(K :: FldAlg, k :: FldRat:Partial := false) -> GrpPerm
{For a subfield k of K, compute the subgroup U of the automorphism group of K that fixes it}
  
  // redo: if the automorphisms are known, use them!
  require IsAbsoluteField(K) and (Partial or IsNormal(K)): 
                 "K must be an absolute normal field";
  
  return FixedGroup(K, K!1:Partial := Partial);
end intrinsic;


intrinsic DecompositionField(p :: RngOrdIdl) -> FldNum, Map
{Computes the decomposition field of p.}
  M := Order(p);
  K := NumberField(M);

  return to_field(K, DecompositionGroup(p));
end intrinsic;

intrinsic RamificationField(p :: RngOrdIdl, i:: RngIntElt) -> FldNum, Map
{Computes the i-th ramification field of p (lower index).}
  M := Order(p);
  K := NumberField(M);

  return to_field(K, RamificationGroup(p, i));
end intrinsic;

intrinsic RamificationField(p :: RngOrdIdl) -> FldNum, Map
{Computes the ramification field of p.}
  return RamificationField(p, 1);
end intrinsic;  

intrinsic InertiaField(p :: RngOrdIdl) -> FldNum, Map
{Computes the inertia field of p.}
  return RamificationField(p, 0);
end intrinsic;  

intrinsic Numerator(x::FldAlgElt) -> FldAlgElt
  {Returns the numerator of x, ie. x * Denominator(x).}
  return x*Denominator(x);
end intrinsic;

intrinsic IsCyclic(k::FldAlg) -> BoolElt
  {Tests if the field is normal with cyclic automorphism group.}
  if not IsAbelian(k) then
    return false;
  end if;
  return IsCyclic(AutomorphismGroup(k));
end intrinsic;    

intrinsic IsNormal(K::FldCyc[FldRat]) -> BoolElt
  {True iff K is normal.}
    return true;
end intrinsic;

intrinsic IsAbelian(K::FldCyc[FldRat]) -> BoolElt
  { True iff K is normal with abelian Galois group.}
    return true;
end intrinsic;

intrinsic Content(X::Mtrx) -> RngOrdFracIdl
  {The ideal generated by all entries in X}
  rt := Cputime();
  if ISA(Type(CoefficientRing(X)), FldAlg) then
    g := MyGCD(Eltseq(X));
    rt := Cputime(rt);
    return g;
  elif ISA(Type(CoefficientRing(X)), RngOrd) then
    g := MyGCD(ChangeUniverse(Eltseq(X), FieldOfFractions(CoefficientRing(X))));
    rt := Cputime(rt);
    return g;
  elif IsMagmaEuclideanRing(CoefficientRing(X)) then
    return GCD(Eltseq(X));
  else
    error "Matrix must be over some (Magma) Euclidean ring or some order in a number field";
  end if;

end intrinsic;

intrinsic Decomposition(R::Map[FldAlg,FldAlg], P::PlcNumElt) -> []
  {For a map R between two number fields, and a place P of the domain, compute the composition in the codomain.}
  k := Domain(R);
  K := Codomain(R);
  if IsInfinite(P) then
    pe := PrimitiveElement(k);
    I := InfinitePlaces(K);
    Ppe := Evaluate(pe, P);
    return [<x, LocalDegree(x) div LocalDegree(P)> : x in I | Abs(Ppe - Evaluate(R(pe), x)) lt 10^-20];
  end if;
  return [<Place(x[1]), x[2]> : x in Factorisation(
     ideal<MaximalOrder(K)| [R(x) : x in Generators(Ideal(P))]>)];
end intrinsic;

intrinsic Decomposition(R::Map[FldRat, FldAlg], P::RngIntElt) -> []
  {"} // "
  k := Domain(R);
  K := Codomain(R);
  if P eq 0 then
    return Decomposition(K, Infinity());
  end if;
  return Decomposition(K, P);
end intrinsic;


// Added March 2010, SRD

intrinsic Representation(x::RngElt, elts::SeqEnum[RngElt] : O:=-1) -> SeqEnum
{Represent x (an element in a number field K) as an O-linear combination 
of the given elts, where O is Integers(K) by default}

  require #elts gt 0 : "The second argument should be nonempty";

  if Type(O) eq RngOrd then
    K := NumberField(O);
  else
    K := NumberField(Universe(elts));
    O := Integers(K);
  end if;
  FF := FieldOfFractions(O);
  d := AbsoluteDegree(K);
  Q := Rationals();
  Z := Integers();

  bool1, x := IsCoercible(FF, x);
  bool2, elts := CanChangeUniverse(elts, FF); 

  require bool1 : "The first argument is not coercible to the number field";
  require bool2 : "The second argument is not compatible with the specified Order";

  Obasis := AbsoluteBasis(FF);

  xx := Vector(Q, Flat(FF!x));
  basis := Matrix(Q, [Flat(FF!e*b) : b in Obasis, e in elts]);

  denom := LCM([Denominator(c) : c in Eltseq(xx) cat Eltseq(basis)]);
  xx := ChangeRing(denom*xx, Z);
  basis := ChangeRing(denom*basis, Z);
  bool, sol := IsConsistent(basis, xx);

  require bool : "No such representation exists";

  // TO DO: adjust by kernel (closest vector problem)
 
  sol := Eltseq(sol);
  ans := [O| &+[sol[i+d*j]*Obasis[i] : i in [1..d]] : j in [0..#elts-1]];
assert x eq &+[ans[i]*elts[i] : i in [1..#elts]];
  return ans;

end intrinsic;


// Berstein (coprime basis in linear time) stuff:

function PPIO(a,c)
  x := GCD(a, c);
  y := a div x;
  res := [x];
  repeat
    g := GCD(x, y);
    if IsOne(g) then
      Append(~res, x);
      Append(~res, y);
      return Explode(res);
    end if;
    _ := TwoElement(g);
    x *:= g;
    y div:= g;
  until false;
end function;

function PPGLE(a,b)
  y := GCD(a, b);
  _ := TwoElement(y);
  res := [y];
  x := a div y;
  repeat
    g := GCD(x, y);
    if IsOne(g) then
      Append(~res, x);
      Append(~res, y);
      return Explode(res);
    end if;
    _ := TwoElement(g);
    x *:= g;
    y div:= g;
  until false;
end function;

function DCBA(a,b)  // bernstein: coprime basis for {a,b}
  if IsOne(b) then
    if IsOne(a) then
      return [Parent(a)|];
    else
      return [a];
    end if;
  end if;
  _, a, r := PPIO(a, b);
  if Norm(r) ne 1 then
    res := [r];
  else
    res := [];
  end if;
  g, h, c := PPGLE(a, b);
  c0 := c;
  x := c0;
  n := 1;
  repeat
    g, h, c := PPGLE(h, g^2);
    d := GCD(c, b);
    x *:= d;
    y := d^2^(n-1);
    res cat:= DCBA(c div y, d);
    n +:= 1;
  until IsOne(h);
  res cat:= DCBA(b div x, c0);
  return res;
end function;

function CBA(a,b)  // naive version, missing part is to switch 
                   // over to bernstein if level is large
  pr := [];
  procedure cba(~pr, ~ret, a, b:Level := 0)
    g := GCD(a, b);
    if IsOne(g) then
      if not IsOne(a) then
        Append(~pr, a);
      end if;
      ret := b;
      return;
    end if;
    _ := TwoElement(g);
    cba(~pr, ~r, a div g, g:Level := Level+1);
    cba(~pr, ~s, r, b div g:Level := Level+1);
    ret := s;
  end procedure;
  cba(~pr, ~r, a, b);
  if not IsOne(r) then
    Append(~pr, r);
  end if;
  return pr;
end function;
  
function Coprime(a,b) // to seletc CBA or DCBA
  return CBA(a,b);
end function;

function SPLIT(a, P: Prod := false)
  procedure split(~res, a, P: Prod := false)
    assert #P eq #Set(P);
    if #P eq 0 then
      return;
    end if;
    if Prod cmpne false then
      _, b, _ := PPIO(a, Prod);
    else
      _, b, _ := PPIO(a, &meet P);
    end if;
    if #P eq 1 then
      Append(~res, <P[1], b>);
      return;
    end if;
    split(~res, b, P[1..#P div 2]);
    split(~res, b, P[#P div 2 +1 .. #P]);
  end procedure;
  res := [];
  split(~res, a, P:Prod := Prod);
  return res;
end function;

function ExtendCoprime(L, b)
  if #L eq 0 then
    if IsOne(b) then
      return [Parent(b)|];
    else
      return [b];
    end if;
  end if;
  res := [];  
  x := &meet L;
  _, a, r := PPIO(b, x);
  S := SPLIT(a,L : Prod := x);
  if not IsOne(r) then
    Append(~res, r);
  end if;
  for pc in S do
    res cat:= Coprime(pc[1], pc[2]);
  end for;
  return res;
end function;

function MergeCoprime(P, Q)
  n := #Q;
  b := Ilog2(n)+1;
  S := P;
  function bit(k, i)
    return k mod 2^(i+1) div 2^i;
  end function;
  for i:= 0 to b do
    x := &meet [Parent(Q[1])|Q[k+1] : k in [0..n-1] | bit(k, i) eq 0];
    T := ExtendCoprime(S, x);
    x := &meet [Parent(Q[1])|Q[k+1] : k in [0..n-1] | bit(k, i) eq 1];
    S := ExtendCoprime(T, x);
  end for;
  return S;
end function;

function CoprimeList(L)
  if #L eq 0 then
    return [];
  end if;
  if #L eq 1 then
    return L;
  end if;
  P := CoprimeList(L[1..#L div 2]);
  Q := CoprimeList(L[#L div 2 + 1..#L]);
  return MergeCoprime(P, Q);
end function;

intrinsic Orbit(G::Grp, M::Any, A::Any:MaxSize := Infinity()) -> {}
  {The orbit of A under G,
  where the group G acts via the map M
  (where M may be a map of type Map or a function of type UserProgram)}

  return OrbitClosure(G, M, {A}:MaxSize := MaxSize);
end intrinsic;

intrinsic OrbitClosure(G::Grp, M::Any, A::{}:MaxSize := Infinity()) -> {}
  {The smallest G-invariant set containing A,
  where the group G acts via the map M
  (where M may be a map of type Map or a function of type UserProgram)}

  if ISA(Type(G), GrpPerm) then
    g := [M(x) : x in FewGenerators(G)];
  else
    g := [M(G.i) : i in [1..Ngens(G)]];
  end if;

  O := A;
  N := A;
  n := 100;
  while N ne {} do
    N := {n @ x : x in g, n in N} diff O;
    old := #O;
    O join:= N;
    if #O gt n then
      n *:= 1.2;
//      print "Orbit size now", #O;
    end if;
    if #O gt MaxSize then
//      print "Orbit too large, quitting";
      return O;
    end if;
  end while;
//  assert #G gt 10^4 or forall{ <g,a> : g in G, a in O | M(g)(a) in O};
  return O;
end intrinsic;

intrinsic MyGCD(L::[FldAlgElt]) -> RngOrdIdl
  {}
  vprint Reduce, 2: "Gcd of", #L, "elements";  
  M := MaximalOrder(Universe(L));
  FM := FieldOfFractions(M);
  p := {x : x in [1..#L] | not IsZero(L[x])};
  if #p eq 0 then
    return 0*M;
  end if;
  initial := Maximum(#L div 20, 5);
  initial := 3;
  initial := Minimum(#L, initial);
  vprint Reduce, 2: "initial gcd is using", initial;
  vtime Reduce, 2: for i:= 1 to initial do
    r := Random(p);
    Exclude(~p, r);
    if i eq 1 then
      g := L[r]*M;
    else
      g := g+L[r]*M;
    end if;
    if #p eq 0 then
      break;
    end if;  
  end for;

  vprint Reduce, 2: "initial done, now testing the others...";

  cnt := 0;
  for r in p do
    if not (FM!(L[r])) in g then
      vprint Reduce, 2: "element", r, "not in gcd so far, enlarging";
      vtime Reduce, 2: g +:= L[r]*M;
      cnt +:= 1;
    end if;
  end for;
  vprint Reduce, 2: "needed to enlarge", cnt, "times";
  return g;
end intrinsic;

Num := function(x)
  return x meet 1*Order(x);
end function;
Den := function(x)
  return M!!(x^-1 meet 1*M) where M := Order(x);
end function;

intrinsic CoprimeBasisInsert(~L::[], I::RngOrdFracIdl:GaloisStable := false,
                                          Start := 1, UseBernstein := false) 
  {Inserts an additional ideal into a coprime basis.}
    //"insert at", Start, "of", #L;
  M := Order(I);
  if IsOne(I) then
    return;
  end if;
  if Denominator(I) ne 1 then
    CoprimeBasisInsert(~L, Num(I):GaloisStable := GaloisStable, 
                         Start := Start, UseBernstein := UseBernstein);
    CoprimeBasisInsert(~L, Den(I):GaloisStable := GaloisStable, 
                         Start := Start, UseBernstein := UseBernstein);
    return;
  end if;
  if UseBernstein then
    L := ExtendCoprime(L, I);
    return;
  end if;
  I := M!!I; assert Type(I) eq RngOrdIdl;
  if GaloisStable then
    A, _, mA := AutomorphismGroup(NumberField(M):Partial);
    mA := func<a|func<x|ideal<M|mA(a)(Generators(x))>>>;
  else
    A := Sym(1);
    mA := func<x|func<y|y>>;
  end if;
  if #L eq 0 then
    Append(~L, I);
    return;
  end if;
  i := Start-1;
  while i lt #L do
    i +:=1;
    if L[i] eq I then
      return;
    end if;
    g := L[i]+I;
    if IsOne(g) then
      continue;
    else
      _ := TwoElement(g);
      if g eq L[i] then
        J := I/g;
        O := Orbit(A, mA, J);
        for o in O do
          CoprimeBasisInsert(~L, o:GaloisStable := GaloisStable, Start := i);
        end for;
        return;
      else
        J := I/g;
        JJ := L[i]/g;
        O := OrbitClosure(A, mA, {J, JJ, g});
        L[i] :=L[#L];
        Remove(~L, #L);
        for o in O do
          CoprimeBasisInsert(~L, o:GaloisStable := GaloisStable, Start := i);
        end for;
        return;
      end if;
    end if;
  end while;
  Append(~L, I);
end intrinsic;

intrinsic CoprimeBasis(L::[RngOrdFracIdl]: GaloisStable := false, New := true,
                                           UseBernstein := false) -> []
  {A sequence of ideals that generate multiplicatively the same ideals as L and that is closed under Gcd. If GaloisStable is given, it is also closed under operation of the automorphisms.}

  ideal_aut := func<p, a| ideal<Order(p)|a(Generators(p))>>;
  if #L eq 0 then
    return L;
  end if;
  M := Order(L[1]);
  LL := [PowerIdeal(M)|];

  if New then
    l := {M!!(x meet 1*M) : x in L} join {M!!((x + 1*M)^-1) : x in L};
    ln := {Norm(x) : x in l};
    ip := CoprimeBasis(SetToSequence(ln));

    pPart := function(p, M)
      pp := 1;
      repeat
        d := GCD(p, M);
        assert d in {1, p};
        pp *:= d;
        M div:= d;
      until d eq 1;
      return pp;
    end function;

    for p in ip do
      z := {x +pPart(p[1], Norm(x))*M : x in l};
      z := CoprimeBasis(SetToSequence(z):New := false, GaloisStable := GaloisStable);
      LL cat:= z;
    end for;
    return LL;
  end if;

  if GaloisStable then
    A,_, mA := AutomorphismGroup(NumberField(M):Partial);
    for i in L do
      O := Orbit(A, func<a|func<x|ideal_aut(x, a@mA)>>, i);
      // reasoning (maybe wrong) 
      // if O is closed under action of A, then any set derived by and closed
      // under GCD is also closed under A, thus we don't need it here.
      for o in O do
        CoprimeBasisInsert(~LL, o:GaloisStable := false, 
                                  UseBernstein := UseBernstein);
      end for;
    end for;
  else
    if UseBernstein then
      return CoprimeList(L);
    end if;
    for i in L do
      CoprimeBasisInsert(~LL, i:GaloisStable := false, UseBernstein := false);
    end for;
  end if;
  return LL;
end intrinsic;

intrinsic Support(L::[RngOrdFracIdl]: GaloisStable := false, 
                CoprimeOnly := false, UseBernstein := false) -> SetEnum
  {The support of L, ie. the set of (prime) ideal supporting elements in L.}
  // 1st step: make L a list of coprime ideals with the same support
  // the idea being that this might make the factorisation easier...
  // 2nd step: factorise the ideals

  ideal_aut := func<p, a| ideal<Order(p)|a(Generators(p))>>;
  if #L eq 0 then
    return {Universe(L)|};
  end if;
  M := Order(L[1]);
  L := CoprimeBasis(L:GaloisStable := GaloisStable, 
                      UseBernstein := UseBernstein);
  
  if CoprimeOnly then
    return SequenceToSet(L);
  end if;
  lp := {Minimum(x) : x in L};
  lp := &join [ {x[1] : x in Factorisation(p)} : p in lp];
  lP := &join [{x[1] : x in Decomposition(M, p)} : p in lp];
 
  S := {P : P in lP | exists{x : x in L | x subset P}};
  return S;
end intrinsic;

intrinsic Support(L::[FldAlgElt]:GaloisStable := false, 
                                 CoprimeOnly := false, 
                                 UseBernstein := false) -> SetEnum
  {The minimal set of prime ideals that are neccessary to factor all elements in L completely.}
  M := MaximalOrder(Universe(L));
  L := [x*M : x in L | x ne 1 and x ne 0];
  if #L eq 0 then
    return {PowerIdeal(M)|};
  end if;
  return Support([x : x in L]:GaloisStable := GaloisStable, 
                              CoprimeOnly := CoprimeOnly, 
                              UseBernstein := UseBernstein);
end intrinsic;

intrinsic '&*'(L::{RngOrdFracIdl}) -> RngOrdFracIdl
  {The Product of the ideals in L.}
  return &* SetToSequence(L);  
end intrinsic;

intrinsic '&*'(L::[RngOrdFracIdl]) -> RngOrdFracIdl
  {"} // "
  if #L eq 0 then
    return Universe(L)! 1;
  end if;
  if #L eq 1 then 
    return L[1];
  end if;
  if #L eq 2 then
    return L[1]*L[2];
  end if;
  return &* L[1..#L div 2] * &* L[#L div 2+1 .. #L];
end intrinsic;

intrinsic '&meet'(L::{RngOrdFracIdl}) -> RngOrdFracIdl
  {The intersection (LCM) of the ideals in L.}
  return &meet SetToSequence(L);
end intrinsic;

intrinsic '&meet'(L::[RngOrdFracIdl]) -> RngOrdFracIdl
  {"} // "
  if #L eq 0 then
    return 1*Ring(Universe(L));
  end if;
  if #L eq 1 then 
    return L[1];
  end if;
  if #L eq 2 then
    return L[1] meet L[2];
  end if;
  return &meet L[1..#L div 2] meet &meet L[#L div 2+1 .. #L];
end intrinsic;

intrinsic IsOne(I::RngOrdIdl) -> BoolElt
  {Return true iff I is the trivial ideal generated by 1.}
  return Minimum(I) eq 1;
end intrinsic;

intrinsic IsOne(I::RngOrdFracIdl) -> BoolElt
  {"} // "
  return Denominator(I) eq 1 and Minimum(I) eq 1; 
end intrinsic;

intrinsic 'div'(I::RngOrdIdl, J::RngOrdIdl) -> RngOrdIdl
  {Quotient of I by J; J must divide exactly.}
  if I eq J then
    return 1*Order(I);
  end if;
  J := I/J;
  require Denominator(J) eq 1: "Division was not exact";
  return Parent(I)!J;
end intrinsic;

intrinsic 'div'(I::RngOrdFracIdl, J::RngOrdFracIdl) -> RngOrdFracIdl
  {The quotient of I by J.}
  if I eq J then
    return 1*Order(I);
  end if;
  return I/J;
end intrinsic;

function MinCharPoly(a, R:Char := false)
  K := FieldOfFractions(Parent(a));
  S := FieldOfFractions(R);
  BS := AbsoluteBasis(S);
  fl, BSK := CanChangeUniverse(BS, K);
  if not fl then
    return false, _;
  end if;

  a := K!a;
  d := AbsoluteDegree(K) div AbsoluteDegree(S);
  assert AbsoluteDegree(S) eq #BS;
  lp := [1, a];
  ld := [1] cat [a*x : x in BSK];
  //we solve over the field, thus we can always assume ONE coefficient to
  //be 1 (otherwise the kernel will have #BS rows)
  while #lp le d+1 do
    if d mod (#lp-1) eq 0 then
      M := Matrix([Flat(x) : x in ld]);
      k := KernelMatrix(M);
      if Nrows(k) eq 1 then
        k := Eltseq(k);
        f := Polynomial([k[1]] cat [S!&+[kk[j]*BS[j] : j in [1..#BS]] where kk is k[(i-1)*#BS+2..i*#BS+1] : i in [1..#k div #BS]]);
	// With respect to the BS basis! Can only be coerced wrt the rel basis
        //f := Polynomial([k[1]] cat [S!k[(i-1)*#BS+2..i*#BS+1] : i in [1..#k div #BS]]);
        if Char then
          f := f^(d div Degree(f));
        end if;
        return true, f;
      elif Nrows(k) gt 1 then
        error "MinPoly failed";
      end if;
    end if;
    Append(~lp, lp[#lp]*a);
    ld cat:= [x*lp[#lp] : x in BSK];
  end while;
  error "MinPoly really failed";
end function;

intrinsic InternalMinPoly(a::FldAlgElt, R::FldAlg) -> RngUPolElt
  {Called from MinimalPolynomial(a, R) in the general case}
    
  b,f := MinCharPoly(a, R:Char := false);
  if not b then
    error "cannot embed 2nd argument into parent of 1st";
  end if;
  return f/LeadingCoefficient(f);
end intrinsic;

intrinsic InternalMinPoly(a::FldAlgElt, R::RngOrd) -> RngUPolElt
  {"} // "
    
  b,f := MinCharPoly(a, R:Char := false);
  if not b then
    error "cannot embed 2nd argument into parent of 1st";
  end if;
  d := Lcm([Denominator(x) : x in Eltseq(f)]);
  return Polynomial(R, d*f);
end intrinsic;

intrinsic InternalCharPoly(a::FldAlgElt, R::FldAlg) -> RngUPolElt
  {"} // "
    
  b,f := MinCharPoly(a, R:Char := true);
  if not b then
    error "cannot embed 2nd argument into parent of 1st";
  end if;
  return f/LeadingCoefficient(f);
end intrinsic;

intrinsic InternalCharPoly(a::FldAlgElt, R::RngOrd) -> RngUPolElt
  {"} // "
    
  b,f := MinCharPoly(a, R:Char := true);
  if not b then
    error "cannot embed 2nd argument into parent of 1st";
  end if;
  d := Lcm([Denominator(x) : x in Eltseq(f)]);
  return Polynomial(R, d*f);
end intrinsic;

intrinsic RootOfUnity(n::RngIntElt, K::FldAlg) -> FldAlgElt
  {The primitive n-th root of unity in the field K.}
  //CF: we cannot use FldAlg[FldRat] since then we get ambiguous 
  //signatures for cyclotomics
  require IsAbsoluteField(K): "Field must be absolute";
  T, mT := TorsionUnitGroup(K);
  if #T mod n eq 0 then
    return mT((#T) div n * T.1);
  end if;
  error "Root of unity is not in the field";
end intrinsic;


intrinsic Automorphisms(K::FldAlg:Abelian := false) -> []
  {The list of automorphisms of K}

  if IsSimple(K) then
    return InternalAutomorphisms(K:Abelian:=Abelian);
  end if;
 
  r := [Roots(f, K) : f in DefiningPolynomial(K)];
  return [hom<K->K | [x[1] : x in t]> : t in CartesianProduct(r)];
end intrinsic;


intrinsic Radical(I::RngOrdIdl) ->RngOrdIdl
  {The radical of I (where I is an ideal in the ring of integers of a number field)}

  return &* [Parent(I) | tup[1] : tup in Factorization(I)];
end intrinsic;


intrinsic PrimesUpTo(B::RngIntElt, K::FldRat : coprime_to:=1) -> SeqEnum[RngInt]
{A sequence containing the prime ideals in the field K with norm less than or equal to B}

  Z := Integers();

  if Type(coprime_to) eq RngInt then
    Q := Z! Norm(coprime_to);
  else
    Q := Z! coprime_to;
  end if;

  return [Parent(Z) | p*Z : p in PrimesUpTo(B) | GCD(p,Q) eq 1];
end intrinsic;


intrinsic PrimesUpTo(B::RngIntElt, K::FldAlg : coprime_to:=1) -> SeqEnum[RngOrdIdl]
{"} // "

  OK := Integers(K);

  t := Type(coprime_to);
  if ISA(t, RngOrdIdl) then
    Q := coprime_to;
  elif ISA(t, RngElt) then
    Q := coprime_to * OK;
  else
    require false : "Bad value of parameter 'coprime_to'";
  end if;

  if not IsAbsoluteField(K) then
    KA := AbsoluteField(K);
    OKA := Integers(KA);
    return [OK !! P : P in PrimesUpTo(B, KA : coprime_to := OKA !! Q)];
  end if;

  mQ := Minimum(Q);  

  primes := [PowerIdeal(OK)| ];
  norms := [Integers()| ];

  for p := 2 to B do
    if IsPrime(p) then
      for tup in Factorization(p*OK) do
        P := tup[1];
        N := Norm(P);
        if N le B and (GCD(N,mQ) eq 1 or Minimum(P+Q) eq 1) then
          Append(~primes, P);
          Append(~norms, N);
        end if;
      end for;
    end if;
  end for;

  ParallelSort(~norms, ~primes);
  return primes;
end intrinsic;

// Note: for large B this much faster than FactorBasis(K, B)


// Replaces old internal RelationMatrix (although that did not work)

intrinsic RelationMatrix(S::[RngOrdIdl]) -> Mtrx, SeqEnum[RngOrdElt]
{Given a sequence of primes S, this calculates the S-unit group, and
returns a matrix containing the valuations (one column per element)
and the corresponding elements}

  U, mU := SUnitGroup(S);

  for i := 1 to Ngens(U) - #S do
    assert IsUnit(U.i @ mU);
  end for;

  R := [U.i @ mU : i in [Ngens(U) - #S + 1 .. Ngens(U)]];

  // column matrix
  V := [Valuation(r, p) : r in R, p in S];
  M := Matrix(Integers(), #S, #S, V);

  return M, R;
end intrinsic;

intrinsic RelationMatrix(O::RngOrd, B::RngIntElt) -> Mtrx, SeqEnum[RngOrdElt]
{Returns RelationMatrix(FactorBasis(O, B))}

  return RelationMatrix(FactorBasis(O, B));
end intrinsic;

intrinsic RelationMatrix(K::FldNum, B::RngIntElt) -> Mtrx, SeqEnum[RngOrdElt]
{Returns RelationMatrix(FactorBasis(RingOfIntegers(K), B))}

  return RelationMatrix(FactorBasis(RingOfIntegers(K), B));
end intrinsic;

intrinsic Components(K::FldNum) -> SeqEnum[FldNum]
{The simple fields defined by the defining polynomials of K};
    if IsSimple(K) then
	return [K];
    end if;

    df := DefiningPolynomial(K);
    C := [];
    for i in [1 .. #df] do
	F := NumberField(df[i]);
	Embed(F, K, K.i);
	Append(~C, F);
    end for;
    return C;
end intrinsic;

intrinsic Components(F::FldOrd) -> SeqEnum[FldOrd]
{The fields of fractions of simple orders defined by the defining polynomials of F};
    O := Order(F);
    require EquationOrder(O) eq O : "Argument 1 must be fractions of an equation order";
    return [FieldOfFractions(o) : o in Components(O)];
end intrinsic;

intrinsic Components(O::RngOrd) -> SeqEnum[RngOrd]
{The simple orders defined by the defining polynomials of O};
    if IsSimple(O) then
	return [O];
    end if;

    require EquationOrder(O) eq O : "Argument 1 must be an equation order";

    df := DefiningPolynomial(O);
    C := [];
    for i in [1 .. #df] do
	F := EquationOrder(df[i]);
	Embed(NumberField(F), NumberField(O), NumberField(O).i);
	Append(~C, F);
    end for;
    return C;
end intrinsic;

function abelian_solve(e,S) // find c_i with e=\sum_i c_i S_i
 A:=Parent(e); n:=Ngens(A); ORD:=[Order(A.i) : i in [1..n]];
 l:=LCM(ORD); MULT:=[l div o : o in ORD];
 v:=[E[i]*MULT[i] : i in [1..n]] where E:=Eltseq(e);
 M:=[[E[i]*MULT[i] : i in [1..n]] where E:=Eltseq(S[j]) : j in [1..#S]];
 M:=ChangeRing(Matrix(M),Integers(l)); v:=ChangeRing(Vector(v),Integers(l));
 return Eltseq(ChangeRing(Solution(M,v),Integers())); end function;

function doit(I,M) p:=1; S:=[]; Ps:=[];
 K:=NumberField(Order(I)); G,mp:=ClassGroup(K); im:=-(I@@mp);
 while true do p:=NextPrime(p); if Gcd(p,Norm(I*M)) ne 1 then continue; end if;
  FAC:=Factorization(p*Integers(K));
  for f in FAC do s:=f[1]@@mp; if im eq s then return f[1]; end if;
   if sub<G|S> eq sub<G|S cat [s]> then continue; end if;
   S:=S cat [s]; Ps:=Ps cat [f[1]]; end for;
  if im in sub<G|S> then break; end if; end while;
 v:=abelian_solve(im,S); ans:=&*[Parent(I) | Ps[i]^v[i] : i in [1..#v]];
 assert IsPrincipal(I*ans); return ans; end function;

intrinsic PrincipalMultiple(I::RngOrdIdl,M::RngOrdIdl) -> RngOrdIdl
{Given an ideal I, find J such that IJ is principal and gcd(J,IM)=1}
 require Order(I) eq Order(M): "Ideals must be from same order";
 if IsPrincipal(I) then return 1*Order(I); end if;
 return doit(I,M); end intrinsic;
