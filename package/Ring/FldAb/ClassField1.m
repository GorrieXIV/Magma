freeze;
///////////////////////////////////////////////////////////////////////////////
/// Abelian Groups!
///////////////////////////////////////////////////////////////////////////////

AddAttribute(GrpAb, "DualMap");
AddAttribute(GrpAb, "H2Base");
AddAttribute(GrpAb, "H2Map");
intrinsic Dual(G:: GrpAb:UseSameGroup:= false) -> GrpAb, Map
{Computes the dual of G together with the pairing into Z/mZ.}
  require IsFinite(G) : "Group must be finite!";
  if UseSameGroup and IsDiagonal(RelationMatrix(G)) then
    H := G;
  else
    H := InvariantRepresentation(G);
  end if;
  if #G eq 1 then
    if UseSameGroup then
      G`DualMap := hom<car<G, G> -> Integers(1) | x :-> 0>;
      return G, G`DualMap;
    end if; 
    H`DualMap :=  hom<car<G,H> -> Integers(1) | x:-> 0>;
    return H, H`DualMap;
  end if;
  e := Exponent(G);
  Zm := Integers(e);
 
  m := function(g,h)
    g := Eltseq(H!g);
    h := Eltseq(H!h);
    xi := &+ [Zm| (g[i]*h[i]) *(e div Order(H.i)) : i in [1..Ngens(H)]];
    return xi;
  end function;
  if UseSameGroup then
    h := hom<car<G,G> -> Zm | x :-> m(x[1], x[2])>;
    G`DualMap := h;
    return G, h;
  else
    h := hom<car<G,H> -> Zm | x :-> m(x[1], x[2])>;
    H`DualMap := h;
    return H, h;
  end if;

end intrinsic;

intrinsic H2_G_QmodZ(G:: GrpAb) -> GrpAb, Map
{Computes (hopefully) H^2(G, Q/Z) and a map into the cocycles, i.e. a map returning a map from G^2 into Q/Z fr every element of H^2 }

  require Type(G) eq GrpAb : "G must be of type GrpAb";

  H := InvariantRepresentation(G);
  l := Invariants(H);
  ll := #l;
  l := [ GCD(l[i], l[j]) : i in [j+1..#l], j in [1..#l] ];
  H2 := AbelianGroup(l);
  n := Invariants(H2);
  if #n eq 0 then
    n := 1;
  else  
    n := n[#n];
  end if;  
  DH2 := Dual(H2);
  m := function(h2)
    mm := function(x1, x2)
      x1 := H!x1;
      x2 := H!x2;
      x1 := Eltseq(x1);
      x2 := Eltseq(x2);
      r := [x1[i]*x2[j] - x1[j]*x2[i] : i in [j+1..ll], j in [1..ll] ];
      return DH2`DualMap(<H2!r, h2>);
    end function;
    return map<car<G, G> -> Integers(n) | x :-> mm(x[1], x[2])>;
  end function;

  DH2`H2Base := G;
  DH2`H2Map := m;

  return DH2, m;
end intrinsic;

intrinsic Res_H2_G_QmodZ(U::GrpAb, H2::GrpAb) -> GrpAb, Map
{Computes H^2(U, Q/Z) and the restriction map from H2 = H^2(G, Q/Z) into H^2(U, Q/Z)}
  IU := InvariantRepresentation(U);
  U2 := H2_G_QmodZ(U);

  lU := Invariants(IU);

  map := hom <H2 -> U2 | 
            [ H2.i -> U2![H2`H2Map(H2.i)(<U!IU.k, U!IU.l>) :
                      k in [l+1..#lU], l in [1..#lU] ]
                                                : i in [1..Ngens(H2)] ]>; 
  return U2, map;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
/// ClassFields
///////////////////////////////////////////////////////////////////////////////

CreateHom := function(G, GG, mp)
  // h := hom<G -> GG | mp>;  // does not work ...
  // mp is a list of pairs. We want to constuct the map
  // that sends mp[i][1] -> mp[i][2].
 
  m1 := Matrix(Integers(), [Eltseq(x[1]) : x in mp]);
  m1 := VerticalJoin(m1, DiagonalMatrix([ Order(G.x) : x in [1..Ngens(G)]]));
  _, t := EchelonForm(m1);
  m1 := Matrix(Integers(), [Eltseq(x[2]) : x in mp]);
  t := Matrix(Integers(), [ Eltseq(t[i])[1..#mp] : i in [1..Nrows(t)]]);
  m1 := t*m1;
  mp := [ GG!Eltseq(m1[i]) : i in [1..Ngens(G)]];
  h := hom<G -> GG | mp>; 
  return h;
end function;  

intrinsic InducedMap(r1::Map, r2::Map, h::Map, Coprime :: RngIntElt) -> Map
{Returns the map between (the RayClassGroups) r1 and r2 that is induced by h}

  p := NextPrime(100);
  li := [ ];
  lg := [ ];
  G := Domain(r1);
  H := Domain(r2);
  o := Ring(Codomain(r1));
  if Gcd(#G, #H) eq 1 then
    return hom<G -> H | [ H.0 : i in [1..Ngens(G)]]>;
  end if;  

  repeat
    repeat
      p := NextPrime(p);
    until Gcd(p, Coprime) eq 1;
    lp := Decomposition(o, p);
    for i in lp do
      if Degree(i[1]) gt 1 and Norm(i[1]) gt 1000 then
        continue;
      end if;
      Append(~lg, i[1] @@ r1);
      Append(~li, h(i[1]) @@ r2);
    end for;
  until sub<G|lg> eq G;

  return CreateHom(G, H, [<lg[i], li[i]> : i in [1..#lg]]);
end intrinsic;

intrinsic InducedAutomorphism(r::Map, h::Map, Coprime :: RngIntElt) -> Map
{Returns the automorphism on (the RayClassGroups) r that is induced by h}
  return InducedMap(r, r, h, Coprime);
end intrinsic;

intrinsic DecompositionType(F::FldAb, p::PlcNumElt) -> GrpAb
{The decomposition type of p as a list of pairs <f, e>};
  M, m0, m_inf := NormGroup(F);

  require Parent(p) eq Places(NumberField(BaseRing(F))):
    "Place must come from the number field of the base ring of F";

  a,b := IsInfinite(p);
  if not a then
    _, b := IsFinite(p);
    b := BaseRing(F)!!b;
    return DecompositionType(F, b);
  end if;
  p := b;

  G := Domain(M);

  if p notin m_inf then
    U := G;
    return [<1,1> : i in [1..Degree(F)]];
  else
    return [<1,2> : i in [1..Degree(F) div 2]];
  end if;
end intrinsic;

intrinsic DecompositionType(F::FldAb, p::RngOrdIdl) -> GrpAb
{The decomposition type of p as a list of pairs <f, e>};
  require IsPrime(p): "Ideal must be a prime ideal";

  M, m0, m_inf := NormGroup(F);

  require Order(p) eq Order(m0): 
       "The prime ideal must belong to the base ring of F";

  o := Order(p);
  G := Domain(M);

  if m0 + p eq 1*o then
    f := Order(p @@ M);
    return [<f, 1> : i in [1..Degree(F) div f]];
  else
    n0 := m0 / p^Valuation(m0, p);
    n_inf := m_inf;

    _, F := RayClassGroup(m0, m_inf);
    I_F_M := InducedMap(F, M, map<Parent(m0) -> Parent(m0) | x :-> x>, 
                                                      Minimum(m0));
    _, M_n := RayClassGroup(n0, n_inf);
    I_F_N := InducedMap(F, M_n, map<Parent(p) -> Parent(p) | x :-> x>,
                                                      Minimum(m0));
    k := Kernel(I_F_M);
    GG, mGG := quo<Domain(M_n) | I_F_N(k)>;
    f := Order(mGG(p @@ M_n));
    assert #G mod #GG eq 0;
    e := #G div #GG;
    return [<f, e> : i in [1..#G div (e*f)]];
  end if;
end intrinsic;


intrinsic DecompositionGroup(p::PlcNumElt, F::FldAb) -> GrpAb
{The decomposition group of p (an infinite place) as a subgroup of the norm group of F}

  require Parent(p) eq Places(NumberField(BaseRing(F))):
    "Place must come from the number field of the base ring of F";

  a,b := IsInfinite(p);
  if not a then
    _, b := IsFinite(p);
    b := BaseRing(F)!!b;
    return DecompositionGroup(F, b);
  end if;
  p := b;
  return DecompositionGroup(p, F);
end intrinsic;


intrinsic DecompositionGroup(p::RngIntElt, F::FldAb) -> GrpAb
{The decomposition group of the p'th infinite place as a subgroup of the norm group of F}

  M, m0, m_inf := NormGroup(F);

  G := Domain(M);

  if p notin m_inf then
    U := G;
  else
    n_inf := Remove(m_inf, Position(m_inf, p));
    n0 := m0;
    _, F := RayClassGroup(m0, m_inf);
    I_F_M := InducedMap(F, M, map<Parent(m0) -> Parent(m0) | x :-> x>, 
                                                      Minimum(m0));
    _, M_n := RayClassGroup(n0, n_inf);
    I_F_N := InducedMap(F, M_n, map<Parent(m0) -> Parent(m0) | x :-> x>,
                                                      Minimum(m0));
    U := sub<G | {I_F_M(x) : x in Generators(Kernel(I_F_N))} >;
  end if;
  return U;
end intrinsic;

intrinsic DecompositionGroup(p::RngOrdIdl, F::FldAb) -> GrpAb
{The decomposition group of p as a subgroup of the norm group of F}
  require IsPrime(p): "Ideal must be a prime ideal";

  M, m0, m_inf := NormGroup(F);

  require Order(p) eq Order(m0): "The prime ideal must belong to the base ring of F";

  o := Order(p);
  G := Domain(M);

  if m0 + p eq 1*o then
    U := sub<G | p @@ M>;
  else
    n0 := m0 / p^Valuation(m0, p);
    n_inf := m_inf;
    _, F := RayClassGroup(m0, m_inf);
    I_F_M := InducedMap(F, M, map<Parent(p) -> Parent(p) | x :-> x>,
                                                      Minimum(m0));
    _, M_n := RayClassGroup(n0, n_inf);
    I_F_N := InducedMap(F, M_n, map<Parent(p) -> Parent(p) | x :-> x>,
                                                      Minimum(m0));
    U := sub<G | {I_F_M((p @@ M_n) @@ I_F_N) } join 
                 {I_F_M(x) : x in Generators(Kernel(I_F_N))} >;
  end if;
  return U;
end intrinsic;

intrinsic DecompositionField(p::PlcNumElt, F::FldAb) -> GrpAb
{The decomposition field of p as an AbelianExtension} 

  require NumberField(p) eq BaseField(F) : 
    "Place must come from the number field of the base ring of F";
  M, m0, m_inf := NormGroup(F);

  U := DecompositionGroup(p, F);
  Q, mq := quo<Domain(M) | U>;
  return AbelianExtension(Inverse(mq)*M);
end intrinsic;  

intrinsic DecompositionField(p::RngOrdIdl, F::FldAb) -> GrpAb
{The decomposition field of p as an AbelianExtension} 
  require IsPrime(p): "Ideal must be a prime ideal";

  M, m0, m_inf := NormGroup(F);

  require Order(p) eq Order(m0): 
               "The prime ideal must belong to the base ring of F";

  U := DecompositionGroup(p, F);
  Q, mq := quo<Domain(M) | U>;
  return AbelianExtension(Inverse(mq)*M);
end intrinsic;  

///////////////////////////////////////////////////////////////////////////////
/// ClassFields and norm equations
///////////////////////////////////////////////////////////////////////////////

intrinsic Knot(F:: FldAb) -> GrpAb
{The quotients of local norms modulo global norms}
  
  M, m0, m_inf := NormGroup(F);
  G := Domain(M);
  H2 := H2_G_QmodZ(G);

  lf := Factorisation(m0);
  k := H2;
  for i in lf do
    U := DecompositionGroup(i[1], F);
    _, m := Res_H2_G_QmodZ(U, H2); 
    k := k meet Kernel(m);
  end for;

  for i in m_inf do
    U := DecompositionGroup(i, F);
    _, m := Res_H2_G_QmodZ(U, H2);
    k := k meet Kernel(m);
  end for;  

  return k;
end intrinsic;

intrinsic IsLocalNorm(F::FldAb, x::RngOrdElt, p::RngOrdIdl) -> BoolElt
{returns true, iff x is a local norm at p}
  require IsPrime(p) : "p must be a prime ideal";

  M, m0, m_inf := NormGroup(F);
  G := Domain(M);
  O := Order(p);

  require Order(p) eq Order(m0): 
               "The prime ideal must belong to the base ring of F";

  v1 := Valuation(x, p);
  v2 := Valuation(m0, p);
  n0 := m0 / p^v2;
  o0 := p^(v1 + v2);
  y := ChineseRemainderTheorem(n0, o0, O!1, x);
  if #m_inf gt 0 then
    y := ChineseRemainderTheorem(n0*o0, m_inf, y, [1 : x in m_inf]); 
  end if;
  y := y*O;
  y := y/p^v1;
 
  return y @@ M eq G.0;
end intrinsic;


intrinsic IsLocalNorm(F::FldAb, x::RngOrdElt, p::RngIntElt) -> BoolElt
{returns true, iff x is a local norm at p (an infinite place)}

  M, m0, m_inf := NormGroup(F);
  G := Domain(M);
  O := Parent(x);

  require 0 lt p and p le Degree(O) : "not a valid place";

  //locally: if p is complex, then the local extension is trivial
  //            and the norm is surjective
  //         if p is real then we have to see if we are ramified or not.
  //            if ramified, then locally, we get the complex field, and
  //               image of norm are positive elements
  //            if unram, then locally we get real/real and norm is surjective   
  a := Conjugate(x, p);
  a := Re(a);
  c, c_inf := Conductor(F);
  if p in c_inf then
    return a ge 0; // real place ramifies => image of norm is R>=0
  else
    return true; // p is a complex place, so local ext. is trivial
  end if;
end intrinsic;

intrinsic IsLocalNorm(F::FldAb, x::RngOrdElt) -> BoolElt
{returns true, iff x is a local norm everywhere}

  M, m0, m_inf := NormGroup(F);

  lf := Factorisation(x*m0);
  for i in lf do
    if not IsLocalNorm(F, x, i[1]) then
      return false;
    end if;
  end for;

  for i in m_inf do
    if not IsLocalNorm(F, x, i) then
      return false;
    end if;
  end for;  
  return true;
end intrinsic;

intrinsic IsLocalNorm(F::FldAb, x::RngOrdElt, p::PlcNumElt) -> BoolElt
{returns true, iff x is a local norm at p}
  require Parent(p) eq Places(NumberField(BaseRing(F))):
    "Place must come from the number field of the base ring of F";

  a,b := IsInfinite(p);
  if not a then
    _, b := IsFinite(p);
    b := BaseRing(F)!!b;
  else
  end if;
  return IsLocalNorm(F, x, b);
end intrinsic;
// missing:
// MaximalOrder(FldAb)
// sub<K | list of fields>
//
///////////////////////////////////////////////////////////////////////////////
/// ClassFields and solving of norm equations
///////////////////////////////////////////////////////////////////////////////

intrinsic NormEquation(F::FldAb, x::RngOrdElt) -> BoolElt, []
{Tries to solve the norm equation N(a) = x in F. If successful it return a solution}

  M, m0, m_inf := NormGroup(F);
  require Order(m0) eq Parent(x) : "x must be of the base ring of F";

  if not IsLocalNorm(F, x) then
    return false, _;
  end if;  


  G := Domain(M);

  K := NumberField(F);
  vprint NormEquation : "We have to solve in the field ", K;

  C := Components(F);
  
  sp := { i[1] : i in Factorisation(#G) };
  if #sp eq 0 then
    return true, [K!x];
  end if;
  sol := [ ];
  vprint NormEquation: "Primes dividing the degree are: ", sp;
  for p in sp do
    vprint NormEquation: "OK, trying ", p, " extensions";
    l := [x : x in C | Degree(x) mod p eq 0];
    L := NumberField([ DefiningPolynomial(x) : x in l]:Abs, Check := false);
    Embed(L, K, [K!x.2 : x in l]); // do it better!

    vprint NormEquation : "Solving for ", x, " in ", L;
    a,b := NormEquation(L, BaseField(L)!x : 
                                Primes := [ Parent(1*BaseRing(F))|]);
    if not a then
      return false, L, x;
    end if;
    Append(~sol, [* p, b[1] *]);;
  end for;

  if #sp eq 1 then
    return true, [sol[1][2]];
  end if;

  vprint NormEquation: "Found all solutions in the subfield, now combining...";
  _, u, v := Xgcd(Degree(Parent(sol[1][2])), Degree(Parent(sol[2][2])));
  s := K!(sol[1][2]^v) * K!(sol[2][2]^u);
  d := Degree(Parent(sol[1][2])) * Degree(Parent(sol[2][2]));

  for i in [3..#sol] do
    _, u, v := Xgcd(d, Degree(Parent(sol[i][2])));
    s := s^v * K!(sol[i][2]^u);
    d := d * Degree(Parent(sol[i][2]));
  end for;
  
  return true, [s];
end intrinsic;

intrinsic IsNorm(F::FldAb, x::RngOrdElt) -> BoolElt
{Returns true iff x is a norm from F}
  if not IsLocalNorm(F, x) then
    return false;
  end if;
  if #Knot(F) eq 1 then
    return true;
  end if;  
  return NormEquation(F, x);
end intrinsic;


intrinsic AbsoluteDiscriminant(L::FldAb) -> RngIntElt
  {The discriminant of L over Q.}
  return Discriminant(BaseRing(L))^Degree(L) * Norm(Discriminant(L));
end intrinsic;
   
