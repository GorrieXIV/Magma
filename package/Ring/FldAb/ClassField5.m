freeze;

function convert(elt, Mk, M, mo)
    X := Domain(M);
    Z := Domain(Mk);
    phi := Mk(elt);
    aut := InducedAutomorphism(M, phi, mo);
    return Matrix([Eltseq(aut(X.i)) : i in [1..Ngens(X)]]);
    // use InducedAut here!!! XXX and do it in C
end function;
cm := recformat<CohomologyModule, AutomorphismGroup>;   
//TODO:: import from ClassField2.m!!
//       write some function to append to record (to deal
//       with AutomorphismGroup and CohomologyModule)
intrinsic CohomologyModule(F :: FldAb:Sub := false) -> ModCoho, Map, Map, Map
{The defining ideal group of F as a cohomology module}
  
  if assigned F`Record and assigned F`Record`CohomologyModule then
    return Explode(F`Record`CohomologyModule);
  end if;

  k := BaseField(F);
  g, _, p := AutomorphismGroup(k);
  if Sub cmpne false then
    g := Sub;
  end if;

  A, mo := NormGroup(F);
  mo := AbsoluteNorm(mo);
  AA := InvariantRepresentation(Domain(A));
  mAA := Coercion(AA, Domain(A));

  inv := AbelianInvariants(AA);
  mats := [ convert(g.i, p, mAA*A, mo) : i in [1..Ngens(g)]]; 
  
  C := CohomologyModule(g, inv, mats);
  Zm := RSpace(Integers(), Ngens(AA));
  mp := map<Zm -> AA | x :-> AA!Eltseq(x), y:-> Zm!Eltseq(y)>;
  // p maps the automorphisms group of k onto automorphisms
  // mAA*AA maps between the ideal group of F and the same group
  //      in Smith form (as used in Cohomology module)
  // mp maps between the RSpace from C to the ideal group.     

  if assigned F`Record and Sub cmpeq false then
    F`Record := rec<cm|CohomologyModule := <C, p, mAA*A, mp>,
                       AutomorphismGroup := F`Record`AutomorphismGroup>;
  else
    F`Record := rec<cm|CohomologyModule := <C, p, mAA*A, mp>>;
  end if;
  return C, p, mAA*A, mp;
end intrinsic;

intrinsic TwoCocycle(F::FldAb) -> UserProgram
  {Given a normal (over Q) abelian extension, return the 2-cocyle corresponding to the group extension deined by A as an element in the cohomology module}
  C, p, m1, m2 := CohomologyModule(F);

  // 1st we need the AutomorphismGroup of F:
  AF, _, mAF := AutomorphismGroup(F:All);
  // 2nd we need a "section" (ie. coset X/A reps for G in AF):
  // To be slightly more precise:
  // 1 -> A -> X -> G -> 1
  // is the sequence we're analyzing. A is the "norm group" of F,
  // X is AF (the automorphism group of F/Q) and G is the 
  // AutomorphismGroup of the base field of F)
  // Also, to compare elements, AF is bad, we need the permutation
  // version of AF, which via is AF`GenericGroup`q
  q := AF`GenericGroup`q;
  AF := Codomain(q);

  k := BaseField(F);
  g := Domain(p);
  G := Domain(p);
  tau_arr := [];
  gens_k := Set(Generators(k));
  gens_kF := ChangeUniverse(gens_k, NumberField(F));
  for g in G do
    au := p(g);
    im := au(gens_k);
    if not exists(Au){Au : Au in AF| (Au@@q@mAF)(gens_kF) eq im} then
      error "section failed";
    else
      Append(~tau_arr, <g, Au>);
    end if;
  end for;
  function tau(X)
    if exists(x){ x : x in tau_arr | x[1] eq X} then
      return x[2];
    else
      error "tau: element not found";
    end if;
  end function;
        
  // 3rd: the 2-cocyle should be 
  // (s,t) -> tau(st)^-1 * tau(s) tau(t)
  // which should be in the Norm group....
  // but, of course, initially it is in AF
  // so, the last step is to map back to the norm group.
  artin := ArtinMap(F);
  N := Domain(m1);
  function map_one(f)
    g := Set(Generators(NumberField(F)));
    im := f(g);
    
    if exists(Au){Au : Au in AF | mAF(Au@@q)(g) eq im} then
      return Au;
    else
      error "map_one: hom not found";
    end if;
  end function;
  H := hom<N -> Image(q) | [map_one(artin(N.i@m1)) : i in [1..Ngens(N)]]>;
  assert #Kernel(H) eq 1;

  inv_H := function(X)
    if exists(y){y : y in N | H(y) eq X} then
      return y;
    else
      error "inv_H: failed";
    end if;
  end function;

  cocyc_arr := [<x, inv_H(tau(x[1]*x[2])^-1*tau(x[1])*tau(x[2])) > : x in car<G,G>];
  
  function cocyc(X)
    if exists(x){x : x in cocyc_arr | x[1] eq X} then
      return x[2] @@ m2;
    else
      error "cocyc: element not found";
    end if;
  end function;

  return cocyc;
end intrinsic;

intrinsic CoboundaryMapImage(C::ModCoho, i::RngIntElt, c::UserProgram) -> .
  {Given a i-cocycle c, return an (i+1)-cocyle (delta)c for the coboundary operator delta}

  if i eq 0 then
    // a 0-cocyle (in magma) is a constant, but aparently in the wrong module
    delta := function(g)
      return func<x|
        ActionOnVector(C, c(<>), g) - c(<>)>;
    end function;
    return delta;
  elif i eq 1 then
    // a 1-cocyle is a function G -> M and the M is the same(?) as for 
    // 2-cocyles...
    delta := function(X)
      g,h := Explode(X);
      return 
        c(<h>)+ActionOnVector(C, c(<g>), h)-c(<g*h>);
    end function;
    return delta;
  elif i eq 2 then
    delta := function(X)
      x1, x2, x3 := Explode(X);
      return -ActionOnVector(C, c(<x1, x2>), x3) - c(<x1*x2, x3>) 
                            + c(<x1, x2*x3>) + c(<x2, x3>);
    end function;
    return delta;
  else
    error "Error: can only compute coboundary operators for i=0,1,2";
  end if;
end intrinsic;

intrinsic LiftCocycle(M::Map, c::UserProgram:NewCodomain := false, Level := false) -> UserProgram
  {The image of the cocycle c under the inflation map induced by the transversal M.}
  /*
   * c: a i-Cocycle for some H-Module C (which is not used)
   * M: G ->> H for some group G (a transversal map)
   * return a i-Cocycle in (but this is NOT constructed) the G-Module
   * Also known as Inflation I think
   */

  G := Codomain(M);
  if Level cmpeq false then
    // Careful: can go wrong! (if the cocyle e.g is constant:
    // func<c|X> then any input is valid...
    try
      _ := c(<G.0, G.0>);
      i := 2;
    catch e
      try
        _ := c(<G.0>);
        i := 1;
      catch f
        try
          _ := c(<>);
          i := 0;
        catch g
          require false: "Argument must be a 0, 1 or 2-cocycle";
        end try;
      end try;
    end try;
  else
    i := Level;
  end if;
      
  if i eq 2 then
    if NewCodomain cmpeq false then
      return func<X|c(<M(X[1]), M(X[2])>)>;
    else
      return func<X|NewCodomain!c(<M(X[1]), M(X[2])>)>;
    end if;
  elif i eq 1 then
    if NewCodomain cmpeq false then
      return func<X|c(<M(X[1])>)>;
    else
      return func<X|NewCodomain!c(<M(X[1])>)>;
    end if;
  elif i eq 0 then
    if NewCodomain cmpeq false then
      return func<X|c(X)>;
    else
      return func<X|NewCodomain!c(X)>;
    end if;
  end if;
end intrinsic;

intrinsic InflationMapImage(M::Map, c::UserProgram:NewCodomain := false, Level := false) -> UserProgram
  {The image of the cocycle c under the inflation map induced by the transversal M.}
  return LiftCocycle(M, c:NewCodomain := NewCodomain, Level := Level);
end intrinsic;

intrinsic CorestrictCocycle(G::Grp, C::ModCoho, c::UserProgram, i::RngIntElt) -> UserProgram
  {The image of the cocyle c of the cohomology module C under the cohomological corestriction}
  /*
   * c: a i-Cocycle for some U-Module C (which is not used)
   * return a i-Cocycle in (but this is NOT constructed) the G-Module
   * and it should be the corestriction.
   * formulae frm Lorenz, Algebra II, p290
   * May need Left insted of Right transversal
   */
    
  U := Group(C);
  assert U subset G;
  C, M := Transversal(G, U);   
  function split(x, y)
    assert y in C;
    m := M(x*y);
    u := m^-1*x*y;
    assert u in U;
    return u, m;
  end function;
  if i eq 2 then
    return func<X|&+ [ActionOnVector(C, c(<split(X[1]*X[2], r)-split(X[2], r), split(X[2], r)>), r^-1) : r in C]>;
  elif i eq 1 then
    return func<X| &+ [ ActionOnVector(C, c(<split(X[1], r)>), r^-1) : r in C]>;
  elif i eq 0 then
    return func<X| &+ [ ActionOnVector(C, c(<>), r^-1) : r in C]>;
  end if;
end intrinsic;

intrinsic CorestrictionMapImage(G::Grp, C::ModCoho, c::UserProgram, i::RngIntElt) -> UserProgram
  {The image of the cocyle c of the cohomology module C under the cohomological corestriction}
  return CorestrictCocycle(G, C, c, i);
end intrinsic;

intrinsic FixedField(A::FldAb, U::GrpAb:IsNormal := false) -> FldAb
  {For an abelian field A and a subgroup U of the norm group, create the subfield corresponding to the quotient by U, ie. the field fixed by U}
  return AbelianSubfield(A, U:IsNormal := IsNormal);
end intrinsic;

intrinsic AbelianSubfield(A::FldAb, U::GrpAb:IsNormal := false, Over := false) -> FldAb
  {For an abelian field A and a subgroup U of the norm group, create the subfield corresponding to the quotient by U, ie. the field fixed by U}

  N := NormGroup(A);
  q, mq := quo<Domain(N)|U>;
  B := AbelianExtension(Inverse(mq)*N);
  if assigned A`Record and assigned A`Record`CohomologyModule 
    and IsNormal and Over cmpeq false then
    q1, q2, q3, q4 := CohomologyModule(A);
    G := Group(q1);

    inv := AbelianInvariants(q);
    mats := [ Matrix(Integers(), #inv, #inv, [Eltseq(ActionOnVector(q1, q.i@@mq@@q4, G.j)@q4@mq)
                       : i in [1..Ngens(q)]]) : j in [1..Ngens(G)]];
    C := CohomologyModule(G, inv, mats);
    Zm := RSpace(Integers(), Ngens(q));
    mp := map<Zm -> q | x :-> q!Eltseq(x), y:-> Zm!Eltseq(y)>;
    B`Record := rec<cm|CohomologyModule := <C, q2, Inverse(mq)*N, mp>>;
  end if;
  return B;
end intrinsic;

intrinsic NormalSubfields(A::FldAb:Quot := false,All := true, Over := false) -> []
  {Finds all absolutely normal subfields of the abelian extension A.}
  // works only if the defining module is Galois-invariant  
  N := NormGroup(A);
  if Quot cmpeq false then
    l := Subgroups(Domain(N));
  else
    l := Subgroups(Domain(N):Quot := Quot);
  end if;

  g, _, mg := AutomorphismGroup(BaseField(A));
  if Over cmpne false then
    require not All : "All cannot be given together with Over";
    g := sub<g|[x @@ mg : x in Over]>;
    q1, q2, q3, q4 := CohomologyModule(A : Sub := g);
  else
    q1, q2, q3, q4 := CohomologyModule(A);
  end if;
  // we SHOULD be able to map (coerce) between Domain(N) and Domain(q3)
  // they should be the same group, but possibly differnt bases.
  // Point is, that q3 has the action already computed...

  G := Group(q1);
  function is_invariant(x)
    a := Generators(x`subgroup);
    ChangeUniverse(~a, Domain(N));
    ChangeUniverse(~a, Domain(q3));
    b := &cat [[ActionOnVector(q1, x@@q4, G.i)@q4 : x in a] : i in [1..Ngens(G)]];
    ChangeUniverse(~b, Domain(N));
    return x`subgroup eq sub<Domain(N)|b>;
  end function;
  //TODO:
  // - create the abelian extensions
  // - set the cohomology module (transfer of the map-matrices)
  l := [x : x in l | is_invariant(x)];
  l := [AbelianSubfield(A, x`subgroup:IsNormal, Over := Over) : x in l];
  return l;              
end intrinsic;


//TODO:
// - normal closure (ie. extend the ideal group)
// - try to get the fundamental class in all cases.
// - investigate the cohomology of prod I_S/U_S (ie. idele with
//   bounded support (S) modulo S-units) as an approximation to the
//   idel-class group and it's cohomology.
//   I think S should contain ramification and generate the class group.
// - try to normalize FundamentalClassImage, currently it may give
//   a conjugate.

function _TransitiveGroupIdentification(G:MaxId := 15)
  if not IsTransitive(G) then
    error "non transitive group found";
    return Hash(G), Degree(G);
  end if;
  if Degree(G) le 30 and Degree(G) le MaxId then
    return TransitiveGroupIdentification(G);
  end if;
  return Hash(G), Degree(G);
end function;

intrinsic IsExtensionOf(G::GrpPerm:Degree := false, MaxId := 15, DegreeBound := false, BaseGroup := false) -> []
  {Computes all(?) possible ways to create G as a group extension. The second return values gives all group types that can be obtained through the extension processes giving G.}
  if Degree cmpeq false then
    A := NormalSubgroups(G:IsAbelian);
    if DegreeBound cmpne false then
      A := [x : x in A | #x`subgroup ge #G/DegreeBound];
    end if;
  else
    A := NormalSubgroups(G:IsAbelian, OrderEqual := #G div Degree);
  end if;
  // we want "maximal elements" here...
  A := [x`subgroup : x in A | x`subgroup ne G and #(x`subgroup) gt 1];
  A := [x : x in A |
    forall{y : y in A | not x  subset y or x eq y}];
  // Now, let's try to create the cohomology modules and identify
  // the cocycles....

  A := [<a,b,AbelianInvariants(i), i> 
     where a,b := _TransitiveGroupIdentification(quo<G|i>:MaxId := MaxId) : i in A];
  if BaseGroup cmpne false then
    A := [x : x in A | <x[2], x[1]> eq BaseGroup];
  end if;
  S := [<x[1], x[2], x[3]> : x in A];   
  s := Set(S);
  A := [ A[Position(S, x)][4] : x in s];
  Res := [**];
  for i in A do
    // now similar to TwoCocycle above, we need 
    //  - a transversal t for G/A = g 
    //  - for each element in <g,g> compute
    //    t(xy)^-1*t(x)*t(y) in A
    w, g := CosetAction(G, i);
    if BaseGroup cmpne false then
      a,b := TransitiveGroupIdentification(g);
      if <b,a> ne BaseGroup then
        continue;
      end if;
    end if;  
    gg, mgg := sub<g|{x : x in FewGenerators(g)| x ne Id(g)}>;
    a, ma := AbelianGroup(i);
    l := func<X|Eltseq((((X[1]*X[2])@mgg@@w)^-1 * X[1]@mgg@@w * X[2]@mgg@@w )@ma)>;
    C := CohomologyModule(gg, a, map<g -> Aut(a)|x :-> 
          hom<a -> a | [((a.j @@ ma)^(x@@w))@ma : j in [1..Ngens(a)]]>>);
    _ := CohomologyGroup(C, 2);
    Append(~Res, <C, IdentifyTwoCocycle(C,l), l, <b,a> 
                  where a,b := _TransitiveGroupIdentification(g:MaxId := MaxId),
                  AbelianInvariants(i),
                 {<b, a> where 
                     a,b := _TransitiveGroupIdentification(
                       DegreeReduction(CosetImage(x, sub<x|>)):MaxId := MaxId)
                         : x in DistinctExtensions(C)}>);
  end for;
  return Res;
end intrinsic;

intrinsic IsExtensionOf(L::[GrpPerm]:Degree := false, MaxId := 15, DegreeBound := false, BaseGroup := false) -> []
  {}
  Res := IsExtensionOf(L[1]:Degree := Degree, MaxId := MaxId, DegreeBound := DegreeBound, BaseGroup := BaseGroup);
  so_far := &join [x[6] : x in Res];
  type := {<x[4], x[5]> : x in Res};
  for i in [2..#L] do
     a,b := _TransitiveGroupIdentification(L[i]:MaxId := MaxId);
     if <a,b> in so_far then
       continue;
     end if;
     r := IsExtensionOf(L[i]:Degree := Degree, MaxId := MaxId, DegreeBound := DegreeBound, BaseGroup := BaseGroup);
     so_far join:= &join [x[6] : x in r];
    
     for x in r do
       if <x[4], x[5]> notin type then
         Include(~type, <x[4], x[5]>);
         Append(~Res, x);
       end if;
     end for;
  end for;                  
  return Res, so_far;
end intrinsic;


/*
  <example>
    k := NumberField(x^2-2);
    K := ext<k|Polynomial([-30-3*k.1, 0,1])>; //totally real C4
    M := MaximalOrder(AbsoluteField(K));
    A := AbelianExtension(13*32*3*37*M);
    l := NormalSubfields(A:Quot := [4]);
    l := [AbelianExtension(Inverse(mq)*N)
       where _, mq := quo<Domain(N)|x`subgroup> 
         where N := NormGroup(A) : x in l];
    for i in l do C := CohomologyModule(i); CohomologyGroup(C, 2); end for;
    for i in l do C := CohomologyModule(i); IdentifyTwoCocycle(C,
      FundamentalClassImage(i)); end for;
   
    K1 := l[32-5];
    K2 := l[32-3];
    IdentifyTwoCocycle(CohomologyModule(K1), FundamentalClassImage(K1));
    IdentifyTwoCocycle(CohomologyModule(K2), FundamentalClassImage(K2));
    time IdentifyTwoCocycle(CohomologyModule(K1), TwoCocyle(K1));
    time IdentifyTwoCocycle(CohomologyModule(K2), TwoCocyle(K2));
    G1 := Extension(CohomologyModule(K1), [2]);
    G2 := Extension(CohomologyModule(K2), [0]);
    GG1 := CosetImage(G1, sub<G1|>);
    GG2 := CosetImage(G2, sub<G2|>);
    TransitiveGroupIdentification(GG1);
    TransitiveGroupIdentification(GG2);
  </example>  

  <example>
    > k := AbsoluteField(NumberField([x^2-2, x^2-3]));
    > m := AbelianExtension(8*5*13*MaximalOrder(k));
    > l := NormalSubfields(m:Quot := [2,2]);
  </example>  
*/

