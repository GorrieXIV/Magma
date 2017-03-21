freeze;

function AbelianExtensionCreate(K, Conductor, MaxAbel)
  // only probablisitic!!!
  // to change this we need a bound on the primes (and a lot of CPU
  // time)
  // but it will work - at least if the field is abelian!

  k := BaseRing(K);
  if Type(k) in {RngInt, FldRat} then
    k := ext<k|Polynomial(k, [-1,1])>;
  end if;

  if Conductor cmpeq false then
    m0 := Discriminant(K);
    minf := [i : i in [1..Signature(k)]];
  else
    if Type(Conductor) in {Tup, SeqEnum, List} then
      m0 := Conductor[1];
      minf := Conductor[2];
    elif Type(Conductor) in {RngIntElt, RngOrdIdl, RngOrdFracIdl} then
      m0 := Conductor;
      minf := [i : i in [1..Signature(k)]]; 
    else
      error "Conductor does not make any sense";
    end if;
  end if;

  p := 100;
  m := MaximalOrder(k);

  if Type(m0) in {RngIntElt, FldRatElt} then
    G, mG := RayClassGroup(m*m0, minf);
    coprime := m0;
  else
    G, mG := RayClassGroup(m!!m0, minf);
    coprime := Minimum(m0);
  end if;


  extra := 5;

  s := [ ];
  old_s := false;
  repeat
    repeat
      p := NextPrime(p);
    until Gcd(p, coprime) eq 1;

    lp := Decomposition(k, p);
    for i in lp do
      if Degree(i[1]) gt 1 and Norm(i[1]) gt 10000 then
        continue;
      end if; 
      if Degree(k) eq 1 then
        dt := DecompositionType(K, Minimum(i[1]));
      else
        dt := DecompositionType(K, k!!i[1]);
      end if;
      if exists{x : x in dt | x[2] ne 1} then
        continue;
      end if;
      if #Set(dt) gt 1 and not MaxAbel then
        error "Error: field is not normal";
      end if;
      for j in [1..#dt] do
        Append(~s, ((m!!i[1]) @@ mG)*dt[j][1]);
      end for;
    end for;
    q, mq := quo<G|s>;
      
    if #q lt Degree(K) and not MaxAbel then
      error "Error: field is not abelian";
    end if;
    
    if #q le Degree(K) then
      if old_s cmpne false then
        if #q eq old_s then
          extra -:= 1;
        else
          extra := 5;
        end if;
      end if;
    end if;
    old_s := #q;
    
  until extra eq 0;
  
  return AbelianExtension(Inverse(mq)*mG);
end function;
  
intrinsic AbelianExtension(K::FldNum : Conductor := false) -> FldAb
{Create an abelian extension of the base field of K isomorphic to K}
  k := BaseField(K);
  require Type(k) eq FldRat or IsAbsoluteField(k) : 
           "The base field of K must be definined over Q";

  return AbelianExtensionCreate(MaximalOrder(K), Conductor, false);
end intrinsic;

intrinsic AbelianExtension(M :: RngOrd : Conductor := false) -> FldAb
{Create an abelian extension of the base ring of M isomorphic to the number field of M}
  k := BaseRing(M);
  require Type(k) eq RngInt or IsAbsoluteOrder(k) : 
           "The base field of K must be definined over Q";

  return AbelianExtensionCreate(M, Conductor, false);
end intrinsic;

intrinsic AbelianExtension(F :: FldOrd : Conductor := false) -> FldAb
{Create an abelian extension of the base field of F isomorphic to F}
  k := BaseField(F);
  require Type(k) eq FldRat or IsAbsoluteField(k) : 
            "The base field of K must be definined over Q";

  return AbelianExtensionCreate(Order(F), Conductor, false);
end intrinsic;

intrinsic MaximalAbelianSubfield(K::FldNum : Conductor := false) -> FldAb
{Create an abelian extension of the base field of K isomorphic to the maximal abelian subfield of K}
  k := BaseField(K);
  require Type(k) eq FldRat or IsAbsoluteField(k) : 
           "The base field of K must be definined over Q";

  return AbelianExtensionCreate(GeneralisedEquationOrder(K), Conductor, true);
end intrinsic;

intrinsic MaximalAbelianSubfield(M :: RngOrd : Conductor := false) -> FldAb
{Create an abelian extension of the base ring of M isomorphic to the maximal abelian subfield of the number field of M}
  k := BaseRing(M);
  require Type(k) eq RngInt or IsAbsoluteOrder(k) : 
           "The base field of K must be definined over Q";

  return AbelianExtensionCreate(M, Conductor, true);
end intrinsic;

intrinsic MaximalAbelianSubfield(F :: FldOrd : Conductor := false) -> FldAb
{Create an abelian extension of the base field of F isomorphic to the maximal abelian subfield of F}
  k := BaseField(F);
  require Type(k) eq FldRat or IsAbsoluteField(k) : 
            "The base field of K must be definined over Q";

  return AbelianExtensionCreate(Order(F), Conductor, true);
end intrinsic;

intrinsic DecompositionType(F::FldAb, p::RngIntElt:Normal := false) -> SeqEnum
{The decomposition shape of p in F as a sequence of pairs <f, e>}
  if p eq 0 then
    _, inf := Conductor(F);
    k := BaseRing(F);
    r1, r2 := Signature(k);
    return [<1, 1> : i in [1..r1], j in [1..Degree(F)] | i notin inf]
      cat [<1,2> : i in [1..r1], j in [1..Degree(F) div 2] | i in inf] 
      cat [<1,1> : i in [1..r2], j in [1..Degree(F)]];  
  end if;
  lp := Decomposition(BaseRing(F), p);
  if Normal then
    ll := DecompositionType(F, lp[1][1]);
    ll := [ <i[1]*Degree(lp[1][1]), i[2]*lp[1][2]> : i in ll];
    l := ll;
    for i in [1..#lp-1] do
      l cat:= ll;
    end for;
  else
    l := [];
    l := &cat [ 
        [ <x[1]*Degree(y[1]), x[2]*y[2]> : x in DecompositionType(F, y[1])] :
          y in lp];
  end if;
  return l;
end intrinsic;  

function DecompositionFrequency(F, s, Normal)
  l := [];
  for i in s do
    if Normal then
      Append(~l, Set(DecompositionType(F, i:Normal)));
    else
      Append(~l, DecompositionType(F, i));
    end if;
  end for;
  return SequenceToMultiset(l);
end function;

intrinsic DecompositionTypeFrequency(F::FldAb, s::SeqEnum:Normal := false) -> SeqEnum
{Computes all decomposition types for the primes in s and returns a multiset with the types and their frequency}
  return DecompositionFrequency(F, s, Normal);
end intrinsic;

intrinsic DecompositionTypeFrequency(F::FldAb, s::RngIntElt, e::RngIntElt:Normal := false) -> SeqEnum
{Computes all decomposition types for the primes between s and e and returns a multiset with the types and their frequency}
  return DecompositionFrequency(F, [x : x in [s..e] | IsPrime(x)], Normal);
end intrinsic;

// XXX vpoly_hom and dpoly_hom should able to handle ideals!
function apply(aut, id)
  l := Generators(id);
  l := [aut(x) : x in l];
  return ideal<Order(id) | l>;
end function;

function is_normal_central(F, autos, central)
  // checks if F is normal wrt to autos (list of automorphisms)
  // if central is true, we check for this too
  // Algo:
  //   the field is normal iff
  //     the module (m0, m_inf) is invariant under autos
  //     (more precisely, if the conductor is invariant)
  //
  //     and if the "denominator" of the quotient group is invariant as 
  //     a set under autos:
  //     
  //     F = (I^m/P_m)/(H/P_m) where P_m < H < I^m
  //     so m and (H/P_m) must be set invariant under autos.
  //
  //     The field is central if in addition the action on
  //     I^m/H is trivial.

  rcg := F`DefiningGroup;
  if assigned F`NormGroup then
    rcg := F`NormGroup;
  end if;

  r1 := Signature(BaseRing(F));

  if #rcg`m_inf gt 0 and #rcg`m_inf ne r1 then
    // we must use the NormGroup!!
    if not assigned F`NormGroup then
      _ := Conductor(F);
    end if;
    assert assigned F`NormGroup;
    if rcg`m_inf ne F`NormGroup`m_inf then
      return is_normal_central(F, autos, central);
    end if;
    g_inf, m_inf := RayResidueRing(1*BaseRing(F), [1..r1]);
    s_inf := {g_inf.(i+1) : i in rcg`m_inf};
  else
    s_inf := {};
    m_inf := map<s_inf -> s_inf | x :-> x>;
  end if;
  if forall{x : x in autos | apply(x, rcg`m0) eq rcg`m0} and
     forall{x : x in autos | (m_inf*x*Inverse(m_inf))(s_inf) eq s_inf} then
    if not assigned rcg`GrpMap and not central then
      return true;
    else
      for i in autos do
        x := InducedAutomorphism(rcg`RcgMap, 
              map<Parent(rcg`m0) -> Parent(rcg`m0) | z :-> apply(i, z)>,
                                         Minimum(rcg`m0));
        g := Domain(rcg`RcgMap);
        if not assigned rcg`GrpMap then
          h := hom<g -> g | [ g.i : i in [1..Ngens(g)]]>;
        else
          h := hom<g -> Domain(rcg`GrpMap) |
                   [ g.i @@ rcg`GrpMap : i in [1..Ngens(g)]]>;
        end if;
        k := Kernel(h);
        if k ne x(k) then
          return false;
        end if;
        if central then
          q, mq := quo<g|k>;
          if exists{y : y in Generators(q) | x(y @@mq)@mq ne y} then
            return false;
          end if;
        end if;
      end for;
    end if;
    return true;
  else
    if F`NormGroup`m0 eq rcg`m0 and F`NormGroup`m_inf eq rcg`m_inf then
      // We've een qorking with the conductor already and the conductor is not
      // invariant under autos (othewise we would not be in this case)
      // So the group cannot define a normal extension:
      return false;
    end if;
    _ := Conductor(F); // this must set NormGroup!
    assert assigned F`NormGroup;
    return is_normal_central(F, autos, central);
  end if;
  return true;
end function;

import "ClassField2.m" : MyEq, MyMult;

function check_All_Over(k, All, Over)
  if not ( All cmpeq false or Over cmpeq false) then 
    error "Error: All and Over cannont be combined";
  end if;
  if not ( Over cmpeq false or 
    ( Type(Over) eq SeqEnum and #Over ge 1 and Type(Over[1]) eq Map)) then
    error "Error: Over must be a sequenc of Maps";
  end if;

  if All cmpne false then
    vprint ClassField, 2: "Computing automorphisms of the base field...";
    g := Automorphisms(k);
    // reduce g to include only a (minimal) set of generators:
    vprint ClassField, 2: "... done. Computing GenericGroup...";
    g, mg := GenericGroup(g: Id := hom<k->k|GeneratorsSequence(k)>,
                             Eq := MyEq,
                             Mult := MyMult);
                             
    vprint ClassField, 2: "... done. Finding small set of generators...";
    gen := FindGenerators(g);                         
    vprint ClassField, 2: "... done. Using ", #gen, " automorphisms";
    // extend them...
  else  
    gen := Over; 
    if Over cmpne false then
      vprint ClassField, 2: "Using ", #gen, " automorphisms";
      g := GenericGroup(gen: Id := hom<k->k|GeneratorsSequence(k)>,
                             Eq := MyEq,
                             Mult := MyMult);
    else  
      return [], _;
    end if;  
  end if;  

  return gen, g;
end function;
  

intrinsic IsNormal(F::FldAb : All := false, Over := false) -> BoolElt
{Tests if F will be normal}

  k := BaseField(F);
  g := check_All_Over(k, All, Over);
  if #g eq 0 then
    return true;
  end if;

  if All cmpne false then
    if assigned F`IsNormal then
      return F`IsNormal;
    end if;
    if assigned F`Record and assigned F`Record`CohomologyModule then
      F`IsNormal := true;
      return true;
    end if;
  end if;
  f := is_normal_central(F, g, false);
  if All cmpne false then
    F`IsNormal := f;
  end if;
  return f;

  return is_normal_central(F, g, false);
end intrinsic;  
 
intrinsic IsCentral(F::FldAb : All := false, Over := false) -> BoolElt
{Tests if F will be a central extension}

  k := BaseField(F);
  g := check_All_Over(k, All, Over);
  if #g eq 0 then
    return true;
  end if;

  if All cmpne false then
    if assigned F`IsCentral then
      return F`IsCentral;
    end if;
    if assigned F`Record and assigned F`Record`CohomologyModule then
      C := CohomologyModule(F);
      if forall{x :x in C`mats | IsOne(x)} then
        F`IsCentral := true;
      else
        F`IsCentral := false;
      end if;
      return F`IsCentral;
    end if;
  end if;
  f := is_normal_central(F, g, true);
  if All cmpne false then
    F`IsCentral := f;
  end if;
  return f;
end intrinsic;  

function check(K, g)
  if IsAbsoluteField(K) or
     forall{x : x in GeneratorsSequence(BaseRing(K), Rationals()),
                m in g
              | m(x) eq x}
  then
    return true, _;
  else
    return false, "The given automorphisms do not fix the base field";
  end if;
end function;

function _FixedField(K, g)
  b := Basis(K);
  aut_mat := function(e)
    return Matrix([Eltseq(K!e(i)) : i in b]);
  end function;
  M := Matrix(BaseField(K), Degree(K), 0, []);
  for i in g do
    M := HorizontalJoin(M, aut_mat(i) -
                      IdentityMatrix(BaseField(K), Degree(K)));
  end for;
  k := NullspaceMatrix(M);
  return sub<K| [K!Eltseq(k[x]) : x in [1..Nrows(k)]]>;
end function;

intrinsic FixedField(K::FldAlg, g :: SeqEnum[Intrinsic]) -> FldAlg
{The field fixed by the maps in g}
  bool, msg := check(K, g);
  require bool: msg;
  return _FixedField(K, g);
end intrinsic;

intrinsic FixedField(K::FldAlg, g :: SeqEnum[UserProgram]) -> FldAlg
{"} // "
  bool, msg := check(K, g);
  require bool: msg;
  return _FixedField(K, g);
end intrinsic;

intrinsic FixedField(K::FldAlg, g :: SeqEnum[Map]) -> FldAlg
{"} // "
  bool, msg := check(K, g);
  require bool: msg;
  return _FixedField(K, g);
end intrinsic;

function maximal_abel(F, g, do_abel)
  // computes the maximal abelian extension of the fixed field of g that is
  // inside F (or the maximal central extension if do_abel is false)
  //
  // so we 1st find the fix-field k of g and the discriminant d
  // (better the conductor) of BaseField(F) =: K over k
  // then transfer the DefiningGroup of F to be defined mod s.th.
  // that is a multiple of d
  // and compute things with ideals....

  if assigned F`NormGroup then
    rcg := F`NormGroup;
  else
    rcg := F`DefiningGroup;
  end if;

  K := BaseField(F);
  k := FixedField(K, g);
  if Degree(k) eq Degree(K) then
    return F;
  end if;
  if Degree(k) eq 1 then
    k := BaseField(K);
    Kr := K;
  else
    Kr := RelativeField(NumberField(k), NumberField(K));
  end if;
  if true then
    FF := MaximalAbelianSubfield(Kr);
                   // XXX we may skip this ... but it gives smaller values...
    vprint ClassField, 2: "MaximalAbelianSubfield is ", FF;
    c, c_inf := Conductor(FF);
  else
    c := Discriminant(MaximalOrder(Kr));
  end if;
  m := MaximalOrder(k);
  // Order(c);MaximalOrder(Kr);
  if IsAbsoluteField(Kr) then
    c := c*Minimum(MaximalOrder(Kr)!!rcg`m0);
  else
    c *:= Order(c)!!
       (BaseRing(MaximalOrder(Kr)) meet (MaximalOrder(Kr)!!rcg`m0));
  end if;
  gc, mgc := RayClassGroup(c, [1..Signature(k)]);
  M := MaximalOrder(K);
  Mr := MaximalOrder(Kr);
  if IsAbsoluteField(K) then
    gC, mgC := RayClassGroup(M*Minimum(c), [1..Signature(K)]);
  else
    gC, mgC := RayClassGroup(M!!c, [1..Signature(K)]);
  end if;
  map_mgC_rcg := InducedMap(mgC, rcg`Map, map<Parent(1*M)->Parent(1*M)| x :->x>,
                                Minimum(c));
  k := Kernel(map_mgC_rcg);
  if IsAbsoluteField(Kr) then
    map_mgC_mgc := InducedMap(mgC, mgc, 
            map<Parent(1*M)->Parent(c) | x :-> Order(c)*Norm(Mr!!x)>,
                                  Minimum(c));
  else
    map_mgC_mgc := InducedMap(mgC, mgc, 
         map<Parent(1*M)->Parent(c) | x :-> m!!(Norm(Mr!!x))>,
                                  Minimum(c));
  end if;

  q, mq := quo<gc | map_mgC_mgc(k)>;
  return AbelianExtension(Inverse(mq)*mgc);
end function;

intrinsic IsAbelian(F::FldAb : All := false, Over := false) -> BoolElt
{Tests if F will be an abelian extension over s.th.}

  k := BaseField(F);
  g := check_All_Over(k, All, Over);
  if #g eq 0 then
    return true;
  end if;

  // here we are stuck: we need to get access to the parts of the defining
  // map so that we can access the GrpAb part and the Ray part....
  // Suppose we can do it:
  //    get the defining module 
  //    get the subgroup that is in the denominator
  //    check for invariance, if neccessary, extend the module 1st
  //    check the action is trival
  // but this should happen in a subfunction...   
  //    and then, the hard part, construct some more groups...
  
  if All cmpne false then
    if assigned F`IsAbelian then
      return F`IsAbelian;
    end if;
  end if;
  f := is_normal_central(F, g, true);
  if All cmpne false and not f then
    F`IsAbelian := false;
    return false;
  end if;

  f := maximal_abel(F, g, true);
  if AbsoluteDegree(f) eq AbsoluteDegree(F) then
    if All cmpne false then
      F`IsAbelian := true;
    end if;
    return true;
  else
    if All cmpne false then
      F`IsAbelian := false;
    end if;
    return false;
  end if;
end intrinsic;  

intrinsic GenusField(F::FldAb: All := false, Over := false) -> FldAb
{Computes the genus field, i.e. the maximal abelian extension of the BaseField of the BaseField of F that is inside F}

  k := BaseField(F);
  g := check_All_Over(k, All, Over);
  if #g eq 0 then
    return true;
  end if;

 return maximal_abel(F, g, true);
end intrinsic;


function convert(elt, Mk, M, mo)
  X := Domain(M);
  Z := Domain(Mk);
  phi := Mk(elt);
  aut := InducedAutomorphism(M, phi, mo);
  return Matrix([Eltseq(aut(X.i)) : i in [1..Ngens(X)]]);
  // use InducedAut here!!! XXX and do it in C
end function;

intrinsic AbelianpExtension(m::Map, p::RngIntElt) -> FldAb
{The maximal p-extension defined by m}
  G := Domain(m);
  e := Valuation(#G, p);
  q, mq := quo<G|[p^e*G.i : i in [1..Ngens(G)]]>;
  return AbelianExtension(Inverse(mq)*m);
end intrinsic;


intrinsic ImproveAutomorphismGroup(F :: FldAb, E :: SeqEnum : Factor := 1) -> GrpFP, []
{Tries to improve the guess of ProbableAutomorphismGroup}
   l := [ SequenceToMultiset([Order(x) : x in 
                      Codomain(CosetAction(y, sub<y|>))]) : y in E];     

  vprint ClassField, 2: "Orders and multiplicies are ", l;

  L := DecompositionTypeFrequency(F, 100, 300:Normal);
  i := 301;
  while #L lt Factor * #E[1] do
    LL := DecompositionTypeFrequency(F, i, i+299:Normal);
    i +:= 300;
    L := L join LL;
  end while;

  L := {* Representative(i)[1] : i in L *};
  vprint ClassField, 2: "Probable orders and multiplicies are ", L;
  
  supp := &join [ Set(i) : i in l ] join Set(L);
  a := [ &+[(Multiplicity(i, j)/#i - Multiplicity(L, j)/#L)^2 : j in supp ] : i in l];
  b := [ 1.0*x : x in a];
  b := [x / c : x in b] where c is &+b;
  vprint ClassField, 1: "Error terms are ", b;
  return E[Position(a, Minimum(a))], E;
end intrinsic; 


intrinsic ProbableAutomorphismGroup(F :: FldAb : Factor := 1) -> GrpFP, []
{Uses extension theory and statistics to find the AutomorphismGroup of F}
  
  k := BaseField(F);
  g, _, p := AutomorphismGroup(k);

  A, mo := NormGroup(F);
  mo := AbsoluteNorm(mo);
  AA := InvariantRepresentation(Domain(A));
  mAA := hom<AA->Domain(A) | [Domain(A)!AA.i : i in [1..Ngens(AA)]]>;

  inv := AbelianInvariants(AA);
  mats := [ convert(g.i, p, mAA*A, mo) : i in [1..Ngens(g)]]; 
  
//  f := Open(GetTempDir() cat "/JOHN", "a");
//  fprintf f, "inv := %m;\ng := %m;\nmats := %m;\n//////////////////////////////\n", inv, g, mats;
 
  C := CohomologyModule(g, inv, mats);
  E := DistinctExtensions(C);
  vprint ClassField, 2 : "OK, found ", #E, "possible extensions";

  if #E eq 1 then
    return E[1];
  end if;

  a,b := ImproveAutomorphismGroup(F, E : Factor := Factor);
  return a,b;

end intrinsic;

intrinsic H2_G_A(F :: FldAb) -> GrpFP, []
{Computes the 2nd Cohomology group}
  
  k := BaseField(F);
  g, _, p := AutomorphismGroup(k);

  A, mo := NormGroup(F);
  mo := AbsoluteNorm(mo);
  AA := InvariantRepresentation(Domain(A));
  mAA := hom<AA->Domain(A) | [Domain(A)!AA.i : i in [1..Ngens(AA)]]>;

  inv := AbelianInvariants(AA);
  mats := [ convert(g.i, p, mAA*A, mo) : i in [1..Ngens(g)]]; 
//  f := Open(GetTempDir() cat "/JOHN", "a");
//  fprintf f, "inv := %m;\ng := %m;\nmats := %m;\n//////////////////////////////\n", inv, g, mats;

  C :=  CohomologyModule(g, inv, mats);
  E := CohomologyGroup(C, 2);
  return E;

end intrinsic;

