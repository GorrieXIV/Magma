freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Minimal generators for arithmetic Fuchsian groups
// May 2006, June 2007, John Voight
//
//////////////////////////////////////////////////////////////////////////////

//-------------
//
// Algorithms to build a presentation for the group of units.
//
//-------------

declare attributes AlgAssVOrd: UnitGroup, UnitMap;

declare attributes GrpPSL2: ShimFDSidepairsDomain, ShimGroupSidepairs, ShimGroupSidepairsMap;

forward InternalShimuraSidepairs;

import "domain.m" : InternalShimuraMingens, AssignPrecision;

intrinsic Group(G::GrpPSL2) -> GrpFP, Map, Map
  {Returns a presentation U for the arithmetic Fuchsian group G,
   a map U -> G, and a map U -> BaseRing(G).}

  mOtoG := map<BaseRing(G) -> G | x :-> G!x>;

  if assigned G`ShimGroup then
    return G`ShimGroup, G`ShimGroupMap*mOtoG, G`ShimGroupMap;
  end if;
  if not assigned G`ShimFDDisc then
    B := Algebra(BaseRing(G));
    if not assigned B`prec then AssignPrecision(B); end if;
    D := UnitDisc(: Center := 9/10*UpperHalfPlane().1, Precision := B`prec);
    F := FundamentalDomain(G, D);
  end if;
  D := Universe(G`ShimFDDisc);
  U, m := InternalShimuraSidepairs(G, D);
  return U, m*mOtoG, m;
end intrinsic;

// Returns a minimal set of generators for the arithmetic Fuchsian group G.
InternalShimuraGenerators := function(G);
  U, m := Group(G);
  return [G!m(u) : u in Generators(U)];
end function;

intrinsic FixedPoints(g::GrpPSL2Elt, D::SpcHyd) -> SeqEnum
  {Returns the fixed points of g acting on D.}

  Z := FixedPoints(g, UpperHalfPlane());
  return [PlaneToDisc(D, z) : z in Z];
end intrinsic;

// Returns the pairing of sides from a the isometric circles of G.
InternalShimuraSidepairs := function(G,D)
  domain := G`ShimFDGens;
  O := BaseRing(G);
  A := Algebra(O);

  Z := G`ShimFDDisc;

  sidepairs := [];
  sidepairs2s := [];

  Deps := Round(100*Log(D`eps)^2)*D`eps;

  // First, find the sides which need to be "doubled"
  i := 1;
  while i le #domain do
    zst := Z[i];
    zend := Z[i mod #domain+1];
    if Abs((G!domain[i])*zst-zend) lt Deps then
      vprint Shimura, 3 : "Need to double side", i;
      domain := domain[1..i-1] cat [domain[i], domain[i]] cat domain[i+1..#domain];
      Z := Insert(Z, i+1, FixedPoints(G!domain[i], D)[1]);
      sidepairs2s cat:= [<domain[i], 2, [i,i mod #domain+1], 
                          [i mod #domain+1, (i+1) mod #domain+1]>];
      i +:= 1;
    end if;
    i +:= 1;
  end while;

  G`ShimFDSidepairsDomain := domain;
  domainG := ChangeUniverse(domain, G);

  // Construct a minimal generating set
  sides := [[i,i mod #domain+1] : i in [1..#domain]];

  vprint Shimura, 3: Z;

  i := 1;
  sidepairs2sst := [d[3] : d in sidepairs2s];
  edges := [];

  while #sides gt 0 and i le #domain do
    // First, identify the doubled sides.
    if [i,i mod #domain+1] in sidepairs2sst then
      j := Index(sidepairs2sst, [i, i mod #domain+1]);
      Append(~sidepairs, sidepairs2s[j]);
      Remove(~sides, Index(sides, [i,i mod #domain+1]));
      Remove(~sides, Index(sides, [i mod #domain+1, (i+1) mod #domain+1]));
      
      Append(~edges, <#sidepairs, [i, (i+1) mod #domain+1]>);
      Append(~edges, <#sidepairs, [i mod #domain+1, i mod #domain+1]>);
    elif [i,i mod #domain+1] in sides then 
      // Sides are paired with their inverses.
      j := 1;
      while not IsScalar(domain[j]*domain[i]) do
        j +:= 1;
      end while;

      pairedw1 := Abs(domainG[i]*Z[i]-Z[j]) lt Deps and
                     Abs(domainG[i]*Z[i mod #domain + 1]-Z[j mod #domain + 1]) lt Deps;
      pairedw2 := Abs(domainG[i]*Z[i]-Z[j mod #domain + 1]) lt Deps and
                     Abs(domainG[i]*Z[i mod #domain + 1]-Z[j]) lt Deps;

      zz00 := Abs(domainG[i]*Z[i]-Z[j]);
      assert not (zz00 gt Deps and zz00 lt Sqrt(Deps));
      zz00 := Abs(domainG[i]*Z[i mod #domain + 1]-Z[j mod #domain + 1]);
      assert not (zz00 gt Deps and zz00 lt Sqrt(Deps));
      zz00 := Abs(domainG[i]*Z[i]-Z[j mod #domain + 1]);
      assert not (zz00 gt Deps and zz00 lt Sqrt(Deps));
      zz00 := Abs(domainG[i]*Z[i mod #domain + 1]-Z[j]);
      assert not (zz00 gt Deps and zz00 lt Sqrt(Deps));

      if pairedw1 and j eq i+1 then
        // Elliptic element fixes i+1.
        k := MultiplicativeOrder(domain[i]);
        Append(~sidepairs, 
          <domain[i], k, [i,i mod #domain+1], [i mod #domain+1, (i+1) mod #domain+1]>);
        Remove(~sides, Index(sides, [i,i mod #domain+1]));
        Remove(~sides, Index(sides, [i mod #domain+1, (i+1) mod #domain+1]));
        
        Append(~edges, <#sidepairs, [i, (i+1) mod #domain+1]>);
        Append(~edges, <#sidepairs, [i mod #domain+1, i mod #domain+1]>);
      elif pairedw1 or pairedw2 then
        Append(~sidepairs, 
          <domain[i], 0, [i,i mod #domain+1], [j, j mod #domain+1]>);
        Remove(~sides, Index(sides, [i,i mod #domain+1]));
        Remove(~sides, Index(sides, [j,j mod #domain+1]));
        
        if pairedw1 then
          // [i,j] and [i+1,j+1] are paired
          Append(~edges, <#sidepairs, [i,j]>);
          Append(~edges, <#sidepairs, [i mod #domain+1, j mod #domain+1]>);
        elif pairedw2 then
          Append(~edges, <#sidepairs, [i,j mod #domain+1]>);
          Append(~edges, <#sidepairs, [i mod #domain+1, j]>);
        end if;
      else
        error "Unpaired side?";
      end if;
    end if;
    i +:= 1;
  end while;

  vprint Shimura, 3: "Sidepairs and edges computed!", sidepairs, edges;

  M := MultiDigraph<#domain |>;
  AssignLabels(~M, Vertices(M), [1..#Vertices(M)]);
  V := VertexSet(M);

  for e in edges do
    AddEdge(~M, V.e[2][1], V.e[2][2], e[1]);
    if V.e[2][1] ne V.e[2][2] then
      AddEdge(~M, V.e[2][2], V.e[2][1], -e[1]);
    end if;
  end for;

  ml := StronglyConnectedComponents(M);
  ml := [SetToSequence(m) : m in ml];
  words := [];
  for i := 1 to #ml do
    w := [];
    for j := 1 to #ml[i] do
      e := Edges(ml[i][j],ml[i][j mod #ml[i]+1]);
      while #e eq 0 do
        ml[i] := ml[i][1..j] cat ml[i][j+2..#ml[i]] cat [ml[i][j+1]];
        e := Edges(ml[i][j],ml[i][j mod #ml[i]+1]);
      end while;
      if #w eq 0 or -Label(e[1]) ne w[#w] then
        Append(~w, Label(e[1]));
      else
        Append(~w, Label(e[2]));        
      end if;
    end for;
    Append(~words, Reverse(w));
  end for;

  vprint Shimura, 3: words;

  for i := 1 to #words do
    w := &*[ sidepairs[Abs(s)][1]^Sign(s) : s in words[i]];
    wpow := w;
    e := 1;
    while not IsScalar(wpow) do
      wpow *:= w;
      e +:= 1;
    end while;
    words[i] := &cat[ words[i] : j in [1..e]];
  end for;

  gammagens := [s[1] : s in sidepairs];
  orders := [s[2] : s in sidepairs];

  Gfree := FreeGroup(#gammagens);
  U := quo<Gfree | [Gfree.i^orders[i] : i in [1..#orders]] cat 
                   [Gfree!w : w in words]>;
  m := map<U -> O | x :-> &*([A!1] cat [ gammagens[Abs(s)]^Sign(s) : s in Eltseq(x)])>;
 
  G`ShimGroupSidepairs := U;

  if assigned G`TriangleBool and G`TriangleBool then
    // Cosmetic reordering for triangle groups
    gammagens := [m(U.1), m(U.2), m((U.1*U.2)^(-1))];
    orders := [MultiplicativeOrder(g) : g in gammagens];

    while orders[1] ge orders[2] do
      gammagens := gammagens[2..#gammagens] cat [gammagens[1]];
      orders := orders[2..#orders] cat orders[1..1];
    end while;
    if orders[3] ge orders[1] and orders[3] lt orders[2] then
      gammagens := Reverse(gammagens);
      gammagens := [gamma^(-1) : gamma in gammagens];
      orders := Reverse(orders);
    end if;
    if orders[3] lt orders[1] and orders[3] lt orders[2] then
      gammagens := [gammagens[3]] cat gammagens[1..2];
      orders := [orders[3]] cat orders[1..2];
    end if;

    Gfree := FreeGroup(3);
    U := quo<Gfree | [Gfree.i^orders[i] : i in [1..#orders]] cat 
                     [Gfree.1*Gfree.2*Gfree.3]>;
    m := map<U -> O | x :-> &*([A!1] cat [ gammagens[Abs(s)]^Sign(s) : s in Eltseq(x)])>; 
  else
    P := TietzeProcess(U);
    SimplifyPresentation(~P);
    U, f := Group(P);
    G`ShimGroupSidepairsMap := f;
    m := f^(-1)*m;
  end if;

/*
  // Simplify
  eliminateList := [i : i in [1..#orders] | orders[i] eq 0];
  for l in eliminateList do
    Eliminate(~P : Generator := l);
  end for;
  Up, f := Group(P);
*/

  G`ShimGroup := U;
  G`ShimGroupMap := m;
  G`ShimFDSidepairs := sidepairs;

  return G`ShimGroup, G`ShimGroupMap;
end function;
