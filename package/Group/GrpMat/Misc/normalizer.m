freeze;

orbitAction := function(G, list, ModScalars)
    n := #list;
    assert n gt 0;
    K := G;
    phis := [PowerStructure(Map)|];
    Ps := [];
    Ks := [];
    i := 0;
    Done := ModScalars select
            func< K | forall{t: t in Generators(K)|IsScalar(t)} >
            else IsTrivial;
    repeat
        i +:= 1;
        phi_i, P_i, K_i := OrbitAction(G, list[i]);
        Append(~phis, phi_i);
        Append(~Ps, P_i);
        Append(~Ks, K_i);
        K := K meet K_i;
    until Done(K) or i eq n;
    DP, inj, proj := DirectProduct(Ps);
    IG := [ &*[ inj[i](phis[i](G.j)): i in [1 .. #Ps] ]: j in [1 .. Ngens(G)]];
    SP := sub<DP | IG >;
    forw := hom < G -> SP | IG >;
 
    return forw, SP, K;
end function;

orbitActionMS := function(G)
    V := RSpace(G);
    list := [ sub<V|V.i> : i in [1..Dimension(V)]];
    n := #list;
    I := [];
    i := 0;
    oldK := G;
    K := G;
    repeat
        i +:= 1;
        phi_i, P_i, K_i := OrbitAction(G, list[i]);
        if not oldK subset K_i then
          Append(~I,i);
          K := K meet K_i;
          oldK := K;
        end if;
    until  forall{t: t in Generators(K)|IsScalar(t)} or i eq n;
    if #I eq 0 then I := [1]; end if;
 
    return OrbitAction(G, {list[i]:i in I});
end function;

FaithfulRepresentation := function (G:ModScalars:=false)
   BSGS (G);
   if ModScalars then return orbitActionMS(G); end if;
   B := BasicOrbitLengths (G);
   L :=[**];
   for i in [1..#B] do
     r := Representative (BasicOrbit (G, i));
     Append(~L,r);
   end for;
   return orbitAction(G,L,ModScalars);
end function;

NormaliserOfMatrixGroup := function(G,H:ModScalars:=true)
/* Normaliser of H in matrix group G */
  if ModScalars then
    phi, P := FaithfulRepresentation(G:ModScalars:=true);
    N := Normaliser(P,phi(H)) @@ phi;
  else
    N := G;
  end if;
  if IsNormal(N, H) then
    return N;
  end if;
  phi, P := FaithfulRepresentation(N:ModScalars:=false);
  N := Normaliser(P,phi(H)) @@ phi;
  return N;
end function;

IsConjugateMatrixGroup := function(G,H,K:ModScalars:=true)
/* Are subgroups H,K of matrix group conjugate? */
  if not ModScalars then
     phi, P := FaithfulRepresentation(G);
     ans,g := IsConjugate(P,phi(H),phi(K));
     if ans then return true, g@@phi;
     else return false,_;
     end if;
  end if;
  phi, P := FaithfulRepresentation(G:ModScalars:=true);
  ans,g := IsConjugate(P,phi(H),phi(K));
  if not ans then return false,_; end if;
  g := g@@phi;
  Hg := H^g;
  if Hg eq K then return true,g; end if;
  //print "Must compute normalizer!";
  N := Normaliser(P,phi(K)) @@ phi;
  ans, h := $$(N, Hg, K : ModScalars:= false);
  if not ans then return false,_; end if;
  return true, g*h;
end function;

intrinsic PermutationRepresentation(G :: GrpMat: ModScalars := false) ->
          Map, GrpPerm, GrpMat
{A faithful permutation representation of matrix group G; faithful
modulo scalars if ModScalars set to true}
  return FaithfulRepresentation(G:ModScalars:=ModScalars);
end intrinsic;

intrinsic Normaliser(G :: GrpMat, H :: GrpMat) -> GrpMat
{Normaliser of H in matrix group G}
  if not H subset G then
    error "Normaliser: Second argument must be a subgroup of first";
  end if;
  if IsNormal(G,H) then return G; end if;
  if GrpMatUseLMG(G) then 
      return LMGNormaliser(G, H);
  else
      return NormaliserOfMatrixGroup(G,H:ModScalars:=true);
  end if;
end intrinsic;

/*
intrinsic Normalizer(G :: GrpMat, H :: GrpMat) -> GrpMat
{Normalizer of H in matrix group G}
  if not H subset G then
    error "Normalizer: Second argument must be a subgroup of first";
  end if;
  return NormaliserOfMatrixGroup(G,H:ModScalars:=true);
end intrinsic;
*/

intrinsic IsConjugate(G :: GrpMat, H :: GrpMat, K :: GrpMat) -> BoolElt,
          GrpMatElt
{Test subgroups of matrix group for conjugacy}
  gen := Generic(G);
  require gen cmpeq Generic(H): "1st and 2nd arguments must have same degree and field";
  require gen cmpeq Generic(K): "1st and 3rd arguments must have same degree and field";
  if #H ne #K then return false, _; end if;
  if not H subset G then
    error "IsConjugate: Second argument must be a subgroup of first";
  end if;
  if not K subset G then
    error "IsConjugate: Third argument must be a subgroup of first";
  end if;
  if IsNormal(G,H) or IsNormal(G,K) then
    if H eq K then return true, Id(G);
    else return false, _;
    end if;
  end if;
  if GrpMatUseLMG(G) then 
    return LMGIsConjugate(G, H, K);
  else
    return IsConjugateMatrixGroup(G,H,K:ModScalars:=true);
  end if;
end intrinsic;

intrinsic CompositionSeries(G :: GrpMat) -> SeqEnum
{Composition series of matrix group G}
local phi, P, K, cs1, cs2, KP, rho;
  if GrpMatUseLMG(G) then
    return LMGCompositionSeries(G);
  end if;
  phi, P, K := PermutationRepresentation(G : ModScalars:=true);
  cs1 := CompositionSeries(P);
  if #K eq 1 then
    return [ s @@ phi : s in cs1 ];
  end if;
  KP, rho := PCGroup(K);
  cs2 := CompositionSeries(KP);
  return [ s @@ phi : s in Prune(cs1) ] cat [ s @@ rho : s in cs2 ];
end intrinsic;
