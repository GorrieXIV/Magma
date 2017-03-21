freeze;

import "lmgrec.m": ZZZ;
import "initialize.m": Initialize, GetCompSer, NameChange;
import "rearrange.m": Rearrange, CanCalculateAutGpAndMaxSubs;
import "sections.m": InSR, GetSolRad, GetUniRad, GetPKer, GetSocleAct,
                     GetChiefSer;
import "gmodsocstar.m" : Gmodsocstar;
import "radquot.m" : GetRadquot;
import "centconj.m": EltCent, IsConj, ConjClasses;
import "maxsubs.m": MaxSubs;
import "lisubs.m": LISubs;
import "normsubs.m": NormSubs;
import "normconj.m": SubNorm, SubIsConj;
import "sylow.m": SylSub;
import "meet.m": MeetSubs;
import "cosact.m": CosAct;
import "stabblock.m": StabBlock;
import "../CompTree/GrpMat/Smash/functions.m": SetImprimitiveFlag,
       ImprimitiveFlag;

intrinsic SetLMGSchreierBound(n :: RngIntElt)
{Set the bound on basic orbit lengths used by RandomSchreierBounded}
  local lmgv;
  //need to do something first for some reason
  lmgv := GetVerbose("LMG");
  SetVerbose("LMG",0);
  _:=LMGOrder(GL(1,2));
  SetVerbose("LMG",lmgv);
  ZZZ := Integers();
  ZZZ`LMGSchreierBound := n;
end intrinsic;

intrinsic LMGInitialise(G :: GrpMat[FldFin] : Al := "", Verify := false,
             RandomSchreierBound := ZZZ`LMGSchreierBound )
{Initialize G for LMG computations, Return true if using BGSG}
   if Al cmpne "" and Al cmpne "RandomSchreier" and
      Al cmpne "CompositionTree" and Al cmpne "CT" and Al cmpne "RS" then
     error "Unknown algorithm:",Al;
   end if;
   Initialize(G : Al := Al, Verify := Verify,
                                 RandomSchreierBound := RandomSchreierBound);
   //return G`LMGNode`RS;
end intrinsic;

intrinsic LMGInitialize(G :: GrpMat[FldFin] : Al := "", Verify:=false,
             RandomSchreierBound := ZZZ`LMGSchreierBound )
{Initialize G for LMG computations, Return true if using BGSG}
   LMGInitialise(G : Al := Al, Verify:=Verify,
             RandomSchreierBound := RandomSchreierBound );
end intrinsic;

intrinsic LMGCompositionSeries(G :: GrpMat[FldFin]) -> SeqEnum
{Composition series of large matrix group G}
  local GG, S, P, m1;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return CompositionSeries(G);
  end if;
  if assigned G`LMGNode`isunirad and G`LMGNode`isunirad then
    GG := G`LMGNode`uniradgp;
    S, P, m1 := LMGUnipotentRadical(GG);
    return [ sub< Generic(G) | {x @@ m1 : x in Generators(s)} > : 
                                 s in CompositionSeries(P) ];
  end if;
  if assigned G`LMGNode`israd and G`LMGNode`israd then
    GG := G`LMGNode`radgp;
    S, P, m1 := LMGSolvableRadical(GG);
    return [ sub< Generic(G) | {x @@ m1 : x in Generators(s)} > : 
                                 s in CompositionSeries(P) ];
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  return Reverse(G`LMGNode`series);
end intrinsic;

intrinsic LMGCompositionFactors(G :: GrpMat[FldFin]) -> SeqEnum
{Composition factors of large matrix group G}
  local GG, S, P;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return CompositionFactors(G);
  end if;
  if assigned G`LMGNode`isunirad and G`LMGNode`isunirad then
    GG := G`LMGNode`uniradgp;
    S, P := LMGUnipotentRadical(GG);
    return CompositionFactors(P);
  end if;
  if assigned G`LMGNode`israd and G`LMGNode`israd then
    GG := G`LMGNode`radgp;
    S, P := LMGSolvableRadical(GG);
    return CompositionFactors(P);
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  return SequenceToCompositionFactors(
            Reverse([NameChange(t) : t in G`LMGNode`factorname]) );
end intrinsic;

intrinsic LMGOrder(G :: GrpMat[FldFin]) -> RngIntElt
{Order of large matrix group G}
  if assigned G`Order then return Order(G); end if;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  return Order(G);
end intrinsic;

intrinsic LMGFactoredOrder(G :: GrpMat[FldFin]) -> SeqEnum
{Factored order of large matrix group G}
  if assigned G`Order then return FactoredOrder(G); end if;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  return FactoredOrder(G);
end intrinsic;

intrinsic LMGIsIn(G :: GrpMat[FldFin], x :: GrpMatElt) -> BoolElt, GrpSLPElt
{Is x in large matrix group G?}
  local GG, t, ingp, w;
  if not x in Generic(G) then
    error "Could not find a covering group";
  end if;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    if x in G then
      return true, InverseWordMap(G)(x);
    end if;
    return false, _;
  end if;
  if assigned G`LMGNode`isunirad and G`LMGNode`isunirad then
    GG := G`LMGNode`uniradgp;
    t, w := CompositionTreeElementToWord(GG, x);
    if t and CompositionTreeFactorNumber(GG, x) - 1 le GG`LMGNode`ngensu then
      return true, CompositionTreeNiceToUser(G)(w);
    end if;
    return false, _;
  end if;
  if assigned G`LMGNode`israd and G`LMGNode`israd then
    GG := G`LMGNode`radgp;
    t, w := InSR(GG, x);
    if t then
      return true, CompositionTreeNiceToUser(GG)(w);
    end if;
    return false, _;
  end if;
  t, w := CompositionTreeElementToWord(G, x);
  if t then
    return true, CompositionTreeNiceToUser(G)(w);
  end if;
  return false, _;
end intrinsic;

intrinsic LMGIsSubgroup(G :: GrpMat[FldFin], H :: GrpMat[FldFin]) -> BoolElt
{Is H a subgroup of large matrix group G?}
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  return forall{x : x in Generators(H) | LMGIsIn(G,x)};
end intrinsic;

intrinsic LMGIndex(G :: GrpMat[FldFin], H :: GrpMat[FldFin]) -> RngIntElt
{Index of subgroup H of large matrix group G}
  require LMGIsSubgroup(G, H): "Second argument is not a subgroup of first.";
  if assigned H`Order then return #G div #H; end if;
  if not assigned H`LMGNode then
    Initialize(H : Verify := G`LMGNode`verified );
  end if;
  return #G div #H;
end intrinsic;

intrinsic LMGEqual(G :: GrpMat[FldFin], H :: GrpMat[FldFin]) -> BoolElt
{Are large matrix groups H,G equal?}
  return LMGIsSubgroup(G,H) and LMGIsSubgroup(H,G);
end intrinsic;

intrinsic LMGIsNormal(G :: GrpMat[FldFin], H :: GrpMat[FldFin]) -> BoolElt
{Is H a normal subgroup of G?}
  require LMGIsSubgroup(G, H): "Second argument is not a subgroup of first.";
  if not assigned H`LMGNode then
    Initialize(H : Verify := G`LMGNode`verified );
  end if;
  return
     forall{<x,y> : x in Generators(H), y in Generators(G) | LMGIsIn(H,x^y)};
end intrinsic;

intrinsic LMGNormalClosure(G :: GrpMat[FldFin], H :: GrpMat[FldFin]) -> GrpMat
{Normal closure of subgroup H of large matrix group G?}
  local ng, RPH, RPG;
  require LMGIsSubgroup(G, H): "Second argument is not a subgroup of first.";
  if G`LMGNode`RS then
    return ncl< G | H >;
  end if;
  RPH := RandomProcess(H);
  RPG := RandomProcess(G);
  ng := Min(Max([Ngens(G),10]), 20);
  K := H;
  repeat
    K := sub< Generic(G) | K, [ Random(RPH)^Random(RPG) : i in [1..ng]] >;
    ng *:= 2; 
  until LMGIsNormal(G, K);
  return K;
end intrinsic;

intrinsic LMGDerivedGroup(G :: GrpMat[FldFin]) -> GrpMat
{Derived group of large matrix group G}
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return DerivedGroup(G);
  end if;
  if Ngens(G) gt 6 then
    gens := [];
    repeat
      for i in [1..20] do Append(~gens, (Random(G),Random(G)) ); end for;
      D := LMGNormalClosure(G, sub< Generic(G) | gens > );
    until forall{t : t in &cat[ [<i,j> : j in [1..i-1]] : i in [1..Ngens(G)] ]
                     | LMGIsIn(D, (G.t[1],G.t[2])) };
    return D;
  end if;
  return LMGNormalClosure(G, H) where H := sub< Generic(G) |
        &cat[ [ (G.i,G.j) : j in [1..i-1] ] :  i in [2..Ngens(G)] ] >;
end intrinsic;

intrinsic LMGCommutatorSubgroup(H :: GrpMat[FldFin], K :: GrpMat[FldFin]) ->
       GrpMat
{Commutator subgroup of large matrix groups H, K <= GL(n,q)}
  local G;
  require Generic(H) eq Generic(K): "Arguments have no common overgroup.";
  if not assigned H`LMGNode then
    Initialize(H);
  end if;
  if not assigned K`LMGNode then
    Initialize(K);
  end if;
  if H`LMGNode`RS and K`LMGNode`RS then
    return CommutatorSubgroup(Generic(H),H,K);
  end if;
  if LMGIsSubgroup(H,K) then G := H;
  elif LMGIsSubgroup(K,H) then G := K;
  else G := sub< Generic(H) | H,K >;
  end if;
  if Ngens(H) * Ngens(K) gt 20 then
    gens := [];
    repeat
      for i in [1..20] do Append(~gens, (Random(H),Random(K)) ); end for;
      D := LMGNormalClosure(G, sub< Generic(G) | gens > );
    until forall{ <i,j> : i in [1..Ngens(H)], j in [1..Ngens(K)]
                     | LMGIsIn(D, (H.i,K.j)) };
    return D;
  end if;
  return LMGNormalClosure(G, L) where L := sub< Generic(H) |
                         [ (h,k) : h in Generators(H), k in Generators(K) ] >;
end intrinsic;

intrinsic LMGIsSolvable(G :: GrpMat[FldFin]) -> BoolElt
{Is large matrix group G solvable?}
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return IsSolvable(G);
  end if;
  if assigned G`LMGNode`isunirad and G`LMGNode`isunirad then
    return true;
  end if;
  if assigned G`LMGNode`israd and G`LMGNode`israd then
    return true;
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  return forall{f : f in G`LMGNode`factorsol | f};
end intrinsic;

intrinsic LMGIsSoluble(G :: GrpMat[FldFin]) -> BoolElt
{Is large matrix group G solvable?}
  return LMGIsSolvable(G);
end intrinsic;

intrinsic LMGUnipotentRadical(G :: GrpMat[FldFin]) -> GrpMat, GrpPC, Map
{Unipotent radical S of large matrix group G, P=PCGroup(S), and map S->P}
  local S, P, m1;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    S := pCore( G, Characteristic(BaseRing(G)) );
    P, m1 := PCGroup(S);
    return S, P, m1;
  end if;
  if assigned G`LMGNode`isunirad and G`LMGNode`isunirad then
    G := G`LMGNode`uniradgp;
  end if;
  if assigned G`LMGNode`israd and G`LMGNode`israd then
    G := G`LMGNode`radgp;
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`uniradPC then
    GetUniRad(G);
  end if;
  return G`LMGNode`unirad, G`LMGNode`uniradPC, G`LMGNode`uniradtoPC;
end intrinsic;

intrinsic LMGSolvableRadical(G :: GrpMat[FldFin]) -> GrpMat, GrpPC, Map
{Solvable radical S of large matrix group G, P=PCGroup(S), and map S->P}
  local S, P, m1;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    S := SolvableRadical(G);
    P, m1 := PCGroup(S);
    return S, P, m1;
  end if;
  if assigned G`LMGNode`isunirad and G`LMGNode`isunirad then
    G := G`LMGNode`uniradgp;
      return G`LMGNode`unirad, G`LMGNode`uniradPC,
         G`LMGNode`uniradtoPC;
  end if;
  if assigned G`LMGNode`israd and G`LMGNode`israd then
    G := G`LMGNode`radgp;
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`radPC then
    GetSolRad(G);
  end if;
  return G`LMGNode`rad, G`LMGNode`radPC, G`LMGNode`radtoPC;
end intrinsic

intrinsic LMGSolubleRadical(G :: GrpMat[FldFin]) -> GrpMat, GrpPC, Map
{Solvable radical S of large matrix group G, P=PCGroup(S), and map S->P}
  return LMGSolvableRadical(G);
end intrinsic;

intrinsic LMGPCGroup(G :: GrpMat[FldFin]) -> GrpPC, Map
{PC presentation P of large matrix group G and map G->P}
  local P, m;
  require LMGIsSolvable(G) : "Argument of LMGPVGroup must be solvable";
  _, P, m := LMGSolvableRadical(G);
  return P, m;
end intrinsic;

intrinsic LMGFittingSubgroup(G :: GrpMat[FldFin]) -> GrpMat, GrpPC, Map
{Fitting subgroup S of large matrix group G, P=PCGroup(S), and map S->P}
  local S, P, m1;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    S := SolvableRadical(G);
    P, m1 := PCGroup(S);
    P := FittingSubgroup(P);
    S := P @@ m1;
    return S, P, m1;
  end if;
  if assigned G`LMGNode`isunirad and G`LMGNode`isunirad then
    G := G`LMGNode`uniradgp;
      return G`LMGNode`unirad, G`LMGNode`uniradPC, G`LMGNode`uniradtoPC;
  end if;
  if assigned G`LMGNode`israd and G`LMGNode`israd then
    G := G`LMGNode`radgp;
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`radPC then
    GetSolRad(G);
  end if;
  P := FittingSubgroup(G`LMGNode`radPC);
  S := sub< Generic(G) | [ g @@ G`LMGNode`radtoPC : g in Generators(P) ] >;
  return S, P, G`LMGNode`radtoPC;
end intrinsic

intrinsic LMGpCore(G :: GrpMat[FldFin], p :: RngIntElt) -> GrpMat, GrpPC, Map
{pCore S of large matrix group G, P=PCGroup(S), and map S->P}
  local S, P, m1;
  require IsPrime(p):
    "Second argument of pCore must be prime";
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    S := SolvableRadical(G);
    P, m1 := PCGroup(S);
    P := pCore(P,p);
    S := P @@ m1;
    return S, P, m1;
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`radPC then
    GetSolRad(G);
  end if;
  P := pCore(G`LMGNode`radPC,p);
  S := sub< Generic(G) | [ g @@ G`LMGNode`radtoPC : g in Generators(P) ] >;
  return S, P, G`LMGNode`radtoPC;
end intrinsic

intrinsic LMGIsNilpotent(G :: GrpMat[FldFin]) -> BoolElt
{Is large matrix group G nilpotent?}
  if not LMGIsSoluble(G) then return false; end if;
  _, P := LMGSolubleRadical(G);
  return IsNilpotent(P);
end intrinsic;

intrinsic LMGCentre(G :: GrpMat[FldFin]) -> GrpMat 
{Centre of large matrix group G}
  local S, P, m1, Z, C, AC, phi, inv, r, mats, mat, id, z, invmat,
        csm, ns, gens, a;
  /* We calculate the fixed point space of the action of G on the centre
   * of the souble radical using the nullspace computation from
   * ZeroCohomologyGroup
   */
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return Centre(G);
  end if;
  S, P, m1 := LMGSolvableRadical(G);
  C := Centre(P);
  if #C eq 1 then return sub<G|>; end if;
  if LMGIsSoluble(G) then
    return sub< Generic(G) | [x @@ m1 : x in Generators(C)] >;
  end if;
  AC, phi := AbelianGroup(C); //phi: C->AC
  inv := Invariants(AC);
  r := #inv;
  Z := Integers();
  mats := [ MatrixAlgebra(Z,r) | ];
  id := IdentityMatrix(Z,r);
  z := ZeroMatrix(Z,r,r);
  for i in [1..Ngens(G)] do
    mat :=
     Matrix( [ Eltseq( ((AC.j @@ phi @@ m1)^G.i) @ m1 @ phi ) : j in [1..r] ] )
              - id;
    if mat ne z then Append( ~mats, mat ); end if;
  end for;

  if #mats eq 0 then
    return sub< Generic(G) | [ AC.j @@ phi @@ m1 : j in [1..r] ] >;
  end if;

  invmat := z;
  for i in [1..r] do invmat[i][i] := inv[i]; end for;
  vmats := [];
  for i in [1..#mats] do
    vmats[i] := VerticalJoin( [mats[i]] cat [ z : j in [1..i-1] ] cat
                              [invmat] cat [ z : j in [i+1..#mats] ] );
  end for;
  csm := HorizontalJoin(vmats);
  ns := Matrix( Basis( Nullspace(csm) ) );
  gens := []; //generators of centre
  for i in [1..Nrows(ns)] do
    a := AC!Eltseq( ExtractBlock(ns,i,1,1,r) );
    if a ne AC!0 then Append( ~gens, a @@ phi @@ m1 ); end if;
  end for;

  return sub< Generic(G) | gens >;
end intrinsic;

intrinsic LMGCenter(G :: GrpMat[FldFin]) -> GrpMat 
{Center of large matrix group G}
  return LMGCentre(G);
end intrinsic;

intrinsic LMGSocleStar(G :: GrpMat[FldFin]) -> GrpMat
{Inverse image in large matrix group G of Socle(G/SolubleRadical(G))}
  local Q, phi;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if LMGIsSoluble(G) then
    return G;
  end if;
  if G`LMGNode`RS then
    Q, phi := RadicalQuotient(G);
    return Socle(Q) @@ phi;
  end if;
  if not assigned G`LMGNode`socstar then
    Rearrange(G);
  end if;
  return G`LMGNode`socstar;
end intrinsic;

intrinsic LMGSocleStarFactors(G :: GrpMat[FldFin]) -> SeqEnum, SeqEnum
{The simple factors of Socle(G/SolubleRadical(G)) for large matrix group
 G, possible represented projectively, together with associated maps
 form factors to G that define homomorphisms to G/SolubleRadical(G)}
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if LMGIsSoluble(G) then
    return [], [];
  end if;
  r := G`LMGNode;
  if r`RS then
    Q, phi := RadicalQuotient(G);
    sf := SocleFactors(Q);
    return sf, [ map< S->G | x :-> x @@ phi, x :-> S!(x @ phi) > : S in sf ];
  end if;
  if not assigned r`socstar then
    Rearrange(G);
  end if;
  ims := [* Codomain(t) : t in r`tofacs *];
  cslen := #r`ims;
  sf := [ i : i in [1..cslen] | r`factortype[i] eq 2 ]; 
  return [ r`ims[i] : i in sf ],
         [ map< Generic(r`ims[i]) -> Generic(G) |
                x :-> x @ Function(r`fromfacs[i]),
                x :-> x @ Function(r`tofacs[i]) > : i in sf ];
end intrinsic;

intrinsic LMGSocleStarActionKernel(G :: GrpMat[FldFin]) -> GrpMat, GrpPC, Map
{Kernel K of large matrix group G in its permutation action on socle factors,
P = PCGroup(K/SocleStar(G)) and map K->P}
  local Q, phi, psi, P, K, SQ, rho, SQP, m;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if LMGIsSoluble(G) then
    return G, PCGroup(Sym(1)), map< Generic(G)->P | x :-> Id(P), x :-> Id(G)  >;
  end if;
  if G`LMGNode`RS then
    Q, phi := RadicalQuotient(G);
    psi, P, K := SocleAction(Q);
    SQ, rho := SocleQuotient(K);
    SQP, m := PCGroup(SQ);
    return K @@ phi, SQP,
           map< Generic(G)->SQP | x:-> x @ phi @ rho @ m, 
                                  x :-> x @@m @@ rho @@ phi >;
  end if;
  if not assigned G`LMGNode`pkerPC then
    GetPKer(G);
  end if;
  return G`LMGNode`pker, G`LMGNode`pkerPC, G`LMGNode`pkertoPC;
end intrinsic;

intrinsic LMGSocleStarAction(G :: GrpMat[FldFin]) -> Map, GrpPerm, GrpMat
{Action of large matrix group G on socle factors, with image and kernel}
  local Q, phi, psi, P, K, SQ;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if LMGIsSoluble(G) then
    Q := Sym(1);
    return map< Generic(G)->Q | x :-> Id(Q), x :-> Id(G) >, Q, G;
  end if;
  if G`LMGNode`RS then
    Q, phi := RadicalQuotient(G);
    psi, P, K := SocleAction(Q);
    return map< Generic(G)->P | x:-> x @ phi @ psi, x:-> x @@psi @@ phi >,
           P, K @@ phi;
  end if;
  if not assigned G`LMGNode`Gtosocperm then
    GetSocleAct(G);
  end if;
  return
     G`LMGNode`Gtosocperm, G`LMGNode`socperm, G`LMGNode`pker;
end intrinsic;

intrinsic LMGSocleStarQuotient(G :: GrpMat[FldFin]) -> GrpPerm, Map, GrpMat
{Quotient of large matrix group G by SocleStar(G) with quotient map and kernel}
  local Q, phi, sq, m, k;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    Q, phi := RadicalQuotient(G);
    sq, m, k := SocleQuotient(Q);
    return sq, phi*m, k@@phi;
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`rad then
    Rearrange(G);
  end if;
  if not assigned G`LMGNode`Gtosocperm then
    GetSocleAct(G);
  end if;
  if not assigned G`LMGNode`Gmodsocstar then
    Gmodsocstar(G);
  end if;
  return G`LMGNode`Gmodsocstar, G`LMGNode`GtoGmodsocstar, G`LMGNode`socstar;
end intrinsic;

intrinsic LMGRadicalQuotient(G :: GrpMat[FldFin]) -> GrpPerm, Map, GrpMat
{Quotient of large matrix group G by SolubleRadical(G) with quotient map and
kernel}
  local Q, phi, sq, m, k;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    Q, m, k := RadicalQuotient(G);
    return Q, m, k;
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`rad then
    Rearrange(G);
  end if;
  if not assigned G`LMGNode`Gtosocperm then
    GetSocleAct(G);
  end if;
  if not assigned G`LMGNode`radquot then
    GetRadquot(G);
  end if;
  return G`LMGNode`radquot, G`LMGNode`Gtoradquot, G`LMGNode`rad;
end intrinsic;

intrinsic LMGChiefSeries(G :: GrpMat[FldFin]) -> SeqEnum
{Chief series of large matrix group G}
  local GG, S, P, m1;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return ChiefSeries(G);
  end if;
  _ := CompositionTree(G);
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  return Reverse(G`LMGNode`cseries);
end intrinsic;

intrinsic LMGChiefFactors(G :: GrpMat[FldFin]) -> SeqEnum
{Chief factors of large matrix group G}
  local GG, S, P, m1;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return ChiefFactors(G);
  end if;
  _ := CompositionTree(G);
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  return SequenceToCompositionFactors( Reverse(G`LMGNode`cfactorname) );
end intrinsic;

intrinsic LMGSylow(G :: GrpMat[FldFin], p :: RngIntElt) -> GrpMat
{Sylow p-subgroup of large matrix group G}
  local GG, S, P, m1;
  require p le 2^30 : "The prime p for LMGSylow(G, p) may not exceed 2^30";
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return Sylow(G, p);
  end if;
  if assigned G`LMGNode`isunirad and G`LMGNode`isunirad then
    GG := G`LMGNode`uniradgp;
    if p eq Characteristic(BaseRing(G)) then
      return G;
    else return sub< G | >;
    end if;
  end if;
  if assigned G`LMGNode`israd and G`LMGNode`israd then
    GG := G`LMGNode`radgp;
    S, P, m1 := LMGSolvableRadical(GG);
    return  sub< Generic(G) | {x @@ m1 : x in Generators( Sylow(P, p) )} >;
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  return SylSub(G, p);
end intrinsic;

intrinsic LMGCentraliser(G :: GrpMat[FldFin], g :: GrpMatElt :
                                               N:=0, layers:={}) -> GrpMat
{Centraliser of g in large matrix group G}
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return Centraliser(G,g);
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  if not assigned G`LMGNode`radquot then
    GetRadquot(G: warning:=true);
  end if;
  return  EltCent(G,g : N:=N,layers:=layers);
end intrinsic;

intrinsic LMGCentralizer(G :: GrpMat[FldFin], g :: GrpMatElt :
                                               N:=0, layers:={}) -> GrpMat
{Centralizer of g in large matrix group G}
  return LMGCentraliser(G,g : N:=N, layers:=layers);
end intrinsic;

intrinsic LMGIsConjugate(G :: GrpMat[FldFin], g :: GrpMatElt, h :: GrpMatElt :
                                        N:=0, layers:={}) -> BoolElt, GrpMatElt
{Test g and h for conjugacy in large matrix group G}
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return IsConjugate(G,g,h);
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  if not assigned G`LMGNode`radquot then
    GetRadquot(G: warning:=true);
  end if;
  return  IsConj(G,g,h : N:=N, layers:=layers);
end intrinsic;

intrinsic LMGClasses(G :: GrpMat[FldFin] : N:=0, layers:={} ) -> SeqEnum
{Conjugacy classes of large matrix group G}
  local cl;
  if HasAttribute(G, "Classes") then
      cl  := Classes(G);
      return cl, [ClassCentralizer(G,i) : i in [1..#cl]];
  end if;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    cl  := Classes(G);
    return cl, [ClassCentralizer(G,i) : i in [1..#cl]];
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  if not assigned G`LMGNode`radquot then
    GetRadquot(G: warning:=true);
  end if;
  cl, cents :=  ConjClasses(G : N:=N, layers:=layers );
  /* force the result of Classes(G) to be what this returns */
  G`Classes := <cl, cents>;
  cl  := Classes(G);
  return cl, [ClassCentralizer(G,i) : i in [1..#cl]];
end intrinsic;

intrinsic LMGConjugacyClasses(G :: GrpMat[FldFin]:  N:=0, layers:={}) ->
                                                               SeqEnum
{Conjugacy classes of large matrix group G}
  return LMGClasses(G : N:=N, layers:=layers);
end intrinsic;

intrinsic LMGMaximalSubgroups(G :: GrpMat[FldFin]) -> SeqEnum
{Conjugacy classes of maximal subgroups of large matrix group G}
  local factorsol, factorname;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return MaximalSubgroups(G);
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  //Let's check first if there is any hope of doing this!
  factorsol:=G`LMGNode`factorsol;
  factorname:=G`LMGNode`factorname;
  for cfno in [1..#factorname] do
    if not factorsol[cfno] and
        not CanCalculateAutGpAndMaxSubs(NameChange(factorname[cfno])) then
   error "Cannot calculate maximal subgroups of group of composition factor",
                     factorname[cfno];
    end if;
  end for;

  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  if not assigned G`LMGNode`radquot then
    GetRadquot(G: warning:=true);
  end if;
  return  MaxSubs(G);
end intrinsic;

intrinsic LMGLowIndexSubgroups(G :: GrpMat[FldFin], n :: RngIntElt :
              Presentation:=false, Print:=0, Max:=0 ) -> SeqEnum
{Conjugacy classes of subgroups of large matrix group G of index up to n}
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return LowIndexSubgroups(G, n : Presentation:=Presentation, Print:=Print);
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  if not assigned G`LMGNode`radquot then
    GetRadquot(G: warning:=true);
  end if;
  if Max cmpeq 0 then Max := n le 250; end if;
  lisubs := LISubs(G,n : Max:=Max, Presentation:=Presentation, Print:=Print);
  if Presentation then
     return [l`subgroup:l in lisubs], [l`presentation:l in lisubs];
  elif Max then return lisubs;
  else  return [l`subgroup:l in lisubs], _;
  end if;
end intrinsic;

intrinsic LMGNormaliser(G :: GrpMat[FldFin], H :: GrpMat[FldFin]) -> GrpMat
{Normaliser in large matrix group G of its subgroup H}
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return Normaliser(G,H);
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  if not assigned G`LMGNode`radquot then
    GetRadquot(G: warning:=true);
  end if;
  if not assigned H`LMGNode then
    Initialize(H : Verify := G`LMGNode`verified );
  end if;
  return  SubNorm(G, H);
end intrinsic;

intrinsic LMGNormalizer(G :: GrpMat[FldFin], H :: GrpMat[FldFin]) -> GrpMat
{Normalizer in large matrix group G of its subgroup H}
  return  LMGNormaliser(G, H);
end intrinsic;

intrinsic LMGIsConjugate(G :: GrpMat[FldFin], H :: GrpMat[FldFin],
                         K :: GrpMat[FldFin]) -> BoolElt, GrpMatElt
{Test subgroups H, K of large matrix group G for conjugacy}
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return IsConjugate(G,H,K);
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  if not assigned G`LMGNode`radquot then
    GetRadquot(G: warning:=true);
  end if;
  if assigned H`Order and assigned K`Order and H`Order ne K`Order then
    return false;
  end if;
  if not assigned H`LMGNode then
     Initialize(H : Verify := G`LMGNode`verified );
  end if;
  if not assigned K`LMGNode then
     Initialize(K : Verify := G`LMGNode`verified );
  end if;
  return  SubIsConj(G, H, K);
end intrinsic;

intrinsic LMGMeet(G :: GrpMat[FldFin], H :: GrpMat[FldFin],
                                       K :: GrpMat[FldFin]) -> GrpMat
{Intersection of subgroups H, K of large matrix group G}
  local lisubs;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return H meet K;
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  if not assigned G`LMGNode`radquot then
    GetRadquot(G: warning:=true);
  end if;
  if not assigned H`LMGNode then
     Initialize(H : Verify := G`LMGNode`verified );
  end if;
  if not assigned K`LMGNode then
     Initialize(K : Verify := G`LMGNode`verified );
  end if;
  return  MeetSubs(G, H, K);
end intrinsic;

intrinsic LMGNormalSubgroups(G :: GrpMat[FldFin] :
              Presentation:=false, Print:=0 ) -> SeqEnum
{Conjugacy classes of subgroups of large matrix group G of index up to n}
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  if G`LMGNode`RS then
    return NormalSubgroups(G : Presentation:=Presentation);
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  if not assigned G`LMGNode`radquot then
    GetRadquot(G: warning:=true);
  end if;
  return NormSubs(G : Presentation:=Presentation, Print:=Print);
end intrinsic;

intrinsic LMGCosetAction(G :: GrpMat[FldFin], H :: GrpMat[FldFin] : ker:=true )
                                                    -> Map, GrpPerm, GrpMat
{Coset action of matrix group G on cosets of subgroup H}
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  require LMGIsSubgroup(G, H): "Second argument is not a subgroup of first.";
  if G`LMGNode`RS then
    return CosetAction(G,H);
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  if not assigned G`LMGNode`radquot then
    GetRadquot(G: warning:=true);
  end if;
  return CosAct(G,H : ker:=ker);
end intrinsic;

intrinsic LMGCosetImage(G :: GrpMat[FldFin], H :: GrpMat[FldFin])
                                                    -> GrpPerm
{Coset image of matrix group G on cosets of subgroup H}
  return ci where _,ci,_ := LMGCosetAction(G,H : ker:=false );
end intrinsic;

intrinsic LMGCosetActionInverseImage(G, ca, i) -> GrpMatElt
{Given a coset action map for a group G and point i in coset image, return an
element of G whose image of 1 under ca(g) is i}
  local rt, imt, rm, imm, rind, imind;
  if not assigned(ca`TransInfo) then
    //presumbaly ca was defined using BSGS methods}
    return i @@ ca;
  end if;
  rt := ca`TransInfo`rtrans; imt := ca`TransInfo`imtrans;
  rm := G`LMGNode`radtoPC; imm := G`LMGNode`Gtoradquot;
  rind := i mod #rt eq 0 select #rt else (i mod #rt);
  imind := i mod #rt eq 0 select i div #rt else (i div #rt) + 1;
  return (rt[rind] @@ rm) * (imt[imind] @@ imm);
end intrinsic;

intrinsic LMGRightTransversal(G :: GrpMat[FldFin], H :: GrpMat[FldFin] :
                                                                  ca := 0)
                                                    -> SetIndx
{Right transversal of matrix group G on cosets of subgroup H. The coset action
may can be given as an optional parameter - otherwise it will be computed.}
  local rt, imt, rm, imm;
  if not assigned G`LMGNode then
    Initialize(G);
  end if;
  require LMGIsSubgroup(G, H): "Second argument is not a subgroup of first.";
  if G`LMGNode`RS then
    return RightTransversal(G,H);
  end if;
  if not assigned G`LMGNode`series then
    GetCompSer(G);
  end if;
  if not assigned G`LMGNode`cseries then
    GetChiefSer(G);
  end if;
  if not assigned G`LMGNode`radquot then
    GetRadquot(G: warning:=true);
  end if;
  if ca cmpeq 0 then ca := CosAct(G,H); end if;
  rt := ca`TransInfo`rtrans; imt := ca`TransInfo`imtrans;
  rm := G`LMGNode`radtoPC; imm := G`LMGNode`Gtoradquot;
  return [ (x @@ rm) * (y @@ imm) : x in rt, y in imt ];
end intrinsic;

intrinsic LMGIsPrimitive(G :: GrpMat[FldFin]) -> BoolElt
{Test matrix group G for imprimitivity}
  local flag, L;
  flag := ImprimitiveFlag (G);
  if Type(flag) cmpeq BoolElt then
      return not flag;
  end if;
  //try standard function first, because it is quicker when it works
  flag := IsPrimitive(G);
  if Type(flag) cmpeq BoolElt then
      SetImprimitiveFlag (G, not flag);
      return flag;
  end if;
  vprint LMG, 1: "Running LMGLowIndexSubgroups";
  L := LMGLowIndexSubgroups(G,Degree(G));
  vprint LMG, 1: #L, "subgroups of index up to degree", Degree(G);
  for H in L do
    if StabBlock(G,H) then return false; end if;
  end for;
  SetImprimitiveFlag (G, false);
  return true;
end intrinsic;

//remaining functions are by billu
intrinsic LMGRSTest(G :: GrpMat[FldFin]) -> BoolElt
{Internal use}
    return not assigned G`LMGNode or G`LMGNode`RS;
end intrinsic;

intrinsic SetGrpMatLMGNil()
{Turn off all internal use of LMG functions}
    SetGrpMatLMG(0);
end intrinsic;

intrinsic SetGrpMatLMGMedian()
{Turn on internal use of LMG functions for groups having a composition tree already}
    SetGrpMatLMG(1);
end intrinsic;

intrinsic SetGrpMatLMGFull()
{Turn on internal use of LMG functions}
    SetGrpMatLMG(2);
end intrinsic;
