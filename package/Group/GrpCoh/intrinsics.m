freeze;

import "compab.m": ZeroCohomologyGroupA, FirstCohomologyGroupA,
        ReduceAbAutVec, MatrixOfGroupElement;
import "strongpres.m": MakeModuleRecordSG, ZeroCohomologyGroupG,
        FirstCohomologyGroupG, SecondCohomologyGroupSG,
        ZeroCocycleG, IdentifyZeroCocycleG, OneCocycleSG,
        IdentifyOneCocycleSG, IsOneCoboundarySG,
        TwoCocycleSG, IdentifyTwoCocycleSG, IsTwoCoboundarySG,
        ExtensionOfModuleSG, SplitExtensionSG, DistinctExtensionsSG,
        SGWordH, ExtensionOfModuleQmodZ, FirstCohomologyGroupQmodZ,
        OneCocycleQmodZ, CorrespondingTwoCocycle, IdentifyTwoCocycleQmodZ;
import "pcpresgen.m": MakeModuleRecordPCPG, SecondCohomologyGroupPCPG,
        OneCocyclePCPG, IdentifyOneCocyclePCPG, IsOneCoboundaryPCPG,
        TwoCocyclePCPG, IdentifyTwoCocyclePCPG, IsTwoCoboundaryPCPG,
        ExtensionOfModulePCPG,
        SplitExtensionPCPG, DistinctExtensionsPCPG;
import "strongpresab.m": MakeModuleRecordSGA, SecondCohomologyGroupSGA,
        OneCocycleSGA, IdentifyOneCocycleSGA, IsOneCoboundarySGA,
        TwoCocycleSGA, IdentifyTwoCocycleSGA, IsTwoCoboundarySGA,
        ExtensionOfModuleSGA, SplitExtensionSGA, DistinctExtensionsSGA; 
import "pcpresgenab.m": MakeModuleRecordPCPGA, SecondCohomologyGroupPCPGA,
        OneCocyclePCPGA, IdentifyOneCocyclePCPGA, IsOneCoboundaryPCPGA,
        TwoCocyclePCPGA, IdentifyTwoCocyclePCPGA, IsTwoCoboundaryPCPGA,
        ExtensionOfModulePCPGA,
        SplitExtensionPCPGA, DistinctExtensionsPCPGA, PCElToSeq;
import "matgp.m": MakeModuleRecordMG, MakeModuleRecordMGA;
import "fp.m": MakeModuleRecordFPG, MakeModuleRecordFPGA,
        OneCocycleFPG, IdentifyOneCocycleFPG, IsOneCoboundaryFPG,
        OneCocycleFPGA, IdentifyOneCocycleFPGA, IsOneCoboundaryFPGA,
               SplitExtensionFPG, SplitExtensionFPGA;
import "pcpres.m": SecondCohomologyDimensionRes2;

intrinsic CohomologyModule(G :: GrpPerm, M :: ModGrp) -> ModCoho
{Create a cohomology module for permutation group G acting on module M}
  if not Group(M) cmpeq G then
    error "Module is over the wrong group";
  end if;
  return MakeModuleRecordSG(G,M);
end intrinsic;

intrinsic CohomologyModule(G :: GrpPerm, invar :: SeqEnum, mats :: SeqEnum)
                                                                  -> ModCoho
{Create a cohomology module for permutation group G acting on abelian group}
  require forall { i: i in [2..#invar] | invar[i-1] eq 0 or invar[i] mod invar[i-1] eq 0 }:
            "invar must be the invariants sequence of an abelian group";
  return MakeModuleRecordSGA(G,invar,mats);
end intrinsic;

intrinsic CohomologyModule(G :: GrpMat, M :: ModGrp) -> ModCoho
{Create a cohomology module for matrix group G acting on module M}
  if IsFinite(G) and #G eq 1 then
    error "Sorry, cannot currently handle trivial matrix groups!";
  end if;
  if not Group(M) cmpeq G then
    error "Module is over the wrong group";
  end if;
  return MakeModuleRecordMG(G,M);
end intrinsic;

intrinsic CohomologyModule(G :: GrpMat, invar :: SeqEnum, mats :: SeqEnum)
                                                                  -> ModCoho
{Create a cohomology module for matrix group G acting on abelian group}
  require forall { i: i in [2..#invar] | invar[i-1] eq 0 or invar[i] mod invar[i-1] eq 0 }:
            "invar must be the invariants sequence of an abelian group";
  if #G eq 1 then
    error "Sorry, cannot currently handle trivial matrix groups!";
  end if;
  return MakeModuleRecordMGA(G,invar,mats);
end intrinsic;

intrinsic CohomologyModule(G :: GrpPC, M :: ModGrp) -> ModCoho
{Create a cohomology module for PC-group G acting on module M}
  if not Group(M) cmpeq G then
    error "Module is over the wrong group";
  end if;
  if not IsConditioned(G) then
    error "Use CohomologyModule only on conditioned PC-presentations";
  end if;
  return MakeModuleRecordPCPG(G,M);
end intrinsic;

intrinsic CohomologyModule(G :: GrpPC, invar :: SeqEnum, mats :: SeqEnum)
                                                                  -> ModCoho
{Create a cohomology module for PC-group G acting on abelian group}
  require forall { i: i in [2..#invar] | invar[i-1] eq 0 or invar[i] mod invar[i-1] eq 0 }:
            "invar must be the invariants sequence of an abelian group";
  if not IsConditioned(G) then
    error "Use CohomologyModule only on conditioned PC-presentations";
  end if;
  return MakeModuleRecordPCPGA(G,invar,mats);
end intrinsic;

intrinsic CohomologyModule(G :: GrpFP, M :: ModGrp) -> ModCoho
{Create a cohomology module for PC-group G acting on module M}
  if not Group(M) cmpeq G then
    error "Module is over the wrong group";
  end if;
  return MakeModuleRecordFPG(G,M);
end intrinsic;

intrinsic CohomologyModule(G :: GrpFP, invar :: SeqEnum, mats :: SeqEnum)
                                                                  -> ModCoho
{Create a cohomology module for PC-group G acting on abelian group}
  require forall { i: i in [2..#invar] | invar[i-1] eq 0 or invar[i] mod invar[i-1] eq 0 }:
            "invar must be the invariants sequence of an abelian group";
  return MakeModuleRecordFPGA(G,invar,mats);
end intrinsic;

intrinsic Dimension(CM :: ModCoho)  -> RngIntElt
{ Dimension of module used to define CM }
  return CM`dim;
end intrinsic;

intrinsic Group(CM :: ModCoho)  -> Grp
{ The group used to define CM }
  if CM`gptype eq GrpPerm or CM`gptype eq GrpMat then
     return CM`gr`gp;
  elif CM`gptype eq GrpFP then
     return CM`gf;
  else return CM`gpc;
  end if; 
end intrinsic;

intrinsic FPGroup(CM :: ModCoho)  -> Grp, HomGrp
{ The finitely presented group F isomorphic to the group G used to define CM,
  and the isomorphism from F to G }
  return CM`gf, CM`gftoG;
end intrinsic;

intrinsic Module(CM :: ModCoho)  -> ModGrp
{ The module (if any) used to define CM }
  if CM`modtype eq GrpAb then
    error "Cohomology module was defined by an action on an abelian group";
  end if;
  return CM`module;
end intrinsic;

intrinsic Invariants(CM :: ModCoho)  -> SeqEnum
{ The invariants of the abelian group (if any) used to define CM }
  if CM`modtype eq ModGrp then
    error "Cohomology module was defined by a module";
  end if;
  return CM`invar;
end intrinsic;

intrinsic Ring(CM :: ModCoho)  -> ModGrp
{ The ring over which the group action is defined }
  return CM`ring;
end intrinsic;

intrinsic CohomologyGroup(CM :: ModCoho, n :: RngIntElt : algorithm:="QmodZ")
                                                                  -> ModTupRng
{ H^n(G,M) as module over base ring of M, for n = 0, 1 or 2}
   if n lt 0 or n gt 3 or (n eq 3 and CM`ring cmpne Integers() ) then
     error
  "H^n(G,M) can only be computed for n=0,1,2, or for n=3 for modules over Z";
   end if;
   if n eq 0 and CM`modtype eq ModGrp then
     ZeroCohomologyGroupG(CM);
     return CM`H0;
   elif n eq 0 and CM`modtype eq GrpAb then
     ZeroCohomologyGroupA(CM);
     return CM`H0;
   elif n eq 1 and CM`modtype eq ModGrp then
     FirstCohomologyGroupG(CM);
     return CM`H1;
   elif n eq 1 and CM`modtype eq GrpAb then
     FirstCohomologyGroupA(CM);
     return CM`H1;
   elif n eq 2 and CM`modtype eq ModGrp and
            (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     if CM`ring cmpeq Integers() and algorithm eq "QmodZ" then
      //quicker to compute as H^1(G,M_QModZ)
       FirstCohomologyGroupQmodZ(CM);      
       return CM`QmodZH1;
     end if;
     SecondCohomologyGroupSG(CM);
     return CM`H2;
   elif n eq 2 and CM`modtype eq ModGrp and CM`gptype eq GrpPC then
     SecondCohomologyGroupPCPG(CM);
     return CM`H2;
   elif n eq 2 and CM`modtype eq GrpAb and
            (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     SecondCohomologyGroupSGA(CM);
     return CM`H2;
   elif n eq 2 and CM`modtype eq GrpAb and CM`gptype eq GrpPC then
     SecondCohomologyGroupPCPGA(CM);
     return CM`H2;
   elif n eq 2 and CM`gptype eq GrpFP then
     error "Second cohomology groups are not implemented for GrpFP";
   elif n eq 3 then
     SecondCohomologyGroupSG(CM: QmodZ:=true);
     return CM`QmodZH2;
   end if;
end intrinsic;

intrinsic CohomologicalDimension(CM :: ModCoho, n :: RngIntElt) -> RngIntElt
{Dimension of cohomology group - quicker method used for H^2(G,M) with
 G a permutation group and M module over prime field}
  local p;
  if n lt 0 or n gt 2 then
    error "CohomologicalDimension can only be computed for n=0,1,2";
  end if;
  if not IsField(CM`ring) then
    error
     "CohomologicalDimension can only be computed for modules over a field";
  end if;
  if CM`modtype eq GrpAb then
     error "Cohomological dimension undefined for action on abelian group";
  end if;
  if n eq 0 then return Dimension(CohomologyGroup(CM,0)); end if;
  if n eq 1 then return Dimension(CohomologyGroup(CM,1)); end if;
  if n eq 2 and (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) and
                  IsFinite(CM`ring) and IsPrime(#CM`ring) then
    p := #CM`ring;
    G := CM`gr`gp;
    if #G mod p ne 0 then return 0; end if;
    return SecondCohomologyDimensionRes2(G,CM`module);
  end if; 
  return Dimension(CohomologyGroup(CM,2));
end intrinsic;

intrinsic ZeroCocycle(CM :: ModCoho, s :: SeqEnum) -> UserProgram
{ Maps element of H^0(G,M) to corresponding fixed point of module }
   if not assigned CM`H0 then
     error "You must run CohomologyGroup(CM,0) before ZeroCocycle"; 
   end if;
   return ZeroCocycleG(CM,s);
end intrinsic;

intrinsic ZeroCocycle(CM :: ModCoho, s :: ModTupRngElt) -> UserProgram
{ Maps element of H^0(G,M) to corresponding fixed point of module }
   if not assigned CM`H0 then
     error "You must run CohomologyGroup(CM,0) before ZeroCocycle"; 
   end if;
   return ZeroCocycleG(CM,s);
end intrinsic;

intrinsic IdentifyZeroCocycle(CM :: ModCoho, s :: UserProgram) -> ModTupRngElt
{ Maps fixed point of module to corresponding element of H^0(G,M) }
   if not assigned CM`H0 then
     error "You must run CohomologyGroup(CM,0) before IdentifyZeroCocycle"; 
   end if;
   return IdentifyZeroCocycleG(CM,s);
end intrinsic;

intrinsic OneCocycle(CM :: ModCoho, s :: SeqEnum) -> UserProgram
{ Maps element of H^1(G,M) to corresponding one-cocyle}
   if not assigned CM`H1 then
     error "You must run CohomologyGroup(CM,1) before OneCocycle"; 
   end if;
   if CM`modtype eq ModGrp and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return OneCocycleSG(CM,s);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpPC then
     return OneCocyclePCPG(CM,s);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpFP then
     return OneCocycleFPG(CM,s);
   elif CM`modtype eq GrpAb and
            (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return OneCocycleSGA(CM,s);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpFP then
     return OneCocycleFPGA(CM,s);
   end if;
end intrinsic;

intrinsic OneCocycle(CM :: ModCoho, s :: ModTupRngElt) -> UserProgram
{ Maps element of H^1(G,M) to corresponding one-cocyle}
   if not assigned CM`H1 then
     error "You must run CohomologyGroup(CM,1) before OneCocycle"; 
   end if;
   if CM`modtype eq ModGrp and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return OneCocycleSG(CM,s);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpPC then
     return OneCocyclePCPG(CM,s);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpFP then
     return OneCocycleFPG(CM,s);
   elif CM`modtype eq GrpAb and
            (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return OneCocycleSGA(CM,s);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpPC then
     return OneCocyclePCPGA(CM,s);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpFP then
     return OneCocycleFPGA(CM,s);
   end if;
end intrinsic;

intrinsic IdentifyOneCocycle(CM :: ModCoho, OC :: UserProgram) -> ModTupRngElt
{ Maps one-cocycle to corresponding element of H^1(G,M) }
   if not assigned CM`H1 then
     error "You must run CohomologyGroup(CM,1) before IdentifyOneCocycle"; 
   end if;
   if CM`modtype eq ModGrp and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return IdentifyOneCocycleSG(CM,OC);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpPC then
     return IdentifyOneCocyclePCPG(CM,OC);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpFP then
     return IdentifyOneCocycleFPG(CM,OC);
   elif CM`modtype eq GrpAb and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return IdentifyOneCocycleSGA(CM,OC);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpPC then
     return IdentifyOneCocyclePCPGA(CM,OC);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpFP then
     return IdentifyOneCocycleFPGA(CM,OC);
   else
  error "IdentifyOneCocycle not yet implemented for this cohomology module";
   end if;
end intrinsic;

intrinsic IsOneCoboundary(CM :: ModCoho, OC :: UserProgram) ->
                                                 BoolElt, UserProgram
{If OC is 1-coboundary then also return  0-cochain z such that
  OC(<g>) = z(<>)^(1-g) for g in G }
   if not assigned CM`csm then
     error "You must run CohomologyGroup(CM,0) before IsOneCoboundary"; 
   end if;
   if CM`modtype eq ModGrp and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return  IsOneCoboundarySG(CM,OC);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpPC then
     return  IsOneCoboundaryPCPG(CM,OC); 
   elif CM`modtype eq ModGrp and CM`gptype eq GrpFP then
     return  IsOneCoboundaryFPG(CM,OC); 
   elif CM`modtype eq GrpAb and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return IsOneCoboundarySGA(CM,OC); 
   elif CM`modtype eq GrpAb and CM`gptype eq GrpPC then
     return IsOneCoboundaryPCPGA(CM,OC);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpFP then
     return  IsOneCoboundaryFPGA(CM,OC); 
   else
  error "IsOneCoboundary not yet implemented for this cohomology module";
   end if;
end intrinsic;

intrinsic TwoCocycle(CM :: ModCoho, s :: SeqEnum) -> UserProgram
{ Maps element of H^2(G,M) to corresponding two-cocyle}
   if not assigned CM`H2 and not assigned CM`QmodZinvar then
     error "You must run CohomologyGroup(CM,2) before TwoCocycle"; 
   end if;
   if CM`modtype eq ModGrp and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     if CM`ring cmpeq Integers() and assigned CM`QmodZinvar then
       return CorrespondingTwoCocycle( CM, OneCocycleQmodZ(CM, s) );
     end if;
     return TwoCocycleSG(CM,s);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpPC then
     return TwoCocyclePCPG(CM,s);
   elif CM`modtype eq GrpAb and
            (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return TwoCocycleSGA(CM,s);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpPC then
     return TwoCocyclePCPGA(CM,s);
   end if;
end intrinsic;

intrinsic TwoCocycle(CM :: ModCoho, s :: ModTupRngElt) -> UserProgram
{ Maps element of H^2(G,M) to corresponding two-cocyle}
   if not assigned CM`H2 then
     error "You must run CohomologyGroup(CM,2) before TwoCocycle"; 
   end if;
   if CM`modtype eq ModGrp and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return TwoCocycleSG(CM,s);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpPC then
     return TwoCocyclePCPG(CM,s);
   elif CM`modtype eq GrpAb and
            (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return TwoCocycleSGA(CM,s);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpPC then
     return TwoCocyclePCPGA(CM,s);
   end if;
end intrinsic;

intrinsic IdentifyTwoCocycle(CM :: ModCoho, TC :: UserProgram) -> ModTupRngElt
{ Maps two-cocycle to corresponding element of H^2(G,M) }
   if not assigned CM`H2 and not assigned CM`QmodZinvar then
     error "You must run CohomologyGroup(CM,2) before IdentifyTwoCocycle"; 
   end if;
   if CM`modtype eq ModGrp and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     if CM`ring cmpeq Integers() and assigned CM`QmodZinvar then
       return IdentifyTwoCocycleQmodZ(CM, TC);
     end if;
     return IdentifyTwoCocycleSG(CM,TC);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpPC then
     return IdentifyTwoCocyclePCPG(CM,TC);
   elif CM`modtype eq GrpAb and
            (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return IdentifyTwoCocycleSGA(CM,TC);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpPC then
     return IdentifyTwoCocyclePCPGA(CM,TC);
   end if;
end intrinsic;

intrinsic IsTwoCoboundary(CM :: ModCoho, TC :: UserProgram) ->
                                                 BoolElt, UserProgram
{If TC is 2-coboundary then also return associated 1-cochain OC}
   if not assigned CM`cem then
     error "You must run CohomologyGroup(CM,1) before IsTwoCoboundary"; 
   end if;
   if CM`modtype eq ModGrp and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return  IsTwoCoboundarySG(CM,TC);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpPC then
     return  IsTwoCoboundaryPCPG(CM,TC); 
   elif CM`modtype eq GrpAb and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return IsTwoCoboundarySGA(CM,TC); 
   elif CM`modtype eq GrpAb and CM`gptype eq GrpPC then
     return IsTwoCoboundaryPCPGA(CM,TC);
   else
  error "IsTwoCoboundary not yet implemented for this cohomology module";
   end if;
end intrinsic;

intrinsic MatrixOfElement(CM :: ModCoho, g :: GrpElt ) -> AlgMatElt
{Matrix of module representing group element g} 
  local w;
  if CM`modtype ne GrpAb then
    R := Representation(CM`module);
    return R(g) where R := Representation(CM`module);
  end if;
  if CM`gptype eq GrpPerm  or CM`gptype eq GrpMat then
    w := SGWordH(CM`gr, g);
  elif CM`gptype eq GrpFP then
    w := Eltseq(g);
  else w := PCElToSeq(g);
  end if;
  return MatrixOfGroupElement(w, CM`invar, CM`mats, CM`imats);
end intrinsic;

intrinsic ActionOnVector(CM :: ModCoho, vec :: ModTupRngElt, g :: GrpElt ) -> 
          ModTupRngElt
{Action of matrix of group element on vector in module}
  local vecim;
  vecim := vec * MatrixOfElement(CM, g);
  if CM`modtype ne GrpAb then
    return vecim;
  end if;
  return ReduceAbAutVec(CM`invar, vec * MatrixOfElement(CM, g) );
end intrinsic;

intrinsic Extension(CM::ModCoho, s::SeqEnum) -> Grp, HomGrp, Map
{Presentation of extension of module by group defined by s}
   local Z, K, finite;
   if not assigned CM`H2 and not assigned CM`QmodZinvar then
     error "You must run CohomologyGroup(CM,2) before Extension";
   end if;
   Z := Integers();
   K := CM`ring;
   finite := IsFinite(K);
   if (not finite and not K cmpeq Z and CM`modtype ne GrpAb) then
    error
    "Sorry, can only construct extensions over integer rings or prime fields";
   end if;
   if CM`modtype eq ModGrp and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     if CM`ring cmpeq Z and assigned CM`QmodZinvar then
       return ExtensionOfModuleQmodZ(CM, s);
     end if;
     return ExtensionOfModuleSG(CM,s);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpPC then
     return ExtensionOfModulePCPG(CM,s);
   elif CM`modtype eq GrpAb and
            (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return ExtensionOfModuleSGA(CM,s);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpPC then
     return ExtensionOfModulePCPGA(CM,s);
   end if;
end intrinsic;

intrinsic Extension(CM::ModCoho, s::ModTupRngElt) -> Grp, HomGrp, Map
{Presentation of extension of module by group defined by s}
   local Z, K, finite;
   if not assigned CM`H2 then
     error "You must run CohomologyGroup(CM,2) before Extension";
   end if;
   Z := Integers();
   K := CM`ring;
   finite := IsFinite(K);
   if (not finite and not K cmpeq Z and CM`modtype ne GrpAb) then
    error
    "Sorry, can only construct extensions over the integers or prime fields";
   end if;
   if CM`modtype eq ModGrp and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return ExtensionOfModuleSG(CM,s);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpPC then
     return ExtensionOfModulePCPG(CM,s);
   elif CM`modtype eq GrpAb and
            (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return ExtensionOfModuleSGA(CM,s);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpPC then
     return ExtensionOfModulePCPGA(CM,s);
   end if;
end intrinsic;

intrinsic SplitExtension(CM::ModCoho) -> Grp, HomGrp, Map
{Presentation of split extension of module by group}
   local se;
   Z := Integers();
   K := CM`ring;
   finite := IsFinite(K);
   if (not finite and not K cmpeq Z) then
    error
 "Sorry, can only construct extensions over the integer rings or prime fields";
   end if;
   if CM`modtype eq ModGrp and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     SplitExtensionSG(CM);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpPC then
     SplitExtensionPCPG(CM);
   elif CM`modtype eq ModGrp and CM`gptype eq GrpFP then
     SplitExtensionFPG(CM);
   elif CM`modtype eq GrpAb and
            (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     SplitExtensionSGA(CM);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpPC then
     SplitExtensionPCPGA(CM);
   elif CM`modtype eq GrpAb and CM`gptype eq GrpFP then
     SplitExtensionFPGA(CM);
   end if;
   se := CM`SplitExtension;
   return se, se`Projection, se`Injection;
end intrinsic;

intrinsic DistinctExtensions(CM::ModCoho) -> SeqEnum
{Distinct extensions, up to isomorphisms fixing module, of module by group}
   local K, finite;
   K := CM`ring;
   finite := IsFinite(K);
   if CM`modtype eq ModGrp and (not finite or not IsPrime(#K)) then
    error
      "Sorry, can only compute distinct extensions over prime field or finite abelian group";
   end if;
   if CM`modtype eq GrpAb and CM`invar[CM`dim] eq 0 then
    error
      "Sorry, can only compute distinct extensions over prime field or finite abelian group";
   end if;
   if CM`modtype eq ModGrp and  CM`gptype eq GrpPC then
     return DistinctExtensionsPCPG(CM);
   elif CM`modtype eq GrpAb and  CM`gptype eq GrpPC then
     return DistinctExtensionsPCPGA(CM);
   elif CM`modtype eq ModGrp and
       (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return DistinctExtensionsSG(CM);
   elif CM`modtype eq GrpAb and
            (CM`gptype eq GrpPerm or CM`gptype eq GrpMat) then
     return DistinctExtensionsSGA(CM);
   end if;
end intrinsic;

intrinsic Restriction(CM :: ModCoho, H :: Grp) -> ModCoho
{Restriction of cohomology module CM to subgroup H of Group(CM)}
  local G, mats, CMH, Res1, Res2;
  require H subset Group(CM):
  "second argument must be a subgroup of the underlying group of the first";
  G := Group(CM);
  if CM`modtype eq GrpAb then
    mats := [ MatrixOfElement(CM, H.i) : i in [1..Ngens(H)] ];
    CMH := CohomologyModule(H, CM`invar, mats);
  else
    CMH := CohomologyModule(H, Restriction (CM`module, H) );
  end if;
  return CMH;
end intrinsic;
