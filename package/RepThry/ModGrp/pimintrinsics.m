freeze;

/* The intrinsics in this file concern KG-modules for finite fields K
 * For example projetive indecomposables can be computed.
 */

import "peakwords.m": ProjectiveIndecomposableB, ProjectiveIndecomposablesB,
 ComputeInfo, DecompositionMat, ProjectiveIndecomposableDims, ProjCover,
 CohDim, CohDims;
import "modext.m": ExtM, ModuleExtension, ExtendByIrreducible;
declare verbose KGModule, 2;

intrinsic ProjectiveIndecomposableDimensions(G :: Grp, K :: FldFin) -> SeqEnum
{Dimensions of projective indecomposable KG-modules. The order corresponds to
 the order of the corresponding irreducible KG-modules}
  require IsFinite(G): "Input group must be finite";
  return ProjectiveIndecomposableDims(G,K);
end intrinsic;

intrinsic ProjectiveIndecomposableModule(M :: ModGrp : limdim := 10000,
                                    condensation:=false ) -> ModGrp
{The projective indecomposable KG-module that projects onto the irreducible
 KG-module M, for finite field K}
  require Type(BaseRing(M)) eq FldFin and IsIrreducible(M) :
    "Module must be over a finite field and irreducible"; 
  return ProjectiveIndecomposableB(M : limdim:=limdim,
                                    condensation:=condensation );
end intrinsic;

intrinsic ProjectiveIndecomposable(M :: ModGrp : limdim := 10000,
                                    condensation:=false ) -> ModGrp
{The projective indecomposable KG-module that projects onto the irreducible
 KG-module M, for finite field K}
  require Type(BaseRing(M)) eq FldFin and IsIrreducible(M) :
    "Module must be over a finite field and irreducible"; 
  return ProjectiveIndecomposableB(M : limdim:=limdim,
                                    condensation:=condensation );
end intrinsic;

intrinsic ProjectiveIndecomposableModules(G :: Grp, K :: FldFin :
                   limdim := 10000, condensation:=false) -> SeqEnum
{The projective indecomposable KG-modules that projects onto the irreducible
 KG-modules M, for finite field K}
  require IsFinite(G): "Input group must be finite";
  return ProjectiveIndecomposablesB(G, K : limdim:=limdim,
                                                 condensation:=condensation );
end intrinsic;

intrinsic ProjectiveIndecomposables(G :: Grp, K :: FldFin : limdim := 10000,
                          condensation:=false) -> SeqEnum
{The projective indecomposable KG-modules that projects onto the irreducible
 KG-modules M, for finite field K}
  require IsFinite(G): "Input group must be finite";
  return ProjectiveIndecomposablesB(G, K : limdim:=limdim,
                                                 condensation:=condensation );
end intrinsic;

intrinsic ProjectiveCover(M :: ModGrp) -> ModGrp, ModMatGrpElt
{The projective cover of KG-module M, for finite field K}
  require Type(BaseRing(M)) eq FldFin : "Module must be over a finite field"; 
  return ProjCover(M);
end intrinsic;

intrinsic CohomologicalDimension(M :: ModGrp, k :: RngIntElt) -> RngIntElt 
{Dimension of H^k(G,M) for k>=0 and KG-module M, calculated using projective
 covers and dimension shifting for k>1}
  local G;
  G := Group(M);
  if k eq 1 and ISA(Type(G), GrpFP) then
    return CohomologicalDimension(CohomologyModule(G, M), 1);
  end if;
  require IsFinite(G): "Group of module must be finite";
  require Type(BaseRing(M)) eq FldFin : "Module must be over a finite field"; 
  return CohDim(M,k);
end intrinsic;

intrinsic CohomologicalDimensions(M :: ModGrp, k :: RngIntElt) -> SeqEnum
{List of dimensions of H^n(G,M) for 1 <= n <= k, where M is a KG-module,
 calculated using projective covers and dimension shifting for k>1}
  G := Group(M);
  require IsFinite(G): "Group of module must be finite";
  require Type(BaseRing(M)) eq FldFin : "Module must be over a finite field";
  return CohDims(M,k);
end intrinsic;

intrinsic CartanMatrix(G :: Grp, K :: FldFin) -> AlgMatElt
{Returns the matrix C such that C_ij is the number of times irreducible
 KG-module j occurs as constituents of projective indecomposable i}
  local entry;
  require IsFinite(G): "Input group must be finite";
  ComputeInfo(G,K);
  entry := [ t : t in G`modrepinfo | assigned t`field and t`field cmpeq K ][1];
  return entry`cartan;
end intrinsic;

intrinsic AbsoluteCartanMatrix(G :: Grp, K :: FldFin) -> AlgMatElt
{Returns the matrix C such that C_ij is the number of times absolutely
 irreducible K'G-module j (K <= K') occurs as constituent of absolutely
 irreducible projective indecomposable i. This is the standard Cartan
 matrix in characteristic p.}
  local entry;
  require IsFinite(G): "Input group must be finite";
  ComputeInfo(G,K);
  entry := [ t : t in G`modrepinfo | assigned t`field and t`field cmpeq K ][1];
  return entry`abscartan;
end intrinsic;

intrinsic DecompositionMatrix(G :: Grp, K :: FldFin) -> ModMatRngElt
{Returns the matrix D such that D_ij is the number of times absolutely
 irreducible K'G-module j (K <= K') occurs as constituent of mod-p restriction
 of ordinary character number i}
  require IsFinite(G): "Input group must be finite";
  return DecompositionMat(G,K);
end intrinsic;

intrinsic Ext(M :: ModGrp, N :: ModGrp) -> ModTupFld, Map
{Ext^1(M,N) for G-modules M,N}
  require BaseRing(M) cmpeq BaseRing(N) and Group(M) cmpeq Group(N):
  "Modules must be over the same ring and group";
  return ExtM(M,N);
end intrinsic;

intrinsic Extension(M :: ModGrp, N :: ModGrp, e :: ModTupFldElt, r :: Map) ->
          ModGrp
{Module extension corresponding to e in E where E,rho := Ext(M,N)}
  return ModuleExtension(M, N, e, r);
end intrinsic;

intrinsic Extension(M :: ModGrp, N :: ModGrp, e :: SeqEnum, r :: Map) ->
          ModGrp
{Module extension corresponding to e in E where E,rho := Ext(M,N)}
  e := Image(r)!e;
  return ModuleExtension(M, N, e, r);
end intrinsic;

intrinsic MaximalExtension(M :: ModGrp, N :: ModGrp, E :: ModTupFld, r :: Map)
    -> ModGrp
{Maximal non-split module extension of a direct sum of copies on irreducible
 module N by M, where E,rho := Ext(M,N)}
  return ExtendByIrreducible(M, N, E, r);
end intrinsic;
