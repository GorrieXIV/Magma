freeze;

import "../GrpPSL2Shim/mingens.m" : InternalShimuraGenerators;
import "../GrpPSL2Shim/definvs.m" : TotallyPositiveUnits;

////////////////////////////////////////////////////////////////////
//                                                                //
//                      Access Functions                          //
//                                                                //
////////////////////////////////////////////////////////////////////

declare attributes GrpPSL2Elt : MatrixH, MatrixD, MatrixDCenter;

intrinsic BaseRing(G::GrpPSL2) -> Rng
    {The base ring of G.}
    return G`BaseRing;
end intrinsic;

intrinsic Identity(G::GrpPSL2) -> GrpPSL2Elt
   {The identity element of G.}
   return G!1;
end intrinsic;

intrinsic Eltseq(A::GrpPSL2Elt) -> SeqEnum
    {Eltseq for the given element A in PSL_2(Z)}
    return Eltseq(A`Element);
end intrinsic;

intrinsic Parent(A::GrpPSL2Elt) -> GrpPSL2
   {}
   return A`Parent;
end intrinsic;

intrinsic Level(G::GrpPSL2) -> RngIntElt
   {The level of G.}
   if assigned G`ShimLevel then
      return G`ShimLevel;
   else
      return G`Level;
   end if;
end intrinsic;

intrinsic CongruenceIndices(G::GrpPSL2) -> RngIntElt
   {For G  a congruence subgroup, returns [[N,M,P]]
   where G consists of matrices [a,b,c,d] with
   c = 0 mod N, a, d = 1 mod M, b = 0 mod P}

  require not assigned G`EichlerOrder : "G must be a congruence subgroup";
  return G`gammaType_list;
end intrinsic;


intrinsic Genus(G::GrpPSL2) -> RngIntElt
   {The genus of the upper half plane quotiented by the congruence
   subgroup G}

   if assigned G`IsShimuraGroup then
     if assigned G`ShimGroup then
       return Integers()!((#Generators(G`ShimGroup)-#Relations(G`ShimGroup)+1)/2);
     end if;
     if EllipticInvariants(G) eq [] then
       g := 1 + ArithmeticVolume(G)/2;
     else
       g := 1 + ArithmeticVolume(G)/2 - 
         &+[s[2]*(1-1/s[1]) : s in EllipticInvariants(G)]/2;
     end if;
     assert IsIntegral(g);
     return Integers()!g;
   end if;

   Z:=Integers();

   require G`BaseRing eq Z: "Argument must be a subgroup of PSL_2(Z)";

   if IsGamma0(G) or IsGamma1(G) then
      return DimensionByFormula(CuspForms(G)); end if;

   if IsGamma(G) then N:=Level(G); if N le 2 then return 0; end if;
    return 1+Z!((N-6)*N^2/24*&*[(1-1/f[1]^2) : f in Factorization(N)]); end if;

   // note, when other groups are implemeneted, a more general
   // formular can be given than below.
   FS := FareySymbol(G);
   cusps := #Cusps(G);
   elliptic3 := #[i : i in Labels(FS) | i eq -3];
   elliptic2 := #[i : i in Labels(FS) | i eq -2];
   genus := 1 + (Index(G) - 6*cusps -4*elliptic3 - 3*elliptic2)/12;
   return Z!genus;
end intrinsic;


// the following is needed because it is not yet
// possible to use things like Set on sequences of
// objects of type GrpPSL2Elt.
intrinsic Matrix(g::GrpPSL2Elt : Precision := 0) -> GrpMatElt
    {returns an element of a matrix group corresponding to g}
   if assigned Parent(g)`IsShimuraGroup then
      if Precision eq 0 then
        if not assigned g`MatrixH then
          gmat := (Parent(g)`MatrixRepresentation)(g`Element);
          gmat /:= Sqrt(Determinant(gmat));
          g`MatrixH := gmat;
        end if;
        return g`MatrixH;
      else
        A := Algebra(BaseRing(Parent(g)));
        gmat := FuchsianMatrixRepresentation(A : Precision := Precision)(g`Element);
        gmat /:= Sqrt(Determinant(gmat));
        g`MatrixH := gmat;
        return g`MatrixH;
      end if;
   end if;
    return g`Element;
end intrinsic;


intrinsic Generators (G::GrpPSL2) -> SeqEnum
   {A sequence containing the generators for G}

   if assigned G`IsShimuraGroup then
      return InternalShimuraGenerators(G);
   end if;

   require G`BaseRing eq Integers():
   "currently only implemented for subgroups of PSL_2(Z)";
   if not assigned G`Generators then
      FS := FareySymbol(G);
      Gens := Generators(FS);
      G`Generators := [G!g : g in Gens];
      return Gens;
   else
      if Type(G`Generators[1]) ne GrpPSL2Elt then
	 G`Generators := [G| x : x in G`Generators];
      end if;
      return G`Generators;
   end if;
end intrinsic;
  

intrinsic Index(G::GrpPSL2) -> RngIntElt
    {The index of G in PSL_2(Z), if this is finite}
	// should improve on this to return a fractional index
	// when G and SL_2(Z) are comensurable
        // Also TO DO: Work it out using formulas for most cases...

    require G`BaseRing eq Integers(): "Argument must be a subgroup of SL_2(Z)";

 if Level(G) eq 1 then return 1; end if;
 if IsGamma(G) then return Level(G)*Index(Gamma1(Level(G))); end if; // MW

    if IsGamma0(G) or IsGamma1(G) then 
       N := Level(G);
       ind := N * &*[Rationals()| 1+1/p : p in PrimeDivisors(N) ];
       if IsGamma1(G) then 
          ind *:= EulerPhi(N);
          if N notin {1,2} then ind /:= 2; end if;
       end if;
       assert IsIntegral(ind);
       return Integers()! ind;
    end if;

    if not assigned G`FS_cosets then
	FS := FareySymbol(G);	
    end if;
    return #G`FS_cosets;
end intrinsic;


intrinsic CosetRepresentatives(G::GrpPSL2) -> SeqEnum
    {returns a list of coset representatives of G in PSL2(Z);
    only defined for G a subgroup of PSL2(Z)}

    require G`BaseRing eq Integers(): "Argument must be a subgroup of SL_2(Z)";

    if not assigned G`FS_cosets then
	FS := FareySymbol(G);	
     end if;
     if Type(G`FS_cosets[1]) ne GrpPSL2Elt then
	P := PSL2(Integers());
	G`FS_cosets := [P| x : x in G`FS_cosets];
     end if;
    return G`FS_cosets;
end intrinsic;
