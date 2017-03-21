freeze;

//////////////////////////////////////////////////////////
//                                                      //
//  Generators, index, and other functions from         //
//  Farey sequences.                                    // 
//                                                      //
//                                                      //
//////////////////////////////////////////////////////////

import "../GrpPSL2Shim/domain.m" : InternalShimuraFDH;

intrinsic FundamentalDomain(G::GrpPSL2,H::SpcHyp) -> SeqEnum
   {returns  a sequence of points in the upperhalf plane union
   cusps, such that the geodesics between these points form the
   boundary of a fundamental domain for G}
   // in future, if H could have a dimension different than
   // 1 this will need to be required to be 1.
   PSL := PSL2(Integers());

   if Type(BaseRing(G)) in {AlgQuat, AlgQuatOrd, AlgAssVOrd} then
      return InternalShimuraFDH(G,H);
   end if;

   if not (assigned G`FS_cusps and assigned G`FS_labels) then
      FS := FareySymbol(G);
   end if;
   cusps := G`FS_cusps;
   labels := G`FS_labels;
   polygon :=[];
   P := PSL2(Integers());
   for i:=1 to #cusps do
      Append(~polygon,H!cusps[i]);
      if i le #labels and labels[i] eq -3 then
	 x := Eltseq(cusps[i]);
	 y := Eltseq(cusps[i+1]);
	 M := P![y[1],x[1],y[2],x[2]];
	 Append(~polygon,M*H.2);
      end if;
   end for;
   return polygon;
end intrinsic;

intrinsic FundamentalDomain(G::GrpPSL2) -> SeqEnum
   {returns a sequence of points in the upper half plane union
   cusps, such that the geodesics between these points form the
   boundary of a fundamental domain for G}
   H := UpperHalfPlaneWithCusps();
   return FundamentalDomain(G,H);      
end intrinsic;
   
	
