freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//         WEIL PAIRING AND INDEPENDENCE OF TORSION POINTS        //
//                         David Kohel                            //
//                      Created May 2000                          //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic pSubgroup(E::CrvEll,p::RngIntElt) -> GrpAb, Map
   {The Sylow p-subgroup of the group of rational points 
   on E over a finite field, followed by the map to E.}
   G, m := TorsionSubgroup(E);
   H := SylowSubgroup(G,p);
   pgens := [ m(H.i) : i in [1..Ngens(H)] ];
   Gp := AbelianGroup([ Order(H.i) : i in [1..Ngens(H)] ]);
   mp := map< Gp -> E | g :-> &+[ E | c[i]*pgens[i]
       where c is Eltseq(g) : i in [1..Ngens(Gp)] ] >;
   return Gp, mp;
end intrinsic;

intrinsic TwoTorsionSubgroup(E::SchGrpEll) -> GrpAb, Map
    {The rational 2-torsion subgroup of E.}
    pts := DivisionPoints(E!0, 2);
    pts := [p : p in pts| p ne E!0];
    require #pts in {0,1,3}:
      "Impossible number of two-torsion points found: ", pts;
    if #pts eq 3 then
      pts:=pts[1..2];
    end if;
    G := AbelianGroup([2 : k in [1..#pts]]);
    return G, hom< G -> E | x :-> &+[ E | Eltseq(x)[k]*pts[k] : k in [1..#pts] ]>;
end intrinsic;

intrinsic IsLinearlyIndependent(P::PtEll,Q::PtEll,
   n::RngIntElt) -> BoolElt
   {True if and only if P and Q form a basis of the $n$-torsion 
   subgroup of E.}
   require Parent(P) eq Parent(Q) : "Argument 1 and 2 have different parents";
   require IsId(n*P) and IsId(n*Q) :
      "Arguments 1 and 2 must be torsion points killed by argument 3"; 
   u := WeilPairing(P,Q,n);
   for p in PrimeDivisors(n) do
      if u^(n div p) eq 1 then
         return false;
      end if;
   end for;
   return true;
end intrinsic;   

intrinsic IsLinearlyIndependent(S::[PtEll],n::RngIntElt) -> BoolElt
   {True if and only if S is a sequence of n-torsion points linearly
   independent over Z/nZ.}
   if #S gt 2 then
      return false;
   end if;
   require &and[ IsId(n*P) : P in S ] : 
      "Argument 1 must be a sequence of torsion points killed by argument 2"; 
   if #S eq 1 then
      return IsOrder(S[1],n);
   else
      u := WeilPairing(S[1],S[2],n);
      for p in PrimeDivisors(n) do
         if u^(n div p) eq 1 then
            return false;
         end if;
      end for;
      return true;
   end if;
end intrinsic;   

