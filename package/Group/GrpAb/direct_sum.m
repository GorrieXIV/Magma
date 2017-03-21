////////////////////////////////////////////////////////////////////
//                                                                //  
//                    Direct Sum of Abelian Groups                // 
//                           David Kohel                          // 
//                            May 2000                            //
//                                                                //  
////////////////////////////////////////////////////////////////////

freeze;

intrinsic DirectSum(S::[GrpAb]) -> GrpAb, SeqEnum, SeqEnum
   {The direct sum of the abelian groups in S followed by the 
   sequences of canonical inclusions and projections, respectively.}
   G := AbelianGroup([]);
   Ggens := [ ];
   projs := [ ];
   for k in [1..#S] do
      G, i1, i2, p1, p2 := DirectSum(G,S[k]);
      Ggens := [ [ i1(x) : x in Ggens[i] ] : i in [1..k-1] ];
      Append(~Ggens,[ i2(S[k].i) : i in [1..Ngens(S[k])] ]);
      projs := [ hom< G -> S[i] | x :-> projs[i](p1(x)) >
         : i in [1..k-1] ] cat [ p2 ];
   end for;
   f := func<x, k|&+[ Eltseq(x)[i]*Ggens[k][i] : i in [1..Ngens(S[k])]]>;
   return G, 
      [ hom< S[k] -> G | [f(S[k].i, k) : i in [1..Ngens(S[k])]]> :
          k in [1..#S] ], projs;
end intrinsic;

