freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: arithabvar.m
   DESC: Basic ModAbVar functionality.
      
 ***************************************************************************/

/***************************************************************************
HANDBOOK_TITLE: Artihmetic of Abelian Varieties

BEGIN_HANDBOOK_INTRO

END_HANDBOOK_INTRO

****************************************************************************/
import "homology.m": 
   Create_ModAbVarHomol,
   Create_ModAbVarHomol_Quotient,
   Create_ModAbVarHomol_Subspace;

import "linalg.m":
   HorizontallyStackMatrices,
   LatticeDirectSum,
   VerticallyStackMatrices;

import "modabvar.m": 
   Create_ModAbVar,
   Name,
   Verbose;

import "morphisms.m": 
   Copy_MapModAbVar,
   Create_MapModAbVar;

import "rings.m": 
   QQ,
   CommonBaseRing,
   CommonFieldOfDefinition,
   OverRing;

forward 
   ComputeIntersectionOfImages,
   GiveCommonCodomain;

/***************************************************************************

  << Direct Sum >>

 ***************************************************************************/

intrinsic '*'(A::ModAbVar, B::ModAbVar) -> ModAbVar, List, List
{The direct sum of A and B.}
   return DirectSum(A,B);
end intrinsic;


function BinaryPowerAlgorithm(x,n)
/* Generic powering algorithm, which uses writing n in binary, and repeated squaring. */
   assert Type(n) eq RngIntElt;
   if n eq 0 then
      return x^0;
   end if;
   assert n ge 1;

   y := x;
   z := x^0;
   while n gt 0 do
      if (n mod 2) eq 1 then
         if z eq x^0 then
            z := y;
         else
            z := z*y;
         end if;
      end if;
      y := y*y;
      n := n div 2;
   end while;
   return z;
end function;

intrinsic '^'(A::ModAbVar, n::RngIntElt) -> ModAbVar
{The direct sum of n copies of A.  If n=0, the zero subvariety
of A.  If n is negative, the (-n)-th power of the dual of A.}
   Verbose("^", Sprintf("Computing direct sum of %o copies of A=%o.", n,A),"");
   if n eq 0 then
      return ZeroSubvariety(A);
   end if;
   if n lt 0 then
      return Dual(A)^(-n);
   end if;
   return BinaryPowerAlgorithm(A,n);
end intrinsic;


intrinsic DirectProduct(A::ModAbVar, B::ModAbVar) -> ModAbVar, List, List
{Same as DirectSum.}
   require Sign(A) eq Sign(B) : "Arguments 1 and 2 must have the same sign.";
   return DirectSum(A,B);
end intrinsic;

intrinsic DirectProduct(X::[ModAbVar]) -> ModAbVar, List, List
{Same as DirectSum.}
   require #Set([Sign(A) : A in X]) eq 1 : 
        "The signs of the summands must all be the same.";
   return DirectSum(X);
end intrinsic;

intrinsic DirectSum(X::[ModAbVar]) -> ModAbVar, List, List
{The direct sum D of the sequence X of modular abelian varieties, 
together with a list containing the embedding maps, and  
a list containing the projection maps.}
   Verbose("DirectSum",Sprintf("Creating direct sum of %o\n", X),"");
   //X := [A : A in X | Dimension(A) gt 0];
   if #X eq 0 then
      Z := ZeroModularAbelianVariety();
      return Z, [], [];
   end if;
   if #X eq 1 then
      return X[1], [IdentityMap(X[1])], [IdentityMap(X[1])];
   end if;

   require #Set([Sign(A) : A in X]) eq 1 : 
        "The signs of the summands must all be the same.";

   K := CommonFieldOfDefinition(X);
   require Type(K) ne BoolElt : 
      "The direct summands must have compatible fields of definition.";

   R := CommonBaseRing(X);
   require Type(R) ne BoolElt : 
      "The direct summands must have compatible base rings.";

   name := "";
   for i in [1..#X] do 
      if Name(X[i]) eq "" then
         name := "";
         break;
      end if;
      name *:= Name(BaseExtend(X[i],R)) * (i lt #X select " x " else "");
   end for;

   D_vs, embed_vs, proj_vs := DirectSum([RationalHomology(A) : A in X]);

   if &and[IsAttachedToModularSymbols(A) : A in X] then
      modsym := &cat[ModularSymbols(A) : A in X];
      H := Create_ModAbVarHomol(modsym);
      D := Create_ModAbVar(name, H, K, R, true);
   else
      N := 1;
      scalar := [];
      for A in X do
         t,n := IsInteger(ModularEmbedding(A)*ModularParameterization(A));
         assert t;
         N := LCM(N,n);
         Append(~scalar,n);
      end for;

      L := IntegralHomology(X[1]);
      for i in [2..#X] do 
         L := LatticeDirectSum(L, IntegralHomology(X[i]));
      end for;
      H := Create_ModAbVarHomol(L);
      H`sign := Sign(X[1]);
      Je, embed_e, param_p := DirectSum([Domain(ModularParameterization(A)) : A in X]);
      embed_matrix := [* *];
      param_matrix := [* *];
      for i in [1..#X] do 
         Append(~embed_matrix, (N div scalar[i])*Matrix(ModularEmbedding(X[i]))*Matrix(embed_e[i]));
         Append(~param_matrix, Matrix(param_p[i])*Matrix(ModularParameterization(X[i])));
      end for;
      embed_matrix := VerticallyStackMatrices(embed_matrix);
      param_matrix := HorizontallyStackMatrices(param_matrix);
      D := Create_ModAbVar(name, H, K, R, <Je, embed_matrix, param_matrix>);
   end if;
   // Create embedding and projection morphisms
   n := Dimension(RationalHomology(D));
   embed := [* *];
   proj := [* *];
   for i in [1..#X] do 
      Append(~embed, Create_MapModAbVar(BaseExtend(X[i],R), D, 
          RMatrixSpace(QQ, Dimension(RationalHomology(X[i])), n)!embed_vs[i], K));
      Append(~proj, Create_MapModAbVar(D, BaseExtend(X[i],R),
       RMatrixSpace(QQ, n, Dimension(RationalHomology(X[i])))!proj_vs[i], K));
   end for;
   D`is_only_motivic := &or[IsOnlyMotivic(A) : A in X];
   D`weights := &join[Weights(A) : A in X];
   return D, embed, proj;
end intrinsic;

intrinsic DirectSum(A::ModAbVar, B::ModAbVar) -> ModAbVar, List, List
{The direct sum D of A and B, together with the embedding
maps, and the projection maps }
   require Sign(A) eq Sign(B) : 
        "The signs of the summands must be the same.";

   return DirectSum([A,B]);
end intrinsic;


/***************************************************************************

  << Sum in an Ambient Variety >>

  The sum {\tt A+B} is the sum of $A$ and $B$ inside a common ambient
  abelian variety, and this sum need not be direct, unless the intersection
of $A$ and $B$ is $0$.

 ***************************************************************************/

function GiveCommonCodomain(X)
   D := [* Codomain(X[1]) *]; 
   for i in [2..#X] do 
      B := Codomain(X[i]);
      if not (B in D) then
         Append(~D, B);
      end if;
   end for;
   if #D gt 1 then
      S, embed, proj := DirectSum([B : B in D]);   // change to sequence
      Y := [];
      for phi in X do 
         for i in [1..#D] do 
            if D[i] eq Codomain(phi) then
               Append(~Y, phi*embed[i]);
               break;
            end if;
         end for;
      end for;
      return Y;
   else
      return X;
   end if;
end function;

intrinsic FindCommonEmbeddings(X::[ModAbVar]) -> BoolElt, List
{True and a list of embeddings into a common abelian variety, if one can
be found.  If true, the second return value is the list of embeddings.}
   Verbose("FindCommonEmbeddings", 
     Sprintf("Finding common embeddings of %o.",X),"");

   /* ALGORITHM:
       We find a codomain in the intersection of every Embeddings(A) as follows.
       Just try each in Embeddings(X[1]) until we find one that is in all,
       or find that nothing is in all embeddings.
   */   
   CD := [* *];
   size := [];
   for A in X do 
      cd := [Codomain(psi) : psi in Embeddings(A)];
      Append(~size, #cd);
      Append(~CD, cd);
   end for; 
   _, i := Min(size);
   for J in CD[i] do
      fails := false;
      for k in [1..i-1] cat [i+1..#CD] do
         is_in := false;
         for l in [1..#CD[k]] do
            if J eq CD[k][l] then
               is_in := true;
               break;
            end if;
         end for;
         if not (is_in) then
            fails := true;
            break;
         end if;
      end for;
      if not fails then
         E := [* *];
         for j in [1..#CD] do
            for s in [1..#CD[j]] do
               if CD[j][s] eq J then
                  Append(~E, Embeddings(X[j])[s]);
               end if;
            end for;
         end for;
         return true, E;
      end if;
   end for;
   return false, [* *];
end intrinsic;

intrinsic SumOfImages(phi::MapModAbVar, psi::MapModAbVar) -> ModAbVar, MapModAbVar, List
{The sum D of the images of the morphisms phi and psi in their common codomain, 
a morphism from D into their common codomain, and a list containing a morphism 
from the domain of each of phi and psi to D.  }
   return SumOfMorphismImages([* phi, psi *]);
end intrinsic;

intrinsic SumOfMorphismImages(X::List) -> ModAbVar, MapModAbVar, List
{The sum D of the images of the morphisms in the list X of
homomorphisms of modular abelian varieties in their common codomain, a
morphism from D into their common codomain, and a list containing a
morphism from the domain of each morphism to D.}
   Verbose("SumOfMorphismImages", 
     Sprintf("Finding sum of images of morphisms %o.",X),"");

   require #X gt 0 : "Argument 1 must be nonempty.";
   Y := GiveCommonCodomain(X);
   CD := Codomain(Y[1]);
   K := CommonFieldOfDefinition(Y);
   R := OverRing([* K, CommonBaseRing([Domain(A) : A in Y] cat [Codomain(A) : A in Y]) *]);

   /*  Lemma: Suppose f and g are morphisms from A, B into a common abelian variety. 
              Then f(A) + g(B) is an abelian variety.  By induction, same statement
              for any number of morphisms.

       Proof. f(A) + g(B) is the image of the abelian variety A x B under the 
              morphism (a,b) |--> f(a) + g(b), so f(A) + g(B) is an abelian
              variety since images of morphisms of abelian varieties are
              abelian varieties (continuous image of connected set is connected).

       Algorithm: Compute the vector space sum of the images of the vector spaces.  
       Since f(A) + f(B) is an abelian subvariety, the integral homology is induced
       from the integral homology of C.   Thus we just have to compute the underlying
       vector space of f(A) + f(B), which is easy.
   */

   // A basis for V defines an embedding matrix from the sum into CD.  
   V := &+[Image(Matrix(phi)) : phi in Y];
   sum_embedding_matrix := RMatrixSpace(QQ, Dimension(V), Degree(V))!Basis(V);
   
   H := Create_ModAbVarHomol_Subspace(Homology(CD), V);
 
   // The matrices in A_to_V define maps from each of the domains of the 
   // maps in Y into the rational homology of V wrt to Basis(V).
   A_to_V := [* *];
   for phi in Y do 
      Append(~A_to_V, RMatrixSpace(QQ, Nrows(M), Dimension(V))!
                   &cat[Coordinates(V,M[i]) : i in [1..Nrows(M)]] where M := Matrix(phi));
   end for;
   
   // Modular structure:   We have maps from modular J_A for 
   // each of the elements A of Y, and we have a modular embedding 
   // from CD into a J_CD.  We use only the modular embedding and
   // let the modular param from J_CD be computed automatically
   // by the modular abelian variety constructor.
   Je := Codomain(ModularEmbedding(CD));
   Je_matrix := sum_embedding_matrix*Matrix(ModularEmbedding(CD));
   /*   Jp, _, Jp_proj := DirectSum([Domain(ModularParameterization(Domain(phi))) : phi in Y]);
   param := [* *];  
   for i in [1..#Y] do 
      Append(~param, Matrix(ModularParameterization(Domain(Y[i])))*A_to_V[i]);
   end for;
   Jp_matrix := VerticallyStackMatrices(param);
   */
   J := <Je, Je_matrix, false>;

   name := "";
   /*   for i in [1..#Y] do 
         name *:= Name(Domain(Y[i])) * (i eq #Y select ")" else "+");
       end for; */

   D := Create_ModAbVar(name, H, K, R, J);   
   from_A := [* *];
   for i in [1..#Y] do 
      Append(~from_A, Create_MapModAbVar(Domain(Y[i]), D, A_to_V[i], K));
   end for;
   into_CD := Create_MapModAbVar(D, CD, sum_embedding_matrix, K);

   return D, into_CD, from_A;
end intrinsic;

intrinsic SumOf(X::[ModAbVar]) ->  ModAbVar
{The sum of the modular abelan varieties in X.}
   require #X gt 0 : "Argument 1 must be nonempty.";
   t, E := FindCommonEmbeddings(X);
   if not t then
      S := DirectSum(X);
      return S;
   end if;
   D, D_to_Je, X_to_D :=  SumOfMorphismImages(E);
   return D;
end intrinsic;

intrinsic '+'(A::ModAbVar, B::ModAbVar) ->  ModAbVar
{The sum of the images of A and B in a common ambient abelian variety.}
   return SumOf([A,B]);
end intrinsic;


/***************************************************************************

  << Intersections >>

 ***************************************************************************/
intrinsic 'meet'(A::ModAbVar, B::ModAbVar) -> ModAbVarSubGrp, ModAbVar, MapModAbVar
{The intersection of the abelian varieties A and B, in some natural
ambient abelian variety.  }
   return Intersection([A, B]);
end intrinsic;


/* The following needs to be optimized!!! */

intrinsic ComponentGroupOfIntersection(X::[ModAbVar]) -> ModAbVarSubGrp
{Finite component group of intersection.}
   G := Intersection(X);   
   return G;
end intrinsic;

intrinsic ComponentGroupOfIntersection(A::ModAbVar, B::ModAbVar) -> ModAbVarSubGrp
{Finite component group of intersection.}
   return ComponentGroupOfIntersection([A,B]);
end intrinsic;

intrinsic Intersection(X::[ModAbVar]) -> ModAbVarSubGrp, ModAbVar, MapModAbVar
{A finite lift of the component group of the intersection, the
connected component of the intersection, and a map from the abelian
variety that contains the connected component to the abelian variety
that contains the component group.  }
   Verbose("Intersection", Sprintf("Finding intersection of %o.", X),"");
   if #X eq 0 then
      A := ZeroModularAbelianVariety();
      return ZeroSubgroup(A), A, IdentityMap(A);
   end if;
   Y := [A : A in X | Dimension(A) gt 0];
   if #Y eq 0 or #X eq 1 then
      return ZeroSubgroup(X[1]), X[1], IdentityMap(X[1]);
   end if;
   X := Y;
   t, E := FindCommonEmbeddings(X);
   require t : "No known way to make sense of this intersection.";

   return IntersectionOfImages(E);
end intrinsic;

function ComputeIntersectionOfImages(X, kernel, connected)
   assert Type(X) eq List;
   assert Type(kernel) eq BoolElt;
   assert Type(connected) eq BoolElt;

   /* Algorithm:  
      (1) The intersection is isomorphic to the kernel of
              Ker(DirectSum(X) ---> J^(#X-1))
          given by 
              (a1,...,ar) |---> (a_1-a_2, a_2-a_3, ..., a_{r-1}-a_r).
      (2) Compute the intersection by finding that kernel, then
          taking its image in a factor of the direct sum.
    */
    J := Codomain(X[1]);
    Xsum, Xembed, Xproj := DirectSum([Domain(f) : f in X]);
    Jsum, Jembed, Jproj := DirectSum([J : i in [1..#X-1]]);
    map := Hom(Xsum,Jsum)!0;
    for i in [1..#X-1] do
       map := map + (Xproj[i]*X[i]-Xproj[i+1]*X[i+1])*Jembed[i] ;
    end for;

    G := false;  C := false; i := false;
    if kernel and not connected then
       G := ComponentGroupOfKernel(map);
    elif not kernel and connected then
       C := ConnectedKernel(map);
    else
       G, C, i := Kernel(map);
    end if;
    if Type(G) ne BoolElt then
       G := X[1](Xproj[1](G));
    end if;
    if Type(C) ne BoolElt then
       C := X[1](Xproj[1](C));
    end if;
    return G, C, i, map;
end function;

intrinsic IntersectionOfImages(X::List) ->  ModAbVarSubGrp, ModAbVar, MapModAbVar
{A finite lift of the component group of the intersection,  the 
connected component of the intersection, and a map from the 
abelian variety that contains the connected component 
to the abelian variety that contains the component group.  }
   Verbose("IntersectionOfImages", 
       Sprintf("Finding intersection of images of %o.", X),"");

   require #X gt 0 : "Argument 1 must be nonempty.";
   if #X eq 1 then
      C := Image(X[1]);
      G := ZeroSubgroup(Codomain(X[1]));
      return G, C, IdentityMap(Codomain(X[1]));
   end if;

   J := Codomain(X[1]);
   for i in [2..#X] do
      require Codomain(X[i]) eq J : "All codomains must be the same.";
   end for;

   return ComputeIntersectionOfImages(X, true, true);   

end intrinsic;


/***************************************************************************

  << Quotients >>


 ***************************************************************************/


intrinsic '/'(A::ModAbVar, B::ModAbVar) -> ModAbVar, MapModAbVar
{The quotient of A by a natural image B' of B, if possible.  }
   Verbose("/", Sprintf("Finding quotient A/B, where A=%o and B=%o.", A,B), "");
   eB := ModularEmbedding(B);
   piA := ModularParameterization(A);
   require Codomain(eB) eq Domain(piA) : 
       "Arguments 1 and 2 must be parameterized by same abelian variety.";
   return Cokernel(eB*piA);
end intrinsic;

