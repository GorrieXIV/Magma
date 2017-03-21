freeze;

   /*--- Constructive recognition functions for *-algebras ---*/


import "verify.m": IsUnitaryElement;

import "prelims.m": __RF_SETUP, IdentifyBasis;

import "grpalg.m": GroupAlgebraAsMatrixStarAlgebra;


__basic_star_algebra_info := function (A)

     RF := __RF_SETUP ("algebra");
     data := rec < RF | >;

     k := BaseRing (A);
     n := Degree (A);     

     RAD, TAFT := TaftDecomposition (A);
     RAD`Star := A`Star;
     TAFT`Star := A`Star;
     TAFT_RF := __RF_SETUP ("algebra");
     TAFT_data := rec < TAFT_RF | >;
     
     TAFT_data`isSemisimple := true;
     TAFT_data`taftComplement := TAFT;
     TAFT_data`jacobsonRadical := sub < Generic (A) | A!0 >;
     TAFT`StarAlgebraInfo := TAFT_data;
 
     if Dimension (RAD) eq 0 then
         ALT_RAD := [ ];
     else
         Rgens := [ (k.1)^f * RAD.i : f in [0..Degree (k) - 1],
                                      i in [1..Ngens (RAD)] ];
         X := { Rgens[i] - Rgens[i] @ A`Star : 
                                  i in [1..#Rgens] };
         X := [ a : a in X | a ne RAD!0 ];
         if (#X gt 0) then
            VXK := [ Vector (X[i]) : i in [1..#X] ];
            U := VectorSpace (PrimeField (k), n^2 * Degree (k));
            VXk := [ U!(&cat [Eltseq (VXK[i][j]) : j in [1..n^2]]) : 
                                                         i in [1..#VXK] ]; 
            positions := IdentifyBasis (VXk);
            ALT_RAD := [ X[i] : i in positions ];
         else
            ALT_RAD := [ ];
         end if;
     end if;
              
     data`isSemisimple := (Dimension (RAD) eq 0);
     data`jacobsonRadical := RAD;
     data`taftComplement := TAFT;
     data`alternatingRadical := ALT_RAD;
    
     A`StarAlgebraInfo := data;

return true;
end function;


/* 
   should produce the same information as one gets for free
   from the slope method for computing adj
*/
__basic_semisimple_info := function (A)

     star := A`Star;
     d := Degree (A);
     K := BaseRing (A);
     RF := __RF_SETUP ("algebra");

     /* first find the minimal ideals of <A> as an assoc. alg. */
     simps := MinimalIdeals (A);
     simples := < >;
     for i in [1..#simps] do
         Xi := simps[i];
         Xi := sub < Generic (Xi) | Basis (Xi) >;
         Xi`IsBasis := true;
         Append (~simples, Xi);
     end for;

     /* now find the minimal *-ideals of <A> */
     star_simples := < >;
     btypes := < >;
     for i in [1..#simples] do

         Xi := simples[i];
         Yi := sub < Generic (A) | 
                     [ (Xi.j) @ star : j in [1..Ngens (Xi)] ] >;
         flag := exists (j){ l : l in [1..#simples] | Yi eq simples[l] };

         if not flag then  

            return false; 

         elif (i le j) then

            if (i eq j) then

               btype := "classical";
               Ui := Xi;

            elif (i lt j) then

               btype := "exchange";
               Ui := sub < Generic (A) | 
                              [ Xi.j : j in [1..Ngens (Xi)] ] cat
                              [ Yi.j : j in [1..Ngens (Yi)] ] >;

            end if;

            Ui`IsBasis := true;
            Ui`Star := A`Star;

            data := rec < RF | isSimple := true,
                               isSemisimple := true,
                               jacobsonRadical := 
                                     sub < Generic (A) | A!0 >,
                               taftComplement := Ui,
                               basicSimpleTypes := < btype >
                        >;
            Ui`StarAlgebraInfo := data;

            Append (~star_simples, Ui);
            Append (~btypes, btype);
           
         end if;

     end for;

     /* find a nice basis that exhibits the *-simples */ 
     newbas := [ ];
     srdegrees := [ ];
     for i in [1..#star_simples] do
         U := star_simples[i];
         imU := &+ [ Image (U.j) : j in [1..Ngens (U)] ];
         newbas cat:= Basis (imU);
         Append (~srdegrees, Dimension (imU));
     end for;
     COB := GL (d, K)!Matrix (newbas);
     COBi := COB^-1;

     /* find the semi-reduced versions of the *-simples */
     srcomps := < >;
     pos := 1;
     for i in [1..#star_simples] do
	  m := srdegrees[i];
	  U := star_simples[i];
          X := [ COB * U.j * COBi : j in [1..Ngens (U)] ];
          Y := [ ExtractBlock (X[j], pos, pos, m, m) : j in [1..#X] ];
          UU := sub < MatrixAlgebra (K, m) | Y >;
          UtoUU := hom < U -> UU | r :-> 
                      ExtractBlock (COB * r * COBi, pos, pos, m, m) >;
          UUtoU := hom < UU -> U | r :-> 
            COBi * InsertBlock (MatrixAlgebra (K, d)!0, r, pos, pos) * COB >;
          UU`Star := hom < UU -> UU | r :-> ((r @ UUtoU) @ U`Star) @ UtoUU >;
          UU`IsBasis := true;
          UU`StarAlgebraInfo := U`StarAlgebraInfo;
          Append (~srcomps, UU);
          pos +:= m;
     end for;

     /* augment the structural information for <A> */
     A`StarAlgebraInfo`isSimple := (#star_simples eq 1);
     A`StarAlgebraInfo`srComponents := srcomps;
     A`StarAlgebraInfo`basicSimpleTypes := btypes;
     A`StarAlgebraInfo`transitionMatrix := COB;
     A`StarAlgebraInfo`srDegrees := srdegrees;
     
return true;
end function;


       /* ---- recognition function for *-algebras ---- */

/*
   The input is an algebra <A> possessing the attribute <A>`Star
   indicating that <A> is equipped with an involution.

   The function attaches to <A> the attribute <A>`StarAlgebraInfo,
   a record consisting of the following fields:

   <isSimple> indicating whether or not <A> is a simple *-algebra
   <isSemisimple> similar
   <jacobsonRadical> the (*-invariant) Jacobson radical of <A>
   <alternatingRadical> this is the intersection of the radical
                        with the subspace consisting of all elements
                        x in <A> for which x^* = -x; this information
                        is useful mostly internally
   <taftComplement> a *-invariant (semisimple) complement to the radical
   <simpleComponents> a complete list of the minimal *-invariant
                      ideals of <taftComplement>
   <basicSimpleTypes> a list indicating whether each elements of 
                      <simpleComponents> is of "classical" or "exchange" type

   For each member, <S>, of <simpleComponents>, the function also attaches
   the attribute <S>`StarSimpleInfo, which consists of the following fields:

   <simpleParameters> a tuple indicating the exact type of the standard 
                      simple *-algebra to which <S> is isomorphic
   <standardSimple> the standard copy, <T>, of that simple *-algebra
   <standardIsomorphism> a *-isomorphism <S> -> <T>
   <standardInverse> the inverse of that map

   The function returns <true> if and only if it succeeded in 
   compiling all of this data.
*/

__power_series_trick := function (z)
    m := 1;
    w := z;
    repeat
        w *:= z;
        m +:= 1;
    until w eq 0;
    x := z + Identity (Parent (z));
    xx := &+ [ Catalan (n-1) * (-1/4)^n * z^(2*n) :
                   n in [1..Ceiling (m/2)] ];
return x - 2 * xx;
end function;


intrinsic RecogniseStarAlgebra (A::AlgMat) -> BoolElt

   { Constructively recognise the *-algebra A. }

     require IsStarAlgebra (A) : "argument has no assigned involution";

     require Type (BaseRing (A)) eq FldFin :
        "Base ring of argument is not a finite field";
     
     if not assigned A`StarAlgebraInfo then
	 /* carry out the basic constructions */
         flag := __basic_star_algebra_info (A);
         if not flag then
            return false;
         end if;
     end if;

     TAFT := A`StarAlgebraInfo`taftComplement;

     if not assigned (A`StarAlgebraInfo`srComponents) then
         /* decompose Taft complement into minimal *-ideals */
         flag := __basic_semisimple_info (TAFT);
         if not flag then
            return false;
         end if;
     end if;

     data := A`StarAlgebraInfo;
     data`isSimple := data`isSemisimple and TAFT`StarAlgebraInfo`isSimple;
     data`taftComplement := TAFT;
     data`transitionMatrix := TAFT`StarAlgebraInfo`transitionMatrix;
     data`srComponents := TAFT`StarAlgebraInfo`srComponents;
     data`srDegrees := TAFT`StarAlgebraInfo`srDegrees;
     data`basicSimpleTypes := TAFT`StarAlgebraInfo`basicSimpleTypes;

     /* process each of the simple components */
     COB := data`transitionMatrix;
     degs := data`srDegrees;
     COBi := COB^-1;
     sharp_gens := [ ];
     sharp_order := 1;
     pos := 1;
     for i in [1..#data`srComponents] do

         S := data`srComponents[i];
         btype := data`basicSimpleTypes[i];

         /* recognise conjugated simple */
         if btype eq "classical" then
             isit, T, StoT, TtoS := RecogniseClassicalSSA (S);
         else
             isit, T, StoT, TtoS := RecogniseExchangeSSA (S);
         end if;
      
         if not isit then
  	    "[Recognise SA]: failed to recognise simple components";
            return false;
         end if;

         /* store recognition info for simple */
         RF := __RF_SETUP ("simple");
         Sdata := rec < RF | >;
         Sdata`simpleParameters := T`StarSimpleInfo`simpleParameters;
         Sdata`standardSimple := T;
         Sdata`standardIsomorphism := StoT;
         Sdata`standardInverse := TtoS;
         S`StarSimpleInfo := Sdata; 

         /* pull back sharp group generators into <S> */
         Tgens := T`StarAlgebraInfo`sharpGroupGenerators;
         sharp_order *:= T`StarAlgebraInfo`sharpGroupOrder;
         Sgens := [ Tgens[j] @ TtoS : j in [1..#Tgens] ];

         /* embed into the sharp group of <A> */
         u := Identity (GL (Degree (A), BaseRing (A)));
         for s in Sgens do
            x := InsertBlock (u, s, pos, pos);
            xx := COBi * x * COB;
            assert IsUnitaryElement (A, xx);
            Append (~sharp_gens, xx);   
         end for;

         /* update <pos> */
         pos +:= degs[i];

     end for;   

     // construct gens for O_p(<I>)
     J := data`jacobsonRadical;
     gl := GL (Degree (A), BaseRing (A));
     Jminus := data`alternatingRadical;

     sharp_order *:= Characteristic (BaseRing (A))^(#Jminus);
     if #Jminus gt 0 then
	Op_gens := [ gl!(__power_series_trick (Generic (A)!z)) : z in Jminus ];
        sharp_gens cat:= Op_gens; 
     end if;

     assert forall{x : x in sharp_gens | IsUnitaryElement (A, x)};
       
     data`sharpGroupOrder := sharp_order;
     data`sharpGroupGenerators := sharp_gens;

     A`StarAlgebraInfo := data;

return true;
end intrinsic;


intrinsic RecogniseStarAlgebra (A::AlgGrp) -> BoolElt

   { Constructively recognise the group algebra A as a *-algebra. }

     if not IsStarAlgebra (A) then
         /* equip <A> with its natural involution */
         star := StarOnGroupAlgebra (A);
     end if;

     "computing with regular representation of A in degree", Dimension (A);

     if Dimension (A) gt 100 then
     "this may take some time...";
     end if;

     /* construct the regular representation of <A> */
     MatA, phi, psi := GroupAlgebraAsMatrixStarAlgebra (A);

     /* recognise <MatA> */
     assert RecogniseStarAlgebra (MatA);
     data := MatA`StarAlgebraInfo;

     /* map relevant constructions back to <A> */
     RF := __RF_SETUP ("grpalg");
     Adata := rec < RF | >; 
     Adata`isSimple := data`isSimple;
     Adata`isSemisimple := data`isSemisimple;
     Adata`jacobsonRadical :=
         sub < A | [ (data`jacobsonRadical.i) @ psi : 
		       i in [1..Ngens (data`jacobsonRadical)] ] >;
     Adata`taftComplement := 
         sub < A | [ (data`taftComplement.i) @ psi : 
		       i in [1..Ngens (data`taftComplement)] ] >;
     Adata`simpleParameters :=
         [ S`StarSimpleInfo`simpleParameters : 
                          S in data`srComponents ]; 

     A`StarAlgebraInfo := Adata;

return true;

end intrinsic;



intrinsic RecognizeStarAlgebra (A::AlgMat) -> BoolElt

   { Constructively recognise the *-algebra A. }

return RecogniseStarAlgebra (A);

end intrinsic;



intrinsic RecognizeStarAlgebra (A::AlgGrp) -> BoolElt
 
   { Constructively recognise the group algebra A as a *-algebra. }

return RecogniseStarAlgebra (A);

end intrinsic;



     /*--- intrinsics to access info about *-algebras ---*/


intrinsic IsSimpleStarAlgebra (A::AlgMat) -> BoolElt

   { True if and only if A has no proper *-ideals.}

     require IsStarAlgebra (A) : "argument has no assigned involution";

     if not assigned A`StarAlgebraInfo`isSimple then
         assert RecogniseStarAlgebra (A);
     end if;

return A`StarAlgebraInfo`isSimple;
   
end intrinsic;


intrinsic IsSimpleStarAlgebra (A::AlgGrp) -> BoolElt

   { True if and only if A has no proper *-ideals. }

     if not IsStarAlgebra (A) then
         /* equip <A> with its natural involution */
         star := StarOnGroupAlgebra (A);
     end if;

     if not assigned A`StarAlgebraInfo`isSimple then
         assert RecogniseStarAlgebra (A);
     end if;

return A`StarAlgebraInfo`isSimple;
   
end intrinsic;


intrinsic NormGroup (A::AlgMat) -> GrpMat

   { The group of elements of the *-algebra A satisfying a^* = a^-1.}

     require IsStarAlgebra (A) : "argument has no assigned involution";

     if not assigned A`StarAlgebraInfo`sharpGroupGenerators then
         assert RecogniseStarAlgebra (A);
     end if;

     gens := A`StarAlgebraInfo`sharpGroupGenerators;
     G := sub < GL (Degree (A), BaseRing (A)) | gens >;
     G`Order := A`StarAlgebraInfo`sharpGroupOrder;

return G;

end intrinsic;



intrinsic SimpleParameters (A::AlgMat) -> SeqEnum

   { The defining parameters of simple quotients of the star algebra A.}

     require IsStarAlgebra (A) : "argument has no assigned involution";

     if not assigned A`StarAlgebraInfo`srComponents then
         assert RecogniseStarAlgebra (A);
     else 
         S := A`StarAlgebraInfo`srComponents[1];
         if not assigned S`StarSimpleInfo`simpleParameters then
            assert RecogniseStarAlgebra (A);
         end if;
     end if;

return [ S`StarSimpleInfo`simpleParameters : 
               S in A`StarAlgebraInfo`srComponents ];

end intrinsic;


intrinsic SimpleParameters (A::AlgGrp) -> SeqEnum

   { The defining parameters of the simple quotients of the group
     algebra A regarded as a *-algebra. }

     if not IsStarAlgebra (A) then
         /* equip <A> with its natural involution */
         star := StarOnGroupAlgebra (A);
     end if;

     if not assigned A`StarAlgebraInfo then
         assert RecogniseStarAlgebra (A);
     end if;

return A`StarAlgebraInfo`simpleParameters;

end intrinsic;
