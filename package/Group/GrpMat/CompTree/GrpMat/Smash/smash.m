freeze;

import "random.m": RandomConjugate;
import "random.m": AddRandomTranslatingConjugate;
import "minblocks.m": MinBlocks, NumberBlocks;
import "functions.m": TensorProductFlag;
import "functions.m": SetImprimitiveFlag;
import "functions.m": SetTensorInducedBasis;
import "functions.m": SetTensorInducedPermutations;
import "functions.m": SetTensorInducedFactors;
import "functions.m": SetBlockSystem;
import "functions.m": BlockSystem;
import "functions.m": SetBlockNumbers;
import "functions.m": SetBlockSizes, SetBlocksImage;
import "functions.m": SetGenerators;
import "functions.m": SetTensorInducedFlag, TensorInducedFlag;
import "random.m": RandomElement;
import "tensor.m": TensorProductDecomposition;
import "tensor.m": KroneckerFactors;
import "semilinear.m": SemiLinearDecomposition;
import "extraspecial.m": ExtraSpecialDecomposition;
import "minblocks.m": GroupActionOnBlocks;
import "induced.m": SymmetricTensorProductDecomposition;
import "induced.m": MultipleTensorProductDecomposition;

forward  RandomIrreducibleSubmodule, SemiSimpleDecomposition, 
TranslatesDirectSum, TranslatesSModules; 

procedure AddRandomNonCentralisingConjugate (module, ~S, C)

   G := Type (module) eq GrpMat select module else Group (module);
   repeat
      g := RandomConjugate (G, S);
   until g * C ne C * g;

   Append (~S, g);

end procedure;

/* module is a G-module for matrix group  G,
   S is a list of matrices lying in G,
   PartialSmash should be true or false.
   Let N be the normal closure of <S> in  G.
   SmashModule looks for certain types of decomposition of 
   the natural GModule M of G  with respect to N.
   The possible decompositions are:
   (i) G is imprimitive and N fixes all blocks in a block system.
   (ii)  G preserves a tensor product decomposition of  M, and 
         N acts as scalars on the first tensor factor.
   (iii) G is semilinear over an extension field of the ground 
         field of G, and N is linear over this extension field.
   (iv) N is extraspecial or a 2-group of symplectic type.
   (v) G is tensor-induced, and all of the tensor
       factors are fixed by  N.
   If one of these decompositions is found, then the relevant 
   information is stored in the appropriate flags of module.

   If PartialSmash is "PartialSmash", we terminate as soon as we 
   discover that the normal subgroup must act absolutely irreducibly
   -- hence, we do not seek to decide whether or not the group is
   is a normaliser of a p-group or is tensor-induced; that is, 
   decompositions of types (iv) and (v) are not looked for. */

SmashModule := procedure (module, ~S, PartialSmash : NoSymTens:=false )

   if #S eq 0 then
      vprint Smash: "S is empty";
      return;
   elif forall {g : g in S | IsScalar (g)} then 
      vprint Smash: "S contains only scalar matrices";
      return;
   end if;

   if IsIrreducible (module) eq false then 
      vprint Smash: "Module is not irreducible";
      return;
   elif IsAbsolutelyIrreducible (module) eq false then 
      vprint Smash: "Module is not absolutely irreducible";
      return;
   end if;

   if PartialSmash cmpeq "PartialSmash" then 
      PartialSmash := true;
   else
      PartialSmash := false;
   end if;

   d, F := BasicParameters (module);

   gl := GL (d, F);
   ChangeUniverse (~S, gl);
   A := MatrixAlgebra (F, d);
   V := RSpace (gl);

   /* if necessary, enlarge S to contain MinSize elements */
   MinSize := 3;
   if #S lt MinSize then 
      vprint Smash: "At entry, S has size ", #S;
      G := Type (module) eq GrpMat select module else Group (module);
      while #S lt MinSize do 
         Append (~S, RandomConjugate (G, S));
      end while;
   end if; 

   while true do
     
     vprint Smash: "At top of main loop, S has size ", #S;

     matrices := GroupGenerators (module);
     Smodule := GModule (sub <gl | S>);

     /* We use gl in the above expression, to prevent MAGMA wasting 
        time checking that the elements of S lie in G.  */

     Wmodule, W := RandomIrreducibleSubmodule (Smodule);
     dimW := Dimension (Wmodule);

     if dimW lt d then  // <S> acts reducibly.
       vprint Smash: "Dimension of <S>-module is ", dimW;
       submodules := [Wmodule];
       summands := [W];
       SemiSimpleDecomposition (matrices, S, Smodule, ~submodules, ~summands);

       /* If successful, submodules and summands are longer, and 
          have increased to sequences which define a direct sum 
          decomposition of the underlying space as a sum of 
          G-translates of Wmodule.
          Otherwise, we increase S and restart.  */

       t := #submodules;

       if t eq 1 then 
         // This occurs <==> we have failed to find a decomposition
         AddRandomTranslatingConjugate (module, ~S, W);
       else
         basis := Basis (RowSpace (W));
         ChangeUniverse (~basis, V);
         blocks := MinBlocks (module, basis);
         if NumberBlocks (blocks) gt 1 then
           vprint Smash: "The group is imprimitive";
           SetImprimitiveFlag (module, true);
           SetBlockSystem (module, blocks);
           SetBlocksImage (module, GroupActionOnBlocks (blocks));
           r := NumberBlocks (BlockSystem (module));
           SetBlockNumbers (module, {r});
           SetBlockSizes (module, {d div r});
           return;
         end if;

         /* At this stage, all of the summands of Wmodule should be 
            isomorphic as <S>-modules.  If not, we need to enlarge  S. 
            If so, we will find explicit isomorphisms.
            We are going to try to build up a natural basis for V, 
            as a matrix "basis".  The rows will be in blocks of length 
            dimW, with the i-th block spanning the i-th summand. 
            The bases will be such that the isomorphisms
            found between the summands map one basis to anaother. */
  
         basis := Hom (V, V)!0;
         InsertBlock (~basis, W, 1, 1);
         i := 2;
         while i le t do
           B := GHom (Wmodule, submodules[i]);
           /* Testing for isomorphism. */
           if Dimension (B) gt 0 then 
             InsertBlock (~basis, (B.1) * summands[i], (i - 1) * dimW + 1, 1);
             i +:= 1;
           else
             break;
           end if;
         end while;

         if Dimension (B) eq 0 then 
           /* The modules are not isomorphic.
              That must mean we don't have the right decomposition, 
              or we would have found blocks of imprimitivity. 
              So we enlarge S and loop around again. */

           vprint Smash: "Submodules non-isomorphic";
           vprint Smash: "Adding random translating conjugate to S";
           AddRandomTranslatingConjugate (module, ~S, W);

         elif IsAbsolutelyIrreducible (Wmodule) then 

           /* If the modules are isomorphic and absolutely irreducible,
              we look for a tensor decomposition. If we fail to find one,
              it must be because we don't have the right decomposition. 
              So we enlarge S and loop around again.  */

           basis := A!basis;
  
           if TensorProductDecomposition (module, basis, t, dimW) then 
              vprint Smash: "Found a tensor product decomposition\n";
              return;
           else 
             vprint Smash: "Failed to find tensor decomposition.\n";
             vprint Smash: "Adding random translating conjugate to S";
             AddRandomTranslatingConjugate (module, ~S, W);
           end if;
         else
           /* we have a centralising field of degree e > 1
              We hope to find the group inside GammaL (d/e, q^e). 
              If we fail to find that embedding, it must be because 
              we have the wrong centraliser.
              So we enlarge S by something which doesn't 
              commute with the matrix C which we thought was the 
              centraliser, and loop around again.  */

           EA := EndomorphismAlgebra (Wmodule);
           c := EA.1;  

           /* c now centralises Wmodule
              and is a dimW x dimW matrix wrt the standard basis.
              We find the centraliser of the full S-module using 
              the isomorphisms between the submodules. 
              First set all the entries to be zero */

           id := MatrixAlgebra (F, t)!1;
           basis := A!basis;
           C := basis^-1 * TensorProduct (id, c) * basis;

           /* The tensor product gives centralising matrix with 
              respect to the basis which is the concatenation of 
              summands[1], B[1]summands[2], ..., B[t-1]summands[t]
              We check it commutes with everything in S */ 

           for s in S do
             t := A!s;
             if t * C ne C * t then
               error "Error in SmashModule - centraliser isn't correct";
             end if;
           end for;

           e := Dimension (EA);

           /* If SemiLinearDecomposition returns false, it must 
              be the case that C doesn't centralise <S>^G. 
              So S is enlarged by the addition of a 
              non-translating element.
              The paper suggests non-centralising element 
              but we can't always find one*/

           if SemiLinearDecomposition (module, S, C, e) then
             return; 
           else
             AddRandomTranslatingConjugate (module, ~S, C);
           end if;
         end if;
       end if; // from:  if t eq 1 then 

     else // if Dimension (Wmodule) lt Dimension (module) then  

       /* <S> acts irreducibly on the module.
          So either <S> acts absolutely irreducibly or 
          <S> <= GL (d/e, q^e) and G <=GammaL (d/e, q^e), for some e > 1. */

       if IsAbsolutelyIrreducible (Smodule) then
         vprint Smash: "<S> acts absolutely irreducibly on the module";
         if PartialSmash then return; end if;
         if ExtraSpecialDecomposition (module, S) then 
           /* it must have found an extraspecial decomposition. */
           vprint Smash: "G normalises a p-group";
           return;
         elif NoSymTens then return;
         elif SymmetricTensorProductDecomposition (module, S) then 
           vprint Smash: "G is tensor-induced\n";
           return;
         else 
           vprint Smash: "No decomposition found\n";
           return;
         end if;
       else // <S> acts irreducibly but not absolutely irreducibly
         vprint Smash: "<S> acts irreducibly";
         EA := EndomorphismAlgebra (Smodule);
         C := EA.1;
         e := Dimension (EA);
         if SemiLinearDecomposition (module, S, C, e) then 
           vprintf Smash: "Group embeds in GammaL (%o, %o^%o)\n", d/e, #F, e, "\n";
           return; 
         else 
            /* When SemiLinearDecomposition returns false it must be 
               the case that C doesn't centralise <S>^G. 
               So S is enlarged by the addition of an element 
               which doesn't centralise C.  */
           AddRandomNonCentralisingConjugate (module, ~S, C);
         end if;
       end if; // if IsAbsolutelyIrreducible (Smodule)=true then
     end if; // if Dimension (Wmodule) lt Dimension (module) then  

   end while;  

end procedure;

/* M is a KG-module. Calls Meataxe repeatedly, and calculates 
   an irreducible submodule  L of M. Returns L and a morphism 
   from L to M (if L ne M).  */

function RandomIrreducibleSubmodule (M)

   L1, Q, x := Meataxe (M);
   if L1 eq M then
     return L1, 0;
   end if;
   phi1 := Morphism (L1, M);
   L2, phi2 := RandomIrreducibleSubmodule (L1);
   if L2 ne L1 then
     phi1 := phi2 * phi1;
   end if;
   return L2, phi1;
end function;

/* S generates a subgroup of G = <matrices>, which acts on 
   a vector space. 
   W = summands[1] spans an irreducible S-module, 
   Wmodule = submodules[1].
   We hope to decompose the underlying vector space as a direct 
   sum of irreducible <S>-modules which are translates of W under G.
   If we can do this, the procedure returns two lists.
   The first contains the irreducible submodules themselves, 
   the second a set of bases for irreducible submodules.
   Otherwise, submodules is unchanged, and has length 1, and S will
   have to be increased. */

SemiSimpleDecomposition := procedure 
                 (matrices, S, Smodule, ~submodules, ~summands)

   TranslatesDirectSum (matrices, ~summands);
   t := #summands;
   dimW := Dimension (submodules[1]);
   if t eq Degree (matrices[1])/dimW then 
     s := TranslatesSModules (matrices, S, summands);
     if s then
         i := 2;
         while i le t do
           Append (~submodules, ImageWithBasis (summands[i], Smodule));
           i +:= 1;
         end while;
         vprintf Smash: "Module is decomposed as a sum of %o irreducibles of\
 dimension %o\n", t, dimW;
     else
       vprint Smash: "Translates of W are not modules";
     end if;
   end if;

end procedure;

/* W = summands[1] is a matrix defining a subspace of a vector space
   on which G = <matrices> acts.
   We attempt to decompose the space as a direct sum of translates 
   of <W>.  If we succeed then summands is increased to a sequence 
   of translates of W which span the space as a direct sum. */

TranslatesDirectSum := procedure (matrices, ~summands)

   socle := RowSpace (summands[1]);
   dimsoc := Dimension (socle);
   dimW := dimsoc;

   i := 1;
   while i le #summands do
     Wi := summands[i];
     j := 1;
     while j le #matrices do
       g := matrices[j];
       Wig := Wi * g; 
       newsocle := socle+RowSpace (Wig);
       /* dimension should be dimsoc or dimsoc + dimW. 
          If not, return false. */
       dns := Dimension (newsocle);
       if dns eq dimsoc + dimW then
         socle := newsocle;
         dimsoc := dns;
         Append (~summands, Wig);
         if dimsoc eq Degree (matrices[1]) then
           return;
         end if;
       elif dns ne dimsoc then
         return;
       end if;
       j +:= 1;
     end while;
     i +:= 1;
   end while;
end procedure;
       
/* G = <matrices> and <S>, a subgroup of G, act on the same space.
   summands is as returned by TranslatesDirectSum, so summands is a 
   list of normed bases, which together span the space.
   The first basis spans a module W for S, the remaining are
   translates of that.
   We check to see if the translates are also submodules of Smodule. 
   If not then some conjugate of S, which we can identify, does 
   not fix W, and we return that conjugate. 
   Otherwise we return true. */

TranslatesSModules := function (matrices, S, summands)

   k := 2;
   while k le #summands do
     Wk := summands[k];
     RS := RowSpace (Wk);
     for s in S do
       if RowSpace (Wk * s) ne RS  then
         return false;
       end if;
     end for; 
     k +:= 1;
   end while;

   return true;

end function;
