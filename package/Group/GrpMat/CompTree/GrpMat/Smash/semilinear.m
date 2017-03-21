freeze;

import "functions.m": SetSemiLinearFlag;
import "functions.m": SemiLinearFlag;
import "functions.m": SetDegreeFieldExtension;
import "functions.m": SetLinearPart;
import "functions.m": SetCentralisingMatrix;
import "functions.m": SetFrobeniusAutomorphisms;
import "functions.m": ImprimitiveFlag;
import "functions.m": TensorProductFlag;
import "misc.m": FormCommutators;
import "smash.m": SmashModule;

/* part of test to see if GL (d/e, q^e) < G <= GammaL (d/e, q^e)

   M is d-dimensional module, acted on by G, and C is a d x d matrix, which
   acts as multiplication by a scalar x  (a field generator of GF (q^e))
   for some embedding of a d/e-dimensional vector
   space over GF (q^e) in the d-dimensional space.
   G acts as a semilinear group of automorphisms on the d/e-dimensional
   space if and only if, for each generator g of G, there is an integer
   i = i (g) such that Cg = gC^{q^i}, i.e. g corresponds to the
   field automorphism x -> x^(q^i).
   Then we have a map from G to the  (cyclic) group Aut (GF (q^e),
   and C centralises the action of the kernel of this map, which thus lies
   in GL (d, q^e). We test this by first, if possible, finding such i=i (g)
   such that wCg = wgC^(q^i) for a single vector w of the d-dimensional space
   (in fact the first vector of the standard basis) and then checking that
   vCg = vgC^ (q^i) for all other vector v in the basis.
   This function returns a list, powermaps, consisting of the integers
   found, or false if no such integers can be found. */

PowerMaps := function (M, C, e)

   dim, F := BasicParameters (M);
   matrices := GroupGenerators (M);
   q := #F;
   V := VectorSpace (F, dim);

   powermaps := [];
   for g in matrices do
     found := false;
     v := V.1; // v is the vector (1, 0, 0, 0, ...)
     L := v * C * g;
     M := v * g;
     N := C;
     s := 0;
     repeat 
       R := M * N;
       if L eq R then
          found := true;
       else
          N := N^q; s +:= 1;
       end if;
     until found eq true or s eq e; 
     if s eq e then
       vprint Smash: "No powermap found";
       return false, _;
     end if;
     for i in [2..dim] do
       v := V.i; //  Now v is the vector (0, 0, .., 1, ..0).
       M := v * g;
       L := v * C * g;
       R := M * N; 
       if L ne R then
         vprint Smash: "No consistent powermap found";
         return false, _;
        end if;
     end for;
     Append (~powermaps, q^s);
   end for;

   return true, powermaps;

end function;

/* matrices generate the matrix group G, over the field F.
   C is already known to centralise a certain subgroup <S>.
   The hypothesis is that C acts as multiplication by a scalar x
   in GF (q^e) for some embedding of a d/e-dimensional vector
   space over GF (q^e) in the d-dimensional space, where x is a field generator
   of GF (q^e). Thus, provided C centralises the action of <S>^G,  the normal
   closure of <S>, <S>^G embeds in GL (d/e, q^e),  and  G 
   embeds in GammaL (d/e, q^e).
   We test for that by trying to construct a map from G to Aut GF (q^e).    
   We check to see if G can be embedded in GammaL (d/e, q^e)
   If not, it must be because C doesn't centralise
   the action of <S>^G, so there is some conjugate of an element of S which is 
   not centralised by C. We then return false.
   Otherwise, we construct the  sequence  seq of integers i such that
   multiplication of C by the generator g corresponds to the action of
   the field automorphism x -> x^q^i on the corresponding element of
   GF (q^e).
   SemiLinearDecomposition then returns the tuple <e, C, seq> */

SemiLinearDecomposition := function (M, S, C, e) 

   vprintf Smash: "\nTesting for a semilinear decomposition\n";

   vprint Smash: "Looking for powermaps";
   flag, powermaps := PowerMaps (M, C, e);

   if flag then 
      dim, F := BasicParameters (M);
      q := #F;
      vprint Smash: "Found a semilinear decomposition";
      vprintf Smash: "Group embeds in GammaL (%o, %o^%o)\n",  dim/e, q, e;
      SetSemiLinearFlag (M, true);
      SetDegreeFieldExtension (M, e);
      SetLinearPart (M, S);
      SetCentralisingMatrix (M, C);
      SetFrobeniusAutomorphisms (M, powermaps);
      return true;
   else 
      return false;
   end if;

end function;

/* test if the module is semilinear */

procedure SemiLinearTest (M: Limit := 100)

   gens := GroupGenerators (M);
   // Mar 2011 addition to avoid explosion in # of generators 
   if #gens gt Limit then gens := [Random (gens): i in [1..Limit]]; end if;
 
   S := SetToSequence (FormCommutators (gens));

   // Mar 2011 addition to avoid explosion in # of generators 
   if #S gt Limit then S := [Random (S):  i in [1..Limit]]; end if;

   /* does S consist entirely of scalars? 
      if so, add a non-scalar generator to S; if the group 
      does not have a non-scalar generator, it is reducible 
      and will be eliminated earlier in BasicReductionTests */

   if forall {x : x in S | IsScalar (x)} then  
      if exists (y) {y : y in gens | IsScalar (y) eq false} then 
         if exists (z) {z : z in gens | IsScalar ( (y,z) ) eq false} then 
           Append (~S, (y,z) );
         else Append (~S, y);
         end if;
      else 
         vprint Smash: "SemiLinearCheck: no non-scalar commutator";
         return;
      end if;
   end if;

   SmashModule (M, ~S, "PartialSmash");

end procedure;
 
/* decide if M is semi-linear */

IsSemiLinearMain := function (M)

   // have we found that it is semilinear?
   f := SemiLinearFlag (M);
   if f cmpeq true or f cmpeq false then return f; end if;

   d, F := BasicParameters (M);

   vprintf Smash: "Input has dimension %o over %o\n", d, F; 

   if Dimension (M) eq 1 then return false; end if;

   // is M irreducible?
   if IsIrreducible (M) eq false then 
      vprint Smash: "Module is not irreducible";
      return false;
   end if;

   // is M absolutely irreducible?
   if IsAbsolutelyIrreducible (M) eq false then 
      vprint Smash: "Module is not absolutely irreducible";
      return true;
   end if;

   SemiLinearTest (M);

   /* we may discover that M acts imprimitively or semilinearly;
      otherwise we can conclude that it is not semilinear */

   // have we found that it is semilinear?
   if SemiLinearFlag (M) cmpeq true then return true; end if;

   /* if we have not found that it's imprimitive, 
      then we now know that it's not semilinear */

   if not (ImprimitiveFlag (M) cmpeq true) 
   and not (TensorProductFlag (M) cmpeq true) then      
      SetSemiLinearFlag (M, false);
      return false;
   else 
      /* otherwise we have found out that it is imprimitive 
         and failed to decide semilinearity */
      return "unknown";
   end if;

end function; 

intrinsic IsSemiLinear(G::GrpMat) -> BoolElt
{return true if we can prove that G is semilinear, false if we can prove
that G is not semilinear, otherwise "unknown"}
    return IsSemiLinearMain(G);
end intrinsic;
