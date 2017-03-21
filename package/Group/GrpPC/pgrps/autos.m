freeze;

import "misc.m": DefiningParameters, VectorToInt;

/* convert matrix A in GL(d, p) describing action on Frattini quotient
   of d-generator p-group G into automorphism of G */

MatrixToAutomorphism := function (G, A: nrows := 0)
   p, d := DefiningParameters (G);
   if nrows eq 0 then
     m := Nrows (A);
   else
     m := nrows;
   end if;
   assert m ge d;
   error if m lt d, "must define action on at least Frattini quotient";
   zeros := [0: i in [1..NPCgens (G) - m]];
   Images := [<G.i, G!(VectorToInt (A[i]) cat zeros)> : i in [1..m]];
   return hom <G -> G | Images : Check := false >;
end function;

/* assume we know definitions */
SpecialMatrixToAutomorphism := function (G, A)
   p, d := DefiningParameters (G);
   zeros := [0: i in [1..NPCgens (G) - d]];
   return hom < G -> G | [ G!(VectorToInt(A[i]) cat zeros) : i in [1..d]] : Check := false >;
end function;

MatricesToAutomorphisms := function (H, Matrices)
   if Type (Matrices) eq GrpMat then
      Matrices := [Matrices.i: i in [1..Ngens (Matrices)]];
   end if;
   return [rec <RF | map := MatrixToAutomorphism (H, Matrices[i])>:
                     i in [1..#Matrices]];
end function;

/* action of alpha on generators of S, a characteristic subgroup of G */
ActionOnSubgroup := function (G, S, alpha)
   p := DefiningParameters (G);
   q := NPCgens (S);
   gl := GL (q, p);
   return GL (q, p) ! &cat[Eltseq (S!(alpha (S.i))): i in [1..q]];
end function;

/* extend Auts to act on subgroup F of P */
procedure ExtendToSubgroup (P, F, ~Auts)
   for i in [1..#Auts] do
      alpha := Auts[i];
      Auts[i]`extension := ActionOnSubgroup (P, F, alpha`map);
//print "ExtToSub: i, ext:",i,Auts[i]`extension;
   end for;
end procedure;

/* return action of automorphisms on characteristic section S/N of P */
ActionOnFactor := function (P, S, N, Auts)
   if #Auts eq 0 then return []; end if;

   Sphi, phi := quo < S | N >;
   //Sphi := phi (S);
   //T := sub < S | [Sphi.i @@ phi : i in [1..NPCGenerators (Sphi)]]>;
   T := [Sphi.i @@ phi : i in [1..NPCGenerators (Sphi)]];

   p := DefiningParameters (P);
   q := NPCgens (Sphi);
   gl := GL (q, p);
   /*return [gl! &cat [Eltseq (Sphi ! phi(alpha`map (T.i))):
                      i in [1..q]] : alpha in Auts];*/
   result := [];
   for alpha in Auts do
      temp := [];
      for i in [1..q] do
         temp cat:= Eltseq(phi(alpha`map(T[i])));
      end for;
      Append(~result, gl!temp);
   end for;

   return result;
end function;

/* set up action of automorphisms on characteristic section S/N of P */
procedure ExtendToFactor (P, S, N, ~Auts)
   mats := ActionOnFactor (P, S, N, Auts);
   for i in [1..#Auts] do
      Auts[i]`extension := mats[i];
   end for;
end procedure;

/* extend the automorphisms Auts to act on P and return their action on S,
   a characteristic subgroup of P */
ExtendAutomorphisms := function (P, Auts, S)
   if #Auts eq 0 then return Auts; end if;

   p, d := DefiningParameters (P);

   H := Domain (Auts[1]`map);

   /* P has definitions, H doesn't necessarily! */
   if HaspQuotientDefinitions(H) then
      theta_inv := hom < H -> P | [ P.i : i in [1..d] ] : Check := false >;
   else
      assert HaspQuotientDefinitions(P);
      theta_inv := hom < P -> H | [ H.i : i in [1..d] ] : Check := false > ^ -1;
   end if;

   /* extend the automorphisms of H to act on the p-covering group */
   for i in [1..#Auts] do
      alpha := Auts[i]`map;
      beta := hom < P -> P | [ H.i : i in [1..d] ] @ alpha @ theta_inv : Check := false >;
      Auts[i]`map := beta;
      Auts[i]`extension := ActionOnSubgroup (P, S, beta);
   end for;

   return Auts;
end function;

IsIdentityMap := function (theta)
   G := Domain (theta);
   gens := [ G.i : i in [1..Ngens(G)] ];
   return (gens @ theta) eq gens;
end function;

ExtractMatrixGroup := function (Auts)
   gens := [Auts[i]`extension : i in [1..#Auts]];
   if #gens eq 0 then return [], []; end if;
   d := Nrows (Rep (gens));
   F := BaseRing (Parent (Rep (gens)));
   MA := sub < GL(d, F) | gens>;
   index := [Position (gens, MA.i): i in [1..Ngens (MA)]];
   return MA, index;
end function;

ExtractMatrices := function (A)
   return [A[i]`extension : i in [1..#A]];
end function;
