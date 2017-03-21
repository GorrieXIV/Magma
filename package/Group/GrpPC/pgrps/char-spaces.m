freeze;

import "stab-of-spaces.m": MyStabiliserOfSpaces;
import "parameters.m": MAXSPACES;
import "misc.m": DefiningParameters, IsFixed;

/* map from V_i to V_{i + 1}  */
PowerMap := function (G, r, i)
   c := pClass (G);
   if i eq c then return false; end if;

   p := FactoredOrder (G)[1][1];

   /* for p = 2, we use powermap  G/P_1(G) -> P_1(G) / DerivedGroup (G) */
/*
   if p eq 2 and i eq 1 then
      D := DerivedGroup (G); r[3] := Depth (G!D.1);
   end if;
*/
   j := i + 1;

   A := [];
   for k in [r[i] + 1..r[i + 1]] do
      w := Eltseq (G.k^p);
      w := [w[l] : l in [r[j] + 1..r[j + 1]]];
      Append (~A, w);
   end for;

   n := #A; m := r[j + 1] - r[j];
   MA := KMatrixSpace (GF (p), n, m);
   return MA! &cat (A);
end function;

/* map from V_i \otimes V_j to V_{i + j} */
CommutatorMap := function (G, r, i, j)
   c := pClass (G);
   if i + j gt c then return false; end if;

   p := FactoredOrder (G)[1][1];

   A := [];
   for k in [r[i] + 1..r[i + 1]] do
      row := [];
      for l in [r[j] + 1..r[j + 1]] do
         w := (G.k, G.l);
         w := Eltseq (w);
         w := [w[m] : m in [r[i + j] + 1..r[i + j + 1]]];
         Append (~row, w);
      end for;
      Append (~A, row);
   end for;

   n := #A[1]; m := #A[1][1];
   MA := KMatrixSpace (GF (p), n, m);
   return [MA! &cat (a) : a in A];
end function;

/* S is a subspace; compute image under p-th power map of S */
PowerImage := function (S, t)
   return S * t;
end function;

/* U subset V; T subset W; compute image of U \otimes W in X
   Replaced with InternalCommutatorImage (C-level).
CommutatorImage := function (A, U, V, T, W, X)

    image := [];
    U := Basis (U);
    T := Basis (T);
    zero := Zero (X);
    BasisX := Basis (X);
    for a in [1..#U] do
       u := Coordinates (V, U[a]);
       for b in [1..#T] do
          t := Coordinates (W, T[b]);
          x := zero;
          for k in [1..#u] do
             for l in [1..#t] do
                temp := A[k][l];
                for m in [1..#BasisX] do
                   x +:= u[k] * t[l] * temp[m] * BasisX[m];
                end for;
             end for;
          end for;
          Append (~image, x);
       end for;
    end for;

    return sub < X | image >;
end function;*/

/* S is a subspace of W; compute preimage of S under linear map t */
LinearPreimage := function (W, S, t)
   Q, phi := quo <W | S>;
   K := KMatrixSpace (BaseRing (W), Degree (W), Degree (Q));
   W := Basis (W);
   M := K ! &cat ([Eltseq (phi (W[i])): i in [1..#W]]);
   return NullSpace (t * M);
end function;

/* U subset V, Y subset X; find W such that U \otimes W subset Y */
CommutatorPreimage := function (G, VS, Maps, i, j, U, V, Y, X)
   if Dimension (U) eq 0 then return sub <VS[j] | >; end if;

   A := Maps[i][j];

   s := [VS[j]];
   U := Basis (U);

   /* From LinearPreImage (don't re-compute all the stuff for the loop!) */
   Q, phi := quo <X | Y>;
   K := KMatrixSpace (BaseRing (X), Degree (X), Degree (Q));
   X := Basis (X);
   M1 := K ! &cat ([Eltseq (X[i] @ phi): i in [1..#X]]);
   /* End from LinearPreImage */

   for i in [1..#U] do
      u := Coordinates (V, U[i]);
      /* Dot product of u with A from 0 to k */
      M := &+[u[k] * A[k] : k in [1..#u]];
      s[i] := NullSpace (M * M1);
   end for;
   return &meet (s);
end function;

GroupDeterminedVectorSpaces := function (G)
   p := FactoredOrder (G)[1][1];
   r := [0] cat pRanks (G);
   r := [r[i+1] - r[i]: i in [1..#r - 1]];
   VS := [VectorSpace (GF (p), r[i]): i in [1..#r]];
   return VS;
end function;

/* determine pre- and images of space under power maps */
ClosePower := function (G, VS, space, powers)
   level := space[2]; space := space[1];
   class := pClass (G);
   images := {@ @};

   p := FactoredOrder (G)[1][1];
   if p eq 2 and level eq 1 then return images; end if;

   if level lt class then
      /* purely because all entries in the image must have a common type */
      images := {@ <VS[level + 1], level + 1> @};
      image := PowerImage (space, powers[level]);
      Include (~images, <image, level + 1>);
   end if;

   if p eq 2 then start := 3; else start := 2; end if;

   if level ge start then
      image := LinearPreimage (VS[level], space, powers[level - 1]);
      Include (~images, <image, level - 1>);
   end if;

   return images;
end function;

/* is the order of stabilising subgroup < MINORDER?
   is stabiliser a unipotent group?
   or has the order remainded fixed for a number of calls?
   in each of these cases, we decide to finish constructing spaces */
FinishConstruction := function (Spaces, Orders)
   MINORDER := 100;

   D := {x[1] : x in Spaces | x[2] eq 1};
   B, P, order := MyStabiliserOfSpaces (D);
   Append (~Orders, order);
   vprint AutomorphismGroup:
        "Order after processing ", #Spaces, "spaces  is ", order;
   return #B eq 0 or (order lt MINORDER) or IsFixed (Orders), Orders;

end function;

/* determine pre- and images of space under commutator maps */
CloseCommutator := function (G, VS, Maps, space, right)
   level := space[2]; space := space[1];
   level2 := right[2]; right := right[1];

   class := pClass (G);
   images := {@ @};

   /* compute space \otimes right */
   if level + level2 le class then
      /* purely because all entries in the image must have a common type */
      images := {@ <VS[level + level2], level + level2> @};
      A := Maps[level][level2];

      image := InternalCommutatorImage (A, space, VS[level], right,
                                   VS[level2], VS[level + level2]);

      Include (~images, <image, level + level2>);
   end if;

   /* find W such that space \otimes W subset right */
   if level2 gt level then
      image := CommutatorPreimage (G, VS, Maps, level, level2 - level, space,
                                   VS[level], right, VS[level2]);
      Include (~images, <image, level2 - level>);
   end if;

   return images;
end function;

CharSubgroupsToSpaces := function (G, Chars)
   p, d := DefiningParameters (G);

   V := VectorSpace (GF (p), d);
   F := FrattiniSubgroup (G);
   Q, phi := quo < G | F >;
   spaces := {@ @};
   for i in [1..#Chars] do
      S := Chars[i] @ phi;
      Include (~spaces,
               <sub <V | [Eltseq (Q ! S.i): i in [1..NPCgens (S)]]>, 1>);
   end for;
   return spaces;
end function;

/* determine characteristic spaces of G under power and commutator maps;
   Known is a list of known characteristic subgroups;
   construct at most Limit spaces;

   be careful - this routine assumes that the pcp supplied was
   constructed by pQuotient; in particular that successive
   generators span terms of the lower p-central series */
CharSpaces := function (G : Known := [], Limit := MAXSPACES)
   VS := GroupDeterminedVectorSpaces (G);
   class := pClass (G);
   p := FactoredOrder (G)[1][1];

   Orders := []; DIV := 100;

   /* initialise */
   spaces := {@ @};
   for i in [1..class] do
      full := VS[i];
      Include (~spaces, <full, i>);
      null := sub <VS[i] | >;
      Include (~spaces, <null, i>);
   end for;

   if #Known gt 0 then
      if Type (Rep (Known)) eq GrpPC then
         initial := CharSubgroupsToSpaces (G, Known);
      elif Type (Rep (Known)) eq Tup then
         initial := Known;
      else
         error "Error in CharSpaces: Known must contain subgroups or subspaces";
      end if;
      spaces join:= initial;
   end if;

   vprint AutomorphismGroup:
        "Initial length of sequence of spaces is ", #spaces;

   r := [0] cat pRanks (G);

   powers := [* *];

   /* for p = 2, we need P_1 / P_2 -> P_2 / gamma_2 */
   if p eq 2 then start := 2; powers[1] := "undefined"; else start := 1; end if;

   /* power maps */
   for i in [start..class - 1] do
      powers[i] := PowerMap (G, r, i);
   end for;

   /* commutator maps */
   Maps := [* *];
   for i in [1..class - 1] do
      Maps[i] := [* *];
      for j in [1..class - 1] do
         if i + j le class then
            Maps[i][j] := CommutatorMap (G, r, i, j);
         end if;
      end for;
   end for;

   procedure CloseUnderPowers (G, VS, ~spaces, powers, start, ~Orders, ~finish)

      i := start; finish := false;
      while (i le #spaces) do
         original := #spaces;
         images := ClosePower (G, VS, spaces[i], powers);
         spaces join:= images;
         i +:= 1;
         if #spaces ge Limit then finish := true; return; end if;
         if #spaces gt original and #spaces mod DIV eq 0 then
            finish, Orders := FinishConstruction (spaces, Orders);
            if finish then return; end if;
         end if;
      end while;

   end procedure;

   procedure CloseUnderCommutators (G, VS, ~spaces, Maps,
                                    start, ~Orders, ~finish)
      i := start; finish := false;
      while (i le #spaces) do
         j := start;
         while (j le #spaces) do
            original := #spaces;
            images := CloseCommutator (G, VS, Maps, spaces[i], spaces[j]);
            spaces join:= images;
            j +:= 1;
            if #spaces ge Limit then finish := true; return; end if;
            if #spaces gt original and #spaces mod DIV eq 0 then
               finish, Orders := FinishConstruction (spaces, Orders);
               if finish then return; end if;
            end if;
         end while;
         i +:= 1;
      end while;

   end procedure;

   power := 1; commutator := 1;
   repeat
      CloseUnderPowers (G, VS, ~spaces, powers, power, ~Orders, ~finish);
      vprint AutomorphismGroup: "After power closure, length is now ", #spaces;
      power := #spaces + 1;
      if finish then return spaces; end if;
      CloseUnderCommutators (G, VS, ~spaces, Maps, commutator,
                             ~Orders, ~finish);
      vprint AutomorphismGroup:
           "After commutator closure, length is now ", #spaces;
      commutator := #spaces + 1;
      if power eq commutator or finish then return spaces; end if;
   until 1 eq 0;

   return spaces;
end function;
