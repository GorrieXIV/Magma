freeze;

import "aut.m": PartitionSubgroups, MyMinimalSubgroups, MyMaximalSubgroups;
import "misc.m": DescribeChar, DefiningParameters, BubbleSort,
SubspaceToSubgroup, SubgroupToSubspace,  FactorToSubspace, MypCentralSeries;
import "parameters.m": MAXPARTITION, DEGREE, ORDERLIMIT, SMALLORBIT;
import "char-spaces.m": CharSpaces;
import "stab-of-spaces.m": MyStabiliserOfSpaces;

/* M is list of subgroups of G which are contained in
   the c-th term of p-lcs; parts is a partition of these;
   phi: G -> Q; construct subspaces corresponding to
   images of these subgroups of Q; write down preimages
   of these in G, kernel of map is kernel */
ProcessLevel := function (G, Q, phi, parts, M, c, kernel)
   ranks := pRanks (G);
   d := c gt 1 select ranks[c] - ranks[c - 1] else ranks[c];
   p := FactoredOrder (G)[1][1];
   VS := VectorSpace (GF (p), d);

   Spaces := {@ <VS, c> @};
   for i in [1..#parts] do
      part := parts[i];
      C := [DescribeChar (Q, c, phi (M[index])): index in part] cat [kernel];
      Include (~Spaces, <&+C, c>);
      Include (~Spaces, <&meet (C), c>);
   end for;

   return {@ Spaces[i] : i in [2..#Spaces] @};
end function;

/* we know some char subgroups Chars of c-th level of plcs of G;
   finger-print a section of this level to get more; restrict to sections
   of rank in range and do not take section listed in Exclusions */
ExamineLevel := function (G, Chars, c, range: Exclusions := [* *])
   exclusions := Exclusions;

   MAXPARTITIONS := 10;
   C := [* *];

   /* char spaces in level c */
   D := [x[1] : x in Chars | x[2] eq c];
   dims := [Dimension (x): x in D];

   if #dims eq 0 then return C, {@ @}, exclusions; end if;

   p, d := DefiningParameters (G);
   r := pRanks (G);
   rank := c eq 1 select r[1] else r[c] - r[c - 1];
   V := VectorSpace (GF (p), rank);

   BubbleSort (~dims, ~D);

   /* record sections and sort list by increasing dimension */
   sections := [* *]; length := [];
   for i in [1..#dims] do
      for j in [i + 1..#dims] do
         if D[i] subset D[j] then
            sections[#sections + 1] := <D[j], D[i]>;
            length[#length + 1] := Dimension (D[j]) - Dimension (D[i]);
         end if;
      end for;
   end for;
   BubbleSort (~length, ~sections);

   LCS := MypCentralSeries (G, p);
   Q, phi := quo < G | LCS[c + 1]>;

   L := {@ <V, c> @};
   for s in [1..#sections] do
      section := sections[s];
      top := section[1]; bottom := section[2];
      vprint AutomorphismGroup, 2: "Dimension of section is ", length[s];
      B := FactorToSubspace (V, top, bottom);
      T := SubspaceToSubgroup (Q, V, B, c);
      top := SubspaceToSubgroup (Q, V, top, c);
      kernel := bottom;
      bottom := SubspaceToSubgroup (Q, V, bottom, c);

      found := false;
      for l in [1..#exclusions] do
         if exclusions[l] cmpeq <section[1], section[2], c> then
            found := true; break;
         end if;
      end for;
      if found then
         vprint AutomorphismGroup, 2: "Factor in exclusions";
         continue;
      end if;
      bottom := bottom @@ phi;
      if NPCgens (T) in range then
         exclusions[#exclusions + 1] := <section[1], section[2], c>;
         vprint AutomorphismGroup:
              "Fingerprint section of dimension ", NPCgens (T),
           " in level ", c;
         min, points, E := MyMinimalSubgroups (G, T, LCS[c + 1], phi);
         minG := [sub < G | bottom, m >: m in min];
         parts := PartitionSubgroups (G, minG);
         vprint AutomorphismGroup: "# of partitions of minimals is ", #parts;
         C[#C + 1] := <minG, parts>;
         if c gt 1 then
            L join:= ProcessLevel (G, Q, phi, parts, min, c, kernel);
         end if;
         if NPCgens (T) gt 2 then
            max := MyMaximalSubgroups (G, T, LCS[c + 1], phi,
                                       points, Q, c);
            maxG := [sub < G | bottom, m >: m in max];
            partsMax := PartitionSubgroups (G, maxG);
            vprint AutomorphismGroup:
                "# of partitions of maximals is ", #partsMax;
            C[#C + 1] := <maxG, partsMax>;
            if c gt 1 then
               L join:= ProcessLevel (G, Q, phi, partsMax, max, c, kernel);
            end if;
         end if;
         if #C ge MAXPARTITIONS then return C, L, exclusions; end if;
      end if;
   end for;

   return C, L, exclusions;
end function;

/* take preimages of Subs, a partition of subgroups of G,
   in Frattini quotient of G; return resulting spaces,
   and sum and intersection of parts of this partition */
Pullback := function (G, Subs)
   Frat := FrattiniSubgroup (G);
   q, tau := quo < G | Frat >;

   subs := Subs[1]; partition := Subs[2];

   Parts := [* *];
   for part in partition do
      // EOB -- revision April 2011 to store spaces in list
      // otherwise Append fails
      spaces := [* *];
      trivial := false;
      for i in part do
         Q, phi := quo < G | subs[i] >;
         U := UpperCentralSeries (Q);
         class := NilpotencyClass (Q);
         u := U[class];
         u := u @@ phi;
         s := tau (u);
         /* if the spaces are all trivial, go to next part */
         if NPCgens (s) eq 0 then trivial := true; break i; end if;
         Append (~spaces, SubgroupToSubspace (q, s));
      end for;
      // EOB -- revision April 2011 to convert to sequence
      spaces := [x : x in spaces];
      if not trivial then
         Parts[#Parts + 1] := spaces;
      end if;
   end for;

   return Parts, SetToIndexedSet (&join{{<&+part, 1>, <&meet(part), 1>}: part in Parts});
end function;

/* use the intersection fingerprint information to refine the partition */
FurtherRefine := function (Part, invariant)
   invariants := Set (invariant);
   if #invariants eq 0 then return {@ @}; end if;

   space := Part[1];
   F := BaseRing (space); d := Degree (space);
   parent := VectorSpace (F, d);
   spaces := {@ <parent, 1> @};
   for s in invariants do
      part := [Part[i] : i in [1..#invariant] | invariant[i] eq s];
      space := &+part; Include (~spaces, <space, 1>);
      space := &meet(part);
      if Dimension (space) gt 0 then
         Include (~spaces, <space, 1>);
      end if;
   end for;
   return {@ spaces[i] : i in [2..#spaces] @};
end function;

/* partition spaces in Part using intersection and sum fingerprints */

PartitionSpaces := function (Part)
   if #Part eq 0 then return {@ @}; end if;

   id, count, spaces := InternalPartitionPairs (Part);
   assert #count eq #spaces;
   vprint AutomorphismGroup, 2: "Set of pairs ids from Partition is ", Set (id);
   vprint AutomorphismGroup, 2:
        "Set of pairs counts from Partition is ", Set (count);

   new := FurtherRefine (Part, id);
   new join:= FurtherRefine (spaces, count);

   if #new gt 0 or #Part gt MAXPARTITION then return new; end if;

   id, count, spaces := InternalPartitionTriples (Part);
   vprint AutomorphismGroup, 2:
        "Set of triples ids from Partition is ", Set (id);
   vprint AutomorphismGroup, 2:
        "Set of triples counts from Partition is ", Set (count);
   new join:= FurtherRefine (Part, id);
   new join:= FurtherRefine (spaces, count);

   return new;
end function;

/* supply union of characteristic spaces from Chars and new to CharSpaces;
   if we get new spaces at level 1, call MyStabiliserOfSpaces
   to get subgroup of GL (d, p) preserving the list */
procedure NewCharacteristicSpaces (G, ~Chars, new, ~Subgroup, ~found)
   vprint AutomorphismGroup: "Number of spaces in Chars is ", #Chars;
   vprint AutomorphismGroup: "Number of new spaces is ", #new;
   vprint AutomorphismGroup:
        "Number of new spaces in union is ", #(Chars join new);

   found := false;
   if new subset Chars then return; end if;
   LevelOne := {@ c[1] : c in Chars | c[2] eq 1 @};
   Chars := CharSpaces (G : Known := Chars join new);
   D := {@ c[1] : c in Chars | c[2] eq 1 @};
   if LevelOne ne D then
      B, Pgp, order := MyStabiliserOfSpaces (D);
      Subgroup := <B, Pgp, order>;
      found := true;
   end if;
end procedure;

/* order levels of p-central series according to dimension
   of known char spaces in these levels */
SortLevels := function (G, Chars)
   prank := pRanks (G);
   assert #Set (Chars) eq #Chars;

   List := [];
   for i in [1..#prank] do
      rank := i gt 1 select prank[i] - prank[i - 1] else prank[1];
      D := [x[1]: x in Chars | x[2] eq i];
      dims := [Dimension (x): x in D];
      BubbleSort (~dims, ~D);
      ranks := [];
      for j in [1..#D] do
         for k in [j + 1..#D] do
            if D[j] subset D[k] then
               Append (~ranks, Dimension (D[k]) - Dimension(D[j]));
            end if;
         end for;
      end for;
      Sort (~ranks);
      Append (~List, ranks);
   end for;

   vprint AutomorphismGroup:
        "List of dimensions of known sections at each level is ", List;
   index := [1..#prank];
   BubbleSort (~List, ~index);
   return List, index;
end function;

/* fingerprint sections of p-central series of G whose dimensions
   are in Range and which are not in Exclusions */

FingerprintSection := function (G, Chars, Order: Range := [],
                                                 Exclusions := [* *])
   vprint AutomorphismGroup:
       "Number of char spaces on entry to Fingerprint is ", #Chars;

   exclusions := Exclusions;

   p, d := DefiningParameters (G);

   f := function (DEGREE, p)
      return Ilog (p, DEGREE * (p - 1) + 1);
   end function;

   range := #Range eq 0 select [2..f (DEGREE, p)] else Range;
   vprint AutomorphismGroup:
       "Acceptable dimensions for fingerprinting are ", range;

   vprint AutomorphismGroup: "Initial order is ", Order;
   Subgroup := [];

   info, index := SortLevels (G, Chars);

   i := 0;
   while (i lt #index) do

      order := Order;

      i +:= 1;
      best := index[i];
      C, new, exclusions := ExamineLevel (G, Chars, best, range:
                                          Exclusions := exclusions);
      if #new gt 1 then
         /* did we get some new char spaces? */
         NewCharacteristicSpaces (G, ~Chars, new, ~Subgroup, ~found);
         if found then
            order := Subgroup[3];
            vprint AutomorphismGroup, 2: "Order is now ", order;
            vprint AutomorphismGroup: "Reduced order by ", Order div order;
            /* if the remaining subgroup is just a p-group, go home */
            pgroup := #Subgroup[1] eq 0;
            if order lt ORDERLIMIT or pgroup then
               return true, Chars, Subgroup, exclusions;
            end if;
            Order := order;
         end if;
      end if;

      /* refine resulting partition to attempt to
         produce new char subspaces of Frattini factor */

      len := [#C[i][2]: i in [1..#C]];
      BubbleSort (~len, ~C);

      for j in [1..#C] do
         Parts, L := Pullback (G, C[j]);
         vprint AutomorphismGroup, 2:
              "Number of non-trivial parts from Pullback is ", #Parts;
         new join:= L;
         for k in [1..#Parts] do
            vprint AutomorphismGroup, 2: "Size of partition is ", #Parts[k];
            new join:= PartitionSpaces (Parts[k]);

            /* did we get some new char spaces? */
            NewCharacteristicSpaces (G, ~Chars, new, ~Subgroup, ~found);
            if found then
               order := Subgroup[3];
               vprint AutomorphismGroup, 2:
                    "Reduced order by ", Order div order;
               pgroup := #Subgroup[1] eq 0;
               if order lt ORDERLIMIT or pgroup then
                  return true, Chars, Subgroup, exclusions;
               end if;
               Order := order;
            end if;
         end for;
      end for;

   end while;

   /* if we have no other choice, try to fingerprint
      smallest section of p-central series */
   min := Minimum (&cat(info));
   if min gt Maximum (range) then
      return $$ (G, Chars, order: Range := [2..min],
                                  Exclusions := exclusions);
   end if;

   return false, Chars, Subgroup, exclusions;
end function;

/* fingerprint characteristic sections of G */
Fingerprint := function (G, Chars, Order)
   /* remember entry order */
   Initial := Order; exclusions := [* *];

   /* continue fingerprinting until we find nothing new,
      or the remaining subgroup is either small or a p-group */
   repeat
      order := Order;
      Break, Chars, Subgroup, exclusions :=
         FingerprintSection (G, Chars, Order: Exclusions := exclusions);
//      if Break then return true, Chars, Subgroup; end if;
      if #Subgroup gt 0 then
         best := Subgroup;
         Order := Subgroup[3];
      else
         Order := order;
      end if;
   until order div Order lt SMALLORBIT;

   if Initial eq Order then
      vprint AutomorphismGroup: "Failed to reduce order?", true;
      return false, _, _;
   else
      vprint AutomorphismGroup: "Best from Fingerprint is ", best;
      p := FactoredOrder (G)[1][1];
      vprint AutomorphismGroup: "Order of p-group is ", p^#best[2];
      return true, Chars, best;
   end if;
end function;
