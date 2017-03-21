freeze;
import "subgroups.m": Nsubs, DecreasingSequence, CompareSequences;

FindSolutions := function (D, M, Degrees)

// print "# of polys is ", #M;
   n := #M;
   lenm := n + 1;
   m := [0 : i in [1..lenm]];
   M[lenm] := 0;
   Degrees[lenm] := 0;

   x := 0;
   Solns := [];

   repeat 
      index := 1;
      m[index] +:= 1;
      x +:= Degrees[index];
      while (index le n and (m[index] gt M[index] or x gt D)) do
         x -:= m[index] * Degrees[index];
         m[index] := 0;
         index +:= 1;
         m[index] +:= 1;
         x +:= Degrees[index];
      end while;
      if x eq D then Append (~Solns, Prune (m)); end if; 
   until (index gt n);

   return Solns;

end function;

CountFixed := function (p, d, M, Degrees, V) 

   Delta := FindSolutions (d, M, Degrees);
   powers := [p^x : x in [1..Maximum (Set (Degrees))]];
   total := Set (&cat (Delta));
   if total eq {} then return 0; end if;
   Parts := [Partitions (i) : i in [1..Maximum (total)]];

   total := 0;
   for delta in Delta do
      product := 1;
      for i in [1..#delta] do
         if delta[i] eq 0 then continue; end if;
         q := powers[Degrees[i]];
         Gamma := Parts [delta[i]];
         Gamma := [gamma : gamma in Gamma | CompareSequences (V[i], gamma)];
         sum := &+[Nsubs (q, V[i], gamma) : gamma in Gamma];
         product *:= sum;
      end for;
      total +:= product;
   end for;

   return total;

end function;

DataForFixedSpaces := function (g)

   CP := CharacteristicPolynomial (g);

   facs := Factorisation (CP);

   /* degrees of factors */
   Degrees := [Degree (facs[i][1]): i in [1..#facs]];

   /* multiplicities of factors */
   M := [facs[i][2]: i in [1..#facs]];

   _, _, R := PrimaryRationalForm (g);

   /* work out all of the Vs */
   V := []; 
   for fac in facs do
      f := fac[1]; 
      v := [0: j in [1..fac[2]]];
      for i in [1..#R] do
         if f eq R[i][1] then 
            v[R[i][2]] +:= 1;
         end if;
      end for;
      v := DecreasingSequence (v);
      Append (~V, v);
   end for;

   return <M, Degrees, V>;

end function;

/* return number of subspaces of dimension s fixed by g */

MyNumberOfFixedSpaces := function (g, s)
   ans := DataForFixedSpaces (g);
   M := ans[1]; Degrees := ans[2]; V := ans[3];
   p := Characteristic (BaseRing (Parent (g)));
   deg := Degree (g); if s gt deg div 2 then s := deg - s; end if;
   return CountFixed (p, s, M, Degrees, V);
end function;

intrinsic NumberOfFixedSpaces (g::GrpMatElt, s::RngIntElt) -> RngIntElt 
{Return number of subspaces of dimension s fixed by g}
   
   requirerange s, 0, Nrows (g);
   return MyNumberOfFixedSpaces (g, s);

end intrinsic;

intrinsic NumberOfFixedSpaces (g::AlgMatElt, s::RngIntElt) -> RngIntElt 
{Return number of subspaces of dimension s fixed by g}

   requirerange s, 0, Nrows (g);
   return MyNumberOfFixedSpaces (g, s);

end intrinsic;
