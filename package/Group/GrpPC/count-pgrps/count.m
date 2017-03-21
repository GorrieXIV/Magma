freeze;

/* original implementation by Eamonn O'Brien 1998;
   revision by Michael Vaughan-Lee Dec 2011 to use types of elements to count */

import "backtrack.m": ClassLength, ClassRep, BackTrack;
import "auto.m": MatrixToAuto; 

declare verbose ClassTwo, 1;

FACTOR := 10000;

IsValidInput := function (p, d)

   if not IsPrime (p) then
      error "ClassTwo: Argument 1 (", p ,") is not a prime";
   end if;

   if d lt 1 then 
      error "ClassTwo: Argument 2 (", d ,") must be at least 1";
   end if;

   return true;

end function;

/* rank of p-multiplicator */

RankOfMultiplicator := function (d, p, Exponent)

   /* rank of p-multiplicator */
   if Exponent eq true then 
      m := p eq 2 select 0 else Binomial (d, 2);  
   else 
      m := Binomial (d, 2) + d; 
   end if;

   return m;

end function;

/* MRV-L's function to find the type of a matrix */
FindType := function(g)
   f :=PrimaryInvariantFactors(g);
   pfs := {f[i][1] : i in [1..#f]};
   type :={* *};
   for pf in pfs do
     party := [];
     for i in [1..#f] do
       if f[i][1] ne pf then continue; end if;
       Append (~party, f[i][2]);
     end for;
     Sort (~party);
     Insert (~party, 1, Degree(pf));
     Include (~type, party);
   end for;
   return type;
end function;


/* Count p-class 2 d-generator groups whose step size is in Step; 
   if Exponent is true, count those groups which have exponent p */

BasicCount := function (d, p, Step, Nmr, m: Exponent := false) 

   //MRV-L XXXXX
   //Arrays to store the types that arise, the number of times each
   //type arises, and the NumberOfFixedSpace information for each type
   types:={@ @};
   numtypes:=[];
   numfixspaces:=[];
   //MRV-L ZZZZZ

   Enforce := Exponent;

   F := FreeGroup (d);

   if Exponent eq true then
      P := pQuotientProcess (F, p, 1 : Exponent := p);
   else
      P := pQuotientProcess (F, p, 1);
   end if;

   G := ExtractGroup (P);

   pCoveringGroup (~P);

   /* count only groups of exponent p */
   if Exponent eq true then
      ExponentLaw (~P);
      EliminateRedundancy (~P);
   end if;

   H := ExtractGroup (P);

   /* if prime is 2 and exponent enforced, then H = G */
   if #H eq #G then return []; end if;

   gl := GL (d, p);
   order := OrderGL (d, p);

   F := BaseRing (gl);

   /* irreducible monic polynomials of degree at most d - 1 */
   Poly := &join[AllIrreduciblePolynomials (F, k) : k in [1..d - 1]];
   Poly := SetToSequence (Poly);  
   Sort (~Poly);

   /* which linear combinations of the degrees sum up to d? */ 
   Degrees := [Degree (poly): poly in Poly];
   M := [d div Degrees[i] : i in [1..#Poly]];
   t := Cputime ();

   /* companion matrices for each polynomial */
   Comp := [* *];
   for i in [1..#Poly] do
      Comp[i] := CompanionMatrix (Poly[i]);
   end for; 

   /* p-multiplicator */
   S := sub <H | [H.i: i in [d + 1..NPCgens (H)]]>;

   t := Cputime ();

   /* required partitions */
   Parts := [Partitions (delta) : delta in [0..d]];
   Reps := []; NmrElts := 0; NmrReps := 0;

   theta_inv := hom < G -> H | [ H.i : i in [1..d] ] : Check := false >;
   q := NPCgens (S); Agl := GL (q, p); 

   /* for each class rep, determine the number of fixed spaces */
   nn := #M;
   lenm := nn + 1;
   delta := [0 : i in [1..lenm]];
   M[lenm] := 0;
   Degrees[lenm] := 0;

   x := 0;
   repeat 
      index := 1;
      delta[index] +:= 1;
      x +:= Degrees[index];
      while (index le nn and (delta[index] gt M[index] or x gt d)) do
         x -:= delta[index] * Degrees[index];
         delta[index] := 0;
         index +:= 1;
         delta[index] +:= 1;
         x +:= Degrees[index];
      end while;

      if x eq d then 

         IndexList := [i : i in [1..#delta] | delta[i] gt 0];
         Gamma := [Parts [delta[i] + 1] : i in IndexList]; 
         nmr := [#Gamma[i]: i in [1..#Gamma]]; 
         P := [Poly[i] : i in IndexList];
         C := [* *]; for i in IndexList do Append (~C, Comp[i]); end for;

         L := BackTrack (nmr);
         Gamma := [[Gamma[i][L[j][i]]: i in [1..#L[j]]]: j in [1..#L]];

         for gamma in Gamma do
            R := ClassRep (gl, C, gamma);
            if Determinant (R) ne 0 then 
               NmrReps +:= 1;
               if NmrReps mod FACTOR eq 0 then 
                  vprintf ClassTwo: "Processing rep %o\n", NmrReps;
               end if;
               len := order div ClassLength (P, p, gamma);
               NmrElts +:= len;
   
               /* extend automorphism of G to act on the p-covering group H */
               alpha := MatrixToAuto (G, gl!R);
               beta := hom < H -> H | [ alpha[i] : i in [1..d] ] @ theta_inv : Check := false >;
               A := Agl ! &cat[Eltseq (S!(beta (S.i))): i in [1..q]];
               //MRV-L XXXXX
               tt := FindType (A);
               tti := Position (types, tt);
               if tti ne 0 then 
                  numtypes[tti] +:= len;
               else 
                  Include(~types, tt);
                  Append(~numtypes, len);
                  temp := [];
                  for s in Step do
                     // printf "s = %o m = %o\n", s, m;
                     temp[s] := NumberOfFixedSpaces (A, s);
                  end for;
                  Append(~numfixspaces, temp);
               end if;
               //MRV-L ZZZZZ
            end if;
         end for;

      end if;
   until (index gt nn);

   /* now deal with polynomials of degree d */
   P := SetToSequence (AllIrreduciblePolynomials (F, d));

   for i in [1..#P] do
      gamma := [[1]];
      C := CompanionMatrix (P[i]);
      R := ClassRep (gl, [C], gamma);
      if Determinant (R) ne 0 then 
         NmrReps +:= 1;
         if NmrReps mod FACTOR eq 0 then 
            vprintf ClassTwo: "Processing rep %o\n", NmrReps;
         end if;
         len := order div ClassLength ([P[i]], p, gamma);
         NmrElts +:= len;
         alpha := MatrixToAuto (G, gl!R);
         beta := hom < H -> H | [ alpha[i] : i in [1..d] ] @ theta_inv : Check := false >;
         A := Agl ! &cat[Eltseq (S!(beta (S.i))): i in [1..q]];
         //MRV-L XXXXX
         tt := FindType (A);
         tti := Position (types, tt);
         if tti ne 0 then 
            numtypes[tti] +:= len;
         else 
            Include(~types,tt);
            Append(~numtypes,len);
            temp := [];
            for s in Step do
                // printf "s = %o m = %o\n", s, m;
                temp[s] := NumberOfFixedSpaces (A, s);
            end for;
            Append(~numfixspaces, temp);
         end if;
         //MRV-L ZZZZZ
      end if;
   end for;
      
   assert NmrElts eq order;

   //MRV-L XXXXX
   for i in [1..#types] do
      len := numtypes[i];
      temp := numfixspaces[i];
      for s in Step do
         Nmr[s]  +:= len*temp[s];
         Nmr[m-s] := Nmr[s];
      end for;
   end for;
   //MRV-L ZZZZZ

   for i in [1..#Nmr] do
      if IsDefined (Nmr, i) then Nmr[i] := Nmr[i] div order; end if;
   end for;
   
   return Nmr;

end function;

intrinsic ClassTwo (p::RngIntElt, d::RngIntElt, s::RngIntElt :
                      Exponent := false) -> RngIntElt
{Count all p-class 2 d-generator groups of order p^(d + s); 
 if Exponent is true, count those groups which have exponent p}

   valid := IsValidInput (p, d);

   if s le 0 then return 0; end if;

   /* rank of p-multiplicator */
   m := RankOfMultiplicator (d, p, Exponent);
   if m eq 0 then return 0; end if;

   if s eq m then return 1; end if;

   if s gt m then return 0; end if;

   if (s gt m div 2) then s := m - s; end if;

   Step := [s]; Nmr := []; Nmr[s] := 0; 
   vprint ClassTwo: "Step is ", Step;

   return BasicCount (d, p, Step, Nmr, m: Exponent := Exponent)[s];

end intrinsic;

intrinsic ClassTwo (p::RngIntElt, d::RngIntElt, Step:: SeqEnum:
                    Exponent := false) -> SeqEnum
{Count all p-class 2 d-generator groups of order p^(d + s) for s in Step; 
 if Exponent is true, count those groups which have exponent p}

   valid := IsValidInput (p, d);

   /* rank of p-multiplicator */
   m := RankOfMultiplicator (d, p, Exponent);
   if m eq 0 then return []; end if;

   /* what step sizes do we consider? */
   Sort (~Step);

   order := OrderGL (d, p);
   Nmr := []; if m in Step then Nmr[m] := order; end if;
   Step := [x : x in Step | x gt 0 and x lt m];
   i := 1;
   while (i le #Step) do
      x := Step[i]; y := m - x;
      if x in Step and y in Step and x ne y then
         Exclude (~Step, y);
      end if;
      i +:= 1;
   end while;
   for i in Step do Nmr[i] := 0; end for;

   vprint ClassTwo: "Step sizes to consider: ", Step;
   if Step eq [] then return []; end if;

   return BasicCount (d, p, Step, Nmr, m: Exponent := Exponent);

end intrinsic;

intrinsic ClassTwo (p::RngIntElt, d::RngIntElt: Exponent := false) -> SeqEnum
{Count all p-class 2 d-generator groups; if Exponent is true, 
 count those groups which have exponent p}

   valid := IsValidInput (p, d);

   /* rank of p-multiplicator */
   m := RankOfMultiplicator (d, p, Exponent);
   if m eq 0 then return []; end if;

   order := OrderGL (d, p);
   Nmr := []; Nmr[m] := order; 
   Step := [1..m div 2];
   for i in [1..m - 1] do Nmr[i] := 0; end for;
   vprint ClassTwo: "Step sizes to consider is ", Step;

   return BasicCount (d, p, Step, Nmr, m: Exponent := Exponent);

end intrinsic;
