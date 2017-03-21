freeze;

forward ChosenGenerators; 
forward PrimeGenerators; 

import "sl2.m": SL2Basis, IsSL2Basis;
import "large-to-small.m": SmallToLarge;

/* presentation for (P)SL(2, p) from Coxeter and Moser */

PrimePresentation := function (p: Projective := false)
   if not IsPrime (p) then return false; end if;
   F<s, t> := FreeGroup (2);
   if IsOdd(p) then 
      q := quo < F | s^p, t^2 = (s * t)^3 =   
                  ((s^4 * t * s^((p + 1) div 2)) * t)^2>;
      if Projective then q := AddRelation (q, t^2 = 1); end if;
   else
      q := quo <F | s^3, t^2, s^t = s^-1>;
   end if;
   return q;
end function;

/* presentation for (P)SL(2, K) where K is even char 
   and degree at least 2; Todd, PLMS, 1936 */

EvenPresentation := function (q: Natural := false) 
   if not IsPrimePower (q) then return false; end if;
   K := GF (q);
   n := Degree (K);

   if n eq 1 then 
      Q := PrimePresentation (q); 
      return Q, PrimeGenerators (SL(2, q), q: Natural := true); 
   end if;

   e := PrimitiveElement (K);
   p := Characteristic (K);
   A := Eltseq (e^n);
   a := [Integers () ! a : a in A];
   b := [a[n] * a[1]] cat [a[n] * a[i] + a[i - 1]: i in [2..n]];

   F := FreeGroup (n + 2);
   R := F.(n + 1); U := F.(n + 2); 
   S := [F.i : i in [1..n]];
   id := Identity (F);
   Rels := [];
   Append (~Rels, R^((q - 1)) = 1);
   Append (~Rels, U^3 = id);
   Append (~Rels, (U * R)^2 = 1);
   Append (~Rels, (U * S[1])^2 = 1);
   Append (~Rels, S[1]^2 = id);
   for i in [2..n] do
      Append (~Rels, (S[i], S[1]) = id);
   end for;
   Rels cat:= [S[i] = R * S[i - 1] * R^-1: i in [2..n]];
   if n gt 1 then 
      Append (~Rels, R * S[n] * R^-1 = &*[S[i]^a[i]: i in [1..n]]);
   end if;
   Q := quo <F | Rels>;
   return Q, ChosenGenerators (SL(2, q), q: Natural := true);
end function;

/* presentation for (P)SL(2, K) where K is odd char 
   and degree at least 2; Todd, PLMS, vol 11, 1936 */

OddPresentation := function (q: Projective := false, Natural := false)
   if not IsPrimePower (q) then return false; end if;
   K := GF (q);
   n := Degree (K);

   if n eq 1 then 
      Q := PrimePresentation (q: Projective := Projective); 
      return Q, PrimeGenerators (SL(2, q), q: Natural := true); 
   end if;

   e := PrimitiveElement (K);
   p := Characteristic (K);
   A := Eltseq (e^n);
   a := [Integers () ! a : a in A];
   b := [a[n] * a[1]] cat [a[n] * a[i] + a[i - 1]: i in [2..n]];

   F := FreeGroup (n + 3);
   R := F.(n + 1); U := F.(n + 2); Z := F.(n + 3); 
   S := [F.i : i in [1..n]];
   id := Identity (F);
   Rels := [];
   Append (~Rels, R^((q - 1) div 2) = Z);
   Append (~Rels, U^3 = id);
   Append (~Rels, (U * R)^2 = Z);
   Append (~Rels, (U * S[1])^2 = Z);
   Append (~Rels, S[1]^p = id);
   if #S ge 2 then 
      Append (~Rels, S[2]^p = id);
   end if;
   for i in [2..n] do
      Append (~Rels, (S[i], S[1]) = id);
   end for;
   for i in [3..n] do
      Append (~Rels, (S[i], S[2]) = id);
   end for;
   Rels cat:= [S[i] = R * S[i - 2] * R^-1: i in [3..n]];
   if n gt 1 then 
      Append (~Rels, R * S[n - 1] * R^-1 = &*[S[i]^a[i]: i in [1..n]]);
   end if;
   Append (~Rels, R * S[n] * R^-1 = &*[S[i]^b[i]: i in [1..n]]);
   if q mod 4 eq 1 and n ge 2 then 
      Append (~Rels, (S[2] * R * U)^3 = Z);
   end if;
   Append (~Rels, Z^2 = id);
   Rels cat:= [(Z, S[i]) = id: i in [1..Minimum (2, n)]];
   Append (~Rels, (Z, U) = id);
   Append (~Rels, (Z, R) = id);
   if Projective then Append (~Rels, Z = id); end if;
   Q := quo < F | Rels>;
   return Q, ChosenGenerators (SL(2, q), q: Projective := Projective,
                                            Natural := true);
end function;

/* presentation for (P)SL(2, q) */

intrinsic SL2Presentation (q :: RngIntElt : Projective := false) -> GrpFP, SeqEnum
{return presentation for SL(2, q); if Projective is true,
 then return presentation for PSL(2, q); also
 return the corresponding elements of SL(2, q)} 

   if not IsPrimePower (q) then 
      error q, "must be a prime power"; 
   end if;
   if IsOdd (q) then 
      F, gens := OddPresentation (q: Projective := Projective, Natural := true);
   else 
      F, gens := EvenPresentation (q: Natural := true);
   end if;
   return F, gens;
end intrinsic;

/* images for chosen generators for PSL(2, p) in G */

PrimeGenerators := function (G, p: Natural := false) 
   L := SL(2, p);
   if p eq 2 then 
      s := L![1, 1, 1, 0];
   else 
      s := L![1, 0, 1, 1];
   end if;
   t := L![0, 1, -1, 0];
   if not Natural then 
      s := SmallToLarge (G, s);
      t := SmallToLarge (G, t);
   end if;
   return [s, t];
end function;

/* construct images of chosen generators for (P)SL(2, q) in G */
    
ChosenGenerators := function (G, q: Projective := false, Natural := false)
   K := GF(q);
   n := Degree (K);
   if n eq 1 then return PrimeGenerators (G, q: Natural := Natural); end if;

   e := PrimitiveElement (K);
   L := SL(2, K);
   if IsOdd (q) then 
      R := L![e, e^-1, 0, e^-1];
   else
      R := L![e^(q div 2), e^-(q div 2), 0, e^-(q div 2)];
   end if;
   S := [L![1, e^i, 0, 1]: i in [0..n - 1]];
   U := L![0,-1,1,-1];

   if not Natural then 
      S := [SmallToLarge (G, s):  s in S];
      R := SmallToLarge (G, R);
      U := SmallToLarge (G, U);
   end if;

   if IsEven (q) then return S cat [R, U]; end if;

   if Projective then 
      Z := Identity (G);
   else 
      Z := L![-1,0,0,-1];
      if not Natural then 
         Z := SmallToLarge (G, Z);
      end if;
   end if;
   return S cat [R, U, Z];
end function;

intrinsic SatisfiesSL2Presentation (G :: GrpMat, q :: RngIntElt: 
         Generators := [], Projective := false) -> BoolElt 
{Decide if G satisfies the presentation for SL(2, q) 
 given by SL2Presentation or for PSL(2, q) if Projective is true. 
 If elements of G are supplied as 
 the optional Generators, these are assumed to be the images of 
 the generators of the finite presentation; otherwise we require 
 that G is first constructively recognised as (P)SL(2, q) and 
 we now construct the required matrices.}

   if Generators cmpeq [] then 
      B := SL2Basis (G);
      if Type (B) eq BoolElt then error "Must first recognizeSL2"; end if;
      gens := ChosenGenerators (G, q: Projective := Projective);
   else 
      gens := Generators;
   end if;
   Q := SL2Presentation (q: Projective := Projective);
   
   F := BaseRing (G);
   d := Degree (G);  
   tau := hom <Q -> GL(d, F) | gens>;
   R := Relations (Q);
   return forall{r : r in R | IsIdentity (tau (LHS (r) * RHS(r)^-1))};
end intrinsic;
