freeze;

import "general.m": JordanDecompositionForGroup, AllCommute, 
                    IsKnownNilpotent, SetVirtualValues;
import "finite.m": MatrixHasFiniteOrder;

/* various algorithms of Detinko & Flannery for nilpotent
   groups defined over finite and infinite fields;
   implementation by Eamonn O'Brien February 2010 */

/* upper bound for class of nilpotent group of degree n defined over K */

ClassLimit := function (n, K)

   if n eq 1 then return 1; end if;

   FiniteFieldBound := function (n, F)
      p := Characteristic (F);
      I := PrimesInInterval (2, n);
      Exclude (~I, p);

      f := [t : t in I | exists{x : x in [1..n] | (#F^x - 1) mod t eq 0}];
      m := 1;
      for t in f do
         s := Valuation (#F - 1, t);
         m := Maximum (m, (t  - 1) * s + 1);
      end for;
      return n * m;
   end function;

   if Type (K) eq FldFin then return FiniteFieldBound (n, K); end if;

   if K cmpeq RationalField () or K cmpeq Integers () then 
      return 3 * n div 2; 
   end if;

   F := CoefficientField (K);

   if ISA(Type(K), FldNum) and 
      (F cmpeq RationalField () or F cmpeq Integers ()) then 
      m := Degree (K);
      return 3 * m * n div 2;
   end if;

   return 1 + $$ (n, F);

end function;

/* write g = s * u where s semisimple, u unipotent */

MyJordanDecomposition := function (g)
   s, u := MultiplicativeJordanDecomposition (g);
   return s, u;

   F := BaseRing (Parent (g));

   if not IsFinite (F) or not IsPrime (#F) then 
      s, u := MultiplicativeJordanDecomposition (g);
      return s, u;
   end if;

   p := Characteristic (F);
   o := Order (g);

   e, q := Valuation (o, p);
   r, a, b := ExtendedGreatestCommonDivisor (p^e, q);
   u := g^(b * q);
   s := g^(a * p^e);
   // assert s * u eq u * s;
   return s, u;
end function;

/* H normal in G; find a non-central element of H which 
   is in the second centre */

SecondCentralElement := function (G, H, l)

   X := [G.i : i in [1..Ngens (G)]];
   Y := [H.i : i in [1..Ngens (H)]];

   found := exists(a){a : a in Y | not IsCentral (H, a)};
   if not found then return false, _; end if;
   
   i := 0; c := 0;
   while i lt #X do 
      i +:= 1;
      b := (X[i], a);
      if not IsCentral (H, b) then 
         a := b; i := 0; c +:= 1;
         if c gt l then return false, _; end if;
      end if;
   end while;

   return true, a;
end function;

/* construct centraliser in G of v */

OrbitStabiliserGenerators := function (G, v)

   X := [G.i : i in [1..Ngens (G)]];
   Y := [x^-1: x in X];
   l := #X;
   orb := {@ v @};
   T := [Generic (G) | Id (G)];
   stab := [Generic (G) | ];
   c := 0;
   while c lt #orb do 
      c +:= 1;
      for i in [1..l] do
         w := Y[i] * orb[c] * X[i];
         j := Position (orb, w);
         if j eq 0 then
            Include (~orb, w);
            Append (~T, T[c] * X[i]);
         else
            s := T[c] * X[i] * T[j]^-1;
            if Order (s) ne 1 then 
               H := sub<Generic (G) | stab>;
               RandomSchreier (H);
               if not s in H then 
                  Append (~stab, s); 
               end if;
            end if;
         end if;
      end for;
   end while;
   U := sub <Generic (G) | stab >;
   return U, #orb;
end function;
   
/* abelian normal series for semisimple group G of class at most l */

AbelianNormalSeries := function (G, l) 

   n := Degree (G);
   F := BaseRing (G);
   p := Characteristic (F);

   C := G;
   S := [* C *]; L := [1];
   c := 0;
   
   while not IsAbelian (C) do
      c +:= 1;
      if c gt n-1 then return false, _, _; end if;
      flag, a := SecondCentralElement (G, C, l);
      if not flag then return false, _, _; end if;
      C, index := OrbitStabiliserGenerators (C, a);
      Append (~S, C); Append (~L, index);
      flag := IsAbelian (C);
      if index mod p eq 0 then return false, _, _; end if;
   end while;

   return true, S, L;
end function;

/* calculate the pi- and pi'- splitting of G,
   where pi is the set of primes in {2..n} */

PiPrimarySplitting := function (G)

   n := Degree (G);
   P := PrimesInInterval (2, n);
   L := [];
   for i in [1..Ngens (G)] do 
      g := G.i;
      o := Order (g);
      x := 1;
      for r in P do 
         if o mod r eq 0 then 
            v := Valuation (o, r);
            x *:= r^v;
         end if;
      end for;
      b := g^(o div x);
      a := g^x;
      Append (~L, <a, b>);
   end for;

   return sub<Generic (G) | [L[i][2]: i in [1..#L]]>,
          sub<Generic (G) | [L[i][1]: i in [1..#L]]>;
end function;

PcGensBySeries := function (G, S)
   A := S[#S];
   U := [Generic (G) | A.i: i in [1..Ngens (A)]];
   for i in [#S - 1 .. 1 by -1] do 
      A := S[i];
      X := [A.j: j in [1..Ngens (A)] | not (A.j in U)];
      U cat:= X;
   end for;
   return U;
end function;

/* P is list of primes; construct powers of g reflecting 
   primes in P and those in P' */

PAndPrimePart := function (g, P)
   o := Order (g);
   a := 1;
   for r in P do 
      if o mod r eq 0 then 
         v := Valuation (o, r);
         a *:= r^v;
      end if;
   end for;
   b := o div a;
   d, x, y := ExtendedGreatestCommonDivisor (a, b);
   return g^(y * b), g^(x * a);
end function;

/* construct Sylow p-subgroup of G, having generators X */

SylowSubgroupOfNilpotentGroup := function (G, X, p)
   Y := [PAndPrimePart (X[i], [p]): i in [1..#X]];
   return sub<Generic (G) | Y>;
end function;

MyIsCentral := function (G, H)
   return forall{h: h in Generators (H) | IsCentral (G, h)};
end function;

/* is G <= GL(n, q) nilpotent? 
   if so, return true; for p <= n, the Sylow p-subgroups of semisimple factor;
   also unipotent subgroup and product of Sylow p-subgroups for p > n;
   if PCPresentation is true, also return pc-presentation for G */

IsNilpotentFFGroup := function (G: PCPresentation := false,
     ClassBound := ClassLimit (Degree (G), BaseRing (G)))

   if Degree (G) eq 1 then return true; end if;


   F := BaseRing (G);
   if not IsFinite (F) then 
      error "Algorithm applies only for finite field"; 
   end if;

   S, U := JordanDecompositionForGroup (G);
   if not AllCommute (S, U) then
      return false, _, _, _;
   end if;
   if not IsUnipotent (U) then 
      return false, _, _, _;
   end if;

   B, C := PiPrimarySplitting (S);
   if not MyIsCentral (S, C) then return false, _, _, _; end if;

   l := ClassBound;
   flag, S, L := AbelianNormalSeries (B, l); 

   if not flag then return false, _, _, _; end if;

   // "Abelian normal series has length ", #S;
   f := Set (&cat([PrimeBasis (x): x in Set (L) | x ne 1]));
   A := S[#S];
   O := {Order (A.i): i in [1..Ngens (A)]};
   y := Set (&cat([PrimeBasis (o): o in O | o ne 1]));
   o := f join y;
   // "B has prime factors ", o;

   n := Degree (G);
   if exists{x : x in o | x gt n} then 
      return false, _, _, _; 
   end if; 

   // compute pcgens by series
   b := PcGensBySeries (B, S);

   // now sylow
   syl := [*  *];
   for q in o do 
      W := SylowSubgroupOfNilpotentGroup (B, b, q);
      for V in syl do
         if not AllCommute (W, V) then return false, _, _, _; end if;
      end for;
      Append (~syl, W);
   end for;

   if PCPresentation then 
      RandomSchreier (U); 
      u := PCGroup (U);
      RandomSchreier (C);
      c := PCGroup (C);
      for s in syl do RandomSchreier (s); end for;
      S := [PCGroup (s): s in syl];
      T := [u, c] cat S;
      P := DirectProduct (T);
      return true, syl, [U, C], P;
   else 
      return true, syl, [U, C], _;
   end if;
end function;

/* construct relations for nilpotent group H 
   as words in word group of H */

ConstructRelations := function (H)

   RandomSchreier (H);
   W, delta := WordGroup (H);
   P, phi := PCGroup (H);
   vprint Infinite: "P has composition length ", 
      NPCgens (P), " order ", FactoredOrder (P);
   F, tau := FPGroup (P);
   gens := [(P.i @@ phi) @@ delta: i in [1..NPCgens (P)]];
   R := Relations (F);
   R := [LHS (r) * RHS (r)^-1: r in R];
   // if Ngens (W) eq 0 then gens := [W.0]; end if;
   if Ngens (W) eq 0 then return []; end if;
   gamma := hom <F->W | gens>;
   words := [gamma (r): r in R];
   return words;
end function;

IsNilpotentGeneral := function (G)

   flag := IsKnownNilpotent (G);
   if flag cmpeq true or flag cmpeq false then
      return flag; 
   end if;

   n := Degree (G);

   F := BaseRing (G);
   l := ClassLimit (n, F);

   if IsFinite (F) then 
      flag := IsNilpotentFFGroup (G: ClassBound := l); 
      return flag;
   end if;

   S, U := JordanDecompositionForGroup (G);

   if not AllCommute (S, U) then return false; end if;
   if not IsUnipotent (U) then return false; end if;
   if IsAbelian (S) then return true; end if;

   H, tau, gensH := CongruenceImage (S);

   /* if congruence image is trivial, then 
      it suffices to check if G is abelian */
   if IsTrivial (H) then 
      flag := IsAbelian (S); 
      SetVirtualValues (G, "Nilpotent", flag); 
      return flag;
   end if;

   index := [Position (gensH, H.i): i in [1..Ngens (H)]];
   gensS := [S.i: i in index];

   flag := IsNilpotentFFGroup (H: ClassBound := l); 
   if not flag then 
      SetVirtualValues (G, "Nilpotent", false); 
      return false; 
   end if;

   /* relations for H */
   words := ConstructRelations (H);

   if #words eq 0 then 
      flag := true; 
   else 
      flag := forall{w : w in words | IsCentral (S, Evaluate (w, gensS))};
   end if;
   SetVirtualValues (G, "Nilpotent", flag); 
   return flag; 
end function;

intrinsic IsNilpotent (G:: GrpMat[FldFin]) -> BoolElt 
{ Given a finite field K and a subgroup G of GL(n, K), return true 
  if G is nilpotent, else false} 

   n := Degree (G);
   F := BaseRing (G);
   l := ClassLimit (n, F);
   return IsNilpotentFFGroup (G: ClassBound := l); 
end intrinsic;

intrinsic IsNilpotent (G:: GrpMat[FldRat]) -> BoolElt 
{ Given the field Q of rational numbers and a subgroup G of GL(n, Q), 
  return true if G is nilpotent, else false} 

   return IsNilpotentGeneral(G);

end intrinsic;

intrinsic IsNilpotent (G:: GrpMat[RngInt]) -> BoolElt
{ Given the ring Z of integers and a subgroup G of GL(n, Z),
  return true if G is nilpotent, else false}

   H := sub<GL(Degree (G), Rationals ()) | [G.i: i in [1..Ngens (G)]]>;
   return IsNilpotentGeneral(H);
end intrinsic;

intrinsic IsNilpotent (G:: GrpMat[FldFunRat]) -> BoolElt 
{ Given a rational function field F and a subgroup G of GL(n, F), 
  return true if G is nilpotent, else false} 

   return IsNilpotentGeneral(G);

end intrinsic;

intrinsic IsNilpotent (G:: GrpMat[FldFun]) -> BoolElt 
{ Given an algebraic function field F and a subgroup G of GL(n, F), 
  return true if G is nilpotent, else false} 

   return IsNilpotentGeneral(G);

end intrinsic;

intrinsic IsNilpotent (G:: GrpMat[FldNum]) -> BoolElt 
{ Given a rational number field F and a subgroup 
  G of GL(n, F), return true if G is nilpotent, else false} 

   return IsNilpotentGeneral(G);

end intrinsic;

/* G is a nilpotent matrix group in char 0; 
   decide if G is finite; if so, return true, else false; 
   if Verify then check that G is nilpotent */

IsFiniteNilpotentMatrixGroup := function (G: Verify := false) 

   F := BaseRing (G);

   if Characteristic (F) ne 0 then 
      error "Defining field must have characteristic zero";
   end if;

   if ISA (Type (F), FldRat) or ISA (Type (F), RngInt) then 
      if exists{i : i in [1..Ngens (G)] | MatrixHasFiniteOrder (G.i) eq false} then 
         return false;
      end if;
   end if;
   
   if Verify then assert IsNilpotent (G); end if;

   S, U := JordanDecompositionForGroup (G);
   if not IsTrivial (U) then return false; end if;

   H, tau, gensH := CongruenceImage  (S);
   index := [Position (gensH, H.i): i in [1..Ngens (H)]];
   gensS := [S.i: i in index];

   /* relations for H */
   words := ConstructRelations (H);

   /* is the kernel non-trivial? */
   return forall{w : w in words | Evaluate (w, gensS) eq Id (S)};
end function;

intrinsic SylowSystem (G :: GrpMat[FldFin]: Verify := false) -> []
{return list of Sylow subgroups of a nilpotent matrix group 
 defined over a finite field, one for each relevant prime; 
 if Verify then check whether G is nilpotent} 

   F := BaseRing (G);
   if not IsFinite (F) then 
      error "Algorithm applies only for finite field"; 
   end if;

   if Verify then
      require IsNilpotent (G): "G must be nilpotent";
   end if;

   p := Characteristic (F);

   S, U := JordanDecompositionForGroup (G);
   B, C := PiPrimarySplitting (S);

   // now G = U x C x B
   // U is p-group, C is abelian 
   gensC := [C.i: i in [1..Ngens (C)]];
   oC := [PrimeBasis(Order (g)): g in gensC];
   oC := Set (&cat (oC));

   gensB := [B.i: i in [1..Ngens (B)]];
   oB := [PrimeBasis (Order (g)): g in gensB];
   oB := Set (&cat (oB));

   o := oC join oB;
   if not IsTrivial (U) then o join:= {p}; end if;

   syl := [];
   for q in o do
      if q eq p then
         Append (~syl, U);
      else
         // join p-subgroup of C and B
         t := [];
         if q in oB then
            W := SylowSubgroupOfNilpotentGroup (B, gensB, q);
            t := [W.i: i in [1..Ngens (W)]];
         end if;
         if q in oC then
            W := SylowSubgroupOfNilpotentGroup (C, gensC, q);
            t cat:= [W.i: i in [1..Ngens (W)]];
         end if;
         W := sub<Generic (G) | t>;
         Append (~syl, W);
      end if;
   end for;
   return syl;
end intrinsic;
