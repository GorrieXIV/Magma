freeze;

//$Id:: gen.m 2745 2014-10-08 01:30:08Z eobr007                              $:

import "../../../basics.m": MyHom, InitialiseGroup, RecognitionError, 
 ClassicalVerify;
import "../../../order.m": MultiplicativeUpperbound, EstimateOrder, 
  GenerateInvolution;
import "../../../is-classical.m": MyIsLinearGroup;
import "../../../section.m": ExtractFactor, ExtractAction, MatrixBlocks;

import "../../../../../recog/magma/node.m": ERROR_RECOGNITION;

/* P parent of G; generating set for derived group of G  */

MyDerivedCentraliser := function (P, G: Limit := 5)
   d := Degree (G);
   F := BaseRing (G);
   gens := [GL(d, F) | Identity (G)];
   U := UserGenerators (G);
   theta := hom <G`SLPGroup -> P`SLPGroup | G`UserWords>;
   words := [Identity (P`SLPGroup)];
   W := G`UserWords; 
   repeat 
      g, w := RandomWord (G);
      for i in [1..#U] do
         c := (U[i], g);
         if not IsIdentity (c) and not (c in gens) then 
            Append (~gens, c);
            Append (~words, (W[i], theta (w)));
         end if;
      end for;
   until #gens ge Limit;

   H := sub <GL(d, F) | gens >;
   H`UserGenerators := gens;
   H`UserWords := words;
   H`SLPGroup := SLPGroup (#gens);
   H`SLPGroupHom := MyHom (H, H`SLPGroup, H`UserGenerators);
   return H;
end function;

/* two representations of G have same dimension;
   are they the same? try to find element of G where char polys on 
   each projection have different factorisations; if so we know they 
   are distinct; if we can't find such an element, we believe they 
   are the same */

DistinctReps := function (G: Limit := 10)
   repeat
      Limit -:= 1;
      g := Random (G);
      blocks := MatrixBlocks (G, g);
      a := blocks[1];
      b := blocks[2];
      different := ProjectiveOrder (a: Proof := false) ne 
                   ProjectiveOrder (b: Proof := false);
   until different or Limit eq 0;
   return different, a, b, g;
end function;

/* g is an element of GL(2, q) wr C2;
   has g got shape [ A  0] ?          
                   [ 0  B]             */

InBaseGroup := function (g)
   
   assert Nrows (g) eq 4;
   b1 := ExtractBlock (g, 1, 1, 2, 2);
   if IsZero (b1) then return false, _, _; end if;
   b2 := ExtractBlock (g, 3, 3, 2, 2);
   if IsZero (b2) then return false, _, _; end if;
   b3 := ExtractBlock (g, 1, 3, 2, 2);
   if not IsZero (b3) then return false, _, _; end if;
   b4 := ExtractBlock (g, 3, 1, 2, 2);
   if not IsZero (b4) then return false, _, _; end if;

   return true, b1, b2;
end function;

/* action of x on two composition factors of group is a and b;
   obtain (estimate of) order of x on second factor 
   and hence kill it off, giving action on first factor;

   if order computations are hard, then we first compute gcd 
   of upper bounds for action on each factor; write 
   bound on order of b as gcd^k * n, where n is coprime
   to order b; now compute order o of b^n; we can now
   take as effective order of g the value gcd * o since this power
   kills b and it doesn't reduce effectiveness of element a 
   produced since powers in o don't occur in order of a */

ObtainActionOnFactor := function (G, x, a, b)
   
   F := BaseRing (G);
   d := Degree (G);
   if Degree (F) lt 10 or d le 30 then
      // "Use strategy 1";
      o := Order (b : Proof := false);
      return a^o, o;
   else 
      // "Use strategy 2";
      // tt := Cputime ();
      bound1 := MultiplicativeUpperbound (a);
      bound2 := MultiplicativeUpperbound (b);
      ell := Gcd (bound1, bound2);
      n := bound2;
      while Gcd (n, ell) ne 1 do n div:= Gcd (n, ell); end while;
      bb := b^n;
      o := Order (bb : Proof := false);
      // "Time to apply strategy 2 is ", Cputime (tt);
      return a^(o), o * n; 
   end if;
end function;

/* Bray elements for centraliser in G of g;
   if order computations are hard, then use multiplicative
   bound only by setting PseudoOrder to true; the elements of 
   the centraliser produced are the same in both cases; however 
   suprisingly there is no visible gain for fields of size 
   GF (p^20) for small primes and d <= 100 */

SpecialGeneratorsWords := function (G, g, wg: fct := Order, 
                                              PseudoOrder := false)

   repeat h, wh := RandomWord (G); until h^2 ne Id (G);

   c := (g, h);

   // t := Cputime ();
   if PseudoOrder then 
      /* c^o is the identity, e is the precise power 
         of 2 diving the order, and o = e * b */
      o, y, e, b := EstimateOrder (c);
   else
      o := fct (c: Proof := false);
   end if;
   // "Time to determine order of centraliser element is ", Cputime (t);

   m := o div 2;
   if IsOdd (o) then 
      return [h * c^m], [wh * (wg, wh)^m];
   elif PseudoOrder then 
      k := e div 2;
      return [y^k, (g, h^-1)^m], [(wg, wh)^m, (wg, wh^-1)^m]; 
   else 
      return [c^m, (g, h^-1)^m], [(wg, wh)^m, (wg, wh^-1)^m]; 
   end if;
end function;

/* apply change of basis matrix COB to G */

ApplyCOB := function (G, CB)
   U := UserGenerators(G);
   U := [CB * U[i] * CB^-1: i in [1..#U]];
   d := Degree (G);
   F := BaseRing (G);
   K := sub <GL(d, F) | U>;
   K`UserGenerators := U;
   K`SLPGroup := G`SLPGroup;
   K`UserWords := G`UserWords;
   K`SLPGroupHom := MyHom (K, K`SLPGroup, U);
   return K;
end function;

/* set up C as a group containing u as generator;
   wu is word for u in generators of H */

RedefineGroup := function (H, C, u, wu)
   U := UserGenerators (C);
   W := C`UserWords;
   S := C`SLPGroup;
   n := Ngens (S);
   d := Degree (C);
   F := BaseRing (C);
   C := sub<GL(d, F) | U, u>;
   U cat:= [u];
   C`UserGenerators := U; 
   C`SLPGroup := SLPGroup (n + 1);
   C`SLPGroupHom := MyHom (C, C`SLPGroup,  U);
   C`UserWords := W cat [wu];
   return C;
end function;

/* produce d x d matrix having X and Y as diagonal submatrices */

CombineMatrices := function (X, Y)
   CB := DiagonalJoin (X, Y);
   return GL(Nrows (CB), BaseRing (Parent (CB))) ! CB;
end function;

/* wg is word in generators of S which are words in generators of P;
   rewrite wg as word in generators of P */

PullbackWord := function (P, S, wg)
   theta := hom <Parent (wg) -> P`SLPGroup | S`UserWords>;
   wg := theta (wg);
   return wg;
end function;

/* CG is subgroup, wu is word in section of CG */

FactorToParent := function (G, CG, wu)
   S1 := Parent (wu);
   S := G`SLPGroup; SC1 := CG`SLPGroup;
   assert Ngens (S1) eq Ngens (SC1);
   /* write wu as word in user-generators of G */
   h := hom <S1 -> SC1 | [SC1.i: i in [1..Ngens (S1)]]>;
   gamma := hom <SC1 -> S | CG`UserWords>;
   h := h * gamma;
   wu := h (wu);
   return wu;
end function;

/* find generator for projective centraliser */

ProjectiveGenerator := function (G, g, wg: Limit := Maximum (100, 5 * Degree (G)))
   nmr := 0;
   repeat 
      repeat h, wh := RandomWord (G); until h^2 ne Identity (G);
      c := (g, h);
      o := ProjectiveOrder (c);
      m := o div 2;
   
      if IsEven (o) then
         e := [c^m, (g, h^-1)^m];
         w := [(wg, wh)^m, (wg, wh^-1)^m];
      else
         e := [h * c^m]; w := [wh * (wg, wh)^m];
      end if;

      if exists(i){i : i in [1..#e] | Order ((g, e[i])) ne 1} then
         vprint User5: "Number of tries to find projective centraliser element", nmr;
         return e[i], w[i];
      end if;
      nmr +:= 1;
   until nmr gt Limit; 
   
   error ERROR_RECOGNITION;
   //error Error (rec<RecognitionError | 
   //      Description := "Constructive recognition for classical group",
   //      Error := "Did not find full projective centraliser">);
end function;

/* kill factor specified by list; construct subgroup of G which has 
   classical action on factors of dimension listed in f; 
   P is parent of G, words are rewritten as words in P  */

GoodCentraliser := function (P, G, desired, list: type := "linear",
   IsCorrectType := MyIsLinearGroup, Words := true, 
   Limit := Maximum (500, 10 * Degree (G))) 

   if #list eq 0 then return G; end if;

   if Type (desired) eq SetEnum then
      desired := SetToSequence (desired);
   end if;

   if Type (desired) eq SeqEnum then 
      Sort (~desired); f := &+desired; 
   else 
      f := desired; desired := [f]; 
   end if;

   d := Degree (G);
   F := BaseRing (G);
   q := #F;
   if type eq "unitary" then q := Isqrt (q); end if;
   action := {1..d} diff list;
   action := Sort (SetToSequence (action));
   assert #action eq f;

   if not Words then P := RandomProcess (G); end if;

   t := Cputime ();
   nmr := 0;
   repeat 
      if Words then 
         g, wg := RandomWord (G);
      else 
         g := Random (P);
      end if;
      a := ExtractAction (g, action);
      b := ExtractAction (g, list);
      a, order := ObtainActionOnFactor (G, g, a, b); 
      nmr +:= 1;
      required := not IsScalar (a);
      if required and q eq 3 then 
         required := not IsPower (Order (a), 2); 
      end if;
   until required or nmr gt Limit;

   if nmr gt Limit then
       error ERROR_RECOGNITION;
      //error Error (rec<RecognitionError | 
      //   Description := "Constructive recognition for classical group",
      //   Error := "Failed to find non-trivial action">);
   end if;
   vprint User5: "Number checked to find non-trivial action = ", nmr;
   vprint User5: "Time taken to get nonscalar action is ", Cputime (t);

   /* we could write down this element */
   g := g^(order);
/* 
   g := Identity (MatrixAlgebra (F, d));
   m := Minimum (action);
   InsertBlock (~g, Minimum (action), 
*/
   A := [a];
   Large := [g];
   if Words then wg := wg^(order); WA := [wg]; end if;

   nmr := 0;
   repeat 
      nmr +:= 1;
      if Words then 
         k, wk := RandomWord (G);
      else 
         k := Random (P);
      end if;
      x := g^k; 
      if x in Large or IsIdentity (x) then flag := false; continue; end if;
      k := ExtractAction (k, action);
      y := k^-1 * a * k;
      if y in A or IsIdentity (y) then flag := false; continue; end if;
      Append (~Large, x);
      Append (~A, y);
      if Words then Append (~WA, wg^wk); end if;
      H := sub <GL(f, F) | A>;
      S := Sections (H);
      vprint User5: "1 # of sections in result is now ", #S;
      flag := #S eq #desired and [Degree (s): s in S] eq desired 
              and forall{s : s in S | IsCorrectType (s)}; 
   until nmr gt Limit or flag;

   if nmr gt Limit then
       error ERROR_RECOGNITION;
      //error Error (rec<RecognitionError | 
      //   Description := "Constructive recognition for classical group",
      //   Error := "Failed to construct factors">);
   end if;
   vprint User5: "Number of conjugates needed to construct factors is ", #A - 1;

   H := sub <GL(d, F) | Large>;

   /* store generators for H as words in P */
   if Words then 
      H`UserGenerators := Large;
      theta := hom <G`SLPGroup -> P`SLPGroup | G`UserWords>;
      WA := [theta (w): w in WA];
      H`UserWords := WA;
      H`SLPGroup := SLPGroup (#A);
      H`SLPGroupHom := MyHom (H, H`SLPGroup, H`UserGenerators);
   end if;

   return H;
end function;

/* g involution in G; wg is corresponding word; construct its centraliser 
   having derived group is SX(f, q) x SX(d - f, q) */

SpecialCentraliser := function (G, g, wg, f: fct := Order, 
   Limit := Maximum (100, 10 * Degree (G)),
   type := "linear",  IsCorrectType := MyIsLinearGroup)

   S := G`SLPGroup;
   F := BaseRing (G);
   d := Degree (G); q := #F;
   E := [[g]]; W := [[wg]];

   i := 2; prev := d;
   repeat 
      E[i], W[i] := SpecialGeneratorsWords (G, g, wg: fct := fct);
      vprint User5: "Lengths are ", [#e: e in E];
      C := sub <GL(d, F) | &cat(E)>;
      S := Sections (C);
      vprint User5: "2 # of sections in result is now ", #S;
      if fct cmpeq ProjectiveOrder then
         flag := #S eq 1 and 
            exists{x : x in Generators (C) | IsIdentity ((g, x)) eq false}; 
      else 
         flag := #S eq 2 and {Degree (s): s in S} eq {f, d - f} and 
            forall{s : s in S | IsCorrectType (s)} and DistinctReps(C); 
      end if;
      if flag and d eq 4 and q eq 3 and f eq 2 then 
         vprint User5: "Special test for dim 2 and field 3";
         prev := #S;  
         RandomSchreier (C);
         if type eq "unitary" then 
            flag := #C eq 2304;
         else 
            flag := #C mod 24^2 eq 0;
         end if;
      elif #S lt prev or flag then 
         prev := #S; 
      end if;
      i +:= 1;
   until flag or i gt Limit;

   if i gt Limit then
      error ERROR_RECOGNITION;
      //error Error (rec<RecognitionError | 
      //   Description := "Constructive recognition for classical group",
      //   Error := "Failed to construct centraliser in SpecialCentraliser">);
   end if;
   vprint User5: "Number of generators for centraliser is", Ngens (C);

   E := &cat(E);
   W := &cat(W);
   C`UserGenerators := E;
   C`UserWords := W;

   B := SLPGroup (#E);
   C`SLPGroup := B;
   C`SLPGroupHom := MyHom (C, B, E);

   return C;
end function;

/* construct centraliser of involution g which is 
   of specified type on Action section */

SecondSpecialCentraliser := function (G, g, wg, Action: 
   IsCorrectType := MyIsLinearGroup, fct := Order)
//   IsCorrectType := MyIsLinearGroup, N := 3, fct := Order)

   S := G`SLPGroup;
   F := BaseRing (G);
   d := Degree (G);
   f := #Action;
   E := [[g]]; W := [[wg]];

   i := 2; prev := d;
   V := VectorSpace (F, d);
   space := sub<V | [V.i : i in Action]>;
   flag := false;
   try 
      repeat 
         E[i], W[i] := SpecialGeneratorsWords (G, g, wg: fct := fct);
         C := sub <GL(d, F) | &cat(E)>;
         M := GModule (C);
         S := Sections (C);
         vprint User5: "# of sections is now ", #S;
         if #S lt prev then i +:= 1; prev := #S; end if;
         U := sub <M | space>;
         if Dimension (U) eq f then 
            S := sub <GL(f, F) | [ActionGenerator (U, j): j in [1..Ngens (C)]]>;
            if IsCorrectType (S) then flag := true; end if;
         end if;
      until flag;
   catch err
       //error ERROR_RECOGNITION;
      error Error(rec<RecognitionError |
         Description := "Constructive recognition for classical group",
         Error := "Failed to construct centraliser in SecondSpecialCentraliser">);
   end try;
   vprint User5: "Number of generators for centraliser is", Ngens (C);

   E := &cat(E);
   W := &cat(W);
   C`UserGenerators := E;
   C`UserWords := W;

   B := SLPGroup (#E);
   C`SLPGroup := B;
   C`SLPGroupHom := MyHom (C, B, E);

   return C;
end function;

/* construct GL2 wr C2 as projective centraliser of 
   involution g = Diagonal ([-1,-1,1,1] in SX(4, q) */

ThirdCentraliser := function (G, g, wg: type := "linear", 
                              IsCorrectType := MyIsLinearGroup)

   S := G`SLPGroup;
   F := BaseRing (G);
   if type eq "unitary" then q := Isqrt (#F); else q := #F; end if;

   d := Degree (G);
   E := [g]; W := [wg];
   found := false; complete := false;

   /* find wreathing element and generators for SL2 x SL2 */
   try 
      repeat 
         X, Y := SpecialGeneratorsWords (G, g, wg: fct := ProjectiveOrder);
         for j in [1..#X] do 
            h := X[j];
            wh := Y[j];
            flag := not InBaseGroup (h); 
            /* record first element found which permutes blocks */
            if flag and not found then 
               found := true; wr := h; word := wh; continue j; 
            /* obtain elements of GL2 x GL2 */
            elif flag and not complete then 
               h := wr * h;
               wh := word * wh;
            end if;
            if not complete and not (h in E) and not IsIdentity (h) then 
               Append (~E, h); Append (~W, wh); 
            end if;
         end for;

         if not complete then 
            H := sub <GL(4, F) | E>;
            S := Sections (H);
            if #S eq 2 and forall{s : s in S | IsCorrectType (s)} then
               U1 := S[1]`UserGenerators;
               U2 := S[2]`UserGenerators;
               complete := [ProjectiveOrder (x): x in U1] ne
                           [ProjectiveOrder (x): x in U2];
               if complete then 
                  if type eq "unitary" then  
                     complete := LCM ([Order (Determinant (x)): x in U1]) eq q + 1; 
                  elif type eq "linear" then 
                     complete := LCM ([Order (Determinant (x)): x in U1]) eq q - 1; 
                  end if;
               end if;
            end if;
         end if;
      until found and complete;
   catch err
       //error ERROR_RECOGNITION;
      error Error(rec<RecognitionError |
         Description := "Constructive recognition for classical group",
         Error := "Failed to construct centraliser in ThirdSpecialCentraliser">);
   end try;

   /* add in wreathing element to generating set */
   Append (~E, wr); Append (~W, word); 
   H := sub <GL(4, F) | E>;
   H`UserGenerators := E;
   H`UserWords := W;
   B := SLPGroup (#E);
   H`SLPGroup := B;
   H`SLPGroupHom := MyHom (H, B, E);

   return H;
end function;

/* find element y of even order 2n such that y^n has
   eigenspaces of dimension f, d - f where each lies in range
   d/3... 2d/3; write G wrt resulting eigenbasis */
 
SplitSpace := function (G : Limit := Maximum (100, 5 * Degree (G)), 
   SortSpaces := true, Range := [Degree(G) div 3..2 * Degree(G) div 3])

   found := false;
   nmr := 0;
   repeat 
      t := Cputime ();
      flag, g, w := GenerateInvolution (G);
      vprint User5: "Time to construct SplitSpace involution is ", Cputime (t);
      if flag then 
         /* ensure that odd is at top, hence we glue only 
            odd - even or even - even */
         U := Eigenspace (g, 1);
         W := Eigenspace (g, -1);
         degs := [Dimension (U), Dimension (W)];
         vprint User5: "Characteristic polynomial factors have degree ", degs;
         found := exists(x){x : x in degs | x in Range};
      end if;
      nmr +:= 1;
   until found or nmr gt Limit;

   if nmr gt Limit then
      error ERROR_RECOGNITION;
      //error Error (rec<RecognitionError | 
      //   Description := "Constructive recognition for classical group",
      //   Error := "Failed to split space">);
   end if;

   vprint User5: "Number of random elements processed to split space is ", nmr;

   d := Degree (G);

   /* if even, ensure large space is at top */
   if SortSpaces and IsEven (d) and Dimension (W) gt Dimension (U) then 
      tmp := U; U := W; W := tmp;
   end if;

   B := [Eltseq (u): u in Basis (U)] cat [Eltseq (u): u in Basis (W)]; 
   B := &cat (B);
   F := BaseRing (G);
   CB := GL (d, F) ! B;
   H := sub <GL(d, F) | [CB * G.i * CB^-1 : i in [1..Ngens (G)]]>;
   b := CB * g * CB^-1;
   return g, w, H, b, CB, Dimension (U), Dimension (W);
end function;

/* G has degree 4k; find involution to split space into I_2k and -I_2k */

SplitInvolution := function (G: Required := Degree (G) div 2, 
                                IsCorrectType := MyIsLinearGroup)

   InitialiseGroup (G);
   d := Degree (G);
   F := BaseRing (G);
   e := Required;

   if (d le 8)  then 
      Range := [Required];
      vprint User1 : "Search for precisely", Range;
   else 
      Range := [d div 3..2 * d div 3];
      vprint User1 : "Search for ", Range;
   end if;

   if not (Required in Range) then
      Range cat:= [Maximum (Range) + 1 ..Required];
      // "Amended -- Search for ", Range;
   end if;

   g, w, H, b, CB, dim, minus := SplitSpace (G: Range := Range, 
                                             SortSpaces := false);
   plus := dim;

   if e eq minus then found := true; return g, w, b, CB; end if;

   H`SLPGroup := G`SLPGroup;
   H`UserGenerators := [CB * x * CB^-1: x in UserGenerators (G)];
   H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));

   C := SpecialCentraliser (H, b, w, dim: IsCorrectType := IsCorrectType);

   MA := MatrixAlgebra (F, d);
   Large := Identity (MA);
   B := Identity (MA);

   pullback := true;

   if e le Minimum ([minus, plus]) then 
      if minus lt plus then 
         C1 := GoodCentraliser (G, C, minus, {1..dim}:
                                IsCorrectType := IsCorrectType); 
         G1 := ExtractFactor (C1, {dim + 1..d});
      else 
         C1 := GoodCentraliser (G, C, plus, {plus + 1..d}:
                               IsCorrectType := IsCorrectType); 
         G1 := ExtractFactor (C1, {1..dim});
      end if;
      g, w, smallb, SmallCB := $$ (G1: Required := e,
                                   IsCorrectType := IsCorrectType); 
      pos := minus lt plus select plus else 0;
      InsertBlock (~Large, SmallCB, pos + 1, pos + 1);
      InsertBlock (~B, smallb, pos + 1, pos + 1);
   elif e gt minus and e le plus then 
      C1 := GoodCentraliser (G, C, plus, {plus + 1..d}:
                             IsCorrectType := IsCorrectType); 
      G1 := ExtractFactor (C1, {1..dim});
      g, w, smallb, SmallCB := $$ (G1: Required := e,
                                   IsCorrectType := IsCorrectType); 
      InsertBlock (~Large, SmallCB, 1, 1);
      InsertBlock (~B, smallb, 1, 1);
   elif e gt plus and e le minus then 
      C1 := GoodCentraliser (G, C, minus, {1..dim}:
                             IsCorrectType := IsCorrectType); 
      G1 := ExtractFactor (C1, {dim + 1..d});
      g, w, smallb, SmallCB := $$ (G1: Required := e,
                                  IsCorrectType := IsCorrectType); 
      InsertBlock (~Large, SmallCB, plus + 1, plus + 1);
      InsertBlock (~B, smallb, plus + 1, plus + 1);
   elif e gt plus and e gt minus then 
      C1 := GoodCentraliser (G, C, plus, {plus + 1..d}:
                             IsCorrectType := IsCorrectType); 
      G1 := ExtractFactor (C1, {1..dim});
      g1, w1, smallb1, SmallCB1 := $$ (G1: 
            Required := e - minus, IsCorrectType := IsCorrectType); 
      /* pull back words to G */
      w1 := FactorToParent (G, C1, w1);
      w := w * w1;
      InsertBlock (~Large, SmallCB1, 1, 1);
      InsertBlock (~B, smallb1, 1, 1);
      CB := Large * CB;
      b := b * B;
      pullback := false;
  else
      //error ERROR_RECOGNITION;
      error Error (rec<RecognitionError | 
         Description := "Constructive recognition for classical group",
         Error := "Problem in SplitInvolution ">);
   end if;
     
   /* pull back words to G */
   if pullback then 
      CB := Large * CB;
      b := B;
      w := FactorToParent (G, C1, w);
   end if;

   return g, w, b, CB;
end function;

/* G has degree 4k; find involution [I_2k, -I_2k] */

SpecialSplitSpace := function (G: IsCorrectType := MyIsLinearGroup)

   g, w, b, cb := SplitInvolution (G : IsCorrectType := IsCorrectType);

   d := Degree (G);
   F := BaseRing (G);

   g := GL(d, F) ! (cb^-1 * b * cb);

   U := Eigenspace (g, 1);
   W := Eigenspace (g, -1);

   /* if even, ensure large space is at top */
   if IsEven (d) and Dimension (W) gt Dimension (U) then 
      tmp := U; U := W; W := tmp;
   end if;

   B := [Eltseq (u): u in Basis (U)] cat [Eltseq (u): u in Basis (W)]; 
   B := &cat (B);
   F := BaseRing (G);
   CB := GL(d, F) ! B;
   H := sub <GL(d, F) | [CB * G.i * CB^-1 : i in [1..Ngens (G)]]>;
   b := CB * g * CB^-1;

   return g, w, H, b, CB, Dimension (U);
end function;

/* element to link first SX to second SX */

GlueElement := function (F)
   M := MatrixAlgebra (F, 4);
   I := Zero (M);
   I[1][3] := 1;
   I[2][4] := 1;
   I[3][1] := 1;
   I[4][2] := 1;
   return GL (4, F)!I;
end function;
