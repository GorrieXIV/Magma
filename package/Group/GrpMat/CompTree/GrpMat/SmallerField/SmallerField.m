freeze;

import "g-h.m": GHLowerFieldTest;

/* decide whether G <= GL(d, K) has an equivalent representation 
   possibly modulo scalars over some subfield F of K. 
   return representation over smallest such subfield.  
   Originally prepared by Eamonn O'Brien, Octover 2004; 
   revised May 2006 to allow call to Glasby-Howlett via Algorithm;
   backtrack procedure revised October 2008 */

declare verbose SmallerField, 1;

forward MainSmallerField, ScalarList; 

QualityLimit := 5;

/* normal generating set for derived group of G */
 
MyDerivedSubgroup := function (G: NumberOfElements := 5)
 
   if Type (G) eq GrpRandProc then 
      P := G; G := Parent (Random (P));
   else 
      P := RandomProcess (G: Scramble := QualityLimit);
   end if;

   d := Degree (G);
   F := BaseRing (G);
   gens := {};
   n := Ngens (G);
   Limit := Minimum (2 * n, n + 10);
   nmr := 0;
   repeat
      nmr +:= 1;
      x := Random (P);
      gens join:= {(G.i, x): i in [1..Ngens (G)]};
   until nmr ge NumberOfElements or #gens ge Limit;
   return sub <GL (d, F) | gens>, P;
end function;

/* construct random F-linear combination of group algebra M;
   P is group or random process for the group */

AlgebraRandomElement := function (MA, F, P: Length := 4)
   RanElt := function (F);
      repeat x := Random (F); until x ne 0;
      return x;
   end function;
   B := [MA ! Random (P): i in [1..Length]];
   L := [RanElt (F): i in [1..#B]];
   return &+[L[i] * B[i]: i in [1..#B]];
end function;

TestAlgebraElements := function (H, F: NumberRandom := 5)
   d := Degree (H);
   K := BaseRing (H);
   P := RandomProcess (H: Scramble := QualityLimit);
   M := MatrixAlgebra (K, d);
   nmr := 0;
   repeat
      nmr +:= 1;
      // x := AlgebraRandomElement (M, F, P);
      x := Random (P);
      t := Trace (x);
      if t ne 0 then 
         if not (t in F) then return false; end if;
      else 
         cp := CharacteristicPolynomial (x);
         coeffs := Coefficients (cp);
         // "coeffs of Algebra element are ", coeffs;
         if exists{x : x in coeffs | not (x in F)} then
            vprint SmallerField: "Characteristic polynomial of element ", nmr, 
            "has coefficients in larger field";
            return false;
         end if;
      end if;
   until nmr gt NumberRandom;
   return true;
end function;

/* do random elements of H have non-zero trace or
   char poly with all coefficients lying in F? */

TestRandomElements := function (H, F: NumberRandom := 5)
   P := RandomProcess (H: Scramble := QualityLimit);
   nmr := 0;
   repeat
      nmr +:= 1;
      // x := AlgebraRandomElement (M, F, P);
      x := Random (P);
      t := Trace (x);
      if t ne 0 then 
         // "non-zero trace";
         if not (t in F) then return false; end if;
      else
         // "zero trace";
         cp := CharacteristicPolynomial (x);
         coeffs := Coefficients (cp);
         // "coeffs of element are ", coeffs;
         if exists{x : x in coeffs | not (x in F)} then
            vprint SmallerField: "Characteristic polynomial of element ", nmr, 
            "has coefficients in larger field";
            return false;
         end if;
      end if;
   until nmr ge NumberRandom;
   return true;
end function;

/* identify those scalars alpha where alpha * g is over subfield F */

IdentifyScalar := function (g, F) 

   G := Parent (g);
   d := Degree (G);
   K := BaseRing (G);

   f := CharacteristicPolynomial (g);
   C := Coefficients (f);
   Reverse (~C);
   Exclude (~C, 1);
   coeffs := [C[i]: i in [1..#C] | C[i] ne 0];
   I := [i: i in [1..#C] | C[i] ne 0];
   s, u := XGCD (I cat [#K - 1]);

   /* alpha^(#K - 1) = 1 so we can ignore u[#u] */
   theta := &*[coeffs[i]^u[i]: i in [1..#I]];
   theta := theta^-1;

   /* reps for F^* / (F^*)^s */
   M, phi := MultiplicativeGroup (F);
   q, tau := quo < M | s * M.1 >;
   reps := [x @@ tau @ phi : x in q];

   R := &cat[AllRoots (theta * r, s): r in reps];

   /* which scalars give char polys with coefficients 
      over smaller field? */
   possible := [];
   vprint SmallerField: "Number of possible scalars without filtering is ", #R;

   for r in R do 
      s := ScalarMatrix (d, r);
      t := s * g;
      cp := CharacteristicPolynomial (t);
      coeffs := Coefficients (cp);
      if forall {x : x in coeffs | x in F} then
         Append (~possible, r); 
      end if; 
   end for;
   vprint SmallerField: "Number of possible scalars is ", #possible;
   if #possible gt 0 then return possible; else return false; end if;
end function;

/* identify possible compatible scalars in F for 
   each element of gens */

ScalarList := function (gens, F) 
   Alpha := [];
   for i in [1..#gens] do
      alpha := IdentifyScalar (gens[i], F);
      if Type (alpha) eq BoolElt then return false; end if;
      Alpha[i] := alpha;
   end for;
   return Alpha;
end function;

/* get set of random  elements for G which generate an 
   absolutely irreducible subgroup */

ChangeGeneratingSet := function (G, P) 
   d := Degree (G);
   K := BaseRing (G);
   n := Ngens (G);
   gens := [];
   repeat 
      Append (~gens, Random (P));
      H := sub <GL(d, K) | gens>;
      found := IsAbsolutelyIrreducible (H);
   until found or #gens gt n - 1; 

   vprint SmallerField: "Found absolutely irreducible subgroup?", found;
   if found then 
      vprint SmallerField: "Ngens is now ", Ngens (H);
      return [H.i: i in [1..Ngens (H)]], P;
   else 
      return [G.i: i in [1..Ngens (G)]], P;
   end if;

end function;

/* does G have a representation modulo scalars 
   over a subfield of degree Deg */

ModScalarsTest := function (G, Deg: Algorithm := "GLO")

   vprint SmallerField: "Test mod scalars for degree ", Deg;

// G:Magma;

   /* avoid changing generating set */
   GeneratorLimit := Infinity ();
   if Ngens (G) gt GeneratorLimit then 
      P := RandomProcess (G);
      gens, P := ChangeGeneratingSet (G, P);
   else
      gens := [G.i : i in [1..Ngens (G)]];
   end if;
      
   K := BaseRing (G);
   p := Characteristic (K);
   F := GF (p^Deg);
// added to address Derek's report re handling of non-standard fields 
Embed (F, K);

   Alpha := ScalarList ([gens[i] : i in [1..#gens]], F);
   if Type (Alpha) eq BoolElt then return false, _; end if;

   /* number of potential scalars for each generator */
   Len := [#alpha: alpha in Alpha];
   vprint SmallerField: "Number of possible scalars for generators is ", Len;

   /* if scalars choice is unique, we perform base test and finish */ 
   d := Degree (G);
   if &*Len eq 1 then 
      H := sub<GL(d, K) | 
              [gens[i] * ScalarMatrix (d, Alpha[i][1]): i in [1..#Alpha]]>;
      if assigned G`SmallerFieldChangeOfBasis then 
         H`SmallerFieldChangeOfBasis := G`SmallerFieldChangeOfBasis;
      end if;
      flag, X := MainSmallerField (H, {Deg} : Scalars := false, 
		                              Algorithm := Algorithm);
      if flag then 
         X`SmallerFieldChangeOfBasis := H`SmallerFieldChangeOfBasis;
         vprint SmallerField: "Degree = ", Deg, " found from input group"; 
         return flag, X; 
      end if;
      return false, _;
   end if;

   good := [i : i in [1..#gens] | #Alpha[i] eq 1];
   bad := [gens[i] : i in [1..#gens] | #Alpha[i] gt 1];
   vprint SmallerField: "Number of generators with undetermined scalars is ", #bad;
   new := [gens[i] * ScalarMatrix (d, Alpha[i][1]): i in good];

   /* add those modified generators having unique solution to D */
   D, P := MyDerivedSubgroup (G);
   D := sub <GL(d, K) | D, new>;

   /* is image of g defined over smaller field? */
   IsImageInSmallerField := function (G, g)
      CB := SmallerFieldBasis (G);
      F := SmallerField (G);
      d := Degree (G);
      K := BaseRing (G);
      CB := GL (d, K) ! Eltseq (CB);
      g := g^CB;
      E := Eltseq (g);
      v := VectorSpace (K, d^2) ! E;
      depth := Depth (v);
      if depth eq 0 then error "Matrix is zero"; end if;
      alpha := v[depth];
      S := ScalarMatrix (d, alpha^-1);
      I := GL(d, K) ! (g * S);
      flag := forall {x : x in Eltseq (I) | x in F}; 
      if flag then return true, GL (d, F) ! I; else return false, _; end if;
   end function;

   /* does SmallerField extend from D to G? */
   ExtendsToGroup := function (G, D, F)
      gens := [];
      for i in [1..Ngens (G)] do 
         flag, x := IsImageInSmallerField (D, G.i);
         if not flag then return false, _; end if;
         Append (~gens, x);
      end for;
      CB := SmallerFieldBasis (G);
      P := Parent (CB);
      H := sub<GL(Degree (G), F) | gens>;
      H`SmallerField := F;
      H`SmallerFieldChangeOfBasis := CB * P ! D`SmallerFieldChangeOfBasis;
      return true, H;
   end function;

   /* if D is absolutely irreducible, we decide if D had 
      a representation over the smaller field; if so, since the
      space is unique, we have a unique solution 
      which either extends to G or not */

   TestAISubgroup := function (G, D)
      D`SmallerFieldChangeOfBasis := Identity (GL (d, K));  
      flag, X := MainSmallerField (D, {Deg} : Scalars := false);
      if flag then 
         vprint SmallerField: "Absolutely irreducible subgroup over field of degree", Deg;
         flag, X := ExtendsToGroup (G, D, F); 
         if flag then 
            vprint SmallerField: "Degree ", Deg, 
               "found from absolutely irreducible subgroup"; 
            return flag, X; 
         else 
            vprint SmallerField: 
               "Cannot extend from absolutely irreducible subgroup to group";
            return false, _; 
         end if;
      else
         return false, _;
      end if;
   end function;

   /* now consider subgroup having unique scalars */
   if IsAbsolutelyIrreducible (D) then 
      return TestAISubgroup (G, D); 
   end if;
      
   /* D does not act absolutely irreducibly */
   vprint SmallerField: "Subgroup having unique scalars does not act absolutely irreducibly";

   Gens := [gens[i] : i in [1..#gens] | #Alpha[i] gt 1];
   Alpha := [Alpha[i] : i in [1..#gens] | #Alpha[i] gt 1];
   vprint SmallerField: "Number of possible scalars is now ", 
                         &*[#alpha: alpha in Alpha];

   /* backtrack procedure to construct absolutely irreducible
      subgroup having correct scalars; L is list of visited nodes; 
      i, j identify current node */

   procedure VisitNode (~gens, ~L, i, j, ~found, ~X)
      vprint SmallerField: "In Backtrack visit node i j = ", i, j;
      g := Gens[i];
      h := g * ScalarMatrix (d, Alpha[i][j]);
      H := sub <GL (d, K) | gens, h>;

      if IsAbsolutelyIrreducible (H) then 
         flag, Y := TestAISubgroup (G, H);
         vprint SmallerField: "Outcome of Test 1 is", flag; 
         if flag then X := Y; found := true; return; end if;
      else
         flag := TestRandomElements (H, F: NumberRandom := 10);
         vprint SmallerField: "Outcome of Test 2 is", flag; 
      end if;

      if flag then
         Append (~L, [i, j]);
         Append (~gens, h); 
         if i eq #Gens then
            return;
         else
            $$ (~gens, ~L, i + 1, 1, ~found, ~X);
         end if;
      elif j lt #Alpha[i] then
         $$ (~gens, ~L, i, j + 1, ~found, ~X);
      else
         flag := false;
         while #L gt 0 and not found do 
            node := L[#L];
            Prune (~L);
            Prune (~gens);
            flag := node[2] lt #Alpha[node[1]]; 
         end while;
         if flag then 
            $$ (~gens, ~L, node[1], node[2] + 1, ~found, ~X);
         else 
            return; 
         end if;
      end if;
   end procedure;

   L := []; found := false; X := G;
   gens := [Generic (D)! D.i: i in [1..Ngens (D)]];
   VisitNode (~gens, ~L, 1, 1, ~found, ~X);

   return found, X; 

end function;

/* construct a linearly independent basis consisting of 
   images of v under G; this is the so-called Spin algorithm */ 

Spin := function (G, v)

   return SpinOrbit (v, [G.i: i in [1..Ngens (G)]]);
 
   d := Degree(G);
   V := VectorSpace (BaseRing (G), d);
   O := {@ V! v @}; 
   S := sub< V | O>;

   k := 1; DIV := 10;
   /* construct the orbit */
   while k le #O do
      pt := O[k];
      for i in [1..Ngens (G)] do
         /* compute the image of a point */
         im := pt * G.i;
         /* add new element to orbit if linearly independent */
         if not (im in S) then 
            Include (~O, im);
            S := sub< V | S, im>;
             if #O mod DIV eq 0 then 
                vprint SmallerField: "Length of orbit is ", #O;  
             end if;
         end if;
         if #O eq d then return O; end if;
      end for;
      k +:= 1;
   end while;
   return O;
end function;

InSmallerField := function (gens, F)
   return forall{g : g in gens | forall{x : x in Set (Eltseq (g)) | x in F}};
end function;

/* decide if G can be written over F = GF (p^d) */

LowerFieldTest := function (G, d : NumberRandom := 20) 

   vprint SmallerField: "Test SmallerField for degree ", d;
   K := BaseRing (G);
   n := Degree (G);

   p := Characteristic (K);
   F := sub <K | d>;

   M := MatrixAlgebra (K, Degree (G));
   P := RandomProcess (G: Scramble := QualityLimit);
   SF := PolynomialRing (F);
   nmr := 0; 
   repeat 
      x := AlgebraRandomElement (M, F, P: Length := 4 + 2 * nmr);
      cp := CharacteristicPolynomial (x);
      coeffs := Coefficients (cp);
      if forall {x : x in coeffs | x in F} then
         facs := Factorisation (SF!cp);
         degs := [<Degree (f[1]), f[2]>: f in facs];
         nmr +:= 1;
         found := <1,1> in degs; 
      else
         vprint SmallerField: "Coefficients of characteristic polynomial not over smaller field";
         return false, _; 
      end if;
   until found or nmr gt NumberRandom;

   if not found then 
      error "Should find an element with eigenspace of dimension 1"; 
   end if;

   vprint SmallerField: "Number of tries to find element with eigenspace of rank 1 = ", nmr;
   // vprint SmallerField: "Time to get good random element is ", Cputime (t);

   CB := G`SmallerFieldChangeOfBasis;
   P := Parent (CB);
   pos := Position (degs, <1,1>);
   fac := facs[pos];
   R := Roots (fac[1]);
   r := R[1][1];
   E := Eigenspace (x, r);
   vprint SmallerField: "Now spin eigenspace to construct basis";
   S := Spin (G, E.1);
   if #S lt Degree(G) then
	error "Group is reducible";
   end if;
   A := M!&cat[Eltseq (s): s in S];
   Am1 := A^-1;
   gens := [A * G.i * Am1: i in [1..Ngens (G)]];
   if InSmallerField (gens, F) then
      H := sub<GL(Degree (G), F) | gens>;
      H`SmallerField := F;
      H`SmallerFieldChangeOfBasis := CB * P ! Am1;
      return true, H;
   else
      return false, _;
   end if;
end function;

/* can G be written (modulo Scalars) over one of the subfields whose
   degree is listed in divse? if so, rewrite G */

procedure ProcessSubfields (~G, ~divse: Scalars := true, Algorithm := "GLO")

   if divse eq {} then return; end if;

   /* process list of divisors in order of magnitude:
      my experience is that coming down list is usually
      more efficient */
/* 
   divs := [x : x in divse];
   Sort (~divs);
   for d in divs do 
      if Scalars then 
         flag, tmp := ModScalarsTest (G, d: Algorithm := Algorithm);
      else 
         if Algorithm eq "GLO" then 
            flag, tmp := LowerFieldTest (G, d);
	 elif Algorithm eq "GH" then 
            flag, tmp := GHLowerFieldTest (G, d);
	 end if; 
      end if;
      if flag eq true then 
         G := tmp;
	 return;
      end if;
   end for;  

   return; 
*/

   /* move down the list of divisors */
   repeat 
      d := Maximum (divse);
      if Scalars then 
         flag, tmp := ModScalarsTest (G, d: Algorithm := Algorithm);
      else 
         if Algorithm eq "GLO" then 
            flag, tmp := LowerFieldTest (G, d);
	 elif Algorithm eq "GH" then 
            flag, tmp := GHLowerFieldTest (G, d);
	 end if; 
      end if;
      if flag eq false then 
         divse diff:= Set (Divisors (d));
      else 
         G := tmp;
         divse := divse meet Set (Exclude (Divisors (d), d));
         $$ (~G, ~divse: Scalars := Scalars, Algorithm := Algorithm); 
         return;
      end if;
   until #divse eq 0;
         
end procedure;

MainSmallerField := function (G, divse: Scalars := true, Algorithm := "GLO")

   K := BaseRing (G);
   H := G;
   ProcessSubfields (~H, ~divse: Scalars := Scalars, Algorithm := Algorithm);
   F := BaseRing (H);
   if #F ne #K then 
      G`SmallerField := BaseRing (H); 
      G`SmallerFieldChangeOfBasis := H`SmallerFieldChangeOfBasis;  
      return true, H;
   end if;
   if assigned G`SmallerFieldChangeOfBasis then
      delete G`SmallerFieldChangeOfBasis;
   end if;
   return false, _;
end function;

intrinsic IsOverSmallerField (G::GrpMat: Scalars := false, Algorithm := "GLO") 
	  -> BoolElt, GrpMat 
{Does absolutely irreducible group G have an equivalent representation 
 (modulo scalars if Scalars is true) over a subfield? 
 If so, return true and equivalent representation.
 For non-scalar case, use either default 
 Glasby / Leedham-Green / O'Brien algorithm (GLO) or 
 Glasby / Howlett algorithm (GH).} 
/* 
   if Type (SmallerField (G)) eq FldFin then 
      return true, SmallerFieldImage (G); 
   end if;
*/
   require IsAbsolutelyIrreducible (G): "Group must be absolutely irreducible";
   require IsTrivial (G) eq false: "Group is trivial";
   if Scalars eq true then
      require Degree (G) gt 1: "Group must have degree at least 2";
   end if;

   K := BaseRing (G);
   e := Degree (K);
   n := Degree (G);
   divse := Set (Exclude (Divisors (e), e));
   G`SmallerFieldChangeOfBasis := Identity (GL (n, K));  
   return MainSmallerField (G, divse: Scalars := Scalars, Algorithm := Algorithm);

end intrinsic;

intrinsic IsOverSmallerField (G :: GrpMat, k :: RngIntElt : 
          Scalars := false, Algorithm := "GLO") -> BoolElt, GrpMat 
{Does absolutely irreducible group G have an equivalent representation 
 (modulo scalars if Scalars is true) over a subfield of degree k?  
 If so, return true and equivalent representation.
 For non-scalar case, use either default 
 Glasby / Leedham-Green / O'Brien algorithm (GLO) 
 or Glasby / Howlett algorithm (GH).} 

/* 
   F := SmallerField (G)); 
   if Type (F) eq FldFin and #F eq Characteristic (F)^k then 
      return true, SmallerFieldImage (G); 
   end if;
*/
   require IsTrivial (G) eq false: "Group is trivial";
   if Scalars eq true then
      require Degree (G) gt 1: "Group must have degree at least 2";
   end if;

   K := BaseRing (G);
   e := Degree (K);
   if not k in [1..e - 1] or e mod k ne 0 then return false, _; end if;

   require IsAbsolutelyIrreducible (G): "Group must be absolutely irreducible";
   n := Degree (G);
   G`SmallerFieldChangeOfBasis := Identity (GL (n, K));  
   return MainSmallerField (G, {k}: Scalars := Scalars, Algorithm := Algorithm);

end intrinsic;

intrinsic SmallerFieldBasis (G::GrpMat) -> GrpMatElt 
{Return change of basis matrix for G so that G (possibly mod scalars)
 can be written over a smaller field}

   if assigned G`SmallerFieldChangeOfBasis then 
      return G`SmallerFieldChangeOfBasis;
   else 
      return "unknown";
   end if; 
end intrinsic;

intrinsic SmallerField (G::GrpMat) -> FldFin  
{Return smaller field over which G (possibly mod scalars) can be written} 
   if assigned G`SmallerField then 
      return G`SmallerField;
   else 
      return "unknown";
   end if;
end intrinsic;

intrinsic SmallerFieldImage (G :: GrpMat, g :: GrpMatElt) -> GrpMatElt 
{G can be rewritten (possibly mod scalars) over smaller field;
 return image of g in group defined over smaller field} 

   CB := SmallerFieldBasis (G);
   if Type (CB) ne GrpMatElt then 
      error "No smaller field change of basis known"; 
   end if;
   F := SmallerField (G);
   d := Degree (G);
   K := BaseRing (G);
   CB := GL (d, K) ! Eltseq (CB);
   g := g^CB;
   if InSmallerField ([g], F) then return GL(d, F) ! (g), 1; end if;
   E := Eltseq (g);
   v := VectorSpace (K, d^2) ! E;
   depth := Depth (v);
   if depth eq 0 then error "Matrix is zero"; end if;
   alpha := v[depth];
   S := ScalarMatrix (d, alpha^-1);
   // assert IsScalar (g * GL(d, K) ! h^-1);
   // return GL(d, F) ! (g * S), alpha; 
   if InSmallerField ([g * S], F) then
      return GL(d, F) ! (g * S), alpha;
   else
      return false, _;
   end if;
end intrinsic;
