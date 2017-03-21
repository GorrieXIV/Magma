freeze;

import "general.m": MatrixGenerators;
import "attributes.m": RF;

/* construct congruence image for group G defined over rationals;
   if Matrices non-empty then they define G;
   Prime: least characteristic of defining field for congruence image; 
   Selberg: compute Selberg homomorphism;
   Virtual flag used only by call from function field code */

RationalCongruence := function (G: Matrices := [], Selberg := false, 
   Prime := 3, Virtual := false)

   K := BaseRing (G);
   gens := Matrices eq [] select [G.i : i in [1..Ngens (G)]] else Matrices;

   least := Virtual select Maximum (NextPrime (Degree (G)), Prime) else Prime; 

   if ISA (Type(K), FldRat) then 
      X := MatrixGenerators (gens);
      Y := Set (&cat[Eltseq (x): x in X]);
      D := {Denominator (y): y in Y};
      primes := &join ({Set (PrimeBasis (d)): d in D});
      if Selberg then p := least; else p := 2; end if;
      while p in primes do p := NextPrime (p); end while;
   elif ISA (Type(K), RngInt) then 
      if Selberg then p := least; else p := 2; end if;
   else
      error "RationalCongruence: Error in input type"; 
   end if;

   n := Degree (G);
   P := GL (n, p);
   images := [P! x : x in gens];
   H := sub<P | images>;
   tau := hom<Generic (G) -> GL(n, p) | x :-> GL(n, p) ! x>;
   return H, tau, images;
end function;

/* construct congruence image for group G defined over number field;
   if Matrices non-empty then they define G;
   Selberg: compute Selberg homomorphism;
   Prime: least characteristic of defining field for congruence image; 
   Virtual flag used only by call from function field code */
      
NumberFieldCongruence := function (G: Matrices := [], Selberg := false,
   Prime := 3, Virtual := false)

   K := BaseRing (G);
   if not ISA (Type(K), FldNum) then 
      error "NumberFieldCongruence: Error in input type"; 
   end if;

   n := Degree (G);

   if not IsAbsoluteField (K) then 
      vprint Infinite: "Non-simple number field: construct absolute";
      K := AbsoluteField (K);
      G := sub<GL(n, K) | [G.i: i in [1..Ngens (G)]]>;
      Matrices := [GL(n, K) ! x : x in Matrices];
   end if;

   gens := Matrices eq [] select [G.i : i in [1..Ngens (G)]] else Matrices;
   X := MatrixGenerators (gens);
   Y := Set (&cat[Eltseq (x): x in X]);
   Y := &join{Set (Eltseq (y)): y in Y};
   D := {Denominator (y): y in Y};

   w := PrimitiveElement (K);
   f := MinimalPolynomial (w, BaseRing (K));
   k := Degree (f);

   // embed is map from possibly non-simple field to simple field 
   V, embed := VectorSpace (K, BaseRing (K), [w^i: i in [0..k - 1]]);

   C := Coefficients (f);
   denoms := {Denominator (c): c in C};
   D join:= denoms;

   least := Virtual select Maximum (NextPrime (Degree (G)), Prime) else Prime; 
   vprint Infinite: "Lower bound for characteristic of congruence image:", least; 

   primes := &join ({Set (PrimeBasis (d)): d in D});
   if Selberg then 
      if ISA (Type(K), FldCyc) then 
         delta := CyclotomicOrder (K);  
      else
         delta := Discriminant (f);
         if not IsIntegral (delta) then 
            c := LCM (denoms);
            delta := Discriminant (c * f); 
         end if;
         delta := Integers () ! delta;
      end if;
      delta := Set (PrimeBasis (delta));
      primes join:= delta;
      p := least; 
      while (p in primes) do p := NextPrime (p); end while;
      // Selberg alternative: choose p not in primes and p > n * k + 1
      // Virtual only: choose p not in primes and p > n 
   else 
      p := 2; 
      while p in primes do p := NextPrime (p); end while;
   end if;

   c := 1;
   repeat 
      E := GF (p, c);
      P := PolynomialRing (E);
      fbar := P!C;
      flag, root := HasRoot (fbar);
      c +:= 1;
   until flag or c gt k;
   if not flag then error "NumberFieldCongruence: Failed to find root"; end if;
   vprint Infinite: "Polynomial has root over ", E;

   ImageOfMatrix := function (A, embed, root, E)
      n := #Rows (A);
      l := [];
      for j in [1..n] do
        for k in [1..n] do
           U := Eltseq (embed(A[j][k]));
           U := [E!u: u in U];
           value := &+[U[i] * root^(i - 1): i in [1..#U]];
           Append (~l, value);
        end for;
      end for;
      return GL(n, E)!l;
   end function;

   images := [ImageOfMatrix (gens[i], embed, root, E): i in [1..#gens]];
   P := GL(n, E);
   H := sub<P | images>;
   tau := hom<Generic (G) -> P | x :-> ImageOfMatrix (x, embed, root, E)>;
   return H, tau, images;
end function;

/* determine if an n-tuple over F are non-roots for all polynomials in D; 
   F may be a finite field or residue ring;
   if Subfield is a proper subfield of F, then consider only n-tuples 
   where at least one element lies outside the subfield */

GenerateTuples := function (F, n, D: Subfield := [], start := -1)
   V := RSpace (F, n);
   ZV := RSpace (Integers (), n);
   avoid := not (start cmpeq -1);

   for v in V do
      if avoid then 
         if not (v cmpeq start) then continue; end if; 
         if v cmpeq start then avoid := false; continue; end if;
      end if;
      soln := v;
      if Type(F) eq RngIntRes then
         soln := Eltseq (ZV!v);
      else
         soln := Eltseq (soln);
      end if;
      if Subfield cmpne [] and #Subfield lt #F and IsSubfield (Subfield, F) and 
         forall{ x : x in soln | x in Subfield} then 
         continue; 
      end if;
      vprint Infinite: "Process tuple ", soln;
      if #D gt 0 and (Type(Rep (D)) eq RngUPolElt) then
         soln := soln[1];
      end if;
      if forall{mu : mu in D | Evaluate (mu, soln) ne 0} then
         return true, soln, v;
      end if;
   end for;

   return false, _, _;
end function;

/* coefficient field for the function field K must now be F;
   embed n x n matrices in B in an appropriate function field */
   
EmbedInLargerField := function (K, F, B)
   if #B eq 0 then return []; end if;
   m := Rank (K);
   L := FunctionField (F, m);
   tau := hom <K -> L | [L.i: i in [1..m]]>;
   n := #Rows (Rep (B));
   P := MatrixAlgebra(L, n);
   B := [Eltseq (b): b in B];
   B := [[tau (y): y in b]: b in B];
   return [P! x: x in B];
end function;

/* G is subgroup of GL(n, K) where K is a function field defined
   over GF (q); construct congruence image of 
   G over (an extension of) the coefficient field of K;
   if Matrices non-empty then they define G;

   search for non-roots, over n-tuples
   in field extensions of max degree EndDegree over F;

   if start is an element of an R-space of dimension k over a finite field
   where k = Rank (K), then consider as possible admissibles 
   only those elements of this R-space which occur later  
   in Magma's ordering of the elements of this space than start;
   if start = -1, then all elements of the R-space are considered;
   if we extend the field, then we reset value of start to -1;
   start with extension of degree ExtDegree of F;
   these features are used by the IsomorphicCopy function;

   if Algebra is true, then we want a congruence which can be used 
   for finiteness testing using our algebra algorithm; we must choose 
   extensions of the field F of degree not divisible by p
*/

PFFC := function (G: start := -1, Matrices := [], Algebra := false,
   ExtDegree := 1, EndDegree := Maximum (ExtDegree, 10))

   K := BaseRing (G);
   if not ISA (Type(K), FldFunRat) then error "PFFC: Incorrect input"; end if;

   F := BaseRing (K);
   if not ISA (Type(F), FldFin) then error "PFFC: Incorrect input"; end if;

   gens := Matrices eq [] select [G.i : i in [1..Ngens (G)]] else Matrices;
   X := MatrixGenerators (gens);
   Y := Set (&cat[Eltseq (x): x in X]);
   D := {Denominator (y): y in Y};

   n := Degree (G);

   rank := Rank (K); p := Characteristic (F);
   if (start cmpeq -1) then
      deg := ExtDegree;
   else
      E := BaseRing (Parent (start));
      deg := Degree (E) div Degree (F);
      if (Algebra and deg mod p eq 0) then 
         vprint Infinite: "PFFC: degree of extension divisible by char"; 
         deg +:= 1;
         vprint Infinite: "PFFC: degree of extension now ", deg;
      end if;
   end if;
   if deg gt EndDegree + 1 then return false, _, _, _; end if;

   smaller := F;
   repeat
      E := ext <F | deg>;
      vprint Infinite: "Investigate tuples over", E;
      found, soln, v := GenerateTuples (E, rank, D: 
                            Subfield := smaller, start := start);
      if not found then 
         deg +:= 1;
         /* avoid extensions of F of degree divisible by p? */
         if Algebra and deg mod p eq 0 then 
            vprint Infinite: "PFFC: degree of extension divisible by char"; 
            deg +:= 1; 
            vprint Infinite: "PFFC: degree of extension now ", deg;
         end if;
         start := -1;
         // problem in handling subfield 
         // smaller := E; 
      end if;
   until found or deg gt EndDegree;

   if not found then 
      // return false, _, _, _; 
      error "PFFC failed -- retry with larger EndDegree?"; 
   end if;

   gens := EmbedInLargerField (K, E, gens); 
   vprint Infinite: "Image is now defined over ", E;
   if Type (soln) eq FldFinElt then soln := [soln]; end if;
   images := [GL(n, E) ! Evaluate (x, soln): x in gens];
   tau := hom<Generic (G) -> GL(n, E) | x :->  
              Evaluate (EmbedInLargerField (K, E, [x])[1], soln)>;
   return sub <GL(n, E) | images>, tau, images, v; 
end function;

/* construct congruence image for group G defined over function field;
   if Matrices non-empty then they define G;

   Limit: if zero characteristic, then examine n-tuples in quo <Z | Limit>,
   else in extensions of degree at most Limit of base field;
   
   if p > 0 and Algebra is true, then construct congruence which can be used 
   for finiteness testing using our algebra algorithm; we must choose 
   extensions of the field F of degree not divisible by p;

   Selberg: compute Selberg homomorphism;
   Prime: least characteristic of defining field for congruence image; 
   Virtual: construct homomorphism used for virtual testing */

FunctionFieldCongruence := function (G: Matrices := [], Virtual := false,
   Algebra := false, Prime := 3, ExtDegree := 1, 
   Selberg := false, Limit := Maximum (ExtDegree + 1, 10))

   K := BaseRing (G);
   if not ISA (Type(K), FldFunRat) then 
      error "FunctionFieldCongruence: Incorrect input"; end if;

   F := BaseRing (K);

   if ISA (Type(F), FldFin) then 
      if Virtual and Characteristic (F) le Degree (G) then
         error "Cannot construct virtual homomorphism: char is at most degree";
      end if;
      H, tau, images := PFFC (G: Algebra := Algebra, ExtDegree := ExtDegree,
                                 Matrices := Matrices, EndDegree := Limit);
      return H, tau, images;
   end if;

   if ISA (Type(F), RngInt) then F := Rationals (); end if;

   if not ISA (Type(F), FldNum) and not ISA(Type(F), FldRat) then 
      error "FunctionFieldCongruence: Incorrect input"; 
   end if;

   gens := Matrices eq [] select [G.i : i in [1..Ngens (G)]] else Matrices;
   X := MatrixGenerators (gens);
   Y := Set (&cat[Eltseq (x): x in X]);
   D := {Denominator (y): y in Y};

   rank := Rank (K);
   l := 5; Z := Integers (); 
   repeat
      I := quo <Z | l>;
      found, soln := GenerateTuples (I, rank, D);
      l +:= 5;
   until found or l gt Limit;
   if not found then error "FunctionFieldCongruence failed"; end if;

   n := Degree (G);
   P := GL(n, F);
   images := [P ! Evaluate (x, soln): x in gens];
   H := sub<P | images>;

   tau1 := hom<Generic (G) -> P | x :-> Evaluate (x, soln)>;

   if Prime eq 0 then return H, tau1, images; end if;

   if ISA (Type(F), FldNum) then 
      H, tau2, images := NumberFieldCongruence (H: Matrices := images, 
         Prime := Prime, Virtual := Virtual, Selberg := Selberg);
   elif ISA (Type(F), FldRat) then 
      H, tau2, images := RationalCongruence (H: Matrices := images, 
         Prime := Prime, Virtual := Virtual, Selberg := Selberg);
   else 
      error "Error in FunctionFieldCongruence"; 
   end if;

   return H, tau1 * tau2, images;
end function;

AFFImageOfMatrix := function (A, soln, root, E)
   n := #Rows (A);
   l := [];
   for j in [1..n] do
      for k in [1..n] do
         U := Eltseq (A[j][k]);
         U := [Evaluate (u, soln): u in U];
         value := &+[U[i] * root^(i - 1): i in [1..#U]];
         Append (~l, value);
      end for;
   end for;
   return GL(n, E)!l;
end function;

/* construct congruence image for group G defined over 
   algebraic function field in positive characteristic; 
   if Matrices non-empty then they define G */

PAFFC := function (G: start := -1, Matrices := [], 
   ExtDegree := 1, EndDegree := Maximum (ExtDegree, 10))

   L := BaseRing (G);
   if not ISA (Type(L), FldFun) then error "PAFFC: Incorrect input"; end if;

   if not IsSimple (L) then 
      vprint Infinite: "Non-simple algebraic function field: construct absolute"; 
      L := RationalExtensionRepresentation(L);
      G := sub<GL(Degree (G), L) | [Eltseq (G.i):i in [1..Ngens (G)]]>;
   end if;

   K := BaseRing (L);
   if not ISA (Type(K), FldFunRat) then error "PAFFC: Incorrect input"; end if;

   F := BaseRing (K);
   if not ISA (Type(F), FldFin) then error "PAFFC: Incorrect input"; end if;

   gens := Matrices eq [] select [G.i : i in [1..Ngens (G)]] else Matrices;
   X := MatrixGenerators (gens);
   Y := Set (&cat[Eltseq (x): x in X]);
   Y := &join{Set (Eltseq (y)): y in Y};
   D := {Denominator (y): y in Y};

   f<t> := MinimalPolynomial (L.1, K);
   C := Coefficients (f);
   D join:= {Denominator (c): c in C};

   rank := Rank (K);
   vprint Infinite: "PAFFC: Rank of function field is ", rank;
   p := Characteristic (L);
   if (start cmpeq -1) then
      deg := ExtDegree;
   else
      E1 := BaseRing (Parent (start));
      deg := Degree (E1) div Degree (F);
      if deg mod p eq 0 then
         vprintf Infinite: 
            "PAFFC: Degree %o of extension is divisible by %o\n", deg, p;
         deg +:= 1;
         vprint Infinite: "PAFFC: Degree of extension is now ", deg;
      end if;
   end if;

   smaller := F;
   repeat
      E1 := ext <F | deg>;
      vprint Infinite: "Investigate tuples over", E1;
      found, soln, v := GenerateTuples (E1, rank, D: 
                            Subfield := smaller, start := start);
      if not found then 
         deg +:= 1;
         if deg mod p eq 0 then
             vprintf Infinite: "PAFFC: Degree %o of extension is divisible by %o\n", deg, p;
            deg +:= 1;
            vprint Infinite: "PAFFC: Degree of extension is now ", deg;
         end if;
         // problem with subfield 
         // smaller := E1; 
         start := -1;
      end if;
   until found or deg gt EndDegree;

   if not found then 
      error "PAFFC failed -- retry with larger EndDegree?"; 
   end if;

   C := [Evaluate (u, soln): u in C];
   k := Degree (f);
   c := 1;
   repeat 
      E := ext<E1 | c>;
      P := PolynomialRing (E);
      fbar := P!C;
      flag, root := HasRoot (fbar);
      c +:= 1;
   until flag or c gt k;
   if not flag then 
      error "AlgebraicFunctionFieldCongruence: Failed to find root"; 
   end if;

   vprint Infinite: "Polynomial has root over ", E;

   n := Degree (G);
   images := [AFFImageOfMatrix (gens[i], soln, root, E): i in [1..#gens]];
   P := GL(n, E);
   H := sub<P | images>;
   tau := hom<Generic (G) -> P | x :-> AFFImageOfMatrix (x, soln, root, E)>;

   return H, tau, images, v;
end function;

/* construct congruence image for group G defined over algebraic function field;
   if Matrices non-empty then they define G;

   Limit: if zero characteristic, then examine n-tuples in quo <Z | Limit>,
   else in extensions of degree at most Limit of base field;

   Prime: least characteristic of defining field for congruence image; 
   Selberg: compute Selberg homomorphism;
   Virtual: construct homomorphism used for virtual testing */

AlgebraicFunctionFieldCongruence := function (G: Matrices := [], 
   ExtDegree := 1, Prime := 3, Virtual := false, Selberg := false, 
   Limit := Maximum (ExtDegree + 1, 10))

   L := BaseRing (G);
   if not ISA (Type(L), FldFun) then 
      error "AlgebraicFunctionFieldCongruence: Incorrect input"; 
   end if;

   K := BaseRing (L);
   if not ISA (Type(K), FldFunRat) then 
      error "AlgebraicFunctionFieldCongruence: Incorrect input"; 
   end if;

   F := BaseRing (K);

   if ISA (Type(F), FldFin) then 
      if Virtual and Characteristic (F) le Degree (G) then
         error "Cannot construct virtual homomorphism: characteristic is at most degree";
      end if;
      H, tau, images := PAFFC (G: Matrices := Matrices, 
         ExtDegree := ExtDegree, EndDegree := Limit);
      return H, tau, images;
   end if;

   if ISA (Type(F), RngInt) then F := Rationals (); end if;

   if not ISA (Type(F), FldNum) and not ISA(Type(F), FldRat) then 
      error "AlgebraicFunctionFieldCongruence: Incorrect input"; 
   end if;

   gens := Matrices eq [] select [G.i : i in [1..Ngens (G)]] else Matrices;
   X := MatrixGenerators (gens);
   Y := Set (&cat[Eltseq (x): x in X]);
   Y := &join{Set (Eltseq (y)): y in Y};
   D := {Denominator (y): y in Y};

   f<t> := MinimalPolynomial (L.1, K);
   k := Degree (f);
   C := Coefficients (f);
   D join:= {Denominator (c): c in C};

   rank := Rank (K);
   vprint Infinite: "Rank of function field is ", rank;
   l := 5; Z := Integers (); 
   repeat
      I := quo <Z | l>;
      found, soln := GenerateTuples (I, rank, D);
      l +:= 5;
   until found or l gt Limit;
   if not found then error "AlgebraicFunctionFieldCongruence failed"; end if;

   E := PolynomialRing (F); t := E.1;
   C := [Evaluate (u, soln): u in C];
   fbar := E!C;
   flag, root := HasRoot (fbar);
   if flag then
      E := F;
   else 
      E := NumberField (fbar);
      root := E.1;
   end if;

   n := Degree (G);
   images := [AFFImageOfMatrix (gens[i], soln, root, E): i in [1..#gens]];
   P := GL(n, E);
   H := sub<P | images>;

   tau1 := hom<Generic (G) -> P | x :-> AFFImageOfMatrix (x, soln, root, E)>;

   if Prime eq 0 then return H, tau1, images; end if;

   if ISA (Type(E), FldNum) then 
      H, tau2, images := NumberFieldCongruence (H:  Prime := Prime,
         Virtual := Virtual, Matrices := images, Selberg := Selberg);
   elif ISA (Type(E), FldRat) then 
      H, tau2, images := RationalCongruence (H: Prime := Prime, 
         Virtual := Virtual, Matrices := images, Selberg := Selberg);
   else 
      error "Problem in AlgebraicFunctionFieldCongruence"; 
   end if;

   return H, tau1 * tau2, images;
end function;

IsValidInput := function (G)
  K := BaseRing (G);
  return (ISA (Type(K), FldRat) or ISA (Type(K), RngInt) or 
         ISA (Type(K), FldNum) or ISA (Type(K), FldFunRat) or 
         ISA (Type(K), FldFun)); 
end function;

/* Virtual, Selberg, Isomorphism are true / false to indicate computed maps */

procedure SetMapTypes (G, Virtual, Selberg, Isomorphism)
   G`Congruence`Virtual := Virtual;
   G`Congruence`Selberg := Selberg;
   G`Congruence`Isomorphism := Isomorphism;
end procedure;

/* Virtual and Selberg are true / false to indicated desired maps;
   have we previously constructed these? */

KnowDesiredMap := function (G, Virtual, Selberg)
   if not assigned G`Congruence then return false; end if;
   if not assigned G`Congruence`Map then return false; end if;
   if not assigned G`Congruence`Image then return false; end if;
   Data := G`Congruence;
   if not assigned Data`Isomorphism or not assigned Data`Selberg
      or not assigned Data`Virtual then return false; end if;
   if Data`Isomorphism eq true then return true; end if;
   if Data`Virtual and (Virtual or Selberg) then return true; end if;
   if Data`Selberg and (Selberg and not Virtual) then return true; end if;
   return (not Virtual and not Selberg) and assigned G`Congruence`Map; 
end function;

/* construct congruence image H of G;
   return H, homomorphism from H to G, and images of generators of G;
   Selberg: construct Selberg congruence;
   Virtual: construct Virtual congruence; 
   Prime: applies to input defined over char 0 only;
          if positive, then lower bound for characteristic of image or 
          if 0 then construct char 0 congruence image;
   Algebra: construct a congruence which can be used for finiteness testing 
            using algebra algorithm; 
  ExtDegree: if G defined over (rational) function field of 
         positive char, then attempt to construct congruence image 
         over extension of this degree of coefficient field; 
   Limit: degree of field extensions to consider in positive char
          or examine tuples in residue ring mod Limit in char 0
*/

MyCongruenceImage := function (G: Selberg := true, Prime := 3, 
    ExtDegree := 1, Algebra := false, Virtual := false, 
    Limit := Maximum (ExtDegree, 10))

   if (Prime lt 0) or not (IsPrime (Prime) or Prime eq 0) then 
      error "CongruenceImage: Prime must be prime"; 
   end if;
   
   if not IsValidInput (G) then 
      error "CongruenceImage: incorrect input"; 
   end if;

   /* Selberg must be set to true if Virtual is true */
   if Virtual then Selberg := true; end if;

   K := BaseRing (G);
   p := Characteristic (K);
   if p gt 0 then Prime := p; end if;

   /* have we already computed data? */
   if KnowDesiredMap (G, Virtual, Selberg) then 
      H := G`Congruence`Image;
      // particular extension required? 
      ext := ((ISA (Type(K), FldFunRat) or ISA (Type(K), FldFun)) 
                  and ExtDegree gt 1);
      if Prime eq Characteristic (BaseRing (H)) and not ext then 
         tau := G`Congruence`Map;
         images := [tau (G.i): i in [1..Ngens (G)]];
         vprint Infinite: "Defining field for congruence image is ", BaseRing (H);
         return H, tau, images;
      end if;
   end if;

   if ISA (Type(K), FldRat) or ISA (Type(K), RngInt) then 
      H, tau, images := RationalCongruence (G: Selberg := Selberg, 
                        Prime := Maximum (Prime, 3));
      if Selberg then Virtual := true; end if;
      G`Congruence := rec<RF | Map := tau, Image := H>;
      SetMapTypes (G, Virtual, Selberg, false);
      vprint Infinite: "Defining field for congruence image is ", BaseRing (H);
      return H, tau, images;
   end if;

   if ISA (Type(K), FldNum) then 
      H, tau, images := NumberFieldCongruence (G: Selberg := Selberg, 
                                               Prime := Maximum (Prime, 3));
      if Selberg then Virtual := true; end if;
      G`Congruence := rec<RF | Map := tau, Image := H>;
      SetMapTypes (G, Virtual, Selberg, false);
      vprint Infinite: "Defining field for congruence image is ", BaseRing (H);
      return H, tau, images;
   end if;

   if ISA (Type(K), FldFunRat) then 
      F := BaseRing (K);
      if ISA (Type(F), FldFin) or ISA (Type(F), RngInt) or  
         ISA (Type(F), FldNum) or ISA (Type(F), FldRat) then 
         H, tau, images := FunctionFieldCongruence (G: Virtual := Virtual,
         ExtDegree := ExtDegree, Algebra := Algebra, 
         Prime := Prime, Selberg := Selberg, Limit := Limit); 
         G`Congruence := rec<RF | Map := tau, Image := H>;
         SetMapTypes (G, Virtual, Selberg, false);
         vprint Infinite: "Defining field for congruence image is ", BaseRing (H);
         return H, tau, images;
      end if;
   end if;

   if ISA (Type(K), FldFun) then 
      L := BaseRing (K);
      if ISA (Type(L), FldFunRat) then 
         F := BaseRing (L);
         if ISA (Type(F), FldFin) or ISA (Type(F), RngInt) or 
            ISA (Type(F), FldNum) or ISA (Type(F), FldRat) then 
            H, tau, images := AlgebraicFunctionFieldCongruence (G: 
               Prime := Prime, Virtual := Virtual, Selberg := Selberg, 
               ExtDegree := ExtDegree, Limit := Limit);  
            G`Congruence := rec<RF | Map := tau, Image := H>;
            SetMapTypes (G, Virtual, Selberg, false);
            vprint Infinite: "Defining field for congruence image is ", BaseRing (H);
            return H, tau, images;
         end if; 
      end if;
   end if;

   error "CongruenceImage: Input type incorrect";
end function;
   
intrinsic CongruenceImage (G :: GrpMat: Prime := 3, ExtDegree := 1, 
   Virtual := false, Limit := Maximum (10, ExtDegree)) -> GrpMat, HomGrp, []
{ construct congruence image H of G;
  return H, homomorphism from G to H, and images of generators of G;
  Virtual: construct Virtual congruence; 
  Prime: applies to input defined over char 0 only;
         if positive, then lower bound for characteristic of image or 
         if 0 then construct char 0 congruence image;
  ExtDegree: if G defined over (rational) function field of 
         positive char, then attempt to construct congruence image 
         over extension of this degree of coefficient field; 
  Limit: degree of field extensions to consider in positive char
         or examine tuples in residue ring mod Limit in char 0
}
   return MyCongruenceImage (G: Prime := Prime, 
      ExtDegree := ExtDegree, Virtual := Virtual, Limit := Limit);
end intrinsic;
