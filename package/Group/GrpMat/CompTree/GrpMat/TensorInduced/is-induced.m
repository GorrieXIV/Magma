freeze;

/* latest version of tensor induction code October 2008 */

declare verbose TensorInduced, 1;

// SetVerbose ("Tensor", 1);
// SetVerbose ("SubmoduleLattice", 1);
// SetVerbose ("STCS", 1);

import "../Smash/functions.m": SetTensorInducedFlag, 
SetTensorInducedImageBasis, SetTensorInducedBasis, 
SetTensorInducedPermutations, TensorInducedImageBasis, 
TensorInducedFactors, TensorInducedFlag;

import "../Smash/induced.m": SymmetricTensorAction;
import "../Smash/random.m": RandomElement;
import "../Smash/numbers.m": FactorList;
import "../Tensor/is-projectivity.m": IsProjectivity;
import "../Tensor/find-point.m": GeneralFindPoint;
import "../Tensor/order.m": LeastProjective;
import "../Tensor/is-tensor.m": ConstructTensorFactors;

/* parameter settings */

/* maximum number of elements of kernel */
MaxGenerators := 50;

/* maximum number of subgroups of small index */
MaxSubgroups := 100;

/* minimum number of relations to generate */
NmrRels := 20; 

/* maximum number of random elements to generate to
   process for kernel elements */
NmrTries := 100;

/* maximum number of random elements whose order is tested
   in order to rule out tensor induction */
NmrRandomElements := 20;

/* are GcdNmrTries entries in relative order seqeuence identical? */
GcdNmrTries := 15;

/* is number of subgroups of low index constant for LisNmrTries times? */
LisNmrTries := 3;

/* exponent of symmetric group of degree n */

ExponentOfSym := function (n)
   return Lcm ([2..n]);
end function;

/* element orders for symmetric groups */

OrdersSym := function (n)
   if n le 10 then 
      EltOrdersSym := [
      {1},
      {1, 2},
      {1, 2, 3},
      {1, 2, 3, 4},
      {1, 2, 3, 4, 5, 6 },
      {1, 2, 3, 4, 5, 6 },
      {1, 2, 3, 4, 5, 6, 7, 10, 12 },
      {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 15 }, 
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 20 }, 
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 20, 21, 30 }   
      ];
      return EltOrdersSym[n];
   else 
      S := Sym (n);
      C := Classes (S);
      return {C[i][1]: i in [1..#C]};
   end if;
end function;

/* factorisations of n into precisely r factors */
 
Factorisations := function (n, r)
 
   L := FactorList (n);

   if r le 2 then 
      return L; 
   else 
      total := [];
      for x in L do 
         Y := $$(x[#x], r - 1);
         total cat:= [[x[1]] cat y: y in Y];
      end for;
      return {Sort (x): x in total};
   end if;

end function;                                   

/* return all coprime factorisations of n into r factors */

CoprimeFactorisations := function (n, r)

  L := Factorisations  (n, r);
  return {x : x in L | Gcd (x) eq 1};

end function;

/* consider the projective order of an arbitrary element of G, 
   a putative r-fold tensor induced group */

OrderTest := function (G, g, r)

   type1 := 1;
   type2 := 2;
   type3 := 3;

   /* n is the projective order of an element of the kernel of 
     every homomorphism from G into S_r */

   SecondOrderTest := function (G, n, r)

      d := Degree (G);
      F := BaseRing (G);
      q := #F;

      u := Iroot (d, r);
   
      /* does g fit completely into each factor? */
      if LeastProjective (n, q) le u then return type1; end if; 

      /* do all coprime factorisations of g fail to fit into 
         the r factors? */

      Factors := CoprimeFactorisations (n, r);
      if forall (fac) {fac : fac in Factors | 
           exists (x) {x : x in fac | LeastProjective (x, q) gt u}} then
          return type2;
      end if;

      /* some factorisation of g fits into the r factors;
         if this is so, then there is at least one prime dividing
         n which must occur to an exponent larger on at least one factor 
         than all others; raise g to this power and resulting element 
         h must act trivially on at least this one factor and non-trivially
         on at least one other factor; hence h must be a projectivity */

      return type3;

   end function;

   n := ProjectiveOrder (g);

   orders := OrdersSym (r);

   divisors := {m : m in orders | n mod m eq 0};
   types := {SecondOrderTest (G, n div m, r) : m in divisors};

   vprint TensorInduced: "Element orders: n is ", n, "types is ", types;
   if type1 in types then
      return true;
   elif type3 in types then
      return g;
   else  
      /* only type is type 2, hence we can rule out tensor decomposition */
      return false;
   end if;
   
end function;

/* return one element from each class of cyclic conjugates of 
   elements of W */

ConjugateReps := function (W)

   Rotate := {{RotateWord (w, i): i in [1..#w]}: w in W};
   return {Rep (r): r in Rotate};

end function;

/* generate words of length m in Letters which do not
   consist of powers of generators */

procedure Words (Letters, ~m, ~Smaller)

   if m eq 1 then return; end if;

   Larger := {x * w : x in Smaller, w in Letters | w ne x};

   Smaller := Larger; 
   m -:= 1;
   $$ (Letters, ~m, ~Smaller); 

end procedure;

/* generate the words of length m in the supplied letters */

WordsOfLength := function (Letters, m)

   if m lt 1 then return {}; end if;

   Smaller := Letters;
   Words (Letters, ~m, ~Smaller);
   Smaller := ConjugateReps (Smaller);
   return SetToIndexedSet (Smaller);

end function;

/* calculate images of cosets of 1-point stabiliser under g */

PermutationImage := function (Elts, g, CB, dim)

   Inv := [Elts[j]^-1 : j in [1..#Elts]];
   Images := {1..#Elts};
   image := [-1 : i in [1..#Elts]];

   for i in [1..#Elts] do 
      w := Elts[i] * g; 
      for j in Images do 
         if IsProportional ((w * Inv[j])^CB, dim) then 
            image[i] := j;
            Exclude (~Images, j);
            break j;
         end if;
      end for;
   end for;

   return image;
end function;

/* did the element induced a permutation of the cosets? */ 

AreValidPerms := function (Perms)

   return not exists {x : x in Perms | -1 in x};

end function;

/* construct orbit of coset reps for the tensor factor */

CosetReps := function (G, CB, dim, n: Call := 1)

   /* if Call = TRIAL, we may find more coset reps than required */
   TRIAL := 0; 

   d := Degree (G);
   F := BaseRing (G);

   Elts := [Id (GL(d, F))];

   i := 1; complete := false;
   while (i le #Elts) and not complete do 
      for j in [1..Ngens (G)] do 
         g := G.j;
         h := Elts[i] * g;
         if forall {l : l in [1..#Elts] | 
            IsProportional ((Elts[l] * h^-1)^CB, dim) eq false} then
            Append (~Elts, h);
            if #Elts gt n then
               if Call eq TRIAL then return false; end if;
               complete := true; 
            end if;
         end if;
      end for;
      i +:= 1;
   end while;
   
   if complete then s := "at least"; else s := ""; end if;
   vprintf TensorInduced: 
      "Number of cosets of 1-point stabiliser is %o %o\n", s, #Elts;

   if #Elts ne n then 
      vprintf TensorInduced: "Hence G not %o-fold tensor induced\n", n;
      return false;
   else 
      return Elts;
   end if;

end function;

/* to get commutator law for S_n, take set of orders 
   of elements of S_n and delete those elements of the set which
   are proper divisors of other elements of the set */

OrdersForCommutatorLaw := function (n)
   orders := OrdersSym (n); 
   for x in orders do
      if exists {y : y in orders | y gt x and y mod x eq 0} then
         Exclude (~orders, x);
      end if;
   end for;   
   return SetToSequence (orders);
end function;

/* x is an element of G; construct, using x, various elements 
   which must lie in the kernel of a homomorphism from G to S_n */

procedure ElementsOfKernel (G, x, n, ~E: Orders := [])

   case n:
      when 2:
         E := {x^2};
         return;

      when 3:
	 y := RandomElement (G);
	 E := {x^6, (x^2, y^2), (x^2, (x^3)^y)};
	 return; 

      when 4:
	 y := RandomElement (G);
         E := {x^12, y^12, ((x^3 * y^3)^4 * (x^3, y^6)^3)^3,
               (x^2, y^2)^2, (x, y)^6, (x^6, y^6), ((x,y)^3, y^3, y^2)};
	 return;

      when 5:
	 y := RandomElement (G);
         E := {x^60, y^60, ((x^15*y^15)^4*(x^15,y^30)^15)^15,
               ((x^20*y^20)^6 * (x^20,y^20)^2)^5,
               (((x^36*y^12)^5*(x^36*y^48)^5)^3*(x^36,y^36)^6)^6,
               (x^6, y^6)^15,
               ((y^20, x^48, y^40)*(y^20, x^12))^10, 
               ((x^12,y^40,x^48)*(y^20,x^12)^2)^6,
               (x, y)^30,
               (((x^5*y^5)^36*(x^5*y^15)^36)^36*(x^30,y^30))^5,
      (((x^21*y^45)^40*(x^21*y^15)^20)^40*(((x^21,y^21)^45,y^15)^21,y^42))^12};
	 return;

/* 
      when 6:
	 h := RandomElement (G);
	 k := RandomElement (G);
	 E := {x^60, (x^4, (x^5)^h, (x^6)^k)};
	 return;

      when 7:
	 h := RandomElement (G);
	 k := RandomElement (G);
	 E := {x^420, (x^7, (x^10)^h, (x^12)^k)};
	 return; 

      when 8:
	 h := RandomElement (G);
	 k := RandomElement (G);
	 l := RandomElement (G);
	 m := RandomElement (G);
	 E := {x^840, (x^7, (x^8)^h, (x^10)^k, (x^12)^l, (x^15)^m)};
	 return; 

      when 9:
	 h := RandomElement (G);
	 k := RandomElement (G);
	 l := RandomElement (G);
	 m := RandomElement (G);
	 a := RandomElement (G);
	 E := {x^2520, (x^8, (x^9)^h, (x^12)^k, (x^14)^l, (x^15)^m, (x^20)^a)};
	 return; 

      when 10:
	 h := RandomElement (G);
	 k := RandomElement (G);
	 l := RandomElement (G);
	 m := RandomElement (G);
	 a := RandomElement (G);
	 b := RandomElement (G);
	 E := {x^2520, (x^8, (x^9)^h, (x^12)^k, (x^14)^l, (x^20)^m, (x^21)^a,
                        (x^30)^b)};
	 return; 
*/
      else 
         if #Orders eq 0 then Orders := OrdersForCommutatorLaw (n); end if;
         R := [RandomElement (G) : i in [1..#Orders]];
         g := x^Orders[1];
         for i in [2..#Orders] do
            g := (g, (x^Orders[i])^R[i]);
         end for;
         E := {x^ExponentOfSym (n), g};   
         return; 

   end case;

end procedure;

/* construct a subgroup of the kernel of every homomorphism from G to S_n */

SubgroupOfKernel := function (G, n, NmrTries, MaxGens)

   K := {};

   /* if necessary, store orders for commutator law */
   orders := n gt 5 select OrdersForCommutatorLaw (n) else [];

   for i in [1..NmrTries] do 
      g := RandomElement (G);
      ElementsOfKernel (G, g, n, ~h: Orders := orders);
      if not (h cmpeq false) then 
         K join:= h;
      end if;
      if #K gt MaxGens then 
	 break i; 
      end if;
   end for;
   vprint TensorInduced: "Number of elements of kernel found is ", #K;

   if Type (G) eq GrpMat then 
      d, q := BasicParameters (G);
      return sub < GL (d, q) | K >;
   elif Type (G) eq GrpPerm then 
      return sub < Sym (Degree (G)) | K >;
   else
      error "Type of group in SubgroupOfKernel";
   end if;

end function;

/* are the last GcdNmrTries entries identical?
   if so, we believe we have found the correct order */

IsGcdSettled := function (L, GcdNmrTries)

   len := #L;
   if L[len] eq 1 then return true; end if;

   if len ge GcdNmrTries then 
      S := {L[len - i + 1] : i in [1..GcdNmrTries]};
      return #S eq 1;
   end if;

   return false;

end function;

/* w is an element of G; approximate its order modulo the normal
   closure in G of subgroup K by repeatedly evaluating the order 
   of w * k, for k an element of the normal closure in G of K, and 
   taking the GCD of resulting orders */

RelativeOrder := function (G, w, K, GcdNmrTries, n)

   O := [ExponentOfSym (n)]; L := [];

   repeat 
      k := NormalSubgroupRandomElement (G, K);
      o := Order (w * k);
      Append (~O, o);
      Append (~L, Gcd (O));
   until IsGcdSettled (L, GcdNmrTries);

   // vprint TensorInduced:  "Relative order sequence terminates in ", L[#L];
   return L[#L];

end function;

/* get a better approximation to the presentation for Q */

procedure ExtendPresentation (F, phi, G, K, n, NmrRels, ~Q, ~Letters, 
                         ~Special, ~WordLen, ~Position: Discard := true)

   while (#Relations (Q) lt NmrRels) do 
      vprint TensorInduced: "Word length is ", WordLen;
      Words := WordsOfLength (Letters, WordLen);

      /* possible that all generators map to the identity,
         hence call generates no words */
      if #Words eq 0 then return; end if;

      for index in [Position + 1..#Words] do
         w := Words[index];
         im := phi (w);
         o := RelativeOrder (G, im, K, GcdNmrTries, n);
         Q := AddRelation (Q, w^o);
         if #Relations (Q) ge NmrRels then 
            vprint TensorInduced: 
               "# of relations for Q is now ", #Relations (Q);
            Position := index; return; 
         end if;

         /* is the relation w * x * w' = 1, where neither of w nor
            w' contains x? if so, exclude x from Letters */
         if o eq 1 then 
            w := Eltseq (w);
            if exists (x) {x : x in w | #[y: y in w | y eq x] eq 1} then 
               Exclude (~Letters, F.x);
               Append (~Special, w);
               vprint TensorInduced: "Letters is now ", Letters;

               /* we may want to generate all short words again 
                  on the shorter generating set */
               if Discard eq true then 
                  Q := quo <F | Special>;
                  // "Q is now ", Q;
                  WordLen := 0;
                  Position := 0;
               else 
                  WordLen -:= 1;
               end if;

               break index;
            end if;
         end if;
      end for;
      WordLen +:= 1; Position := 0;
   end while;

end procedure;

/* is the number of subgroups of index n constant? */

IsLowIndexSettled := function (L)

   len := #L;
   if #L[len] le 1 then return true; end if;

   if len ge LisNmrTries then 
      S := {#L[len - i + 1] : i in [1..LisNmrTries]};
      return #S eq 1 and S ne {MaxSubgroups};
   end if;

   return false;
       
end function;

/* let K be subset of kernel of some homomorphism from G to S_n; 
   find a presentation for Q, a preimage of S_n in G, which contains K; 
   obtain a presentation for Q, repeatedly extending the presentation 
   until the number of subgroups of index n in Q is fixed; 
   we're computing preimages of 1-point stabilisers */ 

FindPreimage := function (G, K, n: Print := 0, 
                                   SubgroupLimit := MaxSubgroups)

   F := FreeGroup (Ngens (G));
   phi := hom < F -> G | [G.i : i in [1..Ngens (G)]]>;
   Q := quo < F | >;

   Special := []; WordLen := 1; Pos := 0; L := []; i := 0; 
   Letters := Generators (F);
   repeat 
      i +:= 1;
      ExtendPresentation (F, phi, G, K, n, NmrRels * i, ~Q, ~Letters, 
                          ~Special, ~WordLen, ~Pos);
      if Type (SubgroupLimit) eq Intrinsic then 
         L[i] := LowIndexSubgroups (Q, <n, n>: Print := Print); 
      else 
         L[i] := LowIndexSubgroups (Q, <n, n>: Print := Print, 
                                            Limit := SubgroupLimit);
      end if;
   until IsLowIndexSettled (L) or i gt NmrTries;

   if L eq [] then L := [[sub < Q | >]]; end if;

   return Q, L[#L];

end function;

/* L is subgroup of index n in Q; get normal generating set 
   in G for kernel of homomorphism from Q to S_n */

NormalGeneratorsOfKernel := function (G, Q, L)

   /* I is image under potential homomorphism from G into S_n */

   phi, I := CosetAction (Q, L);
   vprint TensorInduced: "Order of image is ", #I;
   vprint TensorInduced: "Image is ", I;

   gens := [phi (Q.i): i in [1..Ngens (Q)]];
   id := Identity (I);
   
   /* generators mapping to the identity */
   K := sub <G | [G.i : i in [1..Ngens (G)] | gens[i] eq id]>;

   /* repetitions of generators */
   for i in [1..Ngens (G)] do
      if G.i ne Id (G) then
         equal := [j : j in [i + 1..Ngens (G)] | gens[i] eq gens[j]];
         K := sub < G | K, [G.i * G.j^-1 : j in equal]>;
      end if;
   end for; 
   
   vprint TensorInduced: "Now apply FPGroup to image"; 
   F, f := FPGroup (I);
   vprint TensorInduced: "Succeeding obtaining finite presentation for image"; 
   R := Relations (F);
   if Type (R[1]) eq RelElt then
      R := [LHS (R[i]) * RHS (R[i])^-1 : i in [1..#R]];
   end if;

   /* define map tau from F -> G */
   tau := hom <F -> G | [<F.i, G.Position (gens, f (F.i))> : 
                         i in [1..Ngens (F)]]>;

   return sub <G | K, [tau (r): r in R]>, I, gens;
  
end function;

/* L is a subgroup of index n in Q, a finite presentation for G; 
   write down subgroup generators for the preimage of L in G */

KernelGenerators := function (G, Q, L)

   assert Ngens (G) eq Ngens (Q);
   vprint TensorInduced: "Now attempt to obtain transversal";
   T, phi := Transversal (Q, L);
   Qgens := [Q.i : i in [1..Ngens (Q)]];
   Y := {t * q * (phi (t * q))^-1: t in T, q in Qgens};
   tau := hom < Q -> G | [G.i : i in [1..Ngens (G)]]>;
   K := sub <G | {tau (y): y in Y}>;

   return K;

end function;

/* investigate if the mapping is really a homomorphism by evaluating 
   words in G and I, and deciding that order of word modulo K, the 
   putative kernel of hom, is divisible by order of word in I */

InvestigateMapping := function (G, K, I, gens, NmrTries, n)

   M := BlackboxGroup (#gens);
   P := RandomProcess (M);

   alpha := hom <M -> I | gens >;
   beta := hom <M -> G | [G.i : i in [1..Ngens (G)]]>;

   for i in [1..NmrTries] do 
      w := Random (P);
      Im := Order (alpha (w));
      PreIm := RelativeOrder (G, beta (w), K, GcdNmrTries, n);
      if PreIm mod Im ne 0 then 
         vprint TensorInduced: "Mapping is not a homomorphism";
         return false;
      end if;
   end for;

   return true;

end function;

/* U is a flat of dimension d; extract from it a flat of dimension d div m */

ExtractFlat := function (U, m)

   F := BaseRing (U);
   d := Degree (U);
   len := d div m;

   E := [Eltseq (U.i) : i in [1..Ngens (U)]];
   Short := [[E[i][j] : j in [1..len]] : i in [1..#E]];
   V := VectorSpace (F, len);
   return sub < V | Short >;

end function;

/* compute preimage in matrix group G of stabiliser of elements of list */

StabiliserPreimage := function (G, Perms, list)

   n := #Perms[1];
   P := sub < Sym (n) | Perms >;
   Perms := [P!p : p in Perms];

   U := Stabiliser (P, list);

   X := [G.i: i in [1..Ngens (G)]];

   W := WordGroup (P);
   inv := InverseWordMap (P);

   T, tau := Transversal (P, U);
   transW := [inv (t): t in T];

   gens := [G.Position (Perms, P.i): i in [1..Ngens (P)]];
   preimages := [Evaluate (w, gens): w in transW];

// bug -- W is not equal to codomain of inv 
//   /* define hom from W -> G */
//   thetaInv :=
//        hom <W -> G | [<W.i, G.Position (Perms, P.i)> : i in [1..Ngens (P)]]>;
//    preimages := [thetaInv (w) : w in transW];

   C := [preimages[i] * X[j] *
         preimages[Position (T, tau (T[i] * Perms[j]))]^-1
            : i in [1..#T], j in [1..#X]];

   return sub < G | C >;

end function;

/* find matrix in G which permutes factor 1 -> factor k; Perms 
   stores the permutations induced by each of the generators of G  */

PermutingMatrix := function (G, Perms, k)

   assert #Perms gt 0;
   n := #Perms[1];
   P := sub < Sym (n) | Perms >;
   Perms := [P!x: x in Perms];
   W := WordGroup (P);
   phi := InverseWordMap (P); 
   assert exists (x) {x : x in P | 1^x eq k};
   return Evaluate (phi (x), [G.Position (Perms, P.i): i in [1..Ngens (P)]]);

// doesn't work because W doesn't equal codomain of phi 
// tau := hom < W -> G | [<W.i, G.Position (Perms, P.i)>: i in [1..Ngens (P)]]>;
// return tau (phi (x));

end function;

/* construct change of basis matrix which exhibits tensor induction */ 
ChangeOfBasis := function (G, COB)
  
   F := BaseRing (G);
   d := Degree (G);
   n := #COB + 1;
   m := Iroot (d, n);
   MA := MatrixAlgebra (F, d);

   ConstructMatrix := function (COB)
      A := Zero (MA);
      a := COB[1];
      k := Nrows (a);
      a := MatrixAlgebra (F, k) ! a;
      for j in [1..d div k] do 
         pos := (j - 1) * k + 1;
         InsertBlock (~A, a, pos, pos);
      end for;
      return A;
   end function;

   A := [ConstructMatrix (COB[i]) : i in [1..#COB]];

   CB := GL (d, F) ! &*A;
   
   gens := [G.i^CB : i in [1..Ngens (G)]];
   return AreProportional (gens, m), CB;

end function;

GeneralStep := function (G, Flat, COB, Elts, Perms, KER, CB, n, k, dim, m)

   /* find permutation which maps 1 to k */
   trans := PermutingMatrix (G, Perms, k);

   /* check that trans maps 1 -> k */
   image := PermutationImage (Elts, trans, CB, dim);
   vprint TensorInduced: "Image of 1 under permutation is ", image;
   assert image[1] eq k;

   /* include image of Flat[1] under trans */
   Append (~Flat, Flat[1]^trans);

   FlatMeet := &meet (Flat);

   /* repeatedly extract subsections of vectors */
   for i in [1..k - 1] do 
      FlatMeet := FlatMeet^COB[i][1];
      FlatMeet := ExtractFlat (FlatMeet, m);
   end for;

   /* now we have a flat in geometry of dimension m^k */
   SmallerFlat := FlatMeet;

   /* restrict kernel to factor acting in this dimension */
   list := [1..k];
   PermsKER := [PermutationImage (Elts, KER.i, CB, dim): 
                i in [1..Ngens (KER)]];
   KER := StabiliserPreimage (KER, PermsKER, list);
   y := KER;
   for i in [1..k - 1] do
      // 1st change to reflect new Tensor code 
      // y := ConstructTensorFactors (y, COB[i]);
      _, y := ConstructTensorFactors (y, COB[i]);
   end for;

   B := "unknown"; A := false;
   GeneralFindPoint (y, ~SmallerFlat, Dimension (SmallerFlat), ~A, ~B);

   if A ne true then 
      vprint TensorInduced: "Failed to decompose tensor product"; 
      return false, false, false; 
   end if;

   Append (~COB, B);

   return Flat, COB, KER;

end function;

ConstructDecomposition := function (G, K, CB, Elts, Perms, dim)

   F := BaseRing (G);
   d := Degree (G);
   n := #Elts;
   m := Iroot (d, n);
   CBinv := CB^-1;

   V := VectorSpace (F, d);

   /* set up point of dimension m^(n - 1) */
   if dim eq m then 
      Flat := sub <V | [CBinv[(i - 1) * m + 1] : i in [1..Degree (CB) div m]]>;
   else 
      Flat := sub <V | [CBinv[i] : i in [1..dim]]>;
   end if;

   A := false; B := "unknown";
   GeneralFindPoint (K, ~Flat, dim, ~A, ~B);
   if A cmpeq "unknown" or A cmpeq false then 
      return false, false, false; 
   end if;

   Flat := [Flat];
   COB := [* B *];

   if n eq 2 then 
      KER := K;
   else 
      KER := G;
      for k in [2..n - 1] do 
         vprint TensorInduced: "k is ", k;
         Flat, COB, KER := GeneralStep (G, Flat, COB, Elts, 
                                           Perms, KER, CB, n, k, dim, m);
         if Type (Flat) eq BoolElt then return false, false, false; end if;
      end for;
   end if;

   a, CB := ChangeOfBasis (KER, COB);
   // assert a eq true;

   return a, CB, KER;

end function;

/* is the d x d matrix g proportional for all relevant powers of 
   the n-th root of d? */

AllProportional := function (g, n)
   d := Nrows (g);
   m := Iroot (d, n);
   return [x : x in [m^r : r in [1..n - 1]] | IsProportional (g, x)];
end function;

/* write down permutation matrix which describes the permutation
   of rows and columns determined by permutation sigma  */

PermutationMatrix := function (d, F, r, sigma)
   P := Zero (MatrixAlgebra (F, d^r));
   for n in [0..d^r - 1] do
      x := Intseq (n, d); 
      x cat:= [0: i in [1..r - #x]]; 
      m := Seqint ([x[j] : j in [i^sigma: i in [1..r]]], d);
      P[n + 1][m + 1] := 1;
   end for;
   return P;
end function;

/* write down permutation induced on tensor factors by g */

MatrixToPermutation := function (G, COB, CB, Elts, g)

   n := #Elts;
   h := g^COB;
   d := Degree (G);
   F := BaseRing (G);
   S := Sym (n);
   perm := PermutationImage (Elts, g, CB[1], CB[2]);
   if AreValidPerms ({perm}) eq false then return false; end if;
   perm := S ! perm;
   vprint TensorInduced: "Permutation induced on factors by matrix is ", perm;
   dim := Iroot (d, n);

   /* problem with renumbering of factors */
   s := S! [n - i:  i in [0..n - 1]];
   m := h * PermutationMatrix (dim, F, n, perm^s);
   if #AllProportional (m, n) eq n - 1 then 
      return perm;
   else 
      "We appear to have an example where group permutes tensor \
factorisations of itself, but not the individual factors in a factorisation\n";
      return "unknown";
   end if;

end function;

ImageOfTensorInducedElement := function (G, g)
   COB := TensorInducedBasis (G);
   CB := TensorInducedImageBasis (G);
   return MatrixToPermutation (G, COB, CB[1], CB[2], g);
end function;

intrinsic TensorInducedAction (G::GrpMat, g::GrpMatElt)-> GrpPermElt
{Tensor induced action of g}
   if TensorInducedFlag (G) cmpeq "unknown" then 
      return "unknown";
   end if;
   if TensorInducedImageBasis (G) cmpeq "unknown" then
      /* result obtained from call to Smash */
      return SymmetricTensorAction (G, g);
   else
      /* result obtained from call to IsTensorInduced */
      return ImageOfTensorInducedElement (G, g);
   end if;
end intrinsic;

MainIsTensorInduced := function (G, n)

   error if n lt 2, "<n> must be at least 2";
   d := Degree (G);
   m := Iroot (d, n);

   if m^n ne d then
      vprint TensorInduced: d, "is not a proper", n, "-fold power";
      return false, false, false, false, false;
   end if;

   for  i in [1..NmrRandomElements] do 
      g := RandomElement (G);
      flag := OrderTest (G, g, n);
      if flag cmpeq false then
         return false, false, false, false, false;
      elif Type (flag) cmpeq BoolElt eq false then 
         vprint TensorInduced: "Order test has found potential projectivity";
      end if;
   end for;

   List := [[m, d div m]];

   /* can we construct the decomposition? */
   test := function (G, K, n, call)
      CB := TensorBasis (K);
      T := TensorFactors (K);
      // 2nd change to reflect new Tensor code 
      dim := Degree (T[1]);
      dim := Degree (T[2]);
      Elts := CosetReps (G, CB, dim, n: Call := call);
      if Type (Elts) eq SeqEnum then 
         Perms := [PermutationImage (Elts, G.i, CB, dim): i in [1..Ngens (G)]];
         vprint TensorInduced: "Permutations are ", Perms;
         if AreValidPerms (Perms) then 
            vprint TensorInduced: "G appears to be tensor-induced\n";
            vprint TensorInduced: "We attempt to complete the construction";
            flag, COB, KER := ConstructDecomposition (G, K, CB, Elts, 
                                                       Perms, dim);
            if flag then return flag, COB, <CB, dim>, Elts, KER; end if;
         end if;
      end if;

      return false, false, false, false, false;

   end function;
 
   /* obtain a subgroup of the kernel of every homorphism
      from G to S_n */

   K := SubgroupOfKernel (G, n, NmrTries, MaxGenerators);
   if Ngens (K) eq 0 then 
      vprint TensorInduced: "Intersection of kernels appears to be trivial"; 
   end if;

   /* if K is not a tensor product, G is not a tensor product;
      if K is a tensor product, try to construct permutation
      action on tensor factors of G; if we succeed in constructing 
      the permutations, then G may be tensor-induced; 
      if we fail, this test is inconclusive */

   flag := IsTensor (K: Fast := true, Factors := List, RandomElements := 40);
   if flag cmpeq true then 
      found, COB, CB, Elts, KER := test (G, K, n, 0);
      if found then return found, COB, CB, Elts, KER; end if;
   elif flag cmpeq false then
      vprint TensorInduced: 
          "Kernel does not preserve a tensor decomposition";
      return false, false, false, false, false;
   elif flag cmpeq "unknown" then
      vprint TensorInduced: 
           "Not known whether subgroup of kernel preserves tensor";
   end if;

   /* construct presentation for some preimage Q of S_n in G;
      L is list of subgroups of index n in Q; process each; if 
      none is a tensor product, then G is not tensor induced */

   Q, L := FindPreimage (G, K, n);
   vprint TensorInduced: "Number of subgroups of index ", n, " is at most ", #L;
   Kernels := [];
   for i in [#L..1 by -1] do
      K, I, gens := NormalGeneratorsOfKernel (G, Q, L[i]);
      if InvestigateMapping (G, K, I, gens, NmrTries, n) eq true then 
         K := KernelGenerators (G, Q, L[i]);
         flag := IsTensor (K: Factors := List, Fast := true, 
                              RandomElements := 40);
         if flag cmpeq true then 
            found, COB, CB, Elts, KER := test (G, K, n, 1);
            if found then return found, COB, CB, Elts, KER; end if;
         elif flag cmpeq false then 
            vprint TensorInduced: 
                "Kernel of mapping does not preserve tensor decomposition";
         else 
            vprint TensorInduced:
                "Cannot decide whether kernel of mapping preserves tensor";
            Append (~Kernels, K);
         end if;
      end if;
   end for;

   unknown := [];
   for i in [1..#Kernels] do
      K := Kernels[i];
      flag := IsTensor (K: Factors := List, RandomElements := 40);
      if flag cmpeq true then 
         found, COB, CB, Elts, KER := test (G, K, n, 1);
         if found then return found, COB, CB, Elts, KER; end if;
      elif flag cmpeq false then 
         vprint TensorInduced: 
             "Kernel of mapping does not preserve tensor decomposition";
      else 
         vprint TensorInduced: 
             "Cannot decide whether kernel of mapping preserves tensor";
         Append (~unknown, i);
      end if;
   end for;

   if #unknown gt 0 then 
      return "unknown", "unknown", [Kernels[i]: i in unknown], false, false;
   else 
      return false, false, false, false, false;
   end if;

end function;

/* is G an n-fold tensor induced power? */

nTensorInduced := function (G, n)

   error if n lt 2, "<n> must be at least 2";
   d := Degree (G);
   m := Iroot (d, n);
   error if m^n ne d, d, "is not a proper", n, "-fold power";

   found, COB, CB, Elts, KER := MainIsTensorInduced (G, n);
   if found cmpeq true then 
      Images := [];
      for i in [1..Ngens (G)] do 
         perm := MatrixToPermutation (G, COB, CB, Elts, G.i);
         if perm cmpeq "unknown" then
            return "unknown", _, _, _, _;
         end if;
         if Type (perm) eq BoolElt then return false, _,_,_,_; end if;
         Append (~Images, perm);
      end for;
      return true, Images, COB, CB, Elts;
   elif found cmpeq "unknown" then 
      return "unknown", _, _, _, _;
    else 
      return false, _, _, _, _;
   end if;

end function;

/* construct the tensor-induced factors */

ConstructTensorInducedFactors := function (G, n) 

   F := BaseRing (G);
   COB := TensorInducedBasis (G);

   d := Degree (G);
   m := Iroot (d, n);
   error if m^n ne d, d, "is not a proper", n, "-fold power";
   gens := [G.i^COB : i in [1..Ngens (G)]];
   factors := [];
   for i in [1..n - 1] do 
      flag, Matrices := AreProportional (gens, m);
      assert flag eq true;
      l1 := Nrows (Matrices[1][1]); 
      l2 := Nrows (Matrices[1][2]); 
      small := l1 le l2 select 1 else 2; 
      large := small eq 1 select 2 else 1;
      factors[i] := [Matrices[k][small]: k in [1..#Matrices]];
      gens := [Matrices[k][large]: k in [1..#Matrices]];
   end for;
   Append (~factors, gens);
   return factors;

end function;

/* is G tensor-induced? */

intrinsic IsTensorInduced (G:: GrpMat : InducedDegree := "All") -> BoolElt 
{Return true iff G tensor-induced}

   flag := TensorInducedFlag (G);
   if flag cmpeq true or flag cmpeq false then return flag; end if; 

   if RecogniseClassical (G) cmpeq true then return false; end if;

   if InducedDegree cmpeq "All" then 
      d := Degree (G);
      flag := false;
      for x in [Isqrt (d)..2 by -1] do 
         ispower, n := IsPowerOf (d, x);
         if ispower then 
            vprintf TensorInduced: "Consider %o-fold induction\n", n;
            flag, Images, COB, CB, Elts := nTensorInduced (G, n);
            if flag cmpeq true then 
               SetTensorInducedFlag (G, true);
               SetTensorInducedBasis (G, COB);
               SetTensorInducedPermutations (G, Images);
               SetTensorInducedImageBasis (G, <CB, Elts>);
               return flag;
            end if;
         end if;
      end for;
   else 
      n := InducedDegree;
      vprintf TensorInduced: "Consider %o-fold induction\n", n;
      flag, Images, COB, CB, Elts := nTensorInduced (G, n);
      if flag cmpeq true then 
         SetTensorInducedFlag (G, true);
         SetTensorInducedBasis (G, COB);
         SetTensorInducedPermutations (G, Images);
         SetTensorInducedImageBasis (G, <CB, Elts>);
         return flag;
      end if;
   end if;
 
   if flag cmpeq "unknown" then 
      return "unknown"; 
   elif flag cmpeq false then  
      SetTensorInducedFlag (G, false);
      return false;
   end if;

   error "IsTensorInduced -- no conclusion reached";

end intrinsic;

/* 
intrinsic LowIndexSubgroupsCT (G:: GrpMat, n:: RngIntElt: 
                             Print := 0, Limit := Infinity) -> SeqEnum
{Subgroups of index n in G}
*/

MyLowIndexSubgroups := function (G, n: Print := 0, Limit := Infinity) 

   K := SubgroupOfKernel (G, n, NmrTries, MaxGenerators);
   Q, L := FindPreimage (G, K, n: Print := Print, SubgroupLimit := Limit);
   vprint TensorInduced: "Number of subgroups of index ", n, " is at most ", #L;
   list := [];
   for i in [#L..1 by -1] do
      K, I, gens := NormalGeneratorsOfKernel (G, Q, L[i]);
      if InvestigateMapping (G, K, I, gens, NmrTries, n) eq true then
         K := KernelGenerators (G, Q, L[i]);
         Append (~list, K);
      end if;
   end for;                                                                     

   return list;

// end intrinsic;
end function;

intrinsic LowIndexSubgroupsCT (G:: GrpMat, R::Tup : Print := 0, 
                             Limit := Infinity) -> SeqEnum
{Subgroups of index lying in range specified by R}

   a := R[1]; b := R[2];
   require a ge 1 and b ge a: "Invalid index range";

   L := [];
   for n in [a..b] do 
      L cat:= MyLowIndexSubgroups (G, n: Print := Print, Limit := Limit); 
   end for;
   return L;

end intrinsic;

intrinsic LowIndexSubgroupsCT (G::GrpMat, n:: RngIntElt: Print := 0, 
                                    Limit := Infinity) -> SeqEnum
{Subgroups of index at most n in G}

   requirege n, 1;
   return LowIndexSubgroupsCT (G, <1, n>: Print := Print, Limit := Limit);
end intrinsic;

/* 
intrinsic LowIndex (G::GrpPerm, n:: RngIntElt: Print := 0, 
                                    Limit := Infinity) -> SeqEnum
{Subgroups of index n in G}

   return LowIndexSpecial (G, n: Print := Print, Limit := Limit);

end intrinsic;

intrinsic LowIndexSubgroupsCT (G::GrpMat, n:: RngIntElt: Print := 0, 
                                    Limit := Infinity) -> SeqEnum
{Subgroups of index n in G}

   return LowIndexSpecial (G, <2, n>: Print := Print, Limit := Limit);

end intrinsic;

intrinsic LowIndex (G::GrpPerm, R::Tup : Print := 0, Limit := Infinity) 
                    -> SeqEnum
{Subgroups of index lying in range specified by R}

   return LowIndexSpecial (G, R: Print := Print, Limit := Limit);

end intrinsic;

intrinsic LowIndexSubgroupsCT (G::GrpMat, R::Tup : 
    Print := 0, Limit := Infinity) -> SeqEnum
{Subgroups of index lying in range specified by R}

   return LowIndexSpecial (G, R: Print := Print, Limit := Limit);

end intrinsic;
*/

intrinsic LowIndexSubgroupsSn (G:: GrpPerm, R::Tup : Print := 0, 
          Limit := Infinity) -> SeqEnum
{Subgroups of index lying in range specified by R}

   a := R[1]; b := R[2];
   require Type(a) eq RngIntElt : "index limits must be integers";
   require Type(b) eq RngIntElt : "index limits must be integers";
   require a ge 1 and b ge a: "Invalid index range";

   L := [];
   for n in [a..b] do 
      L cat:= MyLowIndexSubgroups (G, n: Print := Print, Limit := Limit); 
   end for;
   return L;

end intrinsic;

