freeze;

/* input a pc-group G and a pc abelian group U;
   produce Ext (G/G', U) and Hom (H_2 (G), U) in cocycle matrix form 

   Flannery & O'Brien; latest revision March 2013 incorporating
   fix from Ronan Egan */

declare verbose Cocycle, 1;                                               
declare attributes GrpPC : Elements;

CentralRF := recformat < ElementsExt : SeqEnum, G: GrpPC, U: GrpPC, 
                  ElementsHom: SeqEnum, index : Tup, complete : BoolElt >;

GeneratingHoms := function (A, B)
   X, t := Hom (A, B);
   gens := [X.i : i in [1..Ngens (X)]];
   return [t(x): x in gens], [Order (x): x in gens];
end function;

/* g is an element of a pc-group; rewrite as element  
   of FP-group D where we map G.i -> D.(i + offset) */

ConvertWord := function (offset, g, D)
   w := Eltseq (g);
   return D ! &cat [[offset + i : j in [1..w[i]]] : i in [1..#w]];
end function;

/* are G and U both pc-groups? */

procedure CheckInput (G, U)
   error if Type (G) ne GrpPC, "Runtime error: Argument 1 (", 
                               G, ") is not a PC group";
   error if Type (U) ne GrpPC and IsAbelian (U) eq false, 
   "Runtime error: Argument 2 (", U, ") is not an abelian PC group";
end procedure;

/* M is a list of length n^2 whose entries are elements
   of an abelian group; return an element of the n-dimensional
   matrix ring defined over the group algebra of U */

ListToMatrix := function (M, U)
   R := GroupAlgebra (Integers (), U);
   e := &cat (M);
   n := Isqrt (#e);
   MA := MatrixRing (R, n);
   return MA ! e;
end function;

/* n x n matrix whose entries are the identity of U */  

MatrixOfOnes := function (U, n)
   R := GroupAlgebra (Integers (), U);
   MA := MatrixRing (R, n);
   one := Id (U);
   list := [one: i in [1..n^2]];
   return MA!list;
end function;

/* component-wise multiplication of collection of matrices */

ComponentMultiplication := function (M, U)

   if #M eq 0 then return M; end if;
   m := Nrows (M[1]); n := m;

   R := GroupAlgebra (Integers (), U);
   MA := MatrixRing (R, n);

   X := Zero (MA);
   for i in [1..m] do 
      for j in [1..n] do
         X[i][j] := &*[M[k][i][j]: k in [1..#M]];
      end for;
   end for;

   return X;

end function;

/* description of basis of U is as tuple <generator, order> */

ConstructMatrix := function (Pair, U)

   e := Pair[1];
   u := Pair[2][1];
   f := Pair[2][2];

   /* u is the element which determines the matrix */
   // if f gt e then u := u^(f div e); end if;

   id := Identity (U);
   row := [id :  i in [1..e]];

   A := [row];
   for i in [1..e - 1] do 
      x := row;
      for j in [e..e - i + 1 by -1] do
         x[j] := u;
      end for;
      Append (~A, x);
   end for;
   
   return ListToMatrix (A, U);

end function;

/* form the pairwise Kronecker product of the matrices A and B;
   the elements of A and B are elements of a group */

GroupTensorProduct := function (A, B, U) 

   d1 := Nrows (A); d2 := Nrows (B); d := d1 * d2;

   C := []; D := [];

   for u in [1..d] do
      x, y := Quotrem (u - 1, d1);
      for v in [1..d] do
         z, t := Quotrem (v - 1, d1);
         C[(u - 1) * d1 * d2 + v] := A[1 + y][1 + t] * B[1 + x][1 + z];
      end for;
   end for;

   offset := 0;
   for i in [1..d] do
      D[i] := [];
      for j in [1..d] do
         Append (~D[i], C[offset + j]);
      end for;
      offset +:= d;
   end for;

   return ListToMatrix (D, U);

end function;

/* find basis for abelian group A; sort by prime and 
   increasing power of each prime */

///////////////////////////////////////////////
//
//	AllPrimePowerDivisors is a useful function which
//	returns the prime power factorisation of a number n.
//	e.g., input 12, returns [4,3].
//

AllPrimePowerDivisors := func<n | [t[1]^t[2]:t in Factorization(n)]>;

///////////////////////////////////////////////
//
//	MyAbelianBasis is a new version that fixes the 
//	output for the ComputeExt code.
//      supplied by Ronan Egan March 2012 
//      The problem before was the output from MyAbelianBasis.
//      IA was being returned with products of primes, for example
//      inputting the group C12 returned [12], which contains no power
//      of any prime for use in the ComputeExt code.  We want C12 to
//      be of the form C4 X C3 and to adjust the Basis accordingly.  */
//
///////////////////////////////////////////////

/* find basis for abelian group A; sort by prime and 
   increasing power of each prime */

MyAbelianBasis := function (A)

   BasisA, IA := AbelianBasis (A);
   IA := [AllPrimePowerDivisors(i) : i in IA];
   IA := &cat IA;
   PA := {PrimeBasis (x)[1] : x in IA};
   gens := Generators(A);
   gens := Setseq(gens);
   orders := [Order(i) : i in gens];
   BasisA := [<gens[i], orders[i]>: i in [1..#gens]];
   BasisA := [a : a in BasisA | a[2] in IA];
   Sort (~BasisA, func < x, y | x[2] - y[2]>);
   Sort (~BasisA, func < x, y | PrimeBasis (x[2])[1] - PrimeBasis (y[2])[1]>);
   return BasisA, IA, PA;

end function;

/* list elements of G in sequence used to index matrices computed for Ext */

ListElements := function (Rep)

   /* map from G to G/G' */
   eta := Rep[2];

   /* basis for G/G' */
   basis := Rep[3];

   /* powers of elements of basis */
   Elts := {@ {@ basis[i][1]^j : j in [0..Order (basis[i][1]) - 1] @}: 
            i in [1..#basis] @};
  
   /* pull these back to G */
   Elts := {@ Elts[i] @@ eta : i in [1..#basis] @};

   /* add in list of elements of G' */ 
   Include (~Elts, Rep[4]);

   E := Elts[1];
   i := 1;
   while i lt #Elts do 
      j := i + 1;
      E := {@ y * x : y in Elts[j], x in E @}; 
      i +:= 1;
   end while;
  
   return E; 

end function;

intrinsic ElementSequence (G:: GrpPC) -> SetIndx 
{return indexed set of elements of G listed in the order 
 used by ExtGenerators and HomGenerators}

   if assigned G`Elements eq false then 
      error "Error in Central package: Elements of G not explicitly listed";
   end if;
   return G`Elements;

end intrinsic;

/* compute Ext (G/G', U) as matrices where G is PC-group, U is abelian */

ComputeExt := function (G, U)

   CheckInput (G, U);
   D := DerivedGroup (G);
   Q, eta := quo < G | D>;

   BasisQ, IG, PG := MyAbelianBasis (Q);
   BasisU, IU, PU := MyAbelianBasis (U);

   Common := PG meet PU;
   vprint Cocycle: "Common primes are ", Common;

   Matrices := [* *]; Orders := []; 

   /* for each prime p, construct Sylow p-subgroup, write down matrices */
   for p in Common do 

      /* p-primary component of G/G' */
      L := [y : y in IG | IsPowerOf (y, p)];
      // "L is ", L;

      /* p-primary component of U */
      S := SylowSubgroup (U, p);
      IS := AbelianInvariants (S);

      /* basis for S */
      M := [x : x in BasisU | x[2] in IS];

      /* write down matrix for each p-component */
      for x in L do
         Mats := []; Ords := [];
         for y in M do
            A := ConstructMatrix (<x, y>, U);
            Append (~Mats, A);
            Append (~Ords, Minimum (x, y[2]));
         end for;
         if #Mats gt 0 then 
            Matrices[#Matrices + 1] := Mats;
            // Append (~Matrices, Mats);
            Append (~Orders, Ords);
         end if;
      end for;

   end for;

   /* p-dash action */
   pdash := PG diff Common; 
   for p in pdash do
      Matrices[#Matrices + 1] := [MatrixOfOnes (U, #Sylow (Q, p))];
      Append (~Orders, [1]);
   end for;

   /* add in matrix for G' */
   Matrices[#Matrices + 1] := [MatrixOfOnes (U, #G div #Q)];
   Append (~Orders, [1]);

   Rep := <Q, eta, BasisQ, {@ G!x: x in D @}>;
   G`Elements := ListElements (Rep);

   return Matrices, Orders;

end function;

/* is C the matrix consisting entirely of the identity of U? */
IsIdentityMatrix := function (C, U)
   return Set (Eltseq (C)) eq {Identity (U)};
end function; 

/* form Kronecker products of matrices in M to give Ext generators */

intrinsic ExtGenerators (G::GrpPC, U :: GrpPC) -> SeqEnum, SeqEnum
{generators for Ext (G/G', U) as cocyclic matrices; U is abelian}
  
   M, Orders := ComputeExt (G, U);

   gens := []; orders := [];
   // id := [MatrixOfOnes (U, Nrows (M[i][1][1])): i in [1..#M]];
   id := [* *];
   for i in [1..#M] do 
      if #M[i] gt 0 then 
         id[i] := MatrixOfOnes (U, Nrows (M[i][1]));
      else 
         id[i] := [];
      end if;
   end for;
  
   for i in [1..#M] do
      for j in [1..#M[i]] do 
          if IsIdentityMatrix (M[i][j], U) then continue; end if;
          if i gt 1 then 
             product := id[1];
             for k in [2..i - 1] do 
                product := GroupTensorProduct (id[k], product, U);
             end for;
             product := GroupTensorProduct (M[i][j], product, U);
             order := Orders[i][j];
          else 
             product := M[1][j];
             order := Orders[1][j];
          end if; 
          for k in [i + 1..#M] do 
             product := GroupTensorProduct (id[k], product, U);
          end for;
          Append (~gens, product);
          Append (~orders, order);
      end for;
   end for;
     
   return [<gens[i], orders[i]>: i in [1..#gens]];

end intrinsic;
        
/* compute Hom (H_2(G), U) as matrices where G is PC-group, U is abelian */

intrinsic HomGenerators (G :: GrpPC, U :: GrpPC) -> SeqEnum, SeqEnum 
{generators for Hom (H_2 (G), U) as cocyclic matrices; U is abelian} 

   CheckInput (G, U);

   n := NPCgens (G);
   F, gamma := FPGroup (G);
   // EOB -- comment out until decision made on direction of map 
   // assert [F.i @@ gamma : i in [1..n]] eq [G.i : i in [1..n]];

   o := FactoredOrder (G) cat FactoredOrder (U);    
   primes := {x[1] : x in o};

   D := Darstellungsgruppe (F);
   m := Ngens (D);

   CosetOption := false;

   if CosetOption then 
      CS := CosetSpace (D, sub <D|>: Hard, Workspace := 10000000, 
                                       Print := 10000);
      theta, P := CosetAction (CS);
      H, delta := PCGroup (P);
   else 
      // H, delta := SolubleQuotient (D, [<x, 0>: x in primes]: Print := 0);
      H, delta := SolubleQuotient (D, primes: Print := 0);
      theta := IdentityHomomorphism (D);
   end if;
   
   vprint Cocycle: "Schur cover is ", H;

   /* the new generators introduced by Darstellungsgruppe 
      are D.(n + 1)..D.(m); */

   gens := [delta (theta (D.i)) : i in [n + 1 .. m]];

   /* Schur multiplier */
   M := sub < H | gens >;

   assert #G * #M eq #H;

   /* generating homomorphisms from M to U, both finite abelian groups */
   A, orders := GeneratingHoms (M, U);
   vprint Cocycle: "# of generating homomorphisms is ", #A;
   if #A eq 0 then return []; end if;
   
   /* map from a Schur cover D of G to pc-representation H of D */
   eta := hom <D -> H | [delta (theta (D.i)) : i in [1..m]]>;

   /* evaluate words representing distinct elements of G as 
      corresponding words in generators of H */
   E := G`Elements;
   CW := {@ eta (ConvertWord (0, g, D)) : g in E @};

   /* now evaluate (a * b)^-1 * a * b in H, where a and b run over G */
   L := [];
   for a in [1..#E] do 
      R := []; 
      x := CW[a];
      for b in [1..#E] do 
         y := CW[b];
         e := CW[Position (E, E[a] * E[b])]^-1 * x * y;
         assert e in M;
         Append (~R, e);
      end for;
      Append (~L, R);
   end for;
    
   Homs := [[[alpha (l[i]): i in [1..#l]]: l in L]: alpha in A];

   Homs := [ListToMatrix ([[alpha (l[i]): i in [1..#l], l in L]], U): 
            alpha in A];

   return [<Homs[i], orders[i]>: i in [1..#Homs]];

end intrinsic;

/* return fp-group word w where we map w[i] to F.(w[i] + offset) */

FPWordToFPWord := function (offset, w, F)
   w := Eltseq (w);
   for i in [1..#w] do
      if w[i] lt 0 then w[i] -:= offset; else w[i] +:= offset; end if;
   end for;
   return F!w;

end function;

/* w is an Eltseq element of an fp-group F; rewrite as element  
   of PC-group G where we map F.i -> G.(i) */

FPWordToPCWord := function (w, G)
   // w := Eltseq (f);
   return &*[G.(i): i in w];
end function;

/* return relations of PC-group G as list of relators of associated FP-group */

ListRelators := function (G)

   F, phi := FPGroup (G);
   m := Ngens (F);
  // EOB -- comment out until decision made about which way map goes 
  // assert [F.i @@ phi : i in [1..m]] eq [G.i : i in [1..m]];
   R := Relations (F);
   return [LHS(x) * RHS(x)^-1 : x in R], F;

end function;

/* evaluate i, j entry of component-wise product of matrices in A */

EvaluateEntry := function (A, i, j)

   return &*[A[k][i][j]: k in [1..#A]];

end function;

/* G and U pc-groups, A is cocycle matrix, word is word in F = FPGroup (G) */

ValueOfRelator := function (G, U, A, word: Cocycle := true)

   E := G`Elements;

   product := U ! 1;
   w := Eltseq (word); 
   r := #w;
   for j in [2..r] do
      lhs := FPWordToPCWord ([w[i] : i in [1..j - 1]], G);
      rhs := G.(w[j]);
      a := Position (E, lhs); 
      b := Position (E, rhs); 
      entry := Cocycle select U!A[a][b] else U!EvaluateEntry (A, a, b);
      product *:= U!entry;
   end for;
  
   for i in [1..r] do
      if w[i] lt 0 then
         lhs := G.(Abs (w[i])); rhs := lhs^-1;
         a := Position (E, lhs); 
         b := Position (E, rhs); 
         entry := Cocycle select (U!A[a][b])^-1 else U!EvaluateEntry (A, a, b)^-1;
         product *:= U!entry;
      end if;
   end for;

   return product;

end function;

/* G and U pc-groups; A is cocycle matrix or list of such; if
   A is a list, then Cocycle should be false and relevant entries
   to write down central extension are evaluated as needed */

MyCentralExtension := function (G, U, A: Cocycle := true) 

   /* standard relations */
   m := NPCgens (G); n := NPCgens (U);
   E := FreeGroup (m + n);

   lhs := ListRelators (G);
   rhs := [ValueOfRelator (G, U, A, r: Cocycle := Cocycle) : r in lhs];
   rhs := [ConvertWord (m, r, E) : r in rhs];
   lhs := [Eltseq (x) : x in lhs];
   M := [E!lhs[i] = rhs[i] : i in [1..#lhs]];

   Rels := ListRelators (U);
   Rels := [FPWordToFPWord (m, r, E) : r in Rels];

   Comm := [(E.(m + i), E.j) : i in [1..n], j in [1..m]];

   q := quo < E | Rels, Comm, M>;
   s, phi := SolubleQuotient (q, #G*#U: Print := 0);
   return s, phi, q;

end function;

intrinsic CentralExtension (G:: GrpPC, U:: GrpPC, A:: AlgMatElt) -> GrpPC
{central extension of (abelian) U by G determined by cocyclic matrix A}

   return MyCentralExtension (G, U, A: Cocycle := true);

end intrinsic;

/* generate all elements of Ext or Hom using component multiplication */

ElementsOfComponent := function (Cocycles, U)

   if #Cocycles eq 0 then return Cocycles; end if;

   Orders := [Cocycles[i][2] : i in [1..#Cocycles]];
   Cocycles := [Cocycles[i][1] : i in [1..#Cocycles]];
   Elts := [];
   for i in [1..#Cocycles] do 
      O := Orders[i]; 
      Elts[i] := [];
      for j in [1..O] do
         Elts[i][j] := ComponentMultiplication ([Cocycles[i] : k in [1..j]], U);
      end for;
   end for;

   i := 1;
   E := Elts[1];
 
   while i lt #Elts do 
      j := i + 1;
      E := [ComponentMultiplication ([y, x], U) : y in Elts[j], x in E]; 
      i +:= 1;
   end while;

   return E;
end function;

/* A and B are sequences of generators for an abelian group */

intrinsic AbelianInvariants (Ext:: SeqEnum, Hom:: SeqEnum) -> SeqEnum
{return invariants of abelian group Z^2 (G, U) where U is an abelian group; 
Ext and Hom are generators for Ext (G/G', U) and Hom (H_2 (G), U) respectively} 

   return [(Ext[i][2]) : i in [1..#Ext]] cat [(Hom[i][2]): i in [1..#Hom]];

end intrinsic;

intrinsic RepresentativeCocycles (G :: GrpPC, U :: GrpPC, 
                  Ext :: SeqEnum, Hom :: SeqEnum) -> SeqEnum
{return representative cocycles from G to (abelian) U as cocyclic matrices}

   /* list elements of both components */
   Ext := ElementsOfComponent (Ext, U);
   Hom := ElementsOfComponent (Hom, U);

   if #Hom eq 0 then return Ext; end if;
   if #Ext eq 0 then return Hom; end if;

   /* write down all of the cocycles */
   Cocycles := [];
   for i in [1..#Ext] do
      for j in [1..#Hom] do
        cocycle := ComponentMultiplication ([* Ext[i], Hom[j] *], U);
        Append (~Cocycles, cocycle);
      end for;
   end for;

   vprint Cocycle: "# of cocycles is ", #Cocycles;

   return Cocycles;

end intrinsic;

/* write down presentation for extension */

intrinsic CentralExtensions (G:: GrpPC, U:: GrpPC, Cocycles:: [AlgMatElt])
                             -> SeqEnum
{central extensions of (abelian) U by G determined by Cocycles}

   E := [];
   for i in [1..#Cocycles] do
      E[i] := CentralExtension (G, U, Cocycles[i]);
      vprint Cocycle: "Order of extension is ", #E[i];
   end for;

   return E;

end intrinsic;

intrinsic CentralExtensionProcess (G:: GrpPC, U:: GrpPC) -> Rec
{set up process for central extensions of (abelian) U by G}

   /* list generators for Ext */
   Ext := ExtGenerators (G, U); 

   /* list generating set for Hom */
   Hom := HomGenerators (G, U);

   vprint Cocycle: "Abelian invariants of H are", AbelianInvariants (Ext, Hom);

   /* list elements of both components */
   ElementsExt := ElementsOfComponent (Ext, U);
   ElementsHom := ElementsOfComponent (Hom, U);

   P := rec <CentralRF | ElementsExt := ElementsExt, G := G, U := U,
             ElementsHom := ElementsHom, index := <1,1>>;

   P`complete := #ElementsExt eq 0 and #ElementsHom eq 0;

   return P;

end intrinsic;

intrinsic IsEmpty (P:: Rec) -> BoolElt
{true iff central extension process P is empty}

   return assigned P`complete and P`complete eq true;

end intrinsic;

intrinsic NextExtension (~P:: Rec, ~H) 
{construct next central extension determined by process P}

   if IsEmpty (P) then "Process finished"; return; end if;

   ElementsExt := P`ElementsExt; 
   ElementsHom := P`ElementsHom; 

   index := P`index;
   i := index[1]; j := index[2];

   G := P`G;
   U := P`U;

   if #ElementsHom eq 0 then 
      cocycle := ElementsExt[i]; 
   elif #ElementsExt eq 0 then 
      cocycle := ElementsHom[j]; 
   else 
      cocycle := [ElementsExt[i], ElementsHom[j]];
   end if;

   H := MyCentralExtension (G, U, cocycle: 
                            Cocycle := Type (cocycle) eq AlgMatElt);

   if j lt #ElementsHom then 
      P`index := <i, j + 1>;
   elif i lt #ElementsExt then 
      P`index := <i + 1, 1>;
   else 
      P`complete := true;
   end if;

end intrinsic;

