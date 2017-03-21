freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: representation.m (Sub, Dual, Integral, etc., representations
                           of spaces of modular symbols.)

   $Header: /home/was/magma/packages/modsym/code/RCS/representation.m,v 1.7 2002/02/19 02:25:34 was Exp $

   $Log: representation.m,v $
   Revision 1.7  2002/02/19 02:25:34  was
   Atkin-Lehner stuff.

   Revision 1.6  2002/01/21 00:54:35  was
   nothing.

   Revision 1.5  2001/07/08 17:54:23  was
   Fixed up some of the verbose printing (added \n's).

   Revision 1.4  2001/05/28 17:08:47  was
   increased error checking a little.

   Revision 1.3  2001/05/16 03:25:06  was
   changed comments to VectorSpace.

   Revision 1.2  2001/05/13 03:51:41  was
   Changed ModularForms flag to ModularSymbols.

   Revision 1.1  2001/04/20 04:47:01  was
   Initial revision

   Revision 1.11  2001/04/13 21:32:55  was
   Got rid of taking square-free part of poly when characteristic of base field is > 0.
   I don't know if this change is necessary, but it seems like a good idea.

   Revision 1.10  2001/04/12 19:54:56  was
   nothing.

   Revision 1.9  2000/08/01 04:30:55  was
   Woops; the previous idea is OK, but I had implemented it with the opposite logic.
   When p divides the level, it is necessary to compute the full charpoly, but when
   p does not, since the operators are semisimple, it is OK to compute only the
   square-free part.  IDEA for later: Should I use [Coleman-Edixhoven] here, which
   says the Hecke operators are semisimple when p^3 doesn't divide the level?  What
   are their hypothesis?  Will it make a big difference speed-wise?

   Revision 1.8  2000/08/01 04:22:01  was
   Updated the comment at the end a little.

   Revision 1.7  2000/08/01 04:19:01  was
   Fixed a serious bug introduced by some previous optimization.  The Rev 1.4 note
   says to *not* compute kernel of square-free part only, but for some reason the
   code at present *was* computing the kernel of the square-free part.  In some cases,
   such as the full cuspidal subspace at level 40, wt. 2, trivial character, this gave
   the wrong DualVectorSpace.

   Revision 1.6  2000/06/22 08:25:08  was
   Bravely commented out two assertions about dimensions.  They never really come up except in cases where one doesn't really need the dual space, I hope.

   Revision 1.5  2000/06/03 04:53:20  was
   verbose: ModularForm --> ModularForms

   Revision 1.4  2000/05/09 17:05:17  was
   Don't compute kernel of square-free part of T_p, when p divides the level!  This is wrong because those Hecke operators are *not* semisimple.

   Revision 1.3  2000/05/09 16:47:38  was
   Removed evil "SmallestPrimeNonDivisor" because it spoils the "multiplicity one" assumption!

   Revision 1.2  2000/05/03 11:23:02  was
   Added a DualLattice function, which I forgot.

   Revision 1.1  2000/05/02 08:09:56  was
   Initial revision
  
                                                                            
 ***************************************************************************/

import "linalg.m":    
   Intersect_Vector_Space_With_Lattice,
   KernelOn,
   MakeLattice,
   Restrict,
   RestrictionOfScalars,
   SaturateWithRespectToBasis,
   UnRestrictionOfScalars;

import "multichar.m": 
   MC_Lattice;

import "operators.m": 
   FastTn;

/* This should be made internal-only once the "Representation"
   function below is replaced by "VectorSpace" */

intrinsic Representation(x::ModSymElt) -> ModTupFldElt
{The vector corresponding to x in the underlying 
vector space corresponding to the parent of x.}
   return x`element;
end intrinsic;


intrinsic Representation(M::ModSym) -> ModTupFld, Map, Map
{The vector space V underlying M, the map V --> M, and the map M --> V}

   return VectorSpace(M);
end intrinsic;

intrinsic VectorSpace(M::ModSym) -> ModTupFld, Map, Map
{"} // "
   if not assigned M`sub_representation or 
          Dimension(M`sub_representation) gt Dimension(M) then 

      if Dimension(M) eq 0 then
         M`sub_representation  := M`dual_representation;
         V := M`sub_representation;
         return V, hom< M->V | x:->V!0, x:->M!0 >,
                   hom< V->M | x:->M!0, x:->V!0 >;
      end if;

      vprintf ModularSymbols: "Computing subspace representation of %o\n", M;
      IndentPush(); 

      found_V := false;
      if not assigned M`al_decomp and 
               Dimension(M) gt Degree(M) / 2 then     // sometimes clever trick!?
	 C := Complement(M); // quick --  gets the subspace
	 // representation of the complement
	 _ := DualVectorSpace(C);   // much smaller dimension
	 CompC := Complement(C);
	 if assigned CompC`sub_representation then
	    V := CompC`sub_representation;  // avoid infinite recursion
	    found_V := true;
	 end if;
      end if;

      if not found_V then
         if assigned M`sub_representation then
            V := M`sub_representation;
         else
            V := VectorSpace(AmbientSpace(M));
         end if;
         if assigned M`al_decomp then
            for x in M`al_decomp do
               wp := Restrict(AtkinLehnerOperator(AmbientSpace(M),x[1]),V);
               V  := KernelOn(wp - x[2], V);
            end for;
         end if;

         vprintf ModularSymbols : "Goal dimension = %o, initial dimension = %o.\n",
                                        Dimension(M), Dimension(V);

 // TO DO: try skipping small p that divide the level, if they probably
 // won't cut down the space much, and Evaluate is likely to be awful ...
 // For the moment, try skipping but if it turns out that the other primes
 // up to the Hecke bound aren't enough, go back and use the skipped primes
 skipped_small_primes := [];
 do_skipped_small_primes := false;

         p := 2;
         while Dimension(V) gt Dimension(M) do   
            if assigned M`al_decomp and Level(M) mod p eq 0 then
               p := NextPrime(p); 
               continue;
            end if;

 if do_skipped_small_primes and #skipped_small_primes gt 0 then
     p := skipped_small_primes[#skipped_small_primes];
     Prune(~skipped_small_primes);
     vprintf ModularSymbols, 1: "Using %o after all\n", p;
 elif p in {2,3,5,7} and Level(M) mod p eq 0 then
     vprintf ModularSymbols, 1: "Skipping %o\n", p;
     Append( ~skipped_small_primes, p);
     p := NextPrime(p);
     continue;
 end if;

            Tp := Restrict(HeckeOperator(AmbientSpace(M),p),V);
            Tquo := DualHeckeOperator(M,p);
            cp := CharacteristicPolynomial(Tquo);
            R<x> := Parent(cp);
            vprintf ModularSymbols, 3: "charpoly = %o\n", cp; 

            if Level(M) mod p ne 0  and Characteristic(BaseField(M)) eq 0 then
//"VectorSpace: Evaluate (", #Factorization(cp), "calls) on", BaseRing(Parent(cp)), "and", BaseRing(Tp); time
               fT := &*[Evaluate(f[1],Tp) : f in Factorization(cp)];
//          elif Characteristic(BaseField(M)) eq 0 then
//"VectorSpace: Evaluate, using non-squarefree factorization ... old:"; time
//             fT := Evaluate(cp, Tp);
//" ... new:"; time
//             fT := &*[ Evaluate(f[1],Tp)^f[2] : f in Factorization(cp)];
            else
//"VectorSpace: Evaluate on", BaseRing(Parent(cp)), "and", BaseRing(Tp); time
               fT := Evaluate(cp, Tp);
            end if;

            V  := KernelOn(fT,V);

	    if p gt HeckeBound(M) and Dimension(V) gt Dimension(M) then
 if not IsEmpty(skipped_small_primes) then
   do_skipped_small_primes := true;
   continue;
 end if;
	       if Characteristic(BaseField(M)) eq 0 then
		  print "Modular Symbols WARNING: VectorSpace -- algorithm failed.";
	       end if;
               break;
            end if;

            vprintf ModularSymbols: "After using p = %o, dimension = %o\n", p, Dimension(V);

            p  := NextPrime(p);
         end while;
         if Dimension(V) ne Dimension(M)  and Characteristic(BaseField(M)) eq 0 then
            error "An error occurred computing the vector space.";
         end if;
      end if;


/*
REMARK:  Do you wish that the equality

     DualHeckeOperator(M,p) = Transpose(HeckeOperator(M,p))

held?   If so,  DE-COMMENT THE FOLLOWING CODE.  
HOWEVER, THIS CHOICE OF BASIS IS NOT ASSUMED ANYWHERE IN THE
REST OF MY CODE.  Also, computing the inverse below could 
take a lot of time. 

      // Replace Basis(V) by rows of Basis(V)*(DualRepresentation(M)*V)^(-1)
      // so that the matrices of DualHeckeOperator's will be the transposes
      // of the HeckeOperators. 

      MA:= RMatrixSpace(BaseField(M),Dimension(M),Degree(M)); 
      B := Transpose(MA!Basis(V));
      S := MA!Basis(M`dual_representation);
      A := B*(S*B)^(-1);
      V := VectorSpaceWithBasis(Transpose(A));
*/
      M`sub_representation := V;
      IndentPop(); 

   end if;

   V := M`sub_representation;
   return V, hom< V->M | x :-> M!x, x :-> V!Eltseq(x) >, 
             hom< M->V | x :-> V!Eltseq(x), x :-> M!x >;
end intrinsic;


intrinsic DualRepresentation(M::ModSym) -> ModTupFld, Map, Map
{Same as DualVectorSpace}
   return DualVectorSpace(M);
end intrinsic;

intrinsic DualVectorSpace(M::ModSym) -> ModTupFld
{The subspace of the dual space of VectorSpace(AmbientSpace(M)) 
that is isomorphic to M as module of the Hecke algebra}

   if not assigned M`dual_representation or 
      Dimension(M`dual_representation) gt Dimension(M) then // already partially computed using sub_representation

      if Dimension(M) eq 0 then
         M`dual_representation  := M`sub_representation;
         return M`dual_representation;
      end if;

      vprintf ModularSymbols: "Computing DualVectorSpace of %o\n", M;
      IndentPush();

      found_V := false;
      if not assigned M`al_decomp and 
             Dimension(M) gt Degree(M) / 2 then
         C := Complement(M); // instant, gets the dual representation of complement
	 _ := VectorSpace(C);   // much smaller dimension
	 CompC := Complement(C);
	 if assigned CompC`dual_representation then
	    V := CompC`dual_representation;
	    found_V := true;
	 end if;
      end if;

      if not found_V then
	 if assigned M`dual_representation then
            V := M`dual_representation;
         else
            V := DualVectorSpace(AmbientSpace(M));
         end if;

         if assigned M`al_decomp then
            for x in M`al_decomp do
               wp := Restrict(DualAtkinLehnerOperator(AmbientSpace(M),x[1]),V);
               V  := KernelOn(wp - x[2], V);
            end for;
         end if;

         vprintf ModularSymbols : "Goal dimension = %o.\n",Dimension(M);

         p := 2;
         while Dimension(V) gt Dimension(M) do
            if assigned M`al_decomp and Level(M) mod p eq 0 then
               p := NextPrime(p); 
               continue;
            end if;

            Tp := FastTn(AmbientSpace(M),V,p);
            // We do the following to avoid an infinite recursion, since
            // the optimized HeckeOperator on subspaces *uses* ProjectionMatrix
            // which calls Complement, which in turn calls us!  All the full
            // space the ProjectionMatrix problem doesn't arise.
            Tsub := Restrict(HeckeOperator(AmbientSpace(M),p), VectorSpace(M));

            cp := CharacteristicPolynomial(Tsub);
 
            vprintf ModularSymbols, 3: "charpoly = %o\n", cp;
//"DualVectorSpace: Evaluate on", BaseRing(Parent(cp)), "and", BaseRing(Tp); time
            if Level(M) mod p ne 0  and Characteristic(BaseField(M)) eq 0 then
               fT := &*[Evaluate(f[1],Tp) : f in Factorization(cp)];
            else
               fT := Evaluate(cp, Tp);
            end if;
            
            V  := KernelOn(fT,V);
  
            if p gt HeckeBound(M) and Dimension(V) gt Dimension(M) then
	       if Characteristic(BaseField(M)) eq 0 then
                  print "M = ", M; print "Dim V = ", Dimension(V);
		  print "Modular Symbols WARNING: DualVectorSpace -- algorithm failed.";
	       end if;
	       break;
            end if;

            vprintf ModularSymbols: "  p = %o,   dimension = %o.\n",p,Dimension(V);

            p := NextPrime(p);
         end while;
         if Dimension(V) ne Dimension(M)  and Characteristic(BaseField(M)) eq 0 then
            error "An error occurred computing the dual vector space.";
         end if;
      end if;

/*
 // (See the comment above, in Representation)

      // Replace Basis(V) by rows of (V*Representation(M))^(-1)*Basis(V), 
      // so that the matrices of DualHeckeOperator's will be the transposes
      // of the HeckeOperators. 

      MA:= RMatrixSpace(BaseField(M),Dimension(M),Degree(M)); 
      B := MA!Basis(V);
      S := Transpose(MA!Basis(M`sub_representation));
      A := (B*S)^(-1)*B;
      V := VectorSpaceWithBasis(A);
*/

      M`dual_representation := V;
      IndentPop();

   end if;

   return M`dual_representation;
end intrinsic;


/*
  INTEGRAL STRUCTURE:
  Algorithm: Compute basis for the *lattice* generated by the
  Manin symbols [X^iY^(k-2-i),(u,v)].
 */

intrinsic Lattice(M::ModSym) -> Lat, Map

{A basis over the integers for the integral modular symbols in 
the VectorSpace(M).  This is the intersection 
of M with the Z-lattice generated by all modular 
symbols X^iY^(k-2-i)\{a,b\}.   The base field 
of M must be RationalField().}

   L := IntegralRepresentation(M);
   // map into ambient space, since if map into M
   // then MAGMA tries to coerce down to M and this
   // takes lots of extra time.
   if Type(BaseField(M)) eq FldRat then
      f := hom< L->AmbientSpace(M) | x :-> M!x >;
   else
      f := hom< L->AmbientSpace(M) | x :-> M!UnRestrictionOfScalars(x,BaseField(M)) >;  
   end if;

   return L, f;
end intrinsic;

function ORIGINAL_FindLatticeOfSubspace(M)
   Z := Lattice(AmbientSpace(M));
   V := VectorSpace(M);
   if Type(BaseField(M)) ne FldRat then
      B := Basis(BaseField(M));
      V := VectorSpaceWithBasis([RestrictionOfScalars(V!Eltseq(b*v)) 
                 : v in Basis(M), b in B]);
   end if;
   t := Cputime();
   vprint ModularSymbols, 2 : 
       "Intersecting vector space with lattice.";
   L := Intersect_Vector_Space_With_Lattice(V, Z);
   vprintf ModularSymbols, 2 : 
       "Intersecting time = %o seconds\n", Cputime(t);
   return L;
end function;

function FindLatticeOfSubspace(M)
   assert Type(M) eq ModSym;
   assert not IsAmbientSpace(M);

   W := Complement(M);
   /* The lattice we want is the kernel of pi restricted to L. 
      Algorithm:
        (1) Compute Q-matrix with respect to basis of M and
            basis of W.   
        (2) Change to matrix so wrt to basis of L and W.
        (3) Let d be a multiple of all denominators in this basis.
        (4) Replace matrix by d times it.
        (5) Find *integer* kernel. 
        (6) This is the kernel of pi restricted to L.
   */

   pi := ProjectionMatrix(W);     // from ambient space to W.
   if Type(BaseField(M)) ne FldRat then
      pi := RestrictionOfScalars(pi);
   end if;
   L := Lattice(AmbientSpace(M));

   // To change to L basis, premultiply by matrix whose rows are
   // the basis for L. 
   L_to_std := RMatrixSpace(RationalField(),Rank(L),Degree(L))!
                   &cat[Eltseq(b) : b in Basis(L)];
   A := L_to_std*pi;
   d := LCM([Denominator(x) : x in Eltseq(A)]);
   A := d*A;
   B := RMatrixSpace(IntegerRing(),Nrows(A), Ncols(A))!Eltseq(A);
   basisM := Basis(Kernel(B));
   // the elements of basis are the linear combination of Basis(L) that
   // form the lattice we want:
   basisL := Basis(L);
   Z := [&+[basisL[i]*b[i] : i in [1..Rank(L)]] : b in basisM];
   ans := MakeLattice(Z);
   // assert ans eq ORIGINAL_FindLatticeOfSubspace(M);
   return ans;
end function;

intrinsic IntegralRepresentation(M::ModSym) -> Lat
{A basis over the integers for the integral modular symbols in 
the vector space representation of M.  This is the intersection 
of M with the Z-lattice generated by all modular 
symbols X^iY^(k-2-i)\{a,b\}.  If the base field is a number field
not equal to Q, then we view M as a Q-vector space using restriction
of scalars, and return a lattice and set-theoretic map from 
the lattice to M.}

   require Characteristic(BaseField(M)) eq 0 : 
              "Argument 1 must be over a field of characteristic zero.";
   if not assigned M`sub_integral_representation then

      vprintf ModularSymbols, 2 : "Finding lattice of %o.\n", M;

      if Dimension(M) eq 0 then
         M`sub_integral_representation := Representation(M);
      elif IsAmbientSpace(M) and IsMultiChar(M) then
         M`sub_integral_representation := MC_Lattice(M);
      else
         if IsAmbientSpace(M) then
            // It suffices to consider lattice generated by the free 
            // generating symbols X^iY^(k-2-i).(u,v)
            // after modding out by only the S(and I) relations which don't
            // change integrality at all. (They just flip things 
            // around or change signs.) 
            Q    := M`quot;
            gens := [ Q`Scoef[i]*Q`Tquot[Q`Squot[i]] : i in [1..#Q`Squot] ];
            if Type(BaseField(M)) eq FldRat then
            n    := #Q`Tgens;
               gens := [g[i] :  i in [1..n], g in gens];
               L := Lattice(n,gens);
            else
               B := Basis(BaseField(M));
               gens := [RestrictionOfScalars(b*g) : g in gens, b in B];
               L := MakeLattice(gens);
            end if;
            M`sub_integral_representation := L;

	 else
            t := Cputime();
            M`sub_integral_representation := 
                          FindLatticeOfSubspace(M);
            vprintf ModularSymbols, 2: "Time to compute lattice: %o seconds\n", Cputime(t);
         end if;

      end if;
   end if;
   return M`sub_integral_representation;
end intrinsic;




function DualIntegralRepresentation(M)
//{A Z-basis for the Z-module of integral modular symbols 
// in the dual representation of M.}
   assert Type(M) eq ModSym;

   if not assigned M`dual_integral_representation then
      if Dimension(M) eq 0 then
         M`dual_integral_representation := DualRepresentation(M);
      else
         if M eq AmbientSpace(M) then
            S := Basis(IntegralRepresentation(M));
            V := Representation(AmbientSpace(M));
            A := MatrixAlgebra(BaseField(M),#S)![V!b : b in S];
            Dual := A^(-1);
            M`dual_integral_representation := Lattice(
                 RMatrixSpace(BaseField(M),#S,#S)!Dual);
         else
            Z := DualIntegralRepresentation(AmbientSpace(M));
            V := Representation(AmbientSpace(M));
            BV  := [V!b : b in Basis(Z)];
            M`dual_integral_representation := 
               SaturateWithRespectToBasis(DualRepresentation(M),BV);

         end if;
      end if;
   end if;
   return M`dual_integral_representation;
end function;


intrinsic DualLattice(M::ModSym) -> Lat, Map

{A basis over the integers for the integral modular symbols in 
the DualVectorSpace(M).  The base field 
of M must be RationalField().}

   require BaseField(M) cmpeq RationalField() :
        "The base field of M must be RationalField().";
   L := DualIntegralRepresentation(M);
   f := hom< L->M | x :-> M!x>;

   return L, f;
end intrinsic;


function IntegralCuspidalRepresentation(M) 
//{Computes integral representation of M with respect to a fixed integral basis
// for the cuspidal part of the root of M.}
   assert IsCuspidal(M);// : "Argument 1 must be cuspidal.";
   if not assigned M`sub_integral_cuspidal_representation then
      C := CuspidalSubspace(AmbientSpace(M));
      d := Dimension(C);
      L := Lattice(RMatrixSpace(Rationals(),d,d)!MatrixAlgebra(Rationals(),d)!1);
      M`sub_integral_cuspidal_representation := 
          sub<L|[Coordinates(IntegralRepresentation(C), x) :     
                        x in Basis(IntegralRepresentation(M))]>;
   end if;
   return M`sub_integral_cuspidal_representation;
end function;


function DualIntegralCuspidalRepresentation(M) 
//{Integral subspace of integral dual of CuspidalSubspace(AmbientSpace(M)) 
// corresponding to M.}
   assert IsCuspidal(M);// : "Argument 1 must be cuspidal.";
   if not assigned M`dual_integral_cuspidal_representation then
   /* Algorithm: take image in Hom(S_k,Q) and saturate with
      respect to the lattice Hom(S_k,Z).  This is more efficient than
      computing Hom(S_k,Z)[I_M]. */
      D    := RMatrixSpace(Rationals(),Dimension(M),Degree(M))
                 !Basis(DualRepresentation(M));  
      V    := VectorSpace(Rationals(),Degree(M));
      C    := CuspidalSubspace(AmbientSpace(M));
      SkZ  := Transpose(RMatrixSpace(Rationals(),Dimension(C),Degree(C))
                 ![V!b : b in Basis(IntegralRepresentation(C))]);
      DSkZ := D*SkZ;  // the rows are the image in Hom(S_k,Q).
      // Now saturate the rows.
      M`dual_integral_cuspidal_representation :=
               SaturateWithRespectToBasis(RowSpace(DSkZ),
                                          Basis(RowSpace(SkZ))); 
   end if;      
   return M`dual_integral_cuspidal_representation;
end function;





/*************************************************************
 Possibly very out of date IMPORTANT NOTE about 
 dual_representation and sub_representation...

  Subspaces of spaces of modular symbols are represented 
  simultaneously both as a subspace of a vector space V and 
  as a subspace of the linear dual Hom(V,K).   A significant
  proportion of the algorithms draw on information from 
  both the subspace and dual subspace, so it is essential
  to carry this extra information around.  Philosophically, we are
  forced to do this because we know of no EASY TO COMPUTE 
  natural Hecke-invariant nondegenerate inner product on modular
  symbols.  The cup product pairing on homology might answer
  this requirement, but I don't yet know a very fast way to 
  compute it.

  For efficiency, an object is created with at least one, but
  not necessarily both, of these attributes correct.  In general,
  dual_representation contains the *true* dual_representation. 
  To determine whether or not they are equal, simply compare
  dimensions:
  
       Dimension(dual_representation) eq Dimension(M).

  The functions calls DualRepresentation() and Representation() 
  should work as stated; in particular, it is not necessary
  to worry about the above unless you wish to muck with 
  the dual_representation and sub_representation attributes. 

  A possible serious problem: It's conceivable, due to a mistake 
  below or some sneaky user tricks,  that it isn't possible to compute
  DualRepresentation given Representation, or vice-versa.  I don't 
  know of any examples like this. 
  
  Another note:  "Representation(M) eq M`sub_representation."
 *************************************************************/
       
