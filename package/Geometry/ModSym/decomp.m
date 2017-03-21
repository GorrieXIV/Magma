freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                          
                  HECKE:  Modular Symbols in Magma                         
                           William A. Stein                               
                                                                         
  FILE: decomp.m (Decomposition)                                        
                                                                       
  $Header: /home/was/magma/packages/ModSym/code/RCS/decomp.m,v 1.20 2002/10/01 06:02:33 was Exp $

  $Log: decomp.m,v $
  Revision 1.20  2002/10/01 06:02:33  was
  nothing.

  Revision 1.19  2002/02/19 02:32:23  was
  Atkin-Lehner stuff

  Revision 1.18  2002/02/19 02:25:25  was
  AtkinLehner stuff.

  Revision 1.17  2002/01/21 01:07:43  was
  Added AtkinLehnerFactor.

  Revision 1.16  2001/07/27 20:25:07  was
  BaseExtend --> ChangeRing.

  Revision 1.15  2001/07/26 19:37:43  was
  Increaded the verbosity.

  Revision 1.14  2001/07/17 07:17:51  was
  Removed sqfree operator caching.

  Revision 1.13  2001/07/17 07:15:24  was
  Added caching of sqfree_new_operator.

  Revision 1.12  2001/07/14 00:43:06  was
  Finished writing NewformDecomposition when the sign is 0.

  Revision 1.11  2001/07/14 00:06:16  was
  Fill in associated_new_space in
     complete_decomposition_of_a_new_subspace.

  Revision 1.10  2001/07/08 18:46:34  was
  ...

  Revision 1.9  2001/07/08 18:45:23  was
  Added fast decomposition over cyclotomic fields.

  Revision 1.8  2001/07/06 00:56:09  was
  ...

  Revision 1.7  2001/06/17 03:23:04  was
  Additional changes related to Allan's optimizations.

  Revision 1.6  2001/06/12 05:52:04  was
  Lots of optimization of Allan.

  Revision 1.5  2001/05/23 04:51:44  was
  nothing

  Revision 1.4  2001/05/13 04:56:59  was
  fixed ModularSymbols comment.

  Revision 1.3  2001/05/13 03:46:38  was
  Changed verbose flag ModularForms to ModularSymbols.

  Revision 1.2  2001/04/29 02:56:19  was
  Cleaned up comment for "intrinsic ModularSymbols(E::CrvEll, K::Fld, sign::RngIntElt
     : stop := 0 ) -> ModSym"

  Revision 1.1  2001/04/20 04:46:07  was
  Initial revision

  Revision 1.14  2001/04/14 01:19:09  was
  Got rid of the Eisenstein/Cuspidal decomposition in Decomposition when
  Sign(M) eq 0.  I did this because (1) Such behavior is *not* part of
  the definition of Decomposition, and (2) It broke decomposition over
  finite fields.

  Revision 1.13  2001/04/13 21:24:08  was
  got rid of irreducibility test in characteristic p, because it is too hard
  to cut out the subspace.

  Revision 1.12  2001/04/13 20:44:33  was
  Changed from consider the dimension of the PlusSubspaceDual to considering
  whether or not the DualStarInvolution acts as a scalar.

  Revision 1.13  2001/03/22 00:14:27  was
  Nothing.

  Revision 1.12  2001/03/21 20:02:56  was
  Fixed a bug in decomposition; "IsIrreducible" failed for the
  Eisenstein subspace.

  Revision 1.11  2001/01/28 08:49:32  was
  Allow SortDecomposition even if all spaces aren't new.

  Revision 1.10  2001/01/16 09:57:37  was
  nothing.

  Revision 1.9  2000/08/01 04:33:24  was
  And then replaced an accidental BaseField by BaseRing!  (For a CrvEll.)

  Revision 1.8  2000/07/29 09:54:31  was
  Replaced accidental BaseRing by BaseField

  Revision 1.7  2000/07/29 06:50:37  was
  Added a "faster" algorithm for finding ModularSymbols(elliptic curve).
  It turns out to be way way slower!
  So, it is not the default.

  Revision 1.6  2000/07/29 01:49:36  was
  Extended the ModularSymbols(elliptic curve) function to allow
  for nontrivial sign.  Nothing else.  Later, will use this to
  optimize computation when sign is 0.

  Revision 1.5  2000/07/24 02:15:13  was
  Changed CurveEll to CrvEll

  Revision 1.4  2000/06/03 04:49:38  was
  verbose

  Revision 1.3  2000/06/03 03:19:47  was
  TraceOfFrobenius --> Trace

  Revision 1.2  2000/05/02 20:39:36  was
  Removed requirement on base field in EllipticFactors.

  Revision 1.1  2000/05/02 07:59:08  was
  Initial revision


 ***************************************************************************/

import "arith.m"  : DotProd,
                    IsogenyCodeToInteger,
                    PrimeSeq,
                    SmallestPrimeNondivisor;

import "linalg.m" : KernelOn,
                    MyCharpoly;

import "modsym.m" : ModularSymbolsDual,
                    ModularSymbolsSub;

import "multichar.m": MC_Decomposition,
                      MC_DecompositionOfCuspidalSubspace,
                      MC_DecompositionOfNewCuspidalSubspace,
                      MC_NewformDecompositionOfCuspidalSubspace,
                      MC_NewformDecompositionOfNewCuspidalSubspace;

import "operators.m":FastTn;

import "subspace.m":  MinusSubspaceDual,
                      PlusSubspaceDual;

import "subspace.m":  MinusSubspace,
                      PlusSubspace;

forward             NewformDecompositionOfNewNonzeroSignSpaceOverQ,
                    NewformDecompositionOfNewNonzeroSignSpaceOverCyclo,
                    QuickSort;

declare attributes CrvEll: /* MW 18 Nov 2010 */
 ModularSymbolsMinus, ModularSymbolsPlus, ModularSymbolsZero;

function SimpleIrreducibleTest(W,a,elliptic_only)

   // a is the exponent of the factor of the charpoly.
   
   if not elliptic_only then   // we care about all factors, not just elliptic curve factors.
      if a eq 1 then
	 return true;
      end if;
      
      if a eq 2 then
	 if Sign(W) eq 0 and IsCuspidal(W) and
	    Dimension(Kernel(DualStarInvolution(W)-1)) eq Dimension(W)/2 then
	    return true;
	    
	 end if;
      end if;

   else
      
      if Sign(W) eq 0 and Dimension(W) eq 2 then
	 return true;
      end if;
      if Sign(W) ne 0 and Dimension(W) eq 1 then
	 return true;
      end if;

   end if;
   
   return false;

end function;

function W_is_irreducible(W,a,elliptic_only, random_operator_bound)
   /*
   W = subspace of the dual
   a = exponent of factor of the characteristic polynomial.
   */

   irred := SimpleIrreducibleTest(W,a,elliptic_only);

   if irred then
      return true;
   end if;

   if random_operator_bound gt 1 then
      if IsVerbose("ModularSymbols") then 
         printf "Trying to prove irreducible using random sum of Hecke operators.\n";
      end if;
      V := Sign(W) ne 0 select W else PlusSubspaceDual(W);
      T := &+[Random([-3,-2,-1,1,2,3])*DualHeckeOperator(V,ell) : 
                ell in PrimeSeq(2,random_operator_bound)];
      f := CharacteristicPolynomial(T);
      if IsVerbose("ModularSymbols") then 
         printf "Charpoly = %o.\n", f;
      end if;
      if IsIrreducible(f) then
         return true;
      end if;
   end if;

   return false;  

end function;
        

function Decomposition_recurse(M, p, stop, 
                               proof, elliptic_only, random_op)

   assert Type(M) eq ModSym;
   assert Type(p) eq RngIntElt;
   assert IsPrime(p);
   assert Type(stop) eq RngIntElt;
   assert Type(proof) eq BoolElt;
   assert Type(elliptic_only) eq BoolElt;
   assert Type(random_op) eq BoolElt;

   // Compute the Decomposition of the subspace V of DualRepresentation(M)
   // starting with Tp.
   if Dimension(M) eq 0 then
      return [];
   end if;

   p := SmallestPrimeNondivisor(Level(M),p);

   if p gt stop then   // by definition of this function!
      return [M];
   end if;
   

   vprintf ModularSymbols, 1 : "Decomposing space of level %o and dimension %o using T_%o.\n",Level(M),Dimension(M), p;
   vprintf ModularSymbols, 2 : "\t\t(will stop at %o)\n", stop;

   T := DualHeckeOperator(M, p);
   D := [ ];

   if not elliptic_only then
      if GetVerbose("ModularSymbols") ge 2 then
         t := Cputime();
         printf "Computing characteristic polynomial of T_%o.\n", p;
      end if;
      f := MyCharpoly(T,proof);
      if GetVerbose("ModularSymbols") ge 2 then
         f;
         printf "\t\ttime = %o\n", Cputime(t);
         t := Cputime();
         printf "Factoring characteristic polynomial.\n";
      end if;
      FAC := Factorization(f);
      if GetVerbose("ModularSymbols") ge 2 then
         FAC;
         printf "\t\ttime = %o\n", Cputime(t);
      end if;
   else
      R := PolynomialRing(BaseField(M)); x := R.1;
      FAC := [<x-a,1> : a in [-Floor(2*Sqrt(p))..Floor(2*Sqrt(p))]];
   end if;

   for fac in FAC do
      f,a := Explode(fac);
      if Characteristic(BaseField(M)) eq 0 then
         fa := f;
      else
         fa := f^a;
      end if;
      vprintf ModularSymbols, 2: "Cutting out subspace using f(T_%o), where f=%o.\n",p, f;
      fT  := Evaluate(fa,T);
      V   := KernelOn(fT,DualRepresentation(M));
      W   := ModularSymbolsDual(M,V);
      if assigned M`sub_representation then
         W`sub_representation := M`sub_representation;
      end if;    

      if elliptic_only and Dimension(W) eq 0 then
          continue;
      end if;

      if Dimension(W) eq 0 then
          error "WARNING: dim W = 0 factor; shouldn't happen.";
      end if;

      if Characteristic(BaseField(W)) eq 0 and W_is_irreducible(W,a,elliptic_only, random_op select p else 0) then
	 W`is_irreducible := true;
         Append(~D,W); 
      else
         if not assigned W`is_irreducible then
            if NextPrime(p) le stop then
               q    := Dimension(W) eq Dimension(M) select NextPrime(p) else 2;
               Sub  := Decomposition_recurse(W, q, stop, 
                                             proof, elliptic_only, random_op); 
               for WW in Sub do 
                  Append(~D, WW);
               end for;
            else
               Append(~D,W);
            end if;
         end if;
      end if;
   end for;
   return D;
end function;

procedure SortDecomp(~D)
   cmp := func<A, B | Dimension(A) - Dimension(B)>;
   Sort(~D, cmp);
end procedure;

intrinsic Decomposition(M::ModSym, bound::RngIntElt :
   Proof := true) -> SeqEnum
{Decomposition of M with respect to the Hecke operators T_p with
p coprime to the level of M and p<= bound. }

   if IsMultiChar(AmbientSpace(M)) then
      if IsAmbientSpace(M) then
         return MC_Decomposition(M, bound);
      elif M eq CuspidalSubspace(AmbientSpace(M)) then
         return MC_DecompositionOfCuspidalSubspace(AmbientSpace(M),bound);
      elif M eq NewSubspace(CuspidalSubspace(AmbientSpace(M))) then
         return MC_DecompositionOfNewCuspidalSubspace(AmbientSpace(M),bound);
      end if;
   end if;

   if Characteristic(BaseField(M)) eq 0 then
      UseDualSpace := true;     // totally safe.
   else
      UseDualSpace := false;    // it's too dangerous, though I might make it an option.
   end if;

   if Dimension(M) eq 0 then
      return [];
   end if;

   if not assigned M`decomposition then   

      RF := recformat <
      bound  : RngIntElt,              // bound so far
      decomp : SeqEnum    // subspace of DualVectorSpace(M)
      >;

      D := [DualVectorSpace(M)];

      M`decomposition := rec < RF | bound := 0, decomp := D>;
   end if;

   decomp := [ModularSymbolsDual(M,V) : V in (M`decomposition)`decomp];
   known  := (M`decomposition)`bound;
   if bound le known then
      SortDecomp(~decomp);
      return decomp;
   end if;

   // refine decomp 
   refined_decomp := &cat[Decomposition_recurse(MM,NextPrime(known),
                                          bound,Proof, false, false) :
                          MM in decomp];
         
   (M`decomposition)`bound := bound;
   (M`decomposition)`decomp := [DualVectorSpace(MM) : MM in refined_decomp];

   SortDecomp(~refined_decomp);
   return refined_decomp;
end intrinsic;


function build_dual_modsym_from_plus_and_minus(M, Dplus, Dminus)
   assert Type(M) eq ModSym;
   assert Type(Dplus) eq ModSym;
   assert Type(Dminus) eq ModSym;
   Vplus := DualVectorSpace(Dplus);
   Vminus := DualVectorSpace(Dminus);

   return ModularSymbolsDual(M,Vplus + Vminus);
end function;


function index_of_newform_space_with_same_traces(A,D)
   /* Exactly one of the modular symbols spaces in D is 
      the minus one version of A.  This function returns
      that space. */
   assert Type(A) eq ModSym;
   assert Type(D) eq SeqEnum;

   // first, consider only those spaces with the same dimension.
   D := [B : B in D | Dimension(B) eq Dimension(A)];

   // now try to shrink D using traces
   p := 2;
   while #D gt 1 do
      p := SmallestPrimeNondivisor(Level(A),p);
      ap := Trace(DualHeckeOperator(A,p));
      n := #D;
      for i in [0..n-1] do
         if Trace(DualHeckeOperator(D[n-i],p)) ne ap then
            Remove(~D,n-i);
         end if;
      end for;
      p := NextPrime(p);
   end while;

   assert #D eq 1;
   return D[1];
end function;


function match_up_plus_and_minus(M, Dplus, Dminus)
   assert Type(M) eq ModSym;
   assert Type(Dplus) eq SeqEnum;
   assert Type(Dminus) eq SeqEnum;

   D := [];
   for i in [1..#Dplus] do   
      // Find the entry of Dminus that has the same eigenvalues as Dplus[i].
      plus := Dplus[i];
      minus := index_of_newform_space_with_same_traces(plus, Dminus);
      A := build_dual_modsym_from_plus_and_minus(M, plus, minus);
      if assigned plus`sub_representation then
         A`sub_representation := VectorSpace(plus) + VectorSpace(minus);
      end if;
      Append(~D, A);
   end for;
   return D;
end function;


function complete_decomposition_of_a_new_subspace(M)
   assert Type(M) eq ModSym;
   assert IsNew(M);

   t := Cputime();

   if Type(BaseField(M)) eq FldRat then
      if Sign(M) ne 0 then
         D := NewformDecompositionOfNewNonzeroSignSpaceOverQ(M);      

      else  // break up into +1 and -1 subspaces, decompose, then put back together
         Mplus  := PlusSubspace(M);
         Mminus := MinusSubspace(M);
         Mplus`is_new := true;
         Mminus`is_new := true;
         Dplus := NewformDecompositionOfNewNonzeroSignSpaceOverQ(Mplus);
         Dminus := NewformDecompositionOfNewNonzeroSignSpaceOverQ(Mminus);
         assert #Dplus eq #Dminus;
         D := match_up_plus_and_minus(M, Dplus, Dminus);
      end if;

   elif Type(BaseField(M)) eq FldCyc then
      if Sign(M) ne 0 then
         D := NewformDecompositionOfNewNonzeroSignSpaceOverCyclo(M);
      else
         Mplus  := PlusSubspaceDual(M);
         Mminus := MinusSubspaceDual(M);
         Mplus`is_new := true;
         Mminus`is_new := true;
         Dplus := NewformDecompositionOfNewNonzeroSignSpaceOverCyclo(Mplus);
         Dminus := NewformDecompositionOfNewNonzeroSignSpaceOverCyclo(Mminus);
         assert #Dplus eq #Dminus;
         D := match_up_plus_and_minus(M, Dplus, Dminus);
      end if;
   else
      D := Decomposition_recurse(M, 2,
                   HeckeBound(M), true, false, true);
   end if;

   for i in [1..#D] do
      D[i]`associated_new_space := true;
      D[i]`is_new := true;
   end for;

   return D;
end function;

function image_of_old_newform_factor_using_degen_maps(M, A)
   assert Type(M) eq ModSym;
   assert Type(A) eq ModSym;
   return AmbientSpace(M)!!A;
end function;

function image_of_old_newform_factor_using_operators(M, A)
   assert Type(M) eq ModSym;
   assert Type(A) eq ModSym;
   numdiv := NumberOfDivisors(Level(M) div Level(A));
   d := Dimension(A) * numdiv;
   V := CuspidalSubspace(AmbientSpace(M));
   p := 2;
   while Dimension(V) gt d do
      p := SmallestPrimeNondivisor(Level(M),p);
      f := HeckePolynomial(A,p);
      if Characteristic(BaseField(M)) ne 0 then
         f := f^numdiv;
      end if;
      V := Kernel([<p,f>], V);
      p := NextPrime(p);
   end while;         
   error if Dimension(V) ne d, "Bug in image_of_old_newform_factor_using_operators";
   return V;
end function;

function image_of_old_newform_factor(M, A)
   assert Type(M) eq ModSym;
   assert Type(A) eq ModSym;
   assert IsNew(A);
   assert IsIrreducible(A);
   assert IsCuspidal(M);
   assert Level(M) mod Level(A) eq 0;
   if Level(M) eq Level(A) then
      return A;
   end if;
   d := Level(M) div Level(A);
   if IsPrime(d) then
      return image_of_old_newform_factor_using_degen_maps(M,A);
   else
      return image_of_old_newform_factor_using_operators(M,A);
   end if;
end function;

intrinsic NewformDecomposition(M::ModSym
           : Proof := true, Sort := true) -> SeqEnum
{Decomposition of M into factors corresponding to 
the Galois conjugacy classes of newforms of level 
a divisor of the level of M. We require that
IsCuspidal(M) is true.}

   require Type(BaseField(M)) in {FldRat, FldCyc, FldNum} :
      "The base field must be either the rationals, a cyclotomic field, or a number field.";

   if Dimension(M) eq 0 then
      return [];
   end if;

   if HasAssociatedNewSpace(M) then
      return [M];
   end if;

   require IsCuspidal(M) : "Argument 1 must be cuspidal.";

   if IsNew(M) and assigned M`is_irreducible and M`is_irreducible then
      M`associated_new_space := true;
      return [M];
   end if;

   if not assigned M`newform_decomposition then
      vprintf ModularSymbols : "Doing decomposition of %o\n",M;

      if IsMultiChar(AmbientSpace(M)) then
         if M eq CuspidalSubspace(AmbientSpace(M)) then
            M`newform_decomposition := MC_NewformDecompositionOfCuspidalSubspace(AmbientSpace(M));
         elif M eq NewSubspace(CuspidalSubspace(AmbientSpace(M))) then
            M`newform_decomposition := MC_NewformDecompositionOfNewCuspidalSubspace(AmbientSpace(M));
         else
            D := NewformDecomposition(CuspidalSubspace(AmbientSpace(M)));
            M`newform_decomposition := [A : A in D | A subset M];
         end if;
         if Sort then
            M`newform_decomposition := TraceSortDecomposition(M`newform_decomposition);
         end if;
         return M`newform_decomposition;
      end if;

      if IsNew(M) then
         D := complete_decomposition_of_a_new_subspace(M);
         M`newform_decomposition := Sort select SortDecomposition(D) else D;
         return M`newform_decomposition;
      end if;

      D := [ ] ;
      N := Level(M);
      NN := Reverse([a : a in Divisors(N)]);
      pnew := &*([1] cat [p : p in PrimeDivisors(N) | IsNew(M,p)]);

      for i in [1..#NN] do
         if &+[Integers()|Dimension(d) : d in D] eq Dimension(M) then 
            continue;
         end if;

         if GCD(N div NN[i],pnew) gt 1 or
            NN[i] mod Conductor(DirichletCharacter(M)) ne 0 or
            Characteristic(BaseField(M)) eq 0 and
                 DimensionCuspForms(
                    Restrict(DirichletCharacter(M),NN[i]),
                    Weight(M)
                 ) eq 0 then
             continue;
         end if;

         MM := CuspidalSubspace(ModularSymbols(AmbientSpace(M),NN[i]));
         MMnew := NewSubspace(MM);
         if Dimension(MMnew) eq 0 then
            continue;
         end if;
      
         vprintf ModularSymbols, 1: "Now decomposing the new space %o\n", MMnew; 
         IndentPush();
         DD := complete_decomposition_of_a_new_subspace(MMnew);
         IndentPop();
         // Cache it (added 04-09, SRD)
         MMnew`newform_decomposition := Sort select SortDecomposition(DD) else DD;
         vprintf ModularSymbols, 1: 
          " ... new space in level %o of dimension %o decomposes into spaces of dimensions\n%o\n", 
                             Level(MMnew), Dimension(MMnew), [Dimension(it) : it in DD];
        
         // Take all images of DD in M.
         for A in DD do
            B := image_of_old_newform_factor(M,A);       
            if B subset M then
               Append(~D,B);
               D[#D]`associated_new_space := A;
               D[#D]`associated_new_space`associated_new_space := true;
               D[#D]`is_new := NN[i] eq N;
            end if;
         end for;
      end for;
  
      M`newform_decomposition := Sort select SortDecomposition(D) else D;

      assert Dimension(M) eq &+[Integers()|Dimension(d) : d in D];

      if #D eq 1 and HasAssociatedNewSpace(D[1]) then  // useful later
         M`associated_new_space := D[1]`associated_new_space;
         assert not assigned D[1]`associated_newform_space;
         // (if it is assigned, copy it too)
      end if;
   end if;

   return M`newform_decomposition;
end intrinsic;


intrinsic AssociatedNewSpace (M::ModSym) -> ModSym
{The space of modular symbols corresponding to the 
Galois-conjugacy class of newforms associated to M.  
The level of the newforms is allowed to be a proper divisor of the
level of M. The space M must have been created using 
NewformDecomposition.}
/*   require IsIrreducible(M):
       "Argument 1 must be irreducible and cuspidal.";
*/
   require assigned M`associated_new_space :
       "Argument 1 must have an associated new space.";

   if M`associated_new_space cmpeq true then
      return M;
   end if;

   return M`associated_new_space;

end intrinsic;


intrinsic HasAssociatedNewSpace(M::ModSym) -> BoolElt
{True if and only if M was constructed using NewFormDecomposition.}
   return assigned M`associated_new_space;
end intrinsic;


intrinsic SortDecomposition(D::[ModSym]) -> SeqEnum
{Sort the sequence of spaces of modular symbols with respect to
the 'lt' comparison operator.  Each space must corresponding to
a single Galois-conjugacy class of newforms of some level.}

   require &and[HasAssociatedNewSpace(A) : A in D] :
           "Each element of argument 1 must corresponding to a Galois-conjugacy class of newforms of some level.";

   QuickSort(~D, 'lt');
   return D;
end intrinsic;

intrinsic TraceSortDecomposition(D::[ModSym]) -> SeqEnum
{Sort the sequence of spaces of modular symbols with respect to
the very simple sequence of traces comparison.  The sequence of
traces associated to D[i] is [Trace(HeckeOperator(D[i],n)) : n in [1...]].
This function sorts the D[i] so that the corresponding sequence
of traces is sorted in increasing dictionary order.}  

   if #D eq 0 then
      return D;
   end if;

   require Type(BaseField(D[1])) eq FldRat : "The elements of argument 1 must be defined over Q.";

   for A in D do
      require HasAssociatedNewSpace(A) : "The elements of argument 1 must each correspond to a newform (and be created using NewformDecomposition).";
   end for;

   function lessthan(A, B)
      if A eq B then
         return false;
      end if;
      n := 1;
      while Trace(Trace(HeckeOperator(A,n))) eq Trace(Trace(HeckeOperator(B,n))) do
         n := n+1;
      end while;
      return Trace(Trace(HeckeOperator(A,n))) lt Trace(Trace(HeckeOperator(B,n)));
   end function;

   D := [AssociatedNewSpace(A) : A in D];
   QuickSort(~D, lessthan);
   return D;

end intrinsic;


intrinsic EllipticFactors(M::ModSym, bound::RngIntElt
         : Proof := true) -> SeqEnum
{Decomposition of subspace of M obtained using 
 T_2 - a_2, T_3 - a_3, ..., where a_p varies over all 
 rational integers with |a_p| <= 2*Sqrt(p), and p
 varies over primes not dividing the level of M.
 These factors frequently correspond to elliptic curves.}

/*   require Type(BaseField(M)) in {FldRat, FldCyc, FldNum} :
        "The base field must be either the rationals, a cyclotomic field, or a number field.";
*/


   if bound eq -1 then
      bound := HeckeBound(M);
   end if;

   requirege bound,0;
   require Weight(M) eq 2 : "Argument 1 must have weight 2.";
   require IsTrivial(DirichletCharacter(M)) : "Argument 1 must have trivial character.";

   D := Decomposition_recurse(M, 2, bound, Proof, true, false);
   for i in [1..#D] do
      D[i]`is_cuspidal := true;
   end for;
   return D;
end intrinsic;

intrinsic AtkinLehnerSubspace(M::ModSym, p::RngIntElt, eps::RngIntElt) -> ModSym
{Subspace of M where the Atkin-Lehner involution W_q acts as eps, where q 
 is the power of p that exactly divides the level of M and eps is 1 or -1.}
   //   require IsPrime(p) : "Argument 2 must be prime.";
   require eps in {-1, 1} : "Argument 3 must be either -1 or +1.";
   require Level(M) mod p eq 0 : "Argument 2 must divide the level of argument 1.";
   require IsTrivial(DirichletCharacter(M)) : "Character of argument 1 must be trivial";
   require IsEven(Weight(M)) : "Weight of argument 1 must be even.";

   wp := DualAtkinLehner(M,p);
   W  := KernelOn(wp-eps, DualVectorSpace(M));
   A  := ModularSymbolsDual(M,W);
   if assigned M`al_decomp then
      A`al_decomp := M`al_decomp join {<p, eps>};
   else
      A`al_decomp := {<p, eps>}; 
   end if;
   return A;
end intrinsic;


intrinsic AtkinLehnerDecomposition(M::ModSym) -> SeqEnum
{Decompose M with respect to the Atkin-Lehner involutions.}
   require IsTrivial(DirichletCharacter(M)) : "Character of argument 1 must be trivial";
   require IsEven(Weight(M)) : "Weight of argument 1 must be even.";
   D := [M];
   for p in Factorization(Level(M)) do
      D0 := [];
      for A in D do
         Aplus := AtkinLehnerSubspace(A,p[1],+1);
         Aminus := AtkinLehnerSubspace(A,p[1],-1);     
         if Dimension(Aplus) gt 0 then
            Append(~D0, Aplus);
         end if;
         if Dimension(Aminus) gt 0 then
            Append(~D0, Aminus);
         end if;
      end for;
      D := D0;
   end for;  
   return D;
end intrinsic;

function Kernel_helper(M, W, polyprimes)
   for i in [1..#polyprimes] do
      if IsVerbose("ModularSymbols") then
         "Current dimension = ", Dimension(W);
      end if;
      p  := polyprimes[i][1];
      f  := polyprimes[i][2];
      if IsVerbose("ModularSymbols") then
         printf "Computing Ker(f(T_%o))   ", p;
         t  := Cputime();
      end if;
      T  := FastTn(M, W, p);
      fT := Evaluate(f,T);
      W  := KernelOn(fT,W);
      // W  := W meet K;
      // Why was this here ???
      // The 'KernelOn' is constructed as a subspace of W !!
      if IsVerbose("ModularSymbols") then
         Cputime(t), " seconds.";
      end if;
      if Dimension(W) eq 0 then
         return W;
      end if;
   end for;
   if IsVerbose("ModularSymbols") then
      "Current dimension = ", Dimension(W);
   end if;
   return W;
end function;


intrinsic Kernel(I::[Tup], M::ModSym) -> ModSym
{The kernel of I on M.  This is the subspace of M obtained 
by intersecting the kernels of
the operators f_n(T_\{p_n\}), where I is
a sequence [<p_1, f_1(x)>,...,<p_n,f_n(x)>] of pairs
consisting of a prime number and a polynomial.
Only primes p_i which do not divide the level of M are used.}

   if #I eq 0 then
      return M;
   end if;
   p := I[1][1];
   f := I[1][2];
   t := Cputime();
   if IsVerbose("ModularSymbols") then
      printf "Computing Ker(f(T_%o))   ", p;
   end if;
//"Kernel(I,M): Evaluate on", BaseRing(Parent(f)), "and", BaseRing(DualHeckeOperator(M,p)); time
   fT := Evaluate(f, DualHeckeOperator(M,p));
    W := KernelOn(fT,DualRepresentation(M));
   if IsVerbose("ModularSymbols") then
      Cputime(t), " seconds.";
   end if;
   W := Kernel_helper(AmbientSpace(M), W, Remove(I,1));
   N := ModularSymbolsDual(AmbientSpace(M),W);
   if assigned M`sub_representation then
      N`sub_representation := M`sub_representation;
   end if;    
   return N;
end intrinsic;




////////////////////////////////////////////////////////////////
//                                                            //
//         Lifting from +1 or -1 quotient to full space.      //
//                                                            //
////////////////////////////////////////////////////////////////

/* WARNING: very nonoptimized code. */
function LiftToFullSpace(M, plus, minus) 
   vprint ModularSymbols,2: "LiftToFullSpace ... 'WARNING: very nonoptimized code'";
   assert Type(M) eq ModSym;
   assert Type(plus) eq ModSym;
   assert Type(minus) eq ModSym;
   assert Level(M) eq Level(plus);
   assert Level(M) eq Level(minus);
   assert Sign(M) eq 0;
   assert Sign(plus) eq +1;
   assert Sign(minus) eq -1;
   assert BaseField(M) cmpeq BaseField(plus);
   assert BaseField(M) cmpeq BaseField(minus);
   assert Weight(M) eq Weight(plus);
   assert Weight(M) eq Weight(minus);

   function LiftVector(M,Q,sign,v)
      v := Eltseq(v);
      V := DualVectorSpace(M);
      B := Basis(M);
      w := V![DotProd(v,Eltseq(Q!b)) : b in B];
      S := DualStarInvolution(M);
      return w+sign*w*S;
   end function;

   Bplus  := [LiftVector(M,AmbientSpace(plus),+1,v) : v in Basis(DualVectorSpace(plus))];
   Bminus := [LiftVector(M,AmbientSpace(minus),-1,v) : v in Basis(DualVectorSpace(minus))];
   V := DualVectorSpace(M);
   return ModularSymbolsDual(M, sub<V|Bplus cat Bminus>);
end function;


////////////// End lifting ////////////////////////////////////



intrinsic ModularSymbols(E::CrvEll : Al := "") -> ModSym
{The space M of modular symbols associated to the elliptic curve E.
The existence of M is guaranteed by the Shimura-Taniyama conjecture,
which has been proved by Breuil, Conrad, Diamond, Taylor, and Wiles.  
WARNING: Finding M is computationally difficult, even when Conductor(E)
is on the order of 10000.}

   require Type(BaseRing(E)) eq FldRat :
            "Argument 1 must be defined over RationalField.";

   if Al eq "Lift" then
      t := Cputime();
      vprintf ModularSymbols, 1 : "Computing modular symbols attached to E via +1,-1 then lift algorithm.\n";
      vprintf ModularSymbols, 1 : "Finding +1 quotient.\n";
      plus := ModularSymbols(E,+1);
      vprintf ModularSymbols, 1 : "(time = %o)\n", Cputime(t); t:=Cputime();
      vprintf ModularSymbols, 1 : "Finding -1 quotient.\n";
      minus := ModularSymbols(E,-1);
      vprintf ModularSymbols, 1 : "(time = %o)\n", Cputime(t); t:=Cputime();
      M := ModularSymbols(Conductor(E),2);
      vprintf ModularSymbols, 1 : "Lifting to full space.\n";
      full := LiftToFullSpace(M,plus,minus);
      vprintf ModularSymbols, 1 : "(time = %o)\n", Cputime(t); t:=Cputime();
      return full;
   else
      return ModularSymbols(E,0);
   end if;
end intrinsic;


intrinsic ModularSymbols(E::CrvEll, sign::RngIntElt) -> ModSym
{The 0, +1 or -1 quotient of the space M of modular symbols associated
to the elliptic curve E.  The existence of M is guaranteed by the Shimura-Taniyama conjecture,
which has been proved by Breuil, Conrad, Diamond, Taylor, and Wiles.  
WARNING: Finding M is computationally difficult, even when Conductor(E)
is on the order of 10000.}
   require Type(BaseRing(E)) eq FldRat :
            "Argument 1 must be defined over RationalField.";
   return ModularSymbols(E,RationalField(),sign);
end intrinsic;

intrinsic ModularSymbols(E::CrvEll, K::Fld, sign::RngIntElt
   : stop := 0 ) -> ModSym
{The 0, +1 or -1 quotient of the space M of modular symbols over K 
cut out by the system of eigenvalues corresponding to E.}

   require Type(BaseRing(E)) eq FldRat :
            "Argument 1 must be defined over RationalField.";
   require sign in {-1,0,1} : "Sign must be either -1, 0, or +1.";

   if sign eq -1 and assigned E`ModularSymbolsMinus then
      return E`ModularSymbolsMinus;
   elif sign eq 1 and assigned E`ModularSymbolsPlus then
      return E`ModularSymbolsPlus;
   elif sign eq 0 and assigned E`ModularSymbolsZero then
      return E`ModularSymbolsZero; 
   end if;

   N := Conductor(E);
   M := ModularSymbols(N,2,K,sign);
   dim := Dimension(M);

   // Compute intersection of kernels of (Tp - ap) 
   // until we reach the right dimension d = 1 or 2
   d := 2 - Abs(sign);

   if dim eq d then
      W := M;
   else
      // For the first step, do a single kernel on the full dual space.
      // (I've left flexibility to put more than one prime here, this
      // can be useful when a large space survives the first prime.)
      // Avoid ap = 0, as this will sometimes cut too large a space.

      // Smooth levels have many elliptic curves (including oldforms).
      // Empirically chose 2.5 here based on looking at N around 5000.
      num := (SumOfDivisors(N) ge 2.5*N) select 2 else 1;

      primes := [];
      p := 1;
      while #primes lt num do
         p := SmallestPrimeNondivisor(N, NextPrime(p));
         ap := FrobeniusTraceDirect(E, p);
         if ap ne 0 then
            Append(~primes, <p,ap>);
         end if;
      end while;
      // get Tp - ap for each p in primes
      T := [];
      for tup in primes do
         p, ap := Explode(tup);
         Append(~T, DualHeckeOperator(M, p) - ap);
      end for;
   
      vprintf ModularSymbols: "Finding eigenspace for <p, a_p(E)> = %o\n", primes;
      vtime ModularSymbols:
      K := Kernel(SparseMatrix(HorizontalJoin(T)));
      // This Kernel is much faster when we make it a SparseMatrix

      while Dimension(K) gt d do 
         p := SmallestPrimeNondivisor(N, NextPrime(p));
         ap := FrobeniusTraceDirect(E, p);
         vprintf ModularSymbols: 
                "Now down to dimension %o, using %o\n", Dimension(K), <p, ap>;
         Tp := FastTn(M, K, p);
         K := Rowspace( KernelMatrix(Tp - ap) * BasisMatrix(K) );
      end while;
      assert Dimension(K) eq d;

      W := ModularSymbolsDual(M, K);
   end if;

   case sign:
      when -1 : E`ModularSymbolsMinus := W;
      when  0 : E`ModularSymbolsZero := W;
      when  1 : E`ModularSymbolsPlus := W;
   end case;

   return W;
end intrinsic;


function IsNumeric(s)
   assert Type(s) eq MonStgElt;
   if #s eq 0 then
      return false;
   end if;
   for i in [1..#s] do 
      if not ( (s[i] ge "0") and (s[i] le "9") ) then
         return false;
      end if;
   end for; 
   return true;
end function;


intrinsic ModularSymbols(s::MonStgElt, sign::RngIntElt) -> ModSym
{The space of modular symbols "[Level]k[Weight][IsogenyClass]"
 with trivial character and given sign corresponding to 
 a Galois-conjugacy class of newforms.  Here [Level] is the 
 level, [Weight] is the weight,
 [IsogenyClass] is a letter such as "A", "B", ..., "Z", 
 "AA", "BB", etc., and k is a place holder to separate
 the level and weight.
 If argument 1 is "[Level][IsogenyClass]", then the weight k
 is assumed equal to 2.  If argument 1 is "[Level]k[Weight]" then
 the cuspidal subspace of the full ambient 
 space of modular symbols of weight k is returned.}

   require sign in {-1,0,1} : "Argument 2 must be either -1, 0, or +1.";

   i := 1;
   sN := "";
   while i le #s and s[i] ge "0" and s[i] le "9" do
      sN := sN cat s[i];
      i +:= 1;
   end while;
   require IsNumeric(sN) : "The format of argument 1 is invalid.";
   N := StringToInteger(sN);
   if i gt #s then
      return CuspidalSubspace(ModularSymbols(N,2,sign));
   end if;
   if s[i] eq "k" then
      i +:= 1;
      sk := "";
      while i le #s and s[i] ge "0" and s[i] le "9" do
         sk := sk cat s[i];
         i +:= 1;
      end while;
      require IsNumeric(sk) : "The format of argument 1 is invalid.";
      k := StringToInteger(sk);
   else
      k := 2;
   end if;
   if i gt #s then
      return CuspidalSubspace(ModularSymbols(N,k,sign));
   else
      sIso := &cat [s[j] : j in [i..#s]];
      iso := IsogenyCodeToInteger(sIso);
   end if;

   require iso ge 1:
      "In ModularSymbols(): Requested space of modular symbols does not exist, or is not new.";

   D := SortDecomposition(
           NewformDecomposition(
              NewSubspace(
                 CuspidalSubspace(
                    ModularSymbols(N,k,sign)
                 )
              )
           )  
        );
   require iso in [1..#D] :
      "In ModularSymbols(): Requested space of modular symbols does not exist, or is not new.";
   return D[iso];

end intrinsic;

intrinsic ModularSymbols(s::MonStgElt) -> ModSym
{The full space of modular symbols "Nk[Weight][IsogenyClass]"
 with trivial character and corresponding to 
 a Galois-conjugacy class of newforms. }

   return ModularSymbols(s,0);

end intrinsic;


procedure QuickSort_recurse(~items, low, high, lessthan) 
  // sorts Seqenum using the quick sort algorithm
   if low ge high then 
      return;
   end if;
   lo := low;
   hi := high + 1;
   elem := items[low];
   while true do
      while lo lt high  and 
            lessthan(items[lo+1],elem) do
	 lo +:= 1;
      end while;
      lo +:= 1;
      while lessthan(elem,items[hi-1]) do
         hi -:= 1;
      end while;
      hi -:= 1;
      if lo lt hi then
         t := items[hi];
         items[hi] := items[lo];
         items[lo] := t;
      else
         break;
      end if;
   end while;
   t := items[hi];
   items[hi] := items[low];
   items[low] := t;
   QuickSort_recurse(~items,low,hi-1,lessthan);
   QuickSort_recurse(~items,hi + 1,high,lessthan);
end procedure;


procedure QuickSort(~items, lessthan)
   if IsVerbose("ModularSymbols") then
      t := Cputime();
      print "Sorting ...";
   end if;
   QuickSort_recurse(~items,1,#items, lessthan);
   if IsVerbose("ModularSymbols") then
      Cputime(t), "seconds.";
   end if;
end procedure;
   


/////////////////////////////////////////////////////////////
// The function                                            //
//       NewformDecompositionOfNewNonzeroSignSpace         //
// treats a common special case                  
// that we try to deal with in a much more efficient
// way by calling an implementation of a new algorithm     //
// of Allan Steel.                                         //
/////////////////////////////////////////////////////////////

function SimpleMethod(M, complexity : Dual:=false)
   T := Dual select DualHeckeOperator(M,2)
              else  HeckeOperator(M,2);
   dat := [<1,2>];
   p := 3;
   for i in [1..(complexity div 3)+1] do
      a := Random([-2,-1,1,2]);
      Append(~dat, <a,p>);
      Tp := Dual select DualHeckeOperator(M,p)
                  else  HeckeOperator(M,p);
      T +:= a*Tp;
      p := NextPrime(p);
   end for;      
   return T, dat;
end function;

function RandomHeckeOperator(M, complexity)
   vprintf ModularSymbols : 
       "Computing random Hecke -- complexity = %o\n", complexity;
   T, dat := SimpleMethod(M,complexity);
   vprintf ModularSymbols : "Random Hecke: %o\n", dat;
   return T, dat;
end function;

function RandomDualHeckeOperator(M, complexity)
   vprintf ModularSymbols : 
       "Computing random dual Hecke -- complexity = %o\n", complexity;
   T, dat := SimpleMethod(M,complexity : Dual);
   vprintf ModularSymbols : "Random Hecke: %o\n", dat;
   return T, dat;
end function;

function ClearDenominatorsAndMakeIntegral(T)
   denom := LCM([Integers()|Denominator(a) : a in Eltseq(T)]);
   return MatrixAlgebra(IntegerRing(),Degree(Parent(T)))!(denom*T), denom;
end function;

// restrict T to the subspace with basis given by rows of B
function restrict(T, B)
   MA := MatrixAlgebra(BaseRing(B), Nrows(B));
   return MA ! Solution(B, B*T);
end function;

function min_poly_test(T)
   R := BaseRing(T);
   n := Nrows(T);
   A := MatrixAlgebra< R, n | T >;
   v := Vector([R| Random(10) : i in [1..n]]);
   spin := sub< RModule(A) | v >;
   return Dimension(spin) eq n;
end function;

function AssociatedSubspace(W, V)
   assert Type(W) eq ModTupFld;
   assert Type(V) eq ModTupFld;
   
   return RowSpace( BasisMatrix(V) * BasisMatrix(W) );
end function;

function NewformDecompositionOfNewNonzeroSignSpaceOverQ(M)
   assert Type(M) eq ModSym;
   assert IsNew(M) and Sign(M) ne 0;
   assert Type(BaseField(M)) eq FldRat;
   debug := false;

   /* 1. Generate a random Hecke algebra element T
      2. Ask Allan's function if T probably has square-free charpoly.
      3. If not, increase complexity and go to 1.  
      4. If so, call Allan's second function and get a list of
         the invariant subspaces.   Done.

      For steps 1-3, work mod p (otherwise those calls to Restrict kill us)
   */

   BM := BasisMatrix(VectorSpace(M));
   DBM := BasisMatrix(DualVectorSpace(M));
   N := Level(M);

   primes := [2]; // or could use []

   procedure get_heckes_modp(~heckes, primes, GFp, BMp)
      ls := [l : l in primes | l notin Keys(heckes)];
      for l in ls do 
         TAl := HeckeOperator(AmbientSpace(M), l);
         TAlp := ChangeRing(TAl, GFp);
         Tlp := restrict(TAlp, BMp);
         heckes[l] := Tlp;
      end for;
   end procedure;

   time0 := Cputime();

   p := Floor(2^23.5);

   tries := 0; // only for verbose
   ptries := 0;

   while true do 
      // get next prime
      l := Max(primes);
      repeat 
         l := NextPrime(l);
      until N mod l ne 0;
      Append(~primes, l);
          
      // change the prime sometimes, just in case
      if ptries eq 0 or ptries ge 100 then
         ptries := 0;
         repeat 
            p := PreviousPrime(p);
            GFp := GF(p);
            bool, BMp := CanChangeRing(BM, GFp);
         until bool;
         heckes := AssociativeArray(Integers());
      end if;
      get_heckes_modp(~heckes, primes, GFp, BMp);

      // For the moment, same kind of combs as in WAS' SimpleMethod
      num := 2*#primes;
      rand := {-2,-1,1,2};
      mp := Max(primes);
      combs := [[0 : l in [1..mp]] : i in [1..num]];
      combs[1,mp] := 1; // first comb is 1*T_mp
      for i in [2..num] do 
         for l in primes do 
            combs[i,l] := (l eq mp) select 1 else Random(rand);
         end for;
      end for;
      combs := Seqset(combs); 

      found := false; 
      for c in combs do
         cc := c;
         tries +:= 1;
         ptries +:= 1;
         Tp := &+ [cc[l] * heckes[l] : l in primes];
         if min_poly_test(Tp) then
            found := true;
            break c;
         end if;
      end for;

      if not found then 
         continue;
      end if;
      
      vprintf ModularSymbols: 
         "Found a good combination after %o tries (%os)\n", tries, Cputime(time0);

      T_amb := &+ [cc[l] * HeckeOperator(AmbientSpace(M), l) : l in primes];
vprintf ModularSymbols: "restricting: "; 
vtime ModularSymbols:
      T := restrict(T_amb, BM);
      T_int, T_denom := ClearDenominatorsAndMakeIntegral(T);

      // TO DO: avoid this 'restrict' too, instead pass BM and T_amb to
      // FullPrimaryInvariantSpaces (since it works in residue rings).
      // Example: ModularSymbols(15015, 2, 1)

      // TO DO: cache this Hecke combination somewhere on M ?
      // Note: the cost of Restrict dominates for large dimensions. 
      // HeckeOperator(M) sometimes uses the Projection method, 
      // Although it only needs to do the projection for M once, 
      // that's far more expensive than many calls to Restrict. 
      // So it seems Restrict is the right choice here, and 
      // possibly Projection is a poor choice in other situations.

      vprintf ModularSymbols: "Finding invariant subspaces: ";
      vtime ModularSymbols:
      successful, K, L := FullPrimaryInvariantSpaces(T_int);
      // should be successful (and for dual) unless very unlucky

      if successful then
         if debug and BaseRing(K[1]) eq Rationals() then
           TT := ChangeRing(T_int, Rationals());
           printf "Check answer from FullPrimaryInvariantSpaces, dim %o\n", Ncols(TT);
           time for V in K do  // check V is invariant under T_int
               for v in Basis(V) do assert v*TT in V; end for; end for;
         end if;
vprintf ModularSymbols: "restricting: ";
vtime ModularSymbols:
         Tdual := restrict(Transpose(T_amb), DBM);
         Tdual_int, Tdual_denom := ClearDenominatorsAndMakeIntegral(Tdual);
         // Because the denominators might be different, L might not be
         // the charpoly of Tdual_int.  Thus we have to rescale L.
         scale := Tdual_denom / T_denom;
         if scale ne 1 then 
            R := PolynomialRing(Rationals());
            cp := [<Parent(f[1])!(scale^Degree(f[1])*Evaluate(R!f[1], R.1/scale)), f[2]> : f in L];
         else
            cp := L;
         end if;
         if debug then
            assert IsZero(&*[Evaluate(tup[1], Tdual_int) : tup in cp]);
         end if;
         vprintf ModularSymbols: "Finding invariant subspaces of dual: ";
         vtime ModularSymbols:
         dual_successful, Kdual := FullPrimaryInvariantSpaces(Tdual_int, cp);
      end if;

      if successful and dual_successful then
         if debug and BaseRing(Kdual[1]) eq Rationals() then
           TT := ChangeRing(Tdual_int, Rationals());
           printf "Check answer from FullPrimaryInvariantSpaces (dual), dim %o\n", Ncols(TT);
           time for V in Kdual do  // check V is invariant under Tdual_int
              for v in Basis(V) do assert v*TT in V; end for; end for;
         end if;
         MV := VectorSpace(M);
         MVdual := DualVectorSpace(M);
         decomp := [ModularSymbolsSub(M,AssociatedSubspace(MV,V)) : V in K];
         for i in [1..#decomp] do
            decomp[i]`associated_new_space := true;
            decomp[i]`dual_representation := AssociatedSubspace(MVdual,Kdual[i]);
         end for;
         return decomp;
      else
         vprint ModularSymbols : "Spin Kernels failed; trying again."; 
      end if;
   end while;
end function;




//////////////////////////////////////////////////////////////////
//                     
// The functions SpinVectorCyclo, FullMinimalPolynomialTestCyclo,
// and FullPrimaryInvariantSpacesCyclo were written in MAGMA by
// Allan because he doesn't have time to code them in C right now.
//
//////////////////////////////////////////////////////////////////

function SpinVectorCyclo(v, X, n)
   assert Type(v) eq ModTupFldElt;
   assert Type(X) eq AlgMatElt;
   assert Type(n) eq RngIntElt;
   assert Ncols(v) eq Ncols(X);
   B := RMatrixSpace(BaseRing(Parent(X)), n, Ncols(X)) ! 0;
   B[1] := v;
   for i := 2 to n do
      B[i] := B[i - 1] * X;
   end for;
   return B;
end function;

function FullMinimalPolynomialTestCyclo(X)
   /*
   Return whether X probably has min poly equal to char poly.
   X should be over a cyclo field.
   */
   function ModField(C)
        order := CyclotomicOrder(C);
        maxp := 11863283;
        maxi := (maxp - 1) div order;
        i := maxi;
        repeat
           p := order*i + 1;
           i -:= 1;
        until IsPrime(p);
        K := GF(p);
        r := Roots(PolynomialRing(K) ! DefiningPolynomial(C));
        r := [t[1]: t in r];
        assert #r eq Degree(C);
        return K, hom<C -> K | r[1]>;
   end function;
   C := BaseRing(X);
   n := Ncols(X);
   K, h := ModField(C);
   Y := ChangeRing(Parent(X), K) ! [h(x): x in Eltseq(X)];
   v := Vector([Random(K): i in [1 .. n]]);
   S := SpinVectorCyclo(v, Y, n);
   return Rank(S) eq n;
end function;

function FullPrimaryInvariantSpacesCyclo(X)
   /*
   Return:
         true, primary invariant spaces of X, factorization of char poly of X
    or:
         false, _, _     (on failure).
    X should be over a cyclo field.
   */

   C := BaseRing(X);
   n := Ncols(X);
   range := {-1000 .. 1000} diff {0};
   v := Vector(C, [Random(range): i in [1 .. n]]);

   if IsVerbose("ModularSymbols", 2) then
      vprint ModularSymbols, 2: "Spinning";
      time S := SpinVectorCyclo(v, X, n + 1);
      vprint ModularSymbols, 2: "Get kernel";
      time k := Kernel(S);
   else
      S := SpinVectorCyclo(v, X, n + 1);
      k := Kernel(S);
   end if;

   if Dimension(k) ne 1 then
      return false, _, _;
   end if;

   w := k.1;
   f := PolynomialRing(C) ! Eltseq(w / w[n + 1]);
   if IsVerbose("ModularSymbols",2) then
      "Factorizing";
      time L := Factorization(f);
   else
      L := Factorization(f);
   end if;

   PS := [];
   if IsVerbose("ModularSymbols",2) then
      ZEIT := Cputime();   
   end if;
   for t in L do
      g := t[1]^t[2];
      vprint ModularSymbols, 3: "Factor:", g;
      if Degree(g) eq 1 then
         P := Kernel(X + Coefficient(g, 0));
      else
         q := f div g;
         qv := Vector(Eltseq(q));
         w := qv * RowSubmatrix(S, 1, Ncols(qv));
         w := Normalize(w);
         P := SpinVectorCyclo(w, X, Degree(g));
         P := NullspaceOfTranspose(BasisMatrix(NullspaceOfTranspose(P)));
      end if;
      PS := PS cat [P];
   end for;
   vprint ModularSymbols, 2: "Primary spaces time:", Cputime(ZEIT);

   return true, PS, L;
end function;

 
function NewformDecompositionOfNewNonzeroSignSpaceOverCyclo(M);
   assert Type(M) eq ModSym;
   assert IsNew(M) and Sign(M) ne 0;
   assert Type(BaseField(M)) eq FldCyc;

   /* 1. Generate a random Hecke algebra element T of complexity c. 
      2. Ask Allan's function if T probably has square-free charpoly.
      3. If not, increase complexity and go to 1.  
      4. If so, call Allan's second function and get a list of
         the invariant subspaces.   Done.
   */
   complexity := 0;
   while true do 
      complexity +:= 1;
      T, dat := RandomDualHeckeOperator(M,complexity);
      while not FullMinimalPolynomialTestCyclo(T) do
         complexity +:= 1;
         T, dat := RandomDualHeckeOperator(M,complexity);
      end while;
      vprint ModularSymbols : "charpoly is square free -- now trying to spin";
      successful, Kdual, cp := FullPrimaryInvariantSpacesCyclo(T);
      if successful then
         vprint ModularSymbols : "Spin Kernels succeeded.";
         MVdual := DualVectorSpace(M);
         decomp := [ModularSymbolsDual(M,AssociatedSubspace(MVdual,V)) : 
                       V in Kdual];
         for i in [1..#decomp] do
            decomp[i]`associated_new_space := true;
         end for;
         return decomp;
      else
         vprint ModularSymbols : "Spin Kernels failed; trying again."; 
      end if;
   end while;
end function;

/* Some test code:

procedure TestCyclo(N)
   print "N =", N;
   G := DirichletGroup(N,CyclotomicField(EulerPhi(N)));
   eps := G.Ngens(G);   // choose a different element of G here to make easier
   print "eps has order", Order(eps);
   k := IsEven(eps) select 2 else 3;
   if IsEven(eps) then 
      print "eps is Even";
   else
      print "eps is odd (much harder case)";
   end if;
   print "Making space of modular symbols";
   time M := ModularSymbols(eps,k,+1);
   print "Computing cuspidal subspace";
   time C := CuspidalSubspace(M);
   print "Computing new subspace";
   time N := NewSubspace(C);
   print "Computing decomposition";
   time D := NewformDecomposition(N);
end procedure;

*/


intrinsic ChangeSign(M::ModSym, sign::RngIntElt) -> ModSym
{Use this intrinsic if M has one sign and you're interested in the
same space of modular symbols as M, but with a different sign.
We require that M is either cuspidal or its ambient space.}
   if sign eq Sign(M) then 
      return M;
   end if;

   // Make ambient space, and cut version of M with the right sign out from it.
   A := ModularSymbols(DirichletCharacter(M), Weight(M), sign); 
   if IsAmbientSpace(M) then
      return A;
   end if;   
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   
   B := A;
   target_dimension := Dimension(M);
   if Sign(M) eq 0 then
      target_dimension := target_dimension div 2;
   elif sign eq 0 then
      target_dimension := target_dimension * 2;
   end if;
 
   p := 2;
   while Dimension(B) gt target_dimension do
      I := [<p, CharacteristicPolynomial(HeckeOperator(M,p))>];
      B := Kernel(I,B);
      p := NextPrime(p);
   end while;
   // Save some predicates about M.
   if assigned M`is_new then B`is_new := M`is_new; end if;
   if assigned M`is_p_new then B`is_p_new := M`is_p_new; end if;
   if assigned M`is_cuspidal then B`is_cuspidal := M`is_cuspidal; end if;
   if assigned M`is_eisenstein then B`is_eisenstein := M`is_eisenstein; end if;
   if assigned M`is_irreducible then B`is_irreducible := M`is_irreducible; end if;   
   if assigned M`qexpbasis then B`qintbasis := M`qexpbasis; end if;
   if assigned M`qintbasis then B`qintbasis := M`qintbasis; end if;

   return B;

end intrinsic;
