freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: subspace.m (Cuspidal, Eisenstein, etc. subspaces)

   08/16/03: (WAS) Fixed a bug in NewSubspace(M::ModSym) where a circular
             reference to a space is caused when the level is 1.
             Kevin Buzzard found this bug. 

   Revision 1.18  2002/05/06 03:14:18  was
   Got rid of an assert in NewSubspace.  Yes, the dual is different when we
   allow Eisenstein series sometimes (e.g., level 33, p=3), but this is
   simply the way it is!

   Revision 1.17  2002/04/13 05:28:49  was
   *** empty log message ***

   Revision 1.16  2002/04/13 05:28:28  was
   Removed iscuspidal requirement in NewSubspace.  This will definitely cause problems, in that
   sometimes you can get in a situation where modular symbols don't behave nicely.

   Revision 1.15  2002/03/01 01:58:18  was
   Added BasisPlus, BasisMinus, IntegralBasisPlus, IntegralBasisMinus.

   Revision 1.14  2001/07/13 03:31:01  was
   added PlusSubspace and MinusSubspace.

   Revision 1.13  2001/07/13 03:19:40  was
   Added setting of sign attribute to signed subspaces.

   Revision 1.12  2001/07/08 18:02:39  was
   nothin.

   Revision 1.11  2001/07/03 19:39:15  was
   Added an assertion.

   Revision 1.10  2001/06/01 22:13:27  was
   nothing.

   Revision 1.9  2001/05/29 18:53:46  was
   Fixed typo.

   Revision 1.8  2001/05/29 18:52:36  was
   Put the cuspidal subspace requirement back in, because new just doesn't
   make sense for the Eisenstein subspace given that I must maintain the dual
   as well, in our set up.

   Revision 1.7  2001/05/28 17:09:33  was
   Switched to computing the new subspace using ONLY the level raising map,
   since this seems to resolve all of the problems.

   Revision 1.6  2001/05/26 11:05:57  was
   Don't try in NewSubspace(M,p) to cleverly compute dual degen maps
   in the Eisenstein case, since it doesn't work, e.g,. when k=2,N=6.

   Revision 1.5  2001/05/25 10:47:18  was
   Removed IsCuspidal hypothesis from NewSubspace, because it's really not necessary
   and I need NewSuspace in the modular forms package.

   Revision 1.4  2001/05/20 07:20:45  was
   Added ZeroSubspace.

   Revision 1.3  2001/05/16 19:08:32  was
   comment to NewSubspace.

   Revision 1.2  2001/05/13 03:51:53  was
   Changed ModularForms flag to ModularSymbols.

   Revision 1.1  2001/04/20 04:47:02  was
   Initial revision

   Revision 1.9  2000/09/18 23:31:19  was
   Added that M must be cuspidal in documentation for NewSubspace and OldSubspace.

   Revision 1.8  2000/09/18 23:28:54  was
   Deleted a spurious space in the "NewSubspace" comment.
   [ Surely you're joking, Mr Stein?  -- SRD ]

   Revision 1.7  2000/07/30 03:29:51  was
      * I just investigated "CuspidalSubspace" and found a bug.  I had set
        M`is_cuspidal to true instead of M`cuspidal_part to true.

   Revision 1.6  2000/06/03 04:53:25  was
   verbose: ModularForm --> ModularForms

   Revision 1.5  2000/05/14 23:32:37  was
   Eliminated import of DegeneracyMatrix, because it is now an intrinsic.

   Revision 1.4  2000/05/09 17:00:10  was
   added computing new subspace of both sub and dual back in.

   Revision 1.3  2000/05/09 16:21:10  was
   quick fx to  printf "Computing new part of %.\n",M;

   Revision 1.2  2000/05/02 18:39:40  was
   Fixed some missing CR bugs.

   Revision 1.1  2000/05/02 08:10:34  was
   Initial revision
  
                                                                            
 ***************************************************************************/


import "linalg.m" : KernelOn; 

import "modsym.m" : ModularSymbolsDual,
                    ModularSymbolsSub;

import "multichar.m" : MC_CutSubspace;

/* EXPORTS:
   CuspidalSubspace
   EisensteinSubspace
   PlusSubspaceDual
   PlusSubspaceSub
   MinusSubspaceDual
   MinusSubspaceSub
   NewSubspace */




intrinsic ZeroSubspace(M::ModSym) -> ModSym
{The zero subspace of M.}
   V := VectorSpace(AmbientSpace(M));
   return ModularSymbolsSub(M,sub<V|0>); 
end intrinsic;



intrinsic CuspidalSubspace(M::ModSym) -> ModSym
{The cuspidal subspace of M.  This is the kernel of BoundaryMap(M).}
   if not assigned M`cuspidal_part then
      if IsVerbose("ModularSymbols") then
         print "Computing cuspidal part of",M;
      end if;
      if assigned M`is_cuspidal and M`is_cuspidal then
         return M;
      end if;
      if IsAmbientSpace(M) then
         if IsMultiChar(M) then
            M`cuspidal_part := MC_CutSubspace(M,CuspidalSubspace); 
         else
            M`cuspidal_part := ModularSymbolsSub(M,Kernel(BoundaryMap(M)));      
         end if;
      else
         M`cuspidal_part := M meet CuspidalSubspace(AmbientSpace(M));
      end if;
      (M`cuspidal_part)`is_cuspidal := true;
   end if;
   return M`cuspidal_part;
end intrinsic;


intrinsic EisensteinSubspace(M::ModSym) -> ModSym
{The Eisenstein subspace of M. The is the complement in M of the cuspidal
subspace of M.}
   if not assigned M`eisenstein_part then
      if IsVerbose("ModularSymbols") then
         print "Computing Eisenstein part of",M;
      end if;
      if assigned M`is_eisenstein and M`is_eisenstein then
         return M;
      end if;
      if IsAmbientSpace(M) then
         // Perhaps there is a much faster algorithm than just
         // computing the complement; I have *not* found it.      
         if IsMultiChar(M) then
            M`eisenstein_part := MC_CutSubspace(M,EisensteinSubspace); 
         else
            M`eisenstein_part := Complement(CuspidalSubspace(M));
         end if;
      else
         M`eisenstein_part := M meet EisensteinSubspace(AmbientSpace(M));
      end if;
   end if;
   return M`eisenstein_part;
end intrinsic;


intrinsic '-'(M::ModSym) -> ModSym
{A synonym for Complement(M).}
   return Complement(M);
end intrinsic;


/*  ***READ THIS BEFORE YOU EVEN THINK OF IMPORTING ONE OF THE BELOW FUNCTIONS

   These two functions are not exported because they are of questionable
   end user value and allow one to create ModSym objects in bizarre ways
   that might cause difficult to DualRepresentation() and Representation().
   A modular symbols object *has* to be the part of a space of modular symbols 
   annihilated by an ideal of the Hecke algebra (or be constructed using
   "newsubspace").  These object are not such, causing the problem that 
   the sub representation of an object built out of these objects along 
   with ModSym's need not determine an ideal which cuts out the dual
   representation.  

   WARNING: If, e.g., you create one of the below objects using PlusSubspaceSub
   and then ask for DualRepresentation, your program **will** fail.
*/ 


function PlusSubspaceSub(M) 
   if not assigned M`plus_part_sub then
       M`plus_part_sub := ModularSymbolsSub(M,
                           KernelOn(StarInvolution(M)-1, Representation(M)));
      M`plus_part_sub`sign := +1;
   end if;
   return M`plus_part_sub;
end function;


function PlusSubspaceDual(M) 
   if not assigned M`plus_part_dual then
      M`plus_part_dual := ModularSymbolsDual(M,
                        KernelOn(DualStarInvolution(M)-1, DualRepresentation(M)));
      M`plus_part_dual`sign := +1;
   end if;
   return M`plus_part_dual;
end function;


function MinusSubspaceSub(M)
   if not assigned M`minus_part_sub then
      M`minus_part_sub := ModularSymbolsSub(M,
                      KernelOn(StarInvolution(M)+1, Representation(M)));
      M`minus_part_sub`sign := -1;
   end if;
   return M`minus_part_sub;
end function;


function MinusSubspaceDual(M)
   if not assigned M`minus_part_dual then
      M`minus_part_dual := ModularSymbolsDual(M,
                        KernelOn(DualStarInvolution(M)+1, 
                                       DualRepresentation(M)));
      M`minus_part_dual`sign := -1;
      end if;
   return M`minus_part_dual;
end function;

function PlusSubspace(M)
   assert Type(M) eq ModSym;
   if not assigned M`plus_subspace then
      M`plus_subspace := ModularSymbolsDual(M,
                                       KernelOn(DualStarInvolution(M)-1, 
                                       DualVectorSpace(M)));
      M`plus_subspace`sub_representation :=
                                       KernelOn(StarInvolution(M)-1, 
                                       VectorSpace(M));
      M`plus_subspace`sign := -1;
   end if;
   return M`plus_subspace;
end function;

function MinusSubspace(M)
   assert Type(M) eq ModSym;
   if not assigned M`minus_subspace then
      M`minus_subspace := ModularSymbolsDual(M,
                                       KernelOn(DualStarInvolution(M)+1, 
                                       DualVectorSpace(M)));
      M`minus_subspace`sub_representation := 
                                       KernelOn(StarInvolution(M)+1, 
                                       VectorSpace(M));
      M`minus_subspace`sign := -1;
   end if;
   return M`minus_subspace;
end function;

intrinsic BasisPlus(M::ModSym) -> SeqEnum
{Basis for the +1 eigenspace of StarInvolution on M.}
   return IntegralBasis(PlusSubspace(M));
end intrinsic;

intrinsic BasisMinus(M::ModSym) -> SeqEnum
{Basis for the -1 eigenspace of StarInvolution on M.}
   return IntegralBasis(MinusSubspace(M));
end intrinsic;

intrinsic IntegralBasisPlus(M::ModSym) -> SeqEnum
{Integral basis for the +1 eigenspace of StarInvolution on M.}
   return IntegralBasis(PlusSubspace(M));
end intrinsic;

intrinsic IntegralBasisMinus(M::ModSym) -> SeqEnum
{Integral basis for the -1 eigenspace of StarInvolution on M.}
   return IntegralBasis(MinusSubspace(M));
end intrinsic;

// TO DO: rewrite NewSubspace(M, p) similarly to NewSubspace(M),
// ie call NewNewSubspaceSub in non-multichar case.

intrinsic NewSubspace(M::ModSym, p::RngIntElt) -> ModSym
{The p-new subspace of M.  This is the complement in M of the
subspace generated by the modular symbols of level equal to the level
of M divided by p and character the restriction of the character
of M.  If the character of M  does not restrict, then 
NewSubspace(M,p) is equal to M.   Note that M is 
required to be cuspidal.}

/**********************************************************
   For each prime p dividing the level there are two maps
    alp_1,alp_p: Mk(N,e) ----> Mk(N/p,e')
   The intersection 
         Kernel(alp_1) meet Kernel(alp_p) 
   is called the p-new subspace Mkpnew(N) of Mk(N). 
   If e doesn't factor through (Z/(N/p)Z)^* then
   e' is by definition 0.
 ********************************************************/
   if p eq 0 then
      return NewSubspace(M);
   end if;
   require IsPrime(p) : "Argument 2 must be prime.";

   if not assigned M`p_new_part then
      M`p_new_part := [* *];
   end if;

   if exists(i) { i : i in [1..#M`p_new_part] |
                  M`p_new_part[i][1] eq p} then
      return M`p_new_part[i][2];
   end if;

   vprintf ModularSymbols: "Computing %o-new part of %o\n", p, M;

   if IsMultiChar(M) then
      if IsAmbientSpace(M) then
         function func(x) 
            return NewSubspace(x,p);
         end function;
         pnew := MC_CutSubspace(M,func);
         Append(~M`p_new_part,<p,pnew>);
         return pnew;
      else
         pnew := NewSubspace(AmbientSpace(M),p) meet M;
         Append(~M`p_new_part,<p,pnew>);
         return pnew;
      end if;
   end if;

   N     := Level(M);
   k     := Weight(M);

   if N mod p ne 0 then 
      return M;
   end if;

   eps   := DirichletCharacter(M);
   NN    := N div p;

   if NN mod Conductor(eps) ne 0 then
      return M;
   end if;

   old  := ModularSymbols(AmbientSpace(M),NN);

   if Dimension(old) eq 0 then
      return M;
   end if;

   h1  := DegeneracyMatrix(AmbientSpace(M), old, 1);
   hp  := DegeneracyMatrix(AmbientSpace(M), old, p);

   vprintf ModularSymbols, 2: "Intersecting %o-degeneracy kernels: ", p;
   vtime ModularSymbols, 2:
   meeting := Kernel(h1) meet Kernel(hp) meet VectorSpace(M);

   pnew := ModularSymbolsSub(M, meeting);

   g1  := Transpose(DegeneracyMatrix(old, AmbientSpace(M), 1));
   gp  := Transpose(DegeneracyMatrix(old, AmbientSpace(M), p));

   // TO DO: why do we do everything dual as well?
   dual := DualVectorSpace(M);
   vprintf ModularSymbols, 2: "Intersecting %o-degeneracy kernels (dual): ", p;
   vtime ModularSymbols, 2:
   pnew`dual_representation := Kernel(g1) meet Kernel(gp) meet dual;

   //assert Dimension(pnew`sub_representation) eq 
   //           Dimension(pnew`dual_representation);
 
   Append(~M`p_new_part,<p,pnew>);
   return pnew;
end intrinsic;


// New sub-function for NewSubspace

// Note: it's much better to do all the kernels in one operation.
// The downward degeneracy maps are fast; however the dual ones 
// are not expensive, even the those from small old spaces.
// TO DO: should be cheap to detect which are needed, after 
// we've worked out the sub_representation.

// TO DO: this works out the new part of the ambient, so cache it

function NewNewSubspaceSub(M, primes : ComputeDual:=true)

   AM := AmbientSpace(M);
   N := Level(M); 
   Neps := Conductor(DirichletCharacter(M));

   primes := Sort([p : p in primes | N mod (p*Neps) eq 0]);
   // Sort so that below, the blocks of D with largest rank at the left

   Dmats := <>;
   for p in primes do 
      oldp  := ModularSymbols(AM, N div p);
      if Dimension(oldp) gt 0 then
         Append(~Dmats, DegeneracyMatrix(AM, oldp, 1));
         Append(~Dmats, DegeneracyMatrix(AM, oldp, p));
      end if;
   end for;
   if #Dmats eq 0 then
      return M;
   end if;
   D := HorizontalJoin(Dmats);
   
   vprintf ModularSymbols: "Computing kernel of degeneracy maps: ";
   vtime ModularSymbols:
   KD := Kernel(D);
   AMnew := ModularSymbolsSub(AM, KD);
   /*
   vprintf ModularSymbols: "Intersecting kernel with space: ";
   vtime ModularSymbols:
   Vnew := VectorSpace(M) meet KD;
   Mnew := ModularSymbolsSub(M, Vnew); 
   */

   if ComputeDual then
      // Work out the dual representation of Mnew (repeat same method)

      DDmats := <>;
      for p in primes do 
         oldp  := ModularSymbols(AM, N div p); // cached in AM`other_levels
         if Dimension(oldp) gt 0 then
            Append(~DDmats, Transpose(DegeneracyMatrix(oldp, AM, 1)) );
            Append(~DDmats, Transpose(DegeneracyMatrix(oldp, AM, p)) );
         end if;
      end for;
      DD := HorizontalJoin(DDmats);
 
      vprintf ModularSymbols: "Computing kernel of dual degeneracy maps: ";
      vtime ModularSymbols:
      KDD := Kernel(DD);
      AMnew`dual_representation := KDD;
      /*
      vprintf ModularSymbols: "Intersecting kernel with dual space: ";
      vtime ModularSymbols:
      Mnew`dual_representation := DualVectorSpace(M) meet KDD;
      */
   end if;

   vprintf ModularSymbols: "Intersecting space with kernel space: ";
   vtime ModularSymbols:
   Mnew := M meet AMnew;
   // This is better than intersecting by hand (the two commented bits)

   return Mnew;
end function;


intrinsic NewSubspace(M::ModSym : ComputeDual:=true) -> ModSym
{The new subspace of the cuspidal modular symbols space M.   
This is the intersection of NewSubspace(M,p) as p varies 
over all prime divisors of the level of M}

   // TO DO: was this require supposed to be required, or not?
   require IsCuspidal(M) : 
      "The given space must be contained in the cuspidal subspace";

   if assigned M`is_new and M`is_new 
      or Level(M) eq 1 
      or Dimension(M) eq 0
   then
      return M;
   end if;

   if not assigned M`new_part then
      vprintf ModularSymbols: "Computing new part of %o\n", M;

      primes := [tup[1] : tup in Factorization(Level(M))];

      if IsMultiChar(M) then
         // This is the old version of NewSubspace (TO DO)

         Mnew := NewSubspace(M, primes[1]);
         for i in [2..#primes] do 
            p := primes[i];
            Mnewp := NewSubspace(M, p);
            vprintf ModularSymbols, 2: "%o-new space has dimension %o, intersecting: ", 
                                       p, Dimension(Mnewp);
            vtime ModularSymbols, 2:
            Mnew := Mnew meet Mnewp;
            vprintf ModularSymbols, 2: "New part now has dimension %o\n", Dimension(Mnew);
         end for;

      else
         Mnew := NewNewSubspaceSub(M, primes : ComputeDual:=ComputeDual);
      end if;

      Mnew`is_new := true;
      if IsCuspidal(M) then
         Mnew`is_cuspidal := true;
      end if;
      if assigned M`newform_decomposition then  
         Mnew`newform_decomposition := [NF : NF in M`newform_decomposition | NF`is_new];
         assert Dimension(Mnew) eq &+ [Dimension(NF) : NF in Mnew`newform_decomposition];
      end if;
      M`new_part := Mnew;
   end if;

   return M`new_part;
end intrinsic;



intrinsic Complement(M::ModSym) -> ModSym
{The space of modular symbols complementary to M in AmbientSpace(M).  
Thus the ambient space of M is equal to the direct sum of M
and Complement(M).}

   if IsAmbientSpace(M) then
      return ModularSymbolsSub(M, sub<VectorSpace(M)|>);
   end if;

   d := Dimension(M);
   AM := AmbientSpace(M);

   if d eq 0 then
      return AM;
   end if;

   if not assigned M`complement then
      vprint ModularSymbols, 2: "Forming complement of", M;

      if assigned M`dual_representation and 
         d eq Dimension(M`dual_representation) 
      then
         Asub := Kernel(Transpose(BasisMatrix(DualRepresentation(M))));
         M`complement := ModularSymbolsSub(AM, Asub);
      end if;

      if assigned M`sub_representation and 
         d eq Dimension(M`sub_representation) 
      then
         Adual := Kernel(Transpose(BasisMatrix(Representation(M))));
         if not assigned M`complement then
            M`complement := ModularSymbolsDual(AM, Adual);
         else
            M`complement`dual_representation := Adual;
         end if;
      end if;
   end if;

   return M`complement;
end intrinsic;

intrinsic OldSubspace(M::ModSym) -> ModSym
{The old subspace of M.   This is simply the complement
in M of NewSubspace(M).  Note that M is required to be cuspidal.}
   require IsCuspidal(M) :
         "Argument 1 must be cuspidal.";
   if not assigned M`old_part then
      vprintf ModularSymbols : "Computing new part of %o.\n",M;
      M`old_part := Complement(NewSubspace(M)) meet M;
   end if;
   return M`old_part;
end intrinsic;

intrinsic Projection(M::ModSym) -> Map
{The (Hecke-invariant) projection from the ambient space of M onto M}

   pi := ProjectionMatrix(M);
   return hom<AmbientSpace(M) -> AmbientSpace(M) | x :-> x*pi>;
end intrinsic;

intrinsic ProjectionMap(M::ModSym) -> Map
{"} // "
   pi := ProjectionMatrix(M);
   return hom<AmbientSpace(M) -> AmbientSpace(M) | x :-> x*pi>;
end intrinsic;

intrinsic ProjectionMatrix(M::ModSym) -> AlgMatElt
{"} // "
   if not assigned M`projection_matrix then
      vprintf ModularSymbols: "Computing projection matrix to %o from its ambient:\n", M;
      A := AmbientSpace(M);
      V := VectorSpace(M);
      BM := Basis(V);
      BC := Basis(VectorSpace(Complement(M)));
      Mat := MatrixAlgebra(BaseField(M),Dimension(A));
      XBC := Mat ! (BM cat BC);
      X0 := Mat ! (BM cat [V!0 : i in [1..#BC]]);
      vtime ModularSymbols:
      M`projection_matrix := Mat! Tr(Solution(Tr(XBC), Tr(X0))) where Tr is Transpose;
      // assert XBC * M`projection_matrix eq X0;
   end if;
   return M`projection_matrix;   
end intrinsic;
