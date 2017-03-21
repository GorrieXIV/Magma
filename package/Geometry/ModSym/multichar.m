freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: multichar.m  (Spaces defined by multiple characters.)
 
   $Header: /home/was/magma/packages/ModSym/code/RCS/multichar.m,v 1.1 2002/08/25 17:11:35 was Exp was $

   $Log: multichar.m,v $
   Revision 1.1  2002/08/25 17:11:35  was
   Initial revision


 ***************************************************************************/


import "core.m"   : LiftToCosetRep,
                    ManinSymbolList;
import "linalg.m" : MakeLattice,
                    RestrictionOfScalars, 
                    RestrictionOfScalars_Nonsquare,
                    UnRestrictionOfScalars;
import "modsym.m" : CreateTrivialSpace,
                    ModularSymbolsSub;


forward   AssociatedNewformSpace,
          MC_ConvToModularSymbol,
          MC_CuspidalSubspace,
          MC_CutSubspace,
          MC_Decomposition,
          MC_DecompositionOfCuspidalSubspace,
          MC_DecompositionOfNewCuspidalSubspace,
          MC_DualHeckeOperator,
          MC_HeckeOperator,
          MC_Lattice,
          MC_ManinSymToBasis,
          MC_ModSymBasis,
          MC_ModSymToBasis,
          MC_NewformDecompositionOfCuspidalSubspace,
          MC_NewformDecompositionOfNewCuspidalSubspace,
          MC_SubspaceOfSummandToSubspace
          ;

/* SOME DOCUMENTATION

The motivation for multi-character spaces is two fold.  First, one
frequently wants to compute in spaces of modular symbols besides
M_k(N,eps) for a single character eps.  And second, it should be
possible to reduce all modular symbols computations to computations in
the Q(eps) vector-spaces M_k(N,eps) for various eps. 

The purpose of multichar.m is to extend the functionality of the
modular symbols package to allow the user to transparently work in
certain spaces of modular symbols that are defined over Q as follows.
For any character eps, let M_k(N,[eps]) denote the direct sum of the
spaces M_k(N,eps'), where eps' varies over the distinct
Gal(Qbar/Q)-conjugates of eps.  One can prove that M_k(N,[eps])
contains a Hecke-stable Q-subspace M_k(N,[eps],Q) that generates
M_k(N,[eps]) when tensored with Q(eps).  Multichar.m allows the user
to compute in direct sums of Q-spaces of the form M_k(N,[eps],Q), and,
in particular, to compute things like Z-integral basis, Hecke
operators, period maps and lattices, LRatios, intersections, modular
degrees, and so on.

For example, suppose Gamma_H is an intermediate group between
Gamma_0(N) and Gamma_1(N), which corresponds to a subgroup H of
(Z/NZ)^*.  Then the modular symbols for Gamma_H form a Q-vector space
that is isomorphic to the direct sum of spaces M_k(N,[eps],Q) where
eps runs over Dirichlet characters such that eps(H) = 1.  Thus the
computation of modular symbols for any group between Gamma_0(N) and
Gamma_1(N) is reduced to computation of spaces M_k(N,[eps],Q), which
is in turn reduced to computation of M_k(N,eps). 

A key idea in the computation of M_k(N,[eps],Q) is to understand how
to algorithmically view M_k(N,[eps],Q) as the restriction of scalars
of M_k(N,eps), along with its structure as Hecke module.  A key
function is RestrictionOfScalars, which is defined in the file
linalg.m, in the same directory as the file you're currently looking
at.  If x1,...,x_n is a Q(eps)-basis for M_k(N,eps) and a1,...,ad
is a basis for Q(eps), then we view M_k(N,eps) as a Q-vector space 
with basis ...
*/


/************************************************************************
 *                                                                      *
 *                             CONSTRUCTORS                             *
 *                                                                      *
 ************************************************************************/

intrinsic ModularSymbols(chars::[GrpDrchElt], k::RngIntElt) -> ModSym
{The direct sum of the spaces ModularSymbols(eps,k,sign), 
where eps runs through representatives of the Galois orbits 
of the characters in chars, viewed as a spaced defined over the
rational numbers.  The characters eps must all have the same 
modulus.}
   requirege k,2;   
   require #chars gt 0 : "Argument 1 must have length at least 1.";
   require Type(BaseRing(Parent(chars[1]))) in {FldCyc, FldRat} : 
       "The base ring of argument 1 must be the rationals or cyclotomic.";
   return ModularSymbols(chars,k,0);
end intrinsic;


intrinsic ModularSymbols(chars::[GrpDrchElt], k::RngIntElt, 
                          sign::RngIntElt) -> ModSym
{"} // "
   requirege k,2;   
   require sign in {-1,0,1} : "Argument 3 must be either -1, 0, or 1.";
   require #chars gt 0 : "Argument 1 must have length at least 1.";
   require Type(BaseRing(Parent(chars[1]))) in {FldCyc, FldRat} : 
       "The base ring of argument 1 must be the rationals or cyclotomic.";
   chars := GaloisConjugacyRepresentatives(chars);
   M := New(ModSym);
   M`is_ambient_space := true;
   M`k    := k;
   M`N    := Modulus(chars[1]);
   for i in [2..#chars] do 
      require Modulus(chars[i]) eq M`N : 
            "The characters in argument 1 must all have the same modulus.";
   end for;
   M`eps  := chars;
   M`sign := sign;
   M`F    := RationalField();
   M`dimension := &+[Dimension(S)*Degree(BaseRing(S)) : S in MultiSpaces(M)];
   M`sub_representation  := VectorSpace(M`F,M`dimension);
   M`dual_representation  := VectorSpace(M`F,M`dimension);
   M`mlist := ManinSymbolList(M`k, M`N, M`F);
   return M;
end intrinsic;


intrinsic RestrictionOfScalarsToQ(M::ModSym) -> ModSym
{Restriction of scalars down to Q.  Here M must be defined 
over a finite extension of the rationals.}
   if IsMultiChar(M) or Type(BaseField(M)) eq FldRat then
      return M;
   end if;

   require Type(BaseField(M)) in {FldCyc, FldNum} : 
            "The base field of argument 1 must be either the cyclotomics or a number field.";

   return DirectSumRestrictionOfScalarsToQ([M]);
end intrinsic;

intrinsic DirectSumRestrictionOfScalarsToQ(Spaces::[ModSym]) -> ModSym
{Restriction of scalars to Q of the direct sum of the given modular
 symbols spaces, which are assumed distinct.  The modular symbols
 spaces must be defined over a finite extension of the rationals, and
 must not be multi-character spaces.  The level, weight, and sign must
 be constant.}

   require #Spaces gt 0 : "The sequence must be nontrivial.";
   for M in Spaces do
      require not IsMultiChar(M) : "The input spaces must not be multicharacter spaces.";
      require Type(BaseField(M)) in {FldRat, FldCyc, FldNum} : 
            "The base fields must be finite extensions of the rationals.";
   end for;
   require #Set([Level(M) : M in Spaces]) eq 1 : "The level must be constant.";
   require #Set([Weight(M) : M in Spaces]) eq 1 : "The weight must be constant.";
   require #Set([Sign(M) : M in Spaces]) eq 1 : "The sign must be constant.";
   if #Spaces eq 1 and Type(BaseField(Spaces[1])) eq FldRat then
      return Spaces[1];
   end if;

   // Create the ambient space that will contain Res(DirectSum).
   N := Level(Spaces[1]);
   k := Weight(Spaces[1]);
   C := CyclotomicField(EulerPhi(N));
   G := DirichletGroup(N,C);
   chars := [ G | Eltseq(BaseExtend(DirichletCharacter(M), C)) : M in Spaces];
   A := New(ModSym);
   A`is_ambient_space := true;
   A`k    := k;
   A`N    := N;
   A`eps  := chars;
   A`sign := Sign(Spaces[1]);
   A`F    := RationalField();
   A`multi := [AmbientSpace(M) : M in Spaces];
   A`dimension := &+[Dimension(S)*Degree(BaseRing(S)) : S in MultiSpaces(A)];
   A`sub_representation  := VectorSpace(A`F,A`dimension);
   A`dual_representation  := VectorSpace(A`F,A`dimension);
   // Find each of the subspaces of A corresponding to spaces in the sequence,
   // and add them together.  This is the space we are after.
   S := ZeroSubspace(A);
   for M in Spaces do 
      S := S + MC_SubspaceOfSummandToSubspace(A, M);
   end for;
   return S;
end intrinsic;

intrinsic ModularSymbols(G::GrpPSL2, k::RngIntElt, sign::RngIntElt) -> ModSym
{The space of modular symbols attached to the congruence subgroup G, weight k and given 'sign'}
   requirege k,2;      
   require sign in {-1,0,1} : "Argument 3 must be either -1, 0, or 1.";
   if IsGamma0(G) then
      return ModularSymbols(Level(G), k, sign);
   elif IsGamma1(G) then
      N := Level(G);
      F := CyclotomicField(EulerPhi(N));
      D := DirichletGroup(N,F);
      chars := GaloisConjugacyRepresentatives(D);
      if #chars eq 0 then
         chars := [D!1];
      end if;
      M := ModularSymbols(chars, k, sign);
      M`isgamma1 := true;
      return M;
   elif IsCongruence(G) and G eq CongruenceSubgroup(Level(G)) then
      N := Level(G);
      F := CyclotomicField(EulerPhi(N^2));
      D := Elements(DirichletGroup(N^2,F));
      H := [1+a*N : a in [0..N-1]];
      // The following line is inefficient, but this doesn't
      // matter because N must be very small for the modular
      // symbols computations later to go anywhere.
    //chars := [e : e in D | #[h : h in H | Evaluate(e,h) ne 1] eq 0];
      chars := [e : e in D | forall{h : h in H | Evaluate(e,h) eq 1}]; // SRD 04-09
      M := ModularSymbols(chars, k, sign);
      M`isgamma := true;
      return M;
   else
      require false:
             "Argument 1 must be either Gamma_0(N), Gamma_1(N), or Gamma(N)";
   end if;
end intrinsic;

intrinsic ModularSymbols(G::GrpPSL2, k::RngIntElt) -> ModSym
{The space of modular symbols attached to the congruence subgroup G and weight k}
   requirege k,2;      
   return ModularSymbols(G, k, 0);
end intrinsic;

intrinsic ModularSymbols(G::GrpPSL2) -> ModSym
{Same as ModularSymbols(G,2,0)}
   return ModularSymbols(G, 2, 0);
end intrinsic;

intrinsic ModularSymbolsH(N::RngIntElt, gens::[RngIntElt], 
                          k::RngIntElt, sign::RngIntElt) -> ModSym
{The Modular symbols space corresponding to the subgroup Gamma_H of 
Gamma_0(N) of matrices that that modulo N have lower-left entry in 
the subgroup H of (Z/NZ)^* generated by gens.  This space corresponds 
to the direct sum of spaces with Dirichlet character that is trivial 
on H.}
   requirege N,1;
   requirege k,2;
   require sign in {-1,0,1} : "Argument 4 must be either -1, 0, or 1.";
   require #[d : d in gens | GCD(N,d) ne 1] eq 0 : 
                   "Arguments 1 and 2 must be coprime.";
   F := CyclotomicField(EulerPhi(N));
   D := DirichletGroup(N,F);
   chars := [eps : eps in GaloisConjugacyRepresentatives(D) | 
                   #[d : d in gens | Evaluate(eps,d) ne 1] eq 0];
   if #chars eq 1 and chars[1] eq D!1 then
      return ModularSymbols(N,k,sign);
   end if;
   return ModularSymbols(chars, k, sign);
end intrinsic;

intrinsic ModularSymbolsH(N::RngIntElt, ord::RngIntElt, 
                          k::RngIntElt, sign::RngIntElt) -> ModSym
{Let H be a cyclic subgroup of order ord of (Z/NZ)^*.  This function
computes the space of modular symbols corresponding to the subgroup
Gamma_H of Gamma_0(N) of matrices that that modulo N have lower-left
entry in H.  This space corresponds to the direct sum of spaces with
Dirichlet character that is trivial on H.}

   requirege N,1;
   requirege k,2;
   require sign in {-1,0,1} : "Argument 4 must be either -1, 0, or 1.";
   U,phi := UnitGroup(IntegerRing(N));
   for d in U do
      if Order(d) eq ord then
         return ModularSymbolsH(N, [Integers()|phi(d)], k, sign);
      end if;
   end for;
   require false : "There is no cyclic subgroup of (Z/N Z)^* of order ord.";
end intrinsic;


/************************************************************************
 *                                                                      *
 *                             PREDICATES                               *
 *                                                                      *
 ************************************************************************/

intrinsic IsMultiChar(M::ModSym) -> BoolElt
{True if M is defined by more than one Dirichlet character.}
   // added attribute is_multi for faster access 
   // (some frequently called functions need to check it) -- SRD
   if not assigned M`is_multi then
      M`is_multi := (assigned M`eps and Type(M`eps) eq SeqEnum) or
                    (not IsAmbientSpace(M) and IsMultiChar(AmbientSpace(M)));
   end if;
   return M`is_multi;
end intrinsic;

intrinsic IsTrivial(chars::[GrpDrchElt]) -> BoolElt
{For internal use only}
   return false;
end intrinsic;


/************************************************************************
 *                                                                      *
 *                            ATTRIBUTES / DATA                         *
 *                                                                      *
 ************************************************************************/

intrinsic MultiSpaces(M::ModSym) -> SeqEnum
{Sequence of spaces with Dirichlet characters attached to M.}
   if not IsMultiChar(M) then
      return [M];
   end if;
   if not assigned M`multi then
      k := Weight(M);
      sign := Sign(M);
      M`multi := [ModularSymbols(MinimalBaseRingCharacter(eps),k,sign) 
                                        : eps in DirichletCharacter(M)];
   end if;
   return M`multi;
end intrinsic;

intrinsic MultiQuotientMaps(M::ModSym) -> List
{List of quotient maps (with inverse) from M to each of the spaces 
 that define the multi-character space M.}

   require Type(BaseField(M)) eq FldRat : "Argument 1 must be over Q";
   // because RestrictionOfScalars is only for Q
 
   if not IsAmbientSpace(M) then
      return MultiQuotientMaps(AmbientSpace(M));
   end if;

   bool, maps := HasAttribute(M, "multi_quo_maps");
   if bool then
      return maps;
   end if;

   if not IsMultiChar(M) then
      return [* map< M -> M | x:->x, x:->x > *];
   end if;

   // The basis of the multi-space is always chosen to be 
   // the concatenation of the bases of the summands,
   // or in the case where the base fields are different,
   // of the bases produced by "unrestriction-of-scalars".

   V, mV := VectorSpace(M);
   MS := MultiSpaces(M);
   maps := [* *];

   start := 1;
   for i in [1..#MultiSpaces(M)] do
      N := MS[i];
      assert IsAmbientSpace(N);
      K := BaseField(N);
      d := Dimension(N)*Degree(K);
      stop := start + d - 1;

      function f(x) // M -> N
         e := Eltseq(x);
         v := Vector(e[start..stop]);
         return N! UnRestrictionOfScalars(v, K);
      end function;

      function g(x) // N -> M
         eK := Eltseq(x);
         e := RestrictionOfScalars(eK);
         v := V!0;
         InsertBlock(~v, Vector(e), 1, start);
         return v@mV;
      end function;

      Append(~maps, map< M -> N | x:->f(x), x:->g(x) >);

      start := stop+1;
   end for;

   return maps;
end intrinsic;

intrinsic MultiTuple(x::ModSymElt) -> List
{If x is an element of the multicharacter space M, which is 
isomorphic to the direct sum of the restrictions of the restriction
of scalars of spaces M_i, this returns the tuple in the product
of the M_i corresponding to x.  The tuple is represented as a
list of elements of the M_i.}
   M := AmbientSpace(Parent(x));
   if not IsMultiChar(M) then
      return [* x *];
   end if;
   ans := [* *];
   for phi in MultiQuotientMaps(M) do
      Append(~ans, phi(x));
   end for;
   return ans;
end intrinsic;

/************************************************************************
 *                                                                      *
 *                 HELPER FUNCTIONS THAT ARE USED BY OTHER CODE         *
 *                 THROUGHOUT THE MODULAR SYMBOLS PACKAGE TO            * 
 *                 IMPLEMENT MULTICHARACTER SPACES                      *
 *                                                                      *
 ************************************************************************/

function MC_Operator(M, f)
   assert Type(M) eq ModSym;
   assert IsMultiChar(M);
   assert IsAmbientSpace(M);
   S := MatrixAlgebra(RationalField(),Dimension(M))!0;
   offset := 0;
   for MS in MultiSpaces(M) do 
      T := RestrictionOfScalars(f(MS));
      for r in [1..Nrows(T)] do 
         for c in [1..Ncols(T)] do
            S[offset+r, offset+c] := T[r,c];
         end for; 
      end for;
      offset := offset + Nrows(T);
   end for;
   return S;
end function;

function MC_HeckeOperator(M, n) 
   assert Type(n) eq RngIntElt;
   function f(x) 
      return HeckeOperator(x,n);
   end function;
   return MC_Operator(M,f);
end function;

function MC_DualHeckeOperator(M, n) 
   assert Type(M) eq ModSym;
   assert Type(n) eq RngIntElt;
   assert IsAmbientSpace(M);
   return Transpose(HeckeOperator(M,n));
end function;

function MC_StarInvolution(M)
   return MC_Operator(M,StarInvolution);
end function; 

function MC_ModSymToBasis(M, sym)
   // Given a modular symbols (more precisely, something that can be 
   // coerced into each modular symbols space that defines M), returns 
   // the corresponding element of M. 
   
 //assert Type(M) eq ModSym;
 //assert IsMultiChar(M);
   if not IsAmbientSpace(M) then
      M := AmbientSpace(M);
   end if;

   v := VectorSpace(M)!0;
   offset := 1;
   for MS in MultiSpaces(M) do
      x := [Eltseq(a) : a in Eltseq(MS!sym)];
      for i in [1..Degree(BaseField(MS))] do
         for j in [1..Dimension(MS)] do
            v[offset] := x[j][i];
            offset +:= 1;
         end for;
      end for;
   end for;
   return v;   
end function;

function MC_ManinSymToBasis(M, sym)
   // Given a manin symbol sym, returns the corresponding
   // element of M. 
 //assert Type(sym) eq Tup;      
 //assert Type(M) eq ModSym;
 //assert IsMultiChar(M);
 //assert IsAmbientSpace(M); // these checks take too long!

   v := VectorSpace(M)!0;
   offset := 1;
   for MS in MultiSpaces(M) do
      x := [Eltseq(a) : a in Eltseq(ConvertFromManinSymbol(MS,sym))];
      for i in [1..Degree(BaseField(MS))] do
         for j in [1..Dimension(MS)] do
            v[offset] := x[j][i];
            offset := offset + 1;
         end for;
      end for;
   end for;
   return v;   
end function;

function MC_ModSymBasis(M : cache_raw_basis:=false )
   // A sequence of modular symbols <P(X,Y),[alpha,beta]> such that
   // the ith element of the sequence maps to the ith basis vector 
   // of M under MC_ModSymToBasis. 

   assert Type(M) eq ModSym;
   assert IsMultiChar(M);
   assert IsAmbientSpace(M);

   if not assigned M`multi_modsymgens or 
      cache_raw_basis and not assigned M`MC_ModSymBasis_raw 
   then
      G := [* *]; 
      R<X,Y> := PolynomialRing(RationalField(),2);
      N := Level(M);
      k := Weight(M);
      V := VectorSpace(M);
      dim := Dimension(V);
      W := sub<V| >;
      mat := MatrixAlgebra(Rationals(),dim)!0;
      monomials := [X^i*Y^(k-2-i) : i in [0..k-2]];

      // Run through pairs u,v in Z/N in some order
      // TO DO: how can we guess which are likely to be independent generators?
      for u := 0 to N-1 do
         for v := 0 to N-1 do
            if GCD([u,v,N]) ne 1 then continue; end if;
	    for pol in monomials do 
               gen := <pol, [u,v]>;
               x := MC_ManinSymToBasis(M,gen);
               Include(~W, x, ~x_is_new);
               if x_is_new then
                  Append(~G, gen);
                  mat[#G] := x;
                  if #G eq dim then break u; end if;        
               end if; 
            end for;
         end for;
      end for;
      assert #G eq dim;

      matinv := mat^(-1);
      raw_basis := [];
      for gen in G do 
         a,b,c,d := Explode(LiftToCosetRep(gen[2],N));
         poly_part := Evaluate(gen[1], [d*X-b*Y, -c*X+a*Y]);
         Append(~raw_basis, <poly_part, [[b,d],[a,c]]> );
      end for;
      
      if cache_raw_basis then
         M`MC_ModSymBasis_raw := [* raw_basis, mat, matinv *];
      end if;
        
      gens := [* *];
      for i := 1 to dim do
         z := [];
         for j := 1 to dim do
            mij := matinv[i,j];
            if mij ne 0 then
               Append(~z, <mij*bj[1],bj[2]> where bj is raw_basis[j]);
            end if;
         end for;
         Append(~gens, z);
      end for;
      M`multi_modsymgens := gens;
   end if;   
   return M`multi_modsymgens;
end function;

function MC_ConvToModularSymbol(M,v)
   // Convert the element v of M to a sequences of pairs 
   // <P(X,Y), [alpha,beta]>, where alpha=[a,b], beta=[c,d] 
   // are cusps, so alpha=a/b, beta=c/d.
   assert Type(M) eq ModSym;
   assert Type(v) eq ModSymElt;
   assert IsMultiChar(M);

   basis := MC_ModSymBasis(M);
   Z := [];
   w := Eltseq(v);
   for i in [1..Dimension(M)] do   
      if w[i] ne 0 then
         for b in basis[i] do
            Append(~Z,<b[2],w[i]*b[1]>);
         end for;
      end if;
   end for;
   if IsEmpty(Z) then
      return []; // added April 2009, SRD
   end if; 
   Sort(~Z);
   t := Z[1][1];  
   A := [<Z[1][2],t>];
   for i in [2..#Z] do 
      if Z[i][1] eq t then
         A[#A][1] := A[#A][1] + Z[i][2];
      else
         if A[#A][1] eq 0 then
            A[#A] := <Z[i][2],Z[i][1]>;
         else
            Append(~A,<Z[i][2],Z[i][1]>);
         end if;
         t := Z[i][1];
      end if;
   end for;
   if A[#A][1] eq 0 then
      A := [A[i] : i in [1..#A-1]];
   end if;
   return A;
end function;

// For a full multi space M over a field, return matrix giving 
// the action of g in GL_2(Z) on subspace V of VectorSpace(M).
// Both matrices act on the left.
// (This handles efficiently the situation where g acts on M, but 
// does not have well-defined action on the quotient spaces in M`multi)
// Added 04-09, SRD

function MC_MatrixActionOnSubspace(g, V, m)
   M := Codomain(m);
   assert IsMultiChar(M);
   assert IsAmbientSpace(M);
   assert Degree(V) eq Dimension(M);

   R := BaseRing(V); assert IsField(R);
   RM := BaseRing(M);

   // All matrices are row-matrices, ie acting from the right
   
   // Get nice_basis (consisting of one-term symbols) 
   // Rows of T give Basis(M) in terms of nice_basis 
   _ := MC_ModSymBasis(M : cache_raw_basis);
   nice_basis, _, T := Explode(M`MC_ModSymBasis_raw); 

   // action on nice_basis, with images w.r.t standard basis
   g_Mnice_to_M := ZeroMatrix(RM, Degree(V), Degree(V)); 
   for i := 1 to #nice_basis do
      image := ModularSymbolApply(M, g, [nice_basis[i]]);
      g_Mnice_to_M[i] := MC_ModSymToBasis(M, image[1]);
   end for;

   // Action g_M on Basis(M) is given by T * g_Mnice_to_M 
   // Solve g_V * Vmat = Vmat * g_M for g_V
   Vmat := BasisMatrix(V);
   if RM ne R then 
      T := ChangeRing(T, R);
      g_Mnice_to_M := ChangeRing(g_Mnice_to_M, R);
   end if;
   bool, g_V, kern := IsConsistent(Vmat, (Vmat*T)*g_Mnice_to_M );
   error if not bool or Dimension(kern) ne 0, 
        "Action is not well-defined on the given subspace";

   return Transpose(g_V);
end function;


function MC_Lattice(M)
   // Compute the lattice of integral modular symbols in 
   // the multicharacter ambient space M.
   assert Type(M) eq ModSym;
   assert IsMultiChar(M);
   assert IsAmbientSpace(M);
   vprint ModularSymbols, 2: "Creating multi-character lattice";
   gens := [];  
   N := Level(M);
   k := Weight(M);
   R<X,Y> := PolynomialRing(RationalField(),2);
   t := Cputime();
   if k gt 2 then
      vprintf ModularSymbols, 2: "k = 0..%o:\n",k-2;
   end if;
   for i in [0..k-2] do
      P := X^i*Y^(k-2-i);
      /* The S relation on Manin symbols is that 
             [P(X,Y),(u,v)] + [ P(-Y,X), (v,-u)] = 0.
         Thus in writing down generators for the integral structure,
         given [P(X,Y),(u,v)], we automatically get [P(-Y,X), (v,-u)].  
         And, from [P(-Y,X), (v,-u)] we get [P(X,Y), (-u,-v)] and
         also [P(-Y,X), (-v,u)].  Thus we only need to iterate 
         over (u,v) between 0 and Ceiling(N/2)+1.
      */
      vprintf ModularSymbols, 2: "u = 0..%o:\t",Ceiling(N/2)+1;
      for u in [0..Ceiling(N/2)+1] do
        vprintf ModularSymbols, 2: "%o, ", u;
        for v in [v : v in [0..Ceiling(N/2)+1] | GCD(u,GCD(v,N)) eq 1] do 
            x := <P, [u,v]>;
            z := MC_ManinSymToBasis(M,x);
            Append(~gens,z);
         end for;
      end for;
   end for;
   vprint ModularSymbols, 2: "\nTime to make list of generators =", Cputime(t), " seconds.";
   vprint ModularSymbols, 2: "Making lattice...";
   t := Cputime();
   L := MakeLattice(gens);  
   vprintf ModularSymbols, 2: "Time to make lattice = %o.\n", Cputime(t);
   return L;
end function;

function MC_CutSubspace(M, cut_function)
   // Compute the subspace of the ambient space M got by adding up
   // the result of applying the function "cut_function" to each of 
   // the spaces that make up M.

   assert Type(M) eq ModSym;
   assert IsMultiChar(M);
   assert IsAmbientSpace(M);
   
   V := VectorSpace(M);
   B := [V| ];
   offset := 0;
   for MS in MultiSpaces(M) do
      K := BaseField(MS);
      basis := Basis(K);
      for x in Basis(cut_function(MS)) do 
         for alpha in basis do
            y := Eltseq(alpha*x);
            v := V!0;
            for i in [1..#basis] do 
               for j in [1..Dimension(MS)] do
                  v[offset + (i-1)*Dimension(MS) + j] := Eltseq(y[j])[i];
               end for;
            end for;
            Append(~B, v);
         end for;
      end for;
      offset := offset + Degree(BaseField(MS))*Dimension(MS);
   end for;
   return ModularSymbolsSub(M,sub<V|B>);
end function;


function MC_CuspidalSubspace(M)
   assert Type(M) eq ModSym;
   assert IsMultiChar(M);
   assert IsAmbientSpace(M);

   return MC_CutSubspace(M,CuspidalSubspace);
end function;

function MC_SubspaceOfSummandToSubspace(M, S)
   // Given a subspace S of one of the summands that makes up M, returns the
   // corresponding subspace of M. 
   assert Type(M) eq ModSym;
   assert IsMultiChar(M);
   assert IsAmbientSpace(M);
   assert not IsMultiChar(AmbientSpace(S));

   V := VectorSpace(M);
   B := [V| ];
   offset := 0;
   for MS in MultiSpaces(M) do
      K := BaseField(MS);
      basis := Basis(K);
      if MS eq AmbientSpace(S) then
         for x in Basis(VectorSpace(S)) do 
            for alpha in basis do
               y := Eltseq(alpha*x);
               v := V!0;
               for i in [1..#basis] do 
                  for j in [1..Dimension(MS)] do
                     v[offset + (i-1)*Dimension(MS) + j] := Eltseq(y[j])[i];
                  end for;
               end for;
               Append(~B, v);
            end for;
         end for;
         break;
      end if;
      offset := offset + Degree(BaseField(MS))*Dimension(MS);
   end for;
   return ModularSymbolsSub(M,sub<V|B>);
end function;

function MC_Decomposition(M, bound)
   // Compute the decomposition of the ambient multi-character space M using
   // Hecke operators of index <= bound.

   assert Type(M) eq ModSym;
   assert IsMultiChar(M);
   assert IsAmbientSpace(M);
   assert Type(bound) eq RngIntElt;
   
   D := [];
   for MS in MultiSpaces(M) do 
      for A in Decomposition(MS, bound) do 
         Append(~D, MC_SubspaceOfSummandToSubspace(M, A));
      end for;
   end for;
   return D;
end function;


function MC_DecompositionOfCuspidalSubspace(M, bound)
   // Compute the decomposition of the cuspidal subspace of the 
   // ambient multi-character space M using Hecke operators 
   // of index <= bound.

   assert Type(M) eq ModSym;
   assert IsMultiChar(M);
   assert IsAmbientSpace(M);
   assert Type(bound) eq RngIntElt;
   
   D := [];
   for MS in MultiSpaces(M) do 
      for A in Decomposition(CuspidalSubspace(MS), bound) do 
         Append(~D, MC_SubspaceOfSummandToSubspace(M, A));
      end for;
   end for;
   return D;
end function;


function MC_DecompositionOfNewCuspidalSubspace(M, bound)
   // Compute the decomposition of the new cuspidal subspace of the 
   // ambient multi-character space M using Hecke operators 
   // of index <= bound.

   assert Type(M) eq ModSym;
   assert IsMultiChar(M);
   assert IsAmbientSpace(M);
   assert Type(bound) eq RngIntElt;
   
   D := [];
   for MS in MultiSpaces(M) do 
      for A in Decomposition(NewSubspace(CuspidalSubspace(MS)), bound) do 
         Append(~D, MC_SubspaceOfSummandToSubspace(M, A));
      end for;
   end for;
   return D;
end function;


function MC_NewformDecompositionOfCuspidalSubspace(M)
   // Compute the newform decomposition of the cuspidal subspace 
   // of the ambient multi-character space M using Hecke operators 
   // of index <= bound.

   assert Type(M) eq ModSym;
   assert IsMultiChar(M);
   assert IsAmbientSpace(M);
   
   D := [];
   for MS in MultiSpaces(M) do 
      for A in NewformDecomposition(CuspidalSubspace(MS)) do 
         f := MC_SubspaceOfSummandToSubspace(M, A);
         f`associated_newform_space := A;
         f`associated_new_space := A`associated_new_space;
         f`is_new := A`is_new;
         Append(~D, f);
      end for;
   end for;
   return D;
end function;

function MC_NewformDecompositionOfNewCuspidalSubspace(M)
   // Compute the newform decomposition of the new cuspidal subspace 
   // of the ambient multi-character space M using Hecke operators 
   // of index <= bound.
   assert Type(M) eq ModSym;
   assert IsMultiChar(M);
   assert IsAmbientSpace(M);
   
   D := [];
   for MS in MultiSpaces(M) do 
      for A in NewformDecomposition(NewSubspace(CuspidalSubspace(MS))) do 
         f := MC_SubspaceOfSummandToSubspace(M, A);
         f`associated_newform_space := A;
         f`associated_new_space := A`associated_new_space;
         f`is_new := true;
         Append(~D, f);
      end for;
   end for;
   return D;
end function;


// The following two functions are used for multichar spaces that are attached
// to newforms.
function AssociatedNewformSpace(M)
    if not assigned M`associated_newform_space then
       error "Space must be associated to a newform (constructed using NewformDecomposition).";
    end if;
    return M`associated_newform_space;
end function;

function HasAssociatedNewformSpace(M)
    return assigned M`associated_newform_space;
end function;

function MC_ModularSymbols_of_LevelN(M, N)
   assert Type(M) eq ModSym;
   assert Type(N) eq RngIntElt;
   assert IsMultiChar(M);

   X := [x : x in DirichletCharacter(M) | N mod Conductor(x) eq 0];
   if #X eq 0 then
      return CreateTrivialSpace(Weight(M),DirichletGroup(Level(M))!1,Sign(M));
   end if;
    
   G := DirichletGroup(N,CyclotomicField(EulerPhi(N)));
   Y := [G!eps : eps in X];
/*   
   for eps in X do
      if Level(M) mod N eq 0 then
         psi := G!eps;
      else
         psi := 
      end if;
      Append(~Y,psi);
   end for;
*/
   return ModularSymbols(Y, Weight(M), Sign(M));
end function;

function MC_DegeneracyMatrix(M1, M2, d)
   assert IsMultiChar(M1) and IsMultiChar(M2);
   N1 := Level(M1);
   N2 := Level(M2);
   MS1 := MultiSpaces(M1);
   MS2 := MultiSpaces(M2);
   if N1 eq N2 then
      assert d eq 1;
      assert M1 eq M2;
      F := BaseField(M1);
      return Hom(VectorSpace(M1), VectorSpace(M2))!MatrixAlgebra(F,Degree(M1))!1;
   end if;
   ans := MatrixAlgebra(RationalField(),0)!0;   
print "MC_DegeneracyMatrix totally bogus!";
/* Need to find correspondence and put together much much more carefully. */
   for m1 in MS1 do 
      eps1 := DirichletCharacter(m1);
      for m2 in MS2 do 
         eps2 := DirichletCharacter(m2);
         if BaseRing(eps2) cmpeq BaseRing(eps1) then 
         if IsCoercible(Parent(eps2),eps1) and (Parent(eps2)!eps1 eq eps2) then
               degen := DegeneracyMatrix(m1,m2,d);
               degen := RestrictionOfScalars_Nonsquare(degen);
               ans := DirectSum(ans,degen);
               break;
            end if;
         end if;
      end for;
   end for;
   return ans;
end function;
