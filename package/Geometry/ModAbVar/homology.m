freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: homology.m
   DESC: Basic ModAbVarHomol functionality.

 ***************************************************************************/

import "linalg.m": 
   Intersect_Vector_Space_With_Lattice,
   IsMatrix,
   MakeLattice,
   RestrictionOfScalars,
   UnRestrictionOfScalars;

import "modabvar.m":
   Verbose;

import "rings.m": 
   QQ, RR, ZZ;

forward
   AllModularSymbolsSpacesAreFull,
   BasisChange_Lattice_to_Rational,
   BasisChange_Lattice_to_Real,
   BasisChange_Rational_to_Lattice,
   BasisChange_Real_to_Lattice,
   Create_ModAbVarHomol,
   Create_ModAbVarHomol_Quotient,
   Create_ModAbVarHomol_Subspace,
   DimensionQ,
   HeckeTraces,
   HomologyLevel,
   HomologySignZeroDimension,
   ModSymMap_to_HomologyMatrix,
   ModSymMatrix_to_HomologyMatrix,
   ModSym_to_Rational,
   ModSym_to_Rational_Matrix,
   Rational_to_ModSym,
   Rational_to_ModSym_Matrix;


declare type ModAbVarHomol;

declare attributes ModAbVarHomol:
   dimension,             // dimension of rational homology.
   rational,              // rational homology
   real,                  // real homology
   integral,              // integral homology
   assume_rational_modsym_integral, 

   basischange_real_to_lattice,
   basischange_rational_to_lattice,

   modsym,                // Sequence of modular symbols spaces over Q or
                          // cyclotomic extensions.  The spaces must all 
                          // have the same sign.  This attribute need not be assigned.
   
   sign,                  // sign of the modular symbols spaces that
                          // make up H
   rational_to_modsym,    // Isomorphism from vector_space to direct sum of modular_symbols
   rational_to_modsym_matrix,  // Isomorphism from vector_space to direct sum of modular_symbols
                          // spaces, viewed as Q-vector spaces
   modsym_to_rational,    // Isomorphism from modular_symbols to vector_space
   modsym_to_rational_matrix, // Isomorphism from modular_symbols to vector_space
   hecke_traces,          // traces down to Q of Hecke operators on modsym's
   level;                 // least common multiple of levels of modsym



/***************************************************************************

  << Creation >>

 ***************************************************************************/

intrinsic Homology(A::ModAbVar) -> ModAbVarHomol
{The first integral homology of A.}
   return A`homology;
end intrinsic;

intrinsic 'eq'(H1::ModAbVarHomol, H2::ModAbVarHomol) -> BoolElt
/* EXCLUDE FROM HANDBOOK -- since equality is a bit strange.  It's
useful for the other code I've written, but probably not for a user,
who would really just care about equality in the sense of "same
free Z-rank". */
{True if the homology groups H_1 and H_2 are equal.  If neither are
attached to modular symbols, this means that the underlying lattices
of the homology are equal.  If either of H_1 or H_2 are attached to
modular symbols, then both must be attached to the same space of 
modular symbols in order for H_1 and H_2 to be equal.}
   if H1`dimension ne H2`dimension then
      return false;
   elif not assigned H1`modsym and not assigned H2`modsym then
      return Lattice(H1) eq Lattice(H2);
   elif not assigned H2`modsym then
      return false;
   elif not assigned H1`modsym then
      return false;
   elif #H1`modsym ne #H2`modsym then
      return false;
   end if;  
   for i in [1..#H1`modsym] do 
      if H1`modsym[i] ne H2`modsym[i] then
         return false;
      end if;
   end for;
   return true;
end intrinsic;


/***************************************************************************

  << Invariants >>

The only invariant of homology is its dimension.   If $A$ is
an abelian variety, and $H$ is its first homology, then $H$
has dimension equal to twice the dimension of~$A$.  (Except
if, for efficiency purposes, we are working with sign
$+1$ or $-1$, in which case the dimension of $H$ is equal to the
dimension of~$A$.)

EXAMPLES

> Homology(JZero(100));
Modular abelian variety homology space of dimension 14
> Homology(JZero(100,2,+1));
Modular abelian variety homology space of dimension 7
> Homology(JZero(100,2,-1));
Modular abelian variety homology space of dimension 7


 ***************************************************************************/

intrinsic Dimension(H::ModAbVarHomol) -> RngIntElt
{The dimension of the space H of homology.}
   return Dimension(VectorSpace(H));
end intrinsic;


/***************************************************************************

  << Functors to Categories of Lattices and Vector Spaces >>


 ***************************************************************************/

intrinsic RationalHomology(A::ModAbVar) -> ModTupFld
{A Q-vector space obtained by tensoring the homology of A with Q.}
   return VectorSpace(A`homology);
end intrinsic;

intrinsic RealHomology(A::ModAbVar) -> ModTupFld
{A vector space over R obtained by tensoring the homology of A with R,
where R is the field of real numbers.}
   return RealVectorSpace(A`homology);
end intrinsic;

intrinsic IntegralHomology(A::ModAbVar) -> Lat
{The lattice underlying the homology of A.}
   return Lattice(A`homology);
end intrinsic;


intrinsic Lattice(H::ModAbVarHomol) -> Lat
{The underlying lattice of the homology space H.  }
   if not assigned H`integral then
      Verbose("Lattice (homology)", 
         Sprintf("Computing integral structure on %o.",H),"");
      assert assigned H`modsym;
      f := ModSym_to_Rational(H);
      basis := [];
      zero := [* *];
      for M in H`modsym do
         Append(~zero, M!0);
      end for;
      for i in [1..#H`modsym] do 
         v := zero;
         for b in IntegralBasis(H`modsym[i]) do
            v[i] := b;
            Append(~basis,f(v));
         end for;
      end for;
      H`integral := MakeLattice(basis);
   end if;
   return H`integral;
end intrinsic;

intrinsic VectorSpace(H::ModAbVarHomol) -> ModTupFld
{The Q-vector space of dimension equal to the dimension of H.}
   return H`rational;
end intrinsic;

intrinsic RealVectorSpace(H::ModAbVarHomol)  -> ModTupFld
{The R-vector space of dimension equal to the dimension of H.}
   return H`real;
end intrinsic;


/***************************************************************************

  << Modular Structure >>

 ***************************************************************************/

intrinsic IsAttachedToModularSymbols(H::ModAbVarHomol) -> BoolElt
{True if H is presented as being attached to a sequence of spaces of 
modular symbols.}
   return assigned H`modsym;
end intrinsic

intrinsic ModularSymbols(H::ModAbVarHomol) -> SeqEnum
{If H is attached to a sequence Q of spaces of modular symbols, then
return Q}
   require assigned H`modsym : 
        "Argument 1 must be attached to modular symbols.";
   return H`modsym;
end intrinsic;

function DimensionQ(M)
   assert Type(M) eq ModSym;
   return Dimension(M)*Degree(BaseField(M));
end function;

function Create_ModAbVarHomol(x)
   H := New(ModAbVarHomol);
   case Type(x):
      when Lat: 
         assert Degree(x) eq Dimension(x);   // must be a full lattice.
         H`dimension := Dimension(x);
         H`integral := x;
         H`sign := 0;  // this is the default -- it should probably 
                       // be changed by function that calls us.
      when ModSym:
         return Create_ModAbVarHomol([x]);

      when SeqEnum:
         assert #x gt 0 and Type(x[1]) eq ModSym;
         H`sign := Sign(x[1]); 
         H`level := 1;
         for M in x do
            H`level := LCM(H`level, Level(M));
            assert Sign(M) eq H`sign;
            assert Type(BaseField(M)) in {FldRat, FldCyc};
         end for;
         H`modsym := x;         
         H`dimension := &+[DimensionQ(M) : M in x];

      when RngIntElt:
         assert x eq 0;
         H`dimension := 0;
         H`integral := RSpace(ZZ,0);
         H`rational := VectorSpace(QQ,0);
         H`real := VectorSpace(RR,0);
         H`sign := 0;

      when ModTupFld:
         assert Dimension(x) eq 0;
         return Create_ModAbVarHomol(0);
      else:
         print "Unknown type = ", Type(x);
         assert false;
   end case;
   H`rational := VectorSpace(QQ,H`dimension);
   H`real := VectorSpace(RR,H`dimension);
   return H;
end function;

function Create_ModAbVarHomol_Quotient(H, pi)
   assert Type(H) eq ModAbVarHomol;
   assert IsMatrix(pi);
   assert Nrows(pi) eq Dimension(H);
   assert Ncols(pi) le Nrows(pi);
   assert Rank(pi) eq Ncols(pi);   // projection should be surjective!
   
   // The lattice in image of matrix pi induced by H:
   V := VectorSpace(QQ, Dimension(H));
   L := MakeLattice([(V!b)*pi : b in Basis(Lattice(H))]);
   return Create_ModAbVarHomol(L);
end function;

function Create_ModAbVarHomol_Subspace(H, V)
   assert Type(H) eq ModAbVarHomol;
   assert Type(V) eq ModTupFld;

   // The lattice in V induced by CD.
   LV := Intersect_Vector_Space_With_Lattice(V, Lattice(H));

   // Now write lattice wrt to Basis(V).
   W := VectorSpace(QQ,Dimension(V));
   L := MakeLattice([W!Coordinates(V, V!b) : b in Basis(LV)]);

   embed_matrix := RMatrixSpace(QQ, Dimension(V), Degree(V))!Basis(V);
   H2 := Create_ModAbVarHomol(L);
   H2`sign := H`sign;
   return H2, embed_matrix;
end function;

function Rational_to_ModSym(H)
   assert Type(H) eq ModAbVarHomol;
   if not assigned H`rational_to_modsym then
      Verbose("Rational_to_ModSym", "", Sprintf(
         "Computing rational to modular symbols transformation for %o.", H));
      assert assigned H`modsym;
      dimsum := [0];   
      for M in H`modsym do
         Append(~dimsum, DimensionQ(M) + dimsum[#dimsum]);
      end for;
      dims := [Dimension(M)*Degree(BaseField(M)) : M in H`modsym];
      H`rational_to_modsym := 
          function(x)
             v := [* *];
             for i in [1..#H`modsym] do
                M := H`modsym[i];
                V := VectorSpace(M);
                if Dimension(V) eq 0  then
                   Append(~v, M!0);
                else
                   z := [x[dimsum[i] + j] : j in [1..DimensionQ(H`modsym[i])]];
                   w := UnRestrictionOfScalars(z, BaseField(M));
                   Append(~v,M!(&+[V.j*w[j] : j in [1..Degree(w)]]));
		end if;
             end for;
             return v;
          end function;
   end if;
   return H`rational_to_modsym;
end function;

function Rational_to_ModSym_Matrix(H)
   assert Type(H) eq ModAbVarHomol;
   if not assigned H`rational_to_modsym_matrix then
      Verbose("Rational_to_ModSym", "", Sprintf(
         "Computing rational to modular symbols matrix for %o.", H));
      modsym := H`modsym;
      d := &+[Degree(BaseField(M))*Dimension(AmbientSpace(M)) : M in modsym];
      dimsum := [0];   
      for M in H`modsym do
         Append(~dimsum, DimensionQ(M) + dimsum[#dimsum]);
      end for;
      matrix := RMatrixSpace(QQ, Dimension(H), d)!0;
      r := 1;
      padding := 1;
      V := VectorSpace(QQ,d);
      for M in modsym do
         n := DimensionQ(AmbientSpace(M));
         for b in Basis(VectorSpace(M)) do 
            for s in Basis(BaseField(M)) do
               v := RestrictionOfScalars(s*b);
               for c in [padding..padding+n-1] do
                  matrix[r,c] := v[c-padding+1];
               end for;
               r +:= 1;
            end for;
         end for;
         padding +:= DimensionQ(AmbientSpace(M));
      end for;
      H`rational_to_modsym_matrix := matrix;
   end if;
   return H`rational_to_modsym_matrix;
end function;

function ModSym_to_Rational_Matrix(H)
   assert Type(H) eq ModAbVarHomol;
   if not assigned H`modsym_to_rational_matrix then
      Verbose("Rational_to_ModSym", "", Sprintf(
         "Computing modular symbols to rational matrix for %o.", H));
      A := Rational_to_ModSym_Matrix(H);
      Id := MatrixAlgebra(QQ,Dimension(H))!1;
 // IMPORTANT:
 // By computing the matrix this way, we are assuming that 
 // that we only apply the matrix to elements of the subspaces
 // of the ambient modular symbols spaces that define H.  
 // Applying to the ambient space is not well-defined, since
 // it depends on a choice of splitting, which we are making here.

 // SO That's why we multiply by a projection matrix TO MAKE IT WELL DEFINED!!!

      B := Transpose(Solution(Transpose(A),Id));
      PI := RestrictionOfScalars(ProjectionMatrix(H`modsym[1]));
      for i in [2..#H`modsym] do 
         PI := DirectSum(PI,RestrictionOfScalars(ProjectionMatrix(H`modsym[i])));
      end for;
      H`modsym_to_rational_matrix := PI*B;
     
   end if;
   return H`modsym_to_rational_matrix;
end function;

function ModSym_to_Rational(H)
   assert Type(H) eq ModAbVarHomol;
   if not assigned H`modsym_to_rational then
      assert assigned H`modsym;
      M := H`modsym;
      H`modsym_to_rational := 
         function(x)
            return H`rational!(&cat[Eltseq(RestrictionOfScalars(
                      Coordinates(VectorSpace(M[i]),VectorSpace(M[i])!Eltseq(ProjectionMap(M[i])(x[i]))))) : i in [1..#M]]);
         end function;
   end if;
   return H`modsym_to_rational;
end function;


intrinsic Print(H::ModAbVarHomol, level::MonStgElt)
{}
   printf "Modular abelian variety homology space of dimension %o", Dimension(H);
end intrinsic;

function HomologySignZeroDimension(H)
   return Dimension(H) div (H`sign eq 0 select 2 else 1);
end function;

function ModSymMap_to_HomologyMatrix(H1,H2,phi)
   assert Type(H1) eq ModAbVarHomol;   
   assert Type(H2) eq ModAbVarHomol;
   assert assigned H1`modsym;
   assert assigned H2`modsym;
   // Phi is a Q-linear function that takes sequences of elements of M1
   // and gives a sequence in M2.  This function returns a matrix, 
   // defined over Q, that gives the induced map from the rational
   // homology of H1 to the rational homology of H2.

   modsym1 := H1`modsym;
   modsym2 := H2`modsym;
   H1_to_modsym1 := Rational_to_ModSym(H1);
   modsym2_to_H2 := ModSym_to_Rational(H2);
   return RMatrixSpace(QQ, Dimension(H1), Dimension(H2))![
                         modsym2_to_H2(phi(H1_to_modsym1(b))) : 
                            b in Basis(VectorSpace(H1))];
end function;

function ModSymMatrix_to_HomologyMatrix(H1,H2,A)
   assert Type(H1) eq ModAbVarHomol;   
   assert Type(H2) eq ModAbVarHomol;
   assert assigned H1`modsym;
   assert assigned H2`modsym;
   // A is the Q-linear *matrix* induced by (restriction of scalars)
   // on a map that takes sequences of elements of M1 and gives 
   // a sequence in M2.  This function returns a matrix, 
   // defined over Q, that gives the induced map from the rational
   // homology of H1 to the rational homology of H2.

   modsym1 := H1`modsym;
   modsym2 := H2`modsym;
   H1_to_modsym1 := Rational_to_ModSym_Matrix(H1);
   modsym2_to_H2 := ModSym_to_Rational_Matrix(H2);
   return H1_to_modsym1*A*modsym2_to_H2;
end function;

function BasisChange_Lattice_to_Rational(H)
   assert Type(H) eq ModAbVarHomol;
   return MatrixAlgebra(QQ, Dimension(H))!&cat[Eltseq(b) : b in Basis(Lattice(H))];
end function;

function BasisChange_Lattice_to_Real(H)
   assert Type(H) eq ModAbVarHomol;
   return MatrixAlgebra(RR, Dimension(H))!&cat[Eltseq(b) : b in Basis(Lattice(H))];
end function;

function BasisChange_Rational_to_Lattice(H)
   assert Type(H) eq ModAbVarHomol;
   if not assigned H`basischange_rational_to_lattice then
      L := BasisChange_Lattice_to_Rational(H);
      H`basischange_rational_to_lattice := L^(-1);
   end if;
   return H`basischange_rational_to_lattice;
end function;

function BasisChange_Real_to_Lattice(H)
   assert Type(H) eq ModAbVarHomol;
   if not assigned H`basischange_real_to_lattice then
      L := BasisChange_Rational_to_Lattice(H);
      H`basischange_real_to_lattice := MatrixAlgebra(RR, Dimension(H))!Eltseq(L);
   end if;
   return H`basischange_real_to_lattice;
end function;

function HeckeTraces(H, n)
   assert assigned H`modsym;
   if not assigned H`hecke_traces then
      H`hecke_traces := [];
   end if;
   if #H`hecke_traces lt n then
      modsym := H`modsym;
      for i in [#H`hecke_traces..n] do 
         Append(~H`hecke_traces, &+[Trace(Trace(DualHeckeOperator(M,n))) : M in modsym]);
      end for;
   end if;
   a := H`hecke_traces;
   return [a[i] : i in [1..n]];
end function;


intrinsic IsCoercible(H::ModAbVarHomol, x::.) 
/* EXCLUDE FROM HANDBOOK */
       -> BoolElt, ModTupFldElt
{Coerce formal modular symbol x into H.}
   case Type(x):
      when SeqEnum:
         if #x ne 2 then
            return false, "Must be exactly two cusps.";
         end if;
         if not assigned H`modsym then
            return false, "Homology must be associated to modular symbols "*
                          "in order to coerce in a modular symbol.";
         end if;
         k := Weight(H`modsym[1]);
         t, z := IsCoercible(H, <PolynomialRing(QQ,2).1^(k-2),x>);
         if t then
            return true, z;
         else
            return false, "Not coercible";
         end if;
      when Tup, ModSymElt: // modular symbol
         if not assigned H`modsym then
            return false, "Homology must be associated to modular symbols "*
                          "in order to coerce in a modular symbol.";
         end if;
         X := [* *];
         for M in H`modsym do
            t, z := IsCoercible(AmbientSpace(M), x);
            if not t then
               return false, "Could not coerce modular symbol into homology.";
            end if;
            w := (ProjectionMap(M))(z);
            Append(~X, w);
         end for;
         return true, (ModSym_to_Rational(H))(X);
      when List: // of modular symbols
         if not assigned H`modsym then
            return false, "Homology must be associated to modular symbols "*
                          "in order to coerce in a modular symbol.";
         end if;
         X := [* *];
         require #x eq #H`modsym : "The number of modular symbols spaces "*
                         "must be same as length of list.";
         for i in [1..#H`modsym] do M := H`modsym[i];
            t, z := IsCoercible(AmbientSpace(M), x[i]);
            if not t then
               return false, "Could not coerce modular symbol into "* 
                "homology space ",i,".";
            end if;
            w := (ProjectionMap(M))(z);
            Append(~X, w);
         end for;
         return true, (ModSym_to_Rational(H))(X);
      else 
         return false, "Illegal coercion";
   end case;      
end intrinsic;

function AllModularSymbolsSpacesAreFull(H)
   assert Type(H) eq ModAbVarHomol;
   for M in ModularSymbols(H) do 
      if M ne CuspidalSubspace(AmbientSpace(M)) then
         return false;
      end if;
   end for;
   return true;
end function;

function HomologyLevel(H)
   return H`level;
end function;

