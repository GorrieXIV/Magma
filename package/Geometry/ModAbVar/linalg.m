freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: linalg.m
   DESC: standard-ish linear algebra functionality
         Variants of some of these functions also appear in the linalg.m
         files in the modular symbols package.  But this is NOT that file!

   Creation: 06/16/03 -- initial creation
      
 ***************************************************************************/

forward
   EchelonPolySeq,
   EvaluatePolynomial,
   HorizontallyStackMatrices,
   Intersect_Vector_Space_With_Lattice,
   IsMatrix,
   LatticeDirectSum,
   MakeLattice,
   MakeLatticeWithInnerProd,
   MatrixFromColumns,
   MatrixFromRows,
   MatrixLatticeBasis,
   Pivots,
   RestrictMatrix,
   RestrictMatrixDomain,
   RestrictionOfScalars,
   RestrictionOfScalars_AlgMatElt,
   RestrictionOfScalars_ModMatFldElt,
   RestrictionOfScalars_ModTupFld,
   RestrictionOfScalars_ModTupFldElt,
   RestrictionOfScalars_SeqEnum,
   Saturate,
   SaturateWithRespectToBasis,
   UnRestrictionOfScalars,
   UnRestrictionOfScalars_SeqEnum,
   VerticallyStackMatrices,
   ZeroMatrix,
   returnstheactionofRes;


import "rings.m": 
   QQ, ZZ;

function EchelonPolySeq(P, prec) 
// Put the sequence of poly's in Echelon form.
   if #P eq 0 then 
      return P;
   end if;
   R<q> := Parent(P[1]);
   V    := RSpace(BaseRing(R),prec);
   X    := sub<V|[[Coefficient(f,i) : i in [0..prec-1]] :  f in P]>;
   return [&+[v[i+1]*q^i : i in [0..prec-1]] : v in Basis(X)];
end function;

function MakeLattice(B)
   if #B eq 0 or #Eltseq(B[1]) eq 0 then
      return VectorSpace(QQ,0);
   end if;
   Mat := RMatrixSpace(Parent(B[1][1]),#B, #Eltseq(B[1]));
   X   := Mat!B;
   if Dimension(RowSpace(X)) eq 0 then
      return RowSpace(X);
   end if;
   return Lattice(X);
end function;


/***************************
 AVOID USING THIS!!!!
 Don't use lattices at all (note that 'Lattice' does an LLL).
 Instead do something like Saturation(Matrix(B)).
    --- Steve
****************************/
function Saturate(B) 
   t := Cputime();
   if #B gt 0 and Type(B[1]) eq SeqEnum then
      V := RSpace(Rationals(), #B[1]);
      B := [V|b : b in B];
   end if;
   L := MakeLattice(B);
   S := PureLattice(L);
   return S;
end function;

// V is a vector space and B is a basis for a space that contains V.
// This functions returns the lattice of elements of V that are
// contained in the Z-span of B.  In other wors, this returns
// the intersection of V with the Z-span of B.  (See function below.)
function SaturateWithRespectToBasis(V,B)
   if #B eq 0 or Dimension(V) eq 0 then
      A := RSpace(ZZ,Degree(V));
      return sub<A|[A!0]>;
   end if;
   // 1. Choose a basis for V.
 //BV := Basis(V);
   // 2. Write each element of BV as a linear combination of the
   //    basis vectors in B.
 //S := RSpaceWithBasis(B);
   B := Matrix(B);
   C := Solution( B, BasisMatrix(V) );
   // 3. Saturate C.
 //SatC := Saturate(C);
   SatC := Saturation(C);
   // 4. 
   if BaseRing(B) cmpne Integers() then
      SatC := ChangeRing( SatC, BaseRing(B) );
   end if;
   return Lattice( SatC * B );
   // TO DO : add an option to not MakeLattice, and change the calling functions accordingly
end function;

function Intersect_Vector_Space_With_Lattice(V, L)
   W := VectorSpace(QQ, Degree(V));
   B := [W!b : b in Basis(L)];
   return SaturateWithRespectToBasis(V,B);
end function;

function RestrictMatrix(A, x)  // written by Allan Steel.
   F := BaseRing(Parent(A));
   if Type(x) eq SeqEnum then
      B := Matrix(F, x);
   else
      assert Type(x) in {ModTupRng, ModTupFld};
      if Dimension(x) eq 0 then
         return MatrixAlgebra(F,0)!0;
      end if;
      B := Matrix(F, BasisMatrix(x));
   end if; 
   t, S := IsConsistent(B, B*A);
   if not t then
      return false;
   end if;
   return MatrixAlgebra(F, Nrows(B)) ! S;
end function;

function RestrictMatrixDomain(A, W)
   // Suppose A is a matrix that defines a linear transformation T
   // from V to Z and W is a subspace of V.  This function
   // compute the matrix that defines the restriction of T
   // to W with respect to Basis(W).
   F := BaseRing(Parent(A));
   return RMatrixSpace(F, Dimension(W), Ncols(A))![
            b*A : b in Basis(W)];
end function;

function Pivots(B)   // find pivots of reduced basis.
   return [Min(Support(b)): b in B];
end function;




function RestrictionOfScalars_AlgMatElt(A) 
/* The restriction of scalars to the rational field 
   of the matrix A over a number field.
   If alpha1,...,alphad is the basis for the number field F,
   and x1,...,xn is the basis that A is written with respect to,
   then this function returns the action of Res(A) on the basis
       alpha1*x1,...,alpha1*xn, alpha2*x1,...,.alpha2*xn, ..., 
               alphad*x1,...,alphad*xn.
   All matrices are viewed as acting from the right.
*/
   assert Type(A) eq AlgMatElt;
   K := BaseRing(Parent(A));
   assert Type(K) in {FldRat, FldCyc, FldNum};
   if Type(K) eq FldRat then
      return A;
   end if;
   n := Degree(Parent(A));
   d := Degree(K);
   if d eq 1 then
      return MatrixAlgebra(RationalField(),n)!A;
   end if;
   B := MatrixAlgebra(RationalField(),d*n)!0;
   basis := Basis(K);
   for i in [1..n] do
      v := A[i];
      for j in [1..d] do
         w := basis[j]*v;
         for k in [1..n] do
            x := w[k];
            for m in [1..d] do
               B[(j-1)*n+i, (m-1)*n+k] := x[m];
            end for;
         end for;
      end for;
   end for;
   return B;
end function;


function RestrictionOfScalars_ModMatFldElt(A) 
   assert Type(A) eq ModMatFldElt;
   K := BaseRing(Parent(A));
   assert Type(K) in {FldRat, FldCyc, FldNum};
   if Type(K) eq FldRat then
      return A;
   end if;
   n := Nrows(A);
   m := Ncols(A);
   d := Degree(K);
   if d eq 1 then
      return RMatrixSpace(RationalField(),n,m)!A;
   end if;
   B := RMatrixSpace(RationalField(),d*n,d*m)!0;
   basis := Basis(K);
   for i in [1..n] do
      v := A[i];
      for j in [1..d] do
         w := basis[j]*v;
         for k in [1..m] do
            x := w[k];
            for s in [1..d] do
               B[(j-1)*n+i, (s-1)*m+k] := x[s];
            end for;
         end for;
      end for;
   end for;
   return B;
end function;

function RestrictionOfScalars_ModTupFldElt(v) 
   assert Type(v) eq ModTupFldElt;
   K := Parent(v[1]);
   assert Type(K) in {FldRat, FldCyc, FldNum, RngInt};
   if Type(K) eq FldRat then
      return v;
   end if;
   V := VectorSpace(RationalField(),Degree(Parent(v))*Degree(K));
   return V![Eltseq(x)[i] : x in Eltseq(v), i in [1..Degree(K)]];

end function;

function RestrictionOfScalars_ModTupFld(V)
   K := BaseField(V);
   if Type(K) eq FldRat then
      return V;
   end if;
   assert Type(K) in {FldRat, FldCyc, FldNum, RngInt};
  
   BK := Basis(K);
   BV := Basis(V);                               // this order "a*v" is very important.
   return VectorSpaceWithBasis([VectorSpace(QQ,#BK*Degree(V))|
              RestrictionOfScalars(a*v) : v in BV, a in BK]);
end function;


function RestrictionOfScalars_SeqEnum(v) 
   assert Type(v) eq SeqEnum;
   if #v eq 0 then
      return VectorSpace(QQ,0)!0;
   end if;
   K := Parent(v[1]);
   assert Type(K) in {FldRat, FldCyc, FldNum, RngInt};
   if Type(K) eq FldRat then
      return VectorSpace(QQ, #v)!v;
   end if;
   V := VectorSpace(QQ,#v*Degree(K));
   return V![Eltseq(x)[i] : x in v, i in [1..Degree(K)]];

end function;


function RestrictionOfScalars(x)
//   if (Type(x) eq SeqEnum and (#x eq 0 or Type(x[1]) eq FldRat)) or
//      (Type(x) ne SeqEnum and (Type(BaseRing(Parent(x))) eq FldRat)) then
//      return x;
//   end if;
   case Type(x):
      when AlgMatElt:
         return RestrictionOfScalars_AlgMatElt(x);
      when ModMatFldElt:
         return RestrictionOfScalars_ModMatFldElt(x);
      when ModTupFldElt:
         return RestrictionOfScalars_ModTupFldElt(x);
      when ModTupFld:
         return RestrictionOfScalars_ModTupFld(x);
      when SeqEnum:
         return RestrictionOfScalars_SeqEnum(x);
      else:
         print "Type(x) = ", Type(x);
         assert false;
   end case;
end function;

/* Given a matrix or vector x over Q and a field K, 
   compute a matrix or vector y over K whose restriction 
   of scalars down to Q is x.  This is the inverse of
   the RestrictionOfScalars function above. */

function UnRestrictionOfScalars_SeqEnum(x, K)
   d := Degree(K);
   n := #x div d;
   return VectorSpace(K, n) ! [K![x[j+n*i] : i in [0..d-1]] : j in [1..n]];
end function;

function UnRestrictionOfScalars(x, K)
   if Type(K) eq FldRat and Type(x) ne SeqEnum then
      return x;
   end if;
   assert Type(x) in {ModTupFldElt, LatElt, SeqEnum};
   return UnRestrictionOfScalars_SeqEnum(Eltseq(x), K);
end function;

function VerticallyStackMatrices(X)
   assert Type(X) in {List, SeqEnum};
   if #X eq 0 then
      return ZeroMatrix(QQ,0);
   end if;
   assert Type(X[1]) in {AlgMatElt, ModMatFldElt};
   cols := [Ncols(x) : x in X];
   assert #Set(cols) eq 1;
   ncols := cols[1];
   nrows := &+[Nrows(x) : x in X];
   A := RMatrixSpace(BaseField(Parent(X[1])),nrows, ncols)!0;   
   j := 1;
   for x in X do 
      for r in [1..Nrows(x)] do 
         A[j] := x[r];
         j +:= 1;
      end for;
   end for;  
   return A;
end function;

function HorizontallyStackMatrices(X)
   Y := [* *];
   for x in X do
      Append(~Y,Transpose(x));
   end for;
   return Transpose(VerticallyStackMatrices(Y));
end function;

function IsMatrix(A)
   return Type(A) in {AlgMatElt,  ModMatFldElt};
end function;


function MatrixFromRows(A, rows)
   assert IsMatrix(A);
   return RMatrixSpace(BaseRing(Parent(A)), #rows, Ncols(A))![A[i] : i in rows];
end function;

function MatrixFromColumns(A, cols)
   assert IsMatrix(A);
   return Transpose(MatrixFromRows(Transpose(A),cols));
end function;

function LatticeDirectSum(L1,L2)
   // get around nonexistence of zero lattice in MAGMA!
   if Degree(L1) eq 0 then
      return L2;
   elif Degree(L2) eq 0 then
      return L1;
   else
      return DirectSum(L1,L2);
   end if;
end function;


function MatrixLatticeBasis(X)
   // Given a sequence of matrices in M_{mxn}(Q), 
   // compute a basis for the lattice they generate.
   assert Type(X) eq SeqEnum;
   if #X eq 0 then
      return X;
   end if;
   assert Type(X[1]) in {AlgMatElt, ModMatFldElt, ModMatRngElt};
   m := Nrows(X[1]);
   n := Ncols(X[1]);
   V := VectorSpace(QQ,n*m);
   B := [V!Eltseq(x) : x in X];
   return [Parent(X[1])!Eltseq(b) : b in Basis(MakeLattice(B))];

end function;

function ZeroMatrix(K,n)
   return MatrixAlgebra(K,n)!0;
end function;


function MakeLatticeWithInnerProd(B,M)
   V   := VectorSpace(Rationals(), Nrows(M));
   Mat := RMatrixSpace(Rationals(), #B, Dimension(V));
   X   := Mat!B;
   return Lattice(X,M : CheckPositive := false);
end function;

function EvaluatePolynomial(f, x)
   assert Type(f) eq RngUPolElt;
   return &+[Parent(x)|Coefficient(f,n)*x^n : n in [0..Degree(f)]];
end function;
