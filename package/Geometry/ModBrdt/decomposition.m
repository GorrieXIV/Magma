freeze;
////////////////////////////////////////////////////////////////////
//                                                                //  
//                 Brandt Module Decompositions                   // 
//                         David Kohel                            // 
//                    Created September 2000                      //
//                                                                // 
////////////////////////////////////////////////////////////////////

import "brandt_modules.m" : ExtendHecke;
import "brandt_ideals.m" : ExtendAdjacencyHecke;

////////////////////////////////////////////////////////////////////
//                                                                //  
//                        Decomposition                           //  
//                                                                //  
////////////////////////////////////////////////////////////////////

function Submodule(M,S)
   N := New(ModBrdt);
   N`AmbientModule := AmbientModule(M);
   N`Module := sub< M`Module | S >;
   N`IsFull := Dimension(N`Module) eq Degree(M);
   N`RamifiedPrimes := M`RamifiedPrimes;
   N`Conductor := M`Conductor;
   N`BaseRing := M`BaseRing;
   N`HeckePrecision := 0;
   N`HeckePrimes := [ Integers() | ];
   Mat := MatrixAlgebra(N`BaseRing,Dimension(N`Module));
   N`HeckeOperators := [ Mat | ];
   return N;
end function;

intrinsic EisensteinSubspace(M::ModBrdt) -> ModBrdt
   {}
   // Should be modified for Brandt modules or non-Eichler orders
   // nonmaximal at primes dividing the discriminant.
   if IsFull(M) then
      D := Discriminant(M);
      m := Conductor(M);
      if GCD(D,m) eq 1 then
         r := LCM(M`AutoNums);  
         eis := M`Module ! [ r div w : w in M`AutoNums ];
         E := Submodule(M,[eis]);
         E`IsIndecomposable := true;
      else  
         h := Dimension(M);
         GenSeq := [ Genus(LatticeWithGram(A)) : A in M`NormGrams[1..h] ];
         GenSet := [ GenSeq[1] ];
         for H in GenSeq do
            if &and [ G ne H : G in GenSet ] then
               Append(~GenSet,H);
            end if;
         end for;   
         inds := [ [ i : i in [1..h] | G eq GenSeq[i] ] : G in GenSet ];
         B := [ M`Module | ];
         for I in inds do
            r := LCM([ M`AutoNums[i] : i in I ]);  
            eis := M`Module ! 
               [ (i in I select r else 0) div M`AutoNums[i] : i in [1..h] ];
            Append(~B,eis);
         end for;
         E := Submodule(M,B);
         E`IsIndecomposable := false;
      end if;  
      return E;
   end if;
   return M meet EisensteinSubspace(AmbientModule(M));
end intrinsic;

intrinsic IsEisenstein(M::ModBrdt) -> ModBrdt
    {Returns true if and only if M is contained in the Eisenstein 
    subspace of its abmient module.}
    return M subset EisensteinSubspace(AmbientModule(M));
end intrinsic;

intrinsic CuspidalSubspace(M::ModBrdt) -> ModBrdt
    {}
    // Should be modified for Brandt modules or non-Eichler orders
    // nonmaximal at primes dividing the discriminant.
    if IsFull(M) then
	D := Discriminant(M);
	m := Conductor(M);
	if GCD(D,m) eq 1 then
	    g := Dimension(M);
	    B := [ X | X.i-X.(i+1) : i in [1..g-1] ] where X := M`Module;
	    S := Submodule(M,B);
	    if Dimension(S) eq 1 then
		S`IsIndecomposable := true;
	    end if;
	else   
	    h := Dimension(M);
	    GenSeq := [ Genus(LatticeWithGram(A)) : A in M`NormGrams[1..h] ];
	    GenSet := [ GenSeq[1] ];
	    for H in GenSeq do
		if &and [ G ne H : G in GenSet ] then
		    Append(~GenSet,H);
		end if;
	    end for;   
	    inds := [ [ i : i in [1..h] | G eq GenSeq[i] ] : G in GenSet ];
	    B := [ M`Module | ];
	    for I in inds do
		B cat:= [ M`Module | 
		Eltseq(M.I[i]-M.I[i+1]) : i in [1..#I-1] ];
	    end for;
	    S := Submodule(M,B);
	    S`IsIndecomposable := false;
	end if;
	return S;
    end if;
    return M meet CuspidalSubspace(AmbientModule(M));
end intrinsic;

intrinsic IsCuspidal(M::ModBrdt) -> ModBrdt
    {Returns true if and only if M is contained in the cuspidal
    subspace of its abmient module.}
    return M subset CuspidalSubspace(AmbientModule(M));
end intrinsic;

intrinsic Decomposition(M::ModBrdt,B::RngIntElt 
   : Proof := true, Sort := false ) -> SeqEnum
   {Decomposition of M with respect to the Hecke operators T_p 
   for p up to the bound B.}

   require Characteristic(BaseRing(M)) notin {2,3} :
       "The characteristic of the base ring of " *
       "argument 1 must be different from 2 and 3.";
   if Dimension(M) eq 0 then return []; end if;
   if not assigned M`FactorBases then   
      decomp := [ EisensteinSubspace(M), CuspidalSubspace(M) ];
      decomp := [ N : N in decomp | Dimension(N) ne 0 ];
      M`DecompositionBound := 1; 
   else 
      decomp := [ Submodule(M,B) : B in M`FactorBases ];
      for i in [1..#M`FactorBases] do
         decomp[i]`IsIndecomposable := M`FactorIsIndecomposable[i];
      end for; 
   end if;
   done := &and [ assigned N`IsIndecomposable 
                     and N`IsIndecomposable : N in decomp ];

   // First decompose with respect to known Atkin-Lehner operators.
   // We don't currently treat Atkin-Lehner operators for primes not
   // dividing the discriminant, so we restrict to those remaining.

   /* Begin Atkin-Lehner decomposition. */
   if not done then
      prms := AtkinLehnerPrimes(M);
      vprint Brandt : "Decomposing with respect to Atkin-Lehner primes.";
      for p in prms do
         vprint Brandt : "  Prime =", p;
         tyme := Cputime();
	 // The 'meet' function is too slow here. Why?
if false then
         W := AtkinLehnerOperator(M,p);
         S := [ Kernel(W-1), Kernel(W+1) ];
         decomp := &cat[  
            [ Submodule(N,Basis(N`Module meet V)) : V in S ] : N in decomp ];
         decomp := [ N : N in decomp | Dimension(N) ne 0 ];
         for i in [1..#decomp] do
            if Dimension(decomp[i]) eq 1 then
               decomp[i]`IsIndecomposable := true;
            end if; 
         end for;
else 
         ndecomp := [ Parent(M) | ];   
         for N in decomp do
             Q := BasisMatrix(N);
             W := AtkinLehnerOperator(N,p);
             PlusMinus := [ Kernel(W+1), Kernel(W-1) ]; 
             for V in PlusMinus do
                if Dimension(V) ne 0 then
   	           S := [ M`Module | x*Q : x in Basis(V) ];
                   Append(~ndecomp,Submodule(N,S));
                end if; 
             end for;
         end for;
         decomp := ndecomp;
         for i in [1..#decomp] do
            if Dimension(decomp[i]) eq 1 then
      	       decomp[i]`IsIndecomposable := true;
            end if; 
         end for;
end if;
         vprint Brandt, 2 : "    Dimensions:", 
               [ Dimension(N) : N in decomp ];
         vprint Brandt, 2 : "    IsIndecomp:", 
               [ assigned N`IsIndecomposable select 1 
                    else 0 : N in decomp ];
         vprint Brandt, 2 : "    Decomposition time:", Cputime(tyme);
      end for;   
   end if;
   done := &and [ assigned N`IsIndecomposable 
                     and N`IsIndecomposable : N in decomp ];
   /* End Atkin-Lehner decomposition. */

   if not done and M`DecompositionBound lt B then
      vprint Brandt, 2 : "Begin Hecke decomposition.";
      vprint Brandt, 2 :   
         "Hecke operators known up to bound", M`HeckePrecision;
      vprint Brandt : "Decomposing up to new bound", B;
      p := NextPrime(M`DecompositionBound);
      i := Floor(Log(2,M`DecompositionBound));
      while p le B do
         // Check precomputed Hecke operators...
         if p le B and p gt 2^i then 
            i +:= 1; 
            vprint Brandt, 2 : 
               "  Recomputing Hecke operators up to bound", Min(B,2^i);
	    if assigned AmbientModule(M)`NormGrams then
		tyme := Cputime();
   	        ExtendHecke(M,Min(B,2^i));
                vprint Brandt, 2 : "    Hecke time:", Cputime(tyme);
	    else
   	        ExtendAdjacencyHecke(M,[p]);
	    end if;
         end if;
         vprint Brandt : "  Prime =", p;
         M`DecompositionBound := p;
         // Compute individual operators...
         // T := HeckeOperator(AmbientModule(M),p);
         tyme := Cputime();
         decomp := [ N : N in decomp | 
               assigned N`IsIndecomposable and N`IsIndecomposable ] 
            cat &cat[ 
               Decomposition(N,HeckeOperator(N,p) : Proof := Proof) 
                  : N in decomp | not (assigned N`IsIndecomposable 
                                          and N`IsIndecomposable) ]; 
         vprint Brandt, 2 : "    Dimensions:", 
            [ Dimension(N) : N in decomp ];
         vprint Brandt, 2 : "    IsIndecomp:", 
            [ assigned N`IsIndecomposable select 1 else 0 : N in decomp ];
         vprint Brandt, 2 : "    Decomposition time:", Cputime(tyme);
         if &and[ assigned N`IsIndecomposable and 
                     N`IsIndecomposable : N in decomp ] then 
            M`DecompositionBound := Infinity();
            break; 
         end if; 
         p := NextPrime(p);
      end while;
   end if;
   if Sort and Characteristic(BaseRing(M)) eq 0 then
      decomp := SortDecomposition(decomp); 
   end if;
   M`FactorBases := [ [ Eltseq(x) : x in Basis(N) ] : N in decomp ];
   M`FactorIsIndecomposable := [ 
      assigned N`IsIndecomposable select N`IsIndecomposable 
      else false : N in decomp ];
   if not IsFull(M) then
      ; // Update decomposition of ambient module?
   end if;
   return decomp;
end intrinsic;

intrinsic Decomposition(M::ModBrdt,T::AlgMatElt : 
   Proof := true, Sort := false) -> SeqEnum
   {Decomposition of M with respect to the matrix operator T.}

   require Dimension(M) eq Degree(Parent(T)) : 
      "Arguments have incompatible degrees.";
   if Dimension(M) eq 0 then return []; end if;
   if assigned M`IsIndecomposable and M`IsIndecomposable then 
      return [ M ]; 
   end if;
   if Dimension(M) eq 1 then 
      M`IsIndecomposable := true; 
      return [ M ]; 
   end if;
   decomp := [ Parent(M) | ];
   if Proof then
      chi := CharacteristicPolynomial(T);
   else
      chi := CharacteristicPolynomial(T : Al := "Modular", Proof := Proof);
   end if;
   fac := Factorization(chi);
   for f in fac do
      N := Kernel(Evaluate(f[1],T),M);
      if f[2] eq 1 then
         N`IsIndecomposable := true;
      end if;
      Append(~decomp,N);
   end for;
   if Sort then
      decomp := SortDecomposition(decomp); 
   end if;
   return decomp;
end intrinsic;

intrinsic IsIndecomposable(S::ModBrdt,B::RngIntElt) -> BoolElt
   {True if and only if S is indecomposable under the action of 
   the Hecke operators up to the bound B.}

   if assigned S`IsIndecomposable then
      return S`IsIndecomposable;
   end if;   
   if Dimension(S) eq 1 then
      S`IsIndecomposable := true;
      return S`IsIndecomposable;
   end if;
   D := Discriminant(S);
   N := Level(S);
   for p in AtkinLehnerPrimes(S) do
      vprint Brandt, 2 : "Considering Atkin-Lehner decomposition at", p;
      W := AtkinLehnerOperator(S,p);
      f := CharacteristicPolynomial(W : Al := "Modular", Proof := false);
      charfac := Factorization(f);
      if #charfac gt 1 then
         S`IsIndecomposable := false;
         return S`IsIndecomposable;
      end if; 
   end for;
   p := 2;
   while N mod p eq 0 do 
      p := NextPrime(p); 
   end while; 
   while p le B do 
      vprint Brandt, 2 : "Considering decomposition at", p;
      Tp := HeckeOperator(S,p);
      f := CharacteristicPolynomial(Tp : Al := "Modular", Proof := false);
      charfac := Factorization(f);
      if #charfac eq 1 and charfac[1][2] eq 1 then
         S`IsIndecomposable := true;
         return S`IsIndecomposable;
      elif #charfac gt 1 then
         S`IsIndecomposable := false;
         return S`IsIndecomposable;
      end if;
      p := NextPrime(p);
   end while;
   return false;   
end intrinsic;

function MergeSort(C,D)
   i := 1; // index for C
   j := 1; // index for D
   while true do
      if i gt #C then
         break;
      elif j gt #D then
         D cat:= C[i..#C];
         break;
      elif C[i] lt D[j] then
         Insert(~D,j,C[i]);  
         i +:= 1;
      else 
         j +:= 1;
      end if;
   end while;
   return D;
end function;

intrinsic SortDecomposition(D::[ModBrdt]) -> SeqEnum
   {Sort the sequence of Brandt modules according to the 'lt' operator.}
   r := #D;
   vprint Brandt, 2 : "Sorting sequence of length", r;  
   if r eq 2 then
      vprintf Brandt, 2 : "   Dimensions: %o, %o\n", 
         Dimension(D[1]), Dimension(D[2]);  
      if D[2] lt D[1] then
         vprint Brandt, 2 : "   Reversing";  
         Reverse(~D);
      else
         vprint Brandt, 2 : "   Returning";  
      end if; 
   elif r gt 2 then
      s := r div 2;
      D := MergeSort(
              SortDecomposition(D[1..s]),
              SortDecomposition(D[s+1..r]) );
   end if;
   return D;
end intrinsic;

intrinsic OrthogonalComplement(M::ModBrdt) -> ModBrdt
    {}
    N := Kernel(InnerProductMatrix(M)*Transpose(BasisMatrix(M)));
    return Submodule(AmbientModule(M),Basis(N));
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //  
//                       Linear Algebra                           //  
//                                                                //  
////////////////////////////////////////////////////////////////////

intrinsic BasisMatrix(N::ModBrdt) -> ModMatRngElt
   {The matrix whose rows are the basis elements of N.}
   return Matrix(Dimension(N),Degree(N),
                    &cat[ Eltseq(x) : x in Basis(N) ]);
end intrinsic;

intrinsic AtkinLehnerEigenvalue(M::ModBrdt,q::RngIntElt) -> RngElt
   {The trace of the qth Atkin-Lehner opertor on the 
   indecomposable Brandt module S.}

   D := Discriminant(M);
   N := Level(M);
   val, p := IsPrimePower(q);
   require val : "Argument 2 must be a prime power.";
   require N mod q eq 0 and GCD(N div q,q) eq 1 :  
      "Argument 2 must be an exact divisor of the level of argument 1.";;
   W := AtkinLehnerOperator(M,q);
   if W eq 1 then return 1; elif W eq -1 then return -1; end if;
   require false : "Argument 1 is not indecomposable under Atkin-Lehner.";
end intrinsic;

function MatrixKernel(T,V)
   return Kernel(T) meet V;
end function;

intrinsic Kernel(T::AlgMatElt,M::ModBrdt) -> ModBrdt
   {}
   Mat := Parent(T); 
   require BaseRing(M) eq BaseRing(Mat) :
      "Arguments have incompatible base rings.";
   A := AmbientModule(M);
   U := M`Module; 
   if Dimension(M) eq Degree(Mat) then
      V := Kernel(T);
      t := Dimension(V);
      C := BasisMatrix(V)*BasisMatrix(U);
      return Submodule(M,[ C[i] : i in [1..t] ]);
   elif Degree(M) eq Degree(Mat) then
      S := Basis(Kernel(T) meet M`Module); 
      return Submodule(M,S);
   end if;
   require false : "Arguments have incompatible degrees.";
end intrinsic;

intrinsic 'meet'(M::ModBrdt,N::ModBrdt) -> ModBrdt
   {}
   if M eq N then return M; end if; 
   A := AmbientModule(M);
   require AmbientModule(N) eq A : "Modules have no covering module.";
   if IsFull(M) then
      return N;
   elif IsFull(N) then 
      return M;
   end if; 
   return Submodule(A,Basis(M`Module meet N`Module));
end intrinsic;

intrinsic 'subset'(M::ModBrdt,N::ModBrdt) -> BoolElt
   {}
   if M eq N then return true; end if; 
   A := AmbientModule(M);
   require AmbientModule(N) eq A : "Modules have no covering module.";
   return M`Module subset N`Module;
end intrinsic;

intrinsic CharacteristicPolynomial(T::AlgMatElt,M::ModBrdt : Proof := true) 
   -> RngUPolElt
   {The characteristic polynomial of T on M.}
   require Degree(Parent(T)) eq Degree(M) : 
      "Arguments have incompatible dimensions.";
   require BaseRing(Parent(T)) cmpeq BaseRing(M) : 
      "Arguments have incompatible base rings.";
   return CharacteristicPolynomial(T,M`Module : Proof := Proof);
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //  
//          Ordering of Indecomposable Brandt Submodules          //  
//                                                                //  
////////////////////////////////////////////////////////////////////

intrinsic 'lt'(R::ModBrdt,S::ModBrdt : Bound := 101) -> BoolElt
   {Comparison operator extending that of Cremona.}
/* 
   (1) R < S if dim(R) < dim(S);
   (2) R < S if IsEisenstein(R) and IsCuspidal(S)
   (3) When the weight is two and the character is trivial:
       order by Wq eigenvalues, starting with *smallest* p|N and 
       with "+" being less than "-";
   (4) Order by abs(trace(a_p^i)), p not dividing the level, and 
       i = 1,...,g = dim(R) = dim(S), with the positive one being 
       smaller in the the event of equality,
*/
   M := AmbientModule(R);
   require AmbientModule(S) eq M : 
      "Arguments must be components of the same Brandt module.";
   /*
   require IsIndecomposable(R) and IsIndecomposable(S) :
      "Arguments must be indecomposable Brandt modules.";
   */
   if R eq S then return false; end if;
   g := Dimension(S);
   if Dimension(R) lt g then 
      return true; 
   elif Dimension(R) gt g then 
      return false; 
   end if;
   if IsEisenstein(R) and IsCuspidal(S) then
       return true;
   elif IsEisenstein(S) and IsCuspidal(R) then
       return false;
   end if;
   N := Level(S);
   D := Discriminant(S);
   atkin_lehner := AtkinLehnerPrimes(M);
   for p in atkin_lehner do
      q := p^Valuation(N,p);
      eR := AtkinLehnerEigenvalue(R,q); 
      eS := AtkinLehnerEigenvalue(S,q); 
      if eR lt eS then
         return true; 
      elif eR gt eS then
         return false; 
      end if;
   end for;   
   p := 2;
   while p le Bound do
      Tp := HeckeOperator(M,p);
      fR := CharacteristicPolynomial(Tp,R : Proof := false); 
      fS := CharacteristicPolynomial(Tp,S : Proof := false); 
      if p notin atkin_lehner and fR ne fS then
         for i in [1..g] do
            aS := HeckeTrace(S,p^i : Proof := false);
            aR := HeckeTrace(R,p^i : Proof := false);
            if Abs(aR) lt Abs(aS) then
               return true; 
            elif Abs(aR) gt Abs(aS) then
               return false; 
            elif aR gt aS then
               return true; 
            elif aR lt aS then
               return false; 
            end if;
         end for; 
      end if;   
      p := NextPrime(p);
   end while;
   return false;
end intrinsic;

intrinsic 'gt'(N::ModBrdt,M::ModBrdt) -> BoolElt
    {}
    return M lt N;
end intrinsic;

