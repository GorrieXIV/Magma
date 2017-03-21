///////////////////////////////////////////////////////////////////////////////
/////////       Copyright 2016 Roland D. Barrolleta, Jaume Pujol        ///////
/////////                     and Merce Villanueva                      ///////
/////////                                                               ///////
/////////       This program is distributed under the terms of GNU      ///////
/////////               General Public License                          ///////
/////////                                                               ///////
///////////////////////////////////////////////////////////////////////////////

/******************************************************************************
    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
******************************************************************************/


/************************************************************/
/*                                                          */
/* Project name: Codes over Fq in MAGMA                     */
/* File name: PermDecodeOverFq.m                            */
/*                                                          */
/* Comment: Package developed within the CCSG group.        */
/*                                                          */
/* Authors: R. D. Barrolleta, J. Pujol and M. Villanueva	*/
/*                                                          */
/* Revision version and last date: v1.0   2016/02/29        */
/*                                 v1.1   2016/04/30        */
/*                                 v1.2   2016/05/11        */       
/*                                                          */
/************************************************************/
//Uncomment freeze when package finished
freeze;

intrinsic PermDecodeOverFq_version() -> SeqEnum
{Return the current version of this package.}
    version := [1,2];
    return version;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
declare verbose IsPDSetFlag, 3;
///////////////////////////////////////////////////////////////////////////////

/******************************************************************
	GLOBAL VARIABLES
*******************************************************************/		
zero_Code := func<C | Dimension(C) eq 0>;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////				PERMUTATION DECODE FUNCTIONS                        ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/****************************************************************/
/*                                                              */  
/* Function name: ExistPermutationInPDset                       */
/* Parameters: SMonMat, I, v                                    */
/* Function description: Given a PD-set SMonMat, an information */
/*   set I, and a vector v over GF(q), return whether there is  */
/*   a monomial matrix in SMonMat such that moves the nonzero   */
/*   coordinates of v out of the information coordinates.       */  
/*   The PD-set and the information set are given as sequences. */
/*   The PD-set is given as a sequence of monomial matrices.    */
/*                                                              */
/****************************************************************/
ExistPermutationInPDset := function (SMonMat, I, v)
    for M in SMonMat do
        if IsZero([(v*M)[i] : i in I]) then
            return true;
        end if;
    end for;
    return false;
end function;

/****************************************************************/
/*                                                              */  
/* Function name: IsSubsetOfMPAut                               */
/* Parameters: C, SMonMat                                       */
/* Function description: Given a linear code C over GF(q) of    */
/*   length n, and a sequence SMonMat of monomial matrices of   */
/*   order n over GF(q), return whether SMonMat is a subset     */
/*   of MAut(C), that is, the monomial automorphism group of C. */ 
/*                                                              */
/****************************************************************/
IsSubsetOfMPAut := function (C, SMonMat)
    G := GeneratorMatrix(C);
    for M in SMonMat do
        if LinearCode(G*M) ne C then
            return false;
        end if;
    end for;
    return true;
end function;

/****************************************************************/
/*                                                              */  
/* Function name: IsInformationSet                              */
/* Parameters: C, I                                             */
/* Function description: Given a linear code C over GF(q) of    */
/*   length n and dimension k, and a sequence I of integers in  */
/*   {1..n}, return whether I is an information set of C.       */ 
/*                                                              */
/****************************************************************/
IsInformationSet := function (C, I)
    k := Dimension(C);
    if (#I eq k) then
        return Rank(Submatrix(GeneratorMatrix(C), [1..k], Setseq(I))) eq k;
    end if;     
    return false;
end function;

/****************************************************************/
/*                                                              */
/* Function name: IsPermutationDecodeSet                        */
/* Parameters: C, I, S, s                                       */
/* Function description: Given an [n,k] linear code C over      */
/*   GF(2); a sequence I in {1,...,n}, a sequence S of elements */
/*   in the symmetric group Sym(n) of permutations on the set   */
/*   {1,...,n}, and an integer s in {1,...,t}, where t is the   */
/*   error-correcting capability of C, return true if and       */
/*   only if S is an s-PD-set for C with respect to the         */
/*   information set I.                                         */               
/* Input parameters description:                                */
/*   - C : Linear code over GF(2)                               */
/*   - I : Subset of integers in {1..n} as a sequence           */
/*   - S : Subset of permutations acting on {1..n} as a sequence*/
/*   - s : Integer in {1..t}, t is the correcting capability    */
/* Output parameters description:                               */
/*   - Boolean, true if S is an s-PD-set and false otherwise    */
/*                                                              */
/* Signature: (<CodeLinFld> C, <[RngIntElt]> I,                 */
/*              <[GrpPermElt]> S, <RngIntElt> s) -> BoolElt     */
/*                                                              */
/****************************************************************/
intrinsic IsPermutationDecodeSet(C::CodeLinFld, I::[RngIntElt], S::[GrpPermElt], 
                                                        s::RngIntElt) -> BoolElt
{
Given an [n,k] linear code C over a finite field K; a sequence I in [1,...,n]; 
a sequence S of elements in the group of monomial matrices of order n over K; 
and an integer s in [1,...,t], where t is the error-correcting capability of C, 
return true if and only if S is an s-PD-set for C with respect to the information 
set I. The parameter S can also be given as a sequence of elements in the 
symmetric group Sym(n) of permutations on the set [1,...,n], when C is binary.  

Depending on the length of the code C, its dimension k, and the integer s, this 
function could take some time to compute whether S is an s-PD-set for C with respect 
to I. Specifically, if the function returns true, it is necessary to check
(k choose 1)*( n-k choose s-1) + ... + (k choose i)*( n-k choose s-i) s-sets.

The verbose flag IsPDSetFlag is set to level 0 by default. If it is set to level 1, 
the total time used to check the condition is shown. Moreover, the reason why the 
function return false is also shown, that is, whether I is not an information set, 
S is not a subset of the monomial automorphism group of C or S is not an s-PD-set. 
If it is set to level 2, the percentage of the computation process performed is 
also printed.
}
    require not(zero_Code(C)): "Code cannot be the zero code";
    require #BaseField(C) eq 2: "Code must be over a finite field of size 2";
    n := Length(C);
    requirerange s, 1, n;
 
    require not IsEmpty(S): "Argument 3 cannot be an empty sequence";   
    require (Degree(Parent(S[1])) eq n): 
          "Argument 3 should contain permutations acting on a set of cardinality", n;
    k := #I;
    require (k ge 1): "Argument 2 cannot be an empty sequence";
    require (Min(I) ge 1) and (Max(I) le n): 
                                     "Argument 2 should be a subset of", [1..n];
    
    S := [MonomialMatrix([GF(2)!1^^n], p) : p in S];
    return IsPermutationDecodeSet(C, I, S, s);
    
end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: IsPermutationDecodeSet                        */
/* Parameters: C, I, S, s                                       */
/* Function description: Given an [n,k] linear code C over a    */
/*   finite field K; a sequence I in {1,...,n}; a sequence S of */
/*   elements in the group of monomial matrices of order n over */
/*   K; and an integer s in {1,...,t}, where t is the error-    */
/*   correcting capability of C, return true if and only if S   */
/*   is an s-PD-set for C with respect to the information set I.*/
/* Input parameters description:                                */
/*   - C : Linear code over GF(q)                               */
/*   - I : Subset of integers in {1..n} as a sequence           */
/*   - S : Subset of monomial matrices as a sequence            */
/*   - s : Integer in {1..t}, t is the correcting capability    */
/* Output parameters description:                               */
/*   - Boolean, true if S is an s-PD-set and false otherwise    */
/*                                                              */
/* Signature: (<CodeLinFld> C, <[RngIntElt]> I,                 */
/*              <[AlgMatElt]> S, <RngIntElt> s) -> BoolElt     */
/*                                                              */
/****************************************************************/
intrinsic IsPermutationDecodeSet(C::CodeLinFld, I::[RngIntElt], S::[AlgMatElt], 
                                                        s::RngIntElt) -> BoolElt
{
Given an [n,k] linear code C over a finite field K; a sequence I in [1,...,n]; 
a sequence S of elements in the group of monomial matrices of order n over K; 
and an integer s in [1,...,t], where t is the error-correcting capability of C, 
return true if and only if S is an s-PD-set for C with respect to the information 
set I. The parameter S can also be given as a sequence of elements in the 
symmetric group Sym(n) of permutations on the set [1,...,n], when C is binary.  

Depending on the length of the code C, its dimension k, and the integer s, this 
function could take some time to compute whether S is an s-PD-set for C with respect 
to I. Specifically, if the function returns true, it is necessary to check
(k choose 1)*( n-k choose s-1) + ... + (k choose i)*( n-k choose s-i) s-sets.

The verbose flag IsPDSetFlag is set to level 0 by default. If it is set to level 1, 
the total time used to check the condition is shown. Moreover, the reason why the 
function return false is also shown, that is, whether I is not an information set, 
S is not a subset of the monomial automorphism group of C or S is not an s-PD-set. 
If it is set to level 2, the percentage of the computation process performed is 
also printed.
}    
    require not(zero_Code(C)): "Code cannot be the zero code";
    n := Length(C);
    requirerange s, 1, n;

 
    require not IsEmpty(S): "Argument 3 cannot be an empty sequence";   
    require (Degree(Parent(S[1])) eq n): 
          "Argument 3 should contain monomial matrices of order", n;
    require BaseRing(S[1]) eq BaseField(C): 
          "Arguments 1 and 3 should be over the same finite field";
    k := #I;
    require (k ge 1): "Argument 2 cannot be an empty sequence";
    require (Min(I) ge 1) and (Max(I) le n): 
                                     "Argument 2 should be a subset of", [1..n];
    
    ///////////////////////////////////////////////////////////////////
	iniTime := Cputime();
	vprintf IsPDSetFlag,2: "Checking whether I is an information set...\n";
    ///////////////////////////////////////////////////////////////////

    I := Set(I);  // Eliminate repeated coordinate positions in I
    S := Set(S);  // Eliminate repeated permutations in S

    ///////////////////////////////////////////////////////////////////
	vprintf IsPDSetFlag,2: 
                  "Checking whether S is in the permutation automorphism group...\n";
    ///////////////////////////////////////////////////////////////////
   
    if not IsInformationSet(C, I) then
        vprintf IsPDSetFlag,1: "Argument 2 is not an information set for C\n";
        return false; 
    end if;
    
    if not IsSubsetOfMPAut(C, S) then 
        vprintf IsPDSetFlag,1: 
        "Argument 3 is not a subset of the monomial automorphism group of C\n";   
        return false;     
    end if;
             
    ///////////////////////////////////////////////////////////////////
	vprintf IsPDSetFlag,2: "Checking whether S is an s-PD-set...\n";
    ///////////////////////////////////////////////////////////////////

    numCheckSets := &+[ Binomial(k, i) * Binomial(n-k, s-i) : i in [1..s]];
    
    ///////////////////////////////////////////////////////////////////
	tenpc := numCheckSets div 10 + 1; //for verbose flag
    ///////////////////////////////////////////////////////////////////
    
    cont := 0;
    V := VectorSpace(BaseField(C), n);
    checkSet := {1..n} diff I;
    for numErrors in [1..s] do
        allSetsErrorsInfo := Subsets(I, numErrors);
        for errorsSetInfo in allSetsErrorsInfo do
            allSetsErrorsCheck := Subsets(checkSet, s-numErrors);
            for errorsSetCheck in allSetsErrorsCheck do
                errorSet := errorsSetInfo join errorsSetCheck;
                
                errorVec := V!0;
                for i in errorSet do
                    errorVec[i] := 1;
                end for;
                
                cont := cont + 1;
                //////////////////////////////////////////////////////////
                if cont mod tenpc eq 0 then
                    vprintf IsPDSetFlag, 2: "%o %%\n",(cont div tenpc * 10);
                end if;
                //////////////////////////////////////////////////////////
                
                if not ExistPermutationInPDset(S, I, errorVec) then
                
                    /////////////////////////////////////////////////////
                    vprintf IsPDSetFlag,1: "Argument 3 is not an s-PD-set\n";
	                vprintf IsPDSetFlag,1: "Took %o seconds (CPU time)\n", Cputime(iniTime);
                    /////////////////////////////////////////////////////
                
                    return false;
                    
                end if;
            end for;
        end for;
    end for;

    /////////////////////////////////////////////////////
	vprintf IsPDSetFlag,1: "Took %o seconds (CPU time)\n", Cputime(iniTime);
    /////////////////////////////////////////////////////

	return true;
	 
end intrinsic;

/****************************************************************/
/*                                                              */  
/* Function name: PermutationDecodeInitialization               */
/* Parameters: C, I, S                                          */
/* Function description: This function initialize variables     */
/*   used in the permutation decoding algorithm.                */
/*   The parameters C, I, S are the same as PermutationDecode() */
/*   See below the description of the intrinsic                 */
/*   PermutationDecode for more details.                        */   
/*                                                              */
/****************************************************************/
PermutationDecodeInitialization := function(C, I, S)
    
    S := Set(S);  // Eliminate repeated monomial matrices in S
    K := BaseField(C); 
    n := Length(C);
    k := Dimension(C);
 	
    // p in Sym(n) moves the information coordinates given by I to the first positions
    newCols := I cat [i : i in [1..n] | i notin I];
    permSeq := [Position(newCols, i) : i in [1..n]];
    p := Sym(n)!permSeq;
    invp := p^(-1);
    
    // Generator matrix with the identity in the first k positions 
    // G := GeneratorMatrix(C)^p; 
    G := GeneratorMatrix(C^p); 
 
    // Parity-check matrix with the identity in the last n-k positions
    H := Transpose(HorizontalJoin(-Transpose(ColumnSubmatrix(G, k+1, n-k)), 
                                             IdentityMatrix(K, n-k)));
    infSpace := VectorSpace(K, k);
    
    // According to the new generator matrix G, where the information positions  
    // are the first ones, define new variables, Sp and Ip, as the permuted  
    // version of S and I, respectively
    Ip := I^p;    // new I should be [1..k] 
    Sp := [PermutationMatrix(K, invp) * M * PermutationMatrix(K, p)  : M in S];
    identityMat := IdentityMatrix(K, n);
  
	return Sp, p, invp, Ip, G, H, infSpace, identityMat;

end function;

/****************************************************************/
/*                                                              */  
/* Function name: PermutationDecodeAlg                          */
/* Parameters: C, S, s, u, p, invp, G, H, infSpace, I,          */
/*   identityMat                                                */ 
/* Function description: This function performs the permutation */
/*   decoding algorithm from the variables initialized in the   */
/*   function PermutationDecodeInitialization.                  */                       
/*   See below the description of the intrinsic                 */
/*   PermutationDecode for more details.                        */  
/*                                                              */
/****************************************************************/
PermutationDecodeAlg := function(C, S, s, u, p, invp, G, H, infSpace, I, identityMat) 

	u := u^p;
	if Weight(u * H) le s then
        uinf := infSpace![u[i] : i in I]; 
        return true, (uinf * G)^invp;

	else 
        // Remove the identity matrix from S (if it is included in S)
        // to not check twice the same condition  
        Exclude(~S, identityMat);
		for M in S do
            newu := u * M;  
			if Weight(newu * H) le s then
                newuinf := infSpace![newu[i] : i in I];
				return true, (newuinf * G * (M^(-1)))^invp;

			end if;
		end for;
	    return false, C!0;

	end if;

end function;

/****************************************************************/
/*                                                              */
/* Function name: PermutationDecode                             */
/* Parameters: C, I, S, s, u                                    */
/* Function description: Given an [n,k] linear code C over a    */
/*   finite field K; an information set I in {1,...,n} for C as */
/*   a sequence of coordinate positions; a sequence S of        */
/*   elements in the group of monomial matrices of order n over */
/*   K such that S is an s-PD-set for C with respect to I; an   */
/*   integer s in {1,...,t}, where t is the error-correcting    */
/*   capability of C;  and a vector u from the ambient space V  */
/*   of C, attempt to decode u with respect to C. If the        */
/*   decoding algorithm succeeds in computing a vector u' in C  */
/*   as the decoded version of u in V, then the function returns*/
/*   true and u'. If the decoding algorithm does not succeed in */
/*   decoding u, then the function returns false and the zero   */
/*   vector in V. The parameter S can also be given as a        */
/*   sequence of elements in the symmetric group Sym(n) of      */
/*   permutations on the set {1,...,n}, when C is binary.       */
/*   Instead of a vector u, we can also decode a sequence Q     */
/*   of vectors from the ambient space V of C                   */
/* Input parameters description:                                */
/*   - C : Linear code over GF(q)                               */
/*   - I : Subset of integers in {1..n} as a sequence           */
/*   - S : Subset of monomial matrices as a sequence            */
/*   - s : Integer in {1..t}, t is the correcting capability    */
/*   - u : Received vector to be decoded                        */
/* Output parameters description:                               */
/*   - Boolean, true if u is decoded and false otherwise        */
/*   - Decoded vector of u, or the zero vector                  */
/*                                                              */
/* case S is a sequence of elements in the monomial group       */
/* Signature: (<CodeLinFld> C, <[RngIntElt]> I,                 */
/*           <[AlgMatElt]> S, <RngIntElt> s, <ModTupFldElt> u)  */       
/*           -> BoolElt, ModTupFldElt                           */
/*                                                              */
/* case S is a sequence of elements in the symmetric group      */
/* and C is a binary linear code                                */                        
/* Signature: (<CodeLinFld> C, <[RngIntElt]> I,                 */
/*           <[GrpPermElt]> S, <RngIntElt> s, <ModTupFldElt> u) */       
/*           -> BoolElt, ModTupFldElt                           */
/*                                                              */
/* case S is a sequence of elements in the monomial group       */
/* and Q a sequence of vectors over K                           */
/* Signature: (<CodeLinFld> C, <[RngIntElt]> I,                 */
/*          <[AlgMatElt]> S, <RngIntElt> s, <[ModTupFldElt]> Q) */       
/*           -> [BoolElt], [ModTupFldElt]                       */
/*                                                              */
/* case S is a sequence of elements in the symmetric group      */
/* C is a binary linear code                                    */
/* and Q a sequence of vectors over K                           */ 
/* Signature: (<CodeLinFld> C, <[RngIntElt]> I,                 */
/*          <[GrpPermElt]> S, <RngIntElt> s, <[ModTupFldElt]> Q)*/       
/*           -> [BoolElt], [ModTupFldElt]                       */
/*                                                              */
/****************************************************************/
intrinsic PermutationDecode(C::CodeLinFld, I::[RngIntElt], S::[AlgMatElt], 
          s::RngIntElt, u::ModTupFldElt) -> BoolElt, ModTupFldElt
{
Given an [n,k] linear code C over a finite field K; an information set I in 
[1,...,n] for C as a sequence of coordinate positions; a sequence S of elements 
in the group of monomial matrices of order n over K such that S is an s-PD-set 
for C with respect to I; an integer s in [1,...,t], where t is the error-correcting 
capability of C;  and a vector u from the ambient space V of C, attempt to decode 
u with respect to C. If the decoding algorithm succeeds in computing a vector u' 
in C as the decoded version of u in V, then the function returns true and u'. 
If the decoding algorithm does not succeed in decoding u, then the function returns 
false and the zero vector in V. 

The permutation decoding algorithm consists of moving all errors in a received 
vector u=c+e, where c in C and e in V is the error vector with at most t errors, 
out of the information positions, that is, moving the nonzero coordinates of e 
out of the information set I for C, by using an automorphism of C.

Note that the function does not check neither that I is an information set for C,
nor S is an s-PD-set for C with respect to I, nor s <= t.
}
    require not(zero_Code(C)): "Code cannot be the zero code";
    n := Length(C);
    requirerange s, 1, n;
    require (#I ge 1): "Argument 2 cannot be an empty sequence";
    require (Min(I) ge 1) and (Max(I) le n): 
                                    "Argument 2 should be a subset of", [1..n]; 
                                                                         
    require not IsEmpty(S): "Argument 3 cannot be an empty sequence";
    K := BaseField(C);   
    require BaseRing(S[1]) eq K: 
          "Arguments 1 and 3 should be over the same finite field";
    require (Degree(Parent(S[1])) eq n): 
          "Argument 3 should contain monomial matrices of size", n;
                                                                    
    require (BaseRing(u) eq K): 
          "Argument 4 must be a vector from the ambient space of the code";
    require (Degree(u) eq n): "Argument 4 must be of length", n;	
    
	Sp, p, invp, Ip, G, H, infSpace, identityMat := 
                                       PermutationDecodeInitialization(C, I, S);

    return PermutationDecodeAlg(C, Sp, s, u, p, invp, G, H, infSpace, Ip, identityMat);

end intrinsic;

/****************************************************************/
intrinsic PermutationDecode(C::CodeLinFld, I::[RngIntElt], S::[GrpPermElt], 
          s::RngIntElt, u::ModTupFldElt) -> BoolElt, ModTupFldElt
{
Given an [n,k] linear code C over a finite field GF(2); an information set I in 
[1,...,n] for C as a sequence of coordinate positions; a sequence S of elements 
in the symmetric group Sym(n) of permutations on the set [1,...,n] such that S is 
an s-PD-set for C with respect to I; an integer s in [1,...,t], where t is the 
error-correcting capability of C;  and a vector u from the ambient space V of C, 
attempt to decode u with respect to C. If the decoding algorithm succeeds in 
computing a vector u' in C as the decoded version of u in V, then the function 
returns true and u'. If the decoding algorithm does not succeed in decoding u, 
then the function returns false and the zero vector in V. 

The permutation decoding algorithm consists of moving all errors in a received 
vector u=c+e, where c in C and e in V is the error vector with at most t errors, 
out of the information positions, that is, moving the nonzero coordinates of e 
out of the information set I for C, by using an automorphism of C.

Note that the function does not check neither that I is an information set for C,
nor S is an s-PD-set for C with respect to I, nor s <= t.
}
    require not(zero_Code(C)): "Code cannot be the zero code";
    require #BaseField(C) eq 2: "Code must be over a finite field of size 2";
    n := Length(C);
    requirerange s, 1, n;
    require (#I ge 1): "Argument 2 cannot be an empty sequence";
    require (Min(I) ge 1) and (Max(I) le n): 
                                    "Argument 2 should be a subset of", [1..n]; 
                                                                         
    require not IsEmpty(S): "Argument 3 cannot be an empty sequence";
    require (Degree(Parent(S[1])) eq n): 
          "Argument 3 should contain permutations acting on a set of cardinality", n;
 	K := GF(2);                                                                             
    require (BaseRing(u) eq K): 
          "Argument 4 must be a vector from the ambient space of the code";
    require (Degree(u) eq n): "Argument 4 must be of length", n;	
     
    S := [MonomialMatrix([K!1^^n], p) : p in S]; 
	Sp, p, invp, Ip, G, H, infSpace, identityMat := 
                                       PermutationDecodeInitialization(C, I, S);

    return PermutationDecodeAlg(C, Sp, s, u, p, invp, G, H, infSpace, Ip, identityMat);

end intrinsic;

/****************************************************************/
intrinsic PermutationDecode(C::CodeLinFld, I::[RngIntElt], S::[AlgMatElt], 
          s::RngIntElt, Q::[ModTupFldElt]) -> SeqEnum[BoolElt], SeqEnum[ModTupFldElt]
{
Given an [n,k] linear code C over a finite field K; an information set I in [1,...,n] 
for C as a sequence of coordinate positions; a sequence S of elements in the group
of monomial matrices of order n over K such that S is an s-PD-set for C with 
respect to I; an integer s in [1,...,t], where t is the error-correcting 
capability of C; and a sequence Q of vectors from the ambient space V of C, 
attempt to decode the vectors of Q with respect to C.

This function is similar to the function PermutationDecode(C, I, S, s, u) except 
that rather than decoding a single vector, it decodes a sequence of vectors and 
returns a sequence of booleans and a sequence of decoded vectors corresponding 
to the given sequence. The algorithm used is as for the function 
PermutationDecode(C, I, S, s, u).
}
    require not(zero_Code(C)): "Code cannot be the zero code";
    n := Length(C);
    requirerange s, 1, n;
    require (#I ge 1): "Argument 2 cannot be an empty sequence";
    require (Min(I) ge 1) and (Max(I) le n): 
                                    "Argument 2 should be a subset of", [1..n]; 
                                                                         
    require not IsEmpty(S): "Argument 3 cannot be an empty sequence";    
    K := BaseField(C);   
    require BaseRing(S[1]) eq K: 
          "Arguments 1 and 3 should be over the same finite field";
    require (Degree(Parent(S[1])) eq n): 
          "Argument 3 should contain monomial matrices of size", n;
      
    require not IsEmpty(Q): "Argument 4 cannot be an empty sequence";   
    require (BaseRing(Q[1]) eq K): 
          "Argument 4 must contain vectors from the ambient space of the code";
    require (Degree(Q[1]) eq n): "Argument 4 must contain vectors of length", n;
         
    Sp, p, invp, Ip, G, H, infSpace, identityMat := 
                                        PermutationDecodeInitialization(C, I, S);
    isDecodedSeq := [];
    uDecodedSeq := []; 
    for u in Q do
        isDecoded, uDecoded := PermutationDecodeAlg(C, Sp, s, u, p, invp, G, H, 
                                                      infSpace, Ip, identityMat);
        Append(~isDecodedSeq, isDecoded); 
        Append(~uDecodedSeq, uDecoded); 
    end for;
    
    return isDecodedSeq, uDecodedSeq;
 
end intrinsic;

/****************************************************************/
intrinsic PermutationDecode(C::CodeLinFld, I::[RngIntElt], S::[GrpPermElt], 
          s::RngIntElt, Q::[ModTupFldElt]) -> SeqEnum[BoolElt], SeqEnum[ModTupFldElt]
{
Given an [n,k] linear code C over a finite field GF(2); an information set I in [1,...,n] 
for C as a sequence of coordinate positions; a sequence S of elements in the 
symmetric group Sym(n) of permutations on the set [1,...,n] such that S is an 
s-PD-set for C with respect to I; an integer s in [1,...,t], where t is the 
error-correcting capability of C; and a sequence Q of vectors from the ambient 
space V of C, attempt to decode the vectors of Q with respect to C. 

This function is similar to the function PermutationDecode(C, I, S, s, u) except 
that rather than decoding a single vector, it decodes a sequence of vectors and 
returns a sequence of booleans and a sequence of decoded vectors corresponding 
to the given sequence. The algorithm used is as for the function 
PermutationDecode(C, I, S, s, u).
}
    require not(zero_Code(C)): "Code cannot be the zero code";
    require #BaseField(C) eq 2: "Code must be over a finite field of size 2";
    n := Length(C);
    requirerange s, 1, n;
    require (#I ge 1): "Argument 2 cannot be an empty sequence";
    require (Min(I) ge 1) and (Max(I) le n): 
                                    "Argument 2 should be a subset of", [1..n]; 
                                                                         
    require not IsEmpty(S): "Argument 3 cannot be an empty sequence";    
    require (Degree(Parent(S[1])) eq n): 
          "Argument 3 should contain permutations acting on a set of cardinality", n;
      
    require not IsEmpty(Q): "Argument 4 cannot be an empty sequence";  
	K := GF(2);                                                              
    require (BaseRing(Q[1]) eq K): 
          "Argument 4 must contain vectors from the ambient space of the code";
    require (Degree(Q[1]) eq n): "Argument 4 must contain vectors of length", n;    
     
    isDecodedSeq := [];
    uDecodedSeq := [];
    S := [MonomialMatrix([K!1^^n], p) : p in S]; 
	Sp, p, invp, Ip, G, H, infSpace, identityMat := 
                                       PermutationDecodeInitialization(C, I, S);
    for u in Q do
        isDecoded, uDecoded := PermutationDecodeAlg(C, Sp, s, u, p, invp, G, H, 
                                                     infSpace, Ip, identityMat);
        Append(~isDecodedSeq, isDecoded); 
        Append(~uDecodedSeq, uDecoded); 
    end for;
    
    return isDecodedSeq, uDecodedSeq;
 
end intrinsic;
 
/****************************************************************/
/*                                                              */  
/* Function name: MatrixToPerm                                  */
/* Parameters: M, transposeG, columnsG                          */
/* Function description: Given a matrix M, the transpose of the */
/*   generator matrix G of the [n,k] simplex code over K, and a */
/*   sequence with the colums of G as rows, return the monomial */
/*   matrix of size k over K associated to M along with the     */
/*   permutation in Sym(n) corresponding to matrix M having all */
/*   nonzero entries equal to 1.                                */
/*                                                              */
/****************************************************************/
MatrixToPerm := function(M, transposeG, columnsG)
    n := #columnsG;
    m := NumberOfRows(M);
    permGcol := transposeG*M;
    columnGNzed := [Normalize(u) : u in columnsG];
   
    K := BaseRing(M);
    V := VectorSpace(K, m);
    permPositions := [];
    permEltGF := [];
    for i in [1..n] do
        v := permGcol[i];
        vNzed := Normalize(v);
        position := Position(columnGNzed, vNzed);
        if position gt 0  then
            Append(~permPositions, position);
            w := columnsG[position];
            lambda := w[Depth(w)] / v[Depth(v)]; 
            Append(~permEltGF, lambda);               
        end if;       
    end for;
    
    perm := Sym(n)!permPositions;
    return MonomialMatrix(permEltGF, perm), perm;
end function;

/****************************************************************/
/*                                                              */  
/* Function name: InformationSetSimplexCode                     */
/* Parameters: columnsG                                         */
/* Function description: Given a sequence with the columns of a */
/*   generator matrix of the simplex code over a finite field,  */
/*   return the information set I for the simplex code          */
/*   corresponding to positions where the basis vector are.     */
/*                                                              */
/****************************************************************/
InformationSetSimplexCode := function(columnsG)
    B := Basis(VectorSpace(BaseRing(columnsG[1]), Degree(columnsG[1])));
    return [Position(columnsG, v) : v in B];
end function;

/****************************************************************/
/*                                                              */
/* Function name: PDSetSimplexCode                              */
/* Parameters: K, m                                             */
/* Function description: Given a finite field K of cardinality  */
/*   q, and a positive integer m, the [n=(q^m-1)/(q-1), m,      */
/*   q^{m-1}] linear simplex code C over K, given by the        */
/*   function Dual(HammingCode(K, m)), is considered. The       */
/*   function returns an information set I for C together with  */
/*   a subset S of the monomial automorphism group of C such    */
/*   that S is an s-PD-set for C with respect to I, where       */
/*   s=[(q^(m)-1)/(m(q-1))]-1 and [x] is the integer part of x. */
/* Input parameters description:                                */
/*   - K : Finite field                                         */
/*   - m : Positive integer                                     */
/* Output parameters description:                               */
/*   - Information set from {1..n} as a sequence                */  
/*   - s-PD-set for the simplex code of length n over K, as a   */
/*     sequence of monomial matrices of size n over K           */
/*   - Sequence with the corresponding permutations associated  */
/*     to the given s-PD-set, when K=GF(2)                      */
/*                                                              */
/* Signature: (<FldFin> K, <RngIntElt> m) -> SeqEnum[RngIntElt],*/
/*                       SeqEnum[AlgMatElt], SeqEnum[GrpPermElt]*/
/*                                                              */
/* Remark: The set of s+1 matrices must satisfy the condition   */
/*         given in the paper "Partial permutation decoding for */
/*         simplex codes" by W. Fish, J. Key and E. Mwambene    */
/*         in Advances in Mathematics of Communications, vol. 6,*/
/*         no. 4, pp. 505-516, 2012.                            */
/****************************************************************/
intrinsic PDSetSimplexCode(K::FldFin, m::RngIntElt) -> 
                    SeqEnum[RngIntElt], SeqEnum[AlgMatElt], SeqEnum[GrpPermElt]
{
Given a finite field K of cardinality q, and a positive integer m, the 
[n=(q^m-1)/(q-1), m, q^(m-1)] linear simplex code C over K, given by the function 
Dual(HammingCode(K, m)), is considered. The function returns an information set 
I for C together with a subset S of the monomial automorphism group of C such 
that S is an s-PD-set for C with respect to I, where s=[(q^(m)-1)/(m(q-1))]-1
and [x] is the integer part of x.

The information set I is returned as a sequence of m integers, giving the 
coordinate positions that correspond to the information set for C. The set S is 
also returned as a sequence, which contains the s+1 elements in the group of 
monomial matrices of order n over K. When K is of size two, the function also 
returns the elements of S represented as elements in the symmetric group Sym(n) 
of permutations on the set [1,...,n].
}	
    q := #K;
    n := (q^m-1)/(q-1);   	    
    requirege m, 1;
    
    Kext := ext<K | m>;
    z := PrimitiveElement(Kext);
    
    B := [z^i : i in [0..m-1]];
    B0 := Matrix(K, [Eltseq(x, K) : x in B]);
    PDSetMatrices := [ B0 ];
    PDSetMatricesInv := [ B0 ];

    s := Floor(n/m)-1;  
    for i in [1..s] do
        // Construct matrix Bi
        Bi := Matrix(K, [Eltseq(x*(z^(m*i)), K) : x in B]);
        // Normalize the rows of the matrix Bi
        for j in [1..m] do
            Bi[j] := Normalize(Bi[j]);
        end for;
        Append(~PDSetMatrices, Bi);
        Append(~PDSetMatricesInv, Bi^(-1));
    end for;
    
    // Construction of the corresponding permutations in Sym(n)
    G := GeneratorMatrix(Dual(HammingCode(K, m)));
    transposeG := Transpose(G);
    columnsG := [transposeG[i] : i in [1..n]];
    
    PDSetPerms := [];
    PDSetMonomialMatrices := [];
    for M in PDSetMatricesInv do
        monomialM, perm := MatrixToPerm(M, transposeG, columnsG); 
        Append(~PDSetPerms, perm);
        Append(~PDSetMonomialMatrices, monomialM);
    end for;

    if q eq 2 then 
        return InformationSetSimplexCode(columnsG), PDSetMonomialMatrices, PDSetPerms;
    else
        return InformationSetSimplexCode(columnsG), PDSetMonomialMatrices, _;
    end if;

end intrinsic;

/****************************************************************/
/*                                                              */
/* Function name: PDSetHadamardCode                             */
/* Parameters: m                                                */
/* Function description: Given a positive integer m, the [2^m,  */
/*   m+1, 2^{m-1}] binary linear Hadamard code C, given by the  */
/*   function Dual(ExtendCode(HammingCode(GF(2), m))), is       */
/*   considered. The function returns an information set I in   */
/*   {1,..., 2^m} for C together with a subset S of the         */
/*   permutation automorphism group of C such that S is an      */
/*   s-PD-set for C with respect to I, where s=[2^(m)/(m+1)]    */
/*   and [x] is the integer part of x.                          */
/* Input parameters description:                                */
/*   - m : Positive integer                                     */
/* Output parameters description:                               */
/*   - Information set from {1..2^m} as a sequence              */  
/*   - s-PD-set for the Hadamard code of length n over K, as a  */
/*     sequence of permutation matrices of size n over K        */
/*   - Sequence with the corresponding permutations associated  */
/*     to the given s-PD-set                                    */
/*                                                              */
/* Signature: (<RngIntElt> m) -> SeqEnum[RngIntElt],            */
/*                   SeqEnum[AlgMatElt], SeqEnum[GrpPermElt]    */
/*                                                              */
/* Remark: The set of s+1 matrices must satisfy the condition   */
/*         given in the paper "Partial permutation decoding for */
/*         binary linear and Z4-linear Hadamard codes" by R.    */
/*         Barrolleta and M. Villanueva, submitted to Designs,  */
/*         Codes and Cryptography, 2016. arXiv:1512.01839       */
/****************************************************************/
intrinsic PDSetHadamardCode(m::RngIntElt) -> 
                    SeqEnum[RngIntElt], SeqEnum[AlgMatElt], SeqEnum[GrpPermElt]
{
Given a positive integer m, the [2^m, m+1, 2^(m-1)] binary linear Hadamard code C,
given by the function Dual(ExtendCode(HammingCode(GF(2), m))), is considered.
The function returns an information set I in [1,..., 2^m] for C together with a 
subset S of the permutation automorphism group of C such that S is an s-PD-set 
for C with respect to I, where s=[2^(m)/(m+1)] and [x] is the integer part of x.

The information set I is returned as a sequence of m+1 integers, giving the coordinate 
positions that correspond to the information set for C. The set S is also returned 
as a sequence, which contains the s+1 elements in the group of permutation matrices 
of order 2^m over GF(2). The function also returns the elements of S represented 
as elements in the symmetric group Sym(2^m) of permutations on the set [1,...,2^m].
} 
    requirege m, 1;
    
    K := GF(2);
    Kext := ext<K | m>;
    z := PrimitiveElement(Kext);
    
    B := [z^i : i in [0..m-1]];
    L := [z^i - z^0: i in [1..m]];

    zerocolumn := Matrix(K, m+1, 1, [0^i : i in [1..m+1]]);
    row := Matrix(K, 1, m, [0^i : i in [1..m]]);
    B0 := Matrix(K, [Eltseq(x, K) : x in B]);
    B0 := HorizontalJoin(zerocolumn, VerticalJoin(row, B0));
    B0[1][1] := 1;

    PDSetMatricesInv := [ B0 ];
    PDSetMatrices := [ B0 ];

    s := Floor(2^m/(m+1))-1;
    for i in [1..s] do
        Bi := Matrix(K, [Eltseq(x*(z^((m+1)*i-1)), K) : x in L]);
        row := Matrix(K, [Eltseq(z^((m+1)*i-1), K)]);
        Bi := HorizontalJoin(zerocolumn, VerticalJoin(row, Bi));
        Bi[1][1] := 1;
        Append(~PDSetMatricesInv, Bi);
        Append(~PDSetMatrices, Bi^(-1));
    end for;

    // Construction of the corresponding permutations in Sym(n)
    GS := GeneratorMatrix(SimplexCode(m));
    n := 2^m;
    onerow := Matrix(GF(2), 1, n-1, [1^^n-1]);
    G := HorizontalJoin(VerticalJoin(onerow, GS), zerocolumn);
    G[1, n] := 1;
    
    transposeG := Transpose(G);
    columnsG := [transposeG[i] : i in [1..2^m]];

    PDSetPerms := [];
    PDSetMonomialMatrices := [];    
    for M in PDSetMatrices do
        monomialM, perm := MatrixToPerm(M, transposeG, columnsG); 
        Append(~PDSetPerms, perm);
        Append(~PDSetMonomialMatrices, monomialM);
    end for;

    return [1..m] cat [n], PDSetMonomialMatrices, PDSetPerms;

end intrinsic;


