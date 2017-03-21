/************************************************************/
/*                                                          */
/* Project name: Codes over Fq in MAGMA                     */
/* Test file name: testPermDecodeOverFq.m                   */
/*                                                          */
/* Comments: Black-box tests for the functions              */
/*           IsPermutationDecodeSet, PermutationDecode,     */
/*           PDSetSimplexCode and PDSetHadamardCode         */
/*           included in the PermDecodeOverFq.m file        */
/*                                                          */
/* Authors: R. D. Barrolleta, J. Pujol and M. Villanueva    */
/*                                                          */
/* Revision version and last date: v1.0, 2015/11/29         */
/*                                 v1.1, 2015/12/24         */ 
/*                                 v1.2, 2016/02/29         */
/*                                 v1.3, 2016/04/30         */
/*                                 v1.4, 2016/05/11         */
/*                                                          */
/************************************************************/

SetAssertions(true);

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
print "test 1: Simplex code of length 15 over GF(2), #C = 16";

m := 4;
C := SimplexCode(m);
n := Length(C);
V := VectorSpace(BaseField(C), n);
s := Floor(n/m)-1;

// u in C
u := V![0,1,1,0,1,0,1,1,1,1,0,0,0,1,0]; 
// v not in C, 2 errors in positions {1, 4} 
v := V![1,1,1,1,1,0,1,1,1,1,0,0,0,1,0]; 
// w not in C, 4 errors in positions {1, 2, 4, 12} 
w := V![1,0,1,1,1,0,1,1,1,1,0,1,0,1,0];  
Q := [u, v, w];

// Test PDSetSimplexCode function
I, SMAut, SPAut := PDSetSimplexCode(GF(2), m);

// Test IsPermutationDecodeSet function
OutputIsPDSet := IsPermutationDecodeSet(C, I, SPAut, s);
assert OutputIsPDSet eq true;
OutputIsPDSet := IsPermutationDecodeSet(C, I, SMAut, s);
assert OutputIsPDSet eq true;
OutputIsPDSet := IsPermutationDecodeSet(C, I, SPAut, s+1);
assert OutputIsPDSet eq false;
OutputIsPDSet := IsPermutationDecodeSet(C, I, SMAut, s+1);
assert OutputIsPDSet eq false;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u := PermutationDecode(C, I, SPAut, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;

OutputIsDecoded_u, OutputDecoded_u := PermutationDecode(C, I, SMAut, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;

OutputIsDecoded_v, OutputDecoded_v := PermutationDecode(C, I, SPAut, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;

OutputIsDecoded_v, OutputDecoded_v := PermutationDecode(C, I, SMAut, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;

OutputIsDecoded_w, OutputDecoded_w := PermutationDecode(C, I, SPAut, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq V!0;

OutputIsDecoded_w, OutputDecoded_w := PermutationDecode(C, I, SMAut, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq V!0;

OutputIsDecoded_Q, OutputDecoded_Q := PermutationDecode(C, I, SPAut, s, Q);
assert OutputIsDecoded_Q eq [true, true, false];
assert OutputDecoded_Q eq [u, u, V!0];

OutputIsDecoded_Q, OutputDecoded_Q := PermutationDecode(C, I, SMAut, s, Q);
assert OutputIsDecoded_Q eq [true, true, false];
assert OutputDecoded_Q eq [u, u, V!0];

/****************************************************************/
print "test 2: Simplex code of length 31 over GF(2), #C = 32";

m := 5;
C := SimplexCode(m);
n := Length(C);
V := VectorSpace(BaseField(C), n);
s := Floor(n/m)-1;

// u in C
u := V![1,0,0,0,0,1,0,0,1,0,1,1,0,0,1,1,1,1,1,0,0,0,1,1,0,1,1,1,0,1,0]; 
// v not in C, 5 errors in positions {1, 2, 3, 4, 10} 
v := V![0,1,1,1,0,1,0,0,1,1,1,1,0,0,1,1,1,1,1,0,0,0,1,1,0,1,1,1,0,1,0]; 
// w not in C, 6 errors in positions {1, 2, 3, 4, 10, 12} 
w := V![0,1,1,1,0,1,0,0,1,1,1,0,0,0,1,1,1,1,1,0,0,0,1,1,0,1,1,1,0,1,0]; 
Q := [u, v, w];

// Test PDSetSimplexCode function
I, SMAut, SPAut := PDSetSimplexCode(GF(2), m);

// Test IsPermutationDecodeSet function
OutputIsPDSet := IsPermutationDecodeSet(C, I, SPAut, s);
assert OutputIsPDSet eq true;
OutputIsPDSet := IsPermutationDecodeSet(C, I, SMAut, s);
assert OutputIsPDSet eq true;
OutputIsPDSet := IsPermutationDecodeSet(C, I, SPAut, s+1);
assert OutputIsPDSet eq false;
OutputIsPDSet := IsPermutationDecodeSet(C, I, SMAut, s+1);
assert OutputIsPDSet eq false;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u := PermutationDecode(C, I, SPAut, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;

OutputIsDecoded_u, OutputDecoded_u := PermutationDecode(C, I, SMAut, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;

OutputIsDecoded_v, OutputDecoded_v := PermutationDecode(C, I, SPAut, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;

OutputIsDecoded_v, OutputDecoded_v := PermutationDecode(C, I, SMAut, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;

OutputIsDecoded_w, OutputDecoded_w := PermutationDecode(C, I, SPAut, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq V!0;

OutputIsDecoded_w, OutputDecoded_w := PermutationDecode(C, I, SMAut, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq V!0;

OutputIsDecoded_Q, OutputDecoded_Q := PermutationDecode(C, I, SPAut, s, Q);
assert OutputIsDecoded_Q eq [true, true, false];
assert OutputDecoded_Q eq [u, u, V!0];

OutputIsDecoded_Q, OutputDecoded_Q := PermutationDecode(C, I, SMAut, s, Q);
assert OutputIsDecoded_Q eq [true, true, false];
assert OutputDecoded_Q eq [u, u, V!0];

/****************************************************************/
print "test 3: Simplex code of length 40 over GF(3), #C = 3^4=81";

m := 4;
C := Dual(HammingCode(GF(3), m));
n := Length(C);
V := VectorSpace(BaseField(C), n);
s := Floor(n/m)-1;

// u in C
u := V![0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]; 
// v not in C, 9 errors in positions {1, 2, 3, 4, 5, 6, 7, 8, 9} 
v := V![2,2,2,1,1,1,2,2,2,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]; 
// w not in C, 10 errors in positions {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} 
w := V![2,2,2,1,1,1,2,2,2,1,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]; 
Q := [u, v, w];

// Test PDSetSimplexCode function
I, SMAut, SPAut := PDSetSimplexCode(GF(3), m);

// Test IsPermutationDecodeSet function
//OutputIsPDSet := IsPermutationDecodeSet(C, I, SMAut, s);
//assert OutputIsPDSet eq true;
//OutputIsPDSet := IsPermutationDecodeSet(C, I, SMAut, s+1);
//assert OutputIsPDSet eq false;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u := PermutationDecode(C, I, SMAut, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;

OutputIsDecoded_v, OutputDecoded_v := PermutationDecode(C, I, SMAut, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;

OutputIsDecoded_w, OutputDecoded_w := PermutationDecode(C, I, SMAut, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq V!0;

OutputIsDecoded_Q, OutputDecoded_Q := PermutationDecode(C, I, SMAut, s, Q);
assert OutputIsDecoded_Q eq [true, true, false];
assert OutputDecoded_Q eq [u, u, V!0];

/****************************************************************/
print "test 4: Simplex code of length 21 over GF(4), #C = 4^3=64";

m := 3;
K<a> := GF(4);
C := Dual(HammingCode(K, m));
n := Length(C);
V := VectorSpace(BaseField(C), n);
s := Floor(n/m)-1;

// u in C
u := V![0,0,0,  0,  0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]; 
// v not in C, 6 errors in positions {1, 2, 3, 4, 5, 6} 
v := V![a,a,a^2,a^2,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]; 
// w not in C, 7 errors in positions {1, 2, 3, 4, 5, 6, 7} 
w := V![a,a,a^2,a^2,1,0,a,1,1,1,1,1,1,1,1,1,1,1,1,1,1]; 
Q := [u, v, w];

// Test PDSetSimplexCode function
I, SMAut, SPAut := PDSetSimplexCode(K, m);

// Test IsPermutationDecodeSet function
OutputIsPDSet := IsPermutationDecodeSet(C, I, SMAut, s);
assert OutputIsPDSet eq true;
OutputIsPDSet := IsPermutationDecodeSet(C, I, SMAut, s+1);
assert OutputIsPDSet eq false;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u := PermutationDecode(C, I, SMAut, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;

OutputIsDecoded_v, OutputDecoded_v := PermutationDecode(C, I, SMAut, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;

OutputIsDecoded_w, OutputDecoded_w := PermutationDecode(C, I, SMAut, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq V!0;

OutputIsDecoded_Q, OutputDecoded_Q := PermutationDecode(C, I, SMAut, s, Q);
assert OutputIsDecoded_Q eq [true, true, false];
assert OutputDecoded_Q eq [u, u, V!0];

/****************************************************************/
print "test 5: Hadamard code of length 16 over GF(2), #C = 32";

m := 4;
C := Dual(ExtendCode(HammingCode(GF(2), m)));
n := Length(C);
V := VectorSpace(BaseField(C), n);
s := Floor(n/(m+1))-1;

// u in C
u := V![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]; 
// v not in C, 2 errors in positions {1, 2} 
v := V![0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1]; 
// w not in C, 4 errors in positions {1, 2, 14, 15} 
w := V![0,0,1,1,1,1,1,1,1,1,1,1,1,1,0,0]; 
Q := [u, v, w];

// Test PDSetHadamardCode function
I, SMAut, SPAut := PDSetHadamardCode(m);

// Test IsPermutationDecodeSet function
OutputIsPDSet := IsPermutationDecodeSet(C, I, SMAut, s);
assert OutputIsPDSet eq true;
OutputIsPDSet := IsPermutationDecodeSet(C, I, SMAut, s+1);
assert OutputIsPDSet eq false;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u := PermutationDecode(C, I, SMAut, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;

OutputIsDecoded_v, OutputDecoded_v := PermutationDecode(C, I, SMAut, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;

OutputIsDecoded_w, OutputDecoded_w := PermutationDecode(C, I, SMAut, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq V!0;

OutputIsDecoded_Q, OutputDecoded_Q := PermutationDecode(C, I, SMAut, s, Q);
assert OutputIsDecoded_Q eq [true, true, false];
assert OutputDecoded_Q eq [u, u, V!0];

/****************************************************************/
print "test 6: Hadamard code of length 32 over GF(2), #C = 64";

m := 5;
C := Dual(ExtendCode(HammingCode(GF(2), m)));
n := Length(C);
V := VectorSpace(BaseField(C), n);
s := Floor(n/(m+1))-1;

// u in C
u := V![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]; 
// v not in C, 4 errors in positions {1, 2, 3, 4} 
v := V![0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]; 
// w not in C, 7 errors in positions {1, 2, 3, 4, 5, 6, 7} 
w := V![0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]; 
Q := [u, v, w];

// Test PDSetHadamardCode function
I, SMAut, SPAut := PDSetHadamardCode(m);

// Test IsPermutationDecodeSet function
OutputIsPDSet := IsPermutationDecodeSet(C, I, SMAut, s);
assert OutputIsPDSet eq true;
OutputIsPDSet := IsPermutationDecodeSet(C, I, SMAut, s+1);
assert OutputIsPDSet eq false;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u := PermutationDecode(C, I, SMAut, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;

OutputIsDecoded_v, OutputDecoded_v := PermutationDecode(C, I, SMAut, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;

OutputIsDecoded_w, OutputDecoded_w := PermutationDecode(C, I, SMAut, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq V!0;

OutputIsDecoded_Q, OutputDecoded_Q := PermutationDecode(C, I, SMAut, s, Q);
assert OutputIsDecoded_Q eq [true, true, false];
assert OutputDecoded_Q eq [u, u, V!0];
