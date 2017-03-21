/************************************************************/
/*                                                          */
/* Project name: Codes over Z4 in MAGMA                     */
/* Test file name: testDecodeOverZ4_part2.m                 */
/*                                                          */
/* Comments: Black-box tests for the functions              */
/*           InformationSet, IsInformationSet,              */
/*           IsPermutationDecodeSet, PermutationDecode      */
/*           and PDSetHadamardCodeZ4                        */
/*           included in the DecodeOverZ4.m file            */
/*                                                          */
/* Authors: R. D. Barrolleta, J. Pujol and M. Villanueva    */
/*                                                          */
/* Revision version and last date: 1.0, 2015/11/29          */
/*                                 1.1, 2015/12/18          */ 
/*                                 1.2, 2016/05/11          */
/*                                                          */
/************************************************************/

SetAssertions(true);
Alarm(30*60);

/****************************************************************/
/*                                                              */  
/* Function name: PermZ4ToPermZ2                                */
/* Parameters: permZ4                                           */
/* Function description: Given permutation permZ4 from Sym(n),  */
/*   return the pemutatation in Sym(2n) such that               */
/*   i -> 2*permZ4(i/2)  if i is even,                          */
/*   i -> 2*permZ4((i+1)/2)-1  if i is odd.                     */
/*                                                              */
/****************************************************************/
PermZ4ToPermZ2 := function(permZ4)	
    n := Degree(Parent(permZ4));	
    permList := &cat[ [2*(i^permZ4)-1, 2*(i^permZ4)] : i in [1..n]];
    return Sym(2*n)!permList;	
end function;

/****************************************************************/
/*                                                              */
/* Function name: InformationSet                                */
/* Parameters: C                                                */
/* Function description: Given a code C over Z4 of length n and */
/*   type 2^gamma 4^delta, return an information set            */
/*   I=[i_1,...,i_(gamma+delta)] in [1,...,n] for C such that   */
/*   the code C punctured on [1,...,n] minus [i_(gamma+1),...,  */
/*   i_(gamma+delta)] is of type 4^delta, and the corresponding */
/*   information set Phi(I)=[2i_1-1, ..., 2i_gamma-1,           */
/*   2i_(gamma+1)-1, 2i_(gamma+1),..., 2i_(gamma+delta)-1,      */
/*   2i_(gamma+delta)] in [1,...,2n] for the binary code        */
/*   Cbin=Phi(C), where Phi is the Gray map. The information    */
/*   sets I and Phi(I) are returned as a sequence of gamma+delta*/
/*   and gamma+2delta integers, giving the coordinate           */
/*   positions that correspond to the information set of C and  */
/*   Cbin, respectively.                                        */
/* Input parameters description:                                */
/*   - C : Code over Z4                                         */
/* Output parameters description:                               */
/*   - Sequence I with gamma+delta integers                     */
/*   - Sequence Ibin with gamma+2*delta integers                */
/*                                                              */
/* Signature: (<CodeLinRng> C) -> SeqEnum[RngIntElt],           */
/*                                SeqEnum[RngIntElt]            */
/*                                                              */
/****************************************************************/
/****************************************************************/
/*                                                              */
/* Function name: IsInformationSet                              */
/* Parameters: C, I                                             */
/* Function description: Given a code C over Z4 of length n and */
/*   type 2^gamma 4^delta and a sequence I in [1,...,n] or I in */
/*   [1,...,2n], return true if and only if I in [1,...,n] is an*/ 
/*   information set for C. This function also returns another  */
/*   boolean, which is true if an only if I in [1,...,2n] is an */
/*   information set for the corresponding binary code          */
/*   Cbin=Phi(C), where Phi is the Gray map.                    */
/* Input parameters description:                                */
/*   - C : Code over Z4                                         */
/*   - I : Sequence of integers in [1..n] or [1..2n]            */
/* Output parameters description:                               */
/*   - Boolean, true if I is an information set for C           */
/*   - Boolean, true if I is an information set for Cbin        */
/*                                                              */
/* Signature: (<CodeLinRng> C, <[RngIntElt]> I) ->              */
/*                                      BoolElt, BoolElt        */
/*                                                              */
/****************************************************************/
/****************************************************************/
/*                                                              */
/* Function name: IsPermutationDecodeSet                        */
/* Parameters: C, I, S, s                                       */
/* Function description: Given a code C over Z4 of length n and */
/*   type 2^gamma 4^delta, a sequence I in {1,...,2n},          */
/*   a sequence S of elements in the symmetric group Sym(2n) of */ 
/*   permutations on the set {1,...,2n}, and an integer s>1,    */
/*   return true if and only if S is an s-PD-set for            */
/*   Cbin=Phi(C), where Phi is the Gray map, with respect to    */
/*   the information set I.                                     */ 
/*   The parameters I and S can also be given as a sequence I   */
/*   in {1,...,n} and a sequence S of elements in the symmetric */
/*   group Sym(n) of permutations on the set {1,...,n},         */
/*   respectively. In this case, the function returns true      */
/*   if and only if Phi(S) is an s-PD-set for Cbin=Phi(C) with  */
/*   respect to the information set Phi(I), where Phi(I) and    */
/*   Phi(S) are the sequences defined as in the manual.         */
/* Input parameters description:                                */
/*   - C : Code over Z4                                         */
/*   - I : Subset of integers in {1..2n} or {1..n} as a sequence*/
/*   - S : Subset of permutations acting on {1..n} or {1..2n},  */
/*         respectively, as a sequence                          */    
/*   - s : Integer in {1..t}, t is the correcting capability    */
/* Output parameters description:                               */
/*   - Boolean, true if S is an s-PD-set and false otherwise    */
/*                                                              */
/* Signature: (<CodeLinRng> C, <[RngIntElt]> I,                 */
/*              <[GrpPermElt]> S, <RngIntElt> s) -> BoolElt     */
/*                                                              */
/****************************************************************/
/****************************************************************/
/*                                                              */
/* Function name: PermutationDecode                             */
/* Parameters: C, I, S, s, u                                    */
/* Function description: Given a code C over Z4 of length n and */
/*   type 2^gamma 4^delta; an information set I=[i_1,...,       */
/*   i_(gamma+delta)] in [1,...,n] for C as a sequence of       */
/*   coordinate positions, such that the code C punctured on    */
/*   [1,...,n] minus [i_(gamma+1),...,i_(gamma+delta)] is of    */
/*   type 4^delta; a sequence S such that either S or Phi(S) is */
/*   an s-PD-set for Cbin=Phi(C), where Phi is the Gray map,    */
/*   with respect to Phi(I); an integer s in [1,...,t], where t */
/*   is the error-correcting capability of Cbin; and a vector u */
/*   from the ambient space V=Z4^n or V2=Z2^(2n), attempt to    */
/*   decode u with respect to C. If the decoding algorithm      */
/*   succeeds in computing a vector u' in C as the decoded      */
/*   version of u in V, then the function returns true, u' and  */
/*   Phi(u'). If the decoding algorithm does not succeed in     */
/*   decoding u, then the function returns false, the zero      */
/*   vector in V and the zero vector in V2.                     */
/*   Instead of a vector u, we can also decode a sequence Q     */
/*   of vectors in V or V2.                                     */
/* Input parameters description:                                */
/*   - C : Code over Z4                                         */
/*   - I : Subset of integers in {1..n}                         */
/*   - S : Subset of permutations acting on {1..n} or {1..2n}   */
/*   - s : Integer in {1..t}, t is the correcting capability    */
/*   - u : Received vector to be decoded                        */
/* Output parameters description:                               */
/*   - Boolean, true if u is decoded and false otherwise        */
/*   - Decoded vector over Z4 of u, or the zero vector          */
/*   - Decoded binary vector of u, or the zero vector           */
/*                                                              */
/* case binary u                                                */
/* Signature: (<CodeLinRng> C, <[RngIntElt]> I,                 */
/*           <[GrpPermElt]> S, <RngIntElt> s, <ModTupFldElt> u) */       
/*           -> BoolElt, ModTupRngElt, ModTupFldElt             */
/* case quaternary u                                            */
/* Signature: (<CodeLinRng> C, <[RngIntElt]> I,                 */
/*           <[GrpPermElt]> S, <RngIntElt> s, <ModTupRngElt> u) */       
/*           -> BoolElt, ModTupRngElt, ModTupFldElt             */
/*                                                              */ 
/* case binary sequence Q                                       */
/* Signature: (<CodeLinRng> C, <[RngIntElt]> I,                 */
/*          <[GrpPermElt]> S, <RngIntElt> s, <[ModTupFldElt]> Q)*/       
/*           -> [BoolElt], [ModTupRngElt], [ModTupFldElt]       */
/* case quaternary sequence Q                                   */
/* Signature: (<CodeLinRng> C, <[RngIntElt]> I,                 */
/*          <[GrpPermElt]> S, <RngIntElt> s, <[ModTupRngElt]> Q)*/       
/*           -> [BoolElt], [ModTupRngElt], [ModTupFldElt]       */
/*                                                              */
/****************************************************************/
/****************************************************************/
/*                                                              */
/* Function name: PDSetHadamardCodeZ4                           */
/* Parameters: delta, m                                         */
/* Function description: Given an integer m>=5 and an integer   */
/*   delta such that 3<=delta<=floor((m+1)/2), the Hadamard     */
/*   code C over Z4 of length 2^(m-1) and type 2^gamma 4^delta, */
/*   where gamma=m+1-2delta, given by the function              */
/*   HadamardCodeZ4(delta,m), is considered.The function returns*/
/*   an information set I=[i_1,...,i_(gamma+delta)] in [1,...,n]*/
/*   for C together with a subset S of the permutation          */
/*   automorphism group of C such that Phi(S) is an s-PD-set    */
/*   for Cbin=Phi(C) with respect to Phi(I), where Phi is the   */
/*   Gray map and Phi(I) and Phi(S) are defined in the manual.  */
/*   The function also returns the information set Phi(I) and   */
/*   the s-PD-set Phi(S).                                       */
/* Input parameters description:                                */
/*   - delta : Integer                                          */
/*   - m : Integer                                              */
/* Output parameters description:                               */
/*   - Information set from {1..n} for the s-PD-set S           */ 
/*   - s-PD-set for the Hadamard code C over Z4                 */
/*   - Information set from {1..2n} for the s-PD-set Sbin       */
/*   - s-PD-set for the Cbin of the Hadamard code C over Z4     */ 
/*   - Invertible matrices over Z4, associated to the s-PD-set  */  
/*                                                              */
/* Signature: (<RngIntElt> delta, <RngIntElt> m, <RngIntElt> s) */   
/*              -> SeqEnum[RngIntElt], SeqEnum[GrpPermElt],     */
/*                 SeqEnum[RngIntElt], SeqEnum[GrpPermElt],     */
/*                 SeqEnum[AlgMatElt]                           */
/*                                                              */
/* Remark: The fifth output is only given when AlgMethod is set */
/*         to "Deterministic" and m+1-2*delta=0, that is, when  */
/*         gamma=0. This extra output is used to speed up some  */
/*         test to check whether a set is really an s-PD-set.   */
/*                                                              */
/****************************************************************/
/****************************************************************/
/*                                                              */
/* Function name: PDSetKerdockCodeZ4                            */
/* Parameters: m                                                */
/* Function description: Given an integer m >=4 such that 2^m-1 */
/*   is not a prime number, the Kerdock code C over Z4 of       */
/*   length n=2^m and type 4^(m-1), given by the function       */
/*   KerdockCodeZ4(m) is considered. The function returns the   */
/*   information set I={1,..,m+1} in {1,...,n} for C together   */
/*   with a subset S of the permutation automorphism group of C */
/*   such that Phi(S) is an s-PD-set for Cbin=Phi(C) with       */
/*   respect to Phi(I), where Phi is the Gray map and Phi(I)    */
/*   and Phi(S) are defined in the manual. The function also    */
/*   returns the information set Phi(I)={1,..,2m+2} and the     */
/*   s-PD-set Phi(S). The size of the s-PD-set S is always      */
/*   lambda=s+1, where lambda is the greatest divisor of 2^m-1  */
/*   such that lambda <= 2^m/(m+1).                             */
/* Input parameters description:                                */
/*   - m : Integer                                              */
/* Output parameters description:                               */
/*   - Information set from {1..n} for the s-PD-set S           */ 
/*   - s-PD-set for the Kerdock code C over Z4                  */
/*   - Information set from {1..2*n} for the s-PD-set Sbin       */
/*   - s-PD-set for the Cbin of the Kerdock code C over Z4      */ 
/*                                                              */
/* Signature: (<RngIntElt> m) -> SeqEnum[RngIntElt],            */
/*              SeqEnum[GrpPermElt], SeqEnum[RngIntElt],        */
/*              SeqEnum[GrpPermElt]                             */
/*                                                              */
/****************************************************************/
print "test 1: Z4-linear Hadamard code 
               #C = 64, length = 32, gamma = 0, delta = 3";

C := HadamardCodeZ4(3, 5);
R := RSpace(Integers(4), 16);
V := VectorSpace(GF(2), 32);

I := [1, 2, 5]; 
Ibin := [1, 2, 3, 4, 9, 10];

J := [1, 2, 3];
Jbin := [1, 2, 3, 4, 5, 6]; 

Is := [12, 15, 16]; 
Isbin := [23, 24, 29, 30, 31, 32];

s := 3;    

// u in C
u := R![3,2,1,0,1,0,3,2,3,2,1,0,1,0,3,2]; 
// v not in C, 3 errors in positions {1, 4, 12} 
v := R![0,2,1,3,1,0,3,2,3,2,1,3,1,0,3,2]; 
// w not in C, 4 errors in positions {1, 2, 4, 12} 
w := R![0,1,1,3,1,0,3,2,3,2,1,3,1,0,3,2];  
// ubin in Cbin
ubin := V![1,0,1,1,0,1,0,0,0,1,0,0,1,0,1,1,1,0,1,1,0,1,0,0,0,1,0,0,1,0,1,1]; 
// vbin not in Cbin, 3 errors in positions {1, 7, 23}
vbin := V![0,0,1,1,0,1,1,0,0,1,0,0,1,0,1,1,1,0,1,1,0,1,1,0,0,1,0,0,1,0,1,1]; 
// wbin not in Cbin, 4 errors in positions {1, 3, 7, 23}
wbin := V![0,0,0,1,0,1,1,0,0,1,0,0,1,0,1,1,1,0,1,1,0,1,1,0,0,1,0,0,1,0,1,1]; 

Q := [u, v, w];
Qbin := [ubin, vbin, wbin];

// p in PAut(C)
p := Sym(16)!(1,16, 11, 6)(2, 7, 12, 13)(3, 14, 9, 8)(4, 5, 10, 15); 
// q not in PAut(C)
q := Sym(16)!(1, 13, 2)(3, 14, 8, 15, 4, 11, 7, 6, 16, 12);

S1 := [p^i : i in [1..4]];
S2 := [q^i : i in [1..4]];
S1bin := [PermZ4ToPermZ2(p)^i : i in [1..4]];
S2bin := [PermZ4ToPermZ2(q)^i : i in [1..4]];

// Test InformationSet function
OutputInfoSet_C, OutputInfoSet_Cbin := InformationSet(C);
assert OutputInfoSet_C eq Is;
assert OutputInfoSet_Cbin eq Isbin;

// Test IsInformationSet function
OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, I);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Is);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Isbin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, J);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Jbin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq false;

// Test IsPermutationDecodeSet function
OutputIsPDSet := IsPermutationDecodeSet(C, I, S1, s);
assert OutputIsPDSet eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, Ibin, S1bin, s);
assert OutputIsPDSet eq true;
 
OutputIsPDSet := IsPermutationDecodeSet(C, Jbin, S1bin, s);
assert OutputIsPDSet eq false;
//assert OutputReason eq "Argument 2 is not an information set for Cbin = Phi(C)";

OutputIsPDSet := IsPermutationDecodeSet(C, Ibin, S2bin, s);
assert OutputIsPDSet eq false;
//assert OutputReason eq "Argument 3 is not a subset of the permutation automorphism group of Cbin = Phi(C)";

OutputIsPDSet := IsPermutationDecodeSet(C, Ibin, S1bin, s+1);
assert OutputIsPDSet eq false;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                            PermutationDecode(C, I, S1bin, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                            PermutationDecode(C, I, S1bin, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                            PermutationDecode(C, I, S1bin, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                            PermutationDecode(C, I, S1bin, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                            PermutationDecode(C, I, S1bin, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                            PermutationDecode(C, I, S1bin, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

OutputIsDecoded_Q, OutputDecoded_Q, OutputDecoded_Qbin := 
                                            PermutationDecode(C, I, S1bin, s, Q);
assert OutputIsDecoded_Q eq [true, true, false];
assert OutputDecoded_Q eq [u, u, R!0];
assert OutputDecoded_Qbin eq [ubin, ubin, V!0];

OutputIsDecoded_Q, OutputDecoded_Q, OutputDecoded_Qbin := 
                                            PermutationDecode(C, I, S1bin, s, Qbin);
assert OutputIsDecoded_Q eq [true, true, false];
assert OutputDecoded_Q eq [u, u, R!0];
assert OutputDecoded_Qbin eq [ubin, ubin, V!0];

// Test PDSetHadamardCodeZ4 function
delta, gamma := Z4Type(C);
m := gamma + 2*delta - 1;
s2 := Floor((2^(m-1)+delta-m-1)/(m+1-delta));

InfoSetZ4, PDSetZ4, InfoSetZ2, PDSetZ2:= PDSetHadamardCodeZ4(delta, m);

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ4);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ2);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, InfoSetZ4, PDSetZ4, s2);
assert OutputIsPDSet eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, InfoSetZ2, PDSetZ2, s2);
assert OutputIsPDSet eq true;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                    PermutationDecode(C, InfoSetZ4, PDSetZ4, s2, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

/****************************************************************/
print "test 2: Z4-linear Hadamard code 
       #C = 128, length = 64, gamma = 1, delta = 3";

C := HadamardCodeZ4(3, 6);
R := RSpace(Integers(4),32);
V := VectorSpace(GF(2),64);

I1 := [17, 1, 2, 5]; 
I2 := [17, 2, 5, 1];
I3 := [17, 5, 2, 1];

Is := [16, 28, 31, 32]; 
Isbin := [ 31, 55, 56, 61, 62, 63, 64 ];

J1bin := [1, 2, 3, 4, 5, 10, 42]; // syndrome in cosetSyndromes
J2bin := [2, 4, 10, 1, 5, 3, 42]; // shifted J1
Kbin := [1, 2, 3, 4, 5, 10, 31];  // Dimension(kernel) <> Dimension(punctureKernel)

s := 7;    

// u in C
u := R![1,2,3,0,0,1,2,3,3,0,1,2,2,3,0,1,3,0,1,2,2,3,0,1,1,2,3,0,0,1,2,3]; 
// v not in C, 5 (quaternary) errors in positions {1, 2, 3, 16, 27}
v := R![3,0,0,0,0,1,2,3,3,0,1,2,2,3,0,0,3,0,1,2,2,3,0,1,1,2,0,0,0,1,2,3];  
// w not in C, 6 (quaternary) errors in positions {1, 2, 3, 16, 27, 32}
w := R![3,0,0,0,0,1,2,3,3,0,1,2,2,3,0,0,3,0,1,2,2,3,0,1,1,2,0,0,0,1,2,2];  

// ubin in Cbin
ubin := V![0,1,1,1,1,0,0,0,0,0,0,1,1,1,1,0,1,0,0,0,0,1,1,1,1,1,1,0,0,0,0,1, 
           1,0,0,0,0,1,1,1,1,1,1,0,0,0,0,1,0,1,1,1,1,0,0,0,0,0,0,1,1,1,1,0];
// vbin not in Cbin, 7 errors in positions {1, 2, 3, 4, 5, 32, 53}
vbin := V![1,0,0,0,0,0,0,0,0,0,0,1,1,1,1,0,1,0,0,0,0,1,1,1,1,1,1,0,0,0,0,0, 
           1,0,0,0,0,1,1,1,1,1,1,0,0,0,0,1,0,1,1,1,0,0,0,0,0,0,0,1,1,1,1,0]; 
// vbin not in Cbin, 8 errors in positions {1, 2, 3, 4, 5, 32, 53, 64}
wbin := V![1,0,0,0,0,0,0,0,0,0,0,1,1,1,1,0,1,0,0,0,0,1,1,1,1,1,1,0,0,0,0,0, 
           1,0,0,0,0,1,1,1,1,1,1,0,0,0,0,1,0,1,1,1,0,0,0,0,0,0,0,1,1,1,1,1]; 

Q := [u, v, w];
Qbin := [ubin, vbin, wbin];

p := Sym(32)!(1, 24, 26, 15, 3, 22, 28, 13)(2, 23, 27, 14, 4, 21, 25, 16)
             (5, 11, 32, 20, 7, 9, 30, 18)(6, 10, 29, 19, 8, 12, 31,17);
S := [p^i : i in [1..8]];
Sbin := [PermZ4ToPermZ2(p)^i : i in [1..8]];

// Test InformationSet function
OutputInfoSet_C, OutputInfoSet_Cbin := InformationSet(C);
assert OutputInfoSet_C eq Is;
assert OutputInfoSet_Cbin eq Isbin;

// Test IsInformationSet function
OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, I1);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Is);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Isbin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, J1bin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, J2bin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Kbin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq false;

/* Test IsPermutationDecodeSet (SLOW, it takes 3 or 4 minutes)
/OutputIsPDSet := IsPermutationDecodeSet(C, I1, S, s);
assert OutputIsPDSet eq true;
*/

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
					  					  PermutationDecode(C, I1, Sbin, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
					                      PermutationDecode(C, I1, Sbin, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
					                      PermutationDecode(C, I1, Sbin, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
					  					  PermutationDecode(C, I1, Sbin, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
					                      PermutationDecode(C, I1, Sbin, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
					                      PermutationDecode(C, I1, Sbin, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

OutputIsDecoded_Q, OutputDecoded_Q, OutputDecoded_Qbin := 
                                            PermutationDecode(C, I, Sbin, s, Q);
assert OutputIsDecoded_Q eq [true, true, false];
assert OutputDecoded_Q eq [u, u, R!0];
assert OutputDecoded_Qbin eq [ubin, ubin, V!0];

OutputIsDecoded_Q, OutputDecoded_Q, OutputDecoded_Qbin := 
                                            PermutationDecode(C, I, Sbin, s, Qbin);
assert OutputIsDecoded_Q eq [true, true, false];
assert OutputDecoded_Q eq [u, u, R!0];
assert OutputDecoded_Qbin eq [ubin, ubin, V!0];

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
										  PermutationDecode(C, I2, Sbin, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I2, Sbin, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I2, Sbin, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
										  PermutationDecode(C, I2, Sbin, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I2, Sbin, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I2, Sbin, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I3, Sbin, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I3, Sbin, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I3, Sbin, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I3, Sbin, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I3, Sbin, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I3, Sbin, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

// Test PDSetHadamardCodeZ4 function
delta, gamma := Z4Type(C);
m := gamma + 2*delta - 1;
s := 4;

InfoSetZ4, PDSetZ4, InfoSetZ2, PDSetZ2:= PDSetHadamardCodeZ4(delta, m);

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ4);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ2);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, InfoSetZ4, PDSetZ4, s);
assert OutputIsPDSet eq true;

/* (SLOW)
OutputIsPDSet := IsPermutationDecodeSet(C, InfoSetZ2, PDSetZ2, s);
assert OutputIsPDSet eq true;*/

/****************************************************************/
print "test 3: Z4-linear Hadamard code 
       #C = 256, length = 128, gamma = 2, delta = 3";
       
C := HadamardCodeZ4(3, 7);
R := RSpace(Integers(4),64);
V := VectorSpace(GF(2),128);

I1 := [17, 33, 1, 2, 5]; 
I2 := [17, 33, 2, 5, 1];
I3 := [33, 17, 5, 2, 1];

Is := [32, 48, 60, 63, 64];
Isbin := [63, 95, 119, 120, 125, 126, 127, 128];

s := 9;    

// u in C
u := R![0,3,2,1,2,1,0,3,0,3,2,1,2,1,0,3,2,1,0,3,0,3,2,1,2,1,0,3,0,3,2,1,
        0,3,2,1,2,1,0,3,0,3,2,1,2,1,0,3,2,1,0,3,0,3,2,1,2,1,0,3,0,3,2,1];
 
// v not in C, 5 (quaternary) errors in positions {1,2,3,4,5,6,7,8,9}
v := R![3,0,1,2,1,2,3,0,3,3,2,1,2,1,0,3,2,1,0,3,0,3,2,1,2,1,0,3,0,3,2,1,
        0,3,2,1,2,1,0,3,0,3,2,1,2,1,0,3,2,1,0,3,0,3,2,1,2,1,0,3,0,3,2,1];
// w not in C, 6 (quaternary) errors in positions {1,2,3,4,5,6,7,8,9,64}
w := R![3,0,1,2,1,2,3,0,3,3,2,1,2,1,0,3,2,1,0,3,0,3,2,1,2,1,0,3,0,3,2,1,
        0,3,2,1,2,1,0,3,0,3,2,1,2,1,0,3,2,1,0,3,0,3,2,1,2,1,0,3,0,3,2,0];

// ubin in Cbin
ubin := V![0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,
           1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,
           0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,
           1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1];

// vbin not in Cbin, 9 errors in positions {1,3,5,7,9,11,13,15,17}.
vbin := V![1,0,0,0,0,1,1,1,0,1,1,1,1,0,0,0,1,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,
           1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,
           0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,
           1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1];

// vbin not in Cbin, 10 errors in positions {1,3,5,7,9,11,13,15,17,128}
wbin := V![1,0,0,0,0,1,1,1,0,1,1,1,1,0,0,0,1,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,
           1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,
           0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,
           1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,1,1,1,0,1,0,0,1,0,0,0,1,0,1,1,0,0];

p1 := Sym(64)!1;
p2 := Sym(64)!(1, 18, 23, 6)(2, 45, 30, 51)(3, 28, 21, 16)(4, 39, 32, 57)
              (5, 54, 27, 42)(7, 64, 25, 36)(8, 11, 20, 29)(9, 26, 31, 14)
              (10, 37, 22, 59)(12, 47,24, 49)(13, 62, 19, 34)(15, 56, 17, 44)
              (33, 50, 55, 38)(35, 60, 53, 48)(40, 43, 52, 61)(41, 58, 63, 46);

p3 := Sym(64)!(1, 22, 41, 16)(2, 10, 12, 4)(3, 30, 43, 8)(5, 23, 61, 47)
              (6, 11, 32, 35)(7, 31, 63, 39)(9, 24, 33, 14)(13, 21, 53, 45)
              (15, 29, 55, 37)(17, 56, 57, 46)(18, 44, 28, 34)(19, 64, 59, 38)
              (20, 36, 26, 42)(25, 54, 49, 48)(27, 62, 51, 40)(50, 52, 60, 58);

p4 := Sym(64)!(1, 42, 35, 10)(2, 9, 34, 43)(3, 44, 33, 12)(4, 11, 36, 41)
              (5, 46, 39, 14)(6, 13, 38, 47)(7, 48, 37, 16)(8, 15, 40, 45)
              (17, 58, 51, 26)(18, 25, 50, 59)(19, 60, 49, 28)(20, 27, 52, 57)
	      (21, 62, 55, 30)(22, 29, 54, 63)(23, 64, 53, 32)(24, 31, 56, 61);

p5 := Sym(64)!(1, 30, 21, 27, 48, 53, 3, 22, 31, 25, 40, 63)(2, 18, 34, 10, 28, 36)
              (4, 26,44, 12, 20, 42)(5, 43, 8, 39, 59, 56, 15, 41, 16, 45, 57, 64)
              (6, 47, 49,54, 7, 35, 14, 37, 51, 62, 13, 33)
              (9, 24, 23, 19, 38, 55, 11, 32, 29, 17, 46, 61)(50, 58, 52);

p6 := Sym(64)!(1, 14, 53, 27, 64, 47, 41, 38, 29, 51, 24, 7)(2, 52, 42, 28)
              (3, 6, 63, 25, 56, 37, 43, 46, 23, 49, 32, 13)
              (4, 60, 36, 26, 10, 58, 44, 20, 12, 50, 34, 18)
              (5, 9, 8, 55, 19, 54, 45, 33, 48, 31, 59, 30)
              (11, 16, 61, 17, 62,39, 35, 40, 21, 57, 22, 15);

p7 := Sym(64)!(1, 10, 3, 12)(2, 11, 4, 9)(5, 56, 45, 14, 61, 38, 7, 54, 47, 16, 63, 40)
              (6, 53, 46, 15, 62, 39, 8, 55, 48, 13, 64, 37)
              (17, 34, 57, 28, 41, 52, 19, 36, 59, 26, 43, 50)
              (18, 35, 58, 25, 42, 49, 20, 33, 60, 27, 44, 51)
              (21, 32, 23, 30)(22, 29, 24, 31);

p8 := Sym(64)!(1, 50, 45, 30, 9, 58, 37, 22)(2, 63, 46, 27, 10, 55, 38, 19)
              (3, 60, 47, 24,11, 52, 39, 32)(4, 53, 48, 17, 12, 61, 40, 25)
              (5, 62, 33, 26, 13, 54,41, 18)(6, 59, 34, 23, 14, 51, 42, 31)
              (7, 56, 35, 20, 15, 64, 43, 28)(8,49, 36, 29, 16, 57, 44, 21);

p9 := Sym(64)!(1, 30, 4, 55, 17, 16, 20, 37)(2, 53, 19, 14, 18, 39, 3, 32)
              (5, 49, 64, 50, 23, 33, 46, 34)(6, 28, 47, 9, 24, 12, 61, 25)
              (7, 51, 62, 52, 21, 35, 48,36)(8, 26, 45, 11, 22, 10, 63, 27)
              (13, 59, 56, 60, 31, 43, 38, 44)(15, 57, 54, 58, 29, 41, 40, 42);

p10 := Sym(64)!(1, 58, 15, 33, 12, 31, 9, 60, 5, 41, 10, 21)
               (2, 23, 11, 50, 13, 43, 4, 29, 3, 52, 7, 35)(8, 16, 14)
               (17, 18, 63, 59, 44, 45, 25, 20, 53, 51, 42, 39)
               (19, 28, 55, 57, 34, 37, 27, 26, 61, 49, 36, 47)
               (22, 46, 54, 32, 38, 56)(24, 40, 62, 30, 48, 64);

S := [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10];
Sbin := [PermZ4ToPermZ2(p) : p in S];

// Test InformationSet function
OutputInfoSet_C, OutputInfoSet_Cbin := InformationSet(C);
assert Set(OutputInfoSet_C) eq Set(Is);
assert Set(OutputInfoSet_Cbin) eq Set(Isbin);

// Test IsInformationSet function
OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, I1);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Is);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Isbin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I1, Sbin, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I1, Sbin, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I1, Sbin, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I1, Sbin, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I1, Sbin, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I1, Sbin, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I2, Sbin, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I2, Sbin, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I2, Sbin, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I3, Sbin, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I3, Sbin, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I3, Sbin, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

/****************************************************************/
print "test 4: binary Kerdock code 
       #C = 1024, length = 32, gamma = 0, delta = 5";

C := KerdockCode(4);
R := RSpace(Integers(4), 16);
V := VectorSpace(GF(2), 32);

I1 := [1, 2, 3, 4, 5];
I2 := [5, 3, 1, 2, 4];
I3 := [2, 3, 5, 4, 1];

Ibin := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

Is := [12, 13, 14, 15, 16];
Isbin := [23, 24, 25, 26, 27, 28, 29, 30, 31, 32];

s := 2;    

p := Sym(16)!(1, 6, 11)(2, 7, 12)(3, 8, 13)(4, 9, 14)(5, 10, 15);
S := [p^i : i in [1..3]];
Sbin := [PermZ4ToPermZ2(p)^i : i in [1..3]];

// u in C
u := R![2,0,2,2,3,3,3,0,3,1,0,2,3,0,1,3];  
// v not in C, 2 (quaternary) errors in positions {1,12}
v := R![1,0,2,2,3,3,3,0,3,1,0,3,3,0,1,3]; 
// w not in C, 3 (quaternary) errors in positions {1,12,16}
w := R![1,0,2,2,3,3,3,0,3,1,0,3,3,0,1,2];  

// ubin in Cbin
ubin := V![1,1,0,0,1,1,1,1,1,0,1,0,1,0,0,0,1,0,0,1,0,0,1,1,1,0,0,0,0,1,1,0]; 
// vbin not in Cbin, 2 errors in positions {1, 24}
vbin := V![0,1,0,0,1,1,1,1,1,0,1,0,1,0,0,0,1,0,0,1,0,0,1,0,1,0,0,0,0,1,1,0]; 
// wbin not in Cbin, 3 errors in positions {1, 24, 32}
wbin := V![0,1,0,0,1,1,1,1,1,0,1,0,1,0,0,0,1,0,0,1,0,0,1,0,1,0,0,0,0,1,1,1];

// Test InformationSet function
OutputInfoSet_C, OutputInfoSet_Cbin := InformationSet(C);
assert OutputInfoSet_C eq Is;
assert OutputInfoSet_Cbin eq Isbin;

// Test IsInformationSet function
OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, I1);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Is);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Isbin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

// Test IsPermutationDecodeSet function
OutputIsPDSet := IsPermutationDecodeSet(C, I1, S, s);
assert OutputIsPDSet eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, I1, S, s+1);
assert OutputIsPDSet eq false;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I1, S, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I1, S, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I1, S, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I1, S, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I1, S, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I1, S, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I2, S, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I2, S, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I2, S, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I3, S, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I3, S, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I3, S, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

// Test PDSetKerdockCodeZ4 function
s := 2;

InfoSetZ4, PDSetZ4, InfoSetZ2, PDSetZ2 := PDSetKerdockCodeZ4(4);

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ4);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ2);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, InfoSetZ4, PDSetZ4, s);
assert OutputIsPDSet eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, InfoSetZ2, PDSetZ2, s);
assert OutputIsPDSet eq true;

/****************************************************************/
print "test 5: binary Kerdock code 
       #C = 4096, length = 64, gamma = 0, delta = 6";

C := KerdockCode(5);
R := RSpace(Integers(4), 32);
V := VectorSpace(GF(2), 64);

I1 := [1, 2, 3, 4, 5, 6];
I2 := [5, 3, 1, 2, 4, 6];
I3 := [2, 3, 5, 6, 4, 1];

I1bin := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];

Is := [27, 28, 29, 30, 31, 32];
Isbin := [53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64];

s := 4;    

p := Sym(32)!(1, 32, 9, 19, 25)(2, 18, 24, 15, 31)(3, 27, 23, 28, 12)
             (4, 8, 20, 30, 26)(5, 14, 16, 21,13)(6, 10, 17, 29, 22);
S := [p^i : i in [1..5]];
Sbin := [PermZ4ToPermZ2(p)^i: i in [1..5]];

// u in C
u := R![1,1,3,3,1,0,0,0,3,3,2,1,3,1,2,1,2,1,0,0,0,2,3,2,0,1,0,1,1,0,0,2];  
// v not in C, 4 (quaternary) errors in positions {1, 20, 28, 31};
v := R![2,1,3,3,1,0,0,0,3,3,2,1,3,1,2,1,2,1,0,1,0,2,3,2,0,1,0,2,1,0,3,2];
// w not in C, 5 (quaternary) errors in positions {1, 20, 28, 31, 14};
w := R![2,1,3,3,1,0,0,0,3,3,2,1,3,2,2,1,2,1,0,1,0,2,3,2,0,1,0,2,1,0,3,2];  

// ubin in Cbin
ubin := V![0,1,0,1,1,0,1,0,0,1,0,0,0,0,0,0,1,0,1,0,1,1,0,1,1,0,0,1,1,1,0,1,
           1,1,0,1,0,0,0,0,0,0,1,1,1,0,1,1,0,0,0,1,0,0,0,1,0,1,0,0,0,0,1,1]; 
// vbin not in Cbin, 4 errors in positions {1, 39, 55, 61}
vbin := V![1,1,0,1,1,0,1,0,0,1,0,0,0,0,0,0,1,0,1,0,1,1,0,1,1,0,0,1,1,1,0,1,
           1,1,0,1,0,0,1,0,0,0,1,1,1,0,1,1,0,0,0,1,0,0,1,1,0,1,0,0,1,0,1,1];
// wbin not in Cbin, 5 errors in positions {1, 39, 55, 61, 27}
wbin := V![1,1,0,1,1,0,1,0,0,1,0,0,0,0,0,0,1,0,1,0,1,1,0,1,1,0,1,1,1,1,0,1,
           1,1,0,1,0,0,1,0,0,0,1,1,1,0,1,1,0,0,0,1,0,0,1,1,0,1,0,0,1,0,1,1];

// Test InformationSet function
OutputInfoSet_C, OutputInfoSet_Cbin := InformationSet(C);
assert OutputInfoSet_C eq Is;
assert OutputInfoSet_Cbin eq Isbin;

// Test IsInformationSet function
OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, I1);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Is);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Isbin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

/* Test IsPermutationDecodeSet (SLOW, it takes 2 or 3 minutes)
OutputIsPDSet := IsPermutationDecodeSet(C, I1bin, Sbin, s);
assert OutputIsPDSet eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, I1bin, Sbin, s+1);
assert OutputIsPDSet eq false; 
*/

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I1, Sbin, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I1, Sbin, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I1, Sbin, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I1, Sbin, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I1, Sbin, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I1, Sbin, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I2, S, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I2, S, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I2, S, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I3, S, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I3, S, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I3, S, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

/****************************************************************/
print "test 6: Z4-linear code 
      #C = 32, length = 32, gamma = 5, delta = 0";

G := Matrix(Integers(4),[[2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2], 
		                 [0,2,0,0,0,2,0,0,2,2,0,2,0,2,2,2],
                         [0,0,2,0,0,2,2,0,2,0,2,2,2,2,0,0],
                         [0,0,0,2,0,0,2,2,0,2,0,2,2,2,2,0],
                         [0,0,0,0,2,0,0,2,2,0,2,0,2,2,2,2]]);
C := LinearCode(G);
R := RSpace(Integers(4), 16);
V := VectorSpace(GF(2), 32);

I := [1, 2, 3, 4, 5];
Ibin := [1, 3, 5, 7, 9];

Is:= [12, 13, 14, 15, 16];     
Isbin:= [23, 25, 27, 29, 31];

s := 2;

// u in C
u := R![0,2,0,0,0,2,0,0,2,2,0,2,0,2,2,2];  
// v not in C, 2 (quaternary) errors in positions {2, 8};
v := R![0,1,0,0,0,2,0,3,2,2,0,2,0,2,2,2];  
// w not in C, 3 (quaternary) errors in positions {2, 8, 6};
w := R![0,1,0,0,0,1,0,3,2,2,0,2,0,2,2,2]; 

// ubin in Cbin
ubin := V![0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,1,1,1,1,0,0,1,1,0,0,1,1,1,1,1,1];
// vbin not in Cbin, 2 errors in positions {3, 15}
vbin := V![0,0,0,1,0,0,0,0,0,0,1,1,0,0,1,0,1,1,1,1,0,0,1,1,0,0,1,1,1,1,1,1];
// wbin not in Cbin, 3 errors in positions {3, 15, 11}
wbin := V![0,0,0,1,0,0,0,0,0,0,0,1,0,0,1,0,1,1,1,1,0,0,1,1,0,0,1,1,1,1,1,1];

p1 := Sym(16)!1;
p2 := Sym(16)!(1, 14, 11, 9, 6, 10, 13, 3, 15, 5, 16, 2, 12, 8)(4, 7);
p3 := Sym(16)!(1, 14, 11, 2, 7, 9, 5, 12, 3, 16, 13, 6)(4, 15, 8, 10);

S := [p1, p2, p3];
Sbin := [PermZ4ToPermZ2(p) : p in S];

// Test InformationSet function
OutputInfoSet_C, OutputInfoSet_Cbin := InformationSet(C);
assert Set(OutputInfoSet_C) eq Set(Is);
assert Set(OutputInfoSet_Cbin) eq Set(Isbin);

// Test IsInformationSet function
OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, I);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Is);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Isbin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

// Test IsPermutationDecodeSet function
OutputIsPDSet := IsPermutationDecodeSet(C, Ibin, Sbin, s);
assert OutputIsPDSet eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, Ibin, Sbin, s+1);
assert OutputIsPDSet eq false;

OutputIsPDSet := IsPermutationDecodeSet(C, I, S, s);
assert OutputIsPDSet eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, I, S, s+1);
assert OutputIsPDSet eq false;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I, Sbin, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I, Sbin, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I, Sbin, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I, S, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I, S, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I, S, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0;

/****************************************************************/
print "test 7: Z4-linear code 
      #C = 16, length = 30, gamma = 4, delta = 0";

G := Matrix(Integers(4),[[2,0,0,0,2,0,0,2,2,0,2,0,2,2,2],
                         [0,2,0,0,2,2,0,2,0,2,2,2,2,0,0],
                         [0,0,2,0,0,2,2,0,2,0,2,2,2,2,0],
                         [0,0,0,2,0,0,2,2,0,2,0,2,2,2,2]]);
C := LinearCode(G);
R := RSpace(Integers(4), 15);
V := VectorSpace(GF(2), 30);

I := [1, 2, 3, 4];
Ibin := [1, 3, 5, 7];

Is := [12, 13, 14, 15];      
Isbin := [23, 25, 27, 29];

s := 2;

// u in C
u := R![2,2,0,2,0,2,2,2,2,0,0,0,2,0,0];  
// v not in C, 2 (quaternary) errors in positions {1, 13};
v := R![1,2,0,2,0,2,2,2,2,0,0,0,1,0,0];  
// w not in C, 3 (quaternary) errors in positions {1, 2, 13};
w := R![1,1,0,2,0,2,2,2,2,0,0,0,1,0,0];  

// ubin in Cbin
ubin := V![1,1,1,1,0,0,1,1,0,0,1,1,1,1,1,1,1,1,0,0,0,0,0,0,1,1,0,0,0,0];
// vbin not in Cbin, 2 errors in positions {1, 25}
vbin := V![0,1,1,1,0,0,1,1,0,0,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,1,0,0,0,0];
// wbin not in Cbin, 3 errors in positions {1, 3, 25}
wbin := V![0,1,0,1,0,0,1,1,0,0,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,1,0,0,0,0];

p1 := Sym(15)!1;
p2 := Sym(15)!(1, 8, 3, 6, 9, 14)(2, 5, 4, 7, 10, 13)(11, 12, 15);
p3 := Sym(15)!(1, 10, 6, 2, 14, 12, 15)(3, 13, 5, 11, 4, 8, 7);

q := Sym(15)!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);

S1bin := [PermZ4ToPermZ2(p1), PermZ4ToPermZ2(p2), PermZ4ToPermZ2(p3)];
S2bin := [PermZ4ToPermZ2(q)^i : i in [1..15]];

// Test InformationSet function
OutputInfoSet_C, OutputInfoSet_Cbin := InformationSet(C);
assert Set(OutputInfoSet_C) eq Set(Is);
assert Set(OutputInfoSet_Cbin) eq Set(Isbin);

// Test IsInformationSet function
OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, I);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Is);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Isbin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

// Test IsPermutationDecodeSet function
OutputIsPDSet := IsPermutationDecodeSet(C, Ibin, S1bin, s);
assert OutputIsPDSet eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, Ibin, S1bin, s+1);
assert OutputIsPDSet eq false;

OutputIsPDSet := IsPermutationDecodeSet(C, Ibin, S2bin, s+1);
assert OutputIsPDSet eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, Ibin, S2bin, s+2);
assert OutputIsPDSet eq false;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I, S1bin, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I, S1bin, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I, S1bin, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0; 

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I, S2bin, s+1, wbin);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq u;
assert OutputDecoded_wbin eq ubin;

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I, S1bin, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I, S1bin, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I, S1bin, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0; 

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I, S2bin, s+1, w);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq u;
assert OutputDecoded_wbin eq ubin;

/****************************************************************/
print "test 8: Z4-linear Hadamard code 
      #C = 32, length = 16, gamma = 1, delta = 2";

C := HadamardCodeZ4(2, 4);
R := RSpace(Integers(4), 8);
V := VectorSpace(GF(2), 16);

I := [1, 2, 5];
Ibin := [1, 2, 3, 4, 9];

J := [7, 1, 4];
Jbin := [13, 1, 2, 7, 8];

Is := [4, 7, 8];
Isbin := [7, 13, 14, 15, 16];

s := 2;

// u in C
u := R![3,1,3,1,1,3,1,3];  
// v not in C, 2 (quaternary) errors in positions {1, 7};
v := R![0,1,3,1,1,3,0,3];
// w not in C, 3 (quaternary) errors in positions {1, 7, 8};
w := R![0,1,3,1,1,3,0,2];

// ubin in Cbin
ubin := V![1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0];
// vbin not in Cbin, 2 errors in positions {1, 14}
vbin := V![0,0,0,1,1,0,0,1,0,1,1,0,0,0,1,0];
// wbin not in Cbin, 3 errors in positions {1, 14, 16}
wbin := V![0,0,0,1,1,0,0,1,0,1,1,0,0,0,1,1];

p1 := Sym(16)!1;
p2 := Sym(16)!(1, 16, 8, 3, 7, 9, 11, 4, 13, 5, 6, 2, 12, 14)(10, 15);
p3 := Sym(16)!(1, 16, 8, 2, 15, 3, 5, 12, 4, 6, 11, 7)(9, 10, 13, 14);
p4 := Sym(16)!(1, 9)(2, 10)(3, 15)(4, 16)(5, 13)(6, 14)(7, 11)(8, 12);

// S1, S2 in PAut(Cbin), Sbin <> Phi(S).
S1bin := [p1, p2, p3];
S2bin := [p1, p2, p4];

// Test InformationSet function
OutputInfoSet_C, OutputInfoSet_Cbin := InformationSet(C);
assert Set(OutputInfoSet_C) eq Set(Is);
assert Set(OutputInfoSet_Cbin) eq Set(Isbin);

// Test IsInformationSet function
OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, I);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Ibin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Is);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Isbin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, J);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Jbin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

// Test IsPermutationDecodeSet function
OutputIsPDSet := IsPermutationDecodeSet(C, Jbin, S1bin, s);
assert OutputIsPDSet eq false;

OutputIsPDSet := IsPermutationDecodeSet(C, Jbin, S2bin, s);
assert OutputIsPDSet eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, Jbin, S2bin, s+1);
assert OutputIsPDSet eq false;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, J, S2bin, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, J, S2bin, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, J, S2bin, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0; 

/****************************************************************/
print "test 9: (nonlinear) Z4-linear code. 
      Gray map image of a quaternary linear cyclic code.
      #C = 8192 , length = 30, gamma = 1, delta = 6";

PR4<y> := PolynomialRing(Integers(4));   // Cyclic Linear Code C over Integers(4)
C := CyclicCode(15, y^9 + 3*y^7 + y^6 + y^3 + 3*y^2 + 1); 
R := RSpace(Integers(4), 15);
V := VectorSpace(GF(2), 30);

I := [7, 1, 2, 3, 4, 5, 6];
Ibin := [13, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];

tau := Sym(15)!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
S := [tau^i : i in [1..15]];

s := 2;   // t = 2

// u in C
u := R![3,2,0,0,3,2,2,1,3,3,3,1,1,0,2];  
// v not in C, 2 (quaternary) errors in positions {1, 2};
v := R![2,3,0,0,3,2,2,1,3,3,3,1,1,0,2];
// w not in C, 3 (quaternary) errors in positions {1, 2, 3};
w := R![2,3,3,0,3,2,2,1,3,3,3,1,1,0,2];

// ubin in Cbin
ubin := V![1,0,1,1,0,0,0,0,1,0,1,1,1,1,0,1,1,0,1,0,1,0,0,1,0,1,0,0,1,1];
// vbin not in Cbin, 2 errors in positions {2, 4}
vbin := V![1,1,1,0,0,0,0,0,1,0,1,1,1,1,0,1,1,0,1,0,1,0,0,1,0,1,0,0,1,1];
// wbin not in Cbin, 3 errors in positions {2, 4, 5}
wbin := V![1,1,1,0,1,0,0,0,1,0,1,1,1,1,0,1,1,0,1,0,1,0,0,1,0,1,0,0,1,1];

// Test IsInformationSet function
OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, I);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, Ibin);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

// Test IsPermutationDecodeSet function
OutputIsPDSet := IsPermutationDecodeSet(C, I, S, s);
assert OutputIsPDSet eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, I, S, s+1);
assert OutputIsPDSet eq false;

// Test PermutationDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I, S, s, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I, S, s, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I, S, s, wbin);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0; 

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := 
                                          PermutationDecode(C, I, S, s, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := 
                                          PermutationDecode(C, I, S, s, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := 
                                          PermutationDecode(C, I, S, s, w);
assert OutputIsDecoded_w eq false;
assert OutputDecoded_w eq R!0;
assert OutputDecoded_wbin eq V!0; 

/****************************************************************/
print "test 10: PDSetHadamardCodeZ4 function for
      Z4-linear Hadamard codes of type 4^delta with delta in [3,4,5]
      #C = 4^delta, length = 4^(delta-1), gamma = 0";

//***************************
// Hadamard code of type 4^3 
delta := 3;
gamma := 0;
m := gamma + 2*delta - 1;
C := HadamardCodeZ4(delta, m);
s := Floor((2^(m-1)+delta-m-1)/(m+1-delta));

InfoSetZ4, PDSetZ4, InfoSetZ2, PDSetZ2, MatPDSetZ4 := PDSetHadamardCodeZ4(delta, m);

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ4);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ2);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, InfoSetZ4, PDSetZ4, s);
assert OutputIsPDSet eq true;

OutputIsPDSet := IsPermutationDecodeSet(C, InfoSetZ2, PDSetZ2, s);
assert OutputIsPDSet eq true;

//Check that the matrices in MatPDSetZ4 are all invertibles
//the corresponding M^(-1)^* have no rows in common 
MatPDSetZ4inv := [ M^(-1) : M in MatPDSetZ4 ];
allRows := [];
for M in MatPDSetZ4inv do
    Append(~allRows, M[1]);
    for i in [2..NumberOfRows(M)] do
        Append(~allRows, M[1] + M[i]);
   end for;
end for;
assert #Set(allRows) eq (s+1)*delta;

//***************************
// Hadamard code of type 4^4 
delta := 4;
gamma := 0;
m := gamma + 2*delta - 1;
C := HadamardCodeZ4(delta, m);
s := Floor((2^(m-1)+delta-m-1)/(m+1-delta));

InfoSetZ4, PDSetZ4, InfoSetZ2, PDSetZ2, MatPDSetZ4 := PDSetHadamardCodeZ4(delta, m);

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ4);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ2);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

// Check that the matrices in MatPDSetZ4 are all invertibles
// the corresponding M^(-1)^* have no rows in common 
MatPDSetZ4inv := [ M^(-1) : M in MatPDSetZ4 ];
allRows := [];
for M in MatPDSetZ4inv do
    Append(~allRows, M[1]);
    for i in [2..NumberOfRows(M)] do
        Append(~allRows, M[1] + M[i]);
    end for;
end for;
assert #Set(allRows) eq (s+1)*delta;

//***************************
// Hadamard code of type 4^5 
delta := 5;
gamma := 0;
m := gamma + 2*delta - 1;
C := HadamardCodeZ4(delta, m);
s := Floor((2^(m-1)+delta-m-1)/(m+1-delta));

InfoSetZ4, PDSetZ4, InfoSetZ2, PDSetZ2, MatPDSetZ4 := PDSetHadamardCodeZ4(delta, m);

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ4);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ2);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

// Check that the matrices in MatPDSetZ4 are all invertibles
// the corresponding M^(-1)^* have no rows in common 
MatPDSetZ4inv := [ M^(-1) : M in MatPDSetZ4 ];
allRows := [];
for M in MatPDSetZ4inv do
    Append(~allRows, M[1]);
    for i in [2..NumberOfRows(M)] do
        Append(~allRows, M[1] + M[i]);
   end for;
end for;
assert #Set(allRows) eq (s+1)*delta;

/****************************************************************/
print "test 11: Z4-linear Hadamard code 
      #C = 256, length = 128, gamma = 2, delta = 3";

delta := 3;
gamma := 2;
m := gamma + 2*delta - 1;
C := HadamardCodeZ4(delta, m);

InfoSetZ4, PDSetZ4, InfoSetZ2, PDSetZ2, MatPDSetZ4 := 
                PDSetHadamardCodeZ4(delta, m : AlgMethod := "Nondeterministic");
s := #PDSetZ4 - 1;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ4);
assert OutputIsInfoSet_C eq true;
assert OutputIsInfoSet_Cbin eq false;

OutputIsInfoSet_C, OutputIsInfoSet_Cbin := IsInformationSet(C, InfoSetZ2);
assert OutputIsInfoSet_C eq false;
assert OutputIsInfoSet_Cbin eq true;

// Check that the matrices in MatPDSetZ4 are all invertibles
// the corresponding M^(-1)^* have no rows in common 
MatPDSetZ4inv := [ M^(-1) : M in MatPDSetZ4 ];
allRows := [];
for M in MatPDSetZ4inv do
    Append(~allRows, M[1]);
    for i in [2..delta] do
        Append(~allRows, M[1] + M[i]);
    end for;
    for i in [delta+1..gamma+delta] do
        Append(~allRows, M[1] + 2*M[i]);
    end for;
end for;
assert #Set(allRows) eq (s+1)*(gamma+delta);
