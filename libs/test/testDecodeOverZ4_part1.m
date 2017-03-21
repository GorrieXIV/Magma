/************************************************************/
/*                                                          */
/* Project name: Codes over Z4 in MAGMA                     */
/* Test file name: testDecodeOverZ4.m                       */
/*                                                          */
/* Comments: Black-box tests for the functions              */
/*           InformationSpace, SyndromeSpace, Syndrome      */
/*           CosetLeaders, CosetDecode, SyndromeDecode      */
/*           and LiftedDecode                               */
/*           included in the DecodeOverZ4.m file            */
/*                                                          */
/* Authors: M. Villanueva and J. Pujol                      */
/*                                                          */
/* Revision version and last date: 1.0, 2015/10/05          */
/*                                 1.1, 2015/12/17          */
/*                                 1.2, 2016/02/20          */
/*                                 1.3, 2016/05/06          */
/*                                                          */
/************************************************************/
 
SetAssertions(true);
Alarm(30*60);

/****************************************************************/
/*                                                              */
/* Function name: InformationSpace                              */
/* Parameters: C                                                */
/* Function description: Given a code C over Z4 of length n and */
/*   type 2^gamma 4^delta, return the Z4-submodule of Z4^(gamma */
/*   +delta) isomorphic to Z2^gamma x Z4^delta such that the    */
/*   first gamma coordinates are of order two, that is, the     */
/*   space of information vectors for C. The function also      */
/*   returns the (gamma+2delta)-dimensional binary vector space,*/
/*   which is the space of information vectors for the corres-  */
/*   ponding binary code Cbin=Phi(C), where Phi is the Gray map.*/
/*   Finally, for the encoding process, it also returns the     */
/*   corresponding isomorphisms f and fbin from these spaces of */
/*   information vectors onto C and Cbin, respectively.         */
/* Input parameters description:                                */
/*   - C : Code over Z4                                         */
/* Output parameters description:                               */
/*   - Z4-submodule of length gamma+delta                       */
/*   - Binary vector space of dimension gamma+2delta            */
/*   - Map encoding information vectors over Z4 to C            */
/*   - Map encoding information binary vectors to Cbin          */
/*                                                              */
/* Signature: (<CodeLinRng> C) -> ModTupRng, ModTupFld, Map, Map*/
/*                                                              */
/****************************************************************/
/****************************************************************/
/*                                                              */
/* Function name: SyndromeSpace                                 */
/* Parameters: C                                                */
/* Function description: Given a code C over Z4 of length n and */
/*   type 2^gamma 4^delta, return the Z4-submodule of Z4^(n-    */
/*   delta) isomorphic to Z2^gamma x Z4^(n-gamma-delta) such    */
/*   that the first gamma coordinates are of order two, that is,*/
/*   the space of syndrome vectors for C. The function also     */
/*   returns the (2n-2delta-gamma)-dimensional binary vector    */
/*   space,  which is the space of syndrome vectors for the     */
/*   corresponding binary code Cbin=Phi(C), where Phi is the    */
/*   Gray map. Note that these spaces are computed by using the */
/*   function InformationSpace(C) applied to the dual code of   */
/*   C, given by function Dual(C).                              */
/* Input parameters description:                                */
/*   - C : Code over Z4                                         */
/* Output parameters description:                               */
/*   - Z4-submodule of length n-delta                           */
/*   - Binary vector space of dimension 2n-2delta-gamma         */
/*                                                              */
/* Signature: (<CodeLinRng> C) -> ModTupRng, ModTupFld          */
/*                                                              */
/****************************************************************/
/****************************************************************/
/*                                                              */
/* Function name: Syndrome                                      */
/* Parameters: u, C                                             */
/* Function description: Given a code C over Z4 of length n and */
/*   type 2^gamma 4^delta, and a vector u from the ambient space*/
/*   V=Z4^n or V2=Z2^(2n), construct the syndrome of u relative */
/*   to the code C. This will be an element of the syndrome     */
/*   space of C, considered as the Z4-submodule of Z4^(n-delta) */
/*   isomorphic to Z2^gamma x Z4^(n-gamma-delta) such that the  */
/*   first gamma coordinates are of order two.                  */
/* Input parameters description:                                */
/*   - Vector over Z4 of length n or                            */
/*     binary vector of length 2n                               */ 
/*   - C : Code over Z4                                         */
/* Output parameters description:                               */
/*   - Vector over Z4 of length n-delta                         */
/*                                                              */
/* Signature: (<ModTupRngElt> u, <CodeLinRng> C) -> ModTupRngElt*/
/* Signature: (<ModTupFldElt> u, <CodeLinRng> C) -> ModTupRngElt*/
/*                                                              */
/****************************************************************/
/****************************************************************/
/*                                                              */
/* Function name: CosetLeaders                                  */
/* Parameters: C                                                */
/* Function description: Given a code C over Z4 of length n,    */
/*   with ambient space V=Z4^n, return a set of coset leaders   */
/*   (vectors of minimal Lee weight in their cosets) for C in V */
/*   as an indexed set of vectors from V. This function also    */
/*   returns a map from the syndrome space of C into the coset  */
/*   leaders (mapping a syndrome into its corresponding coset   */
/*   leader). Note that this function is only applicable when V */
/*   and C are small.                                           */
/* Input parameters description:                                */
/*   - C : Code over Z4                                         */
/* Output parameters description:                               */
/*   - Indexed set of vectors from V                            */
/*   - Map from the syndrome space of C into the coset leaders  */
/*                                                              */
/* Signature: (<CodeLinRng> C) -> SetIndx, Map                  */
/*                                                              */
/****************************************************************/
/****************************************************************/
/*                                                              */
/* Function name: CosetDecode                                   */
/* Parameters: C, u                                             */
/* Function description: Given a code C over Z4 of length n,    */
/*   and a vector u from the ambient space V=Z4^n or V2=Z2^2n,  */
/*   attempt to decode u with respect to C. If the decoding     */
/*   algorithm succeeds in computing a vector u' in C as the    */
/*   decoded version of u in V, then the function returns true, */
/*   u' and Phi(u'), where Phi is the Gray map. If the decoding */
/*   algorithm does not succeed in decoding u, then the function*/
/*   returns false, the zero vector in V and the zero in V2.    */
/*   Instead of a vector u, we can also decode a sequence Q     */
/*   of vectors in V or V2.                                     */
/* Input parameters description:                                */
/*   - C : Code over Z4                                         */
/*   - u : Received vector to be decoded                        */
/* Output parameters description:                               */
/*   - Boolean, true if u is decoded and false otherwise        */
/*   - Decoded vector over Z4 of u, or the zero vector          */
/*   - Decoded binary vector of u, or the zero vector           */
/*                                                              */
/* Signature: (<CodeLinRng> C, <ModTupRngElt> u)                */
/*               -> BoolElt, ModTupRngElt, ModTupFldElt         */
/* Signature: (<CodeLinRng> C, <ModTupFldElt> u)                */
/*               -> BoolElt, ModTupRngElt, ModTupFldElt         */
/*                                                              */
/* Signature: (<CodeLinRng> C, <[ModTupRngElt]> Q)              */
/*               -> [BoolElt], [ModTupRngElt], [ModTupFldElt]   */
/* Signature: (<CodeLinRng> C, <[ModTupFldElt]> Q)              */
/*               -> [BoolElt], [ModTupRngElt], [ModTupFldElt]   */
/*                                                              */
/****************************************************************/
/****************************************************************/
/*                                                              */
/* Function name: SyndromeDecode                                */
/* Parameters: C, u                                             */
/* Function description: Given a code C over Z4 of length n,    */
/*   and a vector u from the ambient space V=Z4^n or V2=Z2^2n,  */
/*   attempt to decode u with respect to C. The decoding        */
/*   algorithm always succeeds in computing a vector u' in C as */
/*   the decoded version of u in V, and the function returns    */
/*   true, u' and Phi(u'), where Phi is the Gray map. Although  */
/*   the function never returns false, the first output         */
/*   parameter true is given to be consistent with the other    */
/*   decoding functions.                                        */
/*   Instead of a vector u, we can also decode a sequence Q     */
/*   of vectors in V or V2.                                     */
/* Input parameters description:                                */
/*   - C : Code over Z4                                         */
/*   - u : Received vector to be decoded                        */
/* Output parameters description:                               */
/*   - Boolean, true if u is decoded and false otherwise        */
/*   - Decoded vector over Z4 of u, or the zero vector          */
/*   - Decoded binary vector of u, or the zero vector           */
/*                                                              */
/* Signature: (<CodeLinRng> C, <ModTupRngElt> u)                */
/*               -> BoolElt, ModTupRngElt, ModTupFldElt         */
/* Signature: (<CodeLinRng> C, <ModTupFldElt> u)                */
/*               -> BoolElt, ModTupRngElt, ModTupFldElt         */
/*                                                              */
/* Signature: (<CodeLinRng> C, <[ModTupRngElt]> Q)              */
/*               -> [BoolElt], [ModTupRngElt], [ModTupFldElt]   */
/* Signature: (<CodeLinRng> C, <[ModTupFldElt]> Q)              */
/*               -> [BoolElt], [ModTupRngElt], [ModTupFldElt]   */
/*                                                              */
/****************************************************************/
/****************************************************************/
/*                                                              */
/* Function name: LiftedDecode                                  */
/* Parameters: C, u                                             */
/* Function description: Given a code C over Z4 of length n,    */
/*   and a vector u from the ambient space V=Z4^n or V2=Z2^2n,  */
/*   attempt to decode u with respect to C. If the decoding     */
/*   algorithm succeeds in computing a vector u' in C as the    */
/*   decoded version of u in V, then the function returns true, */
/*   u' and Phi(u'), where Phi is the Gray map. If the decoding */
/*   algorithm does not succeed in decoding u, then the function*/
/*   returns false, the zero vector in V and the zero in V2 (in */
/*   the Euclidean case it may happen that u' is not in C).     */
/*   Instead of a vector u, we can also decode a sequence Q     */
/*   of vectors in V or V2.                                     */
/* Input parameters description:                                */
/*   - C : Code over Z4                                         */
/*   - u : Received vector to be decoded                        */
/* Output parameters description:                               */
/*   - Boolean, true if u is decoded and false otherwise        */
/*   - Decoded vector over Z4 of u, or the zero vector          */
/*   - Decoded binary vector of u, or the zero vector           */
/*                                                              */
/* Signature: (<CodeLinRng> C, <ModTupRngElt> u)                */
/*               -> BoolElt, ModTupRngElt, ModTupFldElt         */
/* Signature: (<CodeLinRng> C, <ModTupFldElt> u)                */
/*               -> BoolElt, ModTupRngElt, ModTupFldElt         */
/*                                                              */
/* Signature: (<CodeLinRng> C, <[ModTupRngElt]> Q)              */
/*               -> [BoolElt], [ModTupRngElt], [ModTupFldElt]   */
/* Signature: (<CodeLinRng> C, <[ModTupFldElt]> Q)              */
/*               -> [BoolElt], [ModTupRngElt], [ModTupFldElt]   */
/*                                                              */
/****************************************************************/
print "test 1: Trivial zero code over Z4
               #C = 1, length = 5";
C := ZeroCode(Integers(4),5);
R := RSpace(Integers(4),5);
V := VectorSpace(GF(2),10);
u := C!0;                        // u in C
v := R![1,0,0,0,3];              // v not in C
ubin := V!0;                     // ubin in Cbin
vbin := V![0,1,0,0,0,0,0,0,1,0]; // vbin not in Cbin
d := 0;

// Test Syndrome function
OutputSyndrome_u := Syndrome(u, C);
OutputSyndrome_ubin := Syndrome(ubin, C);
OutputSyndrome_v := Syndrome(v, C);
OutputSyndrome_vbin := Syndrome(vbin, C);
assert OutputSyndrome_u eq u;
assert OutputSyndrome_ubin eq u;
assert OutputSyndrome_v eq v;
assert OutputSyndrome_vbin eq v;

// Test CosetLeaders function
OutputCosetLeadersL, OutputCosetLeadersMap := CosetLeaders(C);
assert OutputCosetLeadersL eq SetToIndexedSet(Set(R));
assert OutputCosetLeadersMap(u) eq u;
assert OutputCosetLeadersMap(v) eq v;

// Test CosetDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := CosetDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq C!0;
assert OutputDecoded_ubin eq V!0;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := CosetDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq C!0;
assert OutputDecoded_vbin eq V!0;

OutputIsDecoded_ubin, OutputDecoded_u, OutputDecoded_ubin := CosetDecode(C, ubin);
assert OutputIsDecoded_ubin eq true;
assert OutputDecoded_u eq C!0;
assert OutputDecoded_ubin eq V!0;

OutputIsDecoded_vbin, OutputDecoded_v, OutputDecoded_vbin := CosetDecode(C, vbin);
assert OutputIsDecoded_vbin eq true;
assert OutputDecoded_v eq C!0;
assert OutputDecoded_vbin eq V!0;

// Test SyndromeDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := SyndromeDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq C!0;
assert OutputDecoded_ubin eq V!0;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := SyndromeDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq C!0;
assert OutputDecoded_vbin eq V!0;

OutputIsDecoded_ubin, OutputDecoded_u, OutputDecoded_ubin := SyndromeDecode(C, ubin);
assert OutputIsDecoded_ubin eq true;
assert OutputDecoded_u eq C!0;
assert OutputDecoded_ubin eq V!0;

OutputIsDecoded_vbin, OutputDecoded_v, OutputDecoded_vbin := SyndromeDecode(C, vbin);
assert OutputIsDecoded_vbin eq true;
assert OutputDecoded_v eq C!0;
assert OutputDecoded_vbin eq V!0;

// Test LiftedDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := LiftedDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq C!0;
assert OutputDecoded_ubin eq V!0;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := LiftedDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq C!0;
assert OutputDecoded_vbin eq V!0;

OutputIsDecoded_ubin, OutputDecoded_u, OutputDecoded_ubin := LiftedDecode(C, ubin);
assert OutputIsDecoded_ubin eq true;
assert OutputDecoded_u eq C!0;
assert OutputDecoded_ubin eq V!0;

OutputIsDecoded_vbin, OutputDecoded_v, OutputDecoded_vbin := LiftedDecode(C, vbin);
assert OutputIsDecoded_vbin eq true;
assert OutputDecoded_v eq C!0;
assert OutputDecoded_vbin eq V!0;

/****************************************************************/
print "test 2: Trivial universe code over Z4
               #C = 4096, lenght = 6";
C := UniverseCode(Integers(4),6);
R := RSpace(Integers(4),6);
V := VectorSpace(GF(2),12);
u := R![2,3,1,3,3,3];                // u in C
ubin := V![1,1,1,0,0,1,1,0,1,0,1,0]; // ubin in Cbin
d := 1;

// Test Syndrome function
OutputSyndrome_u := Syndrome(u, C);
OutputSyndrome_ubin := Syndrome(ubin, C);
assert OutputSyndrome_u eq Matrix(Integers(4),1,0,[]);
assert OutputSyndrome_ubin eq Matrix(Integers(4),1,0,[]);

// Test CosetLeaders function
OutputCosetLeadersL, OutputCosetLeadersMap := CosetLeaders(C);
assert OutputCosetLeadersL eq {@ C!0 @};
assert OutputCosetLeadersMap(Matrix(Integers(4),1,0,[])) eq C!0;

// Test CosetDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := CosetDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_ubin, OutputDecoded_u, OutputDecoded_ubin := CosetDecode(C, ubin);
assert OutputIsDecoded_ubin eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

// Test SyndromeDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := SyndromeDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_ubin, OutputDecoded_u, OutputDecoded_ubin := SyndromeDecode(C, ubin);
assert OutputIsDecoded_ubin eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

// Test LiftedDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := LiftedDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_ubin, OutputDecoded_u, OutputDecoded_ubin := LiftedDecode(C, ubin);
assert OutputIsDecoded_ubin eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

/****************************************************************/
print "test 3: Extended Hamming code over Z4
               #C = 2048, length = 8";
C := ExtendedPerfectCodeZ4(2,4);
R := RSpace(Integers(4),8);
V := VectorSpace(GF(2),16);
d := 4;   // error correcting capability t=1
u := R![3,0,3,0,3,0,3,0];  // u in C
v := R![2,0,3,0,3,0,3,0];  // v not in C, 1 error
w := R![1,0,3,0,3,0,3,0];  // w not in C, 2 errors
w2 := R![2,0,3,0,3,0,3,1]; // w2 not in C, 2 errors, not corrected by lifted decoding
ubin := V![1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0]; // ubin in Cbin
vbin := V![1,1,0,0,1,0,0,0,1,0,0,0,1,0,0,0]; // vbin not in Cbin, 1 error
wbin := V![0,1,0,0,1,0,0,0,1,0,0,0,1,0,0,0]; // wbin not in Cbin, 2 errors
w2bin := V![1,1,0,0,1,0,0,0,1,0,0,0,1,0,0,1];// w2bin not in Cbin, 2 errors

// Test InformationSpace function
OutputR, OutputV, Outputf, Outputfbin := InformationSpace(C);
assert OutputR eq RSpace(LinearCode(DiagonalMatrix(Integers(4),[2,1,1,1,1,1])));
assert OutputV eq VectorSpace(GF(2), 11);

// Test SyndromeSpace function
OutputRs, OutputVs := SyndromeSpace(C);
assert OutputRs eq RSpace(LinearCode(DiagonalMatrix(Integers(4),[2,1,1])));
assert OutputVs eq VectorSpace(GF(2), 5);

// Test Syndrome function
OutputSyndrome_u := Syndrome(u, C);
OutputSyndrome_ubin := Syndrome(ubin, C);
OutputSyndrome_v := Syndrome(v, C);
OutputSyndrome_vbin := Syndrome(vbin, C);
OutputSyndrome_w := Syndrome(w, C);
OutputSyndrome_wbin := Syndrome(wbin, C);
assert OutputSyndrome_u eq OutputRs!0;
assert OutputSyndrome_ubin eq OutputRs!0;
assert OutputSyndrome_v eq OutputRs![0,3,0];
assert OutputSyndrome_vbin eq OutputRs![0,3,0];
assert OutputSyndrome_w eq OutputRs![0,2,0];
assert OutputSyndrome_wbin eq OutputRs![0,2,0];

// Test CosetLeaders function
OutputCosetLeadersL, OutputCosetLeadersMap := CosetLeaders(C);
assert #OutputCosetLeadersL eq 32;
assert OutputCosetLeadersMap(OutputRs!0) eq C!0;
assert OutputCosetLeadersMap(OutputRs![0,3,0]) eq R![3,0,0,0,0,0,0,0];
assert OutputCosetLeadersMap(OutputRs![0,2,0]) eq R![0,1,0,3,0,0,0,0];

// Test CosetDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := CosetDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := CosetDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := CosetDecode(C, w);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![1,0,1,0,3,0,3,0];
assert OutputDecoded_wbin eq V![0,1,0,0,0,1,0,0,1,0,0,0,1,0,0,0];

OutputIsDecoded_ubin, OutputDecode_u, OutputDecoded_ubin := CosetDecode(C,ubin);
assert OutputIsDecoded_ubin eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_vbin, OutputDecode_v, OutputDecoded_vbin := CosetDecode(C,vbin);
assert OutputIsDecoded_vbin eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_wbin, OutputDecode_w, OutputDecoded_wbin := CosetDecode(C,wbin);
assert OutputIsDecoded_wbin eq true;
assert OutputDecoded_w eq R![1,0,1,0,3,0,3,0];
assert OutputDecoded_wbin eq V![0,1,0,0,0,1,0,0,1,0,0,0,1,0,0,0];

// Test SyndromeDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := SyndromeDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := SyndromeDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := SyndromeDecode(C, w);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![1,3,3,1,3,0,3,0];
assert OutputDecoded_wbin eq V![0,1,1,0,1,0,0,1,1,0,0,0,1,0,0,0];

OutputIsDecoded_ubin, OutputDecoded_u, OutputDecoded_ubin := SyndromeDecode(C, ubin);
assert OutputIsDecoded_ubin eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_vbin, OutputDecoded_v, OutputDecoded_vbin := SyndromeDecode(C, vbin);
assert OutputIsDecoded_vbin eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_wbin, OutputDecoded_w, OutputDecoded_wbin := SyndromeDecode(C, wbin);
assert OutputIsDecoded_wbin eq true;
assert OutputDecoded_w eq R![1,3,3,1,3,0,3,0];
assert OutputDecoded_wbin eq V![0,1,1,0,1,0,0,1,1,0,0,0,1,0,0,0];

// Test LiftedDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := LiftedDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := LiftedDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := LiftedDecode(C, w);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq u;
assert OutputDecoded_wbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := LiftedDecode(C, w2);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![1,0,3,0,3,3,3,1];;
assert OutputDecoded_wbin eq V![0,1,0,0,1,0,0,0,1,0,1,0,1,0,0,1];

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := LiftedDecode(C, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := LiftedDecode(C, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := LiftedDecode(C, wbin);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq u;
assert OutputDecoded_wbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := LiftedDecode(C, w2bin);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![1,0,3,0,3,3,3,1];;
assert OutputDecoded_wbin eq V![0,1,0,0,1,0,0,0,1,0,1,0,1,0,0,1];

/****************************************************************/
print "test 4: Hadamard code over Z4
               #C = 64, length = 16";
C := HadamardCodeZ4(3,5);
R := RSpace(Integers(4),16);
V := VectorSpace(GF(2),32);
d := 16;  // error correcting capability t=7
          // dK=16, mimimum weight of the kernel
u := R![1,0,3,2,0,3,2,1,3,2,1,0,2,1,0,3];  // u in C
v := R![1,0,3,3,3,2,0,1,3,2,1,0,2,1,0,2];  // v not in C, 6 errors, type 1^1 2^2 3^3
w := R![1,2,3,2,2,3,2,1,2,0,1,0,2,1,2,2];  // w not in C, 10 errors, type 1^0 2^4 3^2
w2 := R![1,0,3,2,0,3,2,1,3,2,2,1,3,3,2,1]; // w2 not in C, 9 errors, type 1^3 2^3 3^0
w3 := R![1,0,3,2,0,3,2,1,3,3,2,2,0,3,2,1]; // w2 not in C, 12 errors, type 1^2 2^5 3^0
// ubin in Cbin, not in Kernel
ubin := V![0,1,0,0,1,0,1,1,0,0,1,0,1,1,0,1,1,0,1,1,0,1,0,0,1,1,0,1,0,0,1,0];
// vbin not in Cbin, 5 errors  (u plus 5 errors, 6 <=t)
vbin := V![0,1,0,0,1,0,1,0,1,0,1,1,0,0,0,1,1,0,1,1,0,1,0,0,1,1,0,1,0,0,1,1];
// wbin not in Cbin, 10 errors (u plus 10 errors, t < 10 <= dK-1=15)
wbin := V![0,1,1,1,1,0,1,1,1,1,1,0,1,1,0,1,1,1,0,0,0,1,0,0,1,1,0,1,1,1,1,1];
// wbin not in Cbin, 9 errors (u plus 9 errors, t < 9 <= dK-1=15)
w2bin := V![0,1,0,0,1,0,1,1,0,0,1,0,1,1,0,1,1,0,1,1,1,1,0,1,1,0,1,0,1,1,0,1];
// wbin not in Cbin, 12 errors (u plus 12 errors, t < 12 <= dK-1=15)
w3bin := V![0,1,0,0,1,0,1,1,0,0,1,0,1,1,0,1,1,0,1,0,1,1,1,1,0,0,1,0,1,1,0,1];

// Test InformationSpace function
OutputR, OutputV, Outputf, Outputfbin := InformationSpace(C);
assert OutputR eq RSpace(LinearCode(DiagonalMatrix(Integers(4),[1,1,1])));
assert OutputV eq VectorSpace(GF(2), 6);

// Test SyndromeSpace function
OutputRs, OutputVs := SyndromeSpace(C);
assert OutputRs eq RSpace(LinearCode(DiagonalMatrix(Integers(4),[1^^13])));
assert OutputVs eq VectorSpace(GF(2), 26);

// Test Syndrome function
OutputSyndrome_u := Syndrome(u, C);
OutputSyndrome_ubin := Syndrome(ubin, C);
OutputSyndrome_v := Syndrome(v, C);
OutputSyndrome_vbin := Syndrome(vbin, C);
OutputSyndrome_w := Syndrome(w, C);
OutputSyndrome_wbin := Syndrome(wbin, C);
assert OutputSyndrome_u eq OutputRs!0;
assert OutputSyndrome_ubin eq OutputRs!0;
assert OutputSyndrome_v eq OutputRs![3,0,1,3,3,0,0,3,1,2,3,2,3];
assert OutputSyndrome_vbin eq OutputRs![3,0,1,3,3,0,0,3,1,2,3,2,3];
assert OutputSyndrome_w eq OutputRs![1,2,3,2,0,1,0,3,2,0,1,0,3];
assert OutputSyndrome_wbin eq OutputRs![1,2,3,2,0,1,0,3,2,0,1,0,3];

// Test CosetLeaders function     TOO SLOW, since there are 67108864 cosets
//OutputCosetLeadersL, OutputCosetLeadersMap := CosetLeaders(C);
//assert #OutputCosetLeadersL eq 67108864;
//assert OutputCosetLeadersMap(OutputRs!0) eq C!0;

// Test CosetDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := CosetDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := CosetDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := CosetDecode(C, w);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![2^^16];
assert OutputDecoded_wbin eq V![1^^32];

OutputIsDecoded_ubin, OutputDecode_u, OutputDecoded_ubin := CosetDecode(C,ubin);
assert OutputIsDecoded_ubin eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_vbin, OutputDecode_v, OutputDecoded_vbin := CosetDecode(C,vbin);
assert OutputIsDecoded_vbin eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_wbin, OutputDecode_w, OutputDecoded_wbin := CosetDecode(C,wbin);
assert OutputIsDecoded_wbin eq true;
assert OutputDecoded_w eq R![2^^16];
assert OutputDecoded_wbin eq V![1^^32];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := CosetDecode(C, [u,v,w]);
assert OutputIsDecoded eq [true, true, true];
assert OutputDecoded eq [u, u, R![2^^16]];
assert OutputDecodedBin eq [ubin, ubin, V![1^^32]];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := CosetDecode(C, [ubin,vbin,wbin]);
assert OutputIsDecoded eq [true, true, true];
assert OutputDecoded eq [u, u, R![2^^16]];
assert OutputDecodedBin eq [ubin, ubin, V![1^^32]];

// Test SyndromeDecode function   TOO SLOW, since there are 67108864 cosets

// Test LiftedDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := LiftedDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := LiftedDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := LiftedDecode(C, w2);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq u;
assert OutputDecoded_wbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := LiftedDecode(C, w3);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![1,0,3,2,2,1,0,3,3,2,1,0,0,3,2,1];
assert OutputDecoded_wbin eq V![0,1,0,0,1,0,1,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,0,0,0,1,0,1,1,0,1];

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := LiftedDecode(C, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := LiftedDecode(C, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := LiftedDecode(C, w2bin);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq u;
assert OutputDecoded_wbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := LiftedDecode(C, w3bin);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![1,0,3,2,2,1,0,3,3,2,1,0,0,3,2,1];
assert OutputDecoded_wbin eq V![0,1,0,0,1,0,1,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,0,0,0,1,0,1,1,0,1];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := LiftedDecode(C, [u,v,w,w2]);
assert OutputIsDecoded eq [true, true, true, true];
assert OutputDecoded eq [u, u, u, u];
assert OutputDecodedBin eq [ubin, ubin, ubin, ubin];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := LiftedDecode(C, [ubin,vbin,wbin,w2bin]);
assert OutputIsDecoded eq [true, true, true, true];
assert OutputDecoded eq [u, u, u, u];
assert OutputDecodedBin eq [ubin, ubin, ubin, ubin];

/****************************************************************/
print "test 5: Preparata code
               #C = 256, length = 8";
C := PreparataCode(3);
R := RSpace(Integers(4),8);
V := VectorSpace(GF(2),16);
d := 6;   // error correcting capability t=2
          // dK=8, mimimum weight of the kernel
u := R![1,1,3,3,1,3,1,3];                  // u in C
v := R![1,1,3,3,1,3,1,1];                  // v not in C, 2 errors
w := R![3,3,1,1,1,3,1,3];                  // w not in C, 8 errors
// ubin in Cbin, in Kernel
ubin := V![0,1,0,1,1,0,1,0,0,1,1,0,0,1,1,0];
// vbin not in Cbin, 2 errors  (u plus 2 errors, 2 <=t)
vbin := V![0,1,0,1,1,0,1,0,0,1,1,0,0,1,0,1];
// wbin not in Cbin, 5 errors (u plus 8 errors,  8 >= dK-1=7)
wbin := V![1,0,1,0,0,1,0,1,0,1,1,0,0,1,1,0];

// Test InformationSpace function
OutputR, OutputV, Outputf, Outputfbin := InformationSpace(C);
assert OutputR eq RSpace(LinearCode(DiagonalMatrix(Integers(4),[1,1,1,1])));
assert OutputV eq VectorSpace(GF(2), 8);

// Test SyndromeSpace function
OutputRs, OutputVs := SyndromeSpace(C);
assert OutputRs eq RSpace(LinearCode(DiagonalMatrix(Integers(4),[1,1,1,1])));
assert OutputVs eq VectorSpace(GF(2), 8);

// Test Syndrome function
OutputSyndrome_u := Syndrome(u, C);
OutputSyndrome_ubin := Syndrome(ubin, C);
OutputSyndrome_v := Syndrome(v, C);
OutputSyndrome_vbin := Syndrome(vbin, C);
OutputSyndrome_w := Syndrome(w, C);
OutputSyndrome_wbin := Syndrome(wbin, C);
assert OutputSyndrome_u eq OutputRs!0;
assert OutputSyndrome_ubin eq OutputRs!0;
assert OutputSyndrome_v eq OutputRs![2,2,0,2];
assert OutputSyndrome_vbin eq OutputRs![2,2,0,2];
assert OutputSyndrome_w eq OutputRs![2,2,2,2];
assert OutputSyndrome_wbin eq OutputRs![2,2,2,2];

// Test CosetLeaders function
OutputCosetLeadersL, OutputCosetLeadersMap := CosetLeaders(C);
assert #OutputCosetLeadersL eq 256;
assert OutputCosetLeadersMap(OutputRs!0) eq C!0;
assert OutputCosetLeadersMap(OutputRs![2,2,0,2]) eq R![0,0,0,0,0,0,0,2];
assert OutputCosetLeadersMap(OutputRs![2,2,2,2]) eq R![0,1,3,3,0,0,1,0];

// Test CosetDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := CosetDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := CosetDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := CosetDecode(C, w);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![3,3,3,1,1,3,1,1];
assert OutputDecoded_wbin eq V![1,0,1,0,1,0,0,1,0,1,1,0,0,1,0,1];

OutputIsDecoded_ubin, OutputDecode_u, OutputDecoded_ubin := CosetDecode(C,ubin);
assert OutputIsDecoded_ubin eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_vbin, OutputDecode_v, OutputDecoded_vbin := CosetDecode(C,vbin);
assert OutputIsDecoded_vbin eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_wbin, OutputDecode_w, OutputDecoded_wbin := CosetDecode(C,wbin);
assert OutputIsDecoded_wbin eq true;
assert OutputDecoded_w eq R![3,3,3,1,1,3,1,1];
assert OutputDecoded_wbin eq V![1,0,1,0,1,0,0,1,0,1,1,0,0,1,0,1];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := CosetDecode(C, [u,v,w]);
assert OutputIsDecoded eq [true, true, true];
assert OutputDecoded eq [u, u, R![3,3,3,1,1,3,1,1]];
assert OutputDecodedBin eq [ubin, ubin, V![1,0,1,0,1,0,0,1,0,1,1,0,0,1,0,1]];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := CosetDecode(C, [ubin,vbin,wbin]);
assert OutputIsDecoded eq [true, true, true];
assert OutputDecoded eq [u, u, R![3,3,3,1,1,3,1,1]];
assert OutputDecodedBin eq [ubin, ubin, V![1,0,1,0,1,0,0,1,0,1,1,0,0,1,0,1]];

// Test SyndromeDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := SyndromeDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := SyndromeDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := SyndromeDecode(C, w);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![3,2,2,2,1,3,0,3];
assert OutputDecoded_wbin eq V![1,0,1,1,1,1,1,1,0,1,1,0,0,0,1,0];

OutputIsDecoded_ubin, OutputDecoded_u, OutputDecoded_ubin := SyndromeDecode(C, ubin);
assert OutputIsDecoded_ubin eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_vbin, OutputDecoded_v, OutputDecoded_vbin := SyndromeDecode(C, vbin);
assert OutputIsDecoded_vbin eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_wbin, OutputDecoded_w, OutputDecoded_wbin := SyndromeDecode(C, wbin);
assert OutputIsDecoded_wbin eq true;
assert OutputDecoded_w eq R![3,2,2,2,1,3,0,3];
assert OutputDecoded_wbin eq V![1,0,1,1,1,1,1,1,0,1,1,0,0,0,1,0];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := SyndromeDecode(C, [u,v,w]);
assert OutputIsDecoded eq [true, true, true];
assert OutputDecoded eq [u, u, R![3,2,2,2,1,3,0,3]];
assert OutputDecodedBin eq [ubin, ubin, V![1,0,1,1,1,1,1,1,0,1,1,0,0,0,1,0]];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := SyndromeDecode(C, [ubin,vbin,wbin]);
assert OutputIsDecoded eq [true, true, true];
assert OutputDecoded eq [u, u, R![3,2,2,2,1,3,0,3]];
assert OutputDecodedBin eq [ubin, ubin, V![1,0,1,1,1,1,1,1,0,1,1,0,0,0,1,0]];

// Test LiftedDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := LiftedDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := LiftedDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := LiftedDecode(C, w);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![1,3,1,1,1,3,3,3];
assert OutputDecoded_wbin eq V![0,1,1,0,0,1,0,1,0,1,1,0,1,0,1,0];

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := LiftedDecode(C, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := LiftedDecode(C, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := LiftedDecode(C, wbin);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![1,3,1,1,1,3,3,3];
assert OutputDecoded_wbin eq V![0,1,1,0,0,1,0,1,0,1,1,0,1,0,1,0];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := LiftedDecode(C, [u,v,w]);
assert OutputIsDecoded eq [true, true, true];
assert OutputDecoded eq [u, u, R![1,3,1,1,1,3,3,3]];
assert OutputDecodedBin eq [ubin, ubin, V![0,1,1,0,0,1,0,1,0,1,1,0,1,0,1,0]];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := LiftedDecode(C, [ubin,vbin,wbin]);
assert OutputIsDecoded eq [true, true, true];
assert OutputDecoded eq [u, u, R![1,3,1,1,1,3,3,3]];
assert OutputDecodedBin eq [ubin, ubin, V![0,1,1,0,0,1,0,1,0,1,1,0,1,0,1,0]];

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
d := 16;   // error correcting capability t=7
           // dK=16, mimimum weight of the kernel
// u in C
u := R![0,2,0,0,0,2,0,0,2,2,0,2,0,2,2,2];
// v not in C, 2 binary errors in quaternary positions {2, 8};
v := R![0,1,0,0,0,2,0,3,2,2,0,2,0,2,2,2];
// w not in C, 7 binary errors in Z4 positions {2, 4, 5, 6, 8};
w := R![0,1,0,2,2,1,0,3,2,2,0,2,0,2,2,2];
// ubin in Cbin
ubin := V![0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,1,1,1,1,0,0,1,1,0,0,1,1,1,1,1,1];
// vbin not in Cbin, 2 errors in positions {3, 15}
vbin := V![0,0,0,1,0,0,0,0,0,0,1,1,0,0,1,0,1,1,1,1,0,0,1,1,0,0,1,1,1,1,1,1];
// wbin not in Cbin, 7 errors in positions {3, 7, 8, 9, 10, 11, 15}
wbin := V![0,0,0,1,0,0,1,1,1,1,0,1,0,0,1,0,1,1,1,1,0,0,1,1,0,0,1,1,1,1,1,1];

// Test InformationSpace function
OutputR, OutputV, Outputf, Outputfbin := InformationSpace(C);
assert OutputR eq RSpace(LinearCode(DiagonalMatrix(Integers(4),[2,2,2,2,2])));
assert OutputV eq VectorSpace(GF(2), 5);

// Test SyndromeSpace function
OutputRs, OutputVs := SyndromeSpace(C);
assert OutputRs eq RSpace(LinearCode(DiagonalMatrix(Integers(4),[2^^5] cat [1^^11])));
assert OutputVs eq VectorSpace(GF(2), 27);

// Test Syndrome function
OutputSyndrome_u := Syndrome(u, C);
OutputSyndrome_ubin := Syndrome(ubin, C);
OutputSyndrome_v := Syndrome(v, C);
OutputSyndrome_vbin := Syndrome(vbin, C);
OutputSyndrome_w := Syndrome(w, C);
OutputSyndrome_wbin := Syndrome(wbin, C);
assert OutputSyndrome_u eq OutputRs!0;
assert OutputSyndrome_ubin eq OutputRs!0;
assert OutputSyndrome_v eq OutputRs![0,0,0,0,0,0,3,0,0,0,0,0,3,0,0,0];
assert OutputSyndrome_vbin eq OutputRs![0,0,0,0,0,0,3,0,0,0,0,0,3,0,0,0];
assert OutputSyndrome_w eq OutputRs![0,0,0,0,0,0,3,0,2,2,3,0,3,0,0,0];
assert OutputSyndrome_wbin eq OutputRs![0,0,0,0,0,0,3,0,2,2,3,0,3,0,0,0];

// Test CosetLeaders function     TOO SLOW, since there are 134217728 cosets
//OutputCosetLeadersL, OutputCosetLeadersMap := CosetLeaders(C);
//assert #OutputCosetLeadersL eq 134217728;
//assert OutputCosetLeadersMap(OutputRs!0) eq C!0;

// Test CosetDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := CosetDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := CosetDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := CosetDecode(C, w);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq u;
assert OutputDecoded_wbin eq ubin;

OutputIsDecoded_ubin, OutputDecode_u, OutputDecoded_ubin := CosetDecode(C,ubin);
assert OutputIsDecoded_ubin eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_vbin, OutputDecode_v, OutputDecoded_vbin := CosetDecode(C,vbin);
assert OutputIsDecoded_vbin eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_wbin, OutputDecode_w, OutputDecoded_wbin := CosetDecode(C,wbin);
assert OutputIsDecoded_wbin eq true;
assert OutputDecoded_w eq u;
assert OutputDecoded_wbin eq ubin;

OutputIsDecoded, OutputDecoded, OutputDecodedBin := CosetDecode(C, [u,v,w]);
assert OutputIsDecoded eq [true, true, true];
assert OutputDecoded eq [u, u, u];
assert OutputDecodedBin eq [ubin, ubin, ubin];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := CosetDecode(C, [ubin,vbin,wbin]);
assert OutputIsDecoded eq [true, true, true];
assert OutputDecoded eq [u, u, u];
assert OutputDecodedBin eq [ubin, ubin, ubin];

// Test SyndromeDecode function   TOO SLOW, since there are 134217728 cosets

// Test LiftedDecode function
OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := LiftedDecode(C, u);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := LiftedDecode(C, v);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := LiftedDecode(C, w);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![2,2,0,2,2,0,0,2,0,2,0,0,0,0,2,2];
assert OutputDecoded_wbin eq V![1,1,1,1,0,0,1,1,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,1,1,1,1];

OutputIsDecoded_u, OutputDecoded_u, OutputDecoded_ubin := LiftedDecode(C, ubin);
assert OutputIsDecoded_u eq true;
assert OutputDecoded_u eq u;
assert OutputDecoded_ubin eq ubin;

OutputIsDecoded_v, OutputDecoded_v, OutputDecoded_vbin := LiftedDecode(C, vbin);
assert OutputIsDecoded_v eq true;
assert OutputDecoded_v eq u;
assert OutputDecoded_vbin eq ubin;

OutputIsDecoded_w, OutputDecoded_w, OutputDecoded_wbin := LiftedDecode(C, wbin);
assert OutputIsDecoded_w eq true;
assert OutputDecoded_w eq R![2,2,0,2,2,0,0,2,0,2,0,0,0,0,2,2];
assert OutputDecoded_wbin eq
            V![1,1,1,1,0,0,1,1,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,1,1,1,1];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := LiftedDecode(C, [u,v,w]);
assert OutputIsDecoded eq [true, true, true];
assert OutputDecoded eq [u, u, R![2,2,0,2,2,0,0,2,0,2,0,0,0,0,2,2]];
assert OutputDecodedBin eq [ubin, ubin,
           V![1,1,1,1,0,0,1,1,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,1,1,1,1]];

OutputIsDecoded, OutputDecoded, OutputDecodedBin := LiftedDecode(C, [ubin,vbin,wbin]);
assert OutputIsDecoded eq [true, true, true];
assert OutputDecoded eq [u, u, R![2,2,0,2,2,0,0,2,0,2,0,0,0,0,2,2]];
assert OutputDecodedBin eq [ubin, ubin,
          V![1,1,1,1,0,0,1,1,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,1,1,1,1]];
