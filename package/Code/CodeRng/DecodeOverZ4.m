///////////////////////////////////////////////////////////////////////////////
/////////       Copyright 2015-2016 Roland Barrolleta, Jaume Pujol      ///////
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
/* Project name: Codes over Z4 in MAGMA                     */
/* File name: DecodeOverZ4.m                                */
/*                                                          */
/* Comment: Package developed within the CCSG group.        */
/*                                                          */
/* Authors: R. D. Barrolleta, J. Pujol and M. Villanueva	*/
/*                                                          */
/* Revision version and last date: v1.1   28-09-2015        */
/*                                 v1.2   05-10-2015        */
/*                                 v1.3   18-12-2015        */
/*                                 v1.4   30-12-2015        */
/*                                 v1.5   06-02-2016        */
/*                                 v1.6   11-05-2016        */ 
/*                                                          */
/************************************************************/
//Uncomment freeze when package finished
freeze;

import "z4_uab.m": DoublePerm;

intrinsic DecodeOverZ4_version() -> SeqEnum
{Return the current version of this package.}
    version := [1,6];
    return version;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
declare verbose IsPDSetFlag, 3;
///////////////////////////////////////////////////////////////////////////////

/******************************************************************
	GLOBAL VARIABLES
*******************************************************************/		
Z4 := Integers(4);
Z2 := Integers(2);
Z := IntegerRing();

zero_Code := func<C | PseudoDimension(C) eq 0>;

//Maximum number of elements in a sequence for the current MAGMA distribution
//This number can be changed if your distribution allows longer sequences  
MAXSEQLENGTH := 2^28;

//Maximum time to try to find an s-PD-set for the Hadamard code over Z4
//by using the nondeterministic method when gamma<>0
MAXTIME := 5.0;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////                 THE INFORMATION SPACE FUNCTIONS                 ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/****************************************************************/
/*                                                              */  
/* Function name: DiagonalizeDeltaMatrix                        */
/* Parameters: M, delta                                         */
/* Function description: Given a generator matrix M of a code   */
/*   over Z4 of type 2^gamma 4^delta having gamma+delta rows,   */
/*   and the integer number delta, return a new permutation-    */
/*   equivalent matrix such that it contains the identity       */
/*   matrix in the last delta coordinates, and the permutation  */
/*   used to obtain the new matrix.                             */
/*                                                              */
/****************************************************************/
function DiagonalizeDeltaMatrix(M, delta)
    ncols := Ncols(M);
    mrows := Nrows(M);
    nc := ncols;
    mc := mrows;
    colsSym := Sym(ncols);
    P := colsSym!1;

    for j := ncols to ncols - delta + 1 by -1 do
        if (IsZero(M[mc][nc])) or (M[mc][nc] eq 2) then
            m2 := mc;
            while (m2 gt mrows - delta) and ((IsZero(M[m2][nc])) or (M[m2][nc] eq 2)) do
     	        m2 := m2 - 1;
            end while;
            if (m2 gt mrows - delta) then
	            SwapRows(~M, mc, m2);
            else
	            n2 := nc;
                while ((IsZero(M[mc][n2])) or (M[mc][n2] eq 2)) and (n2 gt 0) do
		            n2 := n2 - 1;
	            end while;
	            if (n2 gt 0) and (n2 ne nc) then
		            SwapColumns(~M, nc, n2);
					P := colsSym!(nc, n2)*P;
                end if;
            end if;
        end if;

        if (M[mc][nc] eq 3) then
	        M[mc] := -M[mc];
        end if;
        for i := mc - 1 to 1 by -1 do
            if (not IsZero(M[i][nc])) then
   	            M[i] := M[i] - M[mc]*M[i][nc];
            end if;
        end for;
        for i := mc + 1 to mrows do
            if (not IsZero(M[i][nc])) then
	            M[i] := M[i] - M[mc]*M[i][nc];
            end if;
        end for;

        mc := mc - 1;
        nc := nc - 1;
    end for;
    
    return M, P;
end function;

/****************************************************************/
/*                                                              */  
/* Function name: DiagonalizeGammaMatrix                        */
/* Parameters: M, gamma, delta                                  */
/* Function description: Given a generator matrix M of a code   */
/*   over Z4 of type 2^gamma 4^delta having gamma+delta rows    */
/*   and the identity matrix of size delta in the last delta    */
/*   coordinates, and the integer numbers gamma and delta,      */
/*   return a new permutation-equivalent matrix such that it    */
/*   contains the identity matrix in the [n-delta-gamma+1,...,  */
/*   n-delta] coordinate possitions, and the permutation used   */
/*   to obtain the new matrix.                                  */
/*                                                              */
/****************************************************************/
function DiagonalizeGammaMatrix(M, gamma, delta)
    ncols := Ncols(M);
    mrows := Nrows(M);
    nc := ncols - delta;
    mc := mrows - delta;
    colsSym := Sym(ncols);
    P := colsSym!1;

    for j := nc to nc - gamma + 1 by -1 do
        if (IsZero(M[mc][nc])) then
            m2 := mc;
            while (m2 gt 0) and (IsZero(M[m2][nc])) do
     	        m2 := m2 - 1;
            end while;
            if (not IsZero(m2)) then
	            SwapRows(~M, mc, m2);
            else
	            n2 := nc;
                while (IsZero(M[mc][n2])) and (n2 gt 0) do
		            n2 := n2 - 1;
	            end while;
	            if (n2 gt 0) and (n2 ne nc) then
		            SwapColumns(~M, nc, n2);
					P := colsSym!(nc, n2)*P;
                end if;
            end if;
        end if;

        for i := mc - 1 to 1 by -1 do
            if (not IsZero(M[i][nc])) then
   	            M[i] := M[i] - M[mc];
            end if;
        end for;
        for i := mc + 1 to gamma do
            if (not IsZero(M[i][nc])) then
	            M[i] := M[i] - M[mc];
            end if;
        end for;
        for i := gamma+1 to mrows do
            if (not IsZero(M[i][nc])) and (not IsOne(M[i][nc])) then
	            M[i] := M[i] - M[mc];
            end if;
        end for;

        mc := mc - 1;
        nc := nc - 1;        
    end for;
    
    return M, P;
end function;

/****************************************************************/
/*                                                              */  
/* Function name: Z4StandardForm                                */
/* Parameters: C                                                */
/* Function description: Given a code C over Z4, return a       */
/*   permutation-equivalent code S in standard form, together   */
/*   with the corresponding isomorphism from C onto S, the      */
/*   generator matrix of S in standard form, and the permutation*/
/*   of coordinates used to define the isomorphism.             */
/* Input parameters description:                                */
/*   - C : Code over Z4                                         */
/* Output parameters description:                               */
/*   - Code over Z4 in standard form                            */
/*   - Isomorphism from C onto S                                */
/*   - Generator matrix of S                                    */
/*   - Permutation of coordinates that defines the isomorphism  */
/*                                                              */
/* Signature: (<CodeLinRng> C) -> CodeLinRng, Map,              */
/*                                ModMatRngElt, GrpPermElt      */
/*                                                              */
/****************************************************************/
intrinsic Z4StandardForm(C::CodeLinRng) -> CodeLinRng, Map, ModMatRngElt, GrpPermElt
{
Given a code C over Z4, return a permutation-equivalent code S in standard form, 
together with the corresponding isomorphism from C onto S, the generator matrix 
of S in standard form, and the permutation of coordinates used to define 
the isomorphism.
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";

    M, gamma, delta := MinRowsGeneratorMatrix(C); 
    
    if IsZero(delta) then 
        Md := M;
        Pd := Sym(Length(C))!1;
    else 
        Md, Pd := DiagonalizeDeltaMatrix(M, delta);        
    end if; 
    
    if IsZero(gamma) then  
        Mdg := Md;
        Pg := Sym(Length(C))!1;
    else
        Mdg, Pg := DiagonalizeGammaMatrix(Md, gamma, delta);        
    end if; 
        
    p := Pd * Pg;
	S := LinearCode(Mdg);
	f := map<C -> S | v :-> v^p, w :-> w^(p^-1)>;

	return S, f, Mdg, p;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////                 THE INFORMATION SPACE FUNCTIONS                 ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/****************************************************************/
/*                                                              */  
/* Function name: GrayImageInverse                              */
/* Parameters: v, gamma, delta                                  */
/* Function description: Given a binary vector v of length      */
/*   gamma+delta with delta even, and two integer numbers gamma */
/*   and delta, return a vector of length gamma+delta/2 over Z, */
/*   where the first gamma coordinates are the same and the     */
/*   last delta coordinates are the inverse of the Gray map.    */
/*                                                              */
/****************************************************************/
GrayImageInverse := function(v, gamma, delta)
    Z4GrayInvSeq := [0, 3, 1, 2];
    return Vector([Z!v[i] : i in [1..gamma]] cat [Z4GrayInvSeq[Z!v[x - 1] + 
           2*Z!v[x] + 1 where x is 2*i+gamma] : i in [1..delta]]);
end function;

/****************************************************************/
/*                                                              */  
/* Function name: GrayImageFirstCoordinate                      */
/* Parameters: v                                                */
/* Function description: Given a vector v over Z4, return       */
/*   a binary vector with the first coordinates of the Gray     */
/*   map image of each quaternary coordinate.                   */
/*   The first coordinates of the Gray map image of 0,1,2,3:    */
/*   0 -> 00, 1 -> 01, 2 -> 11, 3 -> 10,  are  0,0,1,1.         */            
/*                                                              */
/****************************************************************/
GrayImageFirstCoordinate := function(v)
    Z4GraySeq := [0, 0, 1, 1];
    return Vector(GF(2),[Z4GraySeq[Z!v[i] + 1] : i in [1..Degree(v)]]);
end function;

/****************************************************************/
/*                                                              */  
/* Function name: MultiplyByG                                   */
/* Parameters: v, gamma, G                                      */
/* Function description: Given a vector v over Z4, an integer   */
/*   number gamma and a generator matrix G of a code over Z4 of */
/*   type 2^gamma 4^delta with gamma+delta rows, where the      */
/*   first gamma are of order two and the last delta are of     */
/*   order four, return the product v*G.                        */
/*   The first gamma coordinates of v belong to {0,2}.          */
/*   Note that before multipling by G, it is necessary to       */
/*   replace {0,2} with {0,1} in the first gamma coordinates.   */ 
/*                                                              */
/****************************************************************/
MultiplyByG := function(v, gamma, G)
    for i in [1..gamma] do
        if v[i] eq 2 then v[i] := 1; end if;
    end for;
    return v*G;
end function;

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
intrinsic InformationSpace(C::CodeLinRng) -> ModTupRng, ModTupFld, Map, Map
{
Given a code C over Z4 of length n and type 2^gamma 4^delta, return the 
Z4-submodule of Z4^(gamma+delta) isomorphic to Z2^gamma x Z4^delta such that
the first gamma coordinates are of order two, that is, the space of information 
vectors for C. The function also returns the (gamma+2*delta)-dimensional binary 
vector space, which is the space of information vectors for the corresponding 
binary code Cbin=Phi(C), where Phi is the Gray map. Finally, for the encoding 
process, it also returns the corresponding isomorphisms f and fbin from these 
spaces of information vectors onto C and Cbin, respectively. 
}  
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require not(zero_Code(C)): "Code cannot be the zero code";
    
    G, gamma, delta  := MinRowsGeneratorMatrix(C);

    diagonal := [2 : i in [1..gamma]] cat [1 : i in [1..delta]];
    InfCode := LinearCode(DiagonalMatrix(Z4, diagonal));
    InfRSpace := RSpace(InfCode);  
    InfVSpace := VectorSpace(GF(2), gamma+2*delta); 
    V := VectorSpace(GF(2), 2*Length(C));

    grayMap := GrayMap(C);
    grayMapInfCode := GrayMap(InfCode); 
    
    encodingZ4 := map<InfRSpace -> C | x :-> MultiplyByG(x, gamma, G)>;
    encodingZ2 := map<InfVSpace -> V | 
        x :-> grayMap(GrayImageInverse(x, gamma, delta)*G) >;

    return InfRSpace, InfVSpace, encodingZ4, encodingZ2;

end intrinsic;

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
intrinsic InformationSet(C::CodeLinRng) -> SeqEnum[RngIntElt], SeqEnum[RngIntElt]
{
Given a code C over Z4 of length n and type 2^gamma 4^delta, return an information 
set I=[i_1,...,i_(gamma+delta)] in [1,...,n] for C such that the code C punctured 
on [1,...,n] minus [i_(gamma+1),..., i_(gamma+delta)] is of type 4^delta, and 
the corresponding information set Phi(I)=[2*i_1-1,..., 2*i_gamma-1, 2*i_(gamma+1)-1, 
2*i_(gamma+1),..., 2*i_(gamma+delta)-1, 2*i_(gamma+delta)] in [1,...,2*n] for the 
binary code Cbin=Phi(C), where Phi is the Gray map. The information sets I and 
Phi(I) are returned as a sequence of gamma+delta and gamma+2*delta integers, 
giving the coordinate positions that correspond to the information set of C 
and Cbin, respectively.

An information set I for C is an ordered set of gamma+delta coordinate positions 
such that |C^I|=2^gamma 4^delta, where C^I=[v^I : v in C] and v^I is the vector 
v restricted to the I coordinates. An information set J for Cbin is an ordered 
set of gamma+2*delta coordinate positions such that |C^J_bin|=2^(gamma+2*delta).
}
   require (BaseRing(C) eq Z4): "Code must be over Z4";
   require not(zero_Code(C)): "Code cannot be the zero code";

   n := Length(C);
   _, gamma, delta  := MinRowsGeneratorMatrix(C);
   _, _, _, perm := Z4StandardForm(C);
   permInv := perm^(-1);

   InfSetZ4_gamma := [i^permInv : i in [n-(gamma+delta)+1..n-delta]];   
   InfSetZ4_delta := [i^permInv : i in [n-delta+1..n]];

   InfSetZ2_gamma := [2*i-1 : i in InfSetZ4_gamma];
   InfSetZ2_delta := &cat[ [2*i-1, 2*i] : i in InfSetZ4_delta];


   return InfSetZ4_gamma cat InfSetZ4_delta,  InfSetZ2_gamma cat InfSetZ2_delta;

end intrinsic;

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
intrinsic IsInformationSet(C::CodeLinRng, I::[RngIntElt]) -> BoolElt, BoolElt
{
Given a code C over Z4 of length n and type 2^gamma 4^delta and a sequence 
I in [1,...,n] or I in [1,...,2*n], return true if and only if I in [1,...,n] 
is an information set for C. This function also returns another boolean, which 
is true if an only if I in [1,...,2*n] is an information set for the corresponding 
binary code Cbin=Phi(C), where Phi is the Gray map.

An information set I for C is an ordered set of gamma+delta coordinate positions 
such that |C^I|=2^gamma 4^delta, where C^I=[v^I : v in C] and v^I is the vector 
v restricted to the I coordinates. An information set J for Cbin is an ordered 
set of gamma+2*delta coordinate positions such that |C^J_bin|=2^(gamma+2*delta).         
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require not(zero_Code(C)): "Code cannot be the zero code";
    I := Set(I);  // Eliminate repeated coordinate positions in I
    k := #I;
    require (k ge 1): "Argument 2 cannot be an empty sequence";
    n := Length(C);
    nbin := 2*n;
    maxI := Max(I);
    require (Min(I) ge 1) and (maxI le nbin): 
          "Argument 2 should be a subset of", [1..n], "or a subset of", [1..nbin];

    _, gamma, delta := MinRowsGeneratorMatrix(C);

    // Check whether I is an information set for C or not
    if (maxI le n) and ((gamma + delta) eq k) then
        checkSet := {1..n} diff I;
        _, gammaCp, deltaCp := MinRowsGeneratorMatrix(PunctureCode(C, checkSet));
        isInfSetZ4 := (gamma eq gammaCp) and (delta eq deltaCp);
    else
        isInfSetZ4 := false;
    end if;
    
    // Check whether I is an information set for Cbin or not
    if (gamma + 2*delta) eq k then 
        _, kernel := KernelZ2CodeZ4(C);
        checkSet := {1..nbin} diff I;
        punctureKernel := PunctureCode(kernel, checkSet);        
        if Dimension(kernel) eq Dimension(punctureKernel) then
            _, cosetRep := KernelCosetRepresentatives(C); 
            H := Transpose(ParityCheckMatrix(punctureKernel));  
            V := VectorSpace(GF(2), k);
            cosetSyndromes := [];
            isInfSetZ2 := true;
            Isorted := Sort(Setseq(I));
            for j := 1 to #cosetRep do
			    punctureCosetRep := V![cosetRep[j][i] : i in Isorted]; 
                syndrome := punctureCosetRep * H; 
                if syndrome in cosetSyndromes then 
                    isInfSetZ2 := false;
                    break;
                else
                    Append(~cosetSyndromes, syndrome);
                end if;
		    end for; 
        else
            isInfSetZ2 := false;
        end if; 
    else
        isInfSetZ2 := false;
    end if;

    return isInfSetZ4, isInfSetZ2;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////                 THE SYNDROME SPACE FUNCTIONS	                ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

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
intrinsic SyndromeSpace(C::CodeLinRng) -> ModTupRng, ModTupFld
{
Given a code C over Z4 of length n and type 2^gamma 4^delta, return the 
Z4-submodule of Z4^(n-delta) isomorphic to Z2^gamma x Z4^(n-gamma-delta)
such that the first gamma coordinates are of order two, that is, the space of 
syndrome vectors for C. The function also returns the (2*n-2*delta-gamma)-
dimensional binary vector space, which is the space of syndrome vectors 
for the corresponding binary code Cbin=Phi(C), where Phi is the Gray map. 
Note that these spaces are computed by using the function 
InformationSpace(C) applied to the dual code of C, given by function Dual(C).
}  
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require (#C ne 4^Length(C)): "Code cannot be the universe code";

    InfRSpace, InfVSpace := InformationSpace(Dual(C));
    return InfRSpace, InfVSpace;

end intrinsic;

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
intrinsic Syndrome(u::ModTupRngElt, C::CodeLinRng) -> ModTupRngElt
{
Given a code C over Z4 of length n and type 2^gamma 4^delta, and a vector u 
from the ambient space V=Z4^n or V2=Z2^(2*n), construct the syndrome of u relative 
to the code C. This will be an element of the syndrome space of C, considered 
as the Z4-submodule of Z4^(n-delta) isomorphic to Z2^gamma x Z4^(n-gamma-delta) 
such that the first gamma coordinates are of order two.
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require (BaseRing(u) eq Z4): "Argument 1 must be a vector over Z4";
    n := Length(C);
    require (Degree(u) eq n): "Argument 1 must be of length", n;

    H := MinRowsGeneratorMatrix(Dual(C));

    return u * Transpose(H);

end intrinsic;

/****************************************************************/
intrinsic Syndrome(u::ModTupFldElt, C::CodeLinRng) -> ModTupRngElt
{
Given a code C over Z4 of length n and type 2^gamma 4^delta, and a vector u 
from the ambient space V=Z4^n or V2=Z2^(2*n), construct the syndrome of u relative 
to the code C. This will be an element of the syndrome space of C, considered 
as the Z4-submodule of Z4^(n-delta) isomorphic to Z2^gamma x Z4^(n-gamma-delta) 
such that the first gamma coordinates are of order two.
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require (BaseRing(u) eq GF(2)): "Argument 1 must be a vector over GF(2)";
    n := Length(C);
    nbin := 2*n;
    require (Degree(u) eq nbin): "Argument 1 must be of length", nbin;

    grayMap := GrayMap(UniverseCode(Z4, n));
    H := MinRowsGeneratorMatrix(Dual(C));
    
    return u@@grayMap*Transpose(H);

end intrinsic;

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
intrinsic CosetLeaders(C::CodeLinRng) -> SetIndx, Map
{
Given a code C over Z4 of length n, with ambient space V=Z4^n, return a set of 
coset leaders (vectors of minimal Lee weight in their cosets) for C in V as an 
indexed set of vectors from V. This function also returns a map from the syndrome 
space of C into the coset leaders (mapping a syndrome into its corresponding 
coset leader). Note that this function is only applicable when V and C are small.
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    n := Length(C);
    totalNumSyndromes := (4^n) / #C;
    require (totalNumSyndromes le MAXSEQLENGTH): "Code has too many cosets";	

    nbin := 2*n; 
    grayMap := GrayMap(UniverseCode(Z4, n));     
    V := UniverseCode(GF(2), nbin);
	
    // Sequences that will have all syndromes and coset leaders  
    H := Transpose(MinRowsGeneratorMatrix(Dual(C)));
    allSyndromes := [ C!0 * H ];
    allCosetLeaders := {@ C!0 @};

    errorCapability := Floor((MinimumLeeDistance(C)-1)/2);
    for i in [1..errorCapability] do

        // All binary vectors of weight i
        vectorsWeight_i := Setseq(Words(V,i));
        numVectorsWeight_i := #vectorsWeight_i;	
		
        // Compute all syndromes up to the error-correcting capability
        for j in [1..numVectorsWeight_i] do
            leaderZ4 := vectorsWeight_i[j]@@grayMap;
            s := leaderZ4 * H;
            Append(~allSyndromes, s);
            Include(~allCosetLeaders, leaderZ4);
        end for;
        
    end for;

    i := errorCapability +1;
    while ((#allSyndromes lt totalNumSyndromes) and (i le nbin)) do

        // All binary vectors of weight i
        vectorsWeight_i := Setseq(Words(V,i));
        numVectorsWeight_i := #vectorsWeight_i;

        // Compute the new sindromes from the leaders of weight i
        j := 1;
        while ((j le numVectorsWeight_i) and (#allSyndromes lt totalNumSyndromes)) do
            leaderZ4 := vectorsWeight_i[j]@@grayMap;
            s := leaderZ4 * H;
            if (s notin allSyndromes) then
                Append(~allSyndromes, s);
                Include(~allCosetLeaders, leaderZ4);
            end if;
            j := j + 1;
        end while;
        
        i := i + 1;
    end while;

    mapSyndromeCosets := map<allSyndromes -> allCosetLeaders | 
                                  x :-> allCosetLeaders[Position(allSyndromes, x)] >; 

    return allCosetLeaders, mapSyndromeCosets;

end intrinsic;    

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////                 COSET DECODE FUNCTIONS                          ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/****************************************************************/
/*                                                              */
/* Function name: CosetDecodeAlg                                */
/* Parameters: kernel, cosetRep, d, u                           */
/* Function description: Given the binary kernel and the coset  */
/*   representatives of a binary code Cbin=Phi(C), where C is a */
/*   code over Z4 of length n, the minimum Lee distance of C,   */
/*   and a binary vector u from the ambient space V2=Z2^(2n),   */
/*   attempt to decode u with respect to Cbin. If the decoding  */
/*   algorithm succeeds in computing a vector u' in Cbin as the */
/*   decoded version of u in V2, then the function returns true */
/*   and u'. If the decoding algorithm does not succeed in      */
/*   decoding u, then the function returns false and the zero   */
/*   vector in V2.                                              */
/*   See below the description of the intrinsic CosetDecode     */
/*   for more details.                                          */
/*                                                              */
/****************************************************************/
CosetDecodeAlg := function(kernel, cosetRep, d, u : minWeightKernel := -1)

    if IsEmpty(cosetRep) then
        // Decode binary linear codes 
        if u in kernel then
            return  true, u;
        end if;
        
        // Compute the minimum word of the extend coset Cu = kernel U (kernel+u)
        Cu := LinearCode(VerticalJoin(GeneratorMatrix(kernel), u));
        minCosetWord := MinimumWord(Cu);
        // Check whether the minCosetWord can be in kernel or not
        if Weight(minCosetWord) lt d then
            return true, u + minCosetWord;
        else  
            return false, kernel!0;
        end if;
    else                                
        // Decode binary nonlinear codes 
        minWord := u;
        minWeight := Weight(u);
    
        G := GeneratorMatrix(kernel);
        cosetRepresentatives := [kernel!0] cat cosetRep;
        t := Floor((d-1)/2); // error correcting capability 
       
        for v in cosetRepresentatives do
            // Check if u in C
            Cv := LinearCode(VerticalJoin(G, v)); 
            if u in Cv then
                return true, u;    
            end if;
                    
            // Compute the minimum word of the extend coset 
            // Cu = kernel U (kernel+u+v)
            Cu := LinearCode(VerticalJoin(G, u+v));
            minExCosetWord := MinimumWord(Cu);
            minExCosetWeight := Weight(minExCosetWord);
            if minExCosetWeight lt minWeight then
                minWord := minExCosetWord;
                minWeight := minExCosetWeight;
            end if;
       
            // Check whether the decoding is unique
            if minWeight le t then
                return true, u + minWord;  
            end if;
        end for;
                
        // Check whether the minWord can be in C`Kernel or not
        minWeightKernel := minWeightKernel eq -1 select 
                                   MinimumWeight(kernel) else minWeightKernel;
        if minWeight lt minWeightKernel then  
            return true, u + minWord;               
        else                           
            return false, kernel!0;   
        end if;
    end if;

end function;

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
/* case quaternary u                                            */
/* Signature: (<CodeLinRng> C, <ModTupRngElt> u)                */
/*               -> BoolElt, ModTupRngElt, ModTupFldElt         */
/* case binary u                                                */
/* Signature: (<CodeLinRng> C, <ModTupFldElt> u)                */
/*               -> BoolElt, ModTupRngElt, ModTupFldElt         */
/*                                                              */
/* case quaternary sequence Q                                   */
/* Signature: (<CodeLinRng> C, <[ModTupRngElt]> Q)              */
/*               -> [BoolElt], [ModTupRngElt], [ModTupFldElt]   */
/* case binary sequence Q                                       */
/* Signature: (<CodeLinRng> C, <[ModTupFldElt]> Q)              */
/*               -> [BoolElt], [ModTupRngElt], [ModTupFldElt]   */
/*                                                              */
/****************************************************************/
intrinsic CosetDecode(C::CodeLinRng, u::ModTupRngElt : MinWeightCode:=-1,
                     MinWeightKernel:=-1) -> BoolElt, ModTupRngElt, ModTupFldElt
{
Given a code C over Z4 of length n, and a vector u from the ambient space V=Z4^n, 
attempt to decode u with respect to C. If the decoding algorithm 
succeeds in computing a vector u' in C as the decoded version of u in V, then 
the function returns true, u' and Phi(u'), where Phi is the Gray map. If the 
decoding algorithm does not succeed in decoding u, then the function returns 
false, the zero vector in V and the zero vector in V2.

The coset decoding algorithm considers the binary linear code Cu=Cbin U 
(Cbin+Phi(u)), when Cbin=Phi(C) is linear. On the other hand, when Cbin is 
nonlinear, we have that Cbin=U_(i=0)^t (Kbin + Phi(ci)), where Kbin=Phi(KC), KC 
is the kernel of C as a subcode over Z4, [c0,c1,...,ct] are the coset 
representatives of C with respect to KC (not necessarily of minimal weight in 
their cosets) and c0 is the zero codeword. In this case, the algorithm considers 
the binary linear codes K0=Kbin U (Kbin+Phi(u)), K1=Kbin U (Kbin+Phi(c1)+Phi(u)), 
..., Kt=Kbin U (Kbin+Phi(ct)+Phi(u)).

If the parameter MinWeightCode is not assigned, then the minimum weight of C, 
which coincides with the minimum weight of Cbin, denoted by d, is computed. 
Note that the minimum distance of Cbin coincides with its minimum weight.
If Cbin is linear and the minimum weight of Cu is less than d, then 
Phi(u')=Phi(u)+e, where e is a word of minimum weight of Cu; otherwise, the 
decoding algorithm returns false. On the other hand, if Cbin is nonlinear and 
the minimum weight of U_(i=0)^t Ki is less than the minimum weight of Kbin, then 
Phi(u')=Phi(u)+e, where e is a word of minimum weight of U_(i=0)^t Ki; otherwise, 
the decoding algorithm returns false. If the parameter MinWeightKernel is not 
assigned, then the minimum Hamming weight of Kbin is computed.
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require (BaseRing(u) eq Z4): "Argument 2 must be a vector over Z4";
    n := Length(C);
    require (Degree(u) eq n): "Argument 2 must be of length", n;

    nbin := 2*n;
    grayMap := GrayMap(UniverseCode(Z4, n));
    ubin := grayMap(u);
    
    d := (MinWeightCode eq -1) select MinimumLeeWeight(C) else MinWeightCode;

    _, kernel := KernelZ2CodeZ4(C);
    _, cosetRep := KernelCosetRepresentatives(C);
    isDecoded, ubinDecoded := CosetDecodeAlg(kernel, cosetRep, d, ubin :
                                                minWeightKernel := MinWeightKernel);
 
    if isDecoded then
        uDecoded := ubinDecoded@@grayMap;
        return isDecoded, uDecoded, ubinDecoded;
    else
        return isDecoded, C!0, grayMap(C!0);
    end if;

end intrinsic;

/****************************************************************/
intrinsic CosetDecode(C::CodeLinRng, u::ModTupFldElt : MinWeightCode:=-1,
                     MinWeightKernel:=-1) -> BoolElt, ModTupRngElt, ModTupFldElt
{
Given a code C over Z4 of length n, and a vector Phi(u) from the ambient space 
V2=Z2^(2*n), attempt to decode u with respect to C. If the decoding algorithm 
succeeds in computing a vector u' in C as the decoded version of u in V, then 
the function returns true, u' and Phi(u'), where Phi is the Gray map. If the 
decoding algorithm does not succeed in decoding u, then the function returns 
false, the zero vector in V and the zero vector in V2.

The coset decoding algorithm considers the binary linear code Cu=Cbin U 
(Cbin+Phi(u)), when Cbin=Phi(C) is linear. On the other hand, when Cbin is 
nonlinear, we have that Cbin=U_(i=0)^t (Kbin + Phi(ci)), where Kbin=Phi(KC), KC 
is the kernel of C as a subcode over Z4, [c0,c1,...,ct] are the coset 
representatives of C with respect to KC (not necessarily of minimal weight in 
their cosets) and c0 is the zero codeword. In this case, the algorithm considers 
the binary linear codes K0=Kbin U (Kbin+Phi(u)), K1=Kbin U (Kbin+Phi(c1)+Phi(u)), 
..., Kt=Kbin U (Kbin+Phi(ct)+Phi(u)).

If the parameter MinWeightCode is not assigned, then the minimum weight of C, 
which coincides with the minimum weight of Cbin, denoted by d, is computed. 
Note that the minimum distance of Cbin coincides with its minimum weight.
If Cbin is linear and the minimum weight of Cu is less than d, then 
Phi(u')=Phi(u)+e, where e is a word of minimum weight of Cu; otherwise, the 
decoding algorithm returns false. On the other hand, if Cbin is nonlinear and 
the minimum weight of U_(i=0)^t Ki is less than the minimum weight of Kbin, then 
Phi(u')=Phi(u)+e, where e is a word of minimum weight of U_(i=0)^t Ki; otherwise, 
the decoding algorithm returns false. If the parameter MinWeightKernel is not 
assigned, then the minimum Hamming weight of Kbin is computed.
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require (BaseRing(u) eq GF(2)): "Argument 2 must be a vector over GF(2)";
    n := Length(C);
    nbin := 2*n;
    require (Degree(u) eq nbin): "Argument 2 must be of length", nbin;
    
    d := (MinWeightCode eq -1) select MinimumLeeWeight(C) else MinWeightCode;

    _, kernel := KernelZ2CodeZ4(C);
    _, cosetRep := KernelCosetRepresentatives(C);
    isDecoded, ubinDecoded := CosetDecodeAlg(kernel, cosetRep, d, u :
                                                minWeightKernel := MinWeightKernel);
    
    grayMap := GrayMap(UniverseCode(Z4, n));
    if isDecoded then
        uDecoded := ubinDecoded@@grayMap;
        return isDecoded, uDecoded, ubinDecoded;
    else
        return isDecoded, C!0, grayMap(C!0);
    end if;

end intrinsic;

/****************************************************************/
intrinsic CosetDecode(C::CodeLinRng, Q::[ModTupRngElt] : MinWeightCode:=-1,
               MinWeightKernel:=-1) -> SeqEnum[BoolElt], SeqEnum[ModTupRngElt], 
               SeqEnum[ModTupFldElt]
{
Given a code C over Z4 of length n, and a sequence Q of vectors from the ambient 
space V=Z4^n, attempt to decode the vectors of Q with respect to C. 
This function is similar to the function CosetDecode(C, u) except that rather than 
decoding a single vector, it decodes a sequence of vectors and returns a sequence 
of booleans and two sequences of decoded vectors corresponding to the given sequence. 
The algorithm used and effect of the parameters MinWeightCode and MinWeightKernel 
are as for the function CosetDecode(C, u).
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require not IsEmpty(Q): "Argument 2 cannot be an empty sequence";  
    require (BaseRing(Q[1]) eq Z4): "Argument 2 must contain vectors over Z4";
    n := Length(C);
    require (Degree(Q[1]) eq n): "Argument 2 must contain vectors of length", n;

    nbin := 2*n;
    grayMap := GrayMap(UniverseCode(Z4, n));
    zerobin := grayMap(C!0);
    
    d := (MinWeightCode eq -1) select MinimumLeeWeight(C) else MinWeightCode;

    _, kernel := KernelZ2CodeZ4(C);
    _, cosetRep := KernelCosetRepresentatives(C);
    
    isDecodedSeq := [];
    uDecodedSeq := [];
    ubinDecodedSeq := [];
    for u in Q do
        ubin := grayMap(u);
        isDecoded, ubinDecoded := CosetDecodeAlg(kernel, cosetRep, d, ubin :
                                                minWeightKernel := MinWeightKernel); 
        Append(~isDecodedSeq, isDecoded); 
        if isDecoded then          
            Append(~uDecodedSeq, ubinDecoded@@grayMap);
            Append(~ubinDecodedSeq, ubinDecoded);
        else
            Append(~uDecodedSeq, C!0);
            Append(~ubinDecodedSeq, zerobin);        
        end if; 
    end for;
    
    return isDecodedSeq, uDecodedSeq, ubinDecodedSeq;

end intrinsic;

/****************************************************************/
intrinsic CosetDecode(C::CodeLinRng, Q::[ModTupFldElt] : MinWeightCode:=-1,
          MinWeightKernel:=-1) -> SeqEnum[BoolElt], SeqEnum[ModTupRngElt], 
          SeqEnum[ModTupFldElt]
{
Given a code C over Z4 of length n, and a sequence Q of vectors from the ambient 
space V2=Z2^(2*n), attempt to decode the vectors of Q with respect to C. 
This function is similar to the function CosetDecode(C, u) except that rather than 
decoding a single vector, it decodes a sequence of vectors and returns a sequence 
of booleans and two sequences of decoded vectors corresponding to the given sequence. 
The algorithm used and effect of the parameters MinWeightCode and MinWeightKernel 
are as for the function CosetDecode(C, u).
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require not IsEmpty(Q): "Argument 2 cannot be an empty sequence";  
    require (BaseRing(Q[1]) eq GF(2)): "Argument 2 must contain vectors over GF(2)";
    n := Length(C);
    nbin := 2*n;
    require (Degree(Q[1]) eq nbin): "Argument 2 must contain vectors of length", nbin;
    
    grayMap := GrayMap(UniverseCode(Z4, n));
    zerobin := grayMap(C!0);
    
    d := (MinWeightCode eq -1) select MinimumLeeWeight(C) else MinWeightCode;

    _, kernel := KernelZ2CodeZ4(C);
    _, cosetRep := KernelCosetRepresentatives(C);
    
    isDecodedSeq := [];
    uDecodedSeq := [];
    ubinDecodedSeq := [];
    for u in Q do
        isDecoded, ubinDecoded := CosetDecodeAlg(kernel, cosetRep, d, u :
                                                minWeightKernel := MinWeightKernel); 
        Append(~isDecodedSeq, isDecoded); 
        if isDecoded then          
            Append(~uDecodedSeq, ubinDecoded@@grayMap);
            Append(~ubinDecodedSeq, ubinDecoded);
        else
            Append(~uDecodedSeq, C!0);
            Append(~ubinDecodedSeq, zerobin);        
        end if; 
    end for;
    
    return isDecodedSeq, uDecodedSeq, ubinDecodedSeq;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////				SYNDROME DECODE FUNCTIONS	                        ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

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
/* case quaternary u                                            */
/* Signature: (<CodeLinRng> C, <ModTupRngElt> u)                */
/*               -> BoolElt, ModTupRngElt, ModTupFldElt         */
/* case binary u                                                */
/* Signature: (<CodeLinRng> C, <ModTupFldElt> u)                */
/*               -> BoolElt, ModTupRngElt, ModTupFldElt         */
/*                                                              */
/* case quaternary sequence Q                                   */
/* Signature: (<CodeLinRng> C, <[ModTupRngElt]> Q)              */
/*               -> [BoolElt], [ModTupRngElt], [ModTupFldElt]   */
/* case binary sequence Q                                       */
/* Signature: (<CodeLinRng> C, <[ModTupFldElt]> Q)              */
/*               -> [BoolElt], [ModTupRngElt], [ModTupFldElt]   */
/*                                                              */
/****************************************************************/
intrinsic SyndromeDecode(C::CodeLinRng, u::ModTupRngElt) 
                                        -> BoolElt, ModTupRngElt, ModTupFldElt
{
Given a code C over Z4 of length n, and a vector u from the ambient space V=Z4^n, 
attempt to decode u with respect to C. The decoding algorithm always succeeds in 
computing a vector u' in C as the decoded version of u in V, and the function 
returns true, u' and Phi(u'), where Phi is the Gray map. Although the function 
never returns false, the first output parameter true is given to be consistent 
with the other decoding functions.

The syndrome decoding algorithm consists of computing a table pairing each possible 
syndrome s with a vector of minimum Lee weight e_s, called coset leader, in the 
coset of C containing all vectors having syndrome s. After receiving a vector u, 
compute its syndrome s using the parity check matrix. Then, u is decoded as the 
codeword c=u-e_s.
}
    require (BaseRing(C) eq Z4) : "Code must be over Z4";
    require (BaseRing(u) eq Z4): "Argument 2 must be a vector over Z4";
    n := Length(C);
    require (Degree(u) eq n): "Argument 2 must be of length", n;

    _, mapCosetLeaders := CosetLeaders(C);
    grayMap := GrayMap(C);
    
    c := u - mapCosetLeaders(Syndrome(u, C));

    return true, c, grayMap(c);

end intrinsic;

/****************************************************************/
intrinsic SyndromeDecode(C::CodeLinRng, u::ModTupFldElt) 
                                        -> BoolElt, ModTupRngElt, ModTupFldElt
{
Given a code C over Z4 of length n, and a vector Phi(u) from the ambient space 
V2=Z2^(2*n), attempt to decode u with respect to C. The decoding algorithm always 
succeeds in computing a vector u' in C as the decoded version of u in V, and the 
function returns true, u' and Phi(u'), where Phi is the Gray map. Although the 
function never returns false, the first output parameter true is given to be 
consistent with the other decoding functions.

The syndrome decoding algorithm consists of computing a table pairing each possible 
syndrome s with a vector of minimum Lee weight e_s, called coset leader, in the 
coset of C containing all vectors having syndrome s. After receiving a vector u, 
compute its syndrome s using the parity check matrix. Then, u is decoded as the 
codeword c=u-e_s.
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require (BaseRing(u) eq GF(2)): "Argument 2 must be a vector over GF(2)";
    n := Length(C);
    nbin := 2*n;
    require (Degree(u) eq nbin): "Argument 2 must be of length", nbin;
    
    _, mapCosetLeaders := CosetLeaders(C);
    grayMap := GrayMap(UniverseCode(Z4, n));

    c := u@@grayMap - mapCosetLeaders(Syndrome(u, C));

    return true, c, grayMap(c);

end intrinsic

/****************************************************************/
intrinsic SyndromeDecode(C::CodeLinRng, Q::[ModTupRngElt]) 
               -> SeqEnum[BoolElt], SeqEnum[ModTupRngElt], SeqEnum[ModTupFldElt]
{
Given a code C over Z4 of length n, and a sequence Q of vectors from the ambient 
space V=Z4^n, attempt to decode the vectors of Q with respect to C. 
This function is similar to the function SyndromeDecode(C, u) except that rather than 
decoding a single vector, it decodes a sequence of vectors and returns a sequence 
of booleans and two sequences of decoded vectors corresponding to the given sequence. 
The algorithm used is as for the function SyndromeDecode(C, u).
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require not IsEmpty(Q): "Argument 2 cannot be an empty sequence";  
    require (BaseRing(Q[1]) eq Z4): "Argument 2 must contain vectors over Z4";
    n := Length(C);
    require (Degree(Q[1]) eq n): "Argument 2 must contain vectors of length", n;

    _, mapCosetLeaders := CosetLeaders(C);
    grayMap := GrayMap(C);
    
    uDecodedSeq := [];
    ubinDecodedSeq := [];
    for u in Q do
        c := u - mapCosetLeaders(Syndrome(u, C));           
        Append(~uDecodedSeq, c);
        Append(~ubinDecodedSeq, grayMap(c));
    end for;
    
    return [true : i in [1..#Q]], uDecodedSeq, ubinDecodedSeq;   

end intrinsic;

/****************************************************************/
intrinsic SyndromeDecode(C::CodeLinRng, Q::[ModTupFldElt]) 
               -> SeqEnum[BoolElt], SeqEnum[ModTupRngElt], SeqEnum[ModTupFldElt]
{
Given a code C over Z4 of length n, and a sequence Q of vectors from the ambient 
space V2=Z2^(2*n), attempt to decode the vectors of Q with respect to C. 
This function is similar to the function SyndromeDecode(C, u) except that rather than 
decoding a single vector, it decodes a sequence of vectors and returns a sequence 
of booleans and two sequences of decoded vectors corresponding to the given sequence. 
The algorithm used is as for the function SyndromeDecode(C, u).
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require not IsEmpty(Q): "Argument 2 cannot be an empty sequence";  
    require (BaseRing(Q[1]) eq GF(2)): "Argument 2 must contain vectors over GF(2)";
    n := Length(C);
    nbin := 2*n;
    require (Degree(Q[1]) eq nbin): "Argument 2 must contain vectors of length", nbin;
    
    _, mapCosetLeaders := CosetLeaders(C);
    grayMap := GrayMap(UniverseCode(Z4, n));

    uDecodedSeq := [];
    ubinDecodedSeq := [];
    for u in Q do
        c := u@@grayMap - mapCosetLeaders(Syndrome(u, C));         
        Append(~uDecodedSeq, c);
        Append(~ubinDecodedSeq, grayMap(c));
    end for;
    
    return [true : i in [1..#Q]], uDecodedSeq, ubinDecodedSeq;  

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////				LIFT DECODE FUNCTIONS	                            ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/****************************************************************/
/*                                                              */
/* Function name: LiftedDecodeAlg                               */
/* Parameters: C0, C1, Gdelta, u, algMethod                     */
/* Function description: Given the binary linear codes C0 and   */
/*   C1 associated to the lifted decoding for a code C over Z4  */
/*   in standard form with information coordinates at the end,  */
/*   a matrix Gdelta over Z4 with the delta rows of order four  */
/*   of a generator matrix of C, a received vector u in V=Z4^n, */
/*   and a decoding algorithm for linear codes ("Euclidean" for */
/*   alternant codes or "Syndrome" in codes in general),        */
/*   attempt to decode u with respect to C. If the decoding     */
/*   algorithm succeeds in computing a vector u' in C as        */
/*   the decoded version of u in V, then the function returns   */
/*   true and u'. If the decoding algorithm does not succeed    */
/*   in decoding u, then the function returns false the zero    */
/*   vector in V.                                               */
/*   See below the description of the intrinsic LiftedDecode    */
/*   for more details.                                          */
/*                                                              */
/****************************************************************/
LiftedDecodeAlg := function(C0, C1, Gdelta, u, algMethod)

    n := Length(C0);
    delta := Dimension(C0);
    gamma := Dimension(C1)-delta;

    u0 := ChangeRing(u, GF(2));
    // if algMethod <> "Syndrome", the best algorithm will be selected
    if algMethod eq "Syndrome" then
        isDecoded0, c0 := Decode(C0, u0 : Al := algMethod); 
    else
        isDecoded0, c0 := Decode(C0, u0); 
    end if;
    // error vector such that u0=c0+e0
    e0 := u0 - c0;
    
    // information vector of c0 being C0 systematic in the last delta coordinates
    i0 := VectorSpace(GF(2), delta)![c0[i] : i in [n-delta+1..n]]; 
    R := RSpace(Z4, n);
    e0 := R!ChangeRing(e0, Z2);
    sumGdelta := IsZero(delta) or IsEmpty(Support(i0)) select R!0 else 
                                              &+[ Gdelta[i] : i in Support(i0) ]; 
    u1 := u - sumGdelta - e0;
    u1 := VectorSpace(GF(2),n)![(u1[i] eq 2) select 1 else 0 : i in [1..n]];
    // if algMethod <> "Syndrome", the best algorithm will be selected
    if algMethod eq "Syndrome" then
        isDecoded1, c1 := Decode(C1, u1 : Al := algMethod);
    else
        isDecoded1, c1 := Decode(C1, u1);
    end if;
    e1 := R!ChangeRing(u1-c1, Z2);  
    
    e := e0 + 2*e1;
    c := u - e; 
    
    return isDecoded0, isDecoded1, c;
    
end function;

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
/* case quaternary u                                            */
/* Signature: (<CodeLinRng> C, <ModTupRngElt> u)                */
/*               -> BoolElt, ModTupRngElt, ModTupFldElt         */
/* case binary u                                                */
/* Signature: (<CodeLinRng> C, <ModTupFldElt> u)                */
/*               -> BoolElt, ModTupRngElt, ModTupFldElt         */
/*                                                              */
/* case quaternary sequence Q                                   */
/* Signature: (<CodeLinRng> C, <[ModTupRngElt]> Q)              */
/*               -> [BoolElt], [ModTupRngElt], [ModTupFldElt]   */
/* case binary sequence Q                                       */
/* Signature: (<CodeLinRng> C, <[ModTupFldElt]> Q)              */
/*               -> [BoolElt], [ModTupRngElt], [ModTupFldElt]   */
/*                                                              */
/****************************************************************/
intrinsic LiftedDecode(C::CodeLinRng, u::ModTupRngElt : AlgMethod := "Euclidean") 
                                        -> BoolElt, ModTupRngElt, ModTupFldElt
{
Given a code C over Z4 of length n, and a vector u from the ambient space V=Z4^n,
attempt to decode u with respect to C. If the decoding algorithm succeeds in 
computing a vector u' in C as the decoded version of u in V, then the function 
returns true, u' and Phi(u'), where Phi is the Gray map. If the decoding algorithm 
does not succeed in decoding u, then the function returns false, the zero vector 
in V and the zero in V2 (in the Euclidean case it may happen that u' is not in C
because there are too many errors in u to correct).

The lifted decoding algorithm consists of lifting decoding algorithms for two 
binary linear codes C0 and C1, known as the residue and torsion codes of C. Let 
t0 and t1 be the error-correcting capability of C0 and C1, respectively. Assume 
the received vector u=c+e, where c in C and e in V is the error vector. Then, 
the lifted decoding algorithm can correct all error vectors e such that 
tau_1 + tau_3 <= t0 and tau_2 + tau_3 <= t1, where tau_i is the number of 
occurrences of i in e.

In the decoding process, the function Decode(C, u) for linear codes is used. 
The accessible algorithms for linear codes are: syndrome decoding and a Euclidean 
algorithm, which operates on alternant codes (BCH, Goppa, and Reed--Solomon codes, etc.).
If C0 or C1 is alternant, the Euclidean algorithm is used by default, but the 
syndrome algorithm will be used if the parameter AlgMethod is assigned the value 
"Syndrome". For non-alternant codes C0 and C1, only syndrome decoding is possible, 
so the parameter AlgMethod is not relevant.
}
    require (BaseRing(C) eq Z4) : "Code must be over Z4";
    require (BaseRing(u) eq Z4): "Argument 2 must be a vector over Z4";
    n := Length(C);
    require (Degree(u) eq n): "Argument 2 must be of length", n;
    
    Cs, _, Gs, perm := Z4StandardForm(C);
    C0 := BinaryResidueCode(Cs); 
    C1 := BinaryTorsionCode(Cs);
    delta := Dimension(C0);
    gamma := Dimension(C1)-delta;  
    Gdelta := RowSubmatrix(Gs, gamma+1, delta);
    
    // received vector u permuted according to the new code Cs
    u := u^(perm^(-1));  
    isDecoded0, isDecoded1, c := LiftedDecodeAlg(C0, C1, Gdelta, u, AlgMethod); 
    // decoded codeword c in Cs permuted to be a codeword in the original code C 
    c := c^perm;     
    
    return isDecoded0 and isDecoded1, c, GrayMap(C)(c);

end intrinsic;

/****************************************************************/
intrinsic LiftedDecode(C::CodeLinRng, u::ModTupFldElt : AlgMethod := "Euclidean") 
                                        -> BoolElt, ModTupRngElt, ModTupFldElt
{
Given a code C over Z4 of length n, and a vector Phi(u) from the ambient space 
V2=Z2^(2*n), attempt to decode u with respect to C. If the decoding algorithm 
succeeds in computing a vector u' in C as the decoded version of u in V, then the 
function returns true, u' and Phi(u'), where Phi is the Gray map. If the decoding 
algorithm does not succeed in decoding u, then the function returns false, the 
zero vector in V and the zero in V2 (in the Euclidean case it may happen that u' 
is not in C because there are too many errors in u to correct).

The lifted decoding algorithm consists of lifting decoding algorithms for two 
binary linear codes C0 and C1, known as the residue and torsion codes of C. Let 
t0 and t1 be the error-correcting capability of C0 and C1, respectively. Assume 
the received vector u=c+e, where c in C and e in V is the error vector. Then, 
the lifted decoding algorithm can correct all error vectors e such that 
tau_1 + tau_3 <= t0 and tau_2 + tau_3 <= t1, where tau_i is the number of 
occurrences of i in e.

In the decoding process, the function Decode(C, u) for linear codes is used. 
The accessible algorithms for linear codes are: syndrome decoding and a Euclidean 
algorithm, which operates on alternant codes (BCH, Goppa, and Reed--Solomon codes, etc.).
If C0 or C1 is alternant, the Euclidean algorithm is used by default, but the 
syndrome algorithm will be used if the parameter AlgMethod is assigned the value 
"Syndrome". For non-alternant codes C0 and C1, only syndrome decoding is possible, 
so the parameter AlgMethod is not relevant.
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require (BaseRing(u) eq GF(2)): "Argument 2 must be a vector over GF(2)";
    n := Length(C);
    nbin := 2*n;
    require (Degree(u) eq nbin): "Argument 2 must be of length", nbin;

    Cs, _, Gs, perm := Z4StandardForm(C);
    C0 := BinaryResidueCode(Cs); 
    C1 := BinaryTorsionCode(Cs);
    delta := Dimension(C0);
    gamma := Dimension(C1)-delta;  
    Gdelta := RowSubmatrix(Gs, gamma+1, delta);
    
    grayMap := GrayMap(UniverseCode(Z4, n));
    u := u@@grayMap;
    // received vector u permuted according to the new code Cs
    u := u^(perm^(-1));  
    isDecoded0, isDecoded1, c := LiftedDecodeAlg(C0, C1, Gdelta, u, AlgMethod); 
    // decoded codeword c in Cs permuted to be a codeword in the original code C 
    c := c^perm;  
          
    return isDecoded0 and isDecoded1, c, GrayMap(C)(c);

end intrinsic; 

/****************************************************************/
intrinsic LiftedDecode(C::CodeLinRng, Q::[ModTupRngElt] : AlgMethod := "Euclidean") 
               -> SeqEnum[BoolElt], SeqEnum[ModTupRngElt], SeqEnum[ModTupFldElt]
{
Given a code C over Z4 of length n, and a sequence Q of vectors from the ambient 
space V=Z4^n, attempt to decode the vectors of Q with respect to C. 
This function is similar to the function LiftedDecode(C, u) except that rather than 
decoding a single vector, it decodes a sequence of vectors and returns a sequence 
of booleans and two sequences of decoded vectors corresponding to the given sequence. 
The algorithm used and effect of the parameter AlgMethod are as for the function 
LiftedDecode(C, u).
}
    require (BaseRing(C) eq Z4) : "Code must be over Z4";
    require not IsEmpty(Q): "Argument 2 cannot be an empty sequence";  
    require (BaseRing(Q[1]) eq Z4): "Argument 2 must contain vectors over Z4";
    n := Length(C);
    require (Degree(Q[1]) eq n): "Argument 2 must contain vectors of length", n;

    Cs, _, Gs, perm := Z4StandardForm(C);
    C0 := BinaryResidueCode(Cs); 
    C1 := BinaryTorsionCode(Cs);
    delta := Dimension(C0);
    gamma := Dimension(C1)-delta;  
    Gdelta := RowSubmatrix(Gs, gamma+1, delta);
    
    grayMap := GrayMap(C);
    zerobin := grayMap(C!0);

    isDecodedSeq := [];
    uDecodedSeq := [];
    ubinDecodedSeq := [];
    for u2 in Q do
        // received vector u permuted according to the new code Cs
        u := u2^(perm^(-1));  
        isDecoded0, isDecoded1, c := LiftedDecodeAlg(C0, C1, Gdelta, u, AlgMethod); 
        // decoded codeword c in Cs permuted to be a codeword in the original code C 
        c := c^perm;     
    
        isDecoded := isDecoded0 and isDecoded1;
        Append(~isDecodedSeq, isDecoded); 
        if isDecoded then          
            Append(~uDecodedSeq, c);
            Append(~ubinDecodedSeq, grayMap(c));
        else
            Append(~uDecodedSeq, C!0);
            Append(~ubinDecodedSeq, zerobin);        
        end if; 
    end for;
    
    return isDecodedSeq, uDecodedSeq, ubinDecodedSeq;
    
end intrinsic;

/****************************************************************/
intrinsic LiftedDecode(C::CodeLinRng, Q::[ModTupFldElt] : AlgMethod := "Euclidean") 
               -> SeqEnum[BoolElt], SeqEnum[ModTupRngElt], SeqEnum[ModTupFldElt]
{
Given a code C over Z4 of length n, and a sequence Q of vectors from the ambient 
space V2=Z2^(2*n), attempt to decode the vectors of Q with respect to C. 
This function is similar to the function LiftedDecode(C, u) except that rather than 
decoding a single vector, it decodes a sequence of vectors and returns a sequence 
of booleans and two sequences of decoded vectors corresponding to the given sequence. 
The algorithm used and effect of the parameter AlgMethod are as for the function 
LiftedDecode(C, u).
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require not IsEmpty(Q): "Argument 2 cannot be an empty sequence";  
    require (BaseRing(Q[1]) eq GF(2)): "Argument 2 must contain vectors over GF(2)";
    n := Length(C);
    nbin := 2*n;
    require (Degree(Q[1]) eq nbin): "Argument 2 must contain vectors of length", nbin;

    Cs, _, Gs, perm := Z4StandardForm(C);
    C0 := BinaryResidueCode(Cs); 
    C1 := BinaryTorsionCode(Cs);
    delta := Dimension(C0);
    gamma := Dimension(C1)-delta;  
    Gdelta := RowSubmatrix(Gs, gamma+1, delta);
   
    grayMap := GrayMap(UniverseCode(Z4, n));
    zerobin := grayMap(C!0);

    isDecodedSeq := [];
    uDecodedSeq := [];
    ubinDecodedSeq := [];
    for ubin in Q do
        u := ubin@@grayMap;
        // received vector u permuted according to the new code Cs
        u := u^(perm^(-1));  
        isDecoded0, isDecoded1, c := LiftedDecodeAlg(C0, C1, Gdelta, u, AlgMethod); 
        // decoded codeword c in Cs permuted to be a codeword in the original code C 
        c := c^perm;     
    
        isDecoded := isDecoded0 and isDecoded1;
        Append(~isDecodedSeq, isDecoded); 
        if isDecoded then          
            Append(~uDecodedSeq, c);
            Append(~ubinDecodedSeq, grayMap(c));
        else
            Append(~uDecodedSeq, C!0);
            Append(~ubinDecodedSeq, zerobin);        
        end if; 
    end for;
    
    return isDecodedSeq, uDecodedSeq, ubinDecodedSeq;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////				PERMUTATION DECODE FUNCTIONS                        ///////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/****************************************************************/
/*                                                              */  
/* Function name: ExistPermutationInPDset                       */
/* Parameters: S, I, v                                          */
/* Function description: Given a PD-set S, an information set I */
/*   and a binary vector v, return whether there exists a       */
/*   permutation in S such that moves the nonzero coordinates   */
/*   of v out of the information coordinates.                   */  
/*   The PD-set S and information set I are given as sequences. */
/*                                                              */
/****************************************************************/
ExistPermutationInPDset := function (S, I, v)
    for p in S do
        if IsZero([(v^p)[i] : i in I]) then
            return true;
        end if;
    end for;
    return false;
end function;

/****************************************************************/
/*                                                              */  
/* Function name: IsSubsetOfPAut                                */
/* Parameters: C, S                                             */
/* Function description: Given a code C over Z4 of length n     */
/*   or a set C with the corresponding binary codewords and a   */
/*   sequence S of permutations in Sym(n) or Sym(2n), return    */
/*   true whether S is a subset of PAut(C).                     */ 
/*                                                              */
/****************************************************************/
IsSubsetOfPAut := function (C, S)
    for p in S do
        if C^p ne C then
            return false;
        end if;
    end for;
    return true;
end function;

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
intrinsic IsPermutationDecodeSet(C::CodeLinRng, I::[RngIntElt], S::[GrpPermElt], 
                                                        s::RngIntElt) -> BoolElt
{
Given a code C over Z4 of length n and type 2^gamma 4^delta, a sequence I in 
[1,...,2*n], a sequence S of elements in the symmetric group Sym(2*n) of 
permutations on the set [1,...,2*n], and an integer s>1, return true if and only 
if S is an s-PD-set for Cbin=Phi(C), where Phi is the Gray map, with respect to 
the information set I.                                      

The parameters I and S can also be given as a sequence I in [1,...,n] and a 
sequence S of elements in the symmetric group Sym(n) of permutations on the set 
[1,...,n], respectively. In this case, the function returns true if and only if 
Phi(S) is an s-PD-set for Cbin=Phi(C) with respect to the information set Phi(I), 
where Phi(I) and Phi(S) are the sequences defined as in the manual.

Depending on the length of the code C, its type, and the integer s, this function 
could take some time to compute whether S or Phi(S) is an s-PD-set for Cbin with 
respect to I or Phi(I), respectively. Specifically, if the function returns true, 
it is necessary to check sum_(i=1)^s (|I| choose i)*((N-|I|) choose (s-i)) s-sets, 
where N=n and |I|=gamma+delta when I is given as an information set for C, or 
N=2*n and |I|=gamma+2*delta when I is given as an information set for Cbin.

The verbose flag IsPDsetFlag is set to level 0 by default. If it is set to level 
1, the total time used to check the condition is shown. If it is set to level 2, 
the percentage of the computation process performed is also printed.
}   
    require (BaseRing(C) eq Z4) : "Code must be over Z4"; 
    require not(zero_Code(C)): "Code cannot be the zero code";
    requirege s, 1;
 
    require not IsEmpty(S): "Argument 3 cannot be an empty sequence";   
    n := Length(C);
	nbin := 2*n; 
    numSymG := Degree(Parent(S[1]));
    require ((numSymG eq n) or (numSymG eq nbin)): 
          "Argument 3 should contain permutations acting on a set of cardinality", 
                                                                    n, "or", nbin;
    k := #I;
    require (k ge 1): "Argument 2 cannot be an empty sequence";
    if numSymG eq n then
        require (Min(I) ge 1) and (Max(I) le n): 
                                     "Argument 2 should be a subset of", [1..n];
    else  // numSymG = nbin
        require (Min(I) ge 1) and (Max(I) le nbin): 
                                  "Argument 2 should be a subset of", [1..nbin];
    end if;
    
    ///////////////////////////////////////////////////////////////////
	iniTime := Cputime();
	vprintf IsPDSetFlag,2: "Checking whether I is an information set...\n";
    ///////////////////////////////////////////////////////////////////
    
	isInfSetZ4, isInfSetZ2 := IsInformationSet(C, I);

    I := Set(I);  // Eliminate repeated coordinate positions in I
    S := Set(S);  // Eliminate repeated permutations in S

    ///////////////////////////////////////////////////////////////////
	vprintf IsPDSetFlag,2: 
                  "Checking whether S is in the permutation automorphism group...\n";
    ///////////////////////////////////////////////////////////////////
     
    case numSymG:
        when n:  
            if not isInfSetZ4 then
                vprintf IsPDSetFlag,1: "Argument 2 is not an information set for C\n";
                return false; 
            end if;
            if not IsSubsetOfPAut(C, S) then 
                vprintf IsPDSetFlag,1: 
                  "Argument 3 is not a subset of the permutation automorphism group of C\n";   
                return false;     
            end if;
            length := n;
        when nbin:
            if not isInfSetZ2 then
                vprintf IsPDSetFlag,1: "Argument 2 is not an information set for Cbin = Phi(C)\n";
                return false; 
            end if;
            if not IsSubsetOfPAut(Set(GrayMapImage(C)), S) then   
                vprintf IsPDSetFlag,1: 
                  "Argument 3 is not a subset of the permutation automorphism group of Cbin = Phi(C)\n";  
                return false;      
            end if;
            length := nbin;
    end case;
     
    ///////////////////////////////////////////////////////////////////
	vprintf IsPDSetFlag,2: "Checking whether S is an s-PD-set...\n";
    ///////////////////////////////////////////////////////////////////

    numCheckSets := &+[ Binomial(k, i) * Binomial(length-k, s-i) : i in [1..s]];
    
    ///////////////////////////////////////////////////////////////////
	tenpc := numCheckSets div 10 + 1; //for verbose flag
    ///////////////////////////////////////////////////////////////////
    
    cont := 0;
    V := VectorSpace(GF(2), length);
    checkSet := {1..length} diff I;
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
/* Function name: SigmaEncoding                                 */
/* Parameters: v, R, gamma, delta                               */
/* Function description: Given a vector v over Z4, a matrix R,  */
/*   and two integer numbers gamma and delta, return a vector   */
/*   over Z4 having the same last delta coordinates, dprime, and*/
/*   where the first gamma coordinates are replaced by them     */
/*   plus Phi1(dprime*R), where Phi1 is the first coordinate of */
/*   the Gray map.                                              */
/*                                                              */
/****************************************************************/
SigmaEncoding := function(v, R, gamma, delta)
    c := Vector(GF(2), [v[i] : i in [1..gamma]]);
    dprime := Vector(Z4, [v[i] : i in [gamma+1..gamma+delta]]);
    cprime := c + GrayImageFirstCoordinate(dprime*R);
    return Vector(Z4, [Z4!(Z!cprime[i]) : i in [1..gamma]] cat 
                      [dprime[i] : i in [1..delta]]); 
end function;

/****************************************************************/
/*                                                              */  
/* Function name: StandardEncodingZ2                            */
/* Parameters: G, gamma, delta                                  */
/* Function description: Given a generator matrix of a code over*/
/*   Z4 of type 2^gamma 4^delta, and two integer numbers gamma  */
/*   and delta, return a systematic encoding map for binary     */
/*   vector of length gamma+2*delta.                            */
/*                                                              */
/****************************************************************/
StandardEncodingZ2 := function(G, gamma, delta)
    InfVSpace := VectorSpace(GF(2), gamma + 2*delta);
    n := Ncols(G); 
    V := VectorSpace(GF(2), 2*n);
    grayMap := GrayMap(LinearCode(G));
  	
    if IsZero(gamma) then
        encodingZ2 := map<InfVSpace -> V | 
            x :-> grayMap(GrayImageInverse(x, gamma, delta)*G) >;
    else 
        R := Submatrix(G, [gamma+1..gamma+delta], [n-delta-gamma+1..n-delta]); 
        encodingZ2 := map<InfVSpace -> V | 
            x :-> grayMap(SigmaEncoding(GrayImageInverse(
                              x, gamma, delta), R, gamma, delta)*G)>;
    end if;
    
    return encodingZ2;
end function;

/****************************************************************/
/*                                                              */  
/* Function name: PermutationDecodeInitialization               */
/* Parameters: C, I, S, n, k, numSymG                           */
/* Function description: This function initialize variables     */
/*   used in the permutation decoding algorithm.                */
/*   The parameters C, I, S are the same as PermutationDecode() */
/*   The parameter n is the length of the code over Z4 C        */
/*   The parameter k is the number of elements in I, |C|=2^k    */
/*   The parameter numSymG is the degree of the elements in S   */ 
/*   See below the description of the intrinsic                 */
/*   PermutationDecode for more details.                        */
/*                                                              */
/****************************************************************/
PermutationDecodeInitialization := function(C, I, S, n, k, numSymG)

    S := Set(S);  // Eliminate repeated permutations in S
    Gs, gamma, delta  := MinRowsGeneratorMatrix(C); 
    
    // p in Sym(n) moves the information coordinates given by I to the last positions
    newCols := [i : i in [1..n] | i notin I] cat I;
    p := Sym(n)![Position(newCols,i) : i in [1..n]];
    Gs := Gs^p; 
 
    // Transform the sequence S in Sym(n) to permutations in Sym(2n)
    if numSymG eq n then
        S := [ PermZ4ToPermZ2(sigma) : sigma in S ];
    end if;
 
    // Define a new variable pZ2 as the permutation p seen over the binary space
    // According to the new generator matrix Gs, where the information positions  
    // are the last ones, define new variables SZ2, IZ2, as the permuted versions 
    // of S and I, respectively
    // All these variables are considered over the binary space of length 2*n 
    pZ2 := PermZ4ToPermZ2(p);
    SZ2 := [pZ2^(-1) * sigma * pZ2 : sigma in S];         
    IZ2 := [2*i - 1 : i in [n-delta-gamma+1..n-delta]] cat 
        [i : i in [2*n - 2*delta + 1..2*n]];              // IZ2 = Phi(I)^pZ2     
 
    // Generator matrix Gs with the identity matrices of size gamma and delta
    _, _, GStandard := Z4StandardForm(LinearCode(Gs)); 
    // Encoding function in the binary space
    fbin := StandardEncodingZ2(GStandard, gamma, delta);
    grayMapC := GrayMap(C);
    invGrayMapC := grayMapC^-1;
    invpZ2 := pZ2^-1;
    identitySym := Sym(2*n)!1;
    
    return SZ2, pZ2, invpZ2, fbin, IZ2, grayMapC, invGrayMapC, identitySym;
end function;

/****************************************************************/
/*                                                              */  
/* Function name: PermutationDecodeAlg                          */
/* Parameters: C, SZ2, s, u, pZ2, invpZ2, fbin, IZ2,            */
/*             grayMapC, invGrayMapC, identitySym               */
/* Function description: This function performs the permutation */
/*   decoding algorithm from the variables initialized in the   */
/*   function PermutationDecodeInitialization.                  */                       
/*   See below the description of the intrinsic                 */
/*   PermutationDecode for more details.                        */
/*                                                              */
/****************************************************************/
PermutationDecodeAlg := function(C, SZ2, s, u, pZ2, invpZ2, fbin, IZ2, 
                              grayMapC, invGrayMapC, identitySym)

	uZ2 := u^pZ2;
	x := fbin(Vector([uZ2[i] : i in IZ2]));
	if Weight(uZ2 + x) le s then
		x_invpZ2 := x^invpZ2;
		return true, invGrayMapC(x_invpZ2), x_invpZ2;

	else 
        // Remove the identity permutation from SZ2 (if it is included in SZ2)
        // to not check twice the same condition  
        Exclude(~SZ2, identitySym);
		for sigma in SZ2 do
			x := fbin(Vector([(uZ2^sigma)[i]: i in IZ2]));
			if Weight(uZ2^sigma + x) le s then
				x_invpZ2 := (x^(sigma^-1))^(invpZ2);
				return true, invGrayMapC(x_invpZ2), x_invpZ2;
			end if;
		end for;
	    return false, C!0, grayMapC(C!0);

	end if;
end function;

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
intrinsic PermutationDecode(C::CodeLinRng, I::[RngIntElt], S::[GrpPermElt], 
          s::RngIntElt, u::ModTupFldElt) -> BoolElt, ModTupRngElt, ModTupFldElt
{
Given a code C over Z4 of length n and type 2^gamma 4^delta; an information set 
I=[i_1,...,i_(gamma+delta)] in [1,...,n] for C as a sequence of coordinate 
positions, such that the code C punctured on [1,...,n] minus [i_(gamma+1),...,
i_(gamma+delta)] is of type 4^delta; a sequence S such that either S or Phi(S) 
is an s-PD-set for Cbin=Phi(C), where Phi is the Gray map, with respect to Phi(I); 
an integer s in [1,...,t], where t is the error-correcting capability of Cbin; 
and a vector Phi(u) from the ambient space V2=Z2^(2*n), attempt to decode u 
with respect to C. If the decoding algorithm succeeds in computing a vector u' 
in C as the decoded version of u in V, then the function returns true, u' and  
Phi(u'). If the decoding algorithm does not succeed in decoding u, then the 
function returns false, the zero vector in V and the zero vector in V2.

The permutation decoding algorithm consists of moving all errors in a received 
vector Phi(u)=c+e, where u in V, c in Cbin and e in V2 is the error vector with 
at most t errors, out of the information positions, that is, moving the nonzero 
coordinates of e out of the information set Phi(I) for Cbin, by using an 
automorphism of Cbin.

Note that Phi(I) and Phi(S) are the sequences defined as in the manual. Moreover, 
the function does not check neither that I is an information set for C, nor S or 
Phi(S) is an s-PD-set for Cbin with respect to Phi(I), nor s <= t.
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require not(zero_Code(C)): "Code cannot be the zero code";
    requirege s, 1;
    
    k := #I;
    n := Length(C);
    require (k ge 1): "Argument 2 cannot be an empty sequence";
    require (Min(I) ge 1) and (Max(I) le n): 
                                    "Argument 2 should be a subset of", [1..n]; 
                                                                         
    require not IsEmpty(S): "Argument 3 cannot be an empty sequence";   
	nbin := 2*n; 
    numSymG := Degree(Parent(S[1]));  
    require ((numSymG eq n) or (numSymG eq nbin)): 
          "Argument 3 should contain permutations acting on a set of cardinality", 
                                                                    n, "or", nbin;
                                                                    
    require (BaseRing(u) eq GF(2)): "Argument 4 must be a vector over GF(2)";
    require (Degree(u) eq nbin): "Argument 4 must be of length", 2*n;	
    
	SZ2, pZ2, invpZ2, fbin, IZ2, grayMapC, invGrayMapC, identitySym := 
                       PermutationDecodeInitialization(C, I, S, n, k, numSymG);

    return PermutationDecodeAlg(C, SZ2, s, u, pZ2, invpZ2, fbin, IZ2, 
                             grayMapC, invGrayMapC, identitySym);

end intrinsic;

/****************************************************************/
intrinsic PermutationDecode(C::CodeLinRng, I::[RngIntElt], S::[GrpPermElt], 
          s::RngIntElt, u::ModTupRngElt) -> BoolElt, ModTupRngElt, ModTupFldElt
{
Given a code C over Z4 of length n and type 2^gamma 4^delta; an information set 
I=[i_1,...,i_(gamma+delta)] in [1,...,n] for C as a sequence of coordinate 
positions, such that the code C punctured on [1,...,n] minus [i_(gamma+1),...,
i_(gamma+delta)] is of type 4^delta; a sequence S such that either S or Phi(S) 
is an s-PD-set for Cbin=Phi(C), where Phi is the Gray map, with respect to Phi(I); 
an integer s in [1,...,t], where t is the error-correcting capability of Cbin; 
and a vector u from the ambient space V=Z4^n, attempt to decode u 
with respect to C. If the decoding algorithm succeeds in computing a vector u' 
in C as the decoded version of u in V, then the function returns true, u' and  
Phi(u'). If the decoding algorithm does not succeed in decoding u, then the 
function returns false, the zero vector in V and the zero vector in V2.

The permutation decoding algorithm consists of moving all errors in a received 
vector Phi(u)=c+e, where u in V, c in Cbin and e in V2 is the error vector with 
at most t errors, out of the information positions, that is, moving the nonzero 
coordinates of e out of the information set Phi(I) for Cbin, by using an 
automorphism of Cbin.

Note that Phi(I) and Phi(S) are the sequences defined as in the manual. Moreover, 
the function does not check neither that I is an information set for C, nor S or 
Phi(S) is an s-PD-set for Cbin with respect to Phi(I), nor s <= t.
}                                                                  
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require not(zero_Code(C)): "Code cannot be the zero code";
    requirege s, 1;
    
    k := #I;
    n := Length(C);
    require (k ge 1): "Argument 2 cannot be an empty sequence";
    require (Min(I) ge 1) and (Max(I) le n): 
                                    "Argument 2 should be a subset of", [1..n]; 
                                                                         
    require not IsEmpty(S): "Argument 3 cannot be an empty sequence";   
	nbin := 2*n; 
    numSymG := Degree(Parent(S[1]));  
    require ((numSymG eq n) or (numSymG eq nbin)): 
          "Argument 3 should contain permutations acting on a set of cardinality", 
                                                                    n, "or", nbin;
    
    require (BaseRing(u) eq Z4): "Argument 4 must be a vector over Z4";
    require (Degree(u) eq n): "Argument 4 must be of length", n;     
 
    SZ2, pZ2, invpZ2, fbin, IZ2, grayMapC, invGrayMapC, identitySym := 
                         PermutationDecodeInitialization(C, I, S, n, k, numSymG);

    ubin := GrayMap(UniverseCode(Z4, n))(u);
    
    return PermutationDecodeAlg(C, SZ2, s, ubin, pZ2, invpZ2, fbin, IZ2, 
                             grayMapC, invGrayMapC, identitySym);
 
end intrinsic;

/****************************************************************/
intrinsic PermutationDecode(C::CodeLinRng, I::[RngIntElt], S::[GrpPermElt], 
          s::RngIntElt, Q::[ModTupFldElt]) -> SeqEnum[BoolElt], SeqEnum[ModTupRngElt], 
          SeqEnum[ModTupFldElt]
{
Given a code C over Z4 of length n and type 2^gamma 4^delta; an information set 
I=[i_1,..., i_(gamma+delta)] in [1,...,n] for C as a sequence of coordinate 
positions, such that the code C punctured on [1,...,n] minus [i_(gamma+1),...,
i_(gamma+delta)] is of type 4^delta; a sequence S such that either S or Phi(S) 
is an s-PD-set for Cbin=Phi(C), where Phi is the Gray map, with respect to Phi(I); 
an integer s in [1,...,t], where t is the error-correcting capability of Cbin; 
and a sequence Q of vectors from the ambient space V2=Z2^(2*n), attempt to decode 
the vectors of Q with respect to C. This function is similar to the function 
PermutationDecode(C, I, S, s, u) except that rather than decoding a single vector, 
it decodes a sequence of vectors and returns a sequence of booleans and two 
sequences of decoded vectors corresponding to the given sequence. The algorithm 
used is as for the function PermutationDecode(C, I, S, s, u). 
}
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require not(zero_Code(C)): "Code cannot be the zero code";
    requirege s, 1;
    
    k := #I;
    n := Length(C);
    require (k ge 1): "Argument 2 cannot be an empty sequence";
    require (Min(I) ge 1) and (Max(I) le n): 
                                    "Argument 2 should be a subset of", [1..n]; 
                                                                         
    require not IsEmpty(S): "Argument 3 cannot be an empty sequence";   
    nbin := 2*n; 
    numSymG := Degree(Parent(S[1]));  
    require ((numSymG eq n) or (numSymG eq nbin)): 
          "Argument 3 should contain permutations acting on a set of cardinality", 
                                                                    n, "or", nbin;
      
    require not IsEmpty(Q): "Argument 4 cannot be an empty  sequence";                                                                
    require (BaseRing(Q[1]) eq GF(2)): "Argument 4 must contain vectors over GF(2)";
    require (Degree(Q[1]) eq nbin): "Argument 4 must contain vectors of length", 2*n;     
     
	SZ2, pZ2, invpZ2, fbin, IZ2, grayMapC, invGrayMapC, identitySym := 
                         PermutationDecodeInitialization(C, I, S, n, k, numSymG);

    isDecodedSeq := [];
    uDecodedSeq := [];
    ubinDecodedSeq := [];

    for u in Q do
       isDecoded, uDecoded, ubinDecoded := PermutationDecodeAlg(C, SZ2, s, u, pZ2, 
                          invpZ2, fbin, IZ2, grayMapC, invGrayMapC, identitySym);
       Append(~isDecodedSeq, isDecoded); 
       Append(~uDecodedSeq, uDecoded);
       Append(~ubinDecodedSeq, ubinDecoded); 
    end for;
    
    return isDecodedSeq, uDecodedSeq, ubinDecodedSeq;
 
end intrinsic;
 
/****************************************************************/
intrinsic PermutationDecode(C::CodeLinRng, I::[RngIntElt], S::[GrpPermElt], 
          s::RngIntElt, Q::[ModTupRngElt]) -> SeqEnum[BoolElt], SeqEnum[ModTupRngElt], 
          SeqEnum[ModTupFldElt]
{
Given a code C over Z4 of length n and type 2^gamma 4^delta; an information set 
I=[i_1,..., i_(gamma+delta)] in [1,...,n] for C as a sequence of coordinate 
positions, such that the code C punctured on [1,...,n] minus [i_(gamma+1),...,
i_(gamma+delta)] is of type 4^delta; a sequence S such that either S or Phi(S) 
is an s-PD-set for Cbin=Phi(C), where Phi is the Gray map, with respect to Phi(I); 
an integer s in [1,...,t], where t is the error-correcting capability of Cbin; 
and a sequence Q of vectors from the ambient space V=Z4^n, attempt to decode 
the vectors of Q with respect to C. This function is similar to the function 
PermutationDecode(C, I, S, s, u) except that rather than decoding a single vector, 
it decodes a sequence of vectors and returns a sequence of booleans and two 
sequences of decoded vectors corresponding to the given sequence. The algorithm 
used is as for the function PermutationDecode(C, I, S, s, u). 
}                                                                  
    require (BaseRing(C) eq Z4): "Code must be over Z4";
    require not(zero_Code(C)): "Code cannot be the zero code";
    requirege s, 1;
    
    k := #I;
    n := Length(C);
    require (k ge 1): "Argument 2 cannot be an empty sequence";
    require (Min(I) ge 1) and (Max(I) le n): 
                                    "Argument 2 should be a subset of", [1..n]; 
                                                                         
    require not IsEmpty(S): "Argument 3 cannot be an empty sequence";   
    nbin := 2*n; 
    numSymG := Degree(Parent(S[1]));  
    require ((numSymG eq n) or (numSymG eq nbin)): 
          "Argument 3 should contain permutations acting on a set of cardinality", 
                                                                    n, "or", nbin;
                                                                    
    require not IsEmpty(Q): "Argument 4 cannot be an empty sequence";    
    require (BaseRing(Q[1]) eq Z4): "Argument 4 must contain vectors over Z4";
    require (Degree(Q[1]) eq n): "Argument 4 must contain vectors of length", n;     
 

	SZ2, pZ2, invpZ2, fbin, IZ2, grayMapC, invGrayMapC, identitySym := 
                         PermutationDecodeInitialization(C, I, S, n, k, numSymG);

    isDecodedSeq := [];
    uDecodedSeq := [];
    ubinDecodedSeq := [];
    grayMap := GrayMap(UniverseCode(Z4, n));
    for u in Q do
       isDecoded, uDecoded, ubinDecoded := PermutationDecodeAlg(C, SZ2, s, 
         grayMap(u), pZ2, invpZ2, fbin, IZ2, grayMapC, invGrayMapC, identitySym);
       Append(~isDecodedSeq, isDecoded); 
       Append(~uDecodedSeq, uDecoded);
       Append(~ubinDecodedSeq, ubinDecoded); 
    end for;

    return isDecodedSeq, uDecodedSeq, ubinDecodedSeq;
 
end intrinsic;
 
/****************************************************************/
/*                                                              */  
/* Function name: MatrixToPermZ4                                */
/* Parameters: M, transG, colsG                                 */
/* Function description: Given a matrix M, the transpose of the */
/*   generator matrix G of the Hadamard code over Z4 of length  */
/*   n and type 2^gamma 4^delta, and a sequence with the colums */
/*   of G as rows, return the permutation in Sym(n) associated  */
/*   to M.                                                      */
/*                                                              */
/****************************************************************/
MatrixToPermZ4 := function(M, transG, colsG)
    n := #colsG;
    permGcol := transG*M;
    return Sym(n)![Position(colsG, permGcol[i]) : i in [1..n]];
end function;

/****************************************************************/
/*                                                              */  
/* Function name: InformationSetHadamardCodeZ4                  */
/* Parameters: gamma, delta                                     */
/* Function description: Given two integer numbers, gamma and   */
/*   delta, return the information set I for the Hadamard code  */
/*   C over Z4 of type 2^gamma 4^delta generated by G, where G  */
/*   is the matrix given by the HadamardCodeZ4 function. The    */
/*   information set corresponds to the columns given by e1+ei, */
/*   i in [1..delta], and e1+2ej j in [delta+1..gamma+delta].   */
/*   The function also returns an information set Ibin for the  */
/*   corresponding binary code Cbin=Phi(C).                     */           
/*                                                              */
/****************************************************************/
function InformationSetHadamardCodeZ4(gamma, delta)
    I := [2^(g + 2*delta - 3 ) + 1 : g in [1..gamma]] cat
                [1] cat [2^(2*d-4) + 1  : d in [2..delta]];
    Ibin := [2*I[i] - 1 : i in [1..gamma]] cat 
             &cat[ [2*I[i] - 1, 2*I[i]] : i in [gamma+1..gamma+delta]];
 
    return I, Ibin;
end function;

/****************************************************************/
/*                                                              */  
/* Function name: PDSetHadamardCodeZ4Determ                     */
/* Parameters: delta                                            */
/* Function description: Given an integer number, delta,        */
/*   construct a sequence of s+1 invertible matrices which give */
/*   an s-PD-set for the Hadamard code C over Z4 of             */
/*   type 2^gamma4^delta given by the HadamardCodeZ4 function.  */
/*   The function returns two sequences containing the          */
/*   permutations in Sym(n) and Sym(2n) associated to the       */
/*   sequence of invertible matrices. Finally, it also returns  */
/*   the sequence of s+1 invertible matrices, where             */
/*   s=floor((2^(2*delta-2)-delta)/delta).                      */ 
/*                                                              */
/* Remark: The set of s+1 matrices must satisfy the condition   */
/*         given in the paper "Partial permutation decoding for */
/*         binary linear and Z4-linear Hadamard codes" by R.    */
/*         Barrolleta and M. Villanueva, submitted to Designs,  */
/*         Codes and Cryptography, 2016. arXiv:1512.01839       */
/****************************************************************/
PDSetHadamardCodeZ4Determ := function(delta)
       
    s := Floor((2^(2*delta-2)-delta)/delta);
    m := delta-1;
       
    ZX<z> := PolynomialRing(Z);
    Z2X := PolynomialRing(Z2);
    Z4X := PolynomialRing(Z4);

    polyG := z^(2^m-1) - 1;
    factorsG := [w[1] : w in Factorization(Z2X!polyG)]; 
    henselfact := HenselLift(ZX!polyG, factorsG, Z4X);
    for i in [1..#henselfact] do
        polyF := henselfact[i];
        if Degree(polyF) eq m and (IsPrimitive(PolynomialRing(GF(2))!polyF)) then
            break;
        end if;
    end for;

    GR<a> := GaloisRing(4, ZX!polyF);
    T := [0] cat [a^i : i in [0..2^m-2]];
    R := [ ];	
    for b in T do
        Tb := [a + 2*b : a in T];
        R := R cat Tb;
    end for;

	zerocolumn := Matrix(Z4, delta, 1, [0^^delta]);
    PDSetMatricesInv := [ ];
    PDSetMatrices := [ ];
    for i in [0..s] do
		r := R[delta*i + 1];
		row := Matrix(Z4, [Eltseq(r)]);
        Bi := Matrix(Z4, [Eltseq(x) : x in [R[delta*i + j] - r : j in [2..delta]]]);
		Bi := HorizontalJoin(zerocolumn, VerticalJoin(row, Bi));
	    Bi[1][1] := 1;
        Append(~PDSetMatricesInv, Bi);
        Append(~PDSetMatrices, Bi^(-1));
    end for;

    // Construction of the corresponding permutations in Sym(n)
	_, G := HadamardCodeZ4(delta, 2*delta-1);
    transG := Transpose(G);
    colsG := [transG[i] : i in [1..2^(2*m)]];
    PDSetPermsZ4 := [MatrixToPermZ4(M, transG, colsG) : M in PDSetMatrices];

    // Construction of the corresponding permutations in Sym(2*n)
    PDSetPermsZ2 := [PermZ4ToPermZ2(permZ4) : permZ4 in PDSetPermsZ4];

    return PDSetPermsZ4, PDSetPermsZ2, PDSetMatrices;

end function;

/****************************************************************/
/*                                                              */  
/* Function name: FindPDSetHadamardCodeZ4Random                 */
/* Parameters: gamma, delta, allzero, V, GLZ4, GLZ2, s          */
/* Function description: Given two integer numbers, gamma and   */
/*   delta, the all-zero vector of length gamma+delta, a set of */
/*   vectors V, the general linear groups GL(delta-1,Z4) and    */
/*   GL(gamma, Z4), and an integer s, the function tries to find*/
/*   a sequence of s+1 invertible matrices fulfilling certain   */
/*   conditions. The function returns two parameters, first     */
/*   whether the sequence of matrices is found or not, and then */
/*   the found sequence. This function is called by the below   */
/*   function PDSetHadamardCodeZ4Random.                        */ 
/*                                                              */ 
/****************************************************************/ 
function FindPDSetHadamardCodeZ4Random(gamma, delta, allzero, V, GLZ4, GLZ2, s) 

    // Include the identity matrix to the final PDSet  
    Id := IdentityMatrix(Z4, delta+gamma);
    PDSetMatrices := [ Id ];

    // Include the rows of the (star) identity matrix to the sequence of (star) rows
    allStarRows := { Id[1] } join { Id[1] + Id[i] : i in [2..delta] } join
                               { Id[1] + 2*Id[i] : i in [delta+1..delta+gamma] };

    // Find a total of (s+1) matrices M from PAut
    repeat
        
        // Find a matrix M from PAut, having a (star) M with no rows in allStarRows 
        iniTime := Cputime();
        repeat
	            					
	    if gamma eq 0 then
	        M := HorizontalJoin(allzero, VerticalJoin(Random(V), Random(GLZ4)));
	    else			
	        BlockZ4 := HorizontalJoin(Random(GLZ4), 2*RandomMatrix(Z4, delta-1, gamma));
            BlockZ2 := HorizontalJoin(RandomMatrix(Z2, gamma, delta-1), Random(GLZ2));
            Block := VerticalJoin(BlockZ4, Matrix(Z4, BlockZ2));		
            M := HorizontalJoin(allzero, VerticalJoin(Random(V), Block));
	    end if;
	    M[1,1] := 1;

	    N := M^(-1);
        MStarRows := { N[1] } join { N[1] + N[i] : i in [2..delta] } join
                                { N[1] + 2*N[i] : i in [delta+1..delta+gamma] };
                                
        // Check whether the matrix M has the required property, that is, whether 
        // the rows of (star)M are all different and disjoint of allStarRows set
        Mfound := #MStarRows eq (gamma+delta) and IsDisjoint(allStarRows, MStarRows);
        if Mfound then
            allStarRows := allStarRows join MStarRows;
        end if;

        until Mfound or (Cputime(iniTime) gt MAXTIME);

        if Mfound then
            Append(~PDSetMatrices, M);
        else
            return false, PDSetMatrices;
        end if;     

    until #PDSetMatrices eq (s+1);
    
    return true, PDSetMatrices;

end function;

/****************************************************************/
/*                                                              */  
/* Function name: PDSetHadamardCodeZ4Random                     */
/* Parameters: gamma, delta                                     */
/* Function description: Given two integer numbers, gamma and   */
/*   delta, construct a sequence of s+1 invertible matrices     */
/*   which give an s-PD-set for the Hadamard code C over Z4 of  */
/*   type 2^gamma4^delta given by the HadamardCodeZ4 function.  */
/*   The function returns two sequences containing the          */
/*   permutations in Sym(n) and Sym(2n) associated to the       */
/*   sequence of invertible matrices.                           */
/*                                                              */  
/*   The function gives an s-PD-set of size s+1 such that       */
/*   floor((2^(2*delta-2)-delta)/delta) <= s <=                 */
/*   floor((2^(m-1)+delta-m-1)/(m+1-delta)). The function starts*/
/*   from the maximum value of s and decreases it when the      */
/*   s-PD-set is not found after a time out.                    */
/*   In case the parameter s=floor((2^(2*delta-2)-delta)/delta),*/
/*   the s-PD-set is constructed using the deterministic method.*/        
/*                                                              */
/* Remark: The set of s+1 matrices must satisfy the condition   */
/*         given in the paper "Partial permutation decoding for */
/*         binary linear and Z4-linear Hadamard codes" by R.D.  */
/*         Barrolleta and M. Villanueva, submitted to Designs,  */
/*         Codes and Cryptography, 2016. arXiv:1512.01839       */
/****************************************************************/
PDSetHadamardCodeZ4Random := function(gamma, delta)
		    	
    allzero := Matrix(Z4, delta+gamma, 1, [0^^delta+gamma]);
    GLZ4 := GL(delta-1, Z4);
    GLZ2 := (gamma ne 0) select GL(gamma, Z2) else 0;
    m := 2*delta + gamma - 1;

    // Construction of all vectors with delta-1 coordinates over Z4, and
    // gamma coordinates in {0,2} over Z4.
    mMinus := 2*(delta-1) + gamma - 1;
    _, GMinus := HadamardCodeZ4(delta-1, mMinus);
    transposeGMinus := Transpose(GMinus);
    V := [transposeGMinus[i] : i in [1..2^(mMinus-1)]];

    minimumS := Floor((2^(2*delta-2)-delta)/delta);
    maximumS := Floor((2^(m-1)+delta-m-1)/(m+1-delta)); 
    s := maximumS;
    while s gt minimumS do
        Mfound, PDSetMatrices := FindPDSetHadamardCodeZ4Random(gamma, delta, 
                                                     allzero, V, GLZ4, GLZ2, s); 
        if Mfound then 
            break;
        else
            s := s - 1;
        end if;
    end while;
    if s eq minimumS then
        S, Sbin := PDSetHadamardCodeZ4Determ(delta);  
		for j in [1..gamma] do
			S := [DoublePerm(p) : p in S]; 
			Sbin := [DoublePerm(pbin) : pbin in Sbin];
		end for;
    	return S, Sbin;
	end if;

    // Construction of the corresponding permutations in Sym(n)
    _, G := HadamardCodeZ4(delta, m);
    transG := Transpose(G);
    colsG := [transG[i] : i in [1..2^(m-1)]];
    PDSetPermsZ4 := [MatrixToPermZ4(M, transG, colsG) : M in PDSetMatrices];

    // Construction of the corresponding permutations in Sym(2*n)
    PDSetPermsZ2 := [PermZ4ToPermZ2(permZ4) : permZ4 in PDSetPermsZ4];

    return PDSetPermsZ4, PDSetPermsZ2, PDSetMatrices;

end function;

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
intrinsic PDSetHadamardCodeZ4(delta::RngIntElt, m::RngIntElt : AlgMethod := 
             "Deterministic") -> SeqEnum[RngIntElt], SeqEnum[GrpPermElt],
             SeqEnum[RngIntElt], SeqEnum[GrpPermElt], SeqEnum[AlgMatElt]
{
Given an integer m >= 5 and an integer delta such that 3 <= delta <= floor((m+1)/2),
the Hadamard code C over Z4 of length n=2^(m-1) and type 2^gamma 4^delta, where 
gamma=m+1-2*delta, given by the function HadamardCodeZ4(delta, m) is considered. 
The function returns an information set I=[i_1,...,i_(gamma+delta)] subseteq [1,...,n] 
for C together  with a subset S of the permutation automorphism group of C such that 
Phi(S) is an s-PD-set for Cbin=Phi(C) with respect to Phi(I), where Phi is the Gray map 
and Phi(I) and Phi(S) are defined in the manual. The function also returns the 
information set Phi(I) and the s-PD-set Phi(S). For m >= 1 and 1 <= delta 2, 
the Gray map image of C is linear and it is possible to find an s-PD-set for 
Cbin=Phi(C), for any s <= floor(2^(m)/(m+1))-1, by using the function 
PDSetHadamardCode(m).

The information sets I and Phi(I) are returned as sequences of gamma+delta and 
gamma+2*delta integers, giving the coordinate positions that correspond to the 
information sets for C and Cbin, respectively. The sets S and Phi(S) are also 
returned as sequences of elements in the symmetric groups Sym(n) and Sym(2*n) of 
permutations on the set [1,...,n] and [1,...,2*n], respectively. The s-PD-set S 
contains the s+1 permutations described in [BaVi16a]. 

A deterministic algorithm is used by default. In this case, the function returns 
the s-PD-set of size s+1 with s=floor((2^(2*delta-2)-delta)/delta), which is the 
maximum value of s when gamma=0, as described in [BaVi16a]. If the parameter AlgMethod 
is assigned the value "Nondeterministic", the function tries to improve the previous 
result giving an s-PD-set of size s+1 such that floor((2^(2*delta-2)-delta)/delta)
<= s <= floor((2^(m-1)+delta-m-1)/(m+1-delta)). In this case, the function starts 
from the maximum value of s and decreases it when the s-PD-set is not found after 
a time out.

[BaVi16a] R. Barrolleta and M. Villanueva, "Partial permutation decoding for binary 
linear and Z4-linear Hadamard codes," submitted to Designs, Codes and Cryptography, 
2016. arXiv:1512.01839
}
    requirege m, 5;
	requirerange delta, 3, (m+1) div 2;
    
    gamma := m+1-2*delta;
    I, Ibin := InformationSetHadamardCodeZ4(gamma, delta);
    
    if AlgMethod eq "Deterministic" then
        if gamma eq 0 then	
            S, Sbin, SMat := PDSetHadamardCodeZ4Determ(delta);
            return I, S, Ibin, Sbin, SMat;
        else 
            S, Sbin := PDSetHadamardCodeZ4Determ(delta); 
			for j in [1..gamma] do
				S := [DoublePerm(p) : p in S]; 
				Sbin := [DoublePerm(pbin) : pbin in Sbin];
			end for;
            return I, S, Ibin, Sbin;
        end if;
    else  
       S, Sbin, SMat := PDSetHadamardCodeZ4Random(gamma, delta);
       return I, S, Ibin, Sbin, SMat;
    end if;
    
end intrinsic;

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
intrinsic PDSetKerdockCodeZ4(m::RngIntElt) -> SeqEnum[RngIntElt], 
            SeqEnum[GrpPermElt], SeqEnum[RngIntElt], SeqEnum[GrpPermElt]
{
Given an integer m >=4 such that 2^m-1 is not a prime number, the Kerdock code 
C over Z4 of length n=2^m and type 4^(m-1), given by the function KerdockCodeZ4(m) 
is considered. The function returns the information set I=[1,..,m+1] in [1,...,n] 
for C together with a subset S of the permutation automorphism group of C such 
that Phi(S) is an s-PD-set for Cbin=Phi(C) with respect to Phi(I), where Phi is 
the Gray map and Phi(I) and Phi(S) are defined in the manual. The function also
returns the information set Phi(I)=[1,..,2m+2] and the s-PD-set Phi(S). The size 
of the s-PD-set S is always lambda=s+1, where lambda is the greatest divisor of 
2^m-1 such that lambda <= 2^m/(m+1).

The information sets I and Phi(I) are returned as sequences of m+1 and 
2m+2 integers, giving the coordinate positions that correspond to the 
information sets for C and Cbin, respectively. The sets S and Phi(S) are also 
returned as sequences of elements in the symmetric groups Sym(n) and Sym(2*n) of 
permutations on the set [1,...,n] and [1,...,2*n], respectively. The s-PD-set
S contains the s+1 permutations described in [BaVi16b].

[BaVi16b] R. Barrolleta and M. Villanueva, "PD-sets for Z4-linear codes: Hadamard 
and Kerdock codes," in Proceedings of the IEEE International Symposium on Information 
Theory, 2016.
}
    requirege m, 4;
    require (not IsPrime(2^m-1)): "2^m-1 must not be a prime number";

	n := 2^m;
	K := KerdockCode(m);

    // Find the greatest divisor of n-1 such that it is <= n/(m+1)
    lambdaBound := Floor(n/(m+1));
	divisorsSeq := Divisors(n-1); 
    for i in [1..#divisorsSeq] do	
        if divisorsSeq[i] gt lambdaBound then
			lambda := divisorsSeq[i-1];
            break;
        end if;
    end for;
	mu := Integers()!((n-1)/lambda);

    // Construct the s-PD-set of size lambda = s+1
    perm := Sym(n)!([2..n-1] cat [1, n]);
	S := [perm^(i*mu) : i in [1..lambda]];
	Sbin := [PermZ4ToPermZ2(tau) : tau in S];

	return [1..m+1], S, [1..2*m+2], Sbin;

end intrinsic;

