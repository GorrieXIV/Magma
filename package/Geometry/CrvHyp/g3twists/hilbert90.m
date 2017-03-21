freeze;

/***
 *  Mini Toolboox for descending a hyperelliptic curve onto twists defined
 *  over its field of moduli (finite fields)
 *
 *  Distributed under the terms of the GNU Lesser General Public License (L-GPL)
 *                  http://www.gnu.org/licenses/
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation; either version 2.1 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 *  Copyright 2011, R. Lercier & C. Ritzenthaler
 */

function MConj(M, sigma)
    return Matrix([[sigma(M[1,1]), sigma(M[1,2])],
	[sigma(M[2,1]), sigma(M[2,2])]]);
end function;

function MNorm(M, sigma, ord_sigma)
    Mr := M;    
    for i:=1 to ord_sigma-1 do
	Mr := MConj(Mr, sigma) * M;
    end for;
    return Mr;
end function;

function MActOnC(f, degf, A)
    _X := Parent(f).1;
    fd  := Parent(f)!(Evaluate(f, (A[1,1]*_X + A[1,2]) / (A[2,1]*_X + A[2,2])) * (A[2,1]*_X + A[2,2])^degf);
    return fd;
end function;


function Glasby(_M, sigma, Fq)

   Fqe := CoefficientRing(_M); w := Fqe.1;
   e := Degree(Fqe, Fq);

   /* Computing M s.t the cocycle relation is true,
      that is Norm(M) eq 1 */
   R := MNorm(_M, sigma, e);
   if not IsScalar(R) or
      not ((R[1, 1] in Fq) and (R[2, 2] in Fq) and (R[1, 1] eq R[2, 2])) then
       "HUM, non scalar endomorphism found after conjugation, I give up...";
       return Parent(_M)!0;
   end if;

   ret, t := NormEquation(Fqe, Fq!R[1,1]);
   
   if ret ne true then
       "HUM, no solution to the norm equation, I give up...";
       return Parent(_M)!0;
   end if;
   
   M := (_M/t);

   /* Finding X */
   notinvertible:=true;
   while notinvertible do
       X := Matrix([[Random(Fqe), Random(Fqe)],[Random(Fqe), Random(Fqe)]]);
       Xb:=X;
       for i := 2 to e do
	   Xb := MConj(Xb, sigma) * M;
	   X := X + Xb;
       end for;
       if IsInvertible(X) then
	   notinvertible:=false;
       end if;
   end while;

//   M - MConj(X, sigma)^(-1) * X;
   
   return X;
end function;


intrinsic HyperellipticPolynomialTwists(f::RngUPolElt, n::RngIntElt) -> SeqEnum[RngUPolElt]
    {Found polynomials fp s.t. the curves y^2 = f(x) and y^2 = fp(x) are
    twisted each other.}
    
    /* Geometric isomorphisms */
    SF := SplittingField(f); FF := CoefficientRing(f);
    _, GeomIsom := IsGL2Equivalent(PolynomialRing(SF)!f, PolynomialRing(SF)!f, n);
    AutGrp := {@ Matrix(2, 2, M) : M in GeomIsom @};
    
    /* Galois Cohomology Classes */
    _, phi := AutomorphismGroup(ProjectiveSpace(SF, 1)); /* Undirectly PGL2 */

    tau := FrobeniusMap(SF, FF);
    FL1 := AutGrp; FL0 := [];
    while #FL1 gt 0 do
	V := FL1[1]; CUR := {@@};
	for B in FL1 do
	    for A in AutGrp do
		if phi(MConj(A, tau) * Matrix(V)) eq phi(B * A) then
		    CUR join:= {@ B @}; continue B;
		end if;
	    end for;
	end for;
	FL1 := FL1 diff CUR; Append(~FL0, CUR);
    end while;

    /* Computing a twist for each class */
    LTwists := [];
    for CUR in FL0 do

	/* Is the current representative equivalent to the identity ? */
	Mt := CUR[1];
//	""; "***";
//	"Starting from", Mt;"";
//	"#CUR is", #CUR;	
	if Identity(Parent(Mt)) in CUR then
	    Append(~LTwists, f); continue;
	end if;

	/* Otherwise, let us get its cohomologic order */
	tau := FrobeniusMap(SF, FF);
	MM := Mt; ord := 1;
	while not IsScalar(MM) or
	    not ((MM[1, 1] in FF) and (MM[2, 2] in FF) and (MM[1, 1] eq MM[2, 2])) do
	    ord +:= 1; MM :=  MConj(MM, tau)*Mt;
	end while;
	ord := LCM(Degree(SF), ord) div Degree(SF);
//	"Ord =", ord, "to be compared to", #GeomIsom div #CUR;

        /* Let us construct the right extension... */
	RF :=  ext<SF |  IrreduciblePolynomial(SF, ord)>;
	sigma := FrobeniusMap(RF, FF);

	/* ... and find the decomposition */
	A := Glasby(ChangeRing(Mt, RF), sigma, FF);
	
	if A eq 0 then /* Should not happen... */
	    "HUMM..., no rational model found .....";
	    "JI :=", ShiodaInvariants(f), ";";
	    continue;
	end if;

	/* And ftilde */
	ftilde  :=  MActOnC(ChangeRing(f, RF), n, A^(-1));
	ftilde /:= Coefficient(ftilde, Degree(ftilde));
	ftilde  := PolynomialRing(FF)!Eltseq(ftilde);
	
//	"Found", ftilde;
    
	Append(~LTwists, ftilde);

    end for;

    /* Computing the quadratic twists and check the non isomorphism */
    Twists := []; eps := PrimitiveElement(FF);
    for f in LTwists do
	Append(~Twists, f);
	fp := eps*f; _, list := IsGL2Equivalent(f, fp, n);
	for t in list do
	    g := MActOnC(f, n, Matrix(2, 2, t));
	    c := LeadingCoefficient(g)/LeadingCoefficient(fp);
	    fl, _ := IsSquare(c);
	    if fl then continue f; end if;
	end for;
	Append(~Twists, fp);
    end for;

//    #Twists, "polynomials finally found.";

    return Twists;
    
end intrinsic;
