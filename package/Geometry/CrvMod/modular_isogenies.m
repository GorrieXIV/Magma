freeze;
////////////////////////////////////////////////////////////////////////
//                                                                    //
//                      ELLIPTIC MODULAR ISOGENIES                    //
//                             David Kohel                            //
//                           September 2000                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "velu_isogenies.m" : VeluRecursion;
import "elkies.m" : ElkiesKernel;
import "lercier.m" : Lercier;

forward AtkinKernelPolynomial, AtkinCodomainCurve;
forward CanonicalKernelPolynomial, ClassicalKernelPolynomial;

////////////////////////////////////////////////////////////////////////
//                 MODULI POINTS FOR ELLIPTIC CURVES                  //
////////////////////////////////////////////////////////////////////////

intrinsic ModuliPoints(X::CrvMod,E::CrvEll) -> SeqEnum
    {Returns the sequence of points on X specifying isogenies
    of the elliptic curve E over its base field.}

    require Indices(X)[2..3] eq [1,1] :
        "Argument 1 must be a modular curve of type X_0(N).";
    require CanChangeUniverse([BaseRing(X)|],BaseRing(E)) :
        "Base ring of arguments are incompatible.";
    if ModelType(X) in {"Atkin","Canonical","Classical"} then
	j := jInvariant(E);
	P := PolynomialRing(BaseRing(E)); x := P.1;
	if IsAffine(X) then
	    f := Evaluate(Polynomial(X),[x,j]);
	    return [ X ! [x[1],j] : x in Roots(f) ];
	else
	    f := Evaluate(Polynomial(X),[x,j,1]);
	    return [ X ! [x[1],j,1] : x in Roots(f) ];
	end if;
    end if;
    require false : "Argument 1 must be a modular curve of type X_0(N).";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                  MODULAR KERNEL POLYNOMIALS                        //
////////////////////////////////////////////////////////////////////////

intrinsic SubgroupScheme(E::CrvEll,P::Pt) -> SchGrpEll
    {The subgroup scheme of E defined by the point P on a modular curve.}
    X0 := Scheme(P);
    model_type := ModelType(X0);
    K := BaseRing(E);
    require Characteristic(K) notin {2,3} :
        "The base ring of argument must not be of characteristic 2 or 3.";
    require K cmpeq Universe(Eltseq(P)) :
	"Arguments have incompatible base rings.";
    require Type(X0) eq CrvMod and not IsSingular(P) :
        "Argument 2 must be a nonsingular point on a modular curve.";
    require Indices(X0)[2..3] eq [1,1] :
	"The parent of argument 2 must be a modular curve of type X_0(N).";
    require model_type in {"Atkin","Canonical","Classical"} :
        "Model type of parent of argument 2 must be \"Atkin\", " *
        "\"Canonical\", or \"Classical\".";
    if model_type eq "Atkin" then
	require Level(X0) gt 2 :
   	    "Argument 2 must not be a point on an Atkin model of level 2.";
	psi := AtkinKernelPolynomial(E,P);
    elif model_type eq "Canonical" then
	psi := CanonicalKernelPolynomial(E,P);
    elif model_type eq "Classical" then
	psi := ClassicalKernelPolynomial(E,P);
    end if;
    return SubgroupScheme(E,psi);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                       MODULAR ISOGENIES                            //
////////////////////////////////////////////////////////////////////////

intrinsic Isogeny(E::CrvEll,P::Pt) -> Map
    {Returns the isogeny E -> F corresponding to the point P on the
    modular curve X_0(N).}

    X0 := Scheme(P);
    model_type := ModelType(X0);
    K := BaseRing(E);
    require Characteristic(K) notin {2,3} :
        "The base ring of argument must not be of characteristic 2 or 3.";
    require K cmpeq Universe(Eltseq(P)) :
	"Arguments have incompatible base rings.";
    require Type(X0) eq CrvMod and not IsSingular(P) :
        "Argument 2 must be a nonsingular point on a modular curve.";
    require Indices(X0)[2..3] eq [1,1] :
	"The parent of argument 2 must be a modular curve of type X_0(N).";
    require model_type in {"Atkin","Canonical","Classical"} :
        "Model type of parent of argument 2 must be \"Atkin\", " *
        "\"Canonical\", or \"Classical\".";

    if model_type eq "Atkin" then
	require Level(X0) gt 2 :
   	    "Argument 2 must not be a point on an Atkin model of level 2.";
	psi := AtkinKernelPolynomial(E,P);
    elif model_type eq "Canonical" then
	psi := CanonicalKernelPolynomial(E,P);
    elif model_type eq "Classical" then
	psi := ClassicalKernelPolynomial(E,P);
    end if;
W,m2:=WeierstrassModel(E);
idata:=IsomorphismData(Inverse(m2));
    F, m := IsogenyFromKernel(W,psi);
_,m3:=Transformation(F,idata);
    return m2*m*m3;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                     ATKIN MODULAR ISOGENIES                        //
////////////////////////////////////////////////////////////////////////

function AtkinKernelPolynomial(E,P)
   // The curve defined by the Velu isogeny of E defined by P.

   X0 := Scheme(P);
   u, j := Explode(Eltseq(P));
   error if jInvariant(E) ne j, "Argument 1 and 2 are inconsistent.";

   K := BaseRing(E);
   error if Characteristic(K) in {2,3}, "Argument 1 must be defined
       over a field of characteristic other than 2 or 3.";
   E1, m1 := WeierstrassModel(E);
   //a1,a2,a3,a4,a6 := Explode(aInvariants(E1));

   p := Level(X0);
   Phi := Polynomial(X0);
   PK := PolynomialRing(K);
   J := PK.1;
   if IsAffine(X0) then
       f := Evaluate(Polynomial(X0),[u,J]);
   else
       f := Evaluate(Polynomial(X0),[u,J,1]);
   end if;
   jCandidates := [ r[1] : r in Roots(f) | r[1] ne j or r[2] gt 1 ];
   vprint ModularCurve :
      "Candidate j-invariants of codomain curve:", jCandidates;
    success := false;
    for j_tilde in jCandidates do
	vprint ModularCurve : "Trying j-invariant", j_tilde;
	F1, p1, success := AtkinCodomainCurve(E1,p,Phi,u,j_tilde);
	if success then
	    vprint ModularCurve :
	        "Found codomain curve isomorphic to", F1;
	    psi, success := ElkiesKernel(E1,F1,p,p1);
	end if;
	if success then
	    vprint ModularCurve : "Correct involution image j-invariant";
	    break;
	else
	    vprint ModularCurve : "Continuing j-invariant loop.";
	end if;
    end for;
    error if not success, "Failed to find isogeny for Atkin model.";
    vprint ModularCurve : "Found kernel polynomial psi =", psi;

    i2 := IsomorphismData(m1);
    if (i2[1] ne 0) or (i2[4] ne 1) then
	psi := Evaluate(psi,(i2[4]^2)*(Parent(psi).1)+i2[1]);
	psi := Normalize(psi);
    end if;
    return psi;
    /*
    F2, m0 := IsogenyFromKernel(E1,psi);
    if F1 ne F2 then
	bool, m2 := IsIsomorphic(F2,F1);
	error if not bool,
	    "Failed codomain isomorphism in Atkin model isogeny.";
	F2 := F1;
        m0 := m0*m2;
    end if;
    i2 := IsomorphismData(Inverse(m1));
    _, m2 := Transformation(F2,i2);
    return m1*m0*m2;
    */
end function;

function AtkinCodomainCurve(E,p,Phi,u,j_tilde)
    // The isogeous curve F, and the sum of the x-coordinates
    // of the points in the kernel of the isogeny E -> F

    j := jInvariant(E);
    s := 12 div GCD(12, p-1);
    _, _, _, e4, e6 := Explode(Coefficients(E));

    E4 := -e4 / 3;       // set lambda = 1
    E6 := -e6 / 2;       // set lambda = 1

    P2 := Parent(Phi);
    ngens := Rank(P2);
    U := P2.1; J := P2.2;
    if ngens eq 2 then
	P := [u,j]; Q := [u,j_tilde];
    else
	P := [u,j,1]; Q := [u,j_tilde,1];
    end if;

    DuPhi := Derivative(Phi, U);
    DuuPhi := Derivative(DuPhi, U);
    DjPhi := Derivative(Phi, J);
    DjjPhi := Derivative(DjPhi, J);
    DujPhi := Derivative(DjPhi, U);

    Du := u * Evaluate(DuPhi, P);
    DuStar := u * Evaluate(DuPhi, Q);
    Dj := j * Evaluate(DjPhi, P);
    DjStar := p * j_tilde * Evaluate(DjPhi, Q);

    // Invalid state, so return.
    if DjStar eq 0 or Du eq 0 or E4 eq 0 then
	return E, 0, false;
    end if;

    u_prime := (u * E6 * Dj) / (E4 * Du);

    E4_tilde := (DuStar^2 * Dj^2 * E6^2 * j_tilde) /
		(DjStar^2 * Du^2 * E4^2 * (j_tilde - 1728));
    E6_tilde := (DuStar^3 * Dj^3 * E6^3 * j_tilde) /
		(DjStar^3 * Du^3 * E4^3 * (j_tilde - 1728));

    a_tilde := -3 * p^4 * E4_tilde;
    b_tilde := -2 * p^6 * E6_tilde;

    F := EllipticCurve([a_tilde,b_tilde]);

    pu := Evaluate(DuPhi, P);
    pj := Evaluate(DjPhi, P);
    puStar := Evaluate(DuPhi, Q);
    pjStar := Evaluate(DjPhi, Q);

    u1 := (1/pu) *
	  ( - u_prime * Evaluate(DuuPhi, P)
            + 2 * j * Evaluate(DujPhi, P) * E6 / E4
            - ( E6^2 / (u_prime * E4^2))
            *  ( j * pj  + j^2 * Evaluate(DjjPhi, P) ) )
          +  (E6 / (3 * E4)) - (E4^2 / (2 * E6));
    u2 := (1/puStar) *
	  ( - u_prime * Evaluate(DuuPhi, Q)
            + 2 * p * j_tilde * Evaluate(DujPhi, Q)
              * E6_tilde / E4_tilde
            - p^2 * (E6_tilde^2 / (u_prime * E4_tilde^2))
	      * (j_tilde * pjStar + j_tilde^2
              * Evaluate(DjjPhi, Q) ) )
            + p * ( E6_tilde / (3 * E4_tilde)
	            - E4_tilde^2 / (2 * E6_tilde) );
   p1 := (u1 - u2) * 6 * p / 2;
   return F, p1, true;
end function;

////////////////////////////////////////////////////////////////////////
//                   CANONICAL MODULAR ISOGENIES                      //
////////////////////////////////////////////////////////////////////////

function CanonicalKernelPolynomial(E,P)
    // The kernel polynomial of the isogeny of E defined by P.

    K := BaseRing(E);
    error if Characteristic(K) in {2,3}, "Argument 1 must be defined
	over a field of characteristic other than 2 or 3.";

    E1, m1 := WeierstrassModel(E);
    //_, _, _, a4, a6 := Explode(aInvariants(E1));

    X0 := Scheme(P);
    N := Level(X0);
    P := Eltseq(P);
    u, j := Explode(P);
    ngens := IsAffine(X0) select 2 else 3;
    PX := PolynomialRing(K,ngens);
    U := PX.1; J := PX.2;
    Psi := Evaluate(Polynomial(X0),(ngens eq 2) select [U,J] else [U,J,1]);

    error if jInvariant(E) ne j, "Argument 1 and 2 are inconsistent.";

    s := 12 div GCD(12, N-1);
    u_tilde := N^s / u; // Canonical involution.

    /*
    // Not reached -- this should determine the correct isogeny
    // provided there is a unique isogeny to the codomain curve
    // of this degree. 
    if Characteristic(K) eq 2 then
	PK := PolynomialRing(K); x := P.1;
	rts := Roots(Evaluate(Psi,[u_tilde,x]));
	for j_tilde in rts do
	    F := EllipticCurveWithjInvariant(j_tilde[1]);
	    bool, psi := Lercier(E,F,N);
	    if bool then break; end if;
	end for;
	error if not bool, "No kernel polynomial found in Lercier.";
	_, m := IsogenyFromKernel(E,psi);
	return DefiningSubschemePolynomial(m);
    end if;
    */

    DuPsi := Derivative(Psi, U);
    DuuPsi := u^2 * Derivative(DuPsi, U);
    DjPsi := Derivative(Psi, J);
    DujPsi := u * j * Derivative(DjPsi, U);
    DjjPsi := j^2 * Derivative(DjPsi, J);

    Du := u * Evaluate(DuPsi, P);
    Dj := j * Evaluate(DjPsi, P);
    Duu := Du + Evaluate(DuuPsi, P);
    Duj := Evaluate(DujPsi, P);
    Djj := Dj + Evaluate(DjjPsi, P);

    _, _, _, a4, a6 := Explode(Coefficients(E1));
    E4 := -a4 / 3; // set lambda = 1
    E6 := -a6 / 2; // set lambda = 1

    error if Du eq 0 or E4 eq 0,
        "Argument 1 is a singular point on the parent of argument 2.";

    E4_tilde := ( E4
        + ( (144 * Dj^2 * E6^2) / (s^2 * Du^2 * E4^2) )
	- ( (48 * Dj * E6^2) / (s * Du * E4^2) )
	- ( (288 * Dj * Duj * E6^2) / (s * Du^2 * E4^2) )
        + ( (144 * Djj * E6^2) / (s * Du * E4^2) )
        + ( (72 * Dj * E4) / (s * Du) )
        + ( (144 * Dj^2 * Duu * E6^2) / (s * Du^3 * E4^2) )
    ) / N^2;
    Delta := (E4^3 - E6^2)/1728;
    Delta_tilde := u^(12 div s) * Delta / N^12;

    j_tilde := E4_tilde^3 / Delta_tilde;

    error if j_tilde eq 0, "Codomain must not have j-invariant 0.";

    if ngens eq 2 then
	Q := [u_tilde,j_tilde];
    else
	Q := [u_tilde,j_tilde,1];
    end if;

    E6_tilde := (-E4_tilde) * ( u_tilde * Evaluate(DuPsi, Q) * Dj * E6 ) /
        ( N * j_tilde * Evaluate(DjPsi, Q) * Du * E4 );

    a_tilde := -3 * N^4 * E4_tilde;
    b_tilde := -2 * N^6 * E6_tilde;

    F1 := EllipticCurve([a_tilde, b_tilde]);

    p1 := (6 * N * E6 * Dj) / (s * E4 * Du);

    psi := ElkiesKernel(E1,F1,N,p1);
    i2 := IsomorphismData(m1);
    if (i2[1] ne 0) or (i2[4] ne 1) then
	psi := Evaluate(psi,(i2[4]^2)*(Parent(psi).1)+i2[1]);
	psi := Normalize(psi);
    end if;
    return psi;
    /*
    F2, m0 := IsogenyFromKernel(E1,psi);
    if F1 ne F2 then
	bool, m2 := IsIsomorphic(F2,F1);
	error if not bool,
	    "Failed codomain isomorphism in canonical model isogeny.";
	F2 := F1;
        m0 := m0*m2;
    end if;
    i2 := IsomorphismData(Inverse(m1));
    _, m2 := Transformation(F2,i2);
    return m1*m0*m2;
    */
end function;

////////////////////////////////////////////////////////////////////////
//                   CLASSICAL MODULAR ISOGENIES                      //
////////////////////////////////////////////////////////////////////////

function ClassicalKernelPolynomial(E,P)
    // The kernel polynomial of the isogeny of E defined by P.

    X0 := Scheme(P);
    p := Level(X0);
    Phi := Polynomial(X0);
    j_p, j := Explode(Eltseq(P));
    error if jInvariant(E) ne j, "Argument 1 and 2 are inconsistent.";
    K := BaseRing(E);
    error if Characteristic(K) in {2,3}, "Argument 1 must be defined
	over a field of characteristic other than 2 or 3.";

    E1, m1 := WeierstrassModel(E);
    //_, _, _, a4, a6 := Explode(aInvariants(E1));


    /*
    // Not reached -- this should determine the correct isogeny
    // provided there is a unique isogeny to the codomain curve
    // of this degree. 
    if Characteristic(K) eq 2 then
	F := EllipticCurveWithjInvariant(j_p);
	bool, psi := Lercier(E,F,p);
	error if not bool, "Failed to find kernel polynomial in Lercier.";
	F, m := IsogenyFromKernel(E,psi);
	return DefiningSubschemePolynomial(m);
    end if;
    */
    E4, E6 := Explode(cInvariants(E));
    error if j eq 0,
	"Domain curve must not have j-invariant 0.";
    error if j eq 12^3,
	"Domain curve must not have j-invariant 12^3.";
    error if j_p eq 0,
	"Codomain curve must not have j-invariant 0.";
    error if j_p eq 12^3,
	"Codomain curve must not have j-invariant 12^3.";
    error if Characteristic(BaseRing(E)) in {2,3},
	"Argument 1 must be defined over a field " *
	"of characteristic different from 2 and 3.";

    P2 := Parent(Phi);
    X := P2.1; Y := P2.2;
    DxPhi := Derivative(Phi, X);

    DxPhiJJ := Evaluate(DxPhi, [j,j_p]);
    DyPhiJJ := Evaluate(DxPhi, [j_p,j]);
    error if DyPhiJJ eq 0,
        "Argument 1 must not be a singularity of curve model.";

    j_prime := -E6*j/E4;
    j_p_prime := -j_prime*DxPhiJJ/(p*DyPhiJJ);

    lambda := -j_p_prime/j_p;
    E4_p := lambda^2*j_p/(j_p-12^3);
    E6_p := lambda*E4_p;

    DxxPhi := Derivative(DxPhi, X);
    DxyPhi := Derivative(DxPhi, Y);

    DxxPhiJJ := Evaluate(DxxPhi, [j,j_p]);
    DxyPhiJJ := Evaluate(DxyPhi, [j,j_p]);
    DyyPhiJJ := Evaluate(DxxPhi, [j_p,j]);

    j_pp := -( j_prime^2*DxxPhiJJ +
               2*p*j_prime*j_p_prime*DxyPhiJJ +
               p^2*j_p_prime^2*DyyPhiJJ ) / (j_prime*DxPhiJJ);
    c2 := 6*j_pp + (3*E4^3 + 4*E6^2)/(E4*E6)
	         - p * (3*E4_p^3 + 4*E6_p^2)/(E4_p*E6_p);

    F1 := EllipticCurve([-p^4*E4_p/48,-p^6*E6_p/864]);

    if p ne 2 then
	psi, bool := ElkiesKernel(E1,F1,p,-p*c2/24);
	error if not bool, "Failure in Elkies kernel.";
    else
	psi := PolynomialRing(K)![p*c2/12,1];
    end if;

    i2 := IsomorphismData(m1);
    if (i2[1] ne 0) or (i2[4] ne 1) then
	psi := Evaluate(psi,(i2[4]^2)*(Parent(psi).1)+i2[1]);
	psi := Normalize(psi);
    end if;
    return psi;
    /*
    F2, m0 := IsogenyFromKernel(E1,psi);
    if F1 ne F2 then
	bool, m2 := IsIsomorphic(F2,F1);
	error if not bool,
	    "Failed codomain isomorphism in classical model isogeny.";
	F2 := F1;
        m0 := m0*m2;
    end if;
    i2 := IsomorphismData(Inverse(m1));
    _, m2 := Transformation(F2,i2);
    return m1*m0*m2;
    */
end function;
