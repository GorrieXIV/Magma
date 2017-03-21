freeze;

/***************************************************************  
   Local representations on GL_2(Q_p)
   
   Jared Weinstein, May 2009
***************************************************************/

declare type RepLoc;

import "../ModSym/twist.m" : associated_newspace;

import "LocalComp.m" : CI_space, CI_rep, CI_datum_provisional, 
                       CI_datum, CIDatumToAdmissiblePair;

/***************************************************************  
  Attributes for RepLoc 
***************************************************************/

declare verbose RepLoc, 2;

declare attributes RepLoc : 
        p,                        // representation is on GL(Q_p)
        type,                     // description of representation (eg, "Supercuspidal")
	CentralCharacter,         // central character of representation, given as a GrpDrchElt
 	ModSymSpace,              // modular symbols space from which rep was created
	IsMinimal,                // false iff some twist of the rep has lower conductor
	MinimalModSymSpace,       // modular symbols space corresponding to minimal twist of rep
	Conductor,                // conductor of representation
	MinimalConductor,         // least conductor of a twist of rep
	TwistingCharacter,	  // character which realizes this least conductor
	CuspidalInducingDatum,    
	AdmissiblePair,
	PrincipalSeriesParameters; 
	

/***************************************************************  
  Compulsory hackobj intrinsics for RepLoc
***************************************************************/

intrinsic Print(x::RepLoc, level::MonStgElt) {}
   printf "%o Representation of GL(2,Q_%o)", x`type, x`p;
   if level eq "Maximal" then
      if assigned x`ModSymSpace then
         printf " associated to %o", x`ModSymSpace;
      end if;
   end if;
end intrinsic;

intrinsic IsCoercible(x::RepLoc, y::.) -> BoolElt, . {}
   return false, "Illegal coercion"; // coercion doesn't make sense
end intrinsic;

intrinsic 'in'(x::., y::RepLoc) -> BoolElt
{}
   return false; // no need to implement 'in'
end intrinsic;


/***************************************************************  
   Access
***************************************************************/

intrinsic Conductor(x::RepLoc) -> RngIntElt
{Returns the conductor of x, written multiplicatively.}
	return x`Conductor;
end intrinsic;

intrinsic DefiningModularSymbolsSpace(x::RepLoc) -> ModSym
{Returns the space of modular symbols from which x was created.}
	return x`ModSymSpace;
end intrinsic;

intrinsic CentralCharacter(x::RepLoc) -> GrpDrchElt
{Returns the central character of x.  This is a Dirichlet character of p-power conductor}
	chi:=x`CentralCharacter;
	return chi;
end intrinsic;

/***************************************************************  
   Creation
***************************************************************/

function p_part_of_chi(chi,p)
        N:=Conductor(chi);
        o:=Valuation(N,p);
        if o eq 0 then
                return DirichletGroup(1)!1;
        end if;
        D:=Decomposition(chi);
        chi_p:=[chi_test : chi_test in D | Conductor(chi_test) mod p eq 0][1];
        return chi_p;
end function;


function TypeOfMinimalRep(M,p)
	N:=Level(M);
        e:=Valuation(N,p);
	if e eq 0 then
		return "Unramified Principal Series";    
	elif e eq 1 then
		chi:=DirichletCharacter(M);
		if Conductor(chi) mod p ne 0 then
			return "Steinberg";
		else 
                        return "Ramified Principal Series";
		end if;
	else
		chi:=DirichletCharacter(M);
		if Valuation(Conductor(chi),p) eq Valuation(N,p) then
			return "Ramified Principal Series";
		else 
                        return "Supercuspidal";
		end if; 
	end if;
end function;


intrinsic LocalComponent(M::ModSym, p::RngIntElt : CheckMinimal:=true) -> RepLoc
{Creates p-local component attached to this newform (or Galois orbit of newforms)}
   
	require IsPrime(p) : "The second argument must be prime";
	require IsCuspidal(M) : "The first argument must be cuspidal";
	require #NewformDecomposition(M) eq 1 : 
                "The first argument must be an irreducible Hecke module";
/*
        M := associated_newspace(M);
        assert not IsMultiChar(M);
*/
	rep := New(RepLoc);  // blank object 
	rep`ModSymSpace:=M;
	rep`p := p;  

        if CheckMinimal then
	   is_minimal,M_minimal,chi:=IsMinimalTwist(M,p);
        else
           is_minimal:=true;
           M_minimal:=M;
           chi:=DirichletGroup(1)!1;
        end if;

	rep`IsMinimal:=is_minimal;
	rep`MinimalModSymSpace:=M_minimal;
	rep`TwistingCharacter:=chi;

	rep`type:=TypeOfMinimalRep(M_minimal,p);
	rep`CentralCharacter := p_part_of_chi(DirichletCharacter(M),p);
	rep`Conductor := p^(Valuation(Level(M),p));
	rep`MinimalConductor := p^(Valuation(Level(M_minimal),p));

        return rep;
end intrinsic;



/***************************************************************  
   Main intrinsics
***************************************************************/

intrinsic IsMinimal(pi::RepLoc) -> BoolElt, GrpDrchElt, RepLoc
{Given a representation pi of GL_2(Q_p), returns true if the conductor of pi 
cannot be lowered by twisting by a character of Q_p^*.  If false, also returns 
a minimal representation and a Dirichlet character whose product is pi.}

	if pi`IsMinimal then
		return true,_,_;
	end if;

	pi_minimal:=New(RepLoc);
	pi_minimal`ModSymSpace:=pi`MinimalModSymSpace;
	pi_minimal`MinimalModSymSpace:=pi_minimal`ModSymSpace;
	pi_minimal`p:=pi`p;
	pi_minimal`IsMinimal:=true;
	pi_minimal`type:=pi`type;	
	pi_minimal`CentralCharacter:=p_part_of_chi(DirichletCharacter(pi_minimal`ModSymSpace),pi`p);
	pi_minimal`Conductor:=pi`MinimalConductor;
	pi_minimal`MinimalConductor:=pi_minimal`Conductor;
	pi_minimal`TwistingCharacter:=DirichletGroup(1)!1;
	chi:=pi`TwistingCharacter;

	return false,pi_minimal,chi;
end intrinsic;
	
intrinsic IsPrincipalSeries(pi::RepLoc) -> BoolElt
{Returns true if argument is a principal series representation}

	pi_type:=pi`type;
        return pi_type eq "Ramified Principal Series" or pi_type eq "Unramified Principal Series";
end intrinsic;

intrinsic PrincipalSeriesParameters(pi::RepLoc) -> GrpDrchElt, GrpDrchElt
{Given a principal series representation pi of GL_2(Q_p), returns two Dirichlet characters of p-power conductor
which represent the restriction to Z_p^* x Z_p^* of the character of the split torus of GL_2(Q_p) associated to pi.}

	require IsPrincipalSeries(pi): "Argument must be a principal series representation";

	if assigned pi`PrincipalSeriesParameters then 
           return pi`PrincipalSeriesParameters; 
        end if;

        chi1:=pi`TwistingCharacter;
        chi2:=chi1*p_part_of_chi(DirichletCharacter(pi`MinimalModSymSpace),pi`p);
        order:=LCM(Order(chi1),Order(chi2));
        K:=CyclotomicField(order);
        G:=DirichletGroup(pi`Conductor,K);
        pi`PrincipalSeriesParameters:=[G!chi1,G!chi2];

	return pi`PrincipalSeriesParameters;
end intrinsic;

intrinsic IsSupercuspidal(pi::RepLoc) -> BoolElt
{Given a representation pi of GL_2(Q_p), decides if pi is supercuspidal}

        return pi`type eq "Supercuspidal";
end intrinsic;


intrinsic CuspidalInducingDatum(pi::RepLoc) -> ModGrp
{Given a minimal supercuspidal representation pi of GL_2(Q_p), 
returns a cuspidal inducing datum which gives rise to pi.}

	if assigned pi`CuspidalInducingDatum then 
                return pi`CuspidalInducingDatum; 
        end if;

	require IsSupercuspidal(pi): "Argument must be a supercuspidal representation";
	require IsMinimal(pi): "Argument must be a minimal representation";

	p:=pi`p;
	M:=pi`ModSymSpace;
	pi`CuspidalInducingDatum:= CI_datum(M,p);

	return pi`CuspidalInducingDatum;
end intrinsic;
	
intrinsic AdmissiblePair(pi::RepLoc) -> RngPad, Map
{Given an ordinary minimal supercuspidal representation of GL_2(Q_p), 
returns the associated admissible pair (E,chi), where E/Q_p is a quadratic 
field extension and chi is a character of the unit group of E.}

	if assigned pi`AdmissiblePair then
		return Explode(pi`AdmissiblePair);
	end if;

	require IsSupercuspidal(pi): "Argument must be a supercuspidal representation";
	require IsMinimal(pi): "Argument must be a minimal representation";

        require IsOdd(pi`p) or IsEven(Valuation(Conductor(pi),pi`p)):
                "Admissible pair does not exist for p = 2 and odd conductor";

	E,chi:=CIDatumToAdmissiblePair(CuspidalInducingDatum(pi));
        pi`AdmissiblePair := [* E, chi *];

	return E,chi;
end intrinsic;

/* OLD VERSION
intrinsic GaloisRepresentation(pi::RepLoc : Precision:=10) -> GrpPerm, Map, RngPad, ModGrp
{Given a minimal representation pi of GL_2(Q_p), returns the representation of 
the Weil group associated to pi under the local Langlands correspondence}

        return WeilRepresentation(pi : Precision:=Precision);
end intrinsic;

intrinsic WeilRepresentation(pi::RepLoc : Precision:=10) -> GrpPerm, Map, RngPad, ModGrp
{"} // "
	p:=pi`p;

	if IsPrincipalSeries(pi) then

		chi1,chi2:=Explode(PrincipalSeriesParameters(pi));
		P:=LCM(Conductor(chi1),Conductor(chi2));
		K:=CyclotomicField(EulerPhi(P));
		Zp:=pAdicRing(p,Precision);
		S := PolynomialRing(Zp); X := S.1;
		f:=S!CyclotomicPolynomial(P);
		g:=Evaluate(f,X+1);
		L:=ext<Zp|g>;
		G,m:=AutomorphismGroup(L);
                Z:=Integers();
                rep_values:=[Matrix(2,[chi1(x),0,0,chi2(x)])
                              where x is Z!Coefficients(m(G.i)(L.1))[2]
                            : i in [1..Ngens(G)]];
		return G,m,L,GModule(G,rep_values);

	elif IsSupercuspidal(pi) then

//Let R,chi be the data returned by "Admissible Pair", so that R/Z_p is quadratic and
//chi is a character of R^*.  We produce the extension F of R cut out by chi by
//local class field theory.

	        require IsMinimal(pi): "Argument must be a minimal representation (if supercuspidal)";
		R,chi:=AdmissiblePair(pi);
		U,m:=UnitGroup(R);
		K:=Parent(chi(R!1));
		Tcyc,mcyc:=UnitGroup(K);
		theta:=hom< U -> Tcyc | [chi(m(U.i)) @@ mcyc : i in [1..Ngens(U)]]>;
		H:=Kernel(theta);
		E:=FieldOfFractions(R);
		Qp:=BaseField(E);
		UE,mE:=UnitGroup(E);
		Hgens:=[m(H.i) @@ mE: i in [1..Ngens(H)]];
		if IsRamified(E) then
			KernelTheta:=sub<UE | Append(Hgens, E.1 @@ mE)>;		
		else 
                        KernelTheta:=sub<UE | Append(Hgens,p @@ mE)>;
		end if;
		F:=ClassField(mE, KernelTheta);
		O_F:=Integers(F);
		O_F_nice,m_nice:=AbsoluteTotallyRamifiedExtension(O_F);
		F_nice:=FieldOfFractions(O_F_nice);
		B,mB:=AutomorphismGroup(O_F_nice);
		pol:=DefiningPolynomial(E);
		pol_F_nice:=ChangeRing(pol,F_nice);
		E_root:=Roots(pol_F_nice)[1][1];
                // We have an exact sequence 
                //    1->A=Gal(F/E)->B=Gal(F/Q_p)->C=Gal(E/Q_p)->1
                // Need to realize A as a subgroup of B 
		elts:=[];
		for b in B do
			if mB(b)(E_root) eq mB(B!1)(E_root) then
				elts:=Append(elts,b);
			end if;
		end for;
		A:=sub<B|elts>;
		Aab,map:=AbelianGroup(A);
		mu:=Order(A);

		L:=CyclotomicField(mu); 
                if mu eq 1 then
		        Aab:=AbelianGroup([1]);
                        map := map * hom<Codomain(map)->Aab|>;
                end if;
		CharOnAab:=Character(GModule(Aab,[Matrix(1,[L.1])]));
		rep_values:=[Matrix(1,[CharOnAab(map(A.i))]):i in [1..Ngens(A)]];
		CharOnA:=GModule(A,rep_values);
		WeilRep:=Induction(CharOnA,B);
		return B,mB,F_nice,WeilRep;

        else

                assert pi`type eq "Steinberg";
                require false: "Not implemented for Steinberg representations";

	end if;
end intrinsic;
*/


intrinsic GaloisRepresentation(pi::RepLoc : Precision:=10) -> GalRep
{Given a minimal representation pi of GL_2(Q_p), returns the representation rho of 
the Weil group associated to pi under the local Langlands correspondence.
In the current implementation, the representation this returns only agrees with
rho on inertia.
}
        return WeilRepresentation(pi : Precision:=Precision);
end intrinsic;


intrinsic WeilRepresentation(pi::RepLoc : Precision:=10) -> GalRep
{"} // "

  // TD Oct 2014, based on Jared's code + new Galois representations machinery
  
  p:=pi`p;

  if IsPrincipalSeries(pi) then

    chi1,chi2:=Explode(PrincipalSeriesParameters(pi));
    return GaloisRepresentation(ArtinRepresentation(chi1)+ArtinRepresentation(chi2),p);

  elif IsSupercuspidal(pi) then
  
    // Let R,chi be the data returned by "Admissible Pair", so that R/Z_p is quadratic and
    // chi is a character of R^*.  We produce the extension F of R cut out by chi by
    // local class field theory.
    
    require IsMinimal(pi): "Argument must be a minimal representation (if supercuspidal)";
    R,chi:=AdmissiblePair(pi);
    U,m:=UnitGroup(R);
    K:=Parent(chi(R!1));
    Tcyc,mcyc:=UnitGroup(K);
    theta:=hom< U -> Tcyc | [chi(m(U.i)) @@ mcyc : i in [1..Ngens(U)]]>;
    H:=Kernel(theta);
    E:=FieldOfFractions(R);
    Qp:=BaseField(E);
    UE,mE:=UnitGroup(E);
    Hgens:=[m(H.i) @@ mE: i in [1..Ngens(H)]];
    g:=IsRamified(E) select E.1 else p;
    KernelTheta:=sub<UE | Append(Hgens, g @@ mE)>; 
    F:=ClassField(mE, KernelTheta);

    GR:=GaloisRepresentations(MinimalPolynomial(F.1,Qp));
    GR:=[G: G in GR | (Degree(G) eq 2) and IsFaithful(Character(G))];
    require #GR eq 1: "Error: found >1 faithful 2-dimensionals";

    return GR[1];

  else

    assert pi`type eq "Steinberg";
    tw:=GaloisRepresentation(ArtinRepresentation(pi`TwistingCharacter),p);
    return tw*SP(BaseField(tw),2);
  
  end if;
end intrinsic;


