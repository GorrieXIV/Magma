freeze;
///////////////////////////////////////////////////////////////////
//     Intrinsics for computing various surface  		 //
//  invariants for ord proj surfaces which are at least	 	 //
//   			Gorenstein	 			 //
//             		mch - 10/2012                            //
///////////////////////////////////////////////////////////////////

import "kod_enr.m": h0;
import "singularity.m": is_known_gor;
import "local_resolution.m" : MultiAdjointLS;
import "../SrfHyp/adjoints.m" : homAdjoints;

function get_arith_genus(S)

    if (assigned S`pg) and (assigned S`q) then
	return (S`pg)-(S`q);
    end if;
    return ArithmeticGenus(S);

end function;

intrinsic GeometricGenus(S::Srfc : CheckGor := false, UseCohom := false) 
		-> RngIntElt
{ Returns the geometric genus of ordinary projective Gorenstein surface S.
  Uses cohomology if UseCohom is true (default: false). Checks the Gorenstein
  condition on S if CheckGor is true (default: false)}

    if assigned S`pg then return S`pg; end if;
    require IsOrdinaryProjective(S) : 
		"S should be a surface in ordinary projective space";
    if CheckGor then
	require IsGorenstein(S) : 
	   "Error: S is not a Gorenstein surface";
    end if;

    if UseCohom then
	OS := StructureSheaf(S);
	SaturateSheaf(~OS); //usually faster to work with full module
	g := CohomologyDimension(OS,2,0);
    else
	K := CanonicalSheaf(S);
	g := h0(K);
    end if;

    S`pg := g;
    return g;

end intrinsic;

intrinsic Plurigenus(S::Srfc, n::RngIntElt : CheckGor := false) -> RngIntElt
{ Returns the nth plurigenus of ordinary projective Gorenstein surface S.
  Checks the Gorenstein condition on S if CheckGor is true (default: false)}

    require IsOrdinaryProjective(S) : 
		"S should be a surface in ordinary projective space";
    require n ge 0: "n should be a non-negative integer";
    if n eq 0 then return 1; end if;
    if n eq 1 then return GeometricGenus(S : CheckGor := CheckGor); end if;

    if CheckGor then
	require IsGorenstein(S) : 
	   "Error: S is not a Gorenstein surface";
    end if;

    // first see if we can deduce result from Kodaira type
    if assigned S`kod_dim then
      case S`kod_dim:
	when -1: return 0;
	when 0: r := S`kod_enr2;
		if r eq -3 then // Enriques
		  return IsEven(n) select 1 else 0;
		elif (r eq -2) or (r eq -1) then // K3 or torus
		  return 1;
		elif r gt 0 then // bielliptic with known order of K
		  return IsDivisibleBy(n,r) select 1 else 0;
		end if;
	when 2:
	  pa := get_arith_genus(S);
	  if not (assigned S`K2m) then
	    K := CanonicalSheaf(S);
	    SaturateSheaf(~K);
	    p2 := h0(TensorPower(K,2));
	    S`K2m := p2-1-pa;
	  end if;
	  return ((n*(n-1)) div 2)*(S`K2m)+1+pa;
      end case;
    end if;

    // just expand K^(tensor)n and take h0
    K := CanonicalSheaf(S);
    SaturateSheaf(~K);
    return h0(TensorPower(K,n));

end intrinsic;

intrinsic Irregularity(S::Srfc : CheckGor := false, UseCohom := false)
			-> RngIntElt
{ Returns the irregularity of ordinary projective surface S.
  Checks the Gorenstein condition on S if CheckGor is true (default: false).
  If S is known Gorenstein, doesn't use cohomology unless UseCohom
  is true (default: false)}

    if assigned S`q then return S`q; end if;
    require IsOrdinaryProjective(S) : 
		"S should be a surface in ordinary projective space";
    if CheckGor then
	boo := IsGorenstein(S);
    end if;
    boo, boo1 := is_known_gor(S);
    if boo then boo := boo1; end if;
    if (not boo) or UseCohom then
	OS := StructureSheaf(S);
	SaturateSheaf(~OS); //usually faster to work with full module
	S`q := CohomologyDimension(OS,1,0);
    else
	pg := GeometricGenus(S);
	pa := get_arith_genus(S);
	S`q := pg-pa;
    end if;
    return S`q;

end intrinsic;

intrinsic ChernNumber(S::Srfc, n::RngIntElt : CheckADE := false)
		-> RngIntElt
{ Returns the nth (n = 1 or 2) ChernNumber of S, an ordinary projective
  surface with only ordinary (A-D-E) singularities. Checks the singularity
  condition on S if CheckADE is true (default: false)}

    require (n eq 1) or (n eq 2): "Second argument must be 1 or 2";
    if not (assigned S`K2) then
      require IsOrdinaryProjective(S) : 
		"S should be a surface in ordinary projective space";
      if CheckADE then
	require HasOnlySimpleSingularities(S):
		"Error: S does not have only simple singularities";
      end if;
      K := CanonicalSheaf(S);
      S`K2 := IntersectionPairing(K,K);
    end if;
    if n eq 1 then
      return S`K2;
    else
      pa := get_arith_genus(S);
      return 12*(1+pa)-(S`K2);
    end if;

end intrinsic;

intrinsic MinimalChernNumber(S::Srfc, n::RngIntElt : CheckADE := false)
		-> RngIntElt
{ Returns the nth (n = 1 or 2) ChernNumber of a minimal model of a desingularization
  of S, an ordinary projective
  surface with only ordinary (A-D-E) singularities. Checks the singularity
  condition on S if CheckADE is true (default: false)}

    require (n eq 1) or (n eq 2): "Second argument must be 1 or 2";
    if not (assigned S`K2m) then
      require IsOrdinaryProjective(S) : 
		"S should be a surface in ordinary projective space";
      if CheckADE then
	require HasOnlySimpleSingularities(S):
		"Error: S does not have only simple singularities";
      end if;
      if not (assigned S`kod_dim) then
	kd := KodairaEnriquesType(S);
      else
	kd := S`kod_dim;
      end if;
      case kd:
	when -1: assert assigned S`q;
		 S`K2m := ((S`q) eq 0) select 9 else 8;
	when 0: S`K2m := 0;
	when 1: S`K2m := 0;
	when 2:
	  if not (assigned S`K2m) then
	    p2 := Plurigenus(S,2); //this will assign S`K2m !
	  end if;
      end case;
    end if;
    if n eq 1 then
      return S`K2m;
    else
      pa := get_arith_genus(S);
      return 12*(1+pa)-(S`K2m);
    end if;

end intrinsic;

intrinsic HodgeNumber(S::Srfc, i::RngIntElt, j::RngIntElt : CheckADE := false)
		-> RngIntElt
{ Returns the h^(i,j) (0 <= i,j <= 2) HodgeNumber of S, an ordinary projective
  surface with only ordinary (A-D-E) singularities. Checks the singularity
  condition on S if CheckADE is true (default: false)}

    require (i ge 0) and (i le 2) and (j ge 0) and (j le 2) : 
		"Arguments i and j must both be 0, 1 or 2";
    require IsOrdinaryProjective(S) : 
		"S should be a surface in ordinary projective space";
    if CheckADE then
	require HasOnlySimpleSingularities(S):
		"Error: S does not have only simple singularities";
    end if;

    // use symmetry to get i, j in standard form
    if i+j ge 2 then
	i := 2-i; j := 2-j;
    end if;
    if i gt j then
	k := i; i := j; j := k;
    end if;
    
    if i+j eq 0 then
	return 1;
    elif (i+j eq 1) and (assigned S`q) then
	return S`q;
    end if;
    pg := GeometricGenus(S);
    if i+j eq 1 then
	pa := get_arith_genus(S);
	S`q := pg-pa;
	return S`q;
    else //i+j eq 2
	if i eq 0 then return pg; end if;
	// h^{1,1} case
	pa := get_arith_genus(S);
	if not (assigned S`K2) then
	  K := CanonicalSheaf(S);
	  S`K2 := IntersectionPairing(K,K);
	end if;
	return 10+8*pa+2*pg-(S`K2);
    end if;

end intrinsic;

intrinsic HomAdjoints(m::RngIntElt, n::RngIntElt, S::Srfc : UseFormalDesing := false) -> SeqEnum
{
Given a (generally singular) surface S in P^3 and integers m and n. Returns a basis
for the vector space of '(m,n)'-adjoints : a subspace of homogeneous degree 
(m-4)*Degree(S)+n polynomials representing the global sections of invertible 
sheaf K^m(nH) on a desingularisation. If S is singular and desingularisation
data has not already been computed and stored, this is computed first.
}
	
    require IsOrdinaryProjective(S) and Dimension(Ambient(S)) eq 3:
	  "S must currently be a surface in ordinary projective 3-space";

    rl,typ := ResolveSingularSurface(S : AdjComp := true, UseFormalDesing := 
						UseFormalDesing);
    if typ eq 1 then
      return homAdjoints(m,n,DefiningPolynomial(S) : FormalDesing := rl);
    elif typ eq 2 then
      return MultiAdjointLS(m,n,S,rl);
    end if;

end intrinsic;

intrinsic PlurigenusOfDesingularization(S::Srfc, m::RngIntElt : UseFormalDesing := false) -> RngIntElt
{
Given a (generally singular) surface S in 'P^3', returns the m-th plurigenus of any
desingularization (m>=0). If S is singular and desingularization
data has not already been computed and stored, this is computed first.

}
 
    require IsOrdinaryProjective(S) and Dimension(Ambient(S)) eq 3:
	  "S must currently be a surface in ordinary projective 3-space";
    require m ge 0: "m must be a non-negative integer";
    if m eq 0 then return 1; end if;

    rl,typ := ResolveSingularSurface(S : AdjComp := true, UseFormalDesing := 
						UseFormalDesing);
    if typ eq 1 then
      return #homAdjoints(m,0,DefiningPolynomial(S) : FormalDesing := rl);
    elif typ eq 2 then
      return #MultiAdjointLS(m,0,S,rl);
    end if;

end intrinsic;

intrinsic GeometricGenusOfDesingularization(S::Srfc : UseFormalDesing := false) -> RngIntElt
{
Given a (generally singular) surface S in 'P^3', returns the geometric genus of any
desingularization. If S is singular and desingularization
data has not already been computed and stored, this is computed first.
}
	require IsOrdinaryProjective(S) and Dimension(Ambient(S)) eq 3:
	  "S must be a surface in ordinary projective 3-space";
	return PlurigenusOfDesingularization(S,1 : UseFormalDesing := UseFormalDesing);

end intrinsic;

intrinsic ArithmeticGenusOfDesingularization(S::Srfc : UseFormalDesing := false) -> RngIntElt
{
Given a (generally singular) surface S in 'P^3', returns the arithmetic genus of any
desingularization. If S is singular and desingularization
data has not already been computed and stored, this is computed first.
}
	
    require IsOrdinaryProjective(S) and Dimension(Ambient(S)) eq 3:
	  "S must be a surface in ordinary projective 3-space";

    rl,typ := ResolveSingularSurface(S : AdjComp := true, UseFormalDesing := 
						UseFormalDesing);

    // TODO: In the desingularisation by blow-up case, where intersection data is
    // available for the curve components over the singular points, should try
    // to use a different method: if X is a desing, ag(X)=ag(S)-sum_x px
    // where the sum is over the singular points of S and px is dim H^1(O_(nDx))
    // for n >> 0  and Dx is the effective divisor supported on components
    // over x given by the pullback of maximal ideal of x.

    // adjdim = dim H^0(K_X(1)), K_X the canonical sheaf of the desingularisation.
    // adjdim2 = dim H^0(K_X(2)). In the case where there are only singularities
    //  in codimension 2 (in particular when typ=2), we can take a general
    //  hyperplane section of S which is a non-singular plane curve of degree
    //  d and is isomorphic to a section of the pullback of the hyperplane
    //  divisor to a desingularisation. Then, can just do the comp. with adjdim.
    d := Degree(S);
    if typ eq 1 then
      adjdim := #homAdjoints(1,1,DefiningPolynomial(S) : FormalDesing := rl);
      adjdim2 := #homAdjoints(1,2,DefiningPolynomial(S) : FormalDesing := rl);
      return d+2*adjdim-adjdim2-1; 
    elif typ eq 2 then
      adjdim := #MultiAdjointLS(1,1,S,rl);
      return adjdim-(((d-1)*(d-2)) div 2);
    end if;

end intrinsic;

intrinsic IsRational(S::Srfc : UseFormalDesing := false, CheckADE := false) -> BoolElt
{
Given an ordinary projective surface S returns whether the surface is rational.
S should either have only simple singularities or lie in 'P^3' (when desingularization to
compute plurigenera is used). In the former case, the singularity condition is only checked
if the 'CheckADE' parameter is set to true. In the latter case, if S is singular and
desingularization data has not already been computed and stored, this is computed first.
}

	require IsOrdinaryProjective(S):
	  "S must be a surface in ordinary projective space";

	t := Type(BaseRing(S)); boo_desing := true;
	if (Dimension(Ambient(S)) ne 3) or 
		((not ((t cmpeq FldRat) or ISA(t,FldAlg))) and
	    (Dimension(SingularSubscheme(S)) ge 1)) then
	  // not a desingularisation case
	  boo_desing := false;
	end if;
	if boo_desing then
	  //even in the desing cases, a simple sing check
	  //should be quick and lead to faster processing.
	  boo_desing := not HasOnlySimpleSingularities(S);
	end if;

        // Castelnuevo criterion: (non-singular) S rational iff arithmetic genus
	// and second plurigenus are both zero.
	if not boo_desing then
	  if CheckADE then
	    require HasOnlySimpleSingularities(S):
		"Surface S should have only simple singularities";
	  end if;
	  pg := GeometricGenus(S : CheckGor := false);
	  if pg ne 0 then return false; end if;
	  if not (assigned S`q) then
	    S`q := pg - ArithmeticGenus(S);
	  end if;
	  if S`q ne 0 then return false; end if;
	  if assigned S`kod_dim then
	    return (S`kod_dim eq -1);
	  else
	    p2 := Plurigenus(S,2 : CheckGor := false);
	    return (p2 eq 0);
	  end if;
	else
	  pa := ArithmeticGenusOfDesingularization(S : UseFormalDesing := UseFormalDesing);
	  if pa ne 0 then return false; end if;
	  p2 := PlurigenusOfDesingularization(S,2 : UseFormalDesing := UseFormalDesing);
	  return (p2 eq 0);
	end if;

end intrinsic;

