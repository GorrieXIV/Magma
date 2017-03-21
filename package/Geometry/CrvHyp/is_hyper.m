freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//        Functions to determine whether a general curve is           //
//          (geometrically) hyperelliptic or not and to               //
//          find a standard Weierstrass model if it is.               //
//                 Mike Harrison 04/05                                //
////////////////////////////////////////////////////////////////////////

declare verbose IsHyp, 2;

import "../Crv/curve_quotient.m" : SquareFreePart;

/* 
    For a curve C , returns whether C is (birationally, geometrically)
     hyperelliptic or not and, if so and depending on retcode, returns 
     a plane conic or P^1, con, (depending on whether genus(C) is
     even or odd) and a map, mp, from C -> con s.t.
      mp: ProjectiveNormalisation(C) -> con is 2-1.
    retcode = 0 - only check for geo hyperellipticity, no map
	      1 - check for hyperellipticity : no map unless necessary
	      2 - always return map to conic or line
    (NB. Here, hyperelliptic requires genus of C >= 2)
*/
function MapToConic(C, retcode)

    vprint IsHyp, 2 : " testing for absolute irreducibility...";
    /* test for absolute irreducibility */
    if (not HasFunctionField(C)) or 
     (DegreeOfExactConstantField(AlgorithmicFunctionField(
                FunctionField(C))) gt 1) then
	return false,_,_;
    end if;
    vprint IsHyp, 2: " computing the genus...";
    g := Genus(C);
    if g le 1 then return false,_,_; end if;
    if (g eq 2) and (retcode ne 2) then return true,_,_; end if;
    vprint IsHyp, 2: " computing the canonical map...";
    phi := CanonicalMap(C);
    if g eq 2 then
	P1 := Curve(ProjectiveSpace(BaseRing(C),1));
	mp := map<C->P1|DefiningEquations(phi)>;
	return true,P1,mp;
    end if;

    vprint IsHyp, 2: " computing the canonical image...";    
    X, bHyp := CanonicalImage(C,phi);
    if not bHyp then
	return false,_,_;
    end if;

    if (retcode eq 0) or ((retcode eq 1) and IsEven(g)) then 
	return true,_,_;
    end if;

    if g eq 3 then //slight simplification
	con := Conic(Ambient(X),DefiningEquation(X));
	return true,con,map<C->con| DefiningEquations(phi) : Check := false>;
    end if;

    b_con := IsOdd(g); // will map to a conic? (otherwise the proj line!)

    if b_con then 
      vprint IsHyp, 2: " mapping to a conic...";
    else
      vprint IsHyp, 2: " mapping to the projective line...";
    end if;
    prm_mp := ParametrizeRationalNormalCurve(X);
    con := Domain(prm_mp);
    if b_con then 
	inv_prm_mp := map<X->con | InverseDefiningPolynomials(prm_mp): Check := false>;
    else
	inv_prm_mp := Inverse(prm_mp);
    end if;
    mp := map<C->X| DefiningEquations(phi) : Check := false> * inv_prm_mp;
    return true,con,mp;
    
end function;
    
intrinsic IsGeometricallyHyperelliptic(C::Crv : Map := true) -> BoolElt,Crv,MapSch
{ Determines whether curve C is a hyperelliptic curve over the
  algebraic closure of its base field. If so and Map is true, a plane conic
  or the projective line (if genus(C) is odd or even) and a degree 2
  map from C to it (all defined over the base field) are also returned.}

    /* Handler trivial special cases */
    b_triv := (Type(C) eq CrvHyp);
    if not b_triv then
	b_triv,C1 := IsHyperellipticCurve(C);
    else
	C1 := C;
    end if;
    if b_triv then
	if Genus(C1) le 1 then return false,_,_; end if;
	if Map then
	    P1 := Curve(ProjectiveSpace(BaseRing(C),1));
	    mp := map<C->P1|[R.1,R.3] : Check := false> 
		where R is CoordinateRing(Ambient(C));
	    return true,P1,mp;
	else
	    return true,_,_;
	end if;
    end if;

    require IsField(BaseRing(C)) and IsExact(BaseRing(C)): 
		"Curve must be defined over an exact field.";
    return MapToConic(C, (Map select 2 else 0));
    
end intrinsic;

intrinsic IsHyperelliptic(C::Crv : Eqn := true) -> BoolElt,CrvHyp,MapSch
{ Determines whether curve C is hyperelliptic over its base field, K,
  (ie has a degree 2 map to the projective line defined over K). If so,
  and the Eqn parameter is true, also returns a CrvHyp, H, over K and an
  isomorphic scheme map from C to H}

    /* Handler trivial special cases */
    b_triv := (Type(C) eq CrvHyp);
    if b_triv then
	C1 := C;
	mp := IdentityMap(C);
    else
	b_triv, C1 := IsHyperellipticCurve(C);
	if b_triv then
	    mp := iso<C->C1|[R.1,R.2,R.3],[R.1,R.2,R.3] : Check := false>
		where R is CoordinateRing(Ambient(C));
	end if;
    end if;
    if b_triv then
	if Genus(C1) le 1 then return false,_,_; end if;
	if Eqn then return true,C1,mp;
	else return true,_,_; end if;
    end if;

    K := BaseRing(C);
    require IsField(K) and IsExact(K): 
		"Curve must be defined over an exact field.";
    vprint IsHyp : "Looking for degree 2 map to line or conic.";
    boo,con,c_map := MapToConic(C, (Eqn select 2 else 1));
    if not boo then return boo,_,_; end if;
    g := Genus(C);

    if IsEven(g) then
        if not Eqn then return true,_,_; end if;
	P1 := Codomain(c_map); p1_map := c_map;
    else  
	/* see if conic has rational point and construct map to P^1 */
	vprint IsHyp : "Looking for rational point on conic.";
    
	boo,pt := HasRationalPoint(con);
	if (not boo) or (not Eqn) then return boo,_,_; end if;
    
	// Make C-mapping projective if not already so.
	if IsAffine(C) then
	   c_map := mp * c_map where mp is
             Restriction(Inverse(ProjectiveClosureMap(Ambient(C))),
	      ProjectiveClosure(C),C);
	end if;
    
	P1 := Curve(ProjectiveSpace(K,1),[]);
	p1_map := c_map * Inverse(Parametrization(con,pt,P1));
	delete con,c_map;
    end if;
    p1_map := Expand(p1_map);
    /* p1_map = [f_x,1] */
    f_x := FunctionField(C)!(p1/p2) where
             p1,p2 := Explode(DefiningPolynomials(p1_map));
        
    /* Now use curve mapping functionality to find hyperelliptic equation */
    /* y^2+h(x)*y=f(x). x is just the function f_x in the function field. */
    /* Must find y in FF(C) and cooresponding h and f.                    */
    vprint IsHyp : "Finding hyperelliptic equation.";
    P := PolynomialRing(K); X:=P.1;
    AFF,mpFF := AlgorithmicFunctionField(FunctionField(C));
    d := 2*g+2;
    x := mpFF(f_x); // will work in the algebraic function field
    vec := [AFF!1,x];
    for i in [2..d] do Append(~vec,x*vec[i]); end for;

    if Characteristic(K) ne 2 then
	vprint IsHyp, 2 : " finding second generator of function field.";
	v := BasisOfHolomorphicDifferentials(AFF)[1]/Differential(x);
	vprint IsHyp, 2 : " finding y coordinate and computing equation.";
	// v = P(x)/y for a polynomial P of degree <= g-1
	//  and y st y^2=Q(x), Q square free of deg 2g+1or2
	// - we find P and Q by getting K-linear relations in F
	vec := [w*e : e in Reverse(vec)] cat
	      [vec[i] : i in [1..2*g]] where w is v^2;
	rels := Basis(Relations(vec,K));
	delete vec;
	assert #rels gt 0;
	rels := EchelonForm(Matrix(rels));
	rel := Eltseq(rels[Nrows(rels)]);
	// this gives the relation R*v^2-S=0 with R of smallest degree
	r := 1;
	while rel[r] eq K!0 do r +:= 1; end while;
	assert r le g+1;
	R := &+[rel[i]*X^(d+1-i) : i in [r..d+1]];
	S := - &+[rel[i+d+2]*X^i : i in [0..d-3]];
	//assert Degree(GCD(R,S)) eq 0;
	// Now S = U*V^2 with U square free and then
	//  Q := U*R and P=U*V
	U,V := SquareFreePart(S);
	pol_x := U*R; Py := U*V;
	f_y := Inverse(mpFF)(Evaluate(Py,x)/v);
	// Do some basic sanity checks on pol_x -
	//  is it separable of the right degree?
	assert (d1 eq d) or (d1 eq d-1) where d1 is Degree(pol_x);
	assert Degree(GCD(pol_x,Derivative(pol_x))) eq 0;
	HyC := HyperellipticCurve(pol_x);
	mp_eqns := [f_x,f_y,1];
	// If K=Q then get MinimalWeierstrass model
	if (Type(K) eq FldRat) then
	    vprint IsHyp, 2 : " simplifying Weierstrass model.";
	    HyC,mp := ReducedMinimalWeierstrassModel(HyC);
	    mp_eqns := [Evaluate(f,mp_eqns) : f in DefiningPolynomials(mp)];
	end if; 
    else   // char(K) = 2 - fiddlier!
	vprint IsHyp, 2 : "getting divisor at infinity.";
	D_inf := Denominator(Divisor(x));
	assert Degree(D_inf) eq 2;
	// find a suitable y in L((g+1)D_inf)
	vprint IsHyp, 2 : " getting RR basis for functions at infinity.";
	V,mp := RiemannRochSpace((g+1)*D_inf);
	assert Dimension(V) eq (g+3);
	vprint IsHyp, 2 : " finding suitable y coordinate in function field.";
	//  get a complement to {1,x,..,x^(g+1)}
	X := sub<V|[V!Inverse(mp)(xp) : xp in [vec[i] : i in [1..g+2]]]>;
	y := mp(Basis(Complement(V,X))[1]);
	vprint IsHyp, 2 : " computing equation.";
	vec := [y^2] cat [y*vec[i]:i in [1..g+2]] cat vec;
	rels := Basis(Relations(vec,K));
	assert #rels eq 1;
	rel := rels[1];
	assert rel[1] ne 0;
	h := P![rel[i]/rel[1]:i in [2..g+3]];
	f := P![rel[i]/rel[1]:i in [g+4..g+4+d]];

	boo,HyC := IsHyperellipticCurve([f,h]);
	assert boo;
	assert Genus(HyC) eq g;
	mp_eqns := [f_x,Inverse(mpFF)(y),1];
    end if;

    h_map := map<C->HyC | mp_eqns : Check := false>;
    return true,HyC,h_map;	          

end intrinsic;
    
intrinsic Specialization(H::CrvHyp[FldFunRat],t::RngElt) -> CrvHyp
{Given a hyperelliptic curve over a rational function field F
 and a ring element that coerces into the base ring of F,
 return the specialization of the hyperelliptic curve.}
 b,t:=IsCoercible(BaseRing(BaseRing(H)),t);
 require b: "t does not coerce into the base ring of the function field";
 f,g:=HyperellipticPolynomials(H);
 f:=Polynomial([Evaluate(c,t) : c in Coefficients(f)]);
 if g ne 0 then g:=Polynomial([Evaluate(c,t) : c in Coefficients(g)]);
 else g:=Parent(f)!0; end if; return HyperellipticCurve(f,g); end intrinsic;
