freeze;

///////////////////////////////////////////////////////////////////////
// curve_maps.m
///////////////////////////////////////////////////////////////////////

intrinsic TranslationToInfinity(C::Crv,p::Pt) -> Crv,MapSch
{Translate the point p to the point [0:1:0] and the tangent line to C at
p to the line at infinity}
    require p in C(BaseRing(C)) and IsNonsingular(C,p):
        "The second argument is not a smooth rational point on the curve";
    P := Ambient(C);
    x := P.1; y := P.2; z := P.3;
    p1 := P ! [0,1,0];
    if p eq p1 then
        f := IdentityMap(P);
        C1 := C;
    else
        f := Translation(P,p,p1);
        C1 := f(C);
    end if;
    T := TangentLine(C1,p1);    // T: (a*x + b*z = 0)
    if IsDivisibleBy(Polynomial(T),z) then
        g := IdentityMap(P);
        C2 := C1;
    else
        a := Coefficient(Polynomial(T),x,1);
        b := Coefficient(Polynomial(T),z,1);
        if b eq 0 then
            g := map<P->P|[z,y,x]>;
        else
            g := map<P->P|[b*x,y,z-a*x]>;
        end if;
        C2 := g(C1);
    end if;
    return C2,f * g;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//              Weierstrass form
///////////////////////////////////////////////////////////////////////
 
intrinsic IsEllipticWeierstrass(C::Crv) -> BoolElt
{True iff C is an elliptic curve in Weierstrass form}
    if IsAffine(C) then C := ProjectiveClosure(C); end if;
    P := Ambient(C); x := P.1; y := P.2; z := P.3;
    f := Polynomial(C);
    a := MonomialCoefficient(f,y^3);
    b := MonomialCoefficient(f,x*y^2);
    c := MonomialCoefficient(f,x^2*y);
    return Degree(C) eq 3 and IsNonsingular(C) and a eq 0 and b eq 0 and c eq 0;
end intrinsic;
 
intrinsic IsHyperellipticWeierstrass(C::Crv) -> BoolElt
{True iff C is a hyperelliptic curve in Weierstrass form}
    if IsAffine(C) then C := ProjectiveClosure(C); end if;
    P := Ambient(C);
    p := P ! [0,1,0];
    if not p in C then
        return false;
    end if;
    deg := Degree(C);
    Cz := Curve(P,P.3);
    if not NoCommonComponent(C,Cz) then
        return false;
    end if;
    intnum := IntersectionNumber(C,Cz,p);
    // projdeg is the degree of the projection of C to P^1 from p
    Cx := Curve(P,P.1);
    if not NoCommonComponent(C,Cx) then
        return false;
    end if;
    projdeg := deg - IntersectionNumber(C,Cx,p);
    affsm := IsNonsingular(AffinePatch(C,1));
    tgtcone := AffinePatch(TangentCone(C,p),1) eq EmptyScheme(AffinePatch(P,1));
    return affsm and intnum eq deg and projdeg eq 2;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//     Extension of map from curve at "bad" point (for internal use)
///////////////////////////////////////////////////////////////////////
intrinsic InternalCurveMapAtPoint(phi::MapSch[Crv, Sch],p::Pt :
		ImPS := 0) -> BoolElt, Pt
{}
// In the case that phi is not defined at p, look for local equations
// at p where it is defined and get the image if they exist, using
// the function field of the domain. Assumed that phi is initially
// not defined at p and (for the moment!) that Codomain(phi) is
// singly (integrally) weighted
// If ImPS is not zero, it should be a pointset of Codomain(phi) in
// which the image can be coerced. This is done before return. 

    if IsAffine(Codomain(phi)) then // no possibility for extension!
	return false,_;
    end if;
    if not HasFunctionField(Domain(phi)) then return false,_; end if;

    // here we ASSUME that p lies in an affine patch (or Places(p)) fails,
    //  so we reduce to an affine patch containing p. Will maybe generalise
    //  later!
    Ca,p1 := AffinePatch(Domain(phi),p);
    phi1 := Expand(Restriction(ProjectiveClosureMap(Ambient(Ca)),Ca,Domain(phi))
		*phi);
    eqns := DefiningPolynomials(phi1);
    g := Gradings(Codomain(phi));
    assert #g eq 1;
    g := g[1];
    if &or[x le 0 : x in g] then
	// can't scale to remove zero values - also, disallow neg wts for now
	return false,_;
    end if;

    // get all places over (poss singular) p   
    pls := [FunctionFieldPlace(pl) : pl in Places(p)];    
    F := FunctionField(Domain(phi));
    AF,Fmp := AlgorithmicFunctionField(F);
    eqnsF := [Fmp(F!e) : e in eqns];
    vals := [[Valuation(e,pl) : e in eqnsF] : pl in pls];
    vals1 := [[Floor(v[i]/g[i]) : i in [1..#g]] : v in vals]; // scale for gradings
    minvals := [Min(v) : v in vals1];
    inds := [[j : j in [1..#eqnsF] | v[j] eq minvals[i]*g[j]] where
		v is vals[i] : i in [1..#vals]];
    // if more than one place over p, check that the non-zero values
    // in the coordinates of the images of each place are compatible
    // - also check that we can get non-zero at least once
    if #(inds[1]) eq 0 then return false,_; end if;
    if #pls gt 1 then
	if &or[inds[j] ne inds[1] : j in [2..#inds]] then
	    return false,_;
	end if;
    end if;
    inds := inds[1];     
    k := BaseRing(Domain(phi));
    PS := Parent(p);
    K := Ring(PS);
    if K cmpne k then
    // if K != k then embed k(a1,..an) into res fields of pls
    //  where k(a1,..an) is the subfield of K generated by the
    //  coordinates of p
      coords := Eltseq(p1);
      if BaseRing(K) cmpne k then
	K0 := K;
	repeat
	  K1 := K0;
	  K0 := BaseRing(K1);
	until (K0 cmpeq k) or (K0 cmpeq K1);
	error if K0 cmpne k, 
	  "Base ring of pointset of point not a field extension of base field of domain";
	K1 :=  RelativeField(k,K);
	Embed(K1,K,K!(K1.1));
	coords := [K1!c : c in coords];
      else
	K1 := K;
      end if;
      L := sub<K1|coords>;
      R := PolynomialRing(k);
      cpols := [R!Eltseq(L!c) : c in coords];
      // get the embedding of L into each pl in pls
      cims := [Fmp(F!(A.i)) : i in [1..Length(A)]] where A is Ambient(Ca);
      impt := 0;
      for i in [1..#pls] do
	pl := pls[i];	
	kpl := ResidueClassField(pl);
	if not (L cmpeq k) then
	  cspl := [Evaluate(c,pl) : c in cims];
	  Rpl := PolynomialRing(kpl);
	  cpols1 := [Rpl!(cpols[j]) - cspl[j] : j in [1..#cspl]];
	  ipol := GCD(cpols1);
	  assert Degree(ipol) eq 1;
	  Embed(L,kpl,-Coefficient(ipol,0)/Coefficient(ipol,1));
	end if;
	pti := [L|0 : j in [1..#eqns]];
	mv := minvals[i];
	u := (mv eq 0) select AF!1 else UniformizingElement(pl);
	for j in [1..#eqns] do
	  if j notin inds then continue; end if;
	  v := Evaluate(eqnsF[j]*(u^(-g[j]*mv)),pl);
	  if v notin L then return false,_; end if;
	  pti[j] := L!v;	  
	end for;
	if Type(impt) ne RngIntElt then
	  //check that have the same point as for earlier places
	  if pti ne impt then return false,_; end if;
	else
	  impt := pti;
	end if;	
      end for;
      retval := (Type(ImPS) cmpeq RngIntElt) select
		  (Codomain(phi)(K))![K!(K1!e) : e in impt] else
		   ImPS![K!(K1!e) : e in impt];
      return true,retval;
    else // K = k
      impt := 0;
      for i in [1..#pls] do
	pl := pls[i];
	kpl := ResidueClassField(pl);	
	pti := [k|0 : j in [1..#eqns]];
	mv := minvals[i];
	u := (mv eq 0) select AF!1 else UniformizingElement(pl);
	for j in [1..#eqns] do
	  if j notin inds then continue; end if;
	  v := Evaluate(eqnsF[j]*(u^(-g[j]*mv)),pl);
	  if v notin k then return false,_; end if;
	  pti[j] := k!v;	  
	end for;
	if Type(impt) ne RngIntElt then
	  //check that have the same point as for earlier places
	  if pti ne impt then return false,_; end if;
	else
	  impt := pti;
	end if;	
      end for;
      retval := (Type(ImPS) cmpeq RngIntElt) select
		   Codomain(phi)!impt else ImPS!impt;
      return true,retval;      
    end if;
end intrinsic;   
