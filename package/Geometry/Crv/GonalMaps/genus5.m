freeze;
////////////////////////////////////////////////////////////////
//      Gonal maps and plane models for genus 5 curves        //
//            mch - 03/12                                     //
////////////////////////////////////////////////////////////////

import "cd1.m":conic_point,quadric_scroll_map;
import "gon_main.m":do_hyperelliptic_case, simplify_map;

function deg_4_map(C,Qs,mp,p)
    es := Eltseq(p);
    K := Universe(es);
    k := BaseRing(C);
    CK := (K cmpeq k) select C else BaseChange(C,K);
    PK := Ambient(CK);
    RK := CoordinateRing(PK);
    fQ := &+[es[i]*(RK!(Qs[i])) : i in [1..3]];
    Q := Scheme(PK,fQ);
    sngs := ReducedSubscheme(SingularSubscheme(Q));
    assert Dimension(sngs) ge 0;
    if Dimension(sngs) eq 1 then //fQ has rank 3
	P2K := ProjectiveSpace(K,2);
	prj := map<Q->P2K|[f : f in DefiningPolynomials(sngs) |
				TotalDegree(f) eq 1]>;
	C1 := Conic(Curve(prj(Q)));
	bsoln, pt := HasRationalPoint(C1);
	if not bsoln then //extend to a quadratic field
	  seq := conic_point(C1);
	  K1 := Universe(seq);
	  P2K1 := ProjectiveSpace(K1,2);
	  CK := BaseChange(CK,K1);
	  _,prj1 := Projection(P2K1,P2K1!seq);
	  defs := [R1!f : f in DefiningPolynomials(prj)] where
		R1 is CoordinateRing(Ambient(CK));
	else
	  K1 := K;
	  _,prj1 := Projection(P2K,P2K!Eltseq(pt));
	  defs := DefiningPolynomials(prj);
	end if;
        vs := [Evaluate(f,defs) : f in DefiningPolynomials(prj1)];
    else // //fQ has rank 4
	pt := Setseq(Support(sngs));
	assert #pt eq 1;
	pt := pt[1];
	_,prj := Projection(PK,PK!Eltseq(pt));
	Q1 := prj(Q); // non-singular quadric in P^3
	prj1 := quadric_scroll_map(Q1);
	K1 := BaseRing(Universe(prj1));
	if K1 cmpeq K then
	  defs := DefiningPolynomials(prj);
	else
	  CK := BaseChange(CK,K1);
	  defs := [R1!f : f in DefiningPolynomials(prj)] where
		R1 is CoordinateRing(Ambient(CK));
	end if;
        vs := [Evaluate(f,defs) : f in prj1];
    end if;
    mp1 := map<CK->Curve(ProjectiveSpace(K1,1))|vs : Check:=false>;
    // add in initial map to the canonical model
    if Domain(mp) eq Codomain(mp) then
	return mp1;
    end if;
    if K1 cmpeq k then
	mp1 := Expand(mp*mp1);
    else
	DK := BaseChange(Domain(mp),K1);
	mp2 := map<DK->CK|defs> where defs is 
		[R1!f : f in DefiningPolynomials(mp)] where
		  R1 is CoordinateRing(Ambient(DK));
	mp1 := Expand(mp2*mp1);
    end if;
    mp1 := simplify_map(mp1);
    return mp1;

end function;

function genus5_gon_3(C)
// C is a genus 5 canonical curve of gonality 3.
//  Returns a g^1_3

    Qs := [f : f in DefiningPolynomials(C) | TotalDegree(f) eq 2];
    if (#Qs ne 3) then
	Qs := [f : f in Basis(Ideal(C)) | TotalDegree(f) eq 2];
    end if;
    R := Generic(Universe(Qs));
    IX := ideal<R|Qs>; //ideal of 2D scroll in P^4
    res := MinimalFreeResolution(QuotientModule(IX));
    assert BettiTable(res) cmpeq [[1,0,0],[0,3,2]];
    mat := Matrix(BoundaryMap(res,2));
    k := BaseRing(C);
    return map<C->Curve(ProjectiveSpace(k,1))|[mat[1,1],mat[2,1]]>;

end function;

function do_general_genus_5(C,cmap)
// C is given by the complete intersection of 3 quadrics in P^4.
//  The scrolls containing C which give degree 4 maps are the
//  singular quadrics in the 3D space of quadrics.

    Qs := DefiningPolynomials(C);
    if (#Qs ne 3) or &or[TotalDegree(f) ne 2 : f in Qs] then 
      Qs := [f : f in Basis(Ideal(C)) | TotalDegree(f) eq 2];
    end if;
    assert #Qs eq 3;
    R := CoordinateRing(Ambient(C));
    k := BaseRing(R);
    P2<u,v,w> := ProjectiveSpace(k,2);
    R2 := CoordinateRing(P2);
    R2X := PolynomialRing(R2,5,"grevlex");

    Quvw := &+[(R2.i)*(R2X!Qs[i]) : i in [1..3]];
    mat_uvw := Matrix(R2,[[MonomialCoefficient(Derivative(Quvw,i),R2X.j) :
		j in [1..5]] : i in [1..5]]);
    F := Determinant(mat_uvw);
    F := Curve(P2,F);
    return F,func<x|deg_4_map(C,Qs,cmap,x)>; 
end function;

intrinsic Genus5GonalMap(C::Crv : DataOnly := false, IsCanonical:=false) -> 
		RngIntElt,MapSch,Crv,UserProgram
{Computes smallest degree (gonal) maps to P^1 for a genus 5 curve, possibly over
a finite extension of the base field. Returns the gonality and a map if DataOnly is false.
Also returns the curve X parametrising degree 4 maps and a function taking points on X
to degree 4 maps in the gonality 4 case. If C is a canonical curve in ordinary projective
space, IsCanonical should be set to true for efficiency}

    if IsCanonical then
	assert IsOrdinaryProjective(C);
	bHyp := false;
	g := Rank(CoordinateRing(Ambient(C)));
	cmap := IdentityMap(C);
	is_can := true;
    else
      g,bHyp,cmap := GenusAndCanonicalMap(C);
      is_can := (Domain(cmap) cmpeq Codomain(cmap));
    end if;
    require g eq 5: "C should be a curve of genus 5";
    if bHyp then
        if DataOnly then return 2,_,_,_,_; end if;
	mp := do_hyperelliptic_case(C,cmap);
	return 2,mp,_,_;
    end if;
    Cc := Codomain(cmap);//canonical image
    if &or[TotalDegree(f) eq 3 : f in DefiningPolynomials(Cc)] then
	//gonality 3 case
	if DataOnly then return 3,_,_,_,_; end if;
	mp3 := genus5_gon_3(Cc);
	if not is_can then
	  mp3 := Expand(cmap*mp3);
	  mp3 := simplify_map(mp3);
	end if;
	return 3,mp3,_,_;
    else
	//gonality 4 (general) case
	F,fn := do_general_genus_5(Cc,cmap);
	if DataOnly then return 4,_,F,fn; end if;
	//search for nice points on F
	k := BaseRing(C);
	sng := ReducedSubscheme(SingularSubscheme(F));
	pt := 0; degs := 0;
	if Dimension(sng) ge 0 then //rank 3 quadrics
	  pts := PrimeComponents(sng);
	  degs := [Degree(p) : p in pts];
	  if Minimum(degs) eq 1 then
	    pt := F!Eltseq(p) where p is 
			Representative(Support(pts[Index(degs,1)]));
	  end if;
	end if;
	if Type(pt) cmpeq RngIntElt then
	  if Type(k) cmpeq FldRat then
	     pts := PointSearch(F,100);
	     if #pts gt 0 then pt := pts[1]; end if;
	  elif Type(k) cmpeq FldFin then
	     pts := RationalPointsByFibration(F : Max := 1);
	     if #pts gt 0 then pt := pts[1]; end if;
	  end if;
	end if;
        if (Type(pt) cmpeq RngIntElt) and (Type(degs) cmpeq SeqEnum) then
	  m := Min(degs);
	  pt := pts[Index(degs,m)];
	elif Type(pt) cmpeq RngIntElt then
	  pts := Scheme(F,Ambient(F).1);
	  pts := PrimeComponents(pts);
	  degs := [Degree(p) : p in pts];
	  m := Min(degs);
	  pt := pts[Index(degs,m)];
	  if m eq 1 then
	    pt := F!Eltseq(p) where p is Representative(Support(pt));
	  end if;	  
	end if;
	if Type(pt) cmpeq Sch then
	  i := 3;
	  pta := AffinePatch(pt,1);
	  if IsEmpty(pta) then
	    i := 2; pta := AffinePatch(pt,2);
	  end if;
	  GB := GroebnerBasis(Ideal(pta));
	  R1 := Generic(Universe(GB));
	  if Degree(GB[2],R1.2) eq 1 then
	     e := -MonomialCoefficient(GB[2],R1!1)/
			MonomialCoefficient(GB[2],R1.2);
	     f := UnivariatePolynomial(GB[1]);
	     K := ext<k|f>;
	     pt_seq := [K.1,e];
	  else
	     f := UnivariatePolynomial(GB[2]);
	     K := ext<k|f>;
	     P := PolynomialRing(K);
	     f1 := Evaluate(GB[1],[P.1,K.1]);
	     e := -Coefficient(f1,0)/Coefficient(f1,1);
	     pt_seq := [e,K.1];
	  end if;
	  Insert(~pt_seq,i,1);
	  pt := F(K)!pt_seq;
	end if;
	return 4,fn(pt),F,fn;
    end if;
end intrinsic;

function pln_crv_model(C,b_is_can,D)
// computes a deg 5 or 6 plane model of C if possible, using rational
//  (non-sing) deg 1 or 2 divisor D if given for the 4-gonal case. If D
//  not given, then serach for a rational point to use as D if the 
//  the basefield is Q or finite.

    if b_is_can then
	assert IsOrdinaryProjective(C);
	bHyp := false;
	g := Rank(CoordinateRing(Ambient(C)));
	cmap := IdentityMap(C);
	is_can := true;
    else
      g,bHyp,cmap := GenusAndCanonicalMap(C);
      is_can := (Domain(cmap) cmpeq Codomain(cmap));
    end if;
    error if g ne 5, "C should be a curve of genus 5";
    if bHyp then return false,_; end if;
    Cc := Codomain(cmap);//canonical image
    k := BaseRing(Cc);
    if &or[TotalDegree(f) eq 3 : f in DefiningPolynomials(Cc)] then
	//gonality 3
    	if IsOrdinaryProjective(C) and (Dimension(Ambient(C)) eq 2) then
	  if Degree(C) eq 5 then return true,IdentityMap(C); end if;
    	end if;
	X := Scheme(Ambient(Cc),[f : f in DefiningPolynomials(Cc) |
		TotalDegree(f) eq 2]);
	R := CoordinateRing(Ambient(X));
	res := MinimalFreeResolution(QuotientModule(Ideal(X)));
	assert BettiTable(res) cmpeq [[1,0,0],[0,3,2]];
	mat := Matrix(BoundaryMap(res,2));
	l1 := mat[1,1]; l2 := mat[2,1];
	I1 := Ideal(X)+ideal<R|l1>;
	Ilin := ColonIdeal(I1,ideal<R|l2>);
	// Ilin is the ideal defining a line L in X
	// projection from the line gives the birational isomorphism
	// of X to P^2 that takes Cc to a deg 5 curve
	B := Basis(Ilin);
	assert (Degree(Ilin) eq 1) and (#B eq 3);
	P2 := ProjectiveSpace(k,2);
	mp := map<Cc->P2|B>;
	C5 := mp(Cc);
	assert Degree(C5) eq 5;
	phi := map<Cc->C5|B : Check := false>;
	if not is_can then
	  phi := Expand(cmap*phi);
	  phi := simplify_map(phi);
	end if;
	return true,phi;
    end if;
    //gonality 4
    if IsOrdinaryProjective(C) and (Dimension(Ambient(C)) eq 2) then
	if Degree(C) eq 6 then return true,IdentityMap(C); end if;
    end if;
    if Type(D) cmpeq RngIntElt then
	// search for a rational point
	if Type(k) cmpeq FldFin then
	   pts := RationalPointsByFibration(C : Max := 10);
	elif k cmpeq Rationals() then
	   pts := PointSearch(C,100);
	else
	   return false,_;
	end if;
	for p in pts do
	   if IsNonsingular(C,p) then 
		D := Cluster(C!p); break;
	   end if;
	end for;
	if Type(D) cmpeq RngIntElt then
	   return false,_; 
        end if;
    end if;
    d := Degree(D);
    if not is_can then
	boo := true;
	try
	  D1 := cmap(D);
	catch e
	  boo := false;
	end try;
	if boo and (Degree(D1) ne d) then boo := false; end if;
	if not boo then //use divisor pushforward
	  D2 := Divisor(C,D);
	  D1 := Pushforward(cmap,D2);
	  assert Degree(D1) eq d;
	  D1 := Cluster(D1);
	end if;
	D := D1;
    end if;
    if d eq 1 then
	ID := Saturation(Ideal(D)^2+Ideal(Cc)); //ideal of tangent line at D	
    else // d=2
	Saturate(~D);
	ID := Ideal(D);
    end if;
    lin := [f : f in Basis(ID) | TotalDegree(f) eq 1];
    assert #lin eq 3;
    P2 := ProjectiveSpace(k,2);
    phi := map<Cc->P2|lin>;
    C6 := phi(Cc);
    assert Degree(C6) eq 6;
    phi := map<Cc->C6|lin>;
    if not is_can then
	phi := Expand(cmap*phi);
	phi := simplify_map(phi);
    end if;
    return true,phi;
    
end function;

intrinsic Genus5PlaneCurveModel(C::Crv : IsCanonical:=false ) -> BoolElt, MapSch
{ Looks for a birational map to a degree 5 or 6 plane curve from genus 5 curve C, when C is 
trigonal or 4-gonal and not a double cover of a genus 1 curve. The first return value is 
whether C is of the correct type and a map has been found and the second is the map if so.
If C is a canonical curve in ordinary projective space, IsCanonical should be set to true for 
efficiency } 

    return pln_crv_model(C,IsCanonical,0);

end intrinsic;

intrinsic Genus5PlaneCurveModel(C::Crv, p::Pt : IsCanonical:=false ) -> BoolElt, MapSch
{ Returns a birational map to a degree 5 or 6 plane curve from genus 5 curve C, when C is 
trigonal or 4-gonal and not a double cover of a genus 1 curve. p should be a non-singular 
point on C, rational over the base field, which is used in the 4-gonal case. The first return 
value is whether C is of the correct type and the second is the map if so.
If C is a canonical curve in ordinary projective space, IsCanonical should be set to true for 
efficiency } 

    require (p in C) and (Ring(Parent(p)) cmpeq BaseRing(C)):
	"Argument 2 must be a point on argument 1 over the base field";
    require IsNonsingular(C,p):
	"Argument 2 must be nonsingular point of argument 1";
    return pln_crv_model(C,IsCanonical,Cluster(p));

end intrinsic;

intrinsic Genus5PlaneCurveModel(C::Crv, Z::Sch : IsCanonical:=false ) -> BoolElt, MapSch
{ Returns a birational map to a degree 5 or 6 plane curve from genus 5 curve C, when C is 
trigonal or 4-gonal and not a double cover of a genus 1 curve. Z should be a subscheme
of C defining a divisor of degree 2 in the non-singular locus of C, which is used in the
4-gonal case. The first return 
value is whether C is of the correct type and the second is the map if so.
If C is a canonical curve in ordinary projective space, IsCanonical should be set to true for 
efficiency } 

    require (Z subset C) and (Dimension(Z) eq 0) and (Degree(Z) eq 2):
	"Argument 2 must be a subscheme of argument 1 defining a divisor of degree 2";
    pts := PointsOverSplittingField(Z);        
    require &and[IsNonsingular(C,p) : p in pts]:
	"Points of argument 2 must be nonsingular points of argument 1";
    boo := false;
    Z1 := Z;
    while not IsAmbient(SuperScheme(Z1)) do
	if SuperScheme(Z1) eq C then boo := true; break; end if;
	Z1 := SuperScheme(Z1);
    end while;
    if boo then
	Z1 := Z;
    else 
	Z1 := C meet Z;
    end if;
	 
    return pln_crv_model(C,IsCanonical,Z1);

end intrinsic;
