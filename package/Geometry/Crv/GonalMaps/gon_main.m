freeze;
////////////////////////////////////////////////////////////////
//      General Functions used in the computation of gonal    //
//         maps for curves of genus <=6                       //
//            mch - 03/12                                     //
////////////////////////////////////////////////////////////////

import "cd1.m":conic_point;
import "../curve_autisos.m":ReduceMapDegree;

function is_canonical(C)
// simple test whether C is a canonical curve of small genus
// in ordinary projective space

    P := Ambient(C);
    if not IsOrdinaryProjective(P) then return false,_; end if;
    g := Rank(CoordinateRing(P));
    if (g gt 6) or (g le 2) then return false,_; end if;
    if IsSingular(C) then return false,_; end if;
    if g eq 3 then
	return (Degree(C) eq 4),3;
    elif g eq 4 then
	B := MinimalBasis(Ideal(C));
	boo := (#B eq 2) and (Sort([TotalDegree(b) : b in B])
				eq [2,3]);
	return boo,4;
    end if;
    CS := CanonicalSheaf(C);
    boo := (assigned CS`Mfull) and (ColumnWeights(Module(CS)) eq [-1]);
    return boo,g;

end function;

function simplify_map(mp)
// apply ReduceMapDegree if domain is ordinary projective (codomain will
//  always be here). This should usually give a large reduction of the degree
//  when a generic canonical map is used at the start. Is there anything else
//  that can be done?

    if IsOrdinaryProjective(Domain(mp)) then
	eqns := ReduceMapDegree(mp);
	mp1 := map<Domain(mp)->Codomain(mp)|eqns : Check := false>;
	return mp1;
    end if;
    return mp;
end function;

function do_hyperelliptic_case(C,cmap)
// C is (geometrically) hyperelliptic and cmap is the canonical map
//  from C to a rational normal curve in P^{g-1}

    X := Codomain(cmap);
    P := Ambient(X);
    g := Rank(CoordinateRing(P));
    if g eq 2 then
	P1 := Curve(P);
	mp := map<C->P1|DefiningEquations(cmap)>;
	return mp;
    end if;
    prm := ParametrizeRationalNormalCurve(X);
    prm := Inverse(prm);
    if IsEven(g) then return Expand(cmap*prm); end if;
    // g odd : prm maps to a conic
    mp := Expand(cmap*prm);
    con := Codomain(prm);
    bsoln, pt := HasRationalPoint(con);
    if not bsoln then //extend to a quadratic field
      seq := conic_point(con);
      K := Universe(seq);
      P2K := ProjectiveSpace(K,2);
      CK := BaseChange(C,K);
      _,prj := Projection(P2K,P2K!seq);
      defs := [R1!f : f in DefiningPolynomials(mp)] where
		R1 is CoordinateRing(Ambient(CK));
    else
      CK := C; K := BaseRing(C);
      P2 := Ambient(con);
      _,prj := Projection(P2,P2!Eltseq(pt));
      defs := DefiningPolynomials(mp);      
    end if;
    vs := [Evaluate(f,defs) : f in DefiningPolynomials(prj)];
    return map<CK -> Curve(ProjectiveSpace(K,1))|vs>;

end function;

intrinsic GenusAndCanonicalMap(C::Crv) -> RngIntElt,BoolElt,MapSch
{Returns the genus of C, whether C is hyperelliptic or genus less than 2 and, if the genus
is greater than 1, a map of C onto its canonical image in ordinary projective space.}

    k := BaseRing(C);
    g := -1;
    if IsOrdinaryProjective(Ambient(C)) and
		(Dimension(Ambient(C)) eq 2) then
	boo,_,Iadj := HasOnlyOrdinarySingularities(C);
	if boo then
	  cls := Sections(CanonicalLinearSystemFromIdeal(Iadj,Degree(C)));
	  if #cls le 1 then
	    return #cls,true,_;
	  end if;
	  g := #cls;
	  cmap := map<C->ProjectiveSpace(k,(#cls)-1)|cls>;
	end if;
    end if;
    if g eq -1 then
	boo,g1 := is_canonical(C);
	if boo then
	  return g1,false,IdentityMap(C);
	end if;
    end if;
    if g eq -1 then
	g := Genus(C);
	if g le 1 then return g,true,_; end if;
	cmap := CanonicalMap(C);
    end if;

    Ccan,bHyp := CanonicalImage(C,cmap);
    cmap := map<C->Ccan|DefiningPolynomials(cmap) : Check := false>;
    return g,bHyp,cmap;

end intrinsic;

function genus3or4_gon3(cmap,is_can)
    Cc := Codomain(cmap);//canonical image
    k := BaseRing(Cc);
    phi := CliffordIndexOne(Cc);
    K := BaseRing(Domain(phi));
    if (not is_can) and (not (K cmpeq k)) then
      CK := BaseChange(Domain(cmap),K); CcK := Domain(phi);
      cmap := map<CK->CcK|defs> where defs is 
	[R1!f : f in DefiningPolynomials(cmap)] where
	  R1 is CoordinateRing(Ambient(CK));
    end if;
    if not is_can then
      phi := Expand(cmap*phi);
      phi := simplify_map(phi);
    end if;
    return phi;
end function;

intrinsic Genus2GonalMap(C::Crv) -> MapSch
{Computes a degree 2 map to P^1 for a genus 2 curve}

    g,bHyp,cmap := GenusAndCanonicalMap(C);
    assert bHyp;
    require g eq 2: "C should be a curve of genus 2";
    return cmap;

end intrinsic;

intrinsic Genus3GonalMap(C::Crv : IsCanonical:=false) -> RngIntElt,MapSch
{Computes smallest degree (gonal) maps to P^1 for a genus 3 curve, possibly over
a finite extension of the base field. Returns the gonality and the map.
If C is a canonical curve in ordinary projective space, IsCanonical should be set to
true for efficiency}

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
    require g eq 3: "C should be a curve of genus 3";
    if bHyp then
	mp := do_hyperelliptic_case(C,cmap);
	return 2,mp;
    end if;
    //gonality 3 - Cc is smooth plane quartic
    phi := genus3or4_gon3(cmap,is_can);
    return 3,phi;

end intrinsic;

intrinsic Genus4GonalMap(C::Crv : IsCanonical:=false) -> RngIntElt,MapSch
{Computes smallest degree (gonal) maps to P^1 for a genus 4 curve, possibly over
a finite extension of the base field. Returns the gonality and the map.
If C is a canonical curve in ordinary projective space, IsCanonical should be set to
true for efficiency}

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
    require g eq 4: "C should be a curve of genus 4";
    if bHyp then
	mp := do_hyperelliptic_case(C,cmap);
	return 2,mp;
    end if;
    //gonality 3
    phi := genus3or4_gon3(cmap,is_can);
    return 3,phi;

end intrinsic;

