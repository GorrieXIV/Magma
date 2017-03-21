freeze;


intrinsic IsHomomorphism ( s :: Map ) -> BoolElt
{ Check if s is a homomorphism. s must be a map from GrpPerm to GrpPerm or
  from GrpPC to GrpPC. }

    G := Domain(s);
    H := Codomain(s);
    require (ISA(Type(G), GrpPerm) and ISA(Type(H), GrpPerm)) or
		(ISA(Type(G), GrpPC) and ISA(Type(H), GrpPC)):
		"Map must be between two groups of type GrpPerm or GrpPC";

    if ISA(Type(G), GrpPC) then
	isHom := IsHomomorphism( G, H, [H | s(G.i) : i in [1 .. NPCgens(G)] ] );
    else
	isHom := IsHomomorphism( G, H, [H |  s(G.i) : i in [1 .. Ngens(G)] ] );
    end if;

    return isHom;

end intrinsic;

intrinsic IsHomomorphism ( G :: GrpPC , H :: GrpPerm , c :: SeqEnum ) -> BoolElt, Map
{Determines if the mapping defined by c contructs a homomorphism G -> H.}
    H_c := sub < H | c >;
    if not IsSoluble ( H_c ) then
        return false, _;
    end if;

    R_H_c, phi_H_c := PCGroup ( H_c );
    b, h := IsHomomorphism ( G, R_H_c, [ h @ phi_H_c : h in c ] );
    if not b then
        return false, _;
    end if;

    return true, hom < G -> H | c >;
end intrinsic;

/* 
//Not necessary -- will be replaced by the definition of IsCentral
//in package/Group/GrpMat/util/order.m. So commented out here.
// DR 2 nov 2010.
intrinsic IsCentral(G :: Grp, x :: GrpElt) -> BoolElt
{Is x a central element of the group G}
    return IsCentral(G, sub<G|x>);
end intrinsic;
*/

intrinsic IsInnerAutomorphism(G :: Grp, N :: Grp, f :: Map) -> BoolElt, GrpElt
{True if the automorphism f : N -> N is induced by an inner automorphism of G.
Requires N to be normal in G. If so, a conjugating element of G is also
returned.}
    C := G;
    ce := G!1;
    // "TRIAL CODE";
    for x in Generators(N) do
	g2 := x@f;
	g1 := x^ce;
	fl, z := IsConjugate(C, g1, g2);
	if not fl then
	    return false, _;
	end if;
	ce := ce*z;
	C := Centralizer(C,g2);
    end for;
    return true, ce;
end intrinsic;

intrinsic IsInnerAutomorphism(G :: Grp, f :: Map) -> BoolElt, GrpElt
{True if the automorphism f : G -> G is induced by an inner automorphism of G.
If so, a conjugating element of G is also returned.}
    return IsInnerAutomorphism(G, G, f);
end intrinsic;

intrinsic NDgens ( G :: Grp ) -> RngIntElt
{Returns the number of 'dot' generators of the given group G, i.e. if G is GrpPC then NPCgens,
if G is GrpPerm or GrpMat then Ngens.}

    if Type(G) eq GrpPC then
        return NPCgens(G);
    else
        return Ngens(G);
    end if;

end intrinsic;
