freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
// testing for equivalence of elements of PSL2(Z) with respect    //
// to quotienting by congruence subgroups.                        //
//                                                                //
////////////////////////////////////////////////////////////////////




import "coercion.m":  MemberTest;

intrinsic IsEquivalent(g::GrpPSL2Elt,h::GrpPSL2Elt,G::GrpPSL2) -> BoolElt,
   GrpPSL2Elt
   {Returns true if A is equivalent to B under action of G, and
    if they are, also returns a matrix g with g*A = B}
    require Parent(g) eq Parent(h): "first and second arguements
    must be defined over the same matrix group";
    a,b,c,d := Explode(Eltseq(g`Element));
    A,B,C,D := Explode(Eltseq(h`Element));
    mA := g`Element;
    mB := h`Element;
    // M will be the matrix g*h^(-1), but we don't necessarily need
    // to compute all it's coefficients.
    // Thus, at some point this function could be improved.
    M := mA*mB^(-1);
    if IsCoercible(G,M) then
	return true, G!M;
    else
	return false, _;
    end if;
end intrinsic;


intrinsic IsEquivalent(g::GrpMatElt,h::GrpMatElt,G::GrpPSL2) -> BoolElt,
    GrpPSL2Elt
    {Returns true if A is equivalent to B under action of G}
    require Parent(g) eq Parent(h): "first and second arguements
    must be defined over the same matrix group";
    require NumberOfColumns(g) eq 2
    and NumberOfColumns(h) eq 2
    and NumberOfRows(g) eq 2
    and NumberOfRows(h) eq 2: "first and second arguments must be
    2 by 2 matrices";
    // M will be the matrix g*h^(-1), but we don't necessarily need
    // to compute all it's coefficients.
    // Thus, at some point this function could be improved.
    M := g*h^(-1);
    if MemberTest(G,M) then
	return true, G!M;
    else
	return false, _;
    end if;
end intrinsic;

