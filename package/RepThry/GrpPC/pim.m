freeze;

intrinsic ProjectiveIndecomposableModules(G::GrpPC, p::RngIntElt) -> SeqEnum
{The projective indecomposable modules for G over a (notional) characteristic p
splitting field for G}

    require p gt 0 and IsPrime(p): "2nd argument must be a prime";

    if #G mod p ne 0 then
	res := AbsolutelyIrreducibleModulesSchur(G, GF(p));
	return res;
    end if;

    BT, D := BrauerCharacterTable(G, p);
    degs := {Integers()|Degree(x): x in BT};
    degs := {y where _, y := Valuation(d,p):d in degs};
    H := HallSubgroup(G, -p);
    M := AbsolutelyIrreducibleModulesSchur(H, GF(p):ExactDimension := degs);
    cmp := function(x,y)
	r := Dimension(x)-Dimension(y);
	if r ne 0 then return r; end if;
	r := Degree(BaseRing(x)) - Degree(BaseRing(y));
	return r;
    end function;
    Sort(~M, cmp);
    XM := [BrauerCharacter(m):m in M];
    res := [];
    b := 0;
    for phi in BT do
	phiH := Restriction(phi, H);
	for i := 1 to #XM do
	    if not IsZero(InnerProduct(phiH, XM[i])) then
		Append(~res, Induction(M[i], G));
		break i;
	    end if;
	end for;
    end for;
    return res;

end intrinsic;
