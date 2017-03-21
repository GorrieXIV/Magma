freeze;

intrinsic IsogenyFromKernel(C::CrvEll, f::RngUPolElt : Check := true)
							-> CrvEll, Map
{Given an elliptic curve E and a univariate polynomial S defining a
 subgroup, this function returns an elliptic curve E1 and a separable
 isogeny I : E -> E1 with kernel defined by S}

    return IsogenyFromKernel(C, f, 0 : Check:=Check);
end intrinsic;

intrinsic IsogenyFromKernelFactored(C::CrvEll, f::RngUPolElt : Check:=true)
							-> CrvEll, Map
{Given an elliptic curve E and a univariate polynomial S defining a subgroup,
 this function returns an elliptic curve E1 and a sequence of isogenies
 whose product is a separable isogeny I : E -> E1 with kernel defined by S}

    return IsogenyFromKernelFactored(C, f, 0 : Check:=Check);
end intrinsic;

intrinsic TorsionSubgroupScheme(G::SchGrpEll, n::RngIntElt) -> SchGrpEll
{Returns the scheme corresponding to the subgroup of G containing the
 n-torsion points of G}
    require n ne 0 : "0-torsion points are nonsensical";
    return SubgroupScheme(G, DivisionPolynomial(Curve(G), Abs(n)));
end intrinsic;

intrinsic IsogenyFromKernel(G::SchGrpEll) -> CrvEll, Map
{Given a subgroup G of an elliptic curve E, returns an elliptic curve E1
 and an isogeny I : E -> E1 with kernel G}

    require G cmpne Curve(G):
	"Argument must be a PROPER subgroup scheme of an elliptic curve"; 
    return IsogenyFromKernel(Curve(G), DefiningSubschemePolynomial(G));
end intrinsic;

intrinsic IsogenyFromKernelFactored(G::SchGrpEll) -> CrvEll, Map
{Given a subgroup G of an elliptic curve E, returns an elliptic curve E1
 and a sequence of isogenies whose product is an isogeny I : E -> E1 with
 kernel G}

    require G cmpne Curve(G):
	"Argument must be a PROPER subgroup scheme of an elliptic curve"; 
    return IsogenyFromKernelFactored(Curve(G), DefiningSubschemePolynomial(G));
end intrinsic;
