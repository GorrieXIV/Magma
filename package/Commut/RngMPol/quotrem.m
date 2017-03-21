freeze;

intrinsic Quotrem(f::RngMPolElt, g::RngMPolElt) -> RngMPolElt, RngMPolElt
{Return q and r such that r is the normal form of f w.r.t. [g] and f = q*g + r};

    require Generic(Parent(f)) cmpeq Generic(Parent(g)):
	"Arguments are not compatible";
    require not IsZero(g): "Argument 2 must be non-zero";

    r, C := NormalForm(f, [g]);
    q := C[1];
    return q, r;

end intrinsic;
