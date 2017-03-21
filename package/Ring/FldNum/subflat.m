freeze;

intrinsic '&meet'(Q::[SubFldLatElt]) -> SubFldLatElt
{The intersection of the subfield lattice elements of Q}
    require #Q ge 1: "Argument 1 must be non-empty";
    S := Q[1];
    for i := 2 to #Q do
	S := S meet Q[i];
    end for;
    return S;
end intrinsic;
