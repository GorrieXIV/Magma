freeze;

intrinsic AddAttributes(T::Cat, L::[MonStgElt])
{Add all attributes in sequence L to the list of valid attributes for
category T}

    for s in L do
	AddAttribute(T, s);
    end for;
end intrinsic;
