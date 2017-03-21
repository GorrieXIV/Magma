freeze;

/*******************************************************************************
			    IsFree
*******************************************************************************/

intrinsic IsFree(M::ModMPol) -> BoolElt
{Return whether M is a free module.}
    return IsZero(MinimalSyzygyModule(Presentation(M)));
end intrinsic;
