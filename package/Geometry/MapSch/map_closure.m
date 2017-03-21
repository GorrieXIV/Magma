freeze;

///////////////////////////////////////////////////////////////////////
// map_closure.m
//	Projective closure of maps is in the kernel.
//	Here I compute restriction of maps to patches.
// Gavin Brown 12/00
///////////////////////////////////////////////////////////////////////

 
///////////////////////////////////////////////////////////////////////
//		Restriction of projective maps
///////////////////////////////////////////////////////////////////////


intrinsic RestrictionToPatch(f::MapSch,j::RngIntElt) -> MapSch
{The restriction of f to the jth affine patch of its codomain}
    // the ith patch is usually the one with a 1 in the (n+1-i)th position
    B := Codomain(f);
    require IsProjective(B):
	"The codomain must lie in some projective space";

    require j in [1..NumberOfAffinePatches(B)]:
	"Second argument is in the wrong range";

    return Expand( f * BtoBa ) where 
	BtoBa is Restriction(Inverse(ProjectiveClosureMap(Ambient(Ba))),B,Ba
                                                                : Check:=false)
		   where Ba is AffinePatch(B,j);
end intrinsic;

intrinsic RestrictionToPatch(f::MapSch,i::RngIntElt,j::RngIntElt) -> MapSch
{The restriction of f to a map from the ith affine patch of its domain to
the jth affine patch of its codomain}
    // the ith patch is usually the one with a 1 in the (n+1-i)th position
    A := Domain(f);
    B := Codomain(f);
    require IsProjective(A) and IsProjective(B):
	"The domain and codomain must be projective";
    require i in [1..NumberOfAffinePatches(A)]:
	"Second argument is in the wrong range";
    require j in [1..NumberOfAffinePatches(B)]:
	"Third argument is in the wrong range";
    Aa := AffinePatch(A,i);
    Ba := AffinePatch(B,j);
    return Expand(AaToA * f * BToBa)
	where AaToA is 
	   Restriction(ProjectiveClosureMap(Ambient(Aa)),Aa,A : Check:=false)
	where BToBa is Restriction(
	   Inverse(ProjectiveClosureMap(Ambient(Ba))),B,Ba  : Check:=false);
end intrinsic;

