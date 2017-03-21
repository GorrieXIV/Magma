freeze;

///////////////////////////////////////////////////////////////////////
// elt_linsys.m
///////////////////////////////////////////////////////////////////////

intrinsic Span(Q::{Pt}) -> Sch
{The linear space linearly spanned by the points of P}
    require #Q ge 1:
	"The set is empty";
    P := Ambient(Scheme(Representative(Q)));
    return Scheme(P,Sections(LinearSystem(L,SetToSequence(Q1))))
		where Q1 is { P ! p : p in Q }
    		where L is LinearSystem(P,1);
end intrinsic;

intrinsic Span(S::Sch,T::Sch) -> Sch
{The linear space in the scheme S spanned by the subscheme T}
    require T subset S:
	"Second argument must be contained in the first";
    L := LinearSystem(Ambient(S),1);
    return Scheme(S,Sections(LinearSystem(L,T)));
end intrinsic;

intrinsic Line(P::Prj,S::{Pt}) -> Sch
{The unique line in the projective space P through the points of S if it exists}
    require #S ge 1:
	"The set is empty";
    require &and[ p in P : p in S]:
	"Points do not lie in the given space";
    seq_of_pts := [ P ! s : s in S ];
    C := Scheme(P,Sections(LinearSystem(L,seq_of_pts)))
    		where L is LinearSystem(P,1);
    require Dimension(C) eq 1:
	"Points do not span a line";
    if Dimension(P) eq 2 then
	_,C := IsCurve(C);
    end if;
    return C;
end intrinsic;

intrinsic Conic(P::Prj,S::{Pt}) -> Crv
{The unique conic in the projective plane P through the points of S if it exists}
    require Dimension(P) eq 2 and Gradings(P) eq [ [1,1,1] ]:
	"P is not an ordinary projective plane";
    S := SchemeThrough(P,2,S);
    require Dimension(S) eq 1:
	"Points are not contained in a conic";
    return Curve(P,Polynomial(S));
end intrinsic;

intrinsic SchemeThrough(S::Sch,d::RngIntElt,P::{Pt}) -> RngIntElt
{The unique hypersurface of degree d of S passing through the points of P}
    seq_of_pts := [ S ! s : s in P ];
    secs := Sections(LinearSystem(LinearSystem(Ambient(S),d),seq_of_pts));
    require #secs eq 1:
	"S does not determine a unique hypersurface";
    return Scheme(S,secs[1]);
end intrinsic;

intrinsic Line(C::Crv,p::Pt,q::Pt) -> Crv
{The line through p and q as points of C}
    require p in C and q in C:
        "Point arguments do not lie on the curve";
    if p eq q then
        return TangentLine(C,p);
    else
        return  Line(Ambient(C),{p,q});
    end if;
end intrinsic;

intrinsic HasLine(P::Prj,S::{Pt}) -> Bool
{True iff there exists a line in the projective space P through the points of S.}
    require #S ge 1:
	"The set is empty";
    require &and[ p in P : p in S]:
	"Points do not lie in the given space";
    seq_of_pts := [ P ! s : s in S ];
    C := Scheme(P,Sections(LinearSystem(L,seq_of_pts)))
    		where L is LinearSystem(P,1);
    if Dimension(C) ne 1 then
		return false;
	else
		return true;
	end if;
end intrinsic;

intrinsic HasConic(P::Prj,S::{Pt}) -> Bool
{True iff there is a unique conic in the projective plane P through the points of S.}
    require Dimension(P) eq 2 and Gradings(P) eq [ [1,1,1] ]:
	"P is not an ordinary projective plane";
    seq_of_pts := [ P ! x : x in S ];
    secs := Sections(LinearSystem(LinearSystem(P,2),seq_of_pts));
    if #secs ne 1 then return false; end if;
	if Dimension(Scheme(P,secs[1])) ne 1 then
		return false;
	else
		return true;
	end if;
end intrinsic;
