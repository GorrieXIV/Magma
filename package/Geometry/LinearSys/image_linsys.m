freeze;

///////////////////////////////////////////////////////////////////////
// image_linsys.m
///////////////////////////////////////////////////////////////////////	


intrinsic Image(f::MapSch,X::Sch,d::RngIntElt) -> SeqEnum
{The scheme defined by polynomials of degree d in the codomain of f which
vanish on f(X)}
    return Scheme(Ambient(Codomain(f)),Sections(ImageSystem(f,X,d)));
end intrinsic;

intrinsic ImageSystem(f::MapSch,X::Sch,d::RngIntElt) -> LinearSys
{The linear system of hypersurfaces of degree d in the codomain of f which
contain f(X)}
    // Notation f : P -> Q, X in Q, L all polys of deg d on Q.
    require X subset Domain(f):
	"The second argument must be in the domain of the first";

    L := LinearSystem(Codomain(f),d);
    M,pbmap := Pullback(f,L);
    M1 := LinearSystem(M,X);

    WM := CoefficientSpace(M);
    WM1inWM := sub< WM | [ CoefficientMap(M)(PolynomialMap(M1)(b)) :
					b in Basis(CoefficientSpace(M1)) ] >;
    QW,pi := quo< WM | WM1inWM >;

    WL := CoefficientSpace(L);
    bigm := hom< WL -> QW | [ pi(pbmap(b)) : b in Basis(WL) ] >;
    return LinearSystem(L,Kernel(bigm));
end intrinsic;

intrinsic Image(f::MapSch,X::Sch,d::SeqEnum) -> SeqEnum
{The scheme defined by polynomials of degree d in the codomain of f which (which lies in a toric variety with as many gradings as the length of the sequence d) vanish on f(X)}
    return Scheme(Ambient(Codomain(f)),Sections(ImageSystem(f,X,d)));
end intrinsic;

intrinsic ImageSystem(f::MapSch,X::Sch,d::SeqEnum) -> LinearSys
{The linear system of hypersurfaces of multidegree d in the codomain of f (which lies in a toric variety with as many gradings as the length of the sequence d) which contain f(X)}
    // Notation f : P -> Q, X in Q, L all polys of deg d on Q.
    require X subset Domain(f):
        "The second argument must be in the domain of the first";

    L := LinearSystem(Codomain(f),d);
    M,pbmap := Pullback(f,L);
    M1 := LinearSystem(M,X);

    WM := CoefficientSpace(M);
    WM1inWM := sub< WM | [ CoefficientMap(M)(PolynomialMap(M1)(b)) :
                                        b in Basis(CoefficientSpace(M1)) ] >;
    QW,pi := quo< WM | WM1inWM >;

    WL := CoefficientSpace(L);
    bigm := hom< WL -> QW | [ pi(pbmap(b)) : b in Basis(WL) ] >;
    return LinearSystem(L,Kernel(bigm));
end intrinsic;

