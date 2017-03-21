freeze;

intrinsic Automorphism(C::CrvRat,S::SetIndx,T::SetIndx) -> MapAutSch
    {The automorphism taking the three element indexed set of
    points S to the three element indexed set of points T.}
    K := BaseRing(C);
    require C(K) cmpeq Universe(S) and C(K) cmpeq Universe(T) :
        "Arguments 2 and 3 must consist of points " *
        "of argument 1 over its base ring.";
    require #S eq 3 and #T eq 3 :
        "Arguments 2 and 3 must each consist of three elements.";
    P2 := Ambient(C);
    phi0 := Parametrization(C,S[1]);
    psi1 := TranslationOfSimplex(Domain(phi0),[ p@@phi0 : p in S ]); 
    psi2 := TranslationOfSimplex(Domain(phi0),[ q@@phi0 : q in T ]);
    return Inverse(psi1*phi0)*psi2*phi0;
end intrinsic;
