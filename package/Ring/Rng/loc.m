/*
AKS 29/4/96.
*/

freeze;

intrinsic Localization(R::RngInt, P::RngInt) -> Rng, Map
{The localization of R at prime ideal P}

    g := Generator(P);
    require g eq 0 or IsPrime(g): "Ideal is not prime";

    Q := RationalField();

    if g eq 0 then
	return Q, Coercion(R, Q);
    end if;

    V := ValuationRing(Q, g);
    return V, Coercion(R, V);
end intrinsic;

intrinsic Localization(R::RngUPol, P::RngUPol) -> Rng, Map
{The localization of R at prime ideal P}

    require IsCompatible(R, P): "Arguments are not compatible";
    require IsOne(Generator(R)): "LHS is not the full ring";

    K := CoefficientRing(R);
    require IsField(K): "Coefficient ring is not a field";

    G := Generator(P);
    require G eq 0 or IsIrreducible(G): "Ideal is not prime";

    F := FunctionField(K);

    if G eq 0 then
	return F, Coercion(R, F);
    end if;

    G := Integers(F)!G;
    V := ValuationRing(F, G);
    return V, Coercion(R, V);
end intrinsic;

intrinsic Localization(R::RngMPol, P::RngMPol) -> Rng, Map
{The localization of R at prime ideal P}

    require IsCompatible(R, P): "Arguments are not compatible";
    require Generic(R) cmpeq R: "LHS is not the full ring";

    K := CoefficientRing(R);
    require IsField(K): "Coefficient ring is not a field";

    require IsPrime(P): "Ideal is not prime";

    return Localization(P);
end intrinsic;
