freeze;

intrinsic CompletionG1(O::RngFunOrd, P::PlcFunElt : Precision := 50) -> Rng, Map
{Return the completion of O at the place P}

    require Type(CoefficientRing(O)) ne RngFunOrd : "Order must not be represented as an extension of another order";
    require FunctionField(O) eq FunctionField(P) : "Place and order must be of the same function field";

    if Degree(P) eq 1 then
        C := PowerSeriesRing(ResidueClassField(P) : Precision := Precision);
        m := map<O -> C | e :-> C!Expand(FunctionField(O)!e, P : AbsPrec := Precision)>;
    else
        R := RationalExtensionRepresentation(CoefficientRing(FunctionField(O)));
        if IsPrime(Minimum(P)*O) then
            pl := Places(R)!Place(Minimum(P)*O);
            C, cm := Completion(R, pl : Precision := Precision);
            C := PowerSeriesRing(CoefficientRing(C), C`DefaultPrecision);
        else
            C := PowerSeriesRing(ConstantField(FunctionField(O)), Precision);
            C := UnramifiedExtension(C, DefiningPolynomial(ResidueClassField(pl)));
            _, m := OptimizedRepresentation(C);
        end if;
        F := LocalFactorization(PolynomialRing(C)!DefiningPolynomial(O));
        for f in F do
            g := PolynomialRing(O)![c @@ cm : c in Coefficients(f[1])];
            I := ideal<O | Minimum(P), Evaluate(g, O!FunctionField(O).1)>;
            if I eq Ideal(P) then
                C := UnramifiedExtension(C, f[1]);
                break;
            end if;
        end for;
        m := map<O -> C | 
                        x :-> &+[C!cm(c[i])*C.1^(i - 1) : i in [1 .. #c]] where c is Eltseq(FunctionField(O)!x), 
                        y :-> &+[FunctionField(O)!(c[i] @@ cm)*FunctionField(O).1^(i - 1) : i in [1 .. #c]] where c is Eltseq(y)>;
    end if;
    return C, m;
end intrinsic;

