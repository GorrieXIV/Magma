freeze;

/*
Steenrod Operations.
Gregor Kemper <Gregor.Kemper@IWR.Uni-Heidelberg.De>
October 1996.
*/

intrinsic SteenrodOperation(f::RngMPolElt, i::RngIntElt) -> RngMPolElt
{The i-th Steenrod operation P^i(f) of f (f must be a multivariate
polynomial with coefficients in a finite field and i must be
a non-negative integer)}

    P:=Parent(f);
    K:=CoefficientRing(P);

    require Type(K) eq FldFin: "Coefficient ring is not a finite field";
    requirege i, 0;
    
    if IsZero(f) then
        return f;
    end if;

    mons:=Monomials(f);
    coeffs:=Coefficients(f);
    if #mons gt 1 then
        mons:=[SteenrodOperation(m,i): m in mons];
	return &+ [coeffs[n]*mons[n]: n in [1..#mons]];
    end if;
    
    q:=#K;
    n:=Rank(P);
    d:=TotalDegree(f);
    if i gt d then
        return 0;
    elif i eq d then
        return f^q;
    end if;
    for j in [1..n] do
        e:=Degree(mons[1],P.j);
	if e gt 0 then
	    x:=P.j;
	    break;
	end if;
    end for;
    c:=Coefficient(mons[1],x,e);
    if c ne 1 then
        return coeffs[1]*
	    (&+ [SteenrodOperation(x^e,j)*SteenrodOperation(c,i-j):
	    j in [Max(0,i-d+e)..Min(i,e)]]);
    end if;
    return Binomial(e,i)*coeffs[1]*x^(e+i*(q-1));

end intrinsic;


/*
Other stuff.
*/

intrinsic IsModular(R::RngInvar) -> BoolElt
{Return whether invariant ring R is modular}
    c := Characteristic(BaseRing(R));
    return c gt 0 and GCD(#Group(R), c) gt 1;
end intrinsic;

intrinsic FreeResolution(R::RngInvar) -> []
{A free resolution of (the module of) R}
    return FreeResolution(Module(R));
end intrinsic;

intrinsic MinimalFreeResolution(R::RngInvar) -> []
{A minimal free resolution of (the module of) R}
    return MinimalFreeResolution(Module(R));
end intrinsic;

intrinsic HomologicalDimension(R::RngInvar) -> []
{The homological dimension of R}
    return HomologicalDimension(Module(R));
end intrinsic;
