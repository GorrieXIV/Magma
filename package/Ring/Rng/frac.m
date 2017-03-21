/*
AKS 29/4/96.
*/

freeze;

intrinsic ResidueClassField(I::RngInt) -> Fld, Map
{The fraction field R/I where I is a maximal ideal of the ring of integers R}

  return ResidueClassField(Integers(), I);
end intrinsic;

intrinsic ResidueClassField(R::RngInt, I::RngInt) -> Fld, Map
{"} // "
    a := Generator(R);
    require a ne 0: "Illegal zero ideal";

    b := Generator(I);
    require b mod a eq 0: "RHS is not an ideal";
    
    p := b div a;
    require IsPrime(p): "Ideal is not maximal";

    if a eq 1 then
        // this is better (map is internal, and accepts FldRatElt)
        return ResidueClassField(p);
    else
        // TO DO: this case was always nonsense (needs to divide by a)
        F := GF(p);
        return F, Coercion(R, F);
    end if;
end intrinsic;

intrinsic ResidueClassField(R::RngMPol, I::RngMPol) -> Fld, Map
{The fraction field R/I where I is a maximal ideal of R}

    require IsCompatible(R, I): "Arguments are not compatible";
    require not IsProper(R): "LHS is not the full ring";

    K := CoefficientRing(R);
    require IsField(K): "Coefficient ring is not a field";

    require IsMaximal(I): "Ideal is not maximal";

    case Type(K):
	when FldFin, FldRat, FldNum:
	    F := K;
	    IF := I;
	    im := [];
	    n := Rank(R);
	    for i := n to 1 by -1 do
		//print "i:", i;
		//print "first IF:", IF;
		U := PolynomialRing(F);
		u := U ! UnivariatePolynomial(
		    UnivariateEliminationIdealGenerator(IF, i)
		);
		v := u;
		//print "i:", i, "u:", u;
		//ff := Factorization(u);
		//v := ff[1][1];
		//print "ff:", ff;
		//for t in ff do
		    //print MultivariatePolynomial(Generic(IF), t[1], i) in IF;
		//end for;
		//print "v:", v;
		if Degree(v) gt 1 then
		    FF := ext<F | v>;
		    im := [FF ! x: x in im];
		    F := FF;
		    imi := F.1;
		else
		    imi := F ! -Coefficient(v, 0);
		end if;
		im := [imi] cat im;
		if i gt 1 then
		    ii := i - 1;
		    IFG := PolynomialRing(F, ii);
		    h := hom<IF -> IFG | [IFG.i: i in [1..ii]] cat [imi]>;
		    IF := ideal<IFG | [h(f): f in Basis(IF)]>;
		    print IF;
		    Groebner(IF);
		    print IF;
		end if;
	    end for;

	    if Type(K) eq FldFin then
		// Flatten the field
		P := PrimeField(F);
		FF := ext<P | DefiningPolynomial(F, P)>;
		im := [FF | Eltseq(x, P): x in im];
		F := FF;
	    end if;

	    f := hom<R -> F | im>;
	else
	    require false: "Bad coefficient ring type";
    end case;

    return F, f;
end intrinsic;

intrinsic ResidueClassField(R::RngUPol, I::RngUPol) -> Fld, Map
{The fraction field R/I where I is a maximal ideal of R}

    require IsCompatible(R, I): "Arguments are not compatible";
    require IsOne(Generator(R)): "LHS is not the full ring";

    K := CoefficientRing(R);
    require IsField(K): "Coefficient ring is not a field";

    G := Generator(I);
    require IsIrreducible(G): "Ideal is not maximal";

    return ResidueClassField(I);

end intrinsic;
