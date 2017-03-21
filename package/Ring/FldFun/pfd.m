// Partial fraction decomposition.
// AKS
// 31/03/97

freeze;

function Decomposition(f, Fact)
    F := Parent(f);
    P := IntegerRing(F);

    p := Numerator(f);
    q := Denominator(f);

    if not IsField(CoefficientRing(P)) then
	PP := FieldOfFractions(CoefficientRing(P));
	FF := FunctionField(PP);
	QQ := $$(FF!p / FF!q, Fact);
	denomlcm := func<f | LCM([Denominator(c): c in Eltseq(f)])>;
	return [
	    <P ! p, n, P ! q>
		where p is PP!L * t[1]
		where q is PP!L^n * t[3]
		where L is B * (A div GCD(A, B^n))
		where A is denomlcm(t[1])
		where B is denomlcm(t[3])
		where n is t[2]:
		    t in QQ
	];
    end if;

    Q := [];

    i, p := Quotrem(p, q);
    if i ne 0 then
	//Q := [F | i];
	Append(~Q, <P!1, 1, i>);
    end if;

    s := Fact(q);

    c := p;
    d := q;
    for t in s do
	q := t[1];
	i := t[2];
	qi := q^i;
	d := d div qi;
	g, mc, ma := XGCD(qi, d);
	//assert IsOne(g);

	mc := mc * c;
	ma := ma * c;
	if Degree(mc) ge Degree(d) then
	    mq, mc := Quotrem(mc, d);
	    ma := ma + mq * qi;
	end if;
	c := mc;
	a := ma;

	QQ := [];
	while Degree(a) ge Degree(q) do
	    a, r := Quotrem(a, q);
	    if r ne 0 then
		//Append(~QQ, F!r/F!(q^i));
		Append(~QQ, <q, i, r>);
	    end if;
	    i -:= 1;
	end while;

	Append(~QQ, <q, i, a>);
	Reverse(~QQ);
	Q cat:= QQ;
    end for;
    return Q;
end function;

intrinsic SquarefreePartialFractionDecomposition(f::FldFunRatUElt) -> []
{The (complete) squarefree partial fraction decomposition of f};
    return Decomposition(f, SquarefreeFactorization);
end intrinsic;

intrinsic PartialFractionDecomposition(f::FldFunRatUElt) -> []
{The (complete) partial fraction decomposition of f};
    require HasPolynomialFactorization(BaseRing(Parent(f))):
	"Factorization not available over base ring";
    return Decomposition(f, Factorization);
end intrinsic;
