
freeze;

import "show.m"          : show_time;

declare attributes AlgMat:
    DiagonalBlockDecomposition,
    DiagonalBlockStructure;

declare attributes Map: DiagMap;

//*********************************************************************

declare attributes AlgMat: DiagMapSeen;

intrinsic NaturalFreeAlgebraCover(A::AlgMat) -> Map
{Returns the map of a free algebra onto the matrix algebra A, such that
   the variables of the free algebra go the the generators of the algebra}

    F<[x]> := FreeAlgebra(CoefficientRing(A), Ngens(A));
    _<z> := BaseRing(F);

    phi := 0;

    if assigned A`DiagonalBlockDecomposition then
	D := A`DiagonalBlockDecomposition;
	vprint Presentation: "Use DiagonalBlockDecomposition:", D;
//"DECOMP:", [IndecomposableSummands(RModule(x)): x in D];
//"Nagens:", [Nagens(RModule(x)): x in D];
//"FACTORS:", [CompositionFactors(RModule(x)): x in D];
	if #D gt 1 then

	    Df := [hom<F -> Generic(S) | [S.i: i in [1 .. Ngens(S)]]>: S in D];

	    if 0 eq 1 then
		/*
		AKS: Oct 2013; save evaluations.
		*/

		GA := Generic(A);

		S := AssociativeArray();
		for i := 1 to Rank(F) do
		    S[F.i] := <S.i: S in D>;
		end for;
		A`DiagMapSeen := S;

		function eval_recall(w)

		    function eval_mon(m)
			S := A`DiagMapSeen;
			if IsDefined(S, m) then
//"REUSE", m;
			    return S[m];
			end if;

			E := 0;
			l := Length(m);
			for i := 1 to l - 1 do
			    lhs := &*[m[j]: j in [1 .. i]];
			    rhs := &*[m[j]: j in [i + 1 .. l]];
			    if IsDefined(S, lhs) and IsDefined(S, rhs) then
//printf "PROD %o = (%o)*(%o)\n", m, lhs, rhs;
				E := <
				    S[lhs, j] * S[rhs, j]: j in [1 .. #Df]
				>;
				break;
			    end if;
			end for;

			if E cmpeq 0 then
			for i := 1 to l - 2 do
			    for j := i + 1 to l - 1 do
				m1 := &*[m[k]: k in [1 .. i]];
				m2 := &*[m[k]: k in [i + 1 .. j]];
				m3 := &*[m[k]: k in [j + 1 .. l]];
				if
				    IsDefined(S, m1) and IsDefined(S, m2) and
				    IsDefined(S, m3)
				then
//printf "PROD3 %o = (%o)*(%o)*(%o)\n", m, m1, m2, m3;
				    S1 := S[m1];
				    S2 := S[m2];
				    S3 := S[m3];
				    E := <
					S1[k] * S2[k] * S3[k]: k in [1 .. #Df]
				    >;
				    break i;
				end if;
			    end for;
			end for;
			end if;

			if E cmpeq 0 then
//"NEW", m;
			    E := <f(m): f in Df>;
			end if;

			TA := A;
			TA`DiagMapSeen := 0;
			S[m] := E;
			TA`DiagMapSeen := S;
			return E;
		    end function;

		    R := <0: i in [1 .. #D]>;
		    C, M := CoefficientsAndMonomials(w);
		    for i := 1 to #C do
			NR := <>;
			E := eval_mon(M[i]);
			for j := 1 to #R do
			    Append(~NR, R[j] + C[i]*E[j]);
			end for;
			R := NR;
		    end for;
		    //R := <GA!X: X in R>;
	//assert R eq <f(w): f in Df>;
		    return R;

		end function;

		phi := hom<F -> GA | w :-> DiagonalJoin(eval_recall(w))>;
		phi`DiagMap := func<w | BlockDiagMat(eval_recall(w))>;
	    else

/*
    // Hacked
    ODf := Df;
    Df := [
	function(x)
	    printf "Eval %o (dim %o)\n", x, Degree(D[i]);
	    [Eltseq(t): t in Monomials(x)];
	    return ODf[i](x);
	end function:
	    i in [1 .. #D]
    ];
*/

		phi := hom<
		    F -> Generic(A) | e :-> DiagonalJoin(<f(e): f in Df>)
		>;
		phi`DiagMap := func<x | BlockDiagMat(<f(x): f in Df>)>;
	    end if;
	end if;
    end if;

    if phi cmpeq 0 then
	phi := hom<F -> Generic(A) | [A.i:i in [1 .. Ngens(A)]]>;
    end if;

    A`NaturalFreeAlgebraCover := phi;

    return phi;

end intrinsic;

//*********************************************************************

function meataxe(A)

     M := RModule(A);

     if assigned A`DiagonalBlockDecomposition then
	 D := A`DiagonalBlockDecomposition;
	 A`DiagonalBlockStructure := [Degree(S): S in D];
	 vprint Presentation:
	     "Given Diagonal Block Structure:", A`DiagonalBlockStructure;
     else
	 D := DiagonalBlockDecomposition(M);
	 if #D gt 1 then
	    A`DiagonalBlockDecomposition := [Action(S): S in D];
	    A`DiagonalBlockStructure := [Dimension(S): S in D];
	    vprint Presentation:
		"Found Diagonal Block Structure:", A`DiagonalBlockStructure;
	 end if;
	 delete D;
     end if;

	t := Cputime();
	CF := Reverse(Constituents(M));
	K := CoefficientRing(M);
	p := Characteristic(K);
     phi := NaturalFreeAlgebraCover(A);
     t := Ngens(A);
     F := Domain(phi);
	s_M := CF;
	a_A := [Action(M): M in s_M];
     s_A := [hom<F -> X | [X.i: i in [1 .. t]]>: X in a_A]; 
	d := [DimensionOfEndomorphismRing(M): M in s_M];
	r := #s_M;

	n := [Degree(a_A[i]) div d[i] : i in [1..r]];
	q := [d[i] eq 1 select #K else (#K)^d[i] : i in [1..r]];
	show_time("Meataxe", Cputime(t));

	vprint Presentation: A;
	vprint Presentation: M;
	vprint Presentation: "Composition series length =", #CF;
	vprint Presentation: "#Simples =", #s_M;
	vprint Presentation: "Simple dimensions =", 
		Reverse(Sort([Dimension(M) : M in s_M]));
	vprint Presentation: "";
	vprint Presentation: "The A_i are:";
	for i := 1 to r do
		vprint Presentation: i, s_A[i]; 
		vprint Presentation: "n_i =", n[i];
		vprint Presentation: "d_i =", d[i];
		vprint Presentation: "q_i =", q[i];
	end for;

	return  s_A, n, d, q;

end function;

//*******************************************************************

intrinsic SimpleQuotientAlgebras(A::AlgMat) -> Rec
{The simple quotient algebras of the matrix algebra A.}

if assigned A`SimpleQuotientAlgebras then
return A`SimpleQuotientAlgebras;
end if;

SimQuots := recformat<SimpleQuotients     :SeqEnum,
		       DegreesOverCenters     :SeqEnum,
		       DegreesOfCenters       :SeqEnum,
		       OrdersOfCenters       :SeqEnum>;
ss, nn, dd, qq := meataxe(A);
sqq := rec< SimQuots | SimpleQuotients       := ss,
		       DegreesOverCenters     := nn,
		       DegreesOfCenters       := dd,
		       OrdersOfCenters       := qq>;
A`SimpleQuotientAlgebras := sqq;

            return sqq;

end intrinsic;

//*******************************************************************

intrinsic SimpleQuotientAlgebras(A::AlgMat, S::SeqEnum) -> Rec
{The simple quotient algebras of the action on the directs sum of the
given sequence of simple modules over an algebra A.}

if assigned A`SimpleQuotientAlgebras then
return A`SimpleQuotientAlgebras;
end if;

SimQuots := recformat<SimpleQuotients     :SeqEnum,
                       DegreesOverCenters     :SeqEnum,
                       DegreesOfCenters       :SeqEnum,
                       OrdersOfCenters       :SeqEnum>;
phi := NaturalFreeAlgebraCover(A);
t := Ngens(A);
F := Domain(phi);
a_A := [Action(M): M in S];
ss := [hom<F -> X | [X.i: i in [1 .. t]]>: X in a_A];
dd := [Dimension(AHom(x,x)): x in S];
nn := [Dimension(S[i]) div dd[i]: i in [1 .. #S]];
qq := [(#BaseRing(A))^x:x in dd];
sqq := rec< SimQuots | SimpleQuotients       := ss,
                       DegreesOverCenters     := nn,
                       DegreesOfCenters       := dd,
                       OrdersOfCenters       := qq>;
A`SimpleQuotientAlgebras := sqq;

            return sqq;

end intrinsic;




// Changes:
// Defining meataxe over A, not M;
// No longer returning A;
// Returning the maps to the quotients not the quotients directly.
// The intrinsic returns a record.
