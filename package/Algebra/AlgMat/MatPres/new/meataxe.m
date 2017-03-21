
freeze;

import "show.m"          : show_time;

declare attributes AlgMat:
    DiagonalBlockDecomposition,
    DiagonalBlockStructure;

declare attributes Map: DiagMap;

//*********************************************************************

intrinsic NaturalFreeAlgebraCover(A::AlgMat) -> Map
{Returns the map of a free algebra onto the matrix algebra A, such that
   the variables of the free algebra go the the generators of the algebra}

    F := FreeAlgebra(CoefficientRing(A), Ngens(A));

    phi := 0;

    if assigned A`DiagonalBlockDecomposition then
	D := A`DiagonalBlockDecomposition;
	vprint Presentation: "Use DiagonalBlockDecomposition:", D;
	if #D gt 1 then
	    Df := [hom<F -> Generic(S) | [S.i: i in [1 .. Ngens(S)]]>: S in D];
	    phi := hom<F -> Generic(A) | e :-> DiagonalJoin(<f(e): f in Df>)>;

	    phi`DiagMap := func<x | BlockDiagMat(<f(x): f in Df>)>;
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
