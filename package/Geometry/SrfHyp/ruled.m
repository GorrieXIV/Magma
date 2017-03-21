// *********************************************************************
// * Package: ruled.mag                                                *
// * ==================                                                *
// *                                                                   *
// * Author: Tobias Beck                                               *
// *                                                                   *
// * Email : Tobias.Beck@oeaw.ac.at                                    *
// *                                                                   *
// * Date  : 9.5.2007                                                  *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Parametrization of surfaces given by rational pencils. The      *
// *   implementation follows strictly and refers to the article:      *
// *   Josef Schicho, Proper Parametrization of Surface with a         *
// *   Rational Pencil, Proceedings of the 2000 International          *
// *   Symposium on Symbolic and Algebraic Computation (St. Andrews),  *
// *   292--300 (electronic), ACM, New York, 2000                      *
// *                                                                   *
// *                                                                   *
// * TODO:                                                             *
// * -----                                                             *
// *                                                                   *
// *   - Problems with Degree(0)=-1?                                   *
// *   - First compose S <- C -> D -> plane, then invert only once?    *
// *   - DoLinearExtension                                             *
// *   - Does randomization in 'PointOnQuadricHypersurface1Chart'      *
// *     always work?
// *                                                                   *
// *********************************************************************
freeze;
import "quadratic.m": PointOnQuadric;




// ======================================
// = Auxiliary functions (not exported) =
// ======================================

// find good weight vectors for diagonal forms
// -------------------------------------------
// input : a diagonal matrix 'M' with integral coefficients
// output: a weight vector s.t. the corresponding quadratic form has
//         degree defect less than or equal to 1 (see equation (3))
// (compare article at the end of the proof of Lemma 1)
function InitialWeights(M)
	degs := [Degree(M[1,1]),Degree(M[2,2]),Degree(M[3,3])];
	
	// start with these weights (must be positive and will only increase)
	wgts := [1,1,1];
	
	// define auxillary values 'tmp' which correspond to the current
	// weighted degrees of the terms, i.e. 'tmp[i] = degs[i] + 2*wgts[i]',
	// we want that '3*Max_i(degs[i] + 2*wgts[i]) - Sum_i(2*wgts[i])' is
	// larger than 'Sum_i(degs[i])' by at most 1
	// => equivalent to '3*Max_i(tmp[i]) - Sum_i(tmp[i]) le 1'
	tmp := [degs[1]+2,degs[2]+2,degs[3]+2];
	max := Max(Max(tmp[1],tmp[2]),tmp[3]);
	
	// make mutual difference of the 'tmp[i]' less or equal 1,
	// hence we already have '3*Max(tmp[i]) - Sum(tmp[i]) le 2'
	for i := 1 to 3 do
		a := (max-tmp[i]) div 2;
		wgts[i] := wgts[i]+a;
		tmp[i] := tmp[i]+2*a;
	end for;
	
	// are there two 'tmp[i]' which are smaller by one than the last?
	// then increase these by 2 and we are done
	if (3*max - (tmp[1]+tmp[2]+tmp[3]) eq 2) then
		for i := 1 to 3 do
			if (tmp[i] lt max) then
				wgts[i] := wgts[i]+1;
				tmp[i] := tmp[i]+2;
			end if;
		end for;
	end if;
	
	return wgts;
end function;


// compute the weighted degree from matrix
// ---------------------------------------
// input : a matrix 'M' and a sequence of weights 'w'
// output: the weighted degree of 'M' (resp. the induced polynomial) w.r.t. 'w'
function MatrixDegree(M, w)
	return Max(Flat([[Degree(M[i,j]) + w[i] + w[j] : i in [1..3]]
	    : j in [1..3]]));
end function;


// compute degree defect from matrix
// ---------------------------------
// input : a matrix 'M' and a sequence of weights 'w'
// output: the degree defect of 'M' (resp. the induced polynomial) w.r.t. 'w'
function MatrixDefect(M, w)
	return (3*MatrixDegree(M,w) - 2*(&+w)) - Degree(Determinant(M));
end function;


// compute the weighted degree of trafo
// ------------------------------------
// input : a matrix 'M' and sequences of weights 'w' and 'u'
// output: the weighted degree of 'M' w.r.t. 'w' and 'u'
// (see article before equation (4))
function TrafoDegree(M, w, u)
	return Max(Flat([[Degree(M[i,j]) - w[i] + u[j] : i in [1..3]]
	    : j in [1..3]]));
end function;


// compute the weighted defect of trafo
// ------------------------------------
// input : a matrix 'M' and sequences of weights 'w' and 'u'
// output: the degree defect of 'M' w.r.t. 'w' and 'u'
// (see article right after equation (4))
function TrafoDefect(M, w, u)
	return (3*TrafoDegree(M,w,u) + (&+w) - (&+u)) - Degree(Determinant(M));
end function;


// find product of irreducible multiple factors of non-zero polynomial
// -------------------------------------------------------------------
// input : a univariate polynomial 'poly'
// output: the product over all factors that have multiplicity greater 1
//         (that is the factors that are at least squares)
function GetSquares(poly)
	assert(not poly eq 0);
	
	A := Gcd(poly, Derivative(poly));
	B := Gcd(A, Derivative(A));
	squares := ExactQuotient(A,B);
	
	return squares;
end function;


// transform quadric equation to normal form
// -----------------------------------------
// input : a homogeneous ternary polynomial 'f' of degree 2 over the field
//         'Q(t)' defining an absolutely irreducible conic
// output: a matrix 'T', an element 'c', and a diagonal matrix 'D' with
//         squarefree Hessian determinant s.t. 'T^t * M * T = c*D' where 'M'
//         is the matrix representation of 'f' (obtained by
//         'SymmetricBilinearForm(f)')
// (see article Lemma 1, a good weight vector is found by 'InitialWeights(M)')
function SimpleDiagonal(f)
	P := Parent(f); QtF := BaseRing(P);
	M := SymmetricBilinearForm(f);
	assert(not Determinant(M) eq 0);
	
	// diagonalize conic
	h, T := DiagonalForm(f); T := Transpose(T);
	
	// pullout content from equation
	lcd := 1; for cf in Coefficients(h) do
		lcd := Lcm(Denominator(cf), lcd);
	end for; h := lcd*h;
	pp := 0; for cf in Coefficients(h) do
		pp := Gcd(Numerator(cf), pp);
	end for; h := (1/pp)*h;
	cf := lcd/pp;
	
	// get rid of square factors
	d := [MonomialCoefficient(h, P.i^2) : i in [1..3]];
	N := MatrixAlgebra(QtF, 3) ! 1;
	for i in [1..3] do
		// remove squares from d[i]
		repeat
			sqrs := QtF ! GetSquares(Numerator(d[i]));	
			d[i] := d[i]/sqrs^2;
			N := N*DiagonalMatrix([(j eq i) select sqrs^(-1) else 1
			                       : j in [1..3]]);
		until sqrs eq 1;
	end for;
	for ij in [[1,2], [1,3], [2,3]] do
		i := ij[1]; j := ij[2];
		// remove gcd from d[i] and d[j]
		repeat
			g := QtF ! Gcd(Numerator(d[i]),Numerator(d[j]));
			d := [k in ij select d[k]/g else d[k]*g : k in [1..3]];
			N := N*DiagonalMatrix([k in ij select g^(-1) else 1
			                       : k in [1..3]]);
			cf := cf*g;
		until g eq 1;
	end for;
	
	// final equation
	return T*N, 1/cf, DiagonalMatrix(QtF,d);
end function;


// produce quadratic equation from bilinear form
// ---------------------------------------------
// input : an 'r x r'-matrix 'M' and a polynomial ring 'P' of rank 'r'
// output: the quadratic form given by '(P.1,...,P.r)*M*(P.1,...,P.r)^t'
function Equation(M, P)
	r := Rank(P);
	v := RMatrixSpace(P,1,r) ! [P.i : i in [1..r]];
	N := RMatrixSpace(P,r,r) ! M;
	return (v*N*Transpose(v))[1,1];
end function;


// divide all entries of a matrix exactly
// --------------------------------------
// input : an '3 x 3'-matrix 'M' and an element 'f' that divides all entries
// output: the matrix 'M/f'
function DivideMatrix(M, f)
	R := Parent(f);
	return Matrix(R,[[ExactQuotient(M[i,j],f): j in [1..3]]: i in [1..3]]);
end function;


// split quadratic form with zero Hessian
// --------------------------------------
// input : a homogeneous ternary polynomial 'f' with zero Hessian determinant
//         of degree 2 defining an absolutely irreducible conic
// output: a linear factor of 'f' defined over the ground field
//         (or over a suitable quadratic extension if 'AllowExtensions=true')
function LinearFactorZeroHessian(f :
     AllowExtensions := false, ExtName := "alpha", ExtCount := 0)
	P<x,y,z> := Parent(f); Q := BaseRing(P);
	M := SymmetricBilinearForm(f);
	V := RMatrixSpace(Q,1,3); A := Parent(M);
	assert(Determinant(M) eq 0);
	
	// diagonalize f
	g, T := DiagonalForm(f); T := Transpose(T);
	M := Transpose(T)*M*T;
	
	// move zeros to last coordinates
	if M[1,1] eq 0 then
		SwapColumns(~M, 1, 3);
		T := T*Matrix(Q,[[0,0,1],[0,1,0],[1,0,0]]);
	end if;
	if M[1,1] eq 0 then
		SwapColumns(~M, 1, 2);
		T := T*Matrix(Q,[[0,1,0],[1,0,0],[0,0,1]]);
	end if;
	if M[2,2] eq 0 then
		SwapColumns(~M, 2, 3);
		T := T*Matrix(Q,[[1,0,0],[0,0,1],[0,1,0]]);		
	end if;
	
	// factor diagonal form
	if M[2,2] eq 0 then
		// Case 1: a x^2
		F := Q; VF := V; AF := A; PF := P;
		L := Transpose(VF ! [F | 1,0,0]);
	else
		// Case 2: a x^2 + b y^2
		sqr, root := IsSquare(-M[2,2]/M[1,1]);
		if sqr then
			F := Q; VF := V; AF := A; PF := P;
			L := Transpose(VF ! [F | 1, root, 0]);
		else
			if AllowExtensions then
				roots, ExtCount := AllRoots(R.1^2+M[2,2]/M[1,1]
				    : ExtName := ExtName, ExtCount := ExtCount)
				    where R is PolynomialRing(Q);
				alpha := roots[1][1]; F := Parent(alpha);
				VF := RMatrixSpace(F,1,3);
				AF := ChangeRing(A,F);
				PF := ChangeRing(P,F);
				L := Transpose(VF ! [F | 1, alpha, 0]);
			else
				F := Q; VF := V; AF := A; PF := P;
				L := Transpose(VF ! [F | 0, 0, 0]);
			end if;
		end if;
	end if;
	
	// translate back to a linear form for the original matrix
	L := Transpose((AF ! Transpose(T^(-1)))*L)[1];
	for i:=1 to 3 do
		if not(L[i] eq 0) then L := 1/L[i]*L; break; end if;
	end for;
	return L, ExtCount;
end function;


// divide all entries of a matrix exactly
// --------------------------------------
// input : an '3 x 3'-matrix 'M' and an element 'f' that divides all entries
// output: the matrix 'M/f'
function DivideMatrix(M, f)
	R := Parent(f);
	return Matrix(R,[[ExactQuotient(M[i,j],f): j in [1..3]]: i in [1..3]]);
end function;


// remove removable factors of the Hessian determinant
// ---------------------------------------------------
// input : a matrix 'M' over 'Q(t)'
// output: a matrix 'T', an element 'c' and a matrix 'N' s.t. ??????????
//         'T^t * M * T = c * N' and as many as possible of the factors of
//         the Hessian of 'M' are removed in 'N'
// (see article Theorem 4)
forward RemoveRemovablesRec;
function RemoveRemovables(M
    : AllowExtensions := false, ExtName := "alpha", ExtCount := 0)
	// compute factorization of determinant of Hessian
	facts := [tup[1] : tup in Factorization(Determinant(M))];
	
	// call recursive procedure
	return RemoveRemovablesRec(M, facts :
	    AllowExtensions := AllowExtensions, ExtName := ExtName,
	    ExtCount := ExtCount);
end function;
function RemoveRemovablesRec(M, facts
    : AllowExtensions := false, ExtName := "alpha", ExtCount := 0)
	vprintf Classify: "'RemoveRemovablesRec' with factors: %o\n", facts;
	A := Parent(M); Qt<t> := BaseRing(A); Q := BaseRing(Qt);
	S := PolynomialRing(Qt,3);
	
	// termination condition: No more factors to treat!
	if #facts eq 0 then
		return A ! 1, Qt ! 1, M, ExtCount;
	end if;
	
	// test one irreducible factor for removability
	fact := facts[1]; facts := Remove(facts, 1);
	F<alpha> :=
	    NumberField(fact : Check := false, DoLinearExtension := true);
	T := ChangeRing(S, F);
	AssignNames(~F, [ExtName*"_"*IntegerToString(ExtCount)]);
	ExtCount := ExtCount + 1;
	StoT := hom<S -> T | hom<Qt->T| T ! alpha>, T.1, T.2, T.3>;
	
	vprintf Classify: "Finding linear factorization over %o.\n", F;
	// try to factor and if possible do a transformation
	g := StoT(Equation(M, S));
	if not AllowExtensions then
		lin := LinearFactorZeroHessian(g);
	else
		lin, ExtCount := LinearFactorZeroHessian(g :
		    AllowExtensions := true, ExtName := ExtName,
		    ExtCount := ExtCount);
		
		// do a basechange with new field
		Q := BaseRing(lin); Qt<t> := ChangeRing(Qt, Q);
		A := ChangeRing(A, Qt); S := ChangeRing(S, Qt);
		facts := [Qt ! elt : elt in facts];
		facts := [ExactQuotient(fact, t - (Q ! alpha))] cat facts;
		fact := t - (Q ! alpha);
		
		// refactor
		vprintf Classify: "Refactoring.\n";
		newfacts := [];
		for elt in facts do
			newfacts := newfacts cat
			    [tup[1] : tup in Factorization(Qt ! elt)];
		end for;
		facts := newfacts;
	end if;
	vprintf Classify: "Constructing transformation.\n";
	if not (lin eq 0) then
		// case: Factor removable!
		// find coefficients
		E := [Qt ! Eltseq(cf, Q) : cf in Eltseq(lin)];
		
		// set up transformation matrix
		if E[1] eq 1 then
			N := Matrix([[  fact, -E[2], -E[3]],
			             [     0,     1,     0],
			             [     0,     0,     1]]);
		else if E[2] eq 1 then
			N := Matrix([[     1,     0,     0],
			             [ -E[1],  fact, -E[3]],
			             [     0,     0,     1]]);
		else
			N := Matrix([[     1,     0,     0],
			             [     0,     1,     0],
			             [ -E[1], -E[2],  fact]]);
		end if;	end if;
		
		// change representation
		K := DivideMatrix(Transpose(N)*(A ! M)*N, fact);
	else
		// case: Factor not removable!
		N := A ! 1; fact := Qt ! 1; K := M;
	end if;
	
	// go into recursion
	No, rem, Ko, ExtCount := RemoveRemovablesRec(K, facts :
	     AllowExtensions := AllowExtensions, ExtName := ExtName,
	     ExtCount := ExtCount);
	return N*No, fact*rem, Ko, ExtCount;
end function;


// find point on quadric surface in first chart
// --------------------------------------------
// input : a homog. polynomial 'p' over 'Q' defining a quadric hypersurface
// output: 'true' and a rational point on the surface (in its first chart
//         with affine coordinates) if existent, otherwise 'false'
//         (if 'AllowExtensions := true' then a quadratic extension is
//         introduced in the case that no rational point exists)
PointOnQuadricHypersurface1Chart := function(p
    : AllowExtensions := false, ExtName := "alpha", ExtCount := 0)

	P := Parent(p); Q := BaseRing(P); r := Rank(P);
	Qt := PolynomialRing(Q); t := Qt.1;
        V1 := RSpace(Q, r); V2 := RSpace(Qt, r);
	
	// find any point on the quadric
	haspt, vec := PointOnQuadric(p);
	if not haspt then
		if AllowExtensions then
			// find any point on f
			rvec := V2 ! ([0 : i in [1..r-1]] cat [1]);
			while true do
				svec := V2!([Random(1):i in [1..r-1]] cat [0]);
				// parametrized line with 'svec' at infinity
				evl := Eltseq(rvec + t*svec);
				s := hom<P -> Qt | evl>(p);
				if Degree(s) eq 2 then break; end if;
			end while;
			rts, ExtCount := AllRoots(s :
			    ExtName := ExtName, ExtCount := ExtCount);
			rt := rts[1][1]; F := Parent(rt);
//			F := NumberField(s);
//			AssignNames(~F,
//			    [ExtName*"_"*IntegerToString(ExtCount)]);
//			rt := F.1;
			ExtCount := ExtCount + 1;
			return true,
			    [hom<Qt -> F | rt>(evl[i]) : i in [1..#evl-1]],
			    ExtCount;
		else
			return false, _, ExtCount;
		end if;
	end if;
	vec := V1 ! vec;
	
	// maybe transform solution to first chart
	if vec[r] eq 0 then
		svec := V2 ! vec;
		while true do;
			rvec := V2 ! ([Random(1) : i in [1..r-1]] cat [1]);
			// parametrized line with 'svec' at infinity
			s := hom<P -> Qt | Eltseq(t*svec + rvec)>(p);
			
			// is 'rvec' itself on quadric?
			if Evaluate(p, Eltseq(rvec)) eq 0 then
				vec := V1 ! rvec; break;
			end if;
			
			// no double point at infinity?
			if Degree(s) eq 1 then
				lambda := -Coefficient(s,0)/Coefficient(s,1);
				vec := V1 ! (lambda*svec + rvec); break;
			end if;
		end while;
	end if;
	
	// return a point in affine coordinates
	return true, [Q | vec[i]/vec[r] : i in [1..r-1]], ExtCount;
end function;


// compute the leaders of a matrix
// -------------------------------
// input : a '3 x 3'-matrix 'M' over 'Q[t]' and a weight vector 'w'
// output: the column index of the leader of each row
// (the definition of a 'leader' is given before algorithm 'ReduceColumns'
// in the article)
function Leaders(M, w)
	MyDeg := func<p | (p eq 0) select -Infinity() else Degree(p)>;
	leaders := [];
	for i := 1 to 3 do
		max := MyDeg(M[1,i])-w[1]; ind := 1;
		for j := 2 to 3 do
			tst := MyDeg(M[j,i])-w[j];
			if (max lt tst) then
				max := tst; ind := j;
			end if;
		end for;
		Append(~leaders, ind);
	end for;
	
	return leaders;
end function;


// reduction of transformations
// ----------------------------
// input : a '3 x 3'-matrix 'M' over 'Q[t]' and a weight vector 'w'
// output: a new matrix 'N' and a new weight vector 'u' s.t. 'M' and 'N'
//         differ only by an invertible matrix over 'Q[t]' and s.t. the
//         degree defect of 'N' w.r.t. 'w' and 'u' is zero
// (compare algorithm 'ReduceColumns' in the article)
function ReduceColumns(M, w)
	Qt<t> := BaseRing(M); N := M;
	
	// interreduce columns
	repeat
		change := false;
		
		// determine leaders
		leaders := Leaders(N, w);
		
		// find a reducible pair
		for ip in [[1,2],[1,3],[2,3]] do
			if leaders[ip[1]] eq leaders[ip[2]] then
				i := leaders[ip[1]]; j := ip[1]; k := ip[2];
				change := true; break;
			end if;
		end for;
		
		// do reduction
		if change then
			// maybe exchange column indices
			if Degree(N[i,j]) lt Degree(N[i,k]) then
				aux := j; j := k; k := aux;
			end if;
			c := ExactQuotient(LeadingTerm(N[i,j]),
			                   LeadingTerm(N[i,k]));
			AddColumn(~N,-c,k,j);
		end if;
	until not change;
	
	// find new weight vector
	leaders := Leaders(N, w);
	u := [w[leaders[j]]-Degree(N[leaders[j],j]) : j in [1..3]];
	m := 1 - Min([u[1], u[2], u[3]]);
	u := [c + m : c in u];
	
	return N, u;
end function;


// normalize surface given as conic curve over Q(t)
// ------------------------------------------------
// input : a homogeneous polynomial 'f' in 'Q(t)[x,y,z]' which defines
//         rationally a surface (in variables e.g. 'x/z', 'y/z' and 't')
//         by giving a conic curve over 'Q(t)'
// output: a matrix 'T', an element 'c' in 'Q(t)', a matrix 'N', and a
//         weight vector 'u' s.t. 'T^t * M * T = c * N' (if
//         'M = SymmetricBilinearForm(f)') and 'N' is of "minimal degree"
//         as shown by the weight vector 'u' (if 'AllowExtensions = true' then
//         algebraic extensions are introduced while removing factors from
//         the Hessian determinant)
// (see algorithm 'DegreeMinimize' and Theorem 5 in the article,
//  before also "minimal degree" is explained!)
function NormalizeSurfaceConic(f
    : AllowExtensions := false, ExtName := "alpha", ExtCount := 0)
	PF := Parent(f); QtF := BaseRing(PF); Q := BaseRing(QtF);
	
	// diagonalize conic
	T, cf, M := SimpleDiagonal(f);
	A := Parent(M);
	
	// find initial weight vector
	w := InitialWeights(M);
	
	// remove removable factors from Hessian
	Qt := PolynomialRing(Q); A2 := MatrixAlgebra(Qt, 3);
	T2, cf2, M2, ExtCount := RemoveRemovables(A2 ! M
	    : AllowExtensions := AllowExtensions, ExtName := ExtName,
	      ExtCount := ExtCount);
	
	// Align transformation
	T3, u := ReduceColumns(T2,w); cf3 := cf2;
	M3 := DivideMatrix(Transpose(T3)*(A2 ! M)*T3, cf3);
	
	// Return nice representation
	Ft := BaseRing(M3); F := BaseRing(Ft); FtF := FunctionField(F);
	A3 := MatrixAlgebra(FtF, 3);
	return (A3 ! T)*(A3 ! T3), (FtF ! cf)*(FtF ! cf3), M3, u, ExtCount;
end function;


// combine two step parametrization
// --------------------------------
// input : a matrix 'T' which describes a first transformation, a sequence
//         '[X,Y,Z]' and a homomorphism 'phi' that parametrize the result
//         (in the sense of 'ParametrizeSurfaceConic' below)
// output: a new tuple '[Xn,Yn,Zn]' that together with 'phi' parametrizes
//         the initial surface (in the sense of 'ParametrizeSurfaceConic')
CombPara := function(T, X, Y, Z, phi)
	Quv := Codomain(phi);
	A := Parent(Matrix(T));	A2 := MatrixAlgebra(Quv, 3);
	v := hom<A -> A2 | phi>(T) * Matrix(Quv, [[X],[Y],[Z]]);
	return [v[1, 1], v[2, 1], v[3, 1]];
end function;


// parametrize a surface of "minimal degree"
// -----------------------------------------
// input : a homogeneous polynomial 'f' in 'Q(t)[x, y, z]' which defines
//         rationally a surface (in variables e.g. 'x/z', 'y/z' and 't')
//         by giving a conic curve over 'Q(t)'
// output: 'true', a sequence '[X, Y, Z]' in 'F^3' and a homomorphism
//         'psi: Q(t) -> F' where 'F' is a function field in two variables
//         inducing an isomorphism 'FF(Q(t)[x, y, z]/f) -> F' of
//         fields of fractions if such exists, otherwise 'false'
// (the algorithm is scattered in section 3 of the paper)
function ParametrizeSurfaceConic(f
    : AllowExtensions := false, ExtName := "alpha", ExtCount := 0)
	P := Parent(f); QtF<t> := BaseRing(P); Q := BaseField(QtF);
	
	// normalize conic and compute the index
	T, fact, M, w, ExtCount := NormalizeSurfaceConic(f
	    : AllowExtensions := AllowExtensions, ExtName := ExtName,
	      ExtCount := ExtCount);
	A := Parent(M); QNt := BaseRing(A); QN := BaseRing(QNt);
	QNtF := FunctionField(QN); QNuv<u,v> := FunctionField(QN,2);
	index := 3*MatrixDegree(M,w) - 2*(&+w);
	
	// zero on the diagonal (see section 3.1)
	if M[1,1]*M[2,2]*M[3,3] eq 0 then
		N := M;
		
		// maybe swap coordinates
		k := 1;
		if M[2,2] eq 0 then
			k := 2;
			SwapColumns(~N,1,2); SwapRows(~N,1,2);
		else if M[3,3] eq 0 then
			k := 3;
			SwapColumns(~N,1,3); SwapRows(~N,1,3);
		end if; end if;
		
		// now we have: N[1,1] eq 0
		phi := hom<QtF->QNuv | u>; phiN := hom<QNtF->QNuv | u>;
		X := -(phiN(N[2,2]) + phiN(N[3,3])*v^2 + 2*phiN(N[2,3])*v)/
		      (2*phiN(N[1,2])+2*phiN(N[1,3])*v);
		Y := 1;	Z := v;
		
		// swap coordinates back
		case k:
			when 1:
			return true, CombPara(T, X, Y, Z, phiN), phi, ExtCount;
			when 2:
			return true, CombPara(T, Y, X, Z, phiN), phi, ExtCount;
			when 3:
			return true, CombPara(T, Z, Y, X, phiN), phi, ExtCount;
		end case;
	end if;
	
	// index 0 (see section 3.2)
	if index eq 0 then
		// coefficients of defining equation are in Q,
		// so we parametrize a curve over Q
		A2 := MatrixAlgebra(QN,3); P2 := PolynomialRing(QN,3);
		M0 := hom<A -> A2 | hom<QNt -> QN| 0>>(M);
		Q0 := Equation(M0,P2);
		C := Conic(ProjectiveSpace(P2),Q0);
		
		if AllowExtensions then
			// choose a point
			haspt, pt, ExtCount := PointOnQuadricHypersurface1Chart
			    (Q0 : AllowExtensions := true, ExtName := ExtName,
			    ExtCount := ExtCount);
			QNN := Universe(pt);
			QNNuv<u,v> := FunctionField(QNN,2);
			
			// parametrize by stereographic projection
			P3 := PolynomialRing(QNNuv); r := P3.1;
			R := -Coefficient(lc,1)/Coefficient(lc,2)
		  	 where lc is Evaluate(Q0,[r+pt[1],v*r+pt[2],1]);
			para := [R+pt[1],v*R+pt[2],1];
			
			// use 'u' as 't'-coordinate to get parametrization
			phi := hom<QtF->QNNuv | u>;
			phiN := hom<QNtF->QNNuv | u>;
		else
			// parametrizable only if rational point exists
			haspt, pt := HasRationalPoint(C);
			if not haspt then
				return false, _, _, ExtCount;
			end if;
			para :=	DefiningEquations(Parametrization(C,pt));
			para := [Evaluate(g, [1,v]) : g in para];
			
			// use 'u' as 't'-coordinate to get parametrization
			phi := hom<QtF->QNuv | u>;
			phiN := hom<QNtF->QNuv | u>;
		end if;
		X := para[1]; Y := para[2]; Z := para[3];
		return true, CombPara(T, X, Y, Z, phiN), phi, ExtCount;
	end if;
	
	// index 1 (impossible, see section 3.3)
	if index eq 1 then
		return false, _, _, ExtCount;
	end if;
	
	// index 2 (see section 3.4)
	if index eq 2 then
		N := M;
		// maybe swap coordinates
		k := 1;
		if w[2] eq 1 then
			k := 2;
			SwapColumns(~N,1,2); SwapRows(~N,1,2);
		else if w[3] eq 1 then
			k := 3;
			SwapColumns(~N,1,3); SwapRows(~N,1,3);
		end if; end if;
		
		// produce quadric nonsingular surface
		P2<x,y,z> := PolynomialRing(QN,3);
		g := hom<P -> P2 | hom<QNtF -> P2 | x>, 1,y,z>(Equation(N,P));
		
		// find a point on surface
		P3 := PolynomialRing(QN,4);
		h := Homogenization(hom<P2 -> P3 | P3.1, P3.2, P3.3>(g), P3.4);
		haspt, pt := PointOnQuadricHypersurface1Chart(h);
		if not haspt then
			return false, _, _, ExtCount;
		end if;
		
		// parametrize by stereographic projection
		h := Evaluate(g,[x+pt[1],y+pt[2],z+pt[3]]);
		P4 := PolynomialRing(QNuv); r := P4.1;
		R := -Coefficient(lc,1)/Coefficient(lc,2)
		  where lc is Evaluate(h,[r,u*r,v*r]);
		
		// backtranslate parametrization
		phi := hom<QtF -> QNuv | R+pt[1]>;
		phiN := hom<QNtF -> QNuv | R+pt[1]>;
		X := QNuv ! 1; Y := u*R+pt[2]; Z := v*R+pt[3];
		
		// swap coordinates back
		if k eq 1 then
			return true, CombPara(T, X, Y, Z, phiN), phi, ExtCount;
		else if k eq 2 then
			return true, CombPara(T, Y, X, Z, phiN), phi, ExtCount;
		else
			return true, CombPara(T, Z, Y, X, phiN), phi, ExtCount;
		end if; end if;
	end if;
	
	// index 3 (see section 3.5)
	if index eq 3 then
		// equation is linear in t
		A2 := MatrixAlgebra(QN,3); P2 := PolynomialRing(QN,3);
		M0 := hom<A -> A2 | hom<QNt -> QN| 0>>(M);
		M1 := hom<A -> A2 | hom<QNt -> QN| 1>>(M-(A ! M0));
		Q0 := Equation(M0,P2); Q1 := Equation(M1,P2);
		q0 := Evaluate(Q0,[1,u,v]); q1 := Evaluate(Q1,[1,u,v]);
		phi := hom<QtF->QNuv | -q0/q1>;
		phiN := hom<QNtF->QNuv | -q0/q1>;
		return true, CombPara(T, 1, u, v, phiN), phi, ExtCount;
	end if;
	
	// no parametrization since index > 3  (see section 3.6)
	return false, _, _, ExtCount;
end function;


// produce a conic over 'Q(t)' from an abstract pencil
// ---------------------------------------------------
// input : a pencil 'pencil: S -> P^n', i.e. a map from a surface into some
//         projective space with image a rational normal curve, s.t. the
//         generic fibre is also a rational curve
// output: 'true', curves 'C' and 'D', over 'Q(t)', a morphism 'rho: C -> S'
//         and a morphism 'phi: C -> D' s.t. 'phi' is birational and 'rho'
//         can be interpreted as birational (it is the generic fibre) if
//         exists, otherwise return 'false'
function PencilToConic(pencil)
	// get surface in domain
	S := Domain(pencil); I := DefiningPolynomials(S);
	P := Universe(I); Q := BaseRing(P);
	
	// parametrize the rational normal curve in the codomain of the pencil
	NC := Curve(Image(pencil)); NC2, NCtoNC2 := Conic(NC);
	L<u,v> := ProjectiveSpace(Q, 1);
	haspt, pt := HasRationalPoint(NC2);
	if not haspt then return false, _, _, _, _; end if;
	LtoNC2 := Parametrization(NC2,pt,Curve(L));
        pencil_aug := Expand(pencil * NCtoNC2 * Inverse(LtoNC2));
	
	// produce projective space curve over 'Q(t)'
	QtF := FunctionField(Q); t := QtF.1; Pt := ChangeRing(P, QtF);
	eqn := DefiningEquations(pencil_aug);
	f1 := Pt ! eqn[1]; f2 := Pt ! eqn[2];
	
	// write 'S' as a curve 'C' over 'Q(t)'
	J := [Pt | Pt ! g : g in I]; Append(~J, f1 - t*f2);
	K := Saturation(ideal<Pt | J>, ideal<Pt | f1,f2>);
	C := Curve(Scheme(ProjectiveSpace(Pt), K));
	rho := map<C -> S | /*[Pt.1,Pt.2,Pt.3,Pt.4]*/[Pt.i : i in [1..Length(S)]]>;
	
	// bugfix: birational map to conic D
	// =================================
	// compute basis of anticanonical divisor
	basis := Basis(-CanonicalDivisor(C));
	R := Parent(Numerator(ProjectiveFunction(basis[1])));
	d1 := Denominator(ProjectiveFunction(basis[1]));
	d2 := Denominator(ProjectiveFunction(basis[2]));
	d3 := Denominator(ProjectiveFunction(basis[3]));
	basis := [Numerator(ProjectiveFunction(basis[1]))*d2*d3,
	          Numerator(ProjectiveFunction(basis[2]))*d1*d3,
	          Numerator(ProjectiveFunction(basis[3]))*d1*d2];
	// compute a birational map to a conic
	P2<x,y,z> := ProjectivePlane(QtF);
	phi := map<C -> P2 | basis>;
	D := Conic(Image(phi)); phi := map<C -> D | basis>;
	
	return true, C, D, rho, phi;
end function;




// ======================
// = Exported functions =
// ======================

// parametrize surface over Q given as rational pencil
intrinsic ParametrizePencil(pencil::MapSch, P2::Prj)
-> BoolElt, MapSch
{
Given an ordinary projective ruled surface as the domain X of a rational pencil 'pencil'
and ordinary projective plane P2 both defined over Q. Return 'false' if X is not
parametrizable over the rationals, otherwise return 'true' and a
parametrization.
}
	// transform pencil to conic equation
	isrewritable, C, D, rho, phi := PencilToConic(pencil);
	if not isrewritable then return false, _; end if;
	surface := Codomain(rho);
	
	// parametrize conic (if possible)
	f := DefiningEquation(D);
	ispara, xyz, psi := ParametrizeSurfaceConic(f);
	if not ispara then return false, _; end if;
	
	// compute parametrizing map from given plane
	_, phi_inv := IsInvertible(phi);
	para := [hom<Parent(f) -> Codomain(psi) |psi, xyz>(g)
                 : g in DefiningEquations(Expand(phi_inv*rho))];
	FF := FunctionField(P2);
	para := [FF | hom<Universe(para) -> FF | FF.1, FF.2>(g) : g in para];
	
	// store inverse
	m := map<P2 -> surface | para>; //_, mi := IsInvertible(m); m := mi^(-1);
//printf "m: %o\n",m;
	return true, m;
end intrinsic;






















// CASE: Index=2 and singular => Shouldn't exist!
// **********************************************
//		// Distinguish cases
//		sing := Variety(JacobianIdeal(g) + ideal< P2 | g>);
//		if #sing eq 1 then
//			// Surface is singular
//			// Move singularity to origin and produce cone
//			pt := sing[1];
//			psi := hom<P2 -> P2| x+pt[1], y+pt[2], z+pt[3]>;
//			h := psi(g);
//			
//			// Parametrize base
//			C := Conic(ProjectiveSpace(P2),h);
//			haspt, pt := HasRationalPoint(C);
//			if not haspt then
//			error("No parametrization: Index 2, no point over Q!");
//			end if;
//			para :=	DefiningEquations(Parametrization(C,pt));
//			
//			// Interpret as surface parametrization
//			para := [Quv ! g : g in para];
//			phi := hom<QtF -> Quv | Quv ! para[1]>;
//			X := Quv ! 1; Y := Quv ! para[2]; Z := Quv ! para[3];
//		else
//			// Surface is nonsingular
//                      ............
//		end if;
