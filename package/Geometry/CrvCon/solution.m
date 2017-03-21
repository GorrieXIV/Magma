freeze;

// Based on paper 
// "Solving Quadratic Equations using Reduced Unimodular Quadratic Forms"
// by Denis Simon, 2003

intrinsic MinimalModel(C::CrvCon) -> CrvCon, MapSch
{Return a conic with discriminant no larger than that of C
and a map from this conic into C}
    require FieldOfFractions(BaseRing(C)) eq Rationals() : 
      "Base ring of the conic must be the rational field or integers";
    Q,W:=MinimiseConicToMatrix(C); W:=MatrixAlgebra(Rationals(),3)!W;
    M := Conic(Ambient(C),
	  InnerProduct
	       (Vector([C.1, C.2, C.3])*Matrix(CoordinateRing(Ambient(C)), Q),
		Vector([C.1, C.2, C.3])));
    return M,
      map<M -> C | Eltseq(Matrix(CoordinateRing(Ambient(C)),Transpose(W))*
			  Matrix(3, 1, [M.1, M.2, M.3])),
                   Eltseq(Matrix(CoordinateRing(Ambient(C)),Transpose(W)^(-1))*
			  Matrix(3, 1, [M.1, M.2, M.3]))>;
end intrinsic;

function integral_matrix(C)
     Q := SymmetricMatrix(DefiningPolynomial(C));
     if not IsCoercible(MatrixAlgebra(Integers(), Nrows(Q)), Q) then
D := LCM([Denominator(c) : c in Eltseq(Q)]); Q := Matrix(Integers(), D*Q);
     else Q := Matrix(Integers(), Q); end if; return Q; end function;

intrinsic LLLReducedModel(S::Sch) -> Sch, MapSch
{Given a scheme S defined by a single quadric equation over the rationals, 
returns a scheme reduced using indefinite LLL and a map from that scheme to S}
    require IsOrdinaryProjective(S) :
      "Scheme must be in a non weighted projective space";
    require #DefiningPolynomials(S) eq 1 :
      "Scheme must be defined by 1 polynomial";
    require TotalDegree(DefiningPolynomial(S)) eq 2 :
      "Scheme must be defined by a quadratic";
    require FieldOfFractions(BaseRing(S)) cmpeq Rationals() : 
      "Base ring of the scheme must be the rational field or integers";

    QQ,B:=LLLGram(integral_matrix(S) : Isotropic:=true, Delta:=0.999);
 /*This does all the work now*/
    R := Scheme(Ambient(S),
                InnerProduct(Vector([S.i : i in [1 .. Length(S)]])*
			            Matrix(CoordinateRing(Ambient(S)), QQ),
			     Vector([S.i : i in [1 .. Length(S)]])));
    return R, map<R -> S |
     Eltseq(Matrix(CoordinateRing(Ambient(S)),Transpose(B))*
	    Matrix(Length(R), 1, [R.i : i in [1 .. Length(R)]])),
     Eltseq(Matrix(CoordinateRing(Ambient(S)),Transpose(B)^-1)*
	    Matrix(Length(R), 1, [R.i : i in [1 .. Length(R)]]))>;
end intrinsic;

