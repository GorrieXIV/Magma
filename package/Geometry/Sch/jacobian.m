freeze;

///////////////////////////////////////////////////////////////////////
// sch_common.m
// April 2001 GDB
///////////////////////////////////////////////////////////////////////

intrinsic InflectionPoints(C::Crv) -> Sch
{The inflection points of C}
  //X := Scheme(Ambient(C),[Polynomial(C),Determinant(HessianMatrix(C))]);
    X := Scheme(C,[Polynomial(C),Determinant(HessianMatrix(C))]);
    b,Z := IsCluster(X);
    if b then
	return Z;
    else
	return X;
    end if;
end intrinsic;

intrinsic Flexes(C::Crv) -> Sch
{The inflection points of C}
    return InflectionPoints(C);
end intrinsic;

intrinsic JacobianIdeal(X::Sch) -> RngMPol
{The jacobian ideal of X}
    require HasGroebnerBasis(X):
	"Groebner basis methods required but unavailable";
    return ideal< CoordinateRing(Ambient(X)) | E,D > where D is
	    &cat[ [ Derivative(f,i) : i in [1..Rank(Universe(E))] ] : f in E ]
	where E is DefiningPolynomials(X);
end intrinsic;

intrinsic JacobianMatrix(X::Sch) -> ModMatRngElt
{The matrix of partial derivatives of the defining polynomials of X}
    return JacobianMatrix(DefiningPolynomials(X));
end intrinsic;
 
intrinsic HessianMatrix(X::Sch) -> Mtrx
{The matrix of second partial derivatives of the polynomial of the
hypersurface X}
    require IsHypersurface(X):
	"The scheme must be a hypersurface";
    return Matrix(n,E) where E is
	[ Derivative(Derivative(Polynomial(X),i),j) : j in [1..n], i in [1..n] ]
	where n is Length(X);
end intrinsic;

