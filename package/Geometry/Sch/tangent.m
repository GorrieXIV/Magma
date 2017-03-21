freeze;

///////////////////////////////////////////////////////////////////////
// tangent.m
//	Tangent cones and tangent spaces
///////////////////////////////////////////////////////////////////////
 
 
intrinsic TangentSpace(S::Sch,p::Pt) -> Sch
{The tangent space to S at p embedded as a scheme in the ambient space of S}
    require p in S:
	"The point does not lie on the scheme";
    /* mch 09/10 - remove unnecessary non-singularity condition */
    //require IsNonsingular(S,p):
        //"The point is a singular point of the scheme";
    A := Ambient(S);
    if S eq A then
	// Deem the whole space to be its own tangent space: a bit
	// odd in some cases perhaps, but still.
	return A;
    end if;
    if IsAffine(A) then
	p := Eltseq(p);
	/* added mch 11/08 - base change A if p is over an extension field */
	if not(Universe(p) cmpeq BaseRing(A)) then
	    A := BaseChange(A,Universe(p));
	end if;
	V := VectorSpace(Universe(p),Length(A));
	TV := sub<V|[V![Evaluate(Derivative(f,i),p) : i in [1..Length(A)]] :
		f in DefiningPolynomials(S) ] >;
	TB := Basis(TV); // do this to get a minimal set of linear equations	
	ts := Scheme(A,TF)
		where TF is [ &+[ CoordinateRing(A) |
		b[i]*(A.i-p[i]) : i in [1..Length(A)] ] : b in TB];
	if Dimension(ts) eq 1 then ts := Curve(ts); end if;
	return ts;
    else
	return ProjectiveClosure(TangentSpace(S@@phi,p))
	    where phi is ProjectiveClosureMap(A)
	    where A,p is AffinePatch(A,p);
    end if;
end intrinsic;

intrinsic TangentSpace(p::Pt) -> Sch
{The tangent space to S at p embedded as a scheme in the ambient space of S
 where S is the parent scheme of p}
    return TangentSpace(Scheme(p),p);
end intrinsic;

intrinsic TangentCone(S::Sch,p::Pt) -> Sch
{The tangent cone at the rational point p to scheme S on which it lies}
    require p in S:
	"The point does not lie on the scheme";
    A := Ambient(S);
    if Type(A) eq Aff then
	/* added mch 11/08 - base change A if p is over an extension field */
	if not(Ring(Parent(p)) cmpeq BaseRing(A)) then
	    A := BaseChange(A,Ring(Parent(p)));
	    p := A!Eltseq(p);
	end if;
	case IsPlaneCurve(S):
	    when true: return Curve(A,f_min)@@phi
		where f_min is &+[ m : m in terms | TotalDegree(m) eq min_deg]
		where min_deg is Minimum([ TotalDegree(m) : m in terms ])
		    where terms := Terms(Evaluate(Polynomial(S),
			InverseDefiningPolynomials(phi)))
		    where phi is Translation(A,p);
	    else
		R := CoordinateRing(A);
		B := [b : b in DefiningPolynomials(S)/*Basis(Ideal(S))*/ | b ne 0];
		if #B eq 0 then return A; end if;
		// mch - 06/10 - should use a LOCAL Groebner basis to guarantee
		//  getting a basis for the initial ideal that generates the
		//  ideal of the tangent cone. Also, mdegs should be the
                //  minimal degree for each basis element, not the global minimal
		//  degree [by defn, TanCone at 0 defined by [init(f) : f in I(S)\0]]
                //  eg, for S: xy+y^3=x^2=0 in Aff(Q,2) at 0, tan cone generated
		//   by [x^2,xy,y^5] - old version missed y^5 because of mdeg prob.
                //  for S: xy+x^3=y^2=0, tan cone gen by [y^2,xy,x^5] - with lex
		//  ordering in CoordRing(A), old version missed the x^5, even with
		//  mdeg problem fixed.
		R1 := LocalPolynomialRing(BaseRing(A),Length(A),"lgrevlex");
		return Scheme(A,[e : e in E_min | e ne 0])@@phi where E_min is
		[ &+[R| m : m in terms[i]| TotalDegree(m) eq mdegs[i]] :
								i in [1..#terms] ]
		where mdegs is [Minimum([TotalDegree(m):m in t]) : t in terms]
		    where terms is [ Terms(R!f) : f in basis ]
		    where basis is GroebnerBasis(ideal<R1|[R1!Evaluate(b,pols) : b in B]>)
		    where pols is InverseDefiningPolynomials(phi)
		    where phi is Translation(A,p);
	end case;
    else
	return ProjectiveClosure(TangentCone(S@@phi,p))
	    where phi is ProjectiveClosureMap(A)
	    where A,p := AffinePatch(A,p);
    end if;
end intrinsic;

intrinsic TangentCone(p::Pt) -> Sch
{The tangent cone at the rational point p to the scheme on which it lies}
    X := Scheme(p);
    b,C := IsCurve(X);
    b := b and IsPlaneCurve(C);
    if b then
        return TangentCone(C,p);
    else
        return TangentCone(X,p);
    end if;
end intrinsic;

