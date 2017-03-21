freeze;

///////////////////////////////////////////////////////////////////////
// projection.m
///////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////
//		Affine elimination
///////////////////////////////////////////////////////////////////////

intrinsic Elimination(X::Sch,V::[RngIntElt]) -> Sch
{The affine scheme obtained by eliminating the ambient variables
whose indices appear in V from the equations of the affine scheme X}
    nv := #V;
    A := Ambient(X);
    na := Dimension(A);
    // error checks
    valid := [1..na];
    for v in V do
	require v in valid:
	    "V must only contain integers that occur as indices of the " *
				"ambient coordinates of X";
    end for;
    // dumb case
    if nv eq 0 then
	return X;
    end if;
    // make the matrix that permutes the entries of V with the first variables
    notV := [ Integers() | ];
    for i in [1..na] do
	if not i in V then
	    Append(~notV,i);
	end if;
    end for;
    trentries := [ Integers() | ];
    zerocol := [ 0 : i in [1..na] ];
    for v in V do
	newcol := zerocol;
	newcol[v] := 1;
	trentries := trentries cat newcol;
    end for;
    for v in notV do
	newcol := zerocol;
	newcol[v] := 1;
	trentries := trentries cat newcol;
    end for;
    M := Matrix(na,trentries);
    // make the linear automorphism to permute the elim coords to the first ones
    aut := Automorphism(A,M);
    // eliminate
    X1 := X @@ aut;
    IX1 := DefiningIdeal(X1);
    eqns := Basis(EliminationIdeal(IX1,nv));
    extras := [ A.i : i in [1..nv] ];
    IX2 := ideal< CoordinateRing(A) | eqns cat extras >;
    X2 := Scheme(A,IX2);
    // return coords to starting point
    invaut := Automorphism(A,M^(-1));
    return X2 @@ invaut;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Projective stuff
///////////////////////////////////////////////////////////////////////

intrinsic Projection(P::Prj,Q::Prj) -> MapSch
{The linear projection P - -> Q which forgets the first dim(P) - dim(Q)
coordinates of P}
    require Dimension(P) gt Dimension(Q):
	"The dimension of the first argument must be greater than the dimension of the second";
    require IsOrdinaryProjective(P) and IsOrdinaryProjective(Q):
	"The arguments must be ordinary projective spaces";
    return map<P->Q|[ P.i : i in [d-Dimension(Q)+1..d+1] ]>
		where d := Dimension(P);
end intrinsic;

intrinsic Projection(X::Sch,Q::Prj) -> Sch,MapSch
{The image of the projection of X away from (1:0:...:0);
the ambient projection map is also returned}
    P := Ambient(X);
    d := Dimension(P);
    require IsOrdinaryProjective(Q) and Dimension(Q) eq d - 1:
	"Second argument must be an ordinary projective space of dimension one less that that of the ambient of the scheme";
    require IsOrdinaryProjective(P):
	"Argument must be embedded in an ordinary projective space";
    pr := Projection(P,Q);
    // calculate the projection using an elimination ideal and
    // push the elimination ideal downstairs using the restriction map
    rest := hom< CoordinateRing(P) -> R | Rest >
        where Rest is [ R | 0 : i in [e+2..d+1] ] cat [ R | R.i : i in [1..e+1]]
	    where R := CoordinateRing(Q)
	    where e := Dimension(Q);
    T := Scheme(Q,[ rest(f) : f in Basis(J) ])
		where J is EliminationIdeal(DefiningIdeal(X),1);
    return T,pr;
end intrinsic;

intrinsic Projection(X::Sch) -> Sch,MapSch
{The image of the projection of X away from (1:0:...:0);
the ambient projection map is also returned}
    P := Ambient(X);
    require IsOrdinaryProjective(P):
	"Argument must be embedded in an ordinary projective space";
    // make the projection map, as well as a restriction map on coord rings
    Q := ProjectiveSpace(BaseRing(P),Dimension(P) - 1);
    return Projection(X,Q);
end intrinsic;

intrinsic Projection(X::Sch,p::Pt) -> Sch,MapSch
{The image of the projection of X away from p;
the ambient projection map is also returned}
    P := Ambient(X);
    require Ambient(Scheme(p)) eq P:
	"The arguments lie in different ambient spaces";
    t := Translation(P,p,q) where q is Simplex(P)[1];
    if ISA(Type(X),Prj) then
      pr:=Projection(t(X));
      T:=Codomain(pr);
    else
      T,pr := Projection(t(X));
    end if;
    return T,Expand(t * pr);
end intrinsic;

intrinsic ProjectionFromNonsingularPoint(X::Sch,p::Pt) -> Sch,MapSch,Sch
{The image of the projection of X away from the nonsingular point p of X
together with the locus in the image which is the blowup of p on X (returned
as a point if X is a curve)}
    P := Ambient(X);
    require p in X(BaseRing(X)) and IsNonsingular(X,p):
	"Point must be a nonsingular rational point of the scheme";
    t := Translation(P,p,q) where q is Simplex(P)[1];
    T,pr := Projection(t(X));
    // The image point is just the intersection of the translated tangent
    // line with the plane x_0 = 0 in P --- after all, it's the projection
    // to that plane which is what eliminating the first variable does.
    Tp := TangentSpace(X,p);
    Tnewp := t(Tp);
    if Dimension(X) eq 1 then
	p_im_coords := Coordinates(Representative(RationalPoints(
  	    Intersection(Tnewp,Scheme(P,P.1)))))[2..Length(P)];
	return T,t * pr,T!p_im_coords;
    else
	blowup := Intersection(Tnewp,Scheme(P,P.1));
	compmap := hom< RP -> RQ | [RQ!0] cat [ RQ.i : i in [1..Rank(RQ)] ] >
		where RP is CoordinateRing(P)
		where RQ is CoordinateRing(Ambient(T));
	E := Scheme(Ambient(T),[ compmap(f) : f in DefiningPolynomials(blowup) ]);
	return T,t * pr,E;
    end if;
end intrinsic;

