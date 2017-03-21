freeze;

///////////////////////////////////////////////////////////////////////
// translation.m
///////////////////////////////////////////////////////////////////////

// THINK: for the next two functions, would be better if
//      the second arg was a set
//      and scrolls were catered for.

intrinsic TranslationOfSimplex(P::Prj,Q::[Pt]) -> MapSch
    {The translation taking the standard simplex of P to
    the dim(P) + 2 points of Q.}
    n := Dimension(P);
    K := BaseRing(P);
    require IsOrdinaryProjective(P) and IsField(K) :  
	"Argument 1 must be an ordinary projective space defined over a field.";
    require IsComplete(Q) and #Q eq n+2 : 
	"Argument 2 has the wrong length or is incomplete.";
    require Universe(Q) cmpeq P(K) : 
	"Elements of argument lie must be points of argument 1.";
    V := VectorSpace(BaseField(P),n+1);
    M := Matrix(n+1,&cat[ Coordinates(Q[i]) : i in [1..n+1] ]);
    bool, w := IsConsistent(M,V!Coordinates(Q[n+2]));
    require bool and &and[ w[i] ne 0 : i in [1..n+1] ] : 
        "Argument 2 must consist of n+2 points, of which no n+1 are dependent."; 
    return Automorphism(P,DiagonalMatrix([w[i] : i in [1..n+1]])*M);
end intrinsic;

intrinsic Translation(P::Prj,S::[Pt]) -> MapSch
{A translation taking the points [0:..1:..0] of P to the dim(P) + 1
points of S}
    // Simply the map from the matrix having the points of S as columns.
    require IsOrdinaryProjective(P) and IsField(BaseRing(P)):
	"First argument must be an ordinary projective space defined over a field";
    require IsComplete(S) and #S eq Length(P):
	"The sequence has the wrong length or is incomplete";
    require S subset P:
	    "The points lie in the wrong ambient space";
    return Automorphism(P,M)
    	where M is Matrix(Length(P),entries)
	where entries is &cat[ Coordinates(p) : p in S ];
end intrinsic;
    
intrinsic Translation(P::Prj,p::Pt,q::Pt) -> MapSch
{A linear automorphism of P taking p to q}
    require IsOrdinaryProjective(P):
	"First argument must be an ordinary projective space";
    require p in P and q in P:
	"Arguments lie in different ambient space";
    return Automorphism(P,Matrix(phi))
	where phi is Translation(P,p) * Inverse(Translation(P,q));
end intrinsic;

forward trans_matrix, make_funs;
intrinsic Translation(S::Sch,p::Pt) -> MapSch
{The automorphism which translates p to the origin (of the first affine patch)}
    require p in S:
        "Arguments lie in different ambient spaces";
    if Type(S) eq Aff then
        return iso< S -> S | polys1,polys2 >
            where polys1 := [R | R.i - p[i] : i in [1..Rank(R)] ]
            where polys2 := [R | R.i + p[i] : i in [1..Rank(R)] ]
                where R is CoordinateRing(S);
    elif Type(S) eq Prj then
        require IsOrdinaryProjective(S):
            "If projective ambient, argument must be ordinary projective space";
        return iso< S -> S | make_funs(R,M^-1),make_funs(R,M) >
                where M is trans_matrix(S,p)
                where R is CoordinateRing(S);
    else
        return  Translation(Ambient(S),p);
    end if;
end intrinsic;
 
make_funs := function(R,M)
    // make the homogeneous linear polys in R corresponding to matrix M
    return [ &+[ M[i,j]*R.j : j in [1..Rank(R)] ] : i in [1..Rank(R)] ];
end function;
 
trans_matrix := function(P,p)
    // This computes a matrix of full rank with p as the last column 
    np := Length(P);
    _,nonzero := NonZeroCoordinates(p);
    ind := nonzero[#nonzero];
    M := Transpose(Matrix(np,
        [ BaseRing(P) | 0 : i in [1..np*(np-1)] ] cat Coordinates(Minus(p)) ));
    corr := 0;
    for i in [1..np-1] do
        if i eq ind then
            corr := 1;
        end if;
        M[i+corr,i] := 1;
    end for;
    return M;
end function;

