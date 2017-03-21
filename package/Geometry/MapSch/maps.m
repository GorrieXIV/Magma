freeze;

declare verbose SchImage, 1;

///////////////////////////////////////////////////////////////////////
// Basic map constructors
///////////////////////////////////////////////////////////////////////

function IsCoercibleMatrix(S,M) // -> BoolElt, Mtrx
    // True if and only if all entries of M are coercible
    // into S; in that case, also return 'S!M'
    bool := true;
    nc := NumberOfColumns(M);
    nr := NumberOfRows(M);
    newentries := [ S | ];
    for i in [1..nr] do
        for j in [1..nc] do
            iscoer,x := IsCoercible(S,M[i,j]);
            if not iscoer then
                bool := false;
                break i;
            end if;
            Append(~newentries,x);
        end for;
    end for;
    if bool then
        Mnew := Matrix(nc,newentries);
        return bool,Mnew;
    else
        return bool,_;
    end if;
end function;

///////////////////////////////////////////////////////////////////////
// Maps in general
///////////////////////////////////////////////////////////////////////

intrinsic IdentityMap(X::Sch) -> MapIsoSch
{The identity map of X}
    if Type(Ambient(X)) eq TorVar then
        return ToricIdentityMap(Ambient(X));
    end if;
    return iso<X->X|F,F> where F is [ X.i : i in [1..Length(X)] ];
end intrinsic;

intrinsic ConstantMap(A::Sch,B::Sch,p::Pt) -> MapSch
{The constant map A -> B with image p}
    require p in B:
        "The third argument should be a point of the second";
    bool,p1 := IsRationalPoint(B,p);
    require bool:
	"Point argument must be a rational point of the second argument";
    require BaseRing(A) cmpeq BaseRing(B):
        "Arguments must be defined over a common base ring";
    return map< A -> B | Coordinates(p1) >;
end intrinsic;

intrinsic Restriction(f::MapSch,X::Sch,Y::Sch : Check:=true, Inverse:=false ) -> MapSch
{The restriction of f to the scheme X in its domain and to new codomain Y. If f has inverse
 defining equations and parameter Inverse is true (default: false), checks to see whether they remain valid
 inverse equations under the restriction and includes them if so. }
    if Check then
      bool := Codomain(f) subset Y;
      require X subset Domain(f) and
          (bool or Y subset Codomain(f)):
          "Second argument must lie inside the domain of the first and " *
                  "third argument must be related to codomain of the first";
      // mch - 03/14 - this should be done (more efficiently!) in the map constructor
      //if not bool then
          //require f(X) subset Y:
              //"Image of second argument under the first must lie in the third";
      end if;
    //end if;
    if HasKnownInverse(f) and Inverse and IsProjective(X) and IsProjective(Y) then
      //cheap case for inheritance of inverses.
      feq:=DefiningEquations(f);
      invfeq:=InverseDefiningPolynomials(f);
      // mch -03/14 - think it is probably more efficient to work with the ambient
      // coordinate rings in general, particularly in the projective case where
      // degrees aren't lowered by normal forms and the normal form doesn't
      // necessarily have fewer terms than an original expression. Best to
      // just do the "reduction mod I" check at the end rather than continually
      // by working in R/I.
      v:=[C.i:i in [1..Rank(C)]] where C:=CoordinateRing(Ambient(Y));
      w:=[Evaluate(Evaluate(f,invfeq),v):f in feq];
      Saturate(~Y); I := Ideal(Y);
      if exists{[i,j]: j in [i+1..#v] , i in [1..#v-1]|
                     w[i]*v[j]-w[j]*v[i] notin I} then
        return map< X -> Y | feq : Check := Check>;
      end if;
      if (not assigned X`Irreducible) or (not X`Irreducible) then
        v:=[C.i:i in [1..Rank(C)]] where C:=CoordinateRing(Ambient(X));
        w:=[Evaluate(Evaluate(f,feq),v):f in invfeq];
	Saturate(~X); I := Ideal(X);
        if exists{[i,j]: j in [i+1..#v], i in [1..#v-1] |
                     w[i]*v[j]-w[j]*v[i] notin I} then
          return map< X -> Y | feq : Check := Check>;
        end if;
      end if;
      return map< X -> Y | feq,invfeq : Check := Check, CheckInverse := false>;
    end if;
    return map< X -> Y | DefiningPolynomials(f) : Check := Check >;
end intrinsic;


///////////////////////////////////////////////////////////////////////
// Explicit Automorphisms
///////////////////////////////////////////////////////////////////////

intrinsic IdentityAutomorphism(X::Sch) -> MapIsoSch
    {The identity automorphism on X}
    return IdentityMap(X);
end intrinsic;
 
intrinsic PermutationAutomorphism(S::Sch,g::GrpPermElt) -> MapIsoSch
{The automorphism of S that permutes its coordinates according to g}
    n := Length(S);
    require Degree(Parent(g)) eq n:
        "The permutation acts on the wrong number of coordinates";
    return iso< S -> S | polys1,polys2 >
	where polys1 is [ S.i^g : i in [1..n] ]
	where polys2 is [ S.i^(g^-1) : i in [1..n] ];
end intrinsic;
 
intrinsic Automorphism(S::Sch,g::GrpPermElt) -> MapIsoSch
{The automorphism of S that permutes its coordinates according to g}
    return PermutationAutomorphism(S,g);
end intrinsic;

intrinsic Automorphism(X::Sch,F::[RngElt]) -> MapSch
{The automorphism determined by the sequence F of functions}
    require CanChangeUniverse(F, FieldOfFractions(CoordinateRing(Ambient(X)))) :
        "Argument 2 must be functions on the ambient space of argument 1.";
    autm := map< X -> X | F >;
    bool, aut := IsAutomorphism(autm);
    require bool: "Argument 2 does not define an automorphism.";
    return aut;
end intrinsic;


///////////////////////////////////////////////////////////////////////
// Explicit automorphisms of projective spaces
///////////////////////////////////////////////////////////////////////

forward make_funs;
intrinsic Automorphism(P::Sch,M::Mtrx) -> MapIsoSch
{The automorphism of P determined by the matrix of base ring elements M}
    require IsAffine(P) or IsOrdinaryProjective(P):
        "Argument 1 must be an ordinary projective space or an affine space.";
    coerced,M1 := IsCoercibleMatrix(BaseRing(P),M);
    require coerced:
        "Argument 2 is not coercible into the base ring of argument 1";
    require NumberOfRows(M1) eq NumberOfColumns(M1) and
        NumberOfColumns(M1) eq Length(P) and Rank(M1) eq Length(P):
        "Argument 2 must be invertible.";
    return iso< P -> P | make_funs(R,M1),make_funs(R,M1^-1) >
                where R is CoordinateRing(P);
end intrinsic;
 
make_funs := function(R,M)
    // make the linear polys in R corresponding to matrix M
    return [ &+[ M[i,j]*R.i : i in [1..Rank(R)] ] : j in [1..Rank(R)] ];
end function;

intrinsic QuadraticTransformation(P::Prj) -> MapIsoSch
    {The quadratic automorphism [x,y,...] -> [1/x,1/y,...]
    of the projective plane P.}
    x := P.1; y := P.2; z := P.3; 
    require IsOrdinaryProjective(P) and Dimension(P) eq 2 :
	"Argument must be an ordinary projective plane.";
    return iso< P -> P | [y*z,x*z,x*y], [y*z,x*z,x*y] >;
end intrinsic;
 
intrinsic QuadraticTransformation(P::Prj,S::[Pt]) -> MapIsoSch
    {The quadratic transformation of P with respect to the linearly
    independent points of S.}
    // this just conjugates the standard quad'c transf'n with a translation.
    require IsOrdinaryProjective(P) and Dimension(P) eq 2 :
	"Argument must be an ordinary projective plane.";
    require IsComplete(S): "Argument 2 must be a complete sequence.";
    require #S eq 3: "Argument 2 must contain 3 independent points";
    bool, S := CanChangeUniverse(S,P(BaseRing(P)));
    require bool : "Argument 2 must consist of rational points.";
    M := Matrix(3,&cat[ Coordinates(p) : p in S ]);
    require Rank(M) eq 3: "Argument 2 must contain 3 independent points";
    return phi * QuadraticTransformation(P) * Inverse(phi)
	where phi is Automorphism(P,M);
end intrinsic;

///////////////////////////////////////////////////////////////////////
// Explicit automorphisms of affine space
///////////////////////////////////////////////////////////////////////

intrinsic Automorphism(S::Sch,p::RngMPolElt) -> MapIsoSch
{The automorphism (x,y,...) ->  (x+p,y,...) where p is a polynomial on S
or its ambient space not involving x}
    A := Ambient(S);
    bool,p1 := IsCoercible(CoordinateRing(A),p);
    require bool: "The polynomial is not defined on the ambient space";
    require Degree(p,1) lt 1: "The polynomial involves the first variable";
    return iso< S -> S | polys1,polys2 >
	where polys1 is [ A.1 + p ] cat [ A.i : i in [2..Length(S)] ]
	where polys2 is [ A.1 - p ] cat [ A.i : i in [2..Length(S)] ];
end intrinsic;

intrinsic Projectivity(A::Aff,M::Mtrx) -> MapAutSch
{The projectivity of A determined by the matrix of base ring elements M}
    k := BaseRing(A);
    require IsField(k):
	"First argument must be defined over a field";
    na := Length(A);
    coerced,M1 := IsCoercibleMatrix(k,M);
    require coerced:
        "The matrix entries must be coercible into the ambient base ring";
    require NumberOfColumns(M1) eq na + 1:
        "Matrix has the wrong number of columns";
    require NumberOfRows(M1) eq na + 1:
        "Matrix has the wrong number of rows";
    require Rank(M1) eq na + 1:
        "Matrix must have full rank";
    funs := [ prefuns[i]/prefuns[na+1] : i in [1..na] ]
	where prefuns is [ R |
		&+[ M1[i,j]*R.j : j in [1..na] ] + M1[i,na+1] : i in [1..na+1] ]
	where R is CoordinateRing(A);
    M2 := M1^-1;
    invfuns := [ iprefuns[i]/iprefuns[na+1] : i in [1..na] ]
	where iprefuns is [ R |
		&+[ M2[i,j]*R.j : j in [1..na] ] + M2[i,na+1] : i in [1..na+1] ]
	where R is CoordinateRing(A);
    return iso< A -> A | funs,invfuns >;
end intrinsic;

intrinsic NagataAutomorphism(A::Aff) -> MapSch
{The Nagata automorphism of 3-space}
    require Dimension(A) eq 3 and Type(A) eq Aff:
        "Argument must be an affine 3-space";
    return Automorphism(A,[ A.1 - 2*A.2*q - A.3*q^2, A.2 + A.3*q, A.3 ])
                        where q := A.1*A.3 + A.2^2;
end intrinsic;

intrinsic AffineDecomposition(f::MapSch) -> MapSch,MapSch
{A linear endomorphism l and a translation t with f = l o t}
    require IsAffineLinear(f): "Argument is not affine linear";
    require IsEndomorphism(f): "Argument is not an endomorphism.";
    A := Domain(f);
    funs := DefiningPolynomials(f);
    n := Dimension(A);
    coeffs := &cat[ [ Coefficient(fi,i,1) : i in [1..n]] : fi in funs ];
    linear := Automorphism(A,Transpose(Matrix(n,coeffs)));
    trans := Translation(A,A![ BaseRing(A) | -ConstantTerm(fi) : fi in funs ]);
    return linear, trans;
end intrinsic;


///////////////////////////////////////////////////////////////////////
// Extras
///////////////////////////////////////////////////////////////////////

intrinsic QuadraticTransformation(X::Sch) -> Sch, MapIsoSch
    {The birational pullback of X under the standard quadratic
    transformation, }
    P := Ambient(X);
    require IsOrdinaryProjective(P) and Dimension(P) eq 2 : 
	"Argument must be contained in an ordinary projective plane";
    E0 := DefiningPolynomials(X);
    require &or[ Evaluate(f,[P.1,P.2,0]) ne 0 : f in E0 ] and 
            &or[ Evaluate(f,[P.1,0,P.3]) ne 0 : f in E0 ] and 
            &or[ Evaluate(f,[0,P.2,P.3]) ne 0 : f in E0 ]:
        "Argument must have no component at infinity.";
    if Dimension(X) eq 0 then
        require &or[ Evaluate(f,[P.1,0,0]) ne 0 : f in E0 ] and 
                &or[ Evaluate(f,[0,P.2,0]) ne 0 : f in E0 ] and 
                &or[ Evaluate(f,[0,0,P.3]) ne 0 : f in E0 ]:
            "Argument must have no component at infinity.";
    end if;
    // pullback X using the equations of the st'd quad'c transformation
    phi := QuadraticTransformation(P);
    // remove all coordinate factors from the equations
    pols := DefiningPolynomials(X @@ phi);
    for i in [1..3] do
	for j in [1..#pols] do
            pols[j] := RemoveFactor(pols[j],i);
	end for;
    end for;
    // return a curve type if that is what was input
    if ISA(Type(X),Crv) and TotalDegree(pols[1]) ge 1 then
        Y := Curve(P,pols[1]);
    else
        Y := Scheme(P,pols);
    end if;
    return Y, iso< X -> Y | funs, funs > 
        where funs := DefiningPolynomials(phi); 
end intrinsic;
 
intrinsic QuadraticTransformation(X::Sch,S::[Pt]) -> Sch, MapIsoSch 
    {The birational pullback of X quadratic transformation 
    of P in the linearly independent points of S.}
    // this just conjugates the standard quad'c transf'n with a translation.
    P := Ambient(X);
    require IsOrdinaryProjective(P) and Dimension(P) eq 2 :
	"Argument must be contained in an ordinary projective plane";
    require IsComplete(S): "Argument 2 must be a complete sequence.";
    require #S eq 3: "Argument 2 must contain 3 independent points.";
    bool, S := CanChangeUniverse(S,P(BaseRing(P)));
    require bool : "Argument 2 must consist of rational points.";
    E0 := DefiningPolynomials(X);
    require &or[ Evaluate(f,[P.1,P.2,0]) ne 0 : f in E0 ] and 
            &or[ Evaluate(f,[P.1,0,P.3]) ne 0 : f in E0 ] and 
            &or[ Evaluate(f,[0,P.2,P.3]) ne 0 : f in E0 ]:
        "Argument must have no component at infinity.";
    if Dimension(X) eq 0 then
        require &or[ Evaluate(f,[P.1,0,0]) ne 0 : f in E0 ] and 
                &or[ Evaluate(f,[0,P.2,0]) ne 0 : f in E0 ] and 
                &or[ Evaluate(f,[0,0,P.3]) ne 0 : f in E0 ]:
            "Argument must have no component at infinity.";
    end if;
    M := Matrix(3,&cat[ Coordinates(p) : p in S ]);
    require Rank(M) eq 3: "Argument 2 must contain 3 independent points.";
    phi := Automorphism(P,M);
    pols := DefiningPolynomials(X @@ phi);
    for i in [1..3] do
	for j in [1..#pols] do
            pols[j] := RemoveFactor(pols[j],i);
	end for;
    end for;
    // return a curve type if that is what was input
    if ISA(Type(X),Crv) and TotalDegree(pols[1]) ge 1 then
        Y := Curve(P,pols[1]);
    else
        Y := Scheme(P,pols);
    end if;
    return Y, iso< X -> Y | funs, funs > 
        where funs := DefiningPolynomials(phi); 
end intrinsic;

intrinsic InternalImageOrdProj(E::SeqEnum, I::RngMPol, irred::BoolElt)
		-> RngMPol
{Function for internal use}
// currently only used if irred = true.
    R := Universe(E);
    n := Rank(R);
    m := #E;
    // map is from P^(n-1) -> P^(m-1)

    // create "graph"
    PG := PolynomialRing(BaseRing(R),n+m,"grevlex");
    incl_hom := hom<Generic(I) -> PG | [PG.i : i in [1..n]]>;
    E1 := [incl_hom(e) : e in E];
    I_gr := ideal<PG|[incl_hom(b) : b in Basis(I)] cat
	[PG.(n+i)*E1[j]-PG.(n+j)*E1[i] : j in [i+1..m], i in [1..m]]>;

    vprint SchImage : "Saturating..";
    if irred then
      // only need to saturate by one non-zero elt of E
      i := 1;
      while i le m do
	if not IsInRadical(E[i],I) then break; end if;
	i +:= 1;
      end while;
      vtime SchImage : I_gr_sat := ColonIdeal(I_gr,E1[i]);
    else
      vtime SchImage : I_gr_sat := &meet[ColonIdeal(I_gr,e) : e in E1];
    end if;
    
    vprint SchImage : "Eliminating..";
    vtime SchImage : B := GroebnerBasis(I_gr_sat); //assume that its a Groebner basis!
    /*B_im := [f : f in B | &and[&and[e[i] eq 0 : i in [1..n]] 
                        where e is Exponents(t): t in Terms(f)]];*/
    B_im := [f : f in B | &and[e[i] eq 0 : i in [1..n]] 
			where e is Exponents(LeadingTerm(f))];

    return ideal<PG|B_im>;
 
end intrinsic;

