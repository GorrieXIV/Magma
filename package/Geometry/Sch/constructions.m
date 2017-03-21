freeze;

///////////////////////////////////////////////////////////////////////
// constructions.m
// April 2001 GDB
///////////////////////////////////////////////////////////////////////

// added 04/13 - mch - to be used by transformation intrinsics - particularly
//  isomorphisms - to transfer most (geometric) scheme attributes to the target
intrinsic InternalTransferAttributes1(X::Sch,Y::Sch)
{}
    if assigned X`Nonsingular and not(assigned Y`Nonsingular) then
	Y`Nonsingular := X`Nonsingular;
    end if;
    if assigned X`Reduced and not(assigned Y`Reduced) then
	Y`Reduced := X`Reduced;
    end if;
    if assigned X`Irreducible and not(assigned Y`Irreducible) then
	Y`Irreducible := X`Irreducible;
    end if;
    if assigned X`GeometricallyIrreducible and not(assigned Y`GeometricallyIrreducible) then
	Y`GeometricallyIrreducible := X`GeometricallyIrreducible;
    end if;
    if assigned X`CM then
	Y`CM := X`CM;
    end if;
    if assigned X`gor then
	Y`gor := X`gor;
    end if;
    if assigned X`normal then
	Y`normal := X`normal;
    end if;

    //should add genus for curves if known - can't immediately get at it!

    // add extra surface attributes
    if ISA(Type(X),Srfc) then
      if assigned X`pg then
	Y`pg := X`pg;
      end if;
      if assigned X`q then
	Y`q := X`q;
      end if;
      if assigned X`K2m then
	Y`K2m := X`K2m;
      end if;
      if assigned X`kod_dim then
	Y`kod_dim := X`kod_dim;
      end if;
       if assigned X`kod_enr2 then
	Y`kod_enr2 := X`kod_enr2;
      end if;
       if assigned X`only_simple_sings then
	Y`only_simple_sings := X`only_simple_sings;
      end if;          	
    end if;
          
end intrinsic;

function graph_map_linear_domain_transform(imXY,mp)

    n := Length(Domain(imXY)); m := Length(Codomain(imXY));
    I := mp`GraphIdeal; R := Generic(I);
    d := Rank(I)-n;
    R1 := PolynomialRing(BaseRing(R),m+d,"grevlex");
    hm := hom<R-> R1|seq1 cat [R1.i : i in [m+1..m+d]]>
	where seq1 is [Evaluate(f,seq) : f in 
	  InverseDefiningPolynomials(imXY)] where
	   seq is [R1.j : j in [1..m]];
    B := [hm(b) : b in Basis(I)];
    I1 := ideal<R1|[b : b in B | b ne 0]>;
    return SchemeGraphMap(Codomain(imXY), Codomain(mp), I1 :
		Saturated := true);

end function;

procedure extra_data_transfer_lin_IM(X,~Y,imXY)
    if assigned X`SingularSubscheme then
	Y`SingularSubscheme := Scheme(Y,DefiningPolynomials(imXY(X`SingularSubscheme)));
    end if;

    if ISA(Type(X),Srfc) then
      if assigned X`K2 then
	Y`K2 := X`K2;
      end if;	
      if assigned X`simp_sings then
	Y`simp_sings := [* <imXY(ss[1]),ss[2],ss[3]> : ss in 
				X`simp_sings *];
      end if;
      if assigned X`min_map then
	mp := X`min_map;
	Y`min_map := (ISA(Type(mp),MapSch) select
	  Expand(Inverse(imXY)*mp) else 
		graph_map_linear_domain_transform(imXY,mp));
      end if;
      if assigned X`can_mod_map then
	mp := X`can_mod_map;
	Y`can_mod_map := (ISA(Type(mp),MapSch) select
	  Expand(Inverse(imXY)*mp) else 
		graph_map_linear_domain_transform(imXY,mp));
      end if;
      if assigned X`fibre_map then
	mp := X`fibre_map;
	Y`fibre_map := (ISA(Type(mp),MapSch) select
	  Expand(Inverse(imXY)*mp) else 
		graph_map_linear_domain_transform(imXY,mp));
      end if;      
    end if;
end procedure;

intrinsic Intersection(X::Sch,Y::Sch) -> Sch
{The scheme defined by all of the defining DefiningPolynomials of X and Y}
    require IdenticalAmbientSpace(X,Y):
	"Arguments lie in different ambient spaces";
    return Scheme(X,DefiningPolynomials(Y));
end intrinsic;

intrinsic 'meet'(X::Sch,Y::Sch) -> Sch
{The scheme defined by all of the defining DefiningPolynomials of X and Y}
    return Intersection(X,Y);
end intrinsic;

intrinsic 'join'(X::Sch,Y::Sch) -> Sch
{The union of the schemes X and Y}
    return Union(X,Y);
end intrinsic;

intrinsic '&join'(S::[Sch]) -> Sch
    {}
    require #S ge 1 : "Argument must be nonempty.";
    require IsComplete(S): "Argument must be a complete sequence.";
    A := Ambient(S[1]);
    X := EmptySubscheme(A);
    for i in [1..#S] do
	require A eq Ambient(S[i]) :
	   "Argument must consist of subschemes of common ambient.";
	X join:= S[i];
    end for;
    return X;
end intrinsic;

intrinsic '&meet'(S::[Sch]) -> Sch
    {}
    require #S ge 1 : "Argument must be nonempty.";
    require IsComplete(S): "Argument must be a complete sequence.";
    A := Ambient(S[1]);
    X := A;
    for i in [1..#S] do
	require A eq Ambient(S[i]) :
   	    "Argument must consist of subschemes of common ambient.";
	X meet:= S[i];
    end for;
    return X;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//		Removing components of schemes
///////////////////////////////////////////////////////////////////////

intrinsic RemoveHypersurface(X::Sch,Y::Sch) -> Sch,RngIntElt
{The scheme X after removing any Y components of it assuming that X and Y are
both hypersurfaces; the number of factors removed is also returned}
    require IdenticalAmbientSpace(X,Y):
	"Arguments lie in different ambient spaces";
    require IsHypersurface(X) and IsHypersurface(Y):
	"Both arguments must be hypersurfaces";
    s := Polynomial(X);
    n := -1;
    more := true;
    while more do
        more,s1 := IsDivisibleBy(s,Polynomial(Y));
        if more then
            s := s1;
        end if;
        n +:= 1;
    end while;
    if Type(X) eq Crv then
	return Curve(Ambient(X),s),n;
    else
	return Scheme(Ambient(X),s),n;
    end if;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//		Secants
///////////////////////////////////////////////////////////////////////

/*
THINK: OMIT since projective case not done properly?

intrinsic SecantVariety(X::Sch) -> Sch
{The secant variety of X}
// This is taken from distributed notes of Stillman.
    A := Ambient(X);
    require HasGroebnerBasis(A):
	"Argument does not admit Groebner basis calculations";
    if Type(A) ne Aff then
	return ProjectiveClosure(SecantVariety(AffinePatch(X,1)));
	// THINK: need to choose patch more carefully.
    end if;
    RA := CoordinateRing(A);
    na := Rank(RA);
    E := DefiningPolynomials(X);
    Rbig := PolynomialRing(BaseRing(A),3*na+1);
    h1 := hom< RA -> Rbig | [ Rbig.i : i in [1..na] ] >;
    h2 := hom< RA -> Rbig | [ Rbig.i : i in [na+1..2*na] ] >;
    h3 := hom< RA -> Rbig | [ Rbig.i : i in [2*na+2..3*na+1] ] >;
    t := Rbig.(2*na+1);
    I := ideal< Rbig | [t*h1(A.i) + (1-t)*h2(A.i) - h3(A.i) : i in [1..na] ]
			    cat [ h1(f) : f in DefiningPolynomials(X) ]
			    cat [ h2(f) : f in DefiningPolynomials(X) ] >;
    J := EliminationIdeal(I,2*na+1);
    return Scheme(A,J1)
	where J1 is [ bigtoA(f) : f in Basis(J)]
	where bigtoA is hom< Rbig -> RA |
		[ RA!0 : i in [1..2*na+1] ] cat [ RA.i : i in [1..na] ]>;
end intrinsic;
*/

//////////// Elimnation of variables ////////////////////////////
////////       mch 11/2012 //////////////////////////////////////

intrinsic RemoveLinearRelations(X::Sch) -> Sch, MapIsoSch
{ Eliminates variables coming from linear relations of ordinary projective
  scheme X. Returns the resulting scheme Y and the isomorphism from X to Y }

    require IsOrdinaryProjective(X): "X should be an ordinary projective scheme";
    Saturate(~X);
    B := MinimalBasis(Ideal(X));
    B1 := [b : b in B | LeadingTotalDegree(b) eq 1];
    if #B1 eq 0 then return X,IdentityMap(X); end if;
    R := CoordinateRing(Ambient(X));
    n := Rank(R);
    mat := Matrix([[MonomialCoefficient(b,R.i) : i in [1..n]] : b in B1]);
    mat := EchelonForm(mat);
    inds := [Min(Support(mat[i])) : i in [1..Nrows(mat)]];
    js := [i : i in [1..n] | i notin inds];
    m := #js;
    if m eq 0 then //X empty!
	P := ProjectiveSpace(BaseRing(R),0);
	Y := Scheme(P,P.1);
	mp := iso<X->Y|[R.1],[R1.1 : i in [1..n]]> where R1 is CoordinateRing(P);
	return Y,mp;
    end if;
    P := ProjectiveSpace(BaseRing(R),m-1);
    R1 := CoordinateRing(P);
    subs1 := [R.i : i in js];
    subs2 := [R1!0 : i in [1..n]];
    for i in [1..m] do subs2[js[i]] := R1.i; end for;
    mvec := Eltseq(ChangeRing(mat,R1)*Matrix(R1,n,1,subs2));
    for i in [1..n-m] do subs2[inds[i]] := -mvec[i]; end for;
    B2 := [b : b in B | LeadingTotalDegree(b) gt 1];
    B3 := [b : b in DefiningPolynomials(X) | LeadingTotalDegree(b) gt 1];
    if #B2 lt #B3 then B3 := B2; end if;
    eqns := [Evaluate(b,subs2) : b in B3];
    if ISA(Type(X),Crv) then
	Y := Curve(P,eqns);
    elif ISA(Type(X),Srfc) then
	Y := Surface(P,eqns : Check := false);
    else
        Y := Scheme(P,eqns);
    end if;
    mp := iso<X->Y|subs1,subs2 : Check := false>;
    // transfer attributes from X to Y
    InternalTransferAttributes1(X,Y);
    extra_data_transfer_lin_IM(X,~Y,mp);   
    return Y,mp;

end intrinsic;
