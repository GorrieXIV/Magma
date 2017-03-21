freeze;

///////////////////////////////////////////////////////////////////////
// singularity.m
// April 2001 GDB
///////////////////////////////////////////////////////////////////////

/* added mch 06/10 - for ambients A not covered by affine patchs, return
   defining equations for the "bad" subscheme of A for where the Jacobian
   subrank scheme doesn't necessarily give the singular points -
   initially just for old-style weighted projective space. Should extend
   for other toric ambients and hopefully, eventually replace the machinery
   with a version that can use toric patches and work everywhere. */
/*
function coordinate_ideal_intersection(R,seqs)
    if #seqs eq 0 then return ideal<R|>; end if;
    B := [R.i : i in seqs[1]];
    for i in [2..#seqs] do
	inds := seqs[i];
	Bexps := [Exponents(b) : b in B];
	Bset := Seqset(B); xj := R.j
	for j in inds do
	  Bset join:= {B[i]*(Bexps[i][j] eq 0 select xj else 1) : i in [1..#B]};	  
	end for;
	B := Setseq(Bset); 
    end for;
    return ideal<R|B>; 
end function;
*/

function ambient_type(A)
// returns 0 if A is covered by affine patches, 1 if bad_subscheme equations
//  works for A and 2 otherwise.
    if IsAffine(A) or IsOrdinaryProjective(A) then return 0; end if;
    if NumberOfQuotientGradings(A) gt 0 then return 2; end if;
    if NumberOfGradings(A) eq 1 then
	if &and[d ge 0 : d in Gradings(A)[1]] then
	  return 1;
	else
	  return 2;
	end if;	
    end if;
    // product projective space? Should be more general criterion for
    //  affine patch coverage
    mat := Matrix(Gradings(A));
    if &and[(e ge 0) and (e le 1) : e in Eltseq(mat)] and
	&and[(u eq 0) or (u eq 1) where u is &+[mat[i,j] : i in [1..Nrows(mat)]]
		: j in [1..Ncols(mat)]] then
	return 0;
    end if;
    return 2;
end function;

function bad_subscheme_equations(A)
// Return eqns of subscheme S of (WPS) ambient for which Jacobian criterion
//  as currently applied fails on (X meet S) <= X, X a subscheme of A.
// What is computed is the (reduced) subscheme of points on which certain
// finite covering maps from affine patches of the "cone" over A to "conified"
// affine patches of A fail to be etale. Outside of these, smoothness of
// X corresponds to smoothness of the points of the affine cone over X for
// which the Jacobi criterion works.
    ds := Gradings(A)[1];
    inds := [i : i in [1..#ds] | ds[i] ne 0];
    //zero_inds := [i : i in [1..#ds] | ds[i] eq 0];

    ds1 := [ds[i] : i in inds];
    fs := [[Integers()|f[1] : f in Factorisation(d)] : d in ds1];
    ps := Setseq(&join([Seqset(f) : f in fs]));
    dsmax := [{i : i in [1..#fs] | p in fs[i]} : p in ps];
    N := #dsmax;
    if N eq 0 then return ideal<CoordinateRing(A)|1>; end if;
    for j  := N to 1 by -1 do
	if &or[dsmax[j] subset dsmax[i] : i in [1..#dsmax] | i ne j] then
	   Remove(~dsmax,j);
	end if;
    end for;
    R := CoordinateRing(A);
    bad_cmps := [[R.j : j in inds | j notin dm] : dm in dsmax];
    Ibad := &meet[ideal<R|seq> : seq in bad_cmps];
    return Ibad, bad_cmps;  
end function;

intrinsic Codimension(X::Sch) -> RngIntElt
    {The codimension of X in its ambient space.}
    return Dimension(Ambient(X)) - Dimension(X);
end intrinsic;

intrinsic JacobianSubrankScheme(X::Sch) -> Sch
    {The subscheme of X of points at which the jacobian matrix of X drops rank.}
    if Dimension(X) eq -1 then // special case for empty scheme
	return EmptySubscheme(X);
    end if;
    minors := Minors(JacobianMatrix(X),Codimension(X));
    if IsProjective(X) then
        // THINK: This assumes that BaseRing is a field!!
        if 0 in [ TotalDegree(p): p in minors ] then 
           return Z where Z := EmptySubscheme(X);
        end if;
	if &and[ TotalDegree(p) lt 0 : p in minors ] then
	    return Scheme(X,[]);
	end if;
    end if;
    // remove zeroes from list of minors
    minors := [p : p in minors | TotalDegree(p) ge 0];
    return Scheme(X,minors);
end intrinsic;

function ClstrToPoint(Z)
// Z is a zero-dimensional reduced, irreducible subscheme in affine
// space A over a field k giving a scheme-theoretic closed point representing a
// set of conjugate points over a finite extension of k.
// Return Eltseq of the point in A(K) corresponding to Z, where K is the residue
// field of Z.

    R := CoordinateRing(Ambient(Z));
    n := Rank(R);
    if MonomialOrder(R)[1] cmpeq "lex" then
	GB := GroebnerBasis(Ideal(Z));
    else
	R0 := PolynomialRing(BaseRing(R),n);
	GB := GroebnerBasis(ideal<R0|[R0!b : b in Basis(Ideal(Z))]>);
	GB := [R!b : b in GB];
    end if;
    assert #GB eq n;
    K := BaseRing(R);
    fn := UnivariatePolynomial(GB[n]);
    if Degree(fn) eq 1 then
	seq := [-Coefficient(fn,0)/Coefficient(fn,1)];
    else
	K := ext<K|fn>;
	seq := [K.1];
    end if;
    for i := n-1 to 1 by -1 do
	coeffs := [Evaluate(c,s) : c in Coefficients(GB[i],i)]
	  where s is [K!0 : j in [1..i]] cat seq;
	if #coeffs eq 2 then //GB[i] degree 1 in R.i
	  Insert(~seq,1,-coeffs[1]/coeffs[2]);
	else
	  K := ext<K|PolynomialRing(K)!coeffs>;
	  ChangeUniverse(~seq,K);
	  Insert(~seq,1,K.1);
	end if;
    end for;
    return seq;

end function;

function image_in_weighted_patch(X,pcm,bprimdec)
// X is a closed subscheme of a weighted proj space P and pcm is the
// inclusion map A -> P of an affine patch (NB: pcm has a base scheme
// whenever the weight corresponding to the patch index is > 1).
// compute pcm^-1(X) <= A, assuming no primary component of X
// lies in (the closure of) the base scheme of pcm.
// If bprimdec is true then compute the primary decomposition of X
// and use this to try to perform only one saturation when removing
// the base scheme.

    A := Domain(pcm);
    R := CoordinateRing(Ambient(A));
    if #Basis(Ideal(X)) eq 0 then return A; end if;
    if IsEmpty(X) then return Scheme(Ambient(A),R!1); end if;

    X1 := X@@pcm;
    I1 := Ideal(X1);

    // remove basescheme components from X1
    defs := AllDefiningPolynomials(pcm);
     // the base scheme for each set of defining equations is a monomial ideal
    bad_mons := [GroebnerBasis(Radical(ideal<R|GroebnerBasis(ideal<R|pols>)>)) : 
					pols in defs];
    if R!1 in &cat(bad_mons) then return X1; end if;
    Sort(~bad_mons,func<x,y|#x-#y>);
     // look for single set in bad_mons to use for saturation
    if (#bad_mons gt 1) and bprimdec then
      cmps := [Ideal(c) : c in PrimaryComponents(X)];
      P := CoordinateRing(Ambient(X));
      eqns := InverseDefiningPolynomials(pcm);
      // get index of variable for which A is the localisation.
      i := Setseq(Support(Vector(Exponents(Denominator(eqns[1])))))[1];
      eqns := [Numerator(e) : e in eqns];
      bmP := [[Evaluate(m,eqns) : m in b] cat [P.i] : b in bad_mons];
      for b in bad_mons do
	Ib := ideal<P|[Evaluate(m,eqns) : m in b] cat [P.i]>;
	if &and[Dimension(c+Ib) lt Dimension(c) : c in cmps] then
	   bad_mons := [b]; break;
	end if;
      end for;
    end if;
    for b in bad_mons do I1 := &meet[ColonIdeal(I1,f) : f in b]; end for;

    return Scheme(Ambient(A),I1);

end function;

intrinsic IsNonsingular(X::Sch : FullCheck := false) -> BoolElt
{ True iff X is nonsingular (strictly, smooth over the base ring). If FullCheck
  is false (the default), it is assumed that X is equidimensional. Otherwise the
  potentially expensive decomposition into equidimensional components is
  performed and the Jacobi criterion applied to each component.}
    if assigned X`Nonsingular then
	return X`Nonsingular;
    end if;

    if Type(X) eq Aff then
	return true;
    elif ISA(Type(X),Prj) then
	return #Gradings(X) ge 2 or IsOrdinaryProjective(X);
    else
	require HasGroebnerBasis(X) :
	    "Groebner basis methods required but unavailable";
	// mch - 06/10 - add a check for the 'bad' subscheme B of
        // toric ambients on which JacobianSubrankScheme may
	// give the wrong answer. If B intersects X non-trivially,
	// return an error.
	A := Ambient(X);
	typ := ambient_type(A);
	b_extra := false;
	if typ eq 1 then
	    Ibad,bad_cmps := bad_subscheme_equations(A);
	    Sbad := Scheme(A,Ibad);
	    Xbad := X meet Sbad;
	    b_bad := not IsEmpty(Xbad);
	    if b_bad and &and[ d gt 0 : d in Gradings(A)[1]] then
		//will apply extra affine check on 'bad part' for WPS
		b_bad := false; b_extra := true;
	    end if;
	end if;
	if (typ eq 2) or ((typ eq 1) and b_bad) then
	    error "Sorry, can't currently guarantee correct (non-)singularity\ncheck",
		"on part of this scheme (ambient toric singularity problem)";
	end if;
	if not FullCheck then
	    J := JacobianSubrankScheme(X);
	    if b_extra then J := Complement(J,Sbad); end if;
	    boo := IsEmpty(J);
	else
	    Saturate(~X);
	    IX := Ideal(X);
	    E := EquidimensionalDecomposition(IX);
	    if #E gt 1 then
		Xequis := [Scheme(Ambient(X),J : Saturated := true) : J in E];
		// first see if two components intersect
		boo := &and[IsEmpty(Intersection(Xequis[i],Xequis[j])) :
			j in [i+1..#Xequis], i in [1..#Xequis]];
		if boo then
		    boo := &and[IsEmpty((b_extra select Complement(J,Sbad) else J)) 
		      where J is JacobianSubrankScheme(Y): Y in Xequis];
		end if;
	    else
	        J := JacobianSubrankScheme(X);
	        if b_extra then J := Complement(J,Sbad); end if;
		boo := IsEmpty(J);
	    end if;
	end if;
	// if test has not already failed and we are in the extra affine
	// patch check case (weighted proj space), do those extra checks.
	if boo and b_extra then
	  R := CoordinateRing(A);
	  gr := Gradings(A)[1];
	  // first get a number of affine patches to cover (X meet Sbad)
	  bad_cmps := [L : L in bad_cmps | not IsEmpty(X meet Scheme(A,L))];
	  js := &join[{Rank(R)+1-i : i in [1..Rank(R)] | R.i notin L} : L
			in bad_cmps]; //patch indices
	  // often it is only a finite number of points at which the affine
	  // checks have to be made. Usually faster to decompose Xbad, base-extend and
	  // do these as point checks.
	  if Dimension(Xbad) eq 0 then
	    ptschs := [PrimeComponents(X meet Scheme(A,L)) : L in bad_cmps];
	    if #bad_cmps gt 1 then
	      ptschs := Setseq(&join[Seqset(p) : p in ptschs]);
	    else
	      ptschs := ptschs[1];
	    end if;
	    pjs := [];
	    for p in ptschs do
		jsp := [Rank(R)+1-j : j in js | R.(Rank(R)+1-j) notin Ideal(p)];
		_,i := Min([gr[j] : j in jsp]);
		Append(~pjs,jsp[i]);
	    end for;
//printf "pts:%o\n,pjs:%o\n",ptschs,pjs;
	    for j in Sort(Setseq(Seqset(pjs)),func<a,b|gr[a]-gr[b]>) do
		Aa,pcm := WeightedAffinePatch(A,Rank(R)+1-j);
		Xa := image_in_weighted_patch(X,pcm,true);//Inverse(pcm)(X);
		for p in [ptschs[i] : i in [1..#ptschs] | pjs[i] eq j] do
		  pa := Inverse(pcm)(p);
		  if IsSingular(Xa(Universe(seq))!seq) where seq is
		      ClstrToPoint(pa) then
		    boo := false; break;
		  end if;
		end for;
		if not boo then break; end if;
	    end for;
	  else
	    // retest all relevant affine patches - not very efficient!
	    // define affine scheme by its GB - expect this to generally be smaller
	    // than the initial set of def eqns, which include those of the patch.
	    boo := &and[IsNonsingular(Scheme(Ambient(Y),GroebnerBasis(Ideal(Y)))) where
		  Y is Inverse(pcm)(X) where
			_,pcm := WeightedAffinePatch(A,j) : j in js];
	  end if;
	end if;

	X`Nonsingular := boo;
	return X`Nonsingular;
    end if;
end intrinsic;

intrinsic IsSingular(X::Sch  : FullCheck := false) -> BoolElt
 { True iff X is singular (strictly, non-smooth over the base ring). If FullCheck
  is false (the default), it is assumed that X is equidimensional. Otherwise the
  potentially expensive decomposition into equidimensional components is
  performed and the Jacobi criterion applied to each component.}
    if assigned X`Nonsingular then
	return not X`Nonsingular;
    end if;

    if not (Type(X) eq Aff or ISA(Type(X),Prj)) then
	require HasGroebnerBasis(X) : 
	    "Groebner basis methods required but unavailable";
    end if;	
    return not IsNonsingular(X : FullCheck := FullCheck);
end intrinsic;

intrinsic IsSingular(p::Pt) -> BoolElt
    {True iff p is a singularity of X, or the scheme in which
    it lies if no scheme argument is given.}
    return IsSingular(Scheme(Parent(p)),p);
end intrinsic;

intrinsic IsSingular(X::Sch,p::Pt) -> BoolElt
{"} // "
    require p in X: "Argument 2 must be a point of argument 1.";

    if assigned X`SingularSubscheme then
	return p in X`SingularSubscheme;
    end if;

    if X eq Ambient(X) then
	// do ambient cases separately by hand.
	if Type(X) eq Aff then
	    return false;
	else
	    // This would be better...
	    // require false:
	    // "Unable to determine singularities in weighted projective space.";
	    // This answer now does not crash but is nonsense:
	    return #Gradings(X) eq 1 and not IsOrdinaryProjective(X);
	end if;
    end if;
    // true iff p is a singularity of X OR p doesn't lie in a top
    // dimensional component of X.
    J := JacobianMatrix(X);
    /* mch -10/05 - on the suggestion of M. Stoll, replaced the
	IsHypersurface(X) check to avoid Groebner comp.         */
    if Nrows(J) eq 1 then
	if DefiningPolynomials(X)[1] eq 0 then
	    return false; /* may be wrong for weighted proj space as above */
	end if;
	for f in ElementToSequence(J) do
	    if not Evaluate(f,Coordinates(p)) eq 0 then
		return false;
	    end if;
	end for;
	return true;
    else
	Jp := Matrix(Ncols(J), [ Evaluate(f,Eltseq(p)) : f in Eltseq(J) ]);
	return Rank(Jp) lt Codimension(X);
    end if;
end intrinsic;

intrinsic IsNonsingular(X::Sch,p::Pt) -> BoolElt
    {True iff p is a nonsingular point of X, or of the scheme
    in which it lies if no scheme argument is given.}
    return not IsSingular(X,p);
end intrinsic;

intrinsic IsNonsingular(p::Pt) -> BoolElt
{"} // "
    return not IsSingular(p);
end intrinsic;

function hyper_multiplicity(X,p)
 // special hypersurface case of general multiplicity function
    if IsProjective(X) then
	XA,q := AffinePatch(X,p);
	return TotalDegree(Polynomial(TangentCone(XA,q)));
    elif IsAffine(X) then
	return TotalDegree(Polynomial(TangentCone(X,p)));
    end if;
end function;

intrinsic Multiplicity(X::Sch,p::Pt) -> RngIntElt
    {The multiplicity of p as a point of X.}
    bool,p := (p in X);
    require bool: "Argument 2 must be a point on argument 1.";

    // special obvious hypersurface case
    if #DefiningEquations(X) eq 1 then
	return hyper_multiplicity(X,p);
    end if;
    
    // localise to affine patch
    if IsProjective(X) then
      X,p := AffinePatch(X,p);
    end if;
    // move p to the origin
    if &or[e ne 0 : e in Eltseq(p)] then
	L := Ring(Parent(p));
	if not(L cmpeq BaseRing(X)) then
	  X := BaseChange(X,L); 
	end if;
        // translate X 
        Xeqns := Basis(Ideal(X));
        Pol := Universe(Xeqns);
        subst := [Pol.i + p[i] : i in [1..Rank(Pol)]];
        X := Scheme(AmbientSpace(X), [Evaluate(f,subst) : f in Xeqns]);
    end if;
    // compute m(X,p) using local Groebner bases
    R := LocalPolynomialRing(BaseRing(X),Length(X),"lgrevlex");
    I := Ideal(X);
//printf "Ideal Groebner ... "; time
//    Groebner(I);
    Iloc := ideal<R|[R!b : b in Basis(I)]>;
//printf "Local Groebner ... "; time
    G := GroebnerBasis(Iloc);
    inits := [LeadingTerm(g) : g in G];
     // now the Hilbert series/poly of R/Iloc is the same as that
     //  of the (homogeneous) monomial ideal generated by inits
    R1 := PolynomialRing(BaseRing(X),Length(X), "grevlex");
    I1 := ideal<R1|inits>;
    H := HilbertPolynomial(I1);
    d := Degree(H);
    if d eq -1 then
      return Integers()!(Evaluate(HilbertSeries(I1),1));
    else
      return Integers()!(LeadingCoefficient(H)*Factorial(d));
    end if;
end intrinsic;

intrinsic IsNode(X::Sch,p::Pt) -> BoolElt
  {True iff p is an ordinary double point singularity on X.}
    bool,p := (p in X);
    require bool: "Argument 2 must be a point on argument 1.";

    // localise to affine patch
    if IsProjective(X) then
      X,p := AffinePatch(X,p);
    end if;
    // move p to the origin
    if &or[e ne 0 : e in Eltseq(p)] then
	L := Ring(Parent(p));
	if not(L cmpeq BaseRing(X)) then
	  X := BaseChange(X,L); p := X!Eltseq(p);
	end if;
	/*phi := Translation(X,p);
	X := phi(X);*/
	trans := [R.i+e[i] :i in [1..Length(X)]] where R is 
	  CoordinateRing(Ambient(X)) where e is Eltseq(p);
	X := Scheme(Ambient(X),[Evaluate(f,trans) : f in DefiningPolynomials(X)]);
	p := X![0 : i in [1..Length(X)]]; 
    end if;
    if IsNonsingular(X,p) then return false; end if;
    T := TangentCone(X,p);
    eqns := DefiningPolynomials(T);
    if not IsReduced(T) then return false; end if;
    if #eqns eq 1 then return TotalDegree(eqns[1]) eq 2; end if;
    //R := PolynomialRing(BaseRing(X),Length(X),"grevlex");
    //inits := [LeadingTerm(R!g) : g in eqns]; 
	// assumed that T gen by a GB for local order!
    //H := HilbertPolynomial(ideal<R|inits>);
    //d := Degree(H);
    return Multiplicity(T,T!Eltseq(p)) eq 2;
end intrinsic;

intrinsic IsNode(p::Pt) -> BoolElt
  {True iff p is an ordinary double point singularity on the scheme of p.}
    return IsNode(Scheme(Parent(p)),p);
end intrinsic;

intrinsic Multiplicity(p::Pt) -> RngIntElt
    {The multiplicity of p as a point of its parent scheme.}
    return Multiplicity(Scheme(Parent(p)),p);
end intrinsic;

intrinsic IsOrdinarySingularity(X::Sch,p::Pt) -> BoolElt
    {True iff the tangent cone to X at p is reduced.}
    return IsSingular(X,p) and IsReduced(TangentCone(X,p));
end intrinsic;

intrinsic IsOrdinarySingularity(p::Pt) -> BoolElt
    {True iff the tangent cone to the scheme of p at p is reduced.}
    return IsSingular(p) and IsReduced(TangentCone(Scheme(Parent(p)),p));
end intrinsic;

intrinsic SingularSubscheme(X::Sch : FullCheck := false) -> Sch
{ The non-smooth locus of X as an scheme embedded in the same ambient space as X.
  If FullCheck is false (the default), it is assumed that X is equidimensional.
  Otherwise the potentially expensive decomposition into equidimensional components
  has to be performed. }
    if not assigned X`SingularSubscheme then
	// mch - 06/10 - add a check for the 'bad' subscheme B of
        // toric ambients on which JacobianSubrankScheme may
	// give the wrong answer. If B intersects X non-trivially,
	// return an error.
	A := Ambient(X);
	typ := ambient_type(A);
	if (typ eq 2) or ((typ eq 1) and not IsEmpty(X meet
				Scheme(A,bad_subscheme_equations(A)))) then
	    error "Sorry, can't currently guarantee correct (non-)singularity\ncheck",
		"on part of this scheme (ambient toric singularity problem)";
	end if;
	if not FullCheck then 
	    X`SingularSubscheme := JacobianSubrankScheme(X);
	else
	    Saturate(~X);
	    IX := Ideal(X);
	    E := EquidimensionalDecomposition(IX);
	    if #E gt 1 then
		Xequis := [Scheme(Ambient(X),J : Saturated := true) : J in E];
		// add all intersections of components
		Z1 := &join[Xequis[i] meet Xequis[j] : j in [i+1..#Xequis], i in [1..#Xequis]];
		Z2 := &join[JacobianSubrankScheme(Y) : Y in Xequis];
		Z := Z1 join Z2;
		Saturate(~Z);
		X`SingularSubscheme := Scheme(X,Ideal(Z));
	    else
		X`SingularSubscheme := JacobianSubrankScheme(X);
	    end if;
	end if;
    end if;
    return X`SingularSubscheme;
end intrinsic;

intrinsic SingularPoints(X::Sch,K::Rng) -> SetIndx
    {A sequence of the singular points of X defined over K,
    assuming that the singular locus is zero dimensional.}
    Z := SingularSubscheme(X);
    require IsEmpty(Z) or IsCluster(Z) :
        "Singular locus of argument is not zero dimensional";
    return {@ X(K) ! p : p in RationalPoints(Z,K) @};
end intrinsic;
 
intrinsic SingularPoints(X::Sch) -> SetIndx
    {A sequence of the singular points of X defined over the base 
    ring of X, assuming that the singular locus is zero dimensional.}
    Z := SingularSubscheme(X);
    require IsEmpty(Z) or IsCluster(Z) :
        "Singular locus of argument is not zero dimensional";
    return {@ X(BaseRing(X)) ! p : p in RationalPoints(Z) @};
end intrinsic;
 
intrinsic SingularPointsOverSplittingField(X::Sch) -> SetIndx
    {A sequence of the singular points of X defined over the base
    ring of X, assuming that the singular locus is zero dimensional.}
    Z := SingularSubscheme(X);
    require IsEmpty(Z) or IsCluster(Z) :
        "Singular locus of argument is not zero dimensional";
    Sings,K := PointsOverSplittingField(Z);
    return {@ X(K) ! p : p in Sings @};
end intrinsic;
 
intrinsic HasSingularPointsOverExtension(X::Sch) -> BoolElt
    {False iff all the singularities of X are defined over
    its current base field.}
    require HasGroebnerBasis(X):
        "Groebner basis methods required but unavailable";
    require IsReduced(X): "Argument is not reduced.";
    return HasPointsOverExtension(SingularSubscheme(X));
end intrinsic;

