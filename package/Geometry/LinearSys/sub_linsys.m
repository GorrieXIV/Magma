freeze;

///////////////////////////////////////////////////////////////////////
// sub_linsys.m
///////////////////////////////////////////////////////////////////////

intrinsic Pullback(f::MapSch,L::LinearSys) -> LinearSys,Map
{The pullback of L by f. The second return value is a comparison
map from the coefficient space of L to that of the pullback system}
    require Ambient(L) eq Codomain(f):
	"Arguments defined on different ambient spaces";
    // create the pullback linear system
    L1 := LinearSystem(P1,F1)
	where F1 is [ CoordinateRing(P1) | p@@f : p in Sections(L) ]
	where P1 is Ambient(Domain(f));
    // calculate the comparison map VL -> RL -> R1 -> V1
    vs_hom := hom< VL -> V1 | images >
	where images is
	    [ CoefficientMap(L1)(PolynomialMap(L)(v) @@ f) : v in Basis(VL) ]
	where VL is CoefficientSpace(L)
	where V1 is CoefficientSpace(L1);
    return L1,vs_hom;
end intrinsic;


///////////////////////////////////////////////////////////////////////

forward monomial_sequence;
forward linear_setup;
intrinsic LinearSystem(L::LinearSys,f::MapSch,i::RngIntElt,m::RngIntElt)
		-> LinearSys
{The subsystem of L for which the pullback by f contains the i-th coordinate
hyperplane to multiplicity m}
    // retrieve data from L
    P := Ambient(L);
    require P eq Codomain(f):
	"Arguments defined on different ambient spaces";
    k := BaseField(P);
    VL := CoefficientSpace(L);
    basis := Basis(VL);
    FL := Sections(L);
    // find the pulled back sections of L by f
    F1 := [ s@@f : s in FL ];
    // calculate the conditions imposed by m over the next paragraphs:
    // i reduce it to a monomial calculation by taking the space of all
    // monomials that appear among the sections of F1.
    // determine a vector space corresponding to monomials that appear in F1
    mseq := monomial_sequence(F1);
    // warning: linear_setup can't handle empty sequences
    V1,pmap,cmap := linear_setup(mseq);
    images := [ cmap(PolynomialMap(L)(v)@@f) : v in basis ];
    phi := hom< VL -> V1 | images >;
    // find the target subspace and make the map to the quotient
    divseq := [];
    for mo in mseq do
	if IsDivisibleBy(mo,P.i^m) then
	    Append(~divseq,mo);
	end if;
    end for;
    good_vecs := [ cmap(mo) : mo in divseq ];
    good_vs := sub< V1 | good_vecs >;
    // impose the conditions
    // the system i want is the kernel of VL -> V1 -> V1/good_vs
    V2,p12 := quo< V1 | good_vs >;
    im := [ p12(phi(v)) : v in basis ];
    vs_hom := hom< VL -> V2 | im >;
    Vker := Kernel(vs_hom);
    // make the restricted linear system from its coefficient space
    return LinearSystem(L,Vker);
end intrinsic;

/*
intrinsic Subsystem(L::LinSys,p::Pt,C::Crv) -> LinSys
{The subsystem of L of projective plane curves tangent to C at p}
    // retrieve data from L
    P := Ambient(L);
    require P eq Ambient(C):
	"Arguments defined on different ambient spaces";
    require P eq Ambient(Scheme(p)):
	"Arguments defined on different ambient spaces";
    require IsNonsingular(C,p):
	"Third argument must be nonsingular at second to define a tangent direction";
    // first restrict L to curves through p
    L1 := Subsystem(L,p);
    if Multiplicity(L1,p) ge 2 then
	return L1;
    end if;
    // make a blowup at p and restrict
    cp := Coordinates(p);
    f1 := DefiningPolynomial(TangentLine(C,p));
    x := P.1; y := P.2; z := P.3;
    a:=Coefficient(f1,x,1); b:=Coefficient(f1,y,1); c:=Coefficient(f1,z,1);
				// so TpC : ax + by + cz = 0; N.B. f1(p) == 0
    if cp[3] ne 0 then		// p == (cp[1]:cp[2]:cp[3])
        if a ne 0 then
	    phi := RationalMap(P,P,[x*y + cp[1]*z^2,y*z + cp[2]*z^2,cp[3]*z^2]);
	    p2 := P ! [b,0,-a];
	else
	    phi := RationalMap(P,P,[x*z + cp[1]*z^2,x*y + cp[2]*z^2,cp[3]*z^2]);
	    p2 := P ! [0,0,1];
	end if;
    elif cp[2] ne 0 then	// p == (cp[1]:cp[2]:0)
        if a ne 0 then
	    phi := RationalMap(P,P,[x*y + cp[1]*z^2, cp[2]*z^2, y*z]);
	    p2 := P ! [c,0,-a];
	else
	    phi := RationalMap(P,P,[x*z + cp[1]*z^2, cp[2]*z^2, x*y]);
	    p2 := P ! [0,0,1];
	end if;
    else			// p == (cp[1]:0:0) and a == 0
	if b ne 0 then
	    phi := RationalMap(P,P,[cp[1]*z^2, x*y, y*z]);
	    p2 := P ! [c,0,-b];
	else
	    phi := RationalMap(P,P,[cp[1]*z^2, x*z, x*y]);
	    p2 := P ! [0,0,1];
	end if;
    end if;
    // pullback and restrict to the "infinitely near" point
    L2,pbmap := Pullback(phi,L1);
    L3 := Subsystem(L2,p2,2);		// mult 2 bcs excl curve has mult 1
    // interpret downstairs using the coefficient comparison map 'pbmap'
    V1 := CoefficientSpace(L1);
    V2 := CoefficientSpace(L2);
    V3 := CoefficientSpace(L3);
    Vtarg,quomap := quo< V2 | V3 >;
    basis := [ CoefficientMap(L1,b) : b in Sections(L1) ];
    ims := [ quomap(pbmap(b)) : b in basis ];
    bigpbmap := hom< V1 -> Vtarg | ims >;
    V := Kernel(bigpbmap);
    L4 := Subsystem(L1,V);
    return L4;
end intrinsic;
*/

///////////////////////////////////////////////////////////////////////
//		Functions
///////////////////////////////////////////////////////////////////////

monomial_sequence := function(F)
    /* determine a sequence of monomials that appear in the sections of F */
    monos := {};
    for f in F do
	mf := Monomials(f);
	for mo in mf do
	    Include(~monos,mo);
	    // ?? maybe I can choose an even smaller space of monomials here
	end for;
    end for;
    mseq := SetToSequence(monos);
    return mseq;
end function;

linear_setup := function(mseq)
    /* Given a nonempty sequence of distinct MONOMIALS of the same homogeneous
     * degree this returns the vector space of coefficients of the linear
     * system they span together with a map from coefficients to polynomials
     * and its inverse. For notation think of
     * 		mseq = [m1,m2,...,mr].					*/
    nm := #mseq;
    R := Universe(mseq);
    k := CoefficientRing(R);
    V := VectorSpace(k,nm);
    pmap := function(vec)
	/* given vec = (a1,...,ar) return a1*m1 + ... + ar*mr */
	poly := R ! 0;
	for i in [1..nm] do
	    poly +:= vec[i]*mseq[i];
	end for;
	return poly;
    end function;
    cmap := function(poly)
	/* given a polynomial (intended to be in the space of mseq, but not
	 * necessarily) return the vector of coefficients of mseq monomials. */
	coeffs := [];
	for i in [1..nm] do
	    mono := mseq[i];
	    co := MonomialCoefficient(poly,mono);
	    Append(~coeffs,co);
	end for;
	vec := V ! coeffs;
	return vec;
    end function;
    return V,pmap,cmap;
end function;

//multdata := function(L,P,m)
//    /* this routine calculates the generating equations and the coefficient
//     * space of polynomials vanishing with multiplicity m at P  */
//    /* L is assumed to be a previously defined linear system */
//    /* recover data about L */
//    d := Degree(L);
//    PP := Ambient(L);
//    k := BaseRing(PP);
//    R := CoordinateRing(PP);
//    nr := Rank(R);
//    WL := CoefficientSpace(L);
//    /* recover data about the complete linear system containing L */
//    LL := CompleteLinearSystem(L);
//    F := Sections(LL);
//    V := CoefficientSpace(LL);
// 
//    /* calculate the functions that will be required to vanish at P */
//    funs := F;
//    for i in [1..m-1] do
//        funs cat:= AllDerivatives(F,i);
//    end for;
//    nr := #F;
//    nc := Integers()!(#funs/nr);
// 
//    /* solve the linear equations determined by vanishing at the points of S */
//    mxentries := [ k | ];
//    p := Coordinates(P);
//    for m in funs do
//        val := Evaluate(m,p);
//        Append(~mxentries,val);
//    end for;
//    /* i transpose the matrix below bcs magma acts with them on the right */
//    M := Transpose(Matrix(nr,mxentries));
//    zero := VectorSpace(k,nc) ! [ k | 0 : i in [1..nc] ];
//    _,W := Solution(M,zero);
//    L1 := Subsystem(LL,W);
//    L2 := L meet L1;
//    W2 := CoefficientSpace(L2);
//    eqns := Sections(L2);
//    return eqns,W2;
//end function;
//
