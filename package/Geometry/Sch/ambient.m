freeze;

///////////////////////////////////////////////////////////////////////
// ambient.m
//	products
//	things at infinity
//	nice affine patches and affine decomposition
// April 2001 GDB
//
// October 2002 Nils Bruin
//   - changes to HyperplaneAtInfinity, LineAtInfinity.
//   really weird closure maps installed with MakeProjectiveClosureMap
//   will not work.
//
// August 2014 mch
//  added WeightedAffinePatch intrinsic to compute the affine patch
//  of any index as an affine scheme (generally with non-trivial
//  relations) along with the projective closure map.
///////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////

intrinsic NumberOfCoordinates(X::Sch) -> RngIntElt
    {The number of coordinates of a point of X.}
    return Length(X);
end intrinsic;

///////////////////////////////////////////////////////////////////////

intrinsic DirectProduct(A::Sch,B::Sch) -> Sch,SeqEnum
{The product of the ambient spaces of A and B together with the two projection
maps}
    require IsAmbient(A) and IsAmbient(B) : 
	    "Arguments must be ambient spaces";
    k := BaseRing(A);
    require BaseRing(B) cmpeq k:
        "Arguments must be defined over the same base ring";
    if (IsAffine(A) or IsOrdinaryProjective(A)) and
	   (IsAffine(B) or IsOrdinaryProjective(B)) then
        dA := Length(A);	// dimension if affine, dimension+1 if projective.
        dB := Length(B);
        if IsAffine(A) and IsAffine(B) then
        P := AffineSpace(k,dA + dB);
        elif IsAffine(A) then
        assert IsOrdinaryProjective(B);
        P := ProjectiveSpace(k,[ 0 : i in [1..dA]] cat [ 1 : i in [1..dB]]);
        elif IsAffine(B) then
        P := ProjectiveSpace(k,[ 1 : i in [1..dA]] cat [ 0 : i in [1..dB]]);
        else 
        P := ProductProjectiveSpace(k,[dA-1,dB-1]);
        end if;
        fPA := map< P -> A | [P.j : j in [1..dA] ] >;
        fPB := map< P -> B | [P.j : j in [dA+1..dA+dB] ] >;
        // Assign the products
        C:=CoxRing(P);
        C`summands:=[PowerStructure(TorVar) | A,B];
        // Return the data
        return P,[fPA,fPB];
    else
        // We can do more in the toric case
        require ISA(Type(A),TorVar) and ISA(Type(B),TorVar):
            "Arguments must be toric varieties";
        require IsField(BaseRing(A)): "The base ring must be a field";
        P,projs:=DirectProduct([PowerStructure(TorVar) | A,B]);
        return P,projs;
    end if;
end intrinsic;

intrinsic DirectProduct(k::Rng,N::SeqEnum) -> Sch,SeqEnum
{The product of projective spaces whose dimensions are the entries of N}
    require &and[ n gt 0 : n in N ]:
	    "The second argument must comprise strictly positive integers";
    return ProductProjectiveSpace(k,N);
end intrinsic;

intrinsic HyperplaneAtInfinity(X::Sch) -> Sch
{The hyperplane at infinity as a subscheme of the projective closure of X}
    require Type(X) eq Aff:
        "Only know about hyperplanes at infinity for affine spaces";

    PX := ProjectiveClosure(X);
    require #Gradings(PX) eq 1:
        "Projective closure is not a projective space";

    assert exists(ind){i:i in [1..#l]|l[i] eq 1} where
               l:=DefiningEquations(ProjectiveClosureMap(X));

    return Scheme(PX,PX.ind);
end intrinsic;
 
intrinsic LineAtInfinity(A::Aff) -> Crv
{The line at infinity as a curve in the projective closure of A}
    require Dimension(A) eq 2:
        "The argument must be an affine plane";
    P := ProjectiveClosure(A);
    require #Gradings(P) eq 1:
        "Projective closure is not a projective plane";

    assert exists(ind){i:i in [1..#l]|l[i] eq 1} where
               l:=DefiningEquations(ProjectiveClosureMap(A));

    return Curve(P,P.ind);
end intrinsic;

intrinsic NumberOfAffinePatches(S::Sch) -> RngIntElt
{The number of standard affine patches of S, returning 0 for an affine scheme}
    A := Ambient(S);
    if Type(A) eq Aff then
        return 0;
    else
	return &*Lengths(A);
    end if;
end intrinsic;

intrinsic AffineDecomposition(P::Prj) -> SeqEnum,Pt
{A sequence of maps from affine spaces whose images partition P together
with the returned point}
    require IsOrdinaryProjective(P):
        "Argument must be ordinary projective space";
    n := Dimension(P);
    k := BaseRing(P);
    spaces := [ AffinePatch(P,1) ] cat
		[ AffineSpace(k,i) : i in [n-1..1 by -1] ];
    maps := [ PCMap(spaces[1]) ];
    for i in [2..n] do
        Ai := spaces[i];
        one := CoordinateRing(Ai) ! 1;
        zero := CoordinateRing(Ai) ! 0;
        m := map<Ai -> P | Fi > where Fi is
	    [ Ai.j : j in [1..n+1-i]] cat [one] cat [zero: j in [1..i-1]];
	maps := maps cat [m];
    end for;
    pt := P ! ([ k!1 ] cat [ 0 : i in [1..n]]);
    return maps,pt;
end intrinsic;

intrinsic CentredAffinePatch(C::Sch,p::Pt) -> Sch,MapSch
{An affine patch of C centred at the point p and the embedding into C}
    require IsProjective(C): "First argument must be projective";
    require p in C(BaseRing(C)):
	"Second argument must be rational point on the first";
    iscurve := ISA(Type(C),Crv);
    Ci,q := AffinePatch(C,p);
    Ai := Ambient(Ci);
    fi := ProjectiveClosureMap(Ai);
    if q eq Origin(Ai) then
        return Ci,fi;
    end if;
    phi := Translation(Ci,q);
    D := Ci @ phi;
    prechart := Inverse(phi) * fi;
    // create a new affine space to enable the correct projective closure map.
    // note that this is a _different_ space from Ai even though they have the
    // same coordinate ring. in particular, they will have different projective
    // closure maps.
    Ri := CoordinateRing(Ai);
    Ap := AffineSpace(Ri);
    // reconstruct the new curve/scheme in Ai
    if iscurve then
	Cp := Curve(Ap,Polynomial(D));
    elif Type(C) eq Prj then
        Cp := Ap;
    else
	Cp := Scheme(Ap,DefiningIdeal(D));
    end if;
    // fix up the domain of the chart
    id := map< Ap -> Ai | [Ap.i: i in [1..Length(Ap)] ]>;
    chart := id * prechart;
    MakeProjectiveClosureMap(Ap,Ambient(C),DefiningPolynomials(chart));
    return Cp,chart;
end intrinsic;

/////////// mch 08/14 - weighted affine patch functions /////////////////////////

function recurse_prime_to_r(seq,r)
// Given seq=[m1,..,mn] of numbers mod r s.t. GCD(m1,..,mn,r)=1,
// find a sequence seq1=[s1,..,sn] of small non-neg integers s.t.
// GCD(s1*m1+..+sn*mn,r)=1.

    if #seq eq 1 then return [1]; end if;
    gcds := [GCD(m,r) : m in seq];
    i := Index(gcds,1);
    if i gt 0 then
      res := [0 : j in [0..#seq]]; res[i] := 1;
      return res;
    end if;
    r1,i := Max(gcds);
    res := recurse_prime_to_r([seq[j] mod r1 : j in [1..#seq] | j ne i],
		r1);
    Insert(~res,i,1);
    s := &+[res[j]*seq[j] : j in [1..#seq]];
    while GCD(s,r) gt 1 do
      res[i] := res[i]+1;
      s := s+seq[i];
    end while;
    return res;

end function;

function minimal_good_subsets(S,bad_sets)
// Compute the set of subsets of set S which are minimal
// with respect to not being a subset of one of bad_sets.
// bad_sets should be a set of non-empty proper subsets of S.

    // Method isn't especially efficient but this function
    // should only be called for fairly small S.
    known_min := [];
    curr := [S];

    while #curr gt 0 do
      T := curr[1]; Remove(~curr,1);
      subs := [s : s in Subsets(T,#T-1) | &and[s notsubset t : t in bad_sets]];
      if #subs eq 0 then 
	Append(~known_min,T);
      else
	subs := [s : s in subs | &and[s ne t : t in curr]];
	curr cat:= subs;
      end if;
    end while;

    return known_min;

end function;

function wp_inv_eqns(A,B,i1,wts)
// Compute a full(ish) set of equations for the inclusion map of the ith affine
// patch A into weighted-projective space P with weights wts. i1=n+1-i
// (n=#wts) is the index of the P variable x for which A=P(x != 0).
// B is the sequence giving the monomials in the remaining P variables
// to which the A variables correspond. Any P-monomial in these remaining
// vars whose total weight (for the P-grading) is a multiple of the weight
// of wt(x), is a product of the 'generating' monomials in B.

    r := wts[i1]; // P-weight of the x variable - r >= 2 here
    n := #wts;
    n1 := #B;
    other_wts := Remove(wts,i1);
    R := Generic(Universe(B));
    Ra := CoordinateRing(Ambient(A));
    // First find the Ra.j that <-> smallest powers of the
    // R variables whose weight is divisible by r (these smallest
    // pure powers must occur in B).
    min_pow_exps := [r div GCD(w,r) : w in other_wts];
    min_pows := [Ra.Index(B,(R.j)^min_pow_exps[j]) : j in [1..n-1]];

    // For each P-variable xj of weight wj with (wj,r)=1, can
    // find equations for f:A->P that give a defined map on f^-1(xj !=0).
    // We first compute these sets of mapping equations. Further
    // alternative equations involve some extra work.
    inv_eqns := [];
    good_is := [j : j in [1..n-1] | GCD(other_wts[j],r) eq 1];
    bad_is := [j : j in [1..n-1] | j notin good_is];

    for j in good_is do
      // 1+mj*wj=0 mod r, where wj=wts[j]
      _,m,_ := XGCD(other_wts[j],r);
      mj := (-m) mod r;
      //The inverse map eqns <-> j will have xk*xj^(mj*wk) in the
      //kth position, k != i1 and xj^(mj*r) in the i1-th. With a
      //monomial m(xk) in the xk of weight d*r representing the rational
      //function  m(Xk)/(X_i1)^d on P, a simple comp shows that
      //this correctly gives the inverse map when the  xk*xj^(mj*wk)
      //are written as monomials in the Ra variables, and that
      //this map is defined on the open subset of A where Ra.s != 0
      //where Ra.s is the smallest xj^t power: this open subset
      //of A corresponds exactly to the open subset of P where
      //P.i1 != 0 AND P.j != 0.
      seq := [];
      for k in [1..n-1] do
	if k ne j then
	  vk,uk := Quotrem(mj*other_wts[k],r);
	  ind := Index(B,(R.k)*(R.j)^uk);
	  assert ind gt 0; //xk*xj^uk must lie in B
	  Append(~seq,(Ra.ind)*(min_pows[j])^vk);
	else
	  vk := (1+mj*other_wts[j]) div r;
	  Append(~seq,(min_pows[j])^vk);
	end if;
      end for;
      Insert(~seq,i1,(min_pows[j])^mj);
      Append(~inv_eqns,seq);
    end for;
     
    // Try to find more alternative eqns related to the bad_is.
    // Indices j s.t. r|wts[j]^infty are of no use so we discard
    // these first.
    ps := [f[1] : f in Factorisation(r)]; r0 := &*ps;
    bad_is := [j : j in bad_is | not IsDivisibleBy(other_wts[j],r0)];
    if #bad_is eq 0 then return inv_eqns; end if;

    // First, try to divide {i : i in bad_is} into minimal (non-disjoint) subsets
    // S s.t. GCD([wts[i] : i in S]) is relatively prime to r.
    // No such subset may exist but, if there are none, good_is must have been
    // non-empty (so we already have some inv_eqns) because GCD(wts)=1    
    bad_wts := [other_wts[j] : j in bad_is];
    if GCD(bad_wts cat [r]) ne 1 then
      assert #good_is gt 0;
      return inv_eqns;
    end if;
    pmat := Matrix([[Valuation(w,p) : w in bad_wts] : p in ps]);
    bad_sets := [{bad_is[j] : j in [1..#rs] | rs[j] gt 0} : rs in RowSequence(pmat)];
    bad_sets := [s : s in bad_sets | #s gt 0];

    i_sets := minimal_good_subsets(Seqset(bad_is),bad_sets);

    //i_sets := [bad_is];

    //For each set {j1,..,jr} in i_sets, find a monomial m=x_{j1}^s1..x_{jr}^sr
    //for small positive si with GCD(wt(m),r)=1
    mons := [];
    for jset in i_sets do
      js := Setseq(jset);
      vec := [0 : j in [1..n-1]];
      vec1 := recurse_prime_to_r([other_wts[j] mod r : j in js],r);
      for j in [1..#js] do vec[js[j]] := vec1[j]; end for;
      Append(~mons,[*vec,&+[other_wts[js[j]]*vec1[j] : j in [1..#js]]*]);
    end for;

    // Finally, for each m=x_{j1}^s1..x_{jr}^sr in mons, compute equations
    // for A->P which are defined on the open subset of A corresponding to
    // the open subset x_{j1} != 0,x_{j2} != 0,...,x_{i1} !=0 of P. Use
    // the same method as for the good_is - a bit more work to find Ra monomials.
    // 
    // Will use LP optimisation code to find POSITIVE integer vector solutions
    // to v*(integer matrix)=integer vector. Slight overkill, but the
    // problems should be easy. Set up arguments for MinimalSolution calls.
    cmat := VerticalJoin(IdentityMatrix(Integers(),n1),
	Transpose(Matrix([Exponents(b) : b in B])));
    rmat := Matrix(n1+n-1,1,[1 : j in [1..n1]] cat [0 :j in [1..n-1]]);
    obj :=  Matrix(1,n1,[1 : j in [1..n1]]);
    vec := [0 : j in [1..n1]];
     // Will append vector of target exponents to vec to give the rhs
     // 1-column matrix in MinimalSolution calls.
    for m in mons do
      em := m[1]; wm := m[2];
      // 1+mm*wm=0 mod r
      _,e,_ := XGCD(wm,r);
      mm := (-e) mod r;
      em := [mm*e : e in em];
      seq := [];
      for j in [1..n-1] do
        vec1 := [other_wts[j]*e : e in em];
        vec1[j] +:= 1;
        sol,ok := MinimalIntegerSolution(cmat,rmat,Matrix(n1+n-1,1,
		 vec cat vec1),obj);
        assert ok eq 0;
	Append(~seq,Monomial(Ra,Eltseq(sol)));
      end for;
      vec1 := [r*e : e in em];
      sol,ok := MinimalIntegerSolution(cmat,rmat,Matrix(n1+n-1,1,
		 vec cat vec1),obj);
      assert ok eq 0;
      Insert(~seq,i1,Monomial(Ra,Eltseq(sol)));
      Append(~inv_eqns,seq);
    end for;

    return inv_eqns;
 
end function;

intrinsic WeightedAffinePatch(P::Prj, i::RngIntElt) -> Sch,MapIsoSch
{ P is weighted projective space with positive integral weights. Constructs
  the ith affine patch as an affine scheme A and returns this along with the
  (invertible) projective closure map f: A -> P. This will be a 'standard'
  Magma affine patch if and only if the weight for the (Rank(P)-i)th variable
  is 1. NB: f will be defined by several sets of alternative equations
  but these will still not define f on all of A except in the weight 1 case.}

    require IsProjective(P) and (NumberOfQuotientGradings(P) eq 0) and
	(NumberOfGradings(P) eq 1) and &and[d gt 0 : d in Gradings(P)[1]]:
      "First argument should be weighted projective space with a single positive integral grading";
    require (i gt 0) and (i le Rank(CoordinateRing(P))):
      "Second argument should be a positive integer <=",IntegerToString(Rank(CoordinateRing(P)));

    wgts := Gradings(P)[1];
    R := CoordinateRing(P);
    n := #wgts;
    i1 := n+1-i;
    r := wgts[i1];
    if r eq 1 then
      return A,ProjectiveClosureMap(A) where
	A is AffinePatch(P,i);
    end if;
    g := GCD(wgts);
    if g gt 1 then
	wgts := [w div g : w in wgts]; r := r div g;
    end if;
    if r eq 1 then 
     // wgts[i]!=1 but divides all other weights - essentially the same as r=1.
     A := AffineSpace(BaseRing(P),n-1);
     pcm := iso<A->P| Insert([A.j : j in [1..n-1]],i1,1), 
		[(P.j)/((P.i1)^wgts[j]): j in [1..n] | j ne i1] : Check := false>;
     return A,pcm;
    end if;

    // Get a minimal set of generators B for monomials in the P-variables P.j
    // j != n+1-i, whose weight is divisible by r.
    // Since this whole computation is universal, only depending on the weights
    // and not the ground field of P, we work over Q.
    // Should compute B directly but, for convenience here, we extend to Q(z) where
    // z^r=1 and use the Invariant theory code for the appropriate action of
    // Z/rZ on the coordinates. However, the invt-thy code is VERY SLOW to compute
    // the (binomial) ideal of relations between the monomials in B, so we do 
    // perform that computation directly. We work over Q because the linear algebra
    // and later Groebner basis computations are highly-tuned over the rationals!

    K := CyclotomicField(r); z := K.1;
    G := sub<GL(n-1,K) | DiagonalMatrix([z^(wgts[j]) : j in [1..n] | j ne i1])>;
    B := FundamentalInvariants(InvariantRing(G));
    assert &and[(#Terms(b) eq 1) and (LeadingCoefficient(b) eq 1) : b in B];
    Rtmp := PolynomialRing(Rationals(),n-1);
    B := [Monomial(Rtmp,Exponents(LeadingMonomial(b))) : b in B];

    // Now compute the ideal of relations between the monomials in B
    wgts1 := [((Vector(Exponents(b))*M)[1]) div r : b in B] where
	M is Matrix(n-1,1,Remove(wgts,i1));
    R1 := PolynomialRing(Rationals(),wgts1,"grevlexw",wgts1);
    n1 := #B;
    mat := Matrix([Exponents(b) : b in B]);
    B1 := [&*[(R1.j)^b[j] : j in [1..n1] | b[j] gt 0] -
	&*[(R1.j)^(-b[j]) : j in [1..n1] | b[j] lt 0] : b in Basis(Kernel(mat))];
 
    // B1 = set of monomial relations m1-m2 in the variables of R1 which give
    // zero when evaluated at B. The full R1-ideal of relations between the
    // monomials in B is the saturation of ideal<R1|B1>. It SHOULD
    // be more efficient to use polyhedral cone computations to compute the
    // integer lattice saturation in a rational cone based on Kernel(mat),
    // but it turns out in practise, it is much faster in Magma to actually do the
    // Groebner basis saturation and minimal basis computations.
    I := ideal<R1|B1>;
    for j in [1..n1] do I := ColonIdeal(I,R1.j); end for;
    B1 := MinimalBasis(I);

    // Convert back to the base-ring of P and compute the proj-closure map
    // We leave the natural grevlexw ordering, even though final result is
    // an affine variety. 
    Ra := PolynomialRing(BaseRing(P),wgts1,"grevlexw",wgts1);
    I := ideal<Ra|[Ra!b : b in B1]>;
    A := (#B1 eq 0) select Spec(Ra) else Scheme(Spec(Ra),I); //the patch
    toA := [Monomial(R,Eltseq(m[j]))/(R.i1^wgts1[j]) : j in [1..n1]]
	where m is HorizontalJoin(ColumnSubmatrix(mat,i1-1),
 	HorizontalJoin(ZeroMatrix(Integers(),n1,1), ColumnSubmatrixRange(mat,i1,n-1)));
    // toA gives eqns for P->A. Inverse defining eqns are a little fiddlier to
    // determine.
    toP := wp_inv_eqns(A,B,i1,wgts); 
    return A, iso<A->P|toP,toA : Check := false>;

end intrinsic;
