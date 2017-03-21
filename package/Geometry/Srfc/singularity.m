freeze;

///////////////////////////////////////////////////////////////////
//     Intrinsics for computing various 'singularity'  		 //
//  properties [only_simple_singularities, (arithmetically)	 //
//   Gorenstein, (arithemtically) Cohen-Macaualay, normal]	 //
//  for surfaces/more general schemes				 //
//             mch - 10/2012                                     //
///////////////////////////////////////////////////////////////////

import "../Sch/norm_form_of_sing.m": trunc_comp,complete_squares;

/////// Functions for checking and setting various singularity ////
/// attributes that may imply/be inferred from others /////////////

function is_known_arith_gor(X)
    if assigned X`arith_gor then
	return true,X`arith_gor;
    else
	return false,_;
    end if;
end function;

function is_known_ACM(X)
    if (assigned X`arith_gor) and X`arith_gor then
	return true,true;
    elif assigned X`ACM then
	return true,X`ACM;
    else
	return false,_;
    end if;
end function;

function is_known_oss(X)
    if (assigned X`Nonsingular) and X`Nonsingular then 
	return true,true;
    elif ISA(Type(X),Srfc) and (assigned X`only_simple_sings) then
	return true,X`only_simple_sings;
    else
	return false,_;
    end if;
end function;

function is_known_gor(X)
    boo,boo1 := is_known_oss(X);
    if boo and boo1 then return true,true; end if;
    if (assigned X`arith_gor) and X`arith_gor then
	return true,true;
    elif assigned X`gor then
	return true,X`gor;
    else
	return false,_;
    end if;
end function;

function is_known_CM(X)
    boo,boo1 := is_known_gor(X);
    if boo and boo1 then return true,true; end if;    
    if (assigned X`ACM) and X`ACM then
	return true,true;
    elif assigned X`CM then
	return true,X`CM;
    else
	return false,_;
    end if;
end function;

function is_known_normal(X)
    boo,boo1 := is_known_oss(X);
    if boo and boo1 then return true,true; end if;
    if assigned X`normal then
	return true,X`normal;
    else
	return false,_;
    end if;
end function;

forward set_oss, set_ACM, set_gor, set_arith_gor, set_non_sing;
 
procedure set_normal(~X,boo)
    if not (assigned X`normal) then
      X`normal := boo;
    end if;
    if not boo then
	if ISA(Type(X),Srfc) then
	  set_oss(~X,false);
	else
	  if not (assigned X`Nonsingular) then
	    X`Nonsingular := boo;
	  end if;
	end if;
    end if;
end procedure;

procedure set_CM(~X,boo)
    if not (assigned X`CM) then
      X`CM := boo;
    end if;
    if not boo then
	set_ACM(~X,false);
	set_gor(~X,false);
    end if;
end procedure;

procedure set_gor(~X,boo)
    if not (assigned X`gor) then
      X`gor := boo;
    end if;
    if boo then
	set_CM(~X,true);
    else
      if ISA(Type(X),Srfc) then
	set_oss(~X,false);
      else
	if not (assigned X`Nonsingular) then
	  X`Nonsingular := boo;
	end if;
      end if;
    end if;
end procedure;

procedure set_oss(~X,boo)
    if not (assigned X`only_simple_sings) then
      X`only_simple_sings := boo;
    end if;
    if boo then
	set_gor(~X,true);
	set_normal(~X,true);
    else
	set_non_sing(~X,false);
    end if;
end procedure;

procedure set_ACM(~X,boo)
    if not (assigned X`ACM) then
      X`ACM := boo;
    end if;
    if boo then
	set_CM(~X,true);
    else
	set_arith_gor(~X,false);
    end if;
end procedure;

procedure set_arith_gor(~X,boo)
    if not (assigned X`arith_gor) then
      X`arith_gor := boo;
    end if;
    if boo then
	set_gor(~X,true);
	set_ACM(~X,true);
    end if;
end procedure;

procedure set_non_sing(~X,boo)
    if not (assigned X`Nonsingular) then
      X`Nonsingular := boo;
    end if;
    if boo then
	set_oss(~X,true);
	if not (assigned X`simp_sings) then
	  X`simp_sings := [**];
	end if;
    end if;
end procedure;

////////// Gorenstein and CM functions ////////////////////////////

function SpecialHilbertSeries(F)
// The Hilbert Series of the graded free module F=R(r1)+..+R(rm)
    R := BaseRing(F);
    wts := ColumnWeights(F);
    P := RationalFunctionField(Integers()); t := P.1;
    if #wts eq 0 then return P!0; end if;
    wm := Min(wts); r := Rank(R);
    return ((t^wm)*&+[t^(w-wm) : w in wts])/((1-t)^r);
end function;

function CM_gor_fn(X,bgor)
// combined functionality for CM/gorenstein testing. bgor = true
//  if Gorensteinness being tested

    I := Ideal(X); //X already saturated
    d := Dimension(I);
    R := Generic(I);
    n := Rank(R);
    // special cases X=P^(n-1) or X empty
    if (d eq n) or (d eq 0) then
	set_arith_gor(~X,true);
	return true,_;
    end if;
    // special case dim(X) le 1
    if (d le 2) and (not bgor) then
	set_CM(~X,true);
	return true,_;
    end if;
    
    //IDEA: X is CM iff the projective coordinate ring R/I is a CM R module
    // except poss at the max ideal m. This is equiv to Ext^i(R/I,R) is a finite
    // R-module for i >= d+1 [ACM <=> Ext^i(R/I,R)=0 for i >= d+1]
    // As in the old version of IsLocallyFree, if
    // F0 -> F1 -> F2 -> .. -> Fr -> 0
    // is the dual of the min free (graded) R-res of R/I, with fi:F_(i-1)->Fi,
    // we need to check that 
    // HilbPoly(F_(i+1)) = HilbPoly(Fi/im(fi))+HilbPoly(F_(i+1)/im(f_(i+1)))
    // for n-d+1<=i<=r [F_(r+1) = 0]
    // For ACM we need r <= n-d (when r = n-d)

    res := MinimalFreeResolution(QuotientModule(I));
    r := #Terms(res)-3;
    if r le n-d then
      set_ACM(~X,true);
      return true,res;
    end if;
    // if not projectively normal, need to revert to saturated
    // structure sheaf.
    assert r le n; // I is saturated!
    if r eq n then // X not projectively normal
	OX := StructureSheaf(X);
	res := MinimalFreeResolution(FullModule(OX));
	r := #Terms(res)-3;
	assert r lt n;
    end if;

    boo := true; 
    hsd := RationalFunctionField(Integers())!0; hsi1 := hsd;
    for i in [n-d+1..r] do
	wtsi := [-w : w in ColumnWeights(Term(res,i))];
	fi := Transpose(Matrix(BoundaryMap(res,i)));
	hsi := HilbertSeries(quo<F|[F!r : r in RowSequence(fi)]>)
	    where F is RModule(R,wtsi);
	if (i gt n-d+1) and (i ne r) then
	    Fip := RModule(R,[-w : w in wtsi]);
	    hsd := hsi+hsi1-
		   SpecialHilbertSeries(Fip);
	    hsi1 := hsi;
	elif i eq r then
	    hsd := hsi;    
	end if;
	boo := (den eq (Parent(den).1)^Degree(den)) where 
		den is Denominator(hsd);
	if not boo then break; end if;
    end for;

    set_CM(~X,boo);
    return boo,res;
end function;

function arith_CM_gor_fn(X,bgor)
// combined functionality for arithmetical CM/gorenstein testing. bgor = true
//  if Gorensteinness being tested

    I := Ideal(X); //X already saturated
    d := Dimension(I);
    R := Generic(I);
    n := Rank(R);
    // special case X = P^(n-1) or X empty
    if (d eq n) or (d eq 0) then return true; end if;
    
    //X is arithmetically CM iff the projective coordinate ring R/I has a minimal
    // free resolution of length n-d (ie 0 -> F_(n-d) -> F_(n-d-1) -> F0 -> 0)
    // X is arith gor iff the above, F_(n-d) has rank 1 and the annihilator of
    // the (n-d)th homology group of the dual resolution has annihilator I

    res := MinimalFreeResolution(QuotientModule(I));
    r := #Terms(res)-3;
    if r gt n-d then
      return false;
    end if;
    if not bgor then return true; end if;
    assert r eq n-d;
    // Do extra Gorenstein test.
    if Rank(Term(res,r)) gt 1 then return false; end if;
    mat := Transpose(Matrix(BoundaryMap(res,r)));
    seq := Eltseq(mat);
    if &and[f in I : f in seq] then
      return true;
    else
      return false;
    end if;
end function;

intrinsic IsCohenMacaulay(X::Sch : CheckEqui := false) -> BoolElt
{ X is an equidimensional ordinary projective scheme. Returns whether X
  is (locally) Cohen-Macaulay. The equidimensionality is only checked if
  the CheckEqui intrinsic is set to true (default false)}

    require IsOrdinaryProjective(X): "Argument X should be ordinary projective";
    boo,boo1 := is_known_CM(X);
    if boo then set_CM(~X,boo1); return boo1; end if;
    Saturate(~X);
    I := Ideal(X);
    if CheckEqui then
	require EquidimensionalPart(I) subset I:
	  "Argument X is not equidimensional";
    end if;

    boo := CM_gor_fn(X,false);
    return boo;

end intrinsic;

intrinsic IsGorenstein(X::Sch : CheckEqui := false) -> BoolElt
{ X is an equidimensional ordinary projective scheme. Returns whether X
  is (locally) Gorenstein. The equidimensionality is only checked if
  the CheckEqui intrinsic is set to true (default false)}

    require IsOrdinaryProjective(X): "Argument X should be ordinary projective";
    boo,boo1 := is_known_gor(X);
    if boo then set_gor(~X,boo1); return boo1; end if;
    Saturate(~X);
    I := Ideal(X);
    if CheckEqui then
	require EquidimensionalPart(I) subset I:
	  "Argument X is not equidimensional";
    end if;

    boo,res := CM_gor_fn(X,true);
    if not boo then return false; end if;
    boo,boo1 := is_known_arith_gor(X);
    if boo and boo1 then //might be now known arith gor in trivial cases
	set_gor(~X,true); return true;
    end if;
    boo,boo1 := is_known_ACM(X);
    if boo and boo1 then
	r := Rank(I)-Dimension(I);
	assert #Terms(res) eq r+3;
	mat := Transpose(Matrix(BoundaryMap(res,r)));
	if Rank(Term(res,r)) eq 1 then
	   seq := Eltseq(mat);
	   if &and[f in I : f in seq] then
	     set_arith_gor(~X,true); return true;
	   else
	     set_gor(~X,false); return false;
	   end if;
	else
	  set_arith_gor(~X,false);
	end if;
	if assigned X`KX then
	  KX := X`KX;
	else
	  KX := Sheaf(quo<F|[F!r : r in RowSequence(mat)]>,X)
	   where F is RModule(Generic(I),[Rank(I)-w : w in ColumnWeights(Term(res,r))]);
	  KX`Mfull := KX`M;
	  X`KX := KX;
	end if;
    else
	KX := CanonicalSheaf(X);
    end if;

    boo,rk := IsLocallyFree(KX);
    boo := boo and (rk eq 1);
    set_gor(~X,boo);
    return boo;

end intrinsic;

intrinsic IsArithmeticallyCohenMacaulay(X::Sch : CheckEqui := false) -> BoolElt
{ X is an equidimensional ordinary projective scheme. Returns whether X
  is arithmetically Cohen-Macaulay. The equidimensionality is only checked if
  the CheckEqui intrinsic is set to true (default false)}

    require IsOrdinaryProjective(X): "Argument X should be ordinary projective";
    boo,boo1 := is_known_ACM(X);
    if boo then set_ACM(~X,boo1); return boo1; end if;
    Saturate(~X);
    I := Ideal(X);
    if CheckEqui then
	require EquidimensionalPart(I) subset I:
	  "Argument X is not equidimensional";
    end if;

    boo := arith_CM_gor_fn(X,false);
    set_ACM(~X,boo);
    return boo;

end intrinsic;

intrinsic IsArithmeticallyGorenstein(X::Sch : CheckEqui := false) -> BoolElt
{ X is an equidimensional ordinary projective scheme. Returns whether X
  is arithmetically Gorenstein. The equidimensionality is only checked if
  the CheckEqui intrinsic is set to true (default false)}

    require IsOrdinaryProjective(X): "Argument X should be ordinary projective";
    boo,boo1 := is_known_arith_gor(X);
    if boo then set_arith_gor(~X,boo1); return boo1; end if;
    Saturate(~X);
    I := Ideal(X);
    if CheckEqui then
	require EquidimensionalPart(I) subset I:
	  "Argument X is not equidimensional";
    end if;

    boo := arith_CM_gor_fn(X,true);
    set_arith_gor(~X,boo);
    return boo;

end intrinsic;

////////////// Surface normality functions ////////////////////////

function depth_ge_2(I)
  // I is an ideal (assumed prime) in R=k[x1,..,xn] contained in
  // m = (x1,x2,..,xn). Returns whether local ring (R/I)_m has
  // depth >=2

    R := Generic(I);
    n := Rank(R);
    // quotient by xi (xi notin I) and check whether the
    // quotient ring R1 has depth >= 1 by seeing if m
    // is a primary component or not
    i := 1;
    while i le n do
	if R.i notin I then break; end if;
	i +:= 1;
    end while;
    if i gt n then // I is m
	return false;
    end if;
    R1 := PolynomialRing(BaseRing(R),n-1);
    seq := [R1.j : j in [1..n-1]];
    Insert(~seq,i,R1!0);
    red_mp := hom<R->R1|seq>;
    I1 := ideal<R1|[red_mp(f) : f in Basis(I)]>;

    // now check whether I1 has m1 as an associated prime.
    // Number of ways to proceed. Do it by checking whether
    // Hom_R1(R1/m1,R1/I1) is the zero module or not.
    // Equiv. to whether (I1:m1) = I1 or (I1:m1^infty)=I1.
    // Is this the most efficient check??
//printf "starting Sat\n";
    I2 := Saturation(I1);
//printf "starting eq\n";
    boo := I2 subset I1;
    return boo; 
    
end function;

intrinsic IsNormal(X::Srfc) -> BoolElt
{ Returns whether surface X is a normal variety. }

    boo,boo1 := is_known_normal(X);
    if boo then
	return boo1;
    end if;

    XS := SingularSubscheme(X);
    if Dimension(XS) eq -1 then
      set_non_sing(~X,true);
    elif Dimension(XS) ge 1 then
      set_non_sing(~X,false);
      set_oss(~X,false);
      X`normal := false;
    else //singular subscheme of dimension 0
      set_non_sing(~X,false);
      if is_known_CM(X) then //CM+(dim sing subscheme = 0) => normal
	X`normal := true;
	return true;
      end if;
      pts,K := PointsOverSplittingField(XS);
      XK := BaseChange(X,K);
      boo := true;
      for p in pts do
	p1 := XK!Eltseq(p);
	if not IsAffine(X) then
	  X1,p1 := AffinePatch(XK,p1);
	else
	  X1 := XK;
	end if;
	// translate to origin
    	if &or[e ne 0 : e in Eltseq(p1)] then
	  tr := Translation(X1,p1);
	  I := ideal<CoordinateRing(Ambient(X1))|
		[Evaluate(f,idp) : f in DefiningPolynomials(X1)]> 
		 where idp is InverseDefiningPolynomials(tr);
	else
	  I := Ideal(X1); 
        end if;
	boo1 := depth_ge_2(I);
	if not boo1 then
	  boo := false;
	  break;
	end if;
      end for;
      X`normal := boo;
    end if;

    return X`normal;

end intrinsic;

///////// Analytical hypersurface singularity functions ////////////////////////

function expand_to_prec(F,d,subs,prec)
     //expansion func up to given precision prec
    n := Rank(Parent(F));
    trunc := func<f | (#T eq 0) select Parent(F)!0 else
	Polynomial([LeadingCoefficient(t) : t in T], [LeadingMonomial(t) : t in T])
	where T is [t : t in Terms(f) | LeadingTotalDegree(t) le prec]>;
    is_good := func<f | &and[&and[e eq 0 : e in es] where es
	is Exponents(t)[d+1..n] : t in Terms(f)]>;
    if not is_good(F) then 
      F := trunc(F);
      while not is_good(F) do
	F := Evaluate(F,subs);
	F := trunc(F);
      end while;
    end if;
    return F;
end function;

function trans_to_hyp(X,prec)
    // By translation and affine patches, assumed that X is affine and
    // the singular point p is the origin here.

    R := CoordinateRing(Ambient(X));
    k := BaseRing(R);
    n := Rank(R);
    T := TangentSpace(X,X![k|0 : i in [1..n]]);
    d := Dimension(X);
    dT := Dimension(T);
    assert dT ge d+1;
    //error if dT gt d+1, "Not isomorphic to a hypersurface singularity";
    if dT gt d+1 then return false,_,_,_,_,_; end if;
    eqns := DefiningPolynomials(T);
    if #eqns gt 0 then
      Tmat := Matrix([[MonomialCoefficient(f,R.i) : i in [1..n]] : 
                f in eqns]);
      Tmat := EchelonForm(Tmat);
      inds := [Min(Support(Tmat[i])) : i in [1..Nrows(Tmat)]];
    else // T is the whole ambient!
      inds := [];
    end if;
    i1 := [i : i in [1..n] | i notin inds];
    isub := inds cat i1;
    Reverse(~isub); // lglex & lgrevlex reverse the var orders!
    isubi := [Index(isub,j) : j in [1..n]];
    xsubi := [R.i : i in isub];
    xsub := [R.i : i in isubi];
    fsub := [Evaluate(f,xsub) : f in Basis(Ideal(X))];

    // get local Groebner basis
    Rl := LocalPolynomialRing(k,n,"lgrevlex");
    Il := ideal<Rl|[Evaluate(f,[Rl.i : i in [1..n]]) : f in fsub]>;
    LB := GroebnerBasis(Il);
    if #LB ne n-d then return false,_,_,_,_,_; end if;
    for i in [1..n-d-1] do 
        assert LeadingMonomial(LB[i]) eq Rl.(n+1-i);
    end for;
    rs := [R.i : i in [1..n]];
    if d eq n-1 then //X is locally a hypersurface at the origin
	F0 := Evaluate(LB[1],rs);
	return true,F0,F0,[R|],xsub,xsubi;
    end if;

    // do substitutions
    lsubs := [R.i : i in [1..d+1]] cat
	Reverse([Evaluate(LeadingTerm(f) - f,rs) : f in LB[1..n-d-1]]);
    F := LB[#LB];
    assert seq[#seq] le d+1 where 
	seq is [i : i in [1..n] | e[i] ne 0] where e is
	Exponents(LeadingTerm(F));
    F0 := Evaluate(F,rs);
    F := expand_to_prec(F0,d+1,lsubs,prec);
    return true,F,F0,lsubs[d+2..n],xsub,xsubi;

end function;

// data record for a hypersurface singularity p
HSSData := recformat<
   F0	 : RngMPolElt, // the exact local equation in n vars
   subs	 : SeqEnum,    // substitutions to go from n to d vars
   subs1 : SeqEnum,    // substitutions to go from orig vars to n vars
   p	 : Pt	       // the singular point p
>;

intrinsic HypersurfaceSingularityExpandFunction(dat::Rec, f::FldFunRatMElt,
			prec::RngIntElt, R::RngMPol) -> RngMPolElt,RngMPolElt
{ If dat is the data record returned for a hypersurface singularity p, expand
  rational function f (given as a quotient of two polynomials in the
  ambient coordinate ring of the scheme on which p lies) in the quotient of
  the analytic coordinate ring R1 = k[[x1,..xd]] for which dat describes the singularity
  p as analytically isomorphic to the singularity at the origin of R1/(F).
  R should be a polynomial ring with base field equal
  to k and rank equal to d. The result is the quotient of the two returned polynomials
  in R (the pullbacks of the numerator and denominator of f) which have been
  expanded to include all terms below degree prec+1. }

    F0 := dat`F0;
    R1 := Parent(F0);
    require IsIdentical(BaseRing(R1),BaseRing(R)):
	"R must have the field of definition of the singular point as base ring";
    require IsIdentical(BaseRing(R1),BaseRing(Parent(f))):
	"The parent of f must have the field of definition of the singular point as base ring";
    require Rank(Parent(f)) eq #(dat`subs1):
	"The parent of f must have the the same rank as the coordinate ring of the singular point";


    subs := dat`subs;
    n := Rank(R1);
    d := n-#subs;
    require Rank(R) eq d:
	"R must have rank equal to",d;

    fn := Numerator(f); fd := Denominator(f);
    S := Parent(fn);
    AX := Ambient(Scheme(dat`p));
    RX := CoordinateRing(AX);
    // check that f is homogeneous of degree 0
    if not IsAffine(AX) then
	if IsIdentical(S,RX) then
	  f1 := fn; f2 := fd;
	else
	  k := BaseRing(AX);
	  f1,f2 := Explode([Polynomial([k!1 : i in [1..#ms]],
		[Monomial(RX,Exponents(m)) : m in ms]) 
		where ms is Monomials(e) : e in [fn,fd]]);
	end if;
	boo := IsHomogeneous(AX,f1) and IsHomogeneous(AX,f2);
	if boo then
	  md1 := Multidegree(AX,f1); md2 := Multidegree(AX,f2);
	end if;
	require boo and (md1 eq md2):
	  "f must be a quotient of homogeneous polynomials of the same",
	  "degree with respect to all gradings of the scheme of the singular point";
    end if;
    fs := [Evaluate(e,dat`subs1) : e in [fn,fd]];
    s := [R1.i : i in [1..d]] cat subs;
    Fs := [expand_to_prec(e,d,s,prec) : e in fs];
    hm := hom<R1->R|[R.i : i in [1..d]] cat [R!0 : i in [d+1..n]]>;
    return hm(Fs[1]), hm(Fs[2]);

end intrinsic;

intrinsic HypersurfaceSingularityExpandFurther(dat::Rec, prec::RngIntElt, R::RngMPol) ->
		RngMPolElt
{ If dat is the data record returned for a hypersurface singularity p, further expand
  and return the analytic hypersurface equation F describing the singularity to include
  all terms below degree prec+1. R should be a polynomial ring with base field equal
  to the field of definition of the singular point p and rank equal to the dimension
  of the tangent space at p. F is returned as an element of R. }

    F0 := dat`F0;
    R1 := Parent(F0);
    require IsIdentical(BaseRing(R1),BaseRing(R)):
	"R must have the field of definition of the singular point as base ring";
    subs := dat`subs;
    n := Rank(R1);
    d := n-#subs;
    require Rank(R) eq d:
	"R must have rank equal to",d;
    s := [R1.i : i in [1..d]] cat subs;
    F := expand_to_prec(F0,d,s,prec);
    hm := hom<R1->R|[R.i : i in [1..d]] cat [R!0 : i in [d+1..n]]>;
    return hm(F);

end intrinsic;

intrinsic IsHypersurfaceSingularity(p::Pt, prec::RngIntElt) -> BoolElt,RngMPolElt,SeqEnum,Rec 
{ Point p in a pointset X(k) of scheme X should be an isolated singular point
  on X. Returns whether p is analytically isomorphic to a hypersurface
  singularity. If so, also returns a multi-variate polynomial f(x1,..xd) over k
  giving the expansion up to terms of degree prec+1 of a power series
  F with an isomorphic singularity at the origin and corresponding
  linear transfomation map from the coordinate ring of the ambient
  of X to the parent of f}

    require prec gt 0:
	"prec should be a positive integer";

    X := Scheme(p);
    require IsSingular(p):
	"p must be a singular point on its scheme";

    k := Ring(Parent(p));
    require IsField(k):
	"p must be in a pointset over a field";

    q := p;
    if not IsIdentical(k,BaseRing(X)) then
	X := BaseChange(X,k);
	p := X!Eltseq(p);
    end if;

    // localise to affine patch
    if not IsAffine(X) then
	Y,p := AffinePatch(X,p);
	pcm := ProjectiveClosureMap(Ambient(Y));
	seq1 := DefiningPolynomials(Inverse(pcm));
	seq1i := DefiningPolynomials(pcm);
    else
	Y := X;
	seq1 := [R.i : i in [1..Rank(R)]] where R is
		CoordinateRing(Ambient(X));
	seq1i := seq1;
    end if;
    // translate to origin
    if &or[e ne 0 : e in Eltseq(p)] then
	tr := Translation(Y,p);
	Y := Scheme(Ambient(Y),[Evaluate(f,idp) : f in
		DefiningPolynomials(Y)]) where idp is
		  InverseDefiningPolynomials(tr);
	seq1 := [seq1[i]-e[i] : i in [1..#seq1]] where e is Eltseq(p);
	seq1i := [Evaluate(f,s) : f in seq1i] where s is
	  [R.i+e[i] : i in [1..Rank(R)]] where R is
	     CoordinateRing(Ambient(Y)) where e is Eltseq(p);
    end if;

    boo,F,F0,ls,xs,xsi := trans_to_hyp(Y,prec);
    if (not boo) then
	return false,_,_,_;
    end if;

    R := Parent(F);
    n := Rank(R);
    d := n-#ls;
    assert d gt 0;
    R1 := PolynomialRing(k,d,"grevlex");
    homRR1 := hom<R->R1|[R1.i : i in [1..d]] cat [R1!0 : i in [1..n-d]]>;
    F := homRR1(F);
    s := [R.i : i in [1..n]];
    inds := [Index(s,xsi[i]) : i in [1..n]];
    seqi := [Evaluate(f,xs) : f in seq1i];
    seq := [seq1[i] : i in inds[1..d]];
    dat := rec<HSSData | F0 := F0, subs := ls, subs1 := seqi, p := q>;
    return true,F,seq,dat;

end intrinsic;

function milnor_tjurina(fData,booT)
// Computes the Milnor number of the analytic hypersurface F defined by
// fData if booT is false or the Tjurina number of F if booT is true.

    F0 := fData`F0;
    R := Generic(Parent(F0));
    n := Rank(R);
    subs := fData`subs;
    r := #subs; // d = n-r
    B := [Derivative(F0,i) + &+[Derivative(F0,n-r+j)*Derivative(subs[j],i) :
       j in [1..r]] : i in [1..n-r]] cat [R.(n-r+i)-subs[i] : i in [1..r]];
    if booT then B := [F0] cat B; end if;

    // Now compute using local Groebner bases : the Milnor number
    // is the k-dimension of the local ring (R/I)_m where I is
    // the ideal generated by B.
    Rloc := LocalPolynomialRing(BaseRing(R),n,"lgrevlex");
    Iloc := ideal<Rloc|[Rloc!b : b in B]>;
    G := GroebnerBasis(Iloc);
    inits := [LeadingTerm(g) : g in G];
     // now the Hilbert series/poly of Rloc/Iloc is the same as that
     //  of the (homogeneous) monomial ideal generated by inits
    R1 := PolynomialRing(BaseRing(R),n, "grevlex");
    I1 := ideal<R1|inits>;
    H := HilbertSeries(I1);
    if Degree(Denominator(H)) eq 0 then    // Rloc/Iloc is finite-dimensional
      return Integers()!(Evaluate(HilbertSeries(I1),1));
    else
      return Infinity();
    end if;

end function;

intrinsic MilnorNumberAnalyticHypersurface(fData::Rec) -> RngIntElt
{ The Milnor number for the analytic hypersurface F at a point p defined
  by fData, which should be the HSSData record returned by
  IsHypersurfaceSingularity(p,<prec>) }

    return milnor_tjurina(fData,false);

end intrinsic;

intrinsic TjurinaNumberAnalyticHypersurface(fData::Rec) -> RngIntElt
{ The Tjurina number for the analytic hypersurface F at a point p defined
  by fData, which should be the HSSData record returned by
  IsHypersurfaceSingularity(p,<prec>) }

    return milnor_tjurina(fData,true);

end intrinsic;

///////// Surface simple singularity functions ////////////////////////

function is_simple_srf_sing(p,bRetTyp)
// test whether (isolated) singular point p in surface X is a simple singularity.
// If so, also return type of singularity if bRetTyp is true: 
// string "A","D" or "E" and a number n with p of type An,Dn or En.
// If p is non-sing return "A",0 (A0).
// Needs char(k) != 2 and if char(k) = 3, always returns false for poss
// En singularities.

    X := Scheme(p);
    if IsNonsingular(p) then return true,"A",0; end if;
    error if Characteristic(BaseRing(X)) eq 2,
	"This function requires characteristic != 2";
    // localise to affine patch
    if not IsAffine(X) then
	X,p,pi := AffinePatch(X,p);
    end if;
    // translate to origin
    if &or[e ne 0 : e in Eltseq(p)] then
	tr := Translation(X,p);
	X := Scheme(Ambient(X),[Evaluate(f,idp) : f in
		DefiningPolynomials(X)]) where idp is
		  InverseDefiningPolynomials(tr);
	p := X!Eltseq(tr(p)); 
    end if;

    boo,F,F0,ls,xs,xsi := trans_to_hyp(X,2);
    if (not boo) or (F eq 0) or (Min([TotalDegree(t) : t in Terms(F)]) ne 2) then
	return false,_,_;
    end if;
    R := Parent(F);
    k := BaseRing(R);
    n := Rank(R);
    assert #ls eq n-3;
    x,y,z := Explode([R.i : i in [1..3]]);
    q2 := Matrix([[MonomialCoefficient(F,m1*m2) : m2 in [x,y,z]] :
			 m1 in [x,y,z]]);
    
    r := Rank(q2+DiagonalMatrix([q2[i,i] : i in [1..3]]));
    if r eq 3 then // A1 singularity
	return true,"A",1;
    end if;

    // transform the degree 2 form f (the deg 2 part of F) to diagonal
    // form x^2 or x^2+u*y^2
    R1<x1,y1,z1> := PolynomialRing(k,3);
    f := q2[1,1]*x1^2+q2[2,2]*y1^2+q2[3,3]*z1^2+
	  q2[1,2]*x1*y1+q2[2,3]*y1*z1+q2[1,3]*z1*x1;
    f1,mat := DiagonalForm(f);
    a := MonomialCoefficient(f1,x1^2);
    if MonomialCoefficient(f1,x1^2) eq 0 then
	if MonomialCoefficient(f1,y1^2) eq 0 then //swap x and z
	  a := MonomialCoefficient(f1,z1^2);
	  mat := PermutationMatrix(k,[3,2,1])*mat;
	elif MonomialCoefficient(f1,z1^2) eq 0 then //swap x and y
	  a := MonomialCoefficient(f1,y1^2);
	  mat := PermutationMatrix(k,[2,1,3])*mat;
        else // permute z <- x <- y <- z
 	  a := MonomialCoefficient(f1,y1^2);
	  mat := PermutationMatrix(k,[2,3,1])*mat;
	end if;
    elif (MonomialCoefficient(f1,y1^2) eq 0) and 
		(MonomialCoefficient(f1,z1^2) ne 0) then
	//swap y and z
	mat := PermutationMatrix(k,[1,3,2])*mat;
    end if;
    F0 := (1/a)*F0;
    if mat ne IdentityMatrix(k,3) then
      subst := Eltseq(Vector([x,y,z])*ChangeRing(mat,R)) cat 
			[R.i : i in [4..n]];
      F0 := Evaluate(F0,subst);
      ls := [Evaluate(f,subst) : f in ls] ;
    end if;
    ls1 := ls;
    bFdone := (n eq 3) or (&and[&and[e eq 0 : e in es] where es
	is Exponents(t)[4..n] : t in Terms(F0)]);
    if bFdone then 
	F := F0;
    else
	F := Evaluate(F0,[x,y,z] cat ls);
	seq := [t : t in Terms(F) | &or[e[i] ne 0 : i in [4..n]]
		where e is Exponents(t)];
	if #seq eq 0 then bFdone := true;
	else m0 := Min([TotalDegree(t) : t in seq]); end if;
    end if;

    if r eq 2 then // An sing for n >=2
	// n = mu except possibly if char(k) = p and p | mu when
        // n may be mu-1. For p|mu, the 2nd case occurs if
        // mu (=TjurinaNumber) != Milnor Number but if they are equal, can
        // only decide by expanding. Maybe we shouldn't class
        // the singularity as a simple An singularity in the bad char p
        // case [F ~ x^2+y^2+z^(p*r)+O(z^(p*r+1))], but we will!
	if not bRetTyp then return true,_,_; end if;
        if bFdone then
      	  mu := TjurinaNumber(Evaluate(F,[x1,y1,z1] cat [0 : i in [4..n]]));
        else
      	  mu := milnor_tjurina(rec<HSSData |F0 := F0,subs := ls>,true);
        end if;
        assert not (Type(mu) cmpeq Infty);
        q := Characteristic(k);
        if (q gt 0) and IsDivisibleBy(mu,q) then
	  if bFdone then
	    mu1 := MilnorNumber(Evaluate(F,[x1,y1,z1] cat [0 : i in [4..n]]));
	  else
	    mu1 := milnor_tjurina(rec<HSSData |F0 := F0,subs := ls>,false);
	  end if;
	  if mu ne mu1 then
	    mu := mu-1;
	  else //must transform to decide whether n=mu or mu-1
	    //first get rid of non x,y,z terms up to degree mu
	    while (not bFdone) and (m0 le mu) do
 	      F := trunc_comp([F],[x,y,z] cat ls,mu)[1];
 	      seq := [t : t in Terms(F) | &or[e[i] ne 0 : i in [4..n]]
 		where e is Exponents(t)];
 	      if #seq eq 0 then bFdone := true;
 	      else m0 := Min([TotalDegree(t) : t in seq]); end if;
	    end while;
	    if not bFdone then
		F := &+[t : t in Terms(f) |TotalDegree(t) le mu];
	    end if;
	    //convert to x1,y1,z1 ring
	    F := Polynomial(Coefficients(F),[Monomial(R1,
		   Exponents(t)[1..3]) : t in Terms(F)]);
	    //transform to x1^2+b*y1^2+p(z1)+O(deg mu+1)
	    F := complete_squares(F,2,mu,false);
	    assert &and[IsZero(MonomialCoefficient(F,z1^r)) : r in [1..mu-1]];
	    if not IsZero(MonomialCoefficient(F,z1^mu)) then //bad case
	      mu := mu-1;
	    end if;
 	  end if;
	end if; 
	return true,"A",mu;
    else // r = 1 - possible Dn,E6,E7,E8 sing
	if (not bFdone) and (m0 eq 3) then
	   F := Evaluate(F,[x,y,z] cat ls);
	   seq := [t : t in Terms(F) | &or[e[i] ne 0 : i in [4..n]]
		where e is Exponents(t)];
	   if #seq eq 0 then bFdone := true;
	   else m0 := Min([TotalDegree(t) : t in seq]); end if;
	end if;
	cs := [MonomialCoefficient(F,m) where
			m is y^(3-i)*z^i : i in [0..3]];
	pc := PolynomialRing(k)!cs;
	if pc eq 0 then
	   return false,_,_;
	end if;
	half := 1/k!2;
	if Degree(pc) le 1 then
	   nr := Degree(pc)+1;
	   if nr eq 1 then // poss. E case
	     a := cs[1];
	     if Characteristic(k) eq 3 then
		return false,_,_;
	     end if;
	   else // nr = 2 - Dn case
	     //transform deg 3 part mod x to a*z*y^2
	     a := cs[2];
	     subst := [x,y,z-(cs[1]/a)*y] cat [R.i : i in [4..n]];
	     F := Evaluate(F,subst);
	     ls := [Evaluate(f,subst) : f in ls] ;
	   end if;
	else
	   if Discriminant(pc) ne 0 then
	     return true,"D",4;
	   end if;
	   if Degree(pc) eq 2 then
	     nr := 2; a := cs[3]; 
	     rt := -cs[2]/(a+a);
	     //transform to deg 3 part mod x to a*z*y^2
	     subst := [x,z,y+rt*z] cat [R.i : i in [4..n]];
	   else //pc of deg 3
	     a := cs[4];
	     gc := GCD(pc,Derivative(pc));
	     nr := 3-Degree(gc);
	     if nr eq 2 then // Dn case
		r1 := Coefficient(gc,0); //gc should be monic!
		r2 := Coefficient(pc div (a*gc^2),0);
		s := 1/(r1-r2);
		//transform deg 3 part mod x to a*z*y^2
		subst := [x,s*(y-z),s*(r1*z-r2*y)] cat [R.i : i in [4..n]];
	     elif nr eq 1 then	// poss. E case
		//transform deg 3 part mod x to a*y^3
		rt := -(half*Coefficient(gc,1));
		subst := [x,z,y+rt*z] cat [R.i : i in [4..n]];
	     else // char(k) = 3, pc = at^3+b
		return false,_,_;
	     end if;	
	   end if;
	   F := Evaluate(F,subst);
	   ls := [Evaluate(f,subst) : f in ls] ;
	end if;
	// F is now in the form 
	// i) nr=2: x^2+a*z*y^2+xp+O(deg4) with mindeg(p) >= 2.
	//  This gives Dn for some n >= 5
	// ii) nr=1: x^2+a*y^3+xp+O(deg4) with mindeg(p) >= 2.
	//  This gives E6,E7 or E8 with other conditions
	if nr eq 2 then
	  // as for An, n can be determined from Tjurina number mu -
	  // simpler for Dn : n=mu even in the char p case when p|mu!.
	  if not bRetTyp then return true,_,_; end if;
          if bFdone then
      	    mu := TjurinaNumber(Evaluate(F,[x1,y1,z1] cat [0 : i in [4..n]]));
          else
      	    mu := milnor_tjurina(rec<HSSData |F0 := F0,subs := ls1>,true);
          end if;
          assert (not (Type(mu) cmpeq Infty)) and (mu ge 5);
	  return true,"D",mu;
	else //nr = 1
	  if (not bFdone) and (m0 eq 4) then
	    F := trunc_comp([F],[x,y,z] cat ls,5)[1];
	  end if;
	  // F now purely expanded to at least deg 4 in x,y,z
	  // First remove degree 3 x*f(y,z) terms.
	  cs := Coefficients(F,x);
	  ts := [t : t in Terms(cs[2]) | TotalDegree(t) eq 2];
	  if #ts ne 0 then
	    F := Evaluate(F,[x-half*(&+ts)] cat [R.i : i in [2..n]]);
	    //don't bother changing ls - won't affect things
            // if we have to do one more substitution for deg 5.
	  end if;
	  if MonomialCoefficient(F,z^4) ne 0 then
	    return true,"E",6;
	  elif MonomialCoefficient(F,y*z^3) ne 0 then
	    return true,"E",7;
	  end if;
	  if (not bFdone) and (m0 le 5) then
	    //guarantee deg 5 part fully expanded in x,y,z
	    F := trunc_comp([F],[x,y,z] cat ls,5)[1];
	  end if;
	  if MonomialCoefficient(F,z^5) ne 0 then
	    return true,"E",8;
	  else
	    return false,_,_;
	  end if;
	end if;	   
    end if;

end function;

intrinsic IsSimpleSurfaceSingularity(p::Pt) -> BoolElt, MonStgElt, RngIntElt
{ Returns whether point p of a surface X is a simple (A-D-E) singularity.
  p should be an isolated singular point (or non-singular: type A0). Also returns
  the type of the simple singularity as a string and a number (e.g. "A",3
  for type A3) }

    X := Scheme(p);
    require ISA(Type(X),Srfc):
	"The scheme of point p should be a surface";
    L := Ring(Parent(p));
    if not (L cmpeq BaseRing(X)) then
       XL := BaseChange(X,L);
       return is_simple_srf_sing(XL!Eltseq(p),true);
    else
       return is_simple_srf_sing(p,true);
    end if;

end intrinsic;

intrinsic HasOnlySimpleSingularities(X::Srfc : ReturnList := false) -> BoolElt, List
{ Returns whether surface X only has simple (A-D-E) isolated singularities.
  If so and ReturnList is true (default: false) also returns a list of singular points
  and their types. }

    if assigned X`Nonsingular then
	if X`Nonsingular then
	   set_non_sing(~X,true);
	end if;
    end if;
    if assigned X`only_simple_sings then
      if not ReturnList then
	return X`only_simple_sings;
      elif (not X`only_simple_sings) then
	return false,_;
      elif assigned X`simp_sings then 
	return true,X`simp_sings;
      end if;
    end if;

    XS := SingularSubscheme(X);
    if Dimension(XS) eq -1 then
      set_non_sing(~X,true);
    elif Dimension(XS) ge 1 then
      set_non_sing(~X,false);
      X`only_simple_sings := false;
    else //singular subscheme of dimension 0
      set_non_sing(~X,false);
      pts,K := PointsOverSplittingField(XS);
      XK := BaseChange(X,K);
      dat := [**];
      boo := true;
      for p in pts do
	boo1,str,n := is_simple_srf_sing(XK!Eltseq(p),ReturnList);
	if boo1 and ReturnList then
	  Append(~dat,<X(K)!Eltseq(p),str,n>); 
	elif not boo1 then
	  boo := false;
	  break;
	end if;
      end for;
      set_oss(~X,boo);
      if boo and ReturnList then	
        X`simp_sings := dat;
      end if;
    end if;

    if ReturnList then
      if X`only_simple_sings then
        return true,X`simp_sings;
      else
	return false,_;
      end if;
    else
      return X`only_simple_sings;
    end if;
	
end intrinsic;
