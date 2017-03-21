freeze;

/////////////////////////////////////////////////////////////////////////////////
///   Functions for computing minimal models as well as the full weighted     ///
///        canonical model/canonical coordinate ring of an ordinary           ///
///              projective surface of general type.                          ///
///                   mch - 09/12                                             ///
/////////////////////////////////////////////////////////////////////////////////

import "../../Commut/RngMPol/sheaf.m":QuotientIdealBasis;
import "kod_enr.m":h0;

function rr(X,ID,F,hX,OXres,i0)
//  Cut down version of DivisorToSheaf giving just the global rr space
// ID > Ideal(X) (& both saturated) defines an effective Cartier divisor D
// F is homogeneous (of deg r) in ID\IX and hX is the Hilbert series of IX.
// OXres is the minimal free resolution of R/IX
//  Returns B,r1-r where r1>=r, u is R.i0^(r1-r) for smallest i0 with R.i0 notin IX
// and B is a sequence of degree r1 polys s.t. b/(F*u), b in B restricted to
// X is a basis for L(D)

    R := CoordinateRing(Ambient(X));
    IX := Ideal(X);
    
    // IDEA: let r be the smallest s.t. ID_r != IX_r.
    //  Let Fr in ID_r\IX_r and IE=(<Fr>+IX:ID). Then
    //  IE is the ideal defining an effective divisor of X with D+E=rH where
    //  H is the hyperplane section and L(D)=L(rH-E) which is represented by
    //  the module (IE/IX)(r).
    //  Note also that (IE/IX)(r) will be saturated in degrees >= 0 if
    //  R_i = (R/I)_i [ith graded pieces] for i >= r

    //dX := Degree(HilbertPolynomial(IX)); dD := Degree(HilbertPolynomial(ID));
    //assert dX eq dD+1;
    hD := HilbertSeries(ID);
    hXD := hX-hD;
    r := LeadingTotalDegree(F); //Valuation(Numerator(hXD));
    Fr := F;

    r1 := r;
    n := Rank(R);
    if #Terms(OXres) ge n+2 then
	assert  #Terms(OXres) eq n+2; //as IX is saturated
	h1 := Term(OXres,n-1);
	    // Ext^(n-1)(R/I,R) is a quotient of the dual of h1.
	    // This is dual to sum_r H^1(P^(n-1),I(r)) with the
	    // r graded piece <-> the (-n-r)th graded piece of
	    // the Ext module. We want the max r >= 0 s.t.
	    // this rth graded piece is non-zero which is the
	    // max r s.t. R_r -> (R/I)_r ISN't onto (if r exists)
	r1 := Max(ColumnWeights(h1))-n+1;
	r1 := Max(r,r1);	    
    end if;
    if r1 gt r then //ASSUMED THAT IX is PRIME HERE
	u := (R.i0)^(r1-r);
    else
	u := R!1;
    end if;

    // Get IE
    IXF := Saturation(IX+ideal<R|F*u>);
    IE := ColonIdeal(IXF,ID); // IE is automatically saturated
    
    // Get (IE/IX)_r1
    B := QuotientIdealBasis(IE,IX,r1);
    //B := MinimalBasis(IE meet ideal<R|MonomialsOfDegree(R,r1)>);
    /* NB : should make the above line more efficient */
    //B := [b : b in B | LeadingTotalDegree(b) eq r1];
 
    return B,r1-r;

end function;

function my_prod(pows,n)
// returns a sequence of all distinct products of n elements in seq B.
// pows is a seq of seqs s.t. pows[i] contain the powers of B[i] from
// B[i]^1 to at least B[i]^n.

    exps := [Exponents(m) : m in 
		MonomialsOfDegree(PolynomialRing(Integers(),#pows),n)];
    prd := [&*[pows[i][e[i]] : i in [1..#pows]| e[i] ne 0] : e in exps];
    return prd,exps;

end function;

function reduce_pols(ps,I)
// ps is a sequence of deg d polys in R and I a homog ideal of R
// return a basis for the space of Normal forms mod I of
// the vector space of polys gen by ps.

    R := Generic(I);
    d := LeadingTotalDegree(ps[1]);
    fs := [NormalForm(f,I) : f in ps];
    mons := Setseq(MonomialsOfDegree(R,d));
    V := VectorSpace(BaseRing(R),#mons);
    W := sub<V|[V![MonomialCoefficient(f,m) : m in mons] : f in fs]>;
    return [R|Polynomial(Eltseq(v),mons) : v in Basis(W)];

end function;

function mons_mod_I(n,Rw,Bs,I)

    R := Generic(Universe(Bs[1]));
    ns := VariableWeights(Rw);
    mons := Setseq(MonomialsOfWeightedDegree(Rw,n));
    es := [Exponents(m) : m in mons];

    // precompute powers
    pows := [];
    for i in [1..#ns] do
      m := Max([e[i] : e in es]);
      B := Bs[i];
      ps := [[b] : b in B];
      for j in [2..m] do
	for k in [1..#B] do Append(~ps[k],ps[k][j-1]*B[k]); end for;
      end for;
      Append(~pows,ps);
    end for;

    degs := [];
    pols := [];
    for e in es do
	cmps := [(e[i] eq 1) select Bs[i] else my_prod(pows[i],e[i]) : 
			i in [1..#ns] | e[i] ne 0];
	cmps := [reduce_pols(c,I) : c in cmps];
	nc := #cmps;
	cmps := (nc eq 1) select cmps[1] else
		[&*[e[i] : i in [1..nc]] : e in CartesianProduct(cmps)];
	Append(~pols,cmps);
	Append(~degs,LeadingTotalDegree(cmps[1]));
    end for;
    return pols,degs;
    
end function;


function new_gens(n,Bn,Bs,ns,i0,IX)

    R := Generic(Universe(Bn));
    Rw := PolynomialRing(BaseRing(R),ns);
    pols,degs := mons_mod_I(n,Rw,Bs,IX);

    assert &and[d ge n : d in degs];
    dn := LeadingTotalDegree(Bn[1]);
    dmax := Max(Max(degs),dn);
    m := R.i0;

    // deal with power of R.i0    
    pols := &cat[(degs[i] eq dmax) select pols[i] else
	[m^(dmax-degs[i])*p : p in pols[i]] : i in [1..#pols]];
    pols := reduce_pols(pols,IX);
    Bnr := (dn eq dmax) select Bn else [m^(dmax-dn)*p : p in Bn];
    Bnr := reduce_pols(Bnr,IX);

    mons := Setseq(MonomialsOfDegree(R,dmax));
    V := VectorSpace(BaseRing(R),#mons);
    W1 := sub<V|[V![MonomialCoefficient(f,m) : m in mons] : f in pols]>;
    W2 := sub<V|[V![MonomialCoefficient(f,m) : m in mons] : f in Bnr]>;
    //assert W1 subset W2
    W := Complement(W2,W1);
    return [R|Polynomial(Eltseq(v),mons) : v in Basis(W)];

end function;

function all_relns(Bs,us,ns,R1,i0,X)
// Bs[i] is a seq of homog polys in R s.t. (f/x^us[i]F^ns[i]) for f in Bs[i]
// are (deg 0) rat fns (giving the "new-part" of L(ns[i]D) for some divisor
// D on X) where x is R.i0 and F is some homog poly of R.
// R1 is a grevlexw poly ring whose vars of weight ns[i] are in 1-1 corr
// with the elts of Bs[i].
// Fn computes and returns the full ideal I1 < R1 of relations between the
// (f/x^us[i]F^ns[i]).

//NB: initially assuming here that ns[1]=1 (ie pg(X) > 0)
    // Compute directly here from the graph ideal of the weighted map
    // into Proj(R1)
    a := Max([Ceiling(us[i]/ns[i]) : i in [1..#ns]]);
    R := Generic(Universe(Bs[1]));
    if a eq 0 then
	seq := &cat(Bs);
    else
	x := R.i0;
	seq := &cat[[f*x^(ns[i]*a-us[i]) : f in Bs[i]] : i in [1..#ns]];
    end if;

    //define graph
    n := Rank(R); m := #seq;
    wts := VariableWeights(R1);
    PG := PolynomialRing(BaseRing(R),s,"grevlexw",s) 
		where s is [1 : i in [1..n]] cat wts;
    incl_hom := hom<R -> PG | [PG.i : i in [1..n]]>;
    E1 := [incl_hom(e) : e in seq];
    I_gr := ideal<PG|[incl_hom(b) : b in Basis(Ideal(X))] cat
	[PG.(n+i)*E1[1]^wts[i]-PG.(n+1)^wts[i]*E1[i] : i in [2..m]]>;

    //saturate wrt Bs[1][1]
    I_gr := ColonIdeal(I_gr,E1[1]);

    //read off basis for I1 and transform back to R1
    B := GroebnerBasis(I_gr);
    B_im := [f : f in B | &and[e[i] eq 0 : i in [1..n]] 
			where e is Exponents(LeadingTerm(f))];
    B_im := [Polynomial(Coefficients(f),[Monomial(R1,e[n+1..n+m])
		where e is Exponents(m1) : m1 in Monomials(f)]) : f in B_im];

    return ideal<R1|B_im>;

end function;

function relns_of_degree(d,Bs,R1,i0,IX)

    mons := Setseq(MonomialsOfWeightedDegree(R1,d));
    es := [Exponents(m) : m in mons];
    n := Rank(R1);
    B := &cat(Bs);
    R := Parent(B[1]);

    //precompute powers
    pows := [];
    for i in [1..#B] do
      m := Max([e[i] : e in es]);
      f := B[i];
      ps := [f];
      for i in [2..m] do Append(~ps,ps[i-1]*f); end for;
      Append(~pows,ps);
    end for;

    //compute monomials evaluated at Bs
    pols := [&*[pows[i][e[i]] : i in [1..n] | e[i] ne 0] : e in es];
    degs := [LeadingTotalDegree(p) : p in pols];

    // deal with power of R.i0 and reduce to Normal form
    dmax := Max(degs);
    x := R.i0;    
    pols := [NormalForm((degs[i] eq dmax) select pols[i] else
	x^(dmax-degs[i])*pols[i],IX) : i in [1..#pols]];

    // compute relations
    mat := Matrix([[MonomialCoefficient(f,m) : m in mons1]: f in pols])
	where mons1 is Setseq(MonomialsOfDegree(R,dmax));
    K := Kernel(mat);
    return [Polynomial(Eltseq(b),mons) : b in Basis(K)];  
         
end function;

function rat_is_pol(f)
   fn := Numerator(f);
   fd := Denominator(f);
   if Degree(fd) gt 0 then return false,_; end if;
   c := Coefficient(fd,0);
   if c ne 1 then fn := (1/c)*fn; end if;
   return true,PolynomialRing(Integers())!fn;
end function;

function can_relns(X)
// Computes and returns the canonical ideal I of gen type surface X.
// Also returns a sequence of polynomials that give the map from
// X into the canonical model Proj(Generic(I)/I).

  D := CanonicalDivisor(X);
  ID := D`ideal;
  KX := DivisorToSheaf(X,ID);
  rr1 := (KX`rr_space)[1];
  F := (KX`rr_space)[2];
  Saturate(~X);
  IX := Ideal(X);
  R := Generic(IX);
  k := BaseRing(R);
  OX := QuotientModule(IX);
  hX := HilbertSeries(OX);
  OXres := MinimalFreeResolution(OX);
  i0 := 1; while (R.i0) in IX do i0 +:=1; end while;

  // get Riemann-Roch spaces for L(rKX), r=1,2
  B1 := rr1;
  u1 := 0;
  ID2 := Saturation(ID^2+IX);
  B2,u2 := rr(X,ID2,F^2,hX,OXres,i0);

  // get invts & canonical hilb series
  pg := #B1;
  error if pg eq 0, "Sorry. Can't currently compute canonical model for",
	"surfaces with geometric genus 0"; 
  if assigned X`pg then
     assert (X`pg) eq pg;
  else
     X`pg := pg;
  end if;
  //K2 := IntersectionPairing(KX,KX);
  if assigned X`q then
    chi := 1+pg-(X`q);
  else
    chi := ArithmeticGenus(X)+1;
    X`q := 1+pg-chi;
    assert (X`q) ge 0;
  end if;
  assert chi gt 0;
  K2m := (#B2)-chi; // K^2 for a minimal model of X
  assert K2m gt 0;
  if assigned X`K2m then
    assert (X`K2m) eq K2m;
  else
    X`K2m := K2m;
  end if;
  if assigned X`K2 then
    assert (X`K2) le K2m;
  end if;
  R := RationalFunctionField(Rationals());
  H := 1+pg*t+t^2*(chi*(t-1)^2+K2m)/(1-t)^3 where t is 
	RationalFunctionField(Rationals()).1;

  // get relations and add new L(rKX) until done
  R := Generic(IX);
  r := LeadingTotalDegree(F);
  m := R.i0;
  if K2m ge 3 then
    n0 := 3;
  elif K2m eq 2 then
    n0 := 4;
  else // K2m=1
    n0 := 5;
  end if;
  //mp := Max([u1,u2]);

  Y := Image(map<X->ProjectiveSpace(k,pg-1)|B1>);
  Saturate(~Y);
  I1 := Ideal(Y);
  R1 := Generic(I1);
  Ht := HilbertSeries(I1);
  Hd := H-Ht;
  Bs := [B1];
  wts := [1 : i in [1..pg]];
  ns := [1];
  us := [u1];
  peaks := 0;
  IDn := ID2;
  nD := 2;

  while Hd ne 0 do
    n := Valuation(Numerator(Hd));
    dn := Integers()!(Coefficient(Numerator(Hd),n)/
		Coefficient(Denominator(Hd),0));
    if n eq 2 then
	Bn := B2; un := u2;
	IDn := ID2;
    else
	IDn := Saturation((ID^(n-nD)*IDn)+IX);
	Bn,un := rr(X,IDn,F^n,hX,OXres,i0);
    end if;
    nD := n;
    Bnew := new_gens(n,Bn,Bs,ns,i0,IX);
    assert #Bnew eq dn;
    Append(~Bs,Bnew);
    Append(~ns,n);
    Append(~us,un);
    wts cat:= [n : i in [1..dn]];
    R1n := PolynomialRing(k,wts,"grevlexw",wts);
    I1 := ideal<R1n|[hm(b) : b in Basis(I1)]> where
	hm is hom<R1->R1n|[R1n.i : i in [1..Rank(R1)]]>;
    R1 := R1n;
    
    if n le n0 then
      I1 := all_relns(Bs,us,ns,R1,i0,X);      
      Ht := HilbertSeries(I1);
      Hd := H-Ht;
    else
      if Type(peaks) eq RngIntElt then
	boo,pol := rat_is_pol(Hd);
	assert boo;
        peaks := [m : m in [n..Degree(pol)] | Coefficient(pol,m) ne 0];
      end if;
      assert peaks[1] eq n;
      d := n;
      Remove(~peaks,1);
      if #peaks eq 0 then
        Ht := HilbertSeries(I1);
	Hd := H-Ht;
      end if;
      while #peaks gt 0 do
	d +:= 1;
	d1 := peaks[1];
	for e in [d..d1] do
	  rels := relns_of_degree(e,Bs,us,ns,R1,IX);
	  if &or[f notin I1 : f in rels] then
            I1 := I1+ideal<R1|rels>;
	  end if;
	end for;
        Ht := HilbertSeries(I1);
	Hd := H-Ht;
	d2 := (Hd eq 0) select d1+1 else Valuation(Numerator(Hd));
	if d2 eq d1 then break; end if;
	d := d1; Remove(~peaks,1);
      end while;
      if #peaks eq 0 then //have all generators but not nec. all relns
	while Hd ne 0 do
	  d := Valuation(Numerator(Hd));
	  relsd := relns_of_degree(d,Bs,R1,i0,IX);
          I1 := I1+ideal<R1|relsd>;
          Ht := HilbertSeries(I1);
	  Hd := H-Ht;
	end while;
      end if;
    end if;
  end while;

  // adjust Bs by powers of R.i0 if nec
  if #ns gt 1 then
    u := Max([Ceiling(us[i]/ns[i]) : i in [1..#ns]]);
    if u gt 0 then
	x := R.i0;
	Bs := [(us[i] eq ns[i]*u) select Bs[i] else
	  ([b*m : b in Bs[i]] where m is x^(ns[i]*u-us[i])) : i in [1..#ns]];
    end if;
  end if; 

  return I1,&cat(Bs);
end function;

intrinsic CanonicalWeightedModel(X::Srfc: CheckADE := false) -> Map, BoolElt
{ Returns a birational map to the full (weighted) canonical model of an
 ordinary projective surface X of general type with only simple singularities. Second return
 value is true if and only if X is already minimal in the sense of having no (-1) curves. }

    if assigned X`can_mod_map then
      assert (assigned X`K2) and (assigned X`K2m);
      return X`can_mod_map, ((X`K2) eq (X`K2m)); 
    end if;
    require IsOrdinaryProjective(X):
	"Argument X should be a surface in ordinary projective space";
    if CheckADE then
	require HasOnlySimpleSingularities(X):
		"Surface argument X should have only simple singularities";
    end if;

    I,B := can_relns(X);
    Xc := Surface(Proj(Generic(I)),I : Check := false);
    cmap := map<X->Xc|B : Check := false>;

    if not (assigned X`K2) then
	X`K2 := IntersectionPairing(KX,KX) where KX is CanonicalSheaf(X);
    end if;
    assert (X`K2) le (X`K2m);
    is_min := ((X`K2) eq (X`K2m));

    //fill in attributes for Xc
    Xc`pg := X`pg; Xc`q := X`q; Xc`K2 := X`K2; Xc`K2m := X`K2m;
    Xc`kod_dim := 2; Xc`can_mod_map := IdentityMap(Xc);
    Xc`only_simple_sings := true;

    X`can_mod_map := cmap;
    return cmap,is_min;

end intrinsic;

intrinsic CanonicalCoordinateIdeal(X::Srfc: CheckADE := false) -> Map, BoolElt
{ For an ordinary projective surface X of general type with only simple singularities,
  returns the canonical ideal I. This is the ideal in a weighted polynomial ring
  R such that R/I is isomorphic to the full canonical coordinate ring of X. }

    if assigned X`can_mod_map then
      return Ideal(Codomain(X`can_mod_map)); 
    end if;
    require IsOrdinaryProjective(X):
	"Argument X should be a surface in ordinary projective space";
    if CheckADE then
	require HasOnlySimpleSingularities(X):
		"Surface argument X should have only simple singularities";
    end if;

    mp := CanonicalWeightedModel(X : CheckADE := false);
    return Ideal(Codomain(mp));
    
end intrinsic;

// Rough version - is there an easy way to tell when the canonical map or
// bi-canonical map work??
intrinsic MinimalModelGeneralType(X::Srfc : CheckADE := false) -> Map, BoolElt
{ Returns a birational map to a minimal model (with (-2)-curves contracted) of an
 ordinary projective surface X of general type with only simple singularities. Second return value
 is true if and only if X is already minimal in the sense of having no (-1) curves.
 See CanonicalWeightedModel for a better model. }

    if assigned X`min_map then
      assert (assigned X`K2) and (assigned X`K2m);
      return X`min_map, ((X`K2) eq (X`K2m)); 
    end if;
    require IsOrdinaryProjective(X):
	"Argument X should be a surface in ordinary projective space";
    if CheckADE then
	require HasOnlySimpleSingularities(X):
		"Surface argument X should have only simple singularities";
    end if;

    KX := CanonicalSheaf(X);
    SaturateSheaf(~KX);
    if assigned X`pg then
	p1 := X`pg; //geometric genus of X
    else
	p1 := h0(KX);
	X`pg := p1;    
    end if;    
    if assigned X`q then
	pa := p1-(X`q);
    else
        pa := ArithmeticGenus(X);
	X`q := p1-pa;
    end if;
    if assigned X`K2 then
	K2 := X`K2;
    else
	K2 := IntersectionPairing(KX,KX);
	X`K2 := K2;
    end if;

    // simple test for whether KX is very ample
    // - true if X a global complete intersection
    codim := Rank(CoordinateRing(Ambient(X)))-3;
    if (#DefiningPolynomials(X) eq codim) or
	(#MinimalBasis(Ideal(X)) eq codim) or
	  (#ColumnWeights(FullModule(KX)) eq 1) then
      if assigned X`K2m then
	assert X`K2m eq K2;
      else
	X`K2m := K2;
      end if;
      return IdentityMap(X),true;
    end if;

    KX2 := TensorPower(KX,2);
    //find the minimal K2
    if assigned X`K2m then
	K2m := X`K2m;
    else
        p2 := h0(KX2);
        K2m := p2-pa-1;
	X`K2m := K2m;
    end if;
    assert K2m le K2;
    is_min := K2 eq K2m;

    //try simple test to see if KX2 is very ample
    if is_min and (#ColumnWeights(FullModule(KX2)) eq 1) then
	return IdentityMap(X),true;
    end if;

    if K2m ne 2 then
	KX3 := TensorProduct(KX2,KX : Maximize := true);
    end if;

    if K2m ge 3 then // f3 works
       mp,Xm := DivisorMap(KX3);
    elif K2m eq 2 then // f4 works
	KX4 := TensorPower(KX2,2);
	mp,Xm := DivisorMap(KX4);
    else
      // K2m eq 1 - use f5 - this is an extremal case lying in the Noether
      // line and should analyse better!
	KX5 := TensorProduct(KX2,KX3 : Maximize := true);
	mp,Xm := DivisorMap(KX5);
    end if;
   mp := Restriction(mp,X,Xm);

   //fill in attributes for Xm
   Xm`pg := X`pg; Xm`q := X`q; Xm`K2 := K2; Xm`K2m := K2m;
   Xm`kod_dim := 2; Xm`min_map := IdentityMap(Xm);
   Xm`only_simple_sings := true;

   X`min_map := mp;
   return mp, is_min;

end intrinsic;
