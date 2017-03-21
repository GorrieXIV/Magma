freeze;

/***************************************************************************************/
//    Intrinsics for BLOWING UP arbitrary subschemes of affine, ordinary projective    //
//       or product projective schemes and also for SEGRE EMBEDDINGS of product        //
//     projective schemes (or a sequence of ordinary proj. schemes to be product       //
//      embedded) into ordinary projective space.                                      //
//                 mch 04/13                                                           //
/***************************************************************************************/

function monomials_of_multi_degree(R,mdeg,ns)
// mdeg := [m1,..,mr] and ns := [n1,..,nr] with ni > 0, mi >= 0
// R is a polynomial ring of degree N=n1+n2+..+nr. Returns 
// a sequence of monomials of R of multidegree mdeg where
// we take the multigrading for which the first n1 vars of R are
// degree [1,0,..,0], the next n2 vars are degree [0,1,0,..,0],
//  etc.

   k := BaseRing(R);
   mons := [R|1]; r := 0;
   for i in [1..#ns] do
     mi := mdeg[i]; ni := ns[i];
     if mi gt 0 then
	Pi := PolynomialRing(k,ni,"grevlex");
	mpi := hom<Pi->R|[R.(r+j) : j in [1..ni]]>;
	monsi := [mpi(m) : m in MonomialsOfDegree(Pi,mi)];
	mons := [m1*m2 : m1 in monsi, m2 in mons];	
     end if;
     r +:= ni;
   end for;
   return mons;

end function;

function ord_proj_basis(IY)
// Y is an ordinary projective variety with ideal IY.
// Return a basis B for IY1 < IY where B consists of
// elements all of the same degree and IY1 defines the
// same scheme (Y) as IY

    R := Generic(IY);
    B0 := Basis(IY);
    B := MinimalBasis(IY);
    if (#B lt #B0) then
	IY1 := ideal<R|B>;
    else
	B := B0;
	IY1 := IY;
    end if;
    degs := [LeadingTotalDegree(b) : b in B];
    d := Max(degs);
    if &and[e eq d : e in degs] then
	return IY1;
    end if;
    IY1 := IY1 meet ideal<R | Setseq(MonomialsOfDegree(R,d))>;
    B := MinimalBasis(IY1);
    return ideal<R|B>;

end function;

function prod_proj_basis(IY,ns,A)
// Y is an product projective variety (in A=P^(n1-1)x..xP^(nr-1) where
// ns = [n1,..ns]) with ideal IY.
// Return an ideal IY1 < IY with minimised basis where B consists of
// elements all of the same multi-degree and IY1 defines the
// same scheme (Y) as IY

    R := Generic(IY);
    B0 := Basis(IY);
    B := MinimalBasis(IY);
    if #B eq 0 then return ideal<R|>; end if;
    if (#B lt #B0) then
	IY1 := ideal<R|B>;
    else
	B := B0;
	IY1 := IY;
    end if;
    mdegs := [Multidegree(A,b) : b in B];
    ds := [Max([m[i] : m in mdegs]) : i in [1..#ns]];
    boo := &and[e[i] eq ds[i] : e in mdegs, i in [1..#ns]];
    if &and[e[i] eq ds[i] : e in mdegs, i in [1..#ns]] then
	return IY1;
    end if;
    IY1 := IY1 meet ideal<R | monomials_of_multi_degree(R,ds,ns)>;
    B := MinimalBasis(IY1);
    return ideal<R|B>;

end function;

function is_product_proj(A)
// true iff the ambient is product projective space

    gs := Gradings(A);
    if (#gs eq 0) or (#(QuotientGradings(A)) gt 0) then
      return false,_;
    end if;
    gm := Matrix(gs);
    if &or[g lt 0 : g in Eltseq(gm)] then return false,_; end if;
    if &or[g gt 1 : g in Eltseq(gm)] then return false,_; end if;
    N := #(gs[1]);
    ns := [Max([i : i in [1..N] | g[i] eq 1]) : g in gs];
    boo := &and[i eq 1 : i in (gs[1])[1..ns[1]]] and
	     (&and[i eq 0 : i in (gs[1])[ns[1]+1..N]]);
    if boo then
      if #gs eq 1 then
	boo := ns[1] eq N;
      else
	n := #gs;
	boo := (ns[n] eq N) and (ns[1] gt 0) and 
	  (&and[ns[i] lt ns[i+1] : i in [1..n-1]]) and
	  (&and[(&and[i eq 0 : i in (gs[j])[1..ns[j-1]]]) and 
		(&and[i eq 1 : i in (gs[j])[ns[j-1]+1..ns[j]]]) and
		(&and[i eq 0 : i in (gs[j])[ns[j]+1..N]]) :
		   j in [2..n]]);
      end if;
    end if;
    if boo then
	return true,[ns[1]] cat [ns[i]-ns[i-1] : i in [2..#gs]];
    else
	return false;
    end if;

end function;

function good_ambient(X)
    A := Ambient(X);
    if IsAffine(A) then
	return 0,_;
    elif IsOrdinaryProjective(A) then
	return 1,_;
    end if;
    boo,ns := is_product_proj(A);
    if boo then
	return 2,ns;
    end if;
    return -1;
end function;

intrinsic SegreProduct(Xs :: SeqEnum[Sch]) -> Sch
{Xs is a sequence of ordinary projective schemes. Computes the direct product scheme
 embedded in ordinary projective space via the Segre embedding. Returns the result
 along with a sequence of scheme maps giving the projections back to
 the Xs[i]}

    require #Xs gt 0 : "The sequence argument must be non-empty";
    require &and[IsOrdinaryProjective(X) : X in Xs] :
	"All the schemes in Xs must be ordinary projective";
    k := BaseRing(Xs[1]);
    require &and[IsIdentical(k,BaseRing(X)) : X in Xs] :
	"All schemes in Xs must be defined over the same base ring";

    ns := [Dimension(Ambient(X))+1 : X in Xs];
    P := ProjectiveSpace(k,(&*ns)-1);
    R := CoordinateRing(P);
   
    // construct sequences for projection maps (with many alternative equations)
    map_seqs := [];
    for i in [1..#Xs] do
	r := &*[Integers()|ns[j] : j in [1..i-1]];
	s := &*[Integers()|ns[j] : j in [i+1..#ns]];
	n := ns[i];
	seqsi := [[R.(j+(l+u*n)*s) : l in [0..n-1]] : j in [1..s], u in [0..r-1]];
	Append(~map_seqs,seqsi);
    end for;

    // get "ambient" defining polynomials (ie for the image of 
    //  P^n1 X P^n2 X .. X P^nr in Proj(P))
    eqns1 := &cat[&cat[[s[i]*t[j]-s[j]*t[i] : i in [1..j-1], j in [1..nl]] 
	where s is se[m] where t is se[n] : m in [1..n-1], n in [1..#se]]
	where se is map_seqs[l] where nl is ns[l] : l in  [1..#Xs]];
      //eqns1 will contain some linearly independent quadrics - get rid
      // with MinimalBasis - lazy method, but works quickly in practice!
    eqns1 := MinimalBasis(ideal<R|eqns1>);
   
    // get other defining polys coming from defining polys of the Xi
    eqns2 := [R|];
    for i in [1..#Xs] do
	eqnsi := DefiningPolynomials(Xs[i]);
	if #eqnsi eq 0 then continue; end if;
	if &or[not IsHomogeneous(e) : e in eqnsi] then
	   eqnsi := MinimalBasis(Ideal(Xs[i]));
	end if;
	eqns2 cat:= [Evaluate(f,seq) : f in eqnsi, seq in map_seqs[i]]; 
    end for;

    // for neatness, we use a minimal basis, even though this may add a 
    //  bit of time to the computation
    if #eqns2 gt 0 then
      eqns := eqns1 cat eqns2;
      eqns := MinimalBasis(ideal<R|eqns>);
    else
      eqns := eqns1;
    end if;

    X := Scheme(P,eqns);
    mps := [map<X->Xs[i] | map_seqs[i] : Check := false> : i in [1..#Xs]];
    return X,mps;

end intrinsic;

function segre_trans(F,A,Rp,ns)
// F is a multi-homogeneous poly of degs (d1,..dr) on product projective
//  space A = P^n1 X .. X P^nr. Return sequence of suitable multiples
//  F*monomial of pure multi-degree (d,d,..,d) reexpressed in
//  "Segre-embedded coordinates" - Rp is the coordinate ring of the ambient
//  for the Segre embedding with the Rp.i <-> x_i1*..*x_ir for all products
//  of the coordinate functions of P^n1,..,P^nr taken in the normal ordering.

    mdegs := Multidegree(A,F);
    P := CoordinateRing(A);
    N := Rank(P);
    d := Max(mdegs);
    r := #ns;

    js := [j : j in [1..r] | mdegs[j] ne d];
    djs := [d-mdegs[j] : j in js];
    njs := [&+[Integers()|ns[i] : i in [1..j-1]] : j in [1..r]];
    pjs := [&*[Integers()|ns[i] : i in [j+1..r]] : j in [1..r]];
    es := Matrix([Exponents(m) : m in Monomials(F)]);
    cs := Coefficients(F);

    esj := [[Exponents(t) : t in MonomialsOfDegree(
		PolynomialRing(Integers(),ns[js[i]],"grevlex"),djs[i] )] : i in [1..#js]];
    //add in 0 exponents for gradings where F has degree d
    esj := [((j ne 0) select esj[j] else [[0 : k in [1..ns[i]]]])
		where j is Index(js,i) : i in [1..r]]; 

    Fs := [];
    for c in CartesianProduct(esj) do
	row := &cat[c[i] : i in [1..r]];
	es1 := RowSequence(es+Matrix([row : i in [1..Nrows(es)]]));
	// convert the monomials in A represented by exponent
	// sequences in es1 to corresponding monomials in Rp
	es2 := [];
	for x in es1 do
	  e := x;
	  seq := [0 : i in [1..Rank(Rp)]];
	  for k in [1..d] do
	    inds := [];
	    for i in [1..r] do
	      for j in [1..ns[i]] do
		if e[njs[i]+j] ne 0 then
		  e[njs[i]+j] -:= 1;
	      	  Append(~inds,j);
		  break; 
		end if;
	      end for;
	    end for;
	    seq[1+&+[(inds[i]-1)*pjs[i] : i in [1..r]]] +:= 1;
	  end for;
	  Append(~es2,seq);
	end for;
	Append(~Fs,Polynomial(cs,[Monomial(Rp,e) : e in es2]));
    end for;

    return Fs;

end function;

intrinsic SegreEmbedding(X::Sch) -> Sch, MapIsoSch
{ X should be a scheme lying in a product projective space. Computes and
  returns the image Y of X under the Segre embedding into ordinary
  projective space and an isomorphism of X to Y }

    A := Ambient(X);
    boo,ns := is_product_proj(A);
    require boo: "The ambient of argument X must be a product projective space";
    //dispose of trivial case
    if #ns eq 1 then
	return X,IdentityMap(X);
    end if;
    k := BaseRing(X);
    Pp,prjs := SegreProduct([ProjectiveSpace(k,n-1) : n in ns]);
    Rp := CoordinateRing(Ambient(Pp));
    Fs := DefiningPolynomials(X);
    eqns := &cat[segre_trans(F,A,Rp,ns) : F in DefiningPolynomials(X)];
    eqns := DefiningPolynomials(Pp) cat eqns;
    // for neatness, we use a minimal basis, even though this may add a 
    //  bit of time to the computation
    eqns := MinimalBasis(ideal<Rp|eqns>);
    if ISA(Type(X),Crv) then
	Y := Curve(Ambient(Pp),eqns);
    elif ISA(Type(X),Srfc) then
	Y := Surface(Ambient(Pp),eqns: Check := false);
    else
        Y := Scheme(Ambient(Pp),eqns);
    end if;

    // generate defining polys for X-> Y
    RA := CoordinateRing(A);
    njs := [&+[Integers()|ns[i] : i in [1..j-1]] : j in [1..#ns]];
    mp_pols := [RA.i : i in [njs[#ns]+1..Rank(RA)]];
    for j := (#ns)-1 to 1 by -1 do
	mp_pols := [(RA.i)*m : m in mp_pols, i in [njs[j]+1..njs[j+1]]];
    end for;
    // and for Y->X
    mpi_pols := [&cat[c[i] : i in [1..#ns]] : c in CartesianProduct(dps)]
	where dps is [AllDefiningPolynomials(p) : p in prjs];

    return Y,iso<X->Y|mp_pols,mpi_pols : Check := false>;

end intrinsic;

intrinsic Blowup(X::Sch,Y::Sch : Ordinary := true) -> Sch, MapSch
{ The blowup of scheme X along subscheme Y. X should be affine, ordinary projective or
  product projective. If parameter Ordinary is true and X is projective, the result
  is Segre-embedded into ordinary projective space. Otherwise, the result will lie
  in an ambient that is the direct product of the ambient of X with an ordinary
  projective space. }

    require Y subset X : "Y must be a subscheme of X";
    typ,typ1 := good_ambient(X);
    require (typ ne -1): "X must be affine, ordinary projective or product projective";

    AX := Ambient(X);
    R := CoordinateRing(AX);
    IY := Ideal(Y);
    if typ eq 1 then  //ordinary projective case
	IY := ideal<R|ord_proj_basis(IY)>;
    elif typ eq 2 then //product projective case
	IY := ideal<R|prod_proj_basis(IY,typ1,AX)>;
    else // affine case
        // can't get a minimal basis, but at least can try to simplify a bit
	B := Basis(IY); B1 := B;
	if #DefiningPolynomials(Y) lt #B then
	    B1 := DefiningPolynomials(Y);
	end if;
	B1 := Setseq(Seqset(B1)); // remove duplicates
	if #B1 lt #B then IY := ideal<R|B1>; end if;
    end if;
    if IsAmbient(X) then
	Ib,hm1 := ReesIdeal(R,IY);
    else
	IX := Ideal(X);
	Ib,hm1 := ReesIdeal(R,IX,IY);
    end if;
    Rb := Generic(Ib);
    n := Rank(Rb)-Rank(R);
    Pnm1 := ProjectiveSpace(BaseRing(X),n-1);
    Pb := DirectProduct(AX,Pnm1);
    hm := hom<Rb->CoordinateRing(Pb) | [Rb.i : i in [1..Rank(Rb)]]>;
    mp_eqns := [hm(hm1(R.i)) : i in [1..Rank(R)]];
    eqns := [hm(b) : b in Basis(Ib)];
    if ISA(Type(X),Crv) then
	Xb := Curve(Pb,eqns);
    elif ISA(Type(X),Srfc) then
	Xb := Surface(Pb,eqns : Check := false);
    else
        Xb := Scheme(Pb,eqns);
    end if;
    // do Segre embedding if required
    if Ordinary and (typ ge 1) then
	Xb,segmp := SegreEmbedding(Xb);
	mp_eqns := [[Evaluate(pol,s) : pol in mp_eqns] : 
			s in AllInverseDefiningPolynomials(segmp)];
	// may have duplicate eqns now - eliminate them!
	mp_eqns := Setseq(Seqset(mp_eqns));
    end if;

    return Xb,map<Xb->X|mp_eqns : Check := false>;

end intrinsic;

intrinsic Blowup(X::Sch,p::Pt : Ordinary := true) -> Sch
{ The blowup of scheme X at the point p (and all of its conjugates) of X(K). 
  X should be affine, ordinary projective or product projective. If parameter Ordinary is
  true and X is projective, the result is Segre-embedded into ordinary projective space.
  Otherwise, the result will lie in an ambient that is the direct product of the ambient of X
  with an ordinary projective space. }

    require p in X : "p must be a point on scheme X";

    k := Ring(Parent(p));
    // Get the equations of p. Transfer p to the ambient to avoid adding
    //  unnecessary extra equations for X!
    Z := Cluster(A(k)!p) where A is Ambient(X); 

    Xb,mp := Blowup(X,Z : Ordinary := Ordinary);
    // In the ordinary projective case, there are often linear relations
    //  after Segre embedding : remove these
    if IsOrdinaryProjective(Xb) then
	Xb,mp1 := RemoveLinearRelations(Xb);
	mp := map<Xb->X| [[Evaluate(pol,s) : pol in seq] : seq in 
	     AllDefiningPolynomials(mp)] : Check := false> 
		where s is InverseDefiningPolynomials(mp1);
    end if;

    // if p a non-singular point, transfer attributes from X to Xb
    if IsNonsingular(p) then
	InternalTransferAttributes1(X,Xb);
	if assigned X`SingularSubscheme then
	  Xb`SingularSubscheme := Scheme(Xb,DefiningPolynomials((X`SingularSubscheme)@@mp));
    	end if;
    	if ISA(Type(X),Srfc) then
	  if assigned X`K2 then
	    Xb`K2 := (X`K2)-Degree(Z);
          end if;
	end if;
    end if;
    return Xb,mp;

end intrinsic;
