freeze;

/**********************************************************

   Functions to compute the dimension of Coherent cohomology
   groups H^r(P^n,M~(i)) for a graded module M over k[x0,..,xn]
   representing coherent sheaf M~ on P^n. Uses the method of
   Decker,Eisenbud,Floystad & Schreyer - the Tate resolution
   over the alternating algebra associated to M is computed
   to a finite degree and the results are read off from that.

               mch 07/08

***********************************************************/
declare verbose Cohom,1;

/* Extra attributes to store information about the part of the
   Tate resolution already computed.                          */
declare attributes ModMPol: CMbound, Aweights, HilbPoly, Aresidue;


/*************************************************************/
// Function to compute an upper bound for the Castelnuevo-Mumford
//  regularity of graded module M. It computes the regularity of
//  a "monomialised M" which is generally faster but only gives
//  an upper bound.

function RegularityBound1(M)

    //assert Type(M) eq ModMPolGrd;

    P := BaseRing(M);
    col_wts := ColumnWeights(M);
    rel_mat := RelationMatrix(M);
    if Nrows(rel_mat) eq 0 then return Max(col_wts); end if;

    // replace relations of M by the leading terms of
    //  a Groebner basis
    F := Module(P,col_wts);
    S := sub<F|[F!Eltseq(rel_mat[i]) : i in [1..Nrows(rel_mat)]]>;
    Groebner(S);
    B := Basis(S);
    B1 := [Eltseq(LeadingTerm(b)) : b in B];
    M := quo<F|[F!b: b in B1]> where F is RModule(P,col_wts);

    /*compute betti numbers of the minimal free res
    res := MinimalFreeResolution(M);
    b_mat := BettiRes(res,col_wts);
    return Min(col_wts)+Nrows(b_mat)-1;*/
    return Regularity(M);

end function;

/******************************************************************/
// Functions to work with A-modules - A being an alternating algebra.
//  (Temporary) functions for computing the kernel of a map between
//  free A-modules and the minimal free resolution of a (reduced)
//  A-module up to a given degree.

function LeftKernelA(B)
// returns a sequence of sequences, s,  s.t. the s give a
//  basis for the left kernel of "homogeneous" A-matrix B
//  (seq s gives the coordinates of a kernel vector)
   Amod := Module(BaseRing(B),Ncols(B));
   S := sub<Amod|[B[i]:i in [1..Nrows(B)]]>;
   return [Eltseq(b): b in MinimalBasis(MinimalSyzygyModule(S))];
end function;

function AKernel(f)

    /*M := Domain(f);
    A := BaseRing(M);
    wts := ColumnWeights(M);
    mat := Matrix(f);
    B := LeftKernelA(mat);
    b_wts := [wts[i]+LeadingTotalDegree(e[i]) where i is 
	   Min([i : i in [1..#e] | e[i] ne 0]) where e is Eltseq(b) : b in B];
    F := Module(A,b_wts);
    S := sub<M | [M!b : b in B]>;
    rels := MinimalSyzygyModule(S);
    return quo<F|[F!b : b in Basis(rels)]>;*/
    return Presentation(Kernel(f));

end function;
 
function MyAMinimalFreeResolution(md,n)
    //assert ISA(Type(md),ModMPol);
    A := BaseRing(md);
    wts := ColumnWeights(md);
    F0 := Module(A,0);
    F := Module(A,wts);
    mps := [* Homomorphism(F,F0,Matrix(A,Degree(F),0,[])) *];
    r_wts := [wts];

    r := 1;
    rels := sub<F|[F!r : r in RowSequence(RelationMatrix(md))]>;
    B := MinimalBasis(rels);
    if n eq 0 then rels := sub<F|B>; end if;
    while (#B ne 0) and (r le n) do
	// get new weights
	wts := [wts[i]+LeadingTotalDegree(e[i]) where i is 
	   Min([i : i in [1..#e] | e[i] ne 0]) where e is Eltseq(b) : b in B];
	G := Module(A,wts);
	mat := Matrix(A,[Eltseq(b) : b in B]);
        mat := Homomorphism(G,F,mat);
	F := G;
	Append(~mps,mat);
	Append(~r_wts,wts);
	rels := MinimalSyzygyModule(rels);
	B := MinimalBasis(rels);
	B := [G!b : b in B];
        rels := sub<G|B>;
	r +:= 1;
    end while;
    mps_rev := [* Homomorphism(F0,F,Matrix(A,0,Degree(F),[])) *];
    for i := #mps to 1 by -1 do
	Append(~mps_rev,mps[i]);
    end for;
    return Complex(mps_rev,-1),r_wts,((#B ne 0) select rels else F0);
end function;


procedure ExtendAResolutionData(~M,n)
    //assert Type(M) eq ModMPolGrd;
    assert assigned M`Aresidue;

    if n eq 0 then return; end if;
    wts := ColumnWeights(M`Aresidue);
    Mwts := M`Aweights;

    if #wts eq 0 then
	Append(~Mwts,[[]:i in [1..n]]);
    else
	rels := M`Aresidue;
	A := BaseRing(rels);
	B := MinimalBasis(rels); r := 1;
	F := Generic(rels);
    	while (#B ne 0) and (r le n) do
	    // get new weights
	    wts := [wts[i]+LeadingTotalDegree(e[i]) where i is 
	   Min([i : i in [1..#e] | e[i] ne 0]) where e is Eltseq(b) : b in B];
	    G := Module(A,wts);
	    F := G;
	    Append(~Mwts,wts);
	    rels := MinimalSyzygyModule(rels);
	    B := MinimalBasis(rels);
	    B := [G!b : b in B];
            rels := sub<G|B>;
	    r +:= 1;
    	end while;
	M`Aresidue := rels;	
    end if;
    M`Aweights := Mwts;
end procedure;

/*************************************************************/
// Functions to compute the nth graded piece of a (reduced) graded
//  module M as a vector space Mn and also compute the linear maps
//  Mn -> M_(n+1) given by multiplication by the variables x_i.
// This is needed to compute the Tate resolution associated to M
// under the BGG correspondence.

function ModuleGradedPiece(M,n)

    //assert Type(M) eq ModMPolGrd;
    
    P := BaseRing(M);
    R := BaseRing(P);
    wts := ColumnWeights(M);
    N := #wts;//Rank(M)

    if n lt Min(wts) then
	return V,map<V->M|v :-> M!0>,map<M->V|m :-> V!0> where
	    V is KSpace(R,0);
    end if;

    /* get all monomials of correct degree for each column */
    degs := [n-w : w in wts];
    diff_degs := Sort(Setseq(Seqset([d : d in degs | d ge 0])));
    Mons_d := [Setseq(MonomialsOfDegree(P,d)) : d in diff_degs];
    colMons := [(ind eq 0) select [P|] else Mons_d[ind] where
	ind is Index(diff_degs,d) : d in degs];

    V := KSpace(R,&+[#cm : cm in colMons]);
    mp_MtoV := map<M->V | m :-> 
	V!&cat[[MonomialCoefficient(e[i],mon):mon in colMons[i]]: i in [1..#e]]
		where e is Eltseq(m)>;
    
    //get relations
    Wvecs := [V|];
    rels := RelationMatrix(M);
    mp_PrtoV := map<PowerSequence(P)->V | m :-> 
        V!&cat[[MonomialCoefficient(m[i],mon):mon in colMons[i]]: i in [1..#m]]>;
    for i in [1..Nrows(rels)] do
        rel := Eltseq(rels[i]);
        if &and[f eq P!0 : f in rel] then continue; end if;
        d_min := Min([Min([TotalDegree(t)+wts[j] : t in Terms(rel[j])]) : 
                        j in [1..N] | rel[j] ne P!0]);
        d_max := Max([Max([TotalDegree(t)+wts[j] : t in Terms(rel[j])]) : 
                        j in [1..N] | rel[j] ne P!0]);
    
        for d in [d_min..d_max] do
            if d gt n then break; end if;
            rel_d := [P| (#ts eq 0 select 0 else &+[t:t in ts]) where
               ts is [te:te in Terms(rel[j])|TotalDegree(te) eq d-wts[j]] :
                           j in [1..N] ];
            Monoms := MonomialsOfDegree(P,n-d);
            Wvecs cat:= [mp_PrtoV([r*m:r in rel_d]):m in Monoms];
        end for;
    end for;
    delete mp_PrtoV;

    WS := Rowspace(Matrix(Wvecs));
    W,prj := quo<V|WS>;
    if WS eq V then
        return W,map<W->M|w :-> M!0>,map<M->W|m :-> W!0>;    
    end if;

    //construct map from W to M
    mon_dims := []; m := 1;
    for cm in colMons do
	if #cm eq 0 then 
	    Append(~mon_dims,[Integers()|]);
	else
	    m1 := m+#cm-1;
	    Append(~mon_dims,[m..m1]);
	    m := m1+1;
	end if;
    end for;

    B := BasisMatrix(WS);
    piv := [Min(Support(B[i])): i in [1 .. Nrows(B)]];

    function map_func(s,inds)
	z := Universe(s)!0;
	seq := s;
	for i in inds do
	  Insert(~seq,i,z);
	end for;
	return seq; 
    end function;

    mp_WtoM := map<W->M| w :-> M![Polynomial([es[j]:j in mon_dims[i]],
	colMons[i]) : i in [1..#colMons]] where 
	  es is map_func(Eltseq(w),piv)>;
                        
    return W,mp_WtoM,mp_MtoV*prj;
    
end function;

function MnToMnplus1(M,n)

    M1,m1,v1 := ModuleGradedPiece(M,n);
    M2,m2,v2 := ModuleGradedPiece(M,n+1);
    
    P := BaseRing(M); R := BaseRing(P);
    maps := [];
    for i in [1..Rank(P)] do
	x := P.i;
	Append(~maps, Matrix(R,[Eltseq(v2(x*m1(b))) : b in Basis(M1)]));
    end for;
    
    return M1,M2,maps;
    
end function;

function GetMMapA(M,n)

    _,_,maps := MnToMnplus1(M,n);
    r1 := Nrows(maps[1]);
    r2 := Ncols(maps[1]);
    
    r := Rank(BaseRing(M));
    K := BaseRing(BaseRing(M));
    
    A := ExteriorAlgebra(K,r);
    
    map_mat := Matrix(A,[[ &+[maps[i][j,k]*A.i : i in [1..#maps]]
		: k in [1..r2] ] : j in [1..r1]]);
    
    M1 := Module(A,[-n : i in [1..r1]]);
    M2 := Module(A,[-n-1 : i in [1..r2]]);
    
    return M1,M2,Homomorphism(M1,M2,map_mat);
    
end function;

/******************************************************************
// Temporary Hilbert Function/Polynomial functions for graded modules.

function MyHilbertSeries(M)
// computes the Hilbert series of graded module M (must be a 
// quotient module)

    //assert Type(M) eq ModMPolGrd;
    R := BaseRing(M);
    n := Ncols(M);
    if n eq 0 then return RationalFunctionField(Integers())!0; end if;
    rels := GroebnerBasis(sub<Universe(R) | R>) where 
		R is Relations(M);
    wts := ColumnWeights(M);
    
    lead_rels := [LeadingTerm(r) : r in rels];
    Iseq := [[]: i in [1..n]];
    for lr in lead_rels do
	j := 1;
	while (lr[j] eq R!0) and (j le n) do j +:= 1; end while;
	if j le n then Append(~(Iseq[j]),lr[j]); end if;
    end for;
    Is := [ideal<R|seq> : seq in Iseq];
    for I in Is do MarkGroebner(I); end for;

    // get hilb series for each ideal
    HSs := [HilbertSeries(I) : I in Is];
    // shift by col weights
    t := Parent(HSs[1]).1;
    HSs := [(t^wts[i])*HSs[i] : i in [1..n]];

    return &+HSs;

end function;
*/
function MyHilbertPolynomial(M)
// computes the Hilbert polynomial of graded module M (must be a 
// quotient module) and minimal k s.t. H(d) agrees with the Hilbert
// function of I at d for d >= k.

    /*HS := MyHilbertSeries(M);
    den := Denominator(HS);
    num := Numerator(HS);
    if IsZero(num) then return num,0; end if;

    // deal with possible t in the denominator
    t := Parent(den).1;
    d := Min([i : i in [1..#cs] | cs[i] ne 0])-1 where
		cs is Coefficients(den);
    if d gt 0 then
	den div:= t^d;
	d := -d;
    end if;

    d +:= Max(0,Degree(num)-Degree(den)+1);
    dd := Degree(den);
    num := (num mod den);
    num1 := Evaluate(num,t+1);
    assert Evaluate(den,t+1) eq t^dd;
    cs := Coefficients(num1);
    cs cat:= [0 : i in [1..dd-#cs]];
    
    // HilbPoly(x) is sum_i (-1)^(dd+1-i)*cs[i]*Binomial(x+dd-i,dd-i)
    R := PolynomialRing(Rationals());
    x := R.1; HP := R!(cs[1]);
    for i in [1..dd-1] do
	HP := HP*((x+(dd-i))/(dd-i)) - R!(cs[i+1]);
    end for;

    return ((-1)^dd)*HP,d;*/
    return HilbertPolynomial(M);

end function;

/******************************************************************/
/*
intrinsic CastelnuevoMumfordBound(M::ModMPolGrd : Exact := true) -> RngIntElt
{ Returns an upper bound for the Castelnuevo-Mumford regularity of graded
  module M. If the parameter Exact is true (the default) then the exact
  regularity is returned. }

  require (Type(R) eq RngMPol) and IsField(BaseRing(R)) where R is
	BaseRing(M) : 
	"M must be defined over a polynomial ring over a field.";
    if Exact then
	return Regularity(M);
    else
	return RegularityBound1(M);
    end if;

end intrinsic;
*/

// Main intrinsic

intrinsic CohomologyDimension(M::ModMPol,r::RngIntElt,n::RngIntElt) -> RngIntElt
{ M is a graded module over polynomial ring k[x0,..,xm]. Returns the
  dimension of H^r(P^m,M~(n)), where M~ is the coherent sheaf on P^m
  associated to M, r >= 0 and n are integers. }

  require (Type(R) eq RngMPol) and IsField(BaseRing(R)) where R is
	BaseRing(M) : 
	"M must be defined over a polynomial ring over a field.";
  require (Type(M) eq ModMPolGrd) or IsHomogeneous(M):
	"Module M must be graded";
  require r ge 0 : "Second argument must be >= 0.";

  Mp := Presentation(M); // use presentation in most functions

  if assigned M`CMbound then
    rb := M`CMbound;
  else
    vprint Cohom: "Getting regularity bound";
    vtime Cohom: rb := RegularityBound1(Mp);
    M`CMbound := rb;
  end if;
  m := r+n;
  if m ge rb then
  // only cohomology in H^0 - read off from Hilbert poly
    if r gt 0 then return 0; end if;
    if assigned M`HilbPoly then
	hp := M`HilbPoly;
    else
	vprint Cohom: "Getting the hilbert polynomial";
	vtime Cohom: hp := MyHilbertPolynomial(Mp);
	M`HilbPoly := hp;
    end if;
    return Evaluate(hp,n);
  end if;
  if not assigned M`Aweights then
    vprint Cohom: "Computing basic A-module map";
    vtime Cohom: M1,M2,f := GetMMapA(Mp,rb);
    wts_M1 := [-rb : i in [1..Degree(M1)]];
    vprint Cohom: "Computing kernel of basic A-module map";
    vtime Cohom: K := AKernel(f);
    vprint Cohom: "Computing projective resolution";
    vtime Cohom: _,r_wts,res := MyAMinimalFreeResolution(K, rb-1-m);
    Insert(~r_wts,1,wts_M1);
    M`Aweights := r_wts; M`Aresidue := res;
  else
    r_wts := M`Aweights;
    if m+(#r_wts) le rb then
	vprint Cohom: "Extending projective resolution";
	vtime Cohom: ExtendAResolutionData(~M,rb+1-m-(#r_wts));
	r_wts := M`Aweights;
    end if;
  end if;
  wts := r_wts[rb+1-m];
  return #[1:w in wts | w eq -n];

end intrinsic;
