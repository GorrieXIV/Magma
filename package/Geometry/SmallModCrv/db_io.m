freeze;
///////////////////////////////////////////////////////////////////
//     Functions to read data from the database file and         //
//        create records for Small Modular Curves                //
//                                                               //
//             mch - 10/2011                                     //
///////////////////////////////////////////////////////////////////

//data_file := "Geometry/SmallModCrv/db1_81";

X0NData :=  recformat<
    N		: RngIntElt,  // the level N of X0(N)
    X0N		: Crv,	      // projective model over Q
/* cusp + other rat point data */
    cusps	: List,       // points/clusters giving the cusps in order of d|N
    cusp_pls    : SeqEnum,    // generation data for places over singular cusps
			      // in order of d|N - empty data for non-sing cusps
    sing_cusps  : SeqEnum,    // sequence of d|N for which corr. cusp is singular 
    rat_pts	: SeqEnum,    // any non-cuspidal rational points for g>0
/* auto data */
    ALs     	: SeqEnum,    // non-trivial Atkin lehner involution eqns in order of d||N
    S2ns        : List,       // [S2,S4,S8] up to biggest S_{2^n} auto-eqns
			      // (over extension fields!)
    S3		: SeqEnum,    // eqns for S3 (if it exists) over Q(mu_3)
    extra_aut   : SeqEnum,    // extra involution when N=37,63 or 108
    max_aut_degs: SeqEnum,    // seq of pairs <d,n> giving the min d such that all auts
			      // of X0(N) over Q(mu_n) can be defined by eqns of deg <=d
    Sn_degs	: SeqEnum,    // if 36|N, gives the (min) degree of the defining equations
			      // for S6,S12,S24 up to the largest S_{3*2^n}
/* projection data/Ei data depending on whether N is prime or not */
    prjs	: List,	      // tups <p,[r1,r2,..,rn]> for p|N where
			      // the ambient of X0(N/p) is of degree n and the
			      // projection map X0(N)->X0(N/p) is given by
			      // [r1,r2,..,rn]. Only for N > 1 not prime.
			      // The ri are polys in the ambient variables.
    dif		: Tup,	      // only for N=p and X0N not subhyperelliptic. tup is
			      // of the form <i,j,r1,r2>  i,j +ive ints and r1,r2
			      // polys in n-1 vars where n=rank(ambient(X0N)). Means
			      // that diff is given on the ith affine patch A (should
			      // be the FF patch) by (r1/r2)d(x_j) where x_j is the
			      // jth variable of A. For genus 0, dif is taken as -dt
			      // and for ell/hyp y^2+hy=f model, as -dx/(2y+h). The
			      // minus signs are chosen so that dif = (q^-1+..)(dq/q)
			      // or (q^g+..)(dq/q) respectively at inf
    Es		: SeqEnum,    // only for N=p or 1: a sequence of 3 pairs [[r1,r2],[s1,s2],[t1,t2]]
			      // s.t. E2p is (r1/r2)*dif, E4 is (s1/s2)*dif^2 and E6 is
			      // (t1/t2)*dif^3 as mero. diff, 2-diff and 3-diff on X0N.
			      // r1,r2 are polys on the ith affine patch as for dif.
			      // E2p := (pE2(pz)-E(z))/d = (p-1)/d+(24/d)sum d(n)q^n
			      // where d is (24,p-1) when N != 1 and [r1,r2]=[0,1] when N=1
			      // E4 = 1+240*sum d3(n)q^n
			      // E6 = 1-504*sum d5(n)q^n
    qexps	: MonStgElt   // string containing a comma-separated series of expressions that
			      // generate the q-expansions of the modular functions/forms
			      // represented by the coordinate functions (for format, see
			      // q_expansions.m) 
>;

offsets := \[ 0, 120, 264, 422, 572, 741, 1010, 1211, 1379, 1561, 1852, 2445, 2752, 3021, 3767, 4640, 
4871, 5588, 5939, 6571, 7204, 8049, 8862, 9295, 9976, 10155, 10820, 11190, 11896, 12374, 
13658, 14200, 14678, 15780, 16777, 17296, 18034, 19044, 20983, 21672, 22289, 22887, 24950, 
25905, 26938, 27780, 28895, 29596, 30284, 30898, 31566, 33306, 34867, 36368, 37607, 39095, 
40211, 41682, 43761, 0, 44534, 0, 45982, 47859, 0, 0, 0, 0, 0, 0, 48377, 0, 0, 0, 0, 0, 0, 
0, 0, 0, 49328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ];

function data_filename()
    return Sprintf("%o/data/db1_81", GetLibraryRoot());
end function;

/*
function compute_offsets()
  F := Open(data_file,"r");
  offs := [0 : i in [1..100]];
  o := 0;
  while true do
    lin := Gets(F);
    if IsEof(lin) then break; end if;
    o +:= (#lin)+1;
    if lin eq "####" then
	lin := Gets(F);
	if IsEof(lin) then break; end if;
	i := Index(lin," ");
	N := StringToInteger(lin[1..i-1]);
	offs[N] := o;
	o +:= (#lin)+1;
    end if;
  end while;
  return offs;  
end function;
*/

function read_int_poly(F,R)
// read in multivariate polynomial from F and return coerced into R
    n := Rank(R);
    cs := [Rationals()|];
    mons := [];
    while true do
	lin := Gets(F);
	if #lin eq 0 then break; end if;
	seq := StringToIntegerSequence(lin);
	assert #seq eq n+1;
	Append(~cs,seq[1]);
	Append(~mons,Monomial(R,seq[2..n+1]));
    end while;
    return Polynomial(cs,mons);
end function;

function read_cyclo_poly(F,R)
// read in multivariate polynomial over Q(mu_n) from F and return coerced into R
    n := Rank(R);
    k := BaseRing(R);
    m := AbsoluteDegree(k);
    cs := [k|];
    mons := [];
    while true do
	lin := Gets(F);
	if #lin eq 0 then break; end if;
	seq := StringToIntegerSequence(lin);
	assert #seq eq n+m;
	Append(~cs,k!(seq[1..m]));
	Append(~mons,Monomial(R,seq[m+1..n+m]));
    end while;
    return Polynomial(cs,mons);
end function;

intrinsic IsInSmallModularCurveDatabase(N::RngIntElt) -> BoolElt
{ Returns whether data for the level N X0(N) is in the small modular curve database }

    require N gt 0: "N should be a positive integer";
    o := ((N le #offsets) select offsets[N] else 0);
    return ((N eq 1) or (o gt 0));

end intrinsic;

intrinsic Create_SmallCrvMod_Structure(N::RngIntElt) -> Rec
{ Internal function }
//Creates the structure for the level N object in the small modular curve database

    o := ((N le #offsets) select offsets[N] else 0);
    require ((N eq 1) or (o gt 0)):
	"Sorry. No data yet for level " cat IntegerToString(N);
    dat_fil := data_filename();
    F := Open(dat_fil,"r");
    Seek(F,o,0);
    // get level N and the type
    lin := Gets(F);
    ns := StringToIntegerSequence(lin);
    N,typ,typ2 := Explode(ns);
    rN := rec<X0NData| N:= N>;
    // get curve equation
    if typ eq 0 then
	C := Curve(ProjectiveSpace(Rationals(),1));
    elif typ le 2 then //1 = elliptic, 2 = hyperelliptic
	P := PolynomialRing(Rationals());
	seq :=  StringToIntegerSequence(Gets(F));
	if typ eq 1 then
	  C := EllipticCurve(seq);
	else
	  h := P!seq;
	  f := P!StringToIntegerSequence(Gets(F));
	  C := HyperellipticCurve(f,h);
	end if;
    else
	P := ProjectiveSpace(Rationals(),typ-1);
	R := CoordinateRing(P);
	eqns := [read_int_poly(F,R) : i in [1..typ2]];
	C := Curve(P,eqns : Saturated := true);
    end if;
    rN`X0N := C;
    P := Ambient(C);
    R := CoordinateRing(P);
    assert Gets(F) eq "#";

    // cusp/rat point data
    ds := Divisors(N);
    cusps := [**];
    sing_inds := [];
    for d in ds do
	seq := StringToIntegerSequence(Gets(F));
	assert d eq seq[1];
	if seq[3] eq 1 then Append(~sing_inds,d);end if;
	if seq[2] eq 0 then //rational cusp
	  pt := StringToIntegerSequence(Gets(F));
	  Append(~cusps,C!pt);
	else //cusp is a place given by a cluster
	  assert seq[2] eq 1;
	  neqns := StringToIntegerSequence(Gets(F))[1];
	  eqns :=  [read_int_poly(F,R) : i in [1..neqns]];
	  Append(~cusps,Cluster(Ambient(C),eqns));
	end if;
    end for;
    rN`cusps := cusps;
    if #sing_inds gt 0 then rN`sing_cusps := sing_inds; end if;
      // any place separation data for sing cusps?
    cusp_pls := [];
    n := StringToIntegerSequence(Gets(F))[1];
    for j in [1..n] do
	d1,d2 := Explode(StringToIntegerSequence(Gets(F)));
	num := read_int_poly(F,R);
	den := read_int_poly(F,R);
	Append(~cusp_pls,<d1,d2,num,den>);
    end for;
    if #cusp_pls gt 0 then rN`cusp_pls := cusp_pls; end if;
      // any non-cuspidal rat. pts (g>0)?
    rat_pts := [];
    n := StringToIntegerSequence(Gets(F))[1];
    for j in [1..n] do
	pt := StringToIntegerSequence(Gets(F));
	Append(~rat_pts,C!pt);
    end for;
    if #rat_pts gt 0 then rN`rat_pts := rat_pts; end if;
    assert Gets(F) eq "#";

    //automorphism data
    ds := [d : d in ds | GCD(d,N div d) eq 1];
    Remove(~ds,1);
    ALs := [];
    for d in ds do
	assert d eq StringToIntegerSequence(Gets(F))[1];
	eqns := [read_int_poly(F,R) : i in [1..Rank(R)]];
	Append(~ALs,eqns);
    end for;
    rN`ALs := ALs;
      //add S2ns if any
    if IsDivisibleBy(N,4) then
	S2ns := [**];
	r := Min(3,Valuation(N,2) div 2);
	for i in [1..r] do
	  if i eq 1 then 
	    eqns := [read_int_poly(F,R) : i in [1..Rank(R)]];
	  else
	    k := (i eq 2) select QuadraticField(-1) else CyclotomicField(8);
	    R1 := PolynomialRing(k,Rank(R),"grevlex");
	    eqns := [read_cyclo_poly(F,R1) : i in [1..Rank(R)]];
	  end if;
	  Append(~S2ns,eqns);
	end for;
	rN`S2ns := S2ns;
    end if;
      //add S3 if it exists
    if IsDivisibleBy(N,9) then
	R1 := PolynomialRing(CyclotomicField(3),Rank(R),"grevlex");
	S3 := [read_cyclo_poly(F,R1) : i in [1..Rank(R)]];
	rN`S3 := S3;
    end if;
      //extra aut if it exists (N = 108 will cause probs as not def over Q or cyclo field!)
    if N in [37,63,108] then
      if N ne 63 then
	ea := [read_int_poly(F,R) : i in [1..Rank(R)]];
	rN`extra_aut := ea;
      else
	R1 := PolynomialRing(CyclotomicField(3),Rank(R),"grevlex");
	ea := [read_cyclo_poly(F,R1) : i in [1..Rank(R)]];
	eai := [read_cyclo_poly(F,R1) : i in [1..Rank(R)]];
	rN`extra_aut := [ea,eai];
      end if;
    end if;
      // max_aut_degs?
    mad := [];
    n := StringToIntegerSequence(Gets(F))[1];
    for j in [1..n] do
	d1,n1 := Explode(StringToIntegerSequence(Gets(F)));
	Append(~mad,<d1,n1>);
    end for;
    if #mad gt 0 then rN`max_aut_degs := mad; end if;
      // Sn_degs?
    n := StringToIntegerSequence(Gets(F))[1];
    if n gt 0 then
	assert IsDivisibleBy(N,36);
	rN`Sn_degs := StringToIntegerSequence(Gets(F));
    end if;
    assert Gets(F) eq "#";

    // projection/Ei data
    if (N eq 1) or IsPrime(N : Proof := false) then
	assert StringToIntegerSequence(Gets(F))[1] eq 0;
	// get dif info
	if typ ge 3 then
	  i,j := Explode(StringToIntegerSequence(Gets(F)));
	  R1 := CoordinateRing(AffinePatch(P,i));
	  d_num := read_int_poly(F,R1);
	  d_den := read_int_poly(F,R1);
	  rN`dif := <i,j,d_num,d_den>;
	else
	  R1 := CoordinateRing(AffinePatch(P,1));
	end if;
	E2 := [read_int_poly(F,R1),read_int_poly(F,R1)];
	E4 := [read_int_poly(F,R1),read_int_poly(F,R1)];
	E6 := [read_int_poly(F,R1),read_int_poly(F,R1)];
	rN`Es := [E2,E4,E6];
    else
	assert StringToIntegerSequence(Gets(F))[1] eq 1;
	nps := StringToIntegerSequence(Gets(F))[1];
	prjs := [**];
	for i in [1..nps] do
	  d,n := Explode(StringToIntegerSequence(Gets(F)));
	  eqns := [read_int_poly(F,R) : i in [1..n]];
	  Append(~prjs,<d,eqns>);
	end for;
	rN`prjs := prjs;
    end if;
    assert Gets(F) eq "#";

    // q-expansion data
    rN`qexps := Gets(F);

    assert Gets(F) eq "####";
    return rN;

end intrinsic; 
